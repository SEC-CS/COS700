"""
residuals/utils/matcher.py
==========================
Recovers the part of a proof step's substitution that is determined by the
goal, so the model never has to emit it.

A Metamath step is `label` plus a substitution for the applied theorem's
mandatory variables. Most of those variables occur in the theorem's own
conclusion, and that conclusion -- under the substitution -- must equal the
goal. So they are pinned by matching the conclusion pattern against the
goal, and are a lookup rather than a prediction. The rest, occurring only
in the theorem's hypotheses, are *residual*: the cut formula, the one part
of the step that is a genuine choice.

This is first-order matching, not unification: only the pattern carries
variables, the goal is ground, and substitution is literal token-list
splicing (see mmverify's six-line apply_subst). `A. x ph` is three tokens,
not a binder -- variable capture is what $d conditions handle, separately
and afterwards.

IMPORTANT: data preparation and proof search must call the *same*
`complete()` with the same `cap`. The training target for a step is built
by stripping exactly the variables the matcher will recover at search
time; strip a variable the matcher then recovers differently and you have
made a training example the model cannot rescue -- it emits a correct
label and the step still fails, with nothing in the loss to say why.
"""

import pickle
from pathlib import Path

# Solutions to return per goal. 32 rather than 8: raising the cap moves the
# unrecoverable rate on section 01 from 0.41% to 0.05% (25 steps -> 3 of
# 6035), while the rate at which the FIRST solution is the correct one is
# flat at 94.98% either way.
DEFAULT_CAP = 32

# Bound on search nodes per goal. A handful of set.mm theorems (merco1,
# merco1lem10, lukshef-ax1 -- Meredith and Lukasiewicz-Sheffer single-axiom
# systems) have 400-700 token flat conclusions with many variables and
# almost no constants to anchor spans against, and blow naive width-guessing
# up to ~2M nodes / 1.5s. 1.06% of section-01 steps cost over 1ms; the
# median is 8us. Without this bound throughput is 83 goals/s; with it, 604.
DEFAULT_MAX_NODES = 2_000_000

DEFAULT_MM = "data/set.mm"
# mmverify.py is a vendored third-party verifier rather than method code, so
# the residuals tree reads the baseline tree's copy instead of duplicating
# it. Override with --mmverify if that ever stops being true.
DEFAULT_MMVERIFY = "baseline/data/mmverify.py"
DEFAULT_CACHE = "residuals/data/label_table.pkl"


# ---------------------------------------------------------------------------
# Per-label table, built once from set.mm
# ---------------------------------------------------------------------------


def label_table(
    mm_path: str = DEFAULT_MM,
    mmverify_path: str = DEFAULT_MMVERIFY,
    cache: str = DEFAULT_CACHE,
    rebuild: bool = False,
) -> dict:
    """
    label -> {"result", "kinds", "rvars"} for every $a/$p assertion.

    result : the assertion's conclusion, as a token pattern
    kinds  : mandatory variable -> typecode ("wff" | "class" | "setvar")
    rvars  : the mandatory variables occurring in the conclusion, i.e. the
             ones `complete()` is responsible for recovering

    The table must be built while mmverify's frame stack is still live.
    After MM.read() returns, mm.fs is empty and anything resolving
    variables through it -- mm.find_vars() included -- silently returns
    nothing. Reading the variable names straight out of `mand_var` avoids
    that; it is the same trap that disables the $d check in
    baseline/search/proof_search.py.

    Parsing set.mm costs ~100s, so the result is pickled to `cache`.
    """
    cache_path = Path(cache)
    if cache_path.exists() and not rebuild:
        with cache_path.open("rb") as f:
            return pickle.load(f)

    import importlib.util

    spec = importlib.util.spec_from_file_location("mmverify", mmverify_path)
    mmv = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mmv)
    mmv.verbosity = 0

    mm = mmv.MM()
    with open(mm_path, encoding="utf-8", errors="replace") as f:
        mm.read(mmv.toks(f))

    table = {}
    for label, (kind, data) in mm.labels.items():
        if kind not in ("$a", "$p"):
            continue
        _distinct, mand_var, _hyp, result = data
        result = list(result)
        in_conclusion = set(result)
        table[label] = {
            "result": result,
            "kinds": {v: k for k, v in mand_var},
            "rvars": {v for _, v in mand_var if v in in_conclusion},
        }

    cache_path.parent.mkdir(parents=True, exist_ok=True)
    with cache_path.open("wb") as f:
        pickle.dump(table, f)
    return table


# ---------------------------------------------------------------------------
# The matcher
# ---------------------------------------------------------------------------


def complete(
    pattern: list,
    goal_conclusion: list,
    kinds: dict,
    cap: int = DEFAULT_CAP,
    max_nodes: int = DEFAULT_MAX_NODES,
) -> list:
    """
    Every substitution s with apply_subst(pattern, s) == goal_conclusion,
    in the order proof search should try them.

    On section 01 the first solution returned is the correct one for 94.98%
    of steps, and the correct one is somewhere in the list for 99.95%.
    Ambiguity is cheap to live with: hand every solution to the verifier as
    a separate candidate step and let it discriminate. Resolving it properly
    would mean parsing the goal with set.mm's 1445 syntax axioms and
    matching tree-against-tree, which is unique and linear but a real
    parser; it is an optimisation, not a prerequisite.
    """
    out = []
    nodes = 0

    def rec(pi, ti, subst):
        nonlocal nodes
        nodes += 1
        if len(out) >= cap or nodes > max_nodes:
            return

        if pi == len(pattern):
            if ti == len(goal_conclusion):
                out.append(dict(subst))
            return

        token = pattern[pi]
        kind = kinds.get(token)

        if kind is None:  # a constant: must match exactly
            if ti < len(goal_conclusion) and goal_conclusion[ti] == token:
                rec(pi + 1, ti + 1, subst)
            return

        if token in subst:  # already bound: must match its binding
            val = subst[token]
            if goal_conclusion[ti : ti + len(val)] == val:
                rec(pi + 1, ti + len(val), subst)
            return

        # setvar spans exactly one token; wff/class span one or more, so
        # the width has to be guessed. Leave one token for each remaining
        # pattern element.
        widest = (
            1
            if kind == "setvar"
            else len(goal_conclusion) - ti - (len(pattern) - pi - 1)
        )
        for width in range(1, max(1, widest) + 1):
            if ti + width > len(goal_conclusion):
                break
            subst[token] = goal_conclusion[ti : ti + width]
            rec(pi + 1, ti + width, subst)
            del subst[token]
            if len(out) >= cap or nodes > max_nodes:
                return

    rec(0, 0, {})
    return out


def determined_key(subst: dict, rvars: set) -> tuple:
    """
    A hashable, order-independent identity for the determined half of a
    substitution, for comparing two candidate solutions.
    """
    return tuple(
        sorted((v, " ".join(val)) for v, val in subst.items() if v in rvars)
    )

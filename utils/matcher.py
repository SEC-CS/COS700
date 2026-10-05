"""

Recovers the part of a proof step's substitution that is determined by the
goal, so the model never has to emit it.

"""

import pickle
from pathlib import Path

# Solutions to return per goal. 
DEFAULT_CAP = 3

# Not really necessary, but a sanity check to avoid combinatorial explosion in pathological cases.
DEFAULT_MAX_NODES = 2_000_000

PAIRS = {"(": ")", "{": "}", "[": "]", "<.": ">.", "[.": "].", "[_": "]_"}
CLOSERS = {close: open_ for open_, close in PAIRS.items()}

DEFAULT_MM = "data/set.mm"

DEFAULT_MMVERIFY = "data/mmverify.py"
DEFAULT_CACHE = "data/residual/label_table.pkl"


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
            span = goal_conclusion[ti : ti + width]
            if not balanced(span):
                continue  # not an expression, so not a real substitution
            subst[token] = span
            rec(pi + 1, ti + width, subst)
            del subst[token]
            if len(out) >= cap or nodes > max_nodes:
                return

    rec(0, 0, {})
    return out


def balanced(tokens: list) -> bool:
    """Whether a token span's delimiters nest properly."""
    stack = []
    for token in tokens:
        if token in PAIRS:
            stack.append(token)
        elif token in CLOSERS and (not stack or stack.pop() != CLOSERS[token]):
            return False
    return not stack


def determined_key(subst: dict, rvars: set) -> tuple:
    """
    A hashable, order-independent identity for the determined half of a
    substitution, for comparing two candidate solutions.
    """
    return tuple(sorted((v, " ".join(val)) for v, val in subst.items() if v in rvars))

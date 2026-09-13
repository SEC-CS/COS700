"""
residuals/utils/formatting.py
=============================
The canonical goal/proofstep string format for the residuals tree.

`parse_goal`, `parse_proofstep`, `format_goal` and `format_proofstep` are
kept semantically identical to baseline/utils/formatting.py, so a residual
target is read back by the same parser the baseline uses -- it is just a
proofstep with fewer `{{ var : val }}` blocks. Everything below
`format_proofstep` is specific to the residual method.

This module is the single definition of the format for this tree. Nothing
else may define its own copy: a hand-synced second copy is how a silent
train/eval format mismatch gets introduced, which looks like a bad result
rather than a bug.
"""

from typing import Optional

# A target carrying an explicit, complete substitution rather than just the
# residual. Emitted for the rare step whose determined substitution the
# matcher cannot recover, so no step is unrepresentable.
SENTINEL = "!FULL"


# ---------------------------------------------------------------------------
# Shared format -- identical semantics to baseline/utils/formatting.py
# ---------------------------------------------------------------------------


def parse_goal(goal_str: str) -> Optional[dict]:
    try:
        inner_start = goal_str.index("[[") + 2
        inner_end = goal_str.index("]]")
        hyp_block = goal_str[inner_start:inner_end].strip()
        conc_block = goal_str[inner_end + 2 :].strip()
        e_hyps = (
            [h.strip().split() for h in hyp_block.split("   ") if h.strip()]
            if hyp_block
            else []
        )
        return {"e_hyps": e_hyps, "conclusion": conc_block.split()}
    except Exception:
        return None


def parse_proofstep(step_str: str) -> Optional[dict]:
    """
    Parse "theorem_label {{ var1 : val1 }} {{ var2 : val2 }} ...".

    A residual target parses identically -- `subst` simply holds only the
    residual variables. A sentinel-prefixed target is rejected here; use
    `parse_target` instead, which strips the sentinel first.
    """
    try:
        subst = {}
        s = step_str
        while "{{" in s:
            start = s.index("{{")
            end = s.index("}}", start)
            subst_str = s[start + 2 : end].strip()
            colon = subst_str.index(":")
            var = subst_str[:colon].strip()
            val = subst_str[colon + 1 :].strip().split()
            subst[var] = val
            s = s[:start] + s[end + 2 :]
        s = s.strip()
        label_toks = s.split()
        if len(label_toks) != 1:
            return None  # exactly one token should remain: the label
        return {"theorem": label_toks[0], "subst": subst}
    except Exception:
        return None


def format_goal(e_hyps: list, conclusion: list) -> str:
    if e_hyps:
        return f"[[ {'   '.join(' '.join(h) for h in e_hyps)} ]] {' '.join(conclusion)}"
    return f"[[ ]] {' '.join(conclusion)}"


def format_proofstep(theorem_label: str, subst: dict) -> str:
    subst_str = " ".join(
        f"{{{{ {v} : {' '.join(val)} }}}}" for v, val in sorted(subst.items()) if val
    )
    return f"{theorem_label}" + (f" {subst_str}" if subst_str else "")


# ---------------------------------------------------------------------------
# Residual method
# ---------------------------------------------------------------------------


def format_target(theorem_label: str, subst: dict, sentinel: bool = False) -> str:
    """
    A training target for the residual method.

    With `sentinel=False` (the normal case) `subst` holds only the residual
    variables and this is exactly `format_proofstep`. With `sentinel=True`
    `subst` is the complete substitution and the target is prefixed with
    SENTINEL, telling the search not to run the matcher for this step.
    """
    step = format_proofstep(theorem_label, subst)
    return f"{SENTINEL} {step}" if sentinel else step


def parse_target(target: str) -> Optional[dict]:
    """
    Inverse of `format_target`.

    -> {"theorem", "subst", "full"} where `full` is True if the target
    carried a complete substitution behind the sentinel (so the caller
    must not try to complete it by matching), and False if `subst` holds
    only residuals and the determined variables still need recovering.
    """
    target = target.strip()
    full = target.startswith(SENTINEL)
    if full:
        target = target[len(SENTINEL) :].strip()
    parsed = parse_proofstep(target)
    if parsed is None:
        return None
    parsed["full"] = full
    return parsed


def goal_conclusion(goal_str: str) -> list:
    """
    The conclusion half of a "[[ hyps ]] conclusion" goal string, as tokens.

    This is what an applied theorem's conclusion pattern gets matched
    against -- the goal currently being expanded, not the root theorem.
    """
    return goal_str.split("]]", 1)[1].split()

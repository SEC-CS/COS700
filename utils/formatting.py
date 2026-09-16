from typing import Optional


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
    Parse a proofstep string of the form:
        "theorem_label {{ var1 : val1 }} {{ var2 : val2 }} ..."

    Unlike the old format, there is no "[[ ... ]] conclusion" block here —
    the model predicts the applied theorem's label directly rather than
    the resulting conclusion string, so there's nothing to re-derive the
    label from.
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

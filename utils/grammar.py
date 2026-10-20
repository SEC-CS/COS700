"""
set.mm's syntax, for checking that a substitution is a well-formed expression
of its variable's type and for producing the syntax proofs the kernel needs.
"""

import itertools
from collections import defaultdict
from functools import lru_cache


class Grammar:
    """Recursive-descent parser over set.mm's syntax axioms, yielding syntax proofs."""

    def __init__(self, mm):
        self.varkind = {}
        self.axioms = defaultdict(list)
        for label, (kind, data) in mm.labels.items():
            if kind == "$f":
                self.varkind[data[1]] = data[0]
        for label, (kind, data) in mm.labels.items():
            if kind != "$a":
                continue
            _, mand_var, hyp, result = data
            if result[0] != "|-" and not hyp:
                kinds = {v: k for k, v in mand_var}
                order = [v for _, v in mand_var]
                self.axioms[result[0]].append((label, tuple(result[1:]), kinds, order))
        self.syntax_proof = lru_cache(maxsize=200_000)(self._syntax_proof)

    def _syntax_proof(self, kind: str, toks: tuple):
        """
        Postfix proof of `kind toks`, with variables left as ("var", token),
        or None if `toks` is not a `kind`. Takes a tuple so it can be cached.
        """

        @lru_cache(None)
        def parse(k, i, j):
            if j - i == 1 and self.varkind.get(toks[i]) == k:
                return (("var", toks[i]),)
            if k == "setvar":
                return None
            for label, pat, kinds, order in self.axioms.get(k, ()):
                if len(pat) > j - i:
                    continue
                if pat[0] not in kinds and pat[0] != toks[i]:
                    continue
                if pat[-1] not in kinds and pat[-1] != toks[j - 1]:
                    continue
                if len(pat) == 1 and kinds.get(pat[0]) == k:
                    continue
                children = match(pat, kinds, 0, i, j)
                if children is not None:
                    by_var = dict(children)
                    return tuple(s for v in order for s in by_var[v]) + (label,)
            return None

        def match(pat, kinds, pi, ti, j):
            if pi == len(pat):
                return () if ti == j else None
            tok = pat[pi]
            if tok not in kinds:
                if ti < j and toks[ti] == tok:
                    return match(pat, kinds, pi + 1, ti + 1, j)
                return None
            rest = len(pat) - pi - 1
            for end in range(ti + 1, j - rest + 1):
                sub = parse(kinds[tok], ti, end)
                if sub is None:
                    continue
                tail = match(pat, kinds, pi + 1, end, j)
                if tail is not None:
                    return ((tok, sub),) + tail
            return None

        if not toks:
            return None
        return parse(kind, 0, len(toks))

    def step_violation(self, mand_var, distinct, subst, scope) -> str | None:
        """
        Why applying an assertion with this substitution inside `scope`
        would be rejected by the kernel, or None if it would not.

        scope: (dv pairs, active variables) of the theorem being proved,
        or (None, None) when there is no such theorem, which checks only
        well-formedness and that $d variables are kept distinct.
        """
        dv, active = scope
        for kind, var in mand_var:
            value = tuple(subst[var])
            if self.syntax_proof(kind, value) is None:
                return f"not a {kind}: {' '.join(value)}"
            if active is not None:
                for tok in value:
                    if tok in self.varkind and tok not in active:
                        return f"variable {tok} not declared in this scope"
        for x, y in distinct:
            x_vars = {t for t in subst[x] if t in self.varkind}
            y_vars = {t for t in subst[y] if t in self.varkind}
            for a, b in itertools.product(x_vars, y_vars):
                if a == b or (dv is not None and (min(a, b), max(a, b)) not in dv):
                    return f"disjoint violation: {a}, {b}"
        return None


def make_scoped_mm(mmv):
    """
    An mmverify MM that also remembers, for every $p, the frame it is proved
    in: its $d pairs and active variables, plus each label's position in the
    database (mm.labels keeps declaration order).
    """

    class ScopedMM(mmv.MM):
        def __init__(self):
            super().__init__()
            self.scopes = {}

        def verify(self, stat_label, stat, proof):
            super().verify(stat_label, stat, proof)
            dv, active = set(), set()
            for frame in self.fs:
                dv |= frame.d
                active |= set(frame.f_labels)
            self.scopes[stat_label] = (frozenset(dv), frozenset(active))

    return ScopedMM

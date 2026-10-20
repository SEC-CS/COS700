"""
Re-verify proofs written by proof_search.py with the Metamath kernel (mmverify).

"""

import argparse
import importlib.util
import json
import os
import sys
from collections import defaultdict

from utils.formatting import parse_proofstep
from utils.grammar import Grammar

HYPOTHESIS_STEP = "$e"


def load_mmverify(path: str):
    spec = importlib.util.spec_from_file_location("mmverify", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def parse_proved_file(path: str) -> dict:
    """label -> {"root": goal, "steps": {conclusion str: step str}}"""
    proofs = {}
    current = None
    with open(path, encoding="utf-8") as f:
        for line in f:
            stripped = line.strip()
            if line.startswith("THEOREM:"):
                current = {"steps": {}}
                proofs[stripped.split(":", 1)[1].strip()] = current
            elif line.startswith("GOAL:"):
                current["root"] = stripped[5:].strip()
            elif stripped.startswith("GOAL:"):
                goal = stripped[5:].strip()
            elif stripped.startswith("STEP:"):
                current["steps"][goal.split("]]", 1)[1].strip()] = stripped[5:].strip()
    return proofs


class ProofRejected(Exception):
    pass


def make_kernel(mmv):
    class Kernel(mmv.MM):
        """
        Reads set.mm; at each target $p it verifies the candidate proofs
        instead of (or as well as) the database's own proof.
        """

        def __init__(self, candidates: dict, grammar_db):
            super().__init__()
            self.candidates = candidates  # label -> {key: proof}
            self.grammar_db = grammar_db
            self.verdicts = {}  # (key, label) -> None (ok) or error string

        def verify(self, stat_label, stat, proof):
            for key, cand in self.candidates.get(stat_label, {}).items():
                try:
                    built = self.build(cand, stat)
                    super().verify(stat_label, stat, built)
                    self.verdicts[key, stat_label] = None
                except Exception as e:  # MMError, KeyError, ProofRejected, ...
                    self.verdicts[key, stat_label] = f"{type(e).__name__}: {e}"

        def build(self, cand, stat):
            steps = cand["steps"]
            grammar = self.grammar_db

            def var_label(tok):
                return self.fs.lookup_f(tok)

            def syntax(kind, toks):
                pf = grammar.syntax_proof(kind, tuple(toks))
                if pf is None:
                    raise ProofRejected(f"not a {kind}: {' '.join(toks)}")
                return [var_label(s[1]) if isinstance(s, tuple) else s for s in pf]

            def prove(conclusion: list, visiting: set) -> list:
                key = " ".join(conclusion)
                if key in visiting:
                    raise ProofRejected(f"circular proof at {key}")
                step = steps.get(key)
                if step is None:
                    raise ProofRejected(f"no step for {key}")
                if step == HYPOTHESIS_STEP:
                    return [self.fs.lookup_e(conclusion)]
                parsed = parse_proofstep(step)
                label, subst = parsed["theorem"], parsed["subst"]
                if label not in self.labels:
                    raise ProofRejected(f"{label} not available before this theorem")
                kind, data = self.labels[label]
                if kind not in ("$a", "$p"):
                    raise ProofRejected(f"{label} is not an assertion")
                _, mand_var, hyp, _ = data
                out = []
                for k, v in mand_var:
                    out += syntax(k, subst.get(v, []))
                visiting = visiting | {key}
                for h in hyp:
                    out += prove(self.apply_subst(h, subst), visiting)
                return out + [label]

            return prove(list(stat), set())

    return Kernel


def main():
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("proved", nargs="+", help="*_theorems_proved_*.txt files")
    parser.add_argument("--mm", default="data/set.mm")
    parser.add_argument("--mmverify", default="data/mmverify.py")
    parser.add_argument(
        "--json-output", default=None, help="Write per-theorem verdicts here"
    )
    parser.add_argument(
        "--write-sound",
        action="store_true",
        help="Write <file>.kernel_sound.txt holding only the kernel-accepted proofs",
    )
    args = parser.parse_args()

    mmv = load_mmverify(args.mmverify)
    mmv.vprint = lambda *a, **k: None

    files = {path: parse_proved_file(path) for path in args.proved}
    candidates = defaultdict(dict)
    for path, proofs in files.items():
        for label, proof in proofs.items():
            candidates[label][path] = proof

    # The grammar needs every syntax axiom up front; read the database once
    # plainly for it, then again with the kernel checking in place.
    plain = mmv.MM()
    plain.verify = lambda *a, **k: None
    with open(args.mm, encoding="utf-8", errors="replace") as f:
        plain.read(mmv.toks(f))
    grammar = Grammar(plain)

    kernel = make_kernel(mmv)(candidates, grammar)
    with open(args.mm, encoding="utf-8", errors="replace") as f:
        kernel.read(mmv.toks(f))

    report = {}
    for path, proofs in files.items():
        verdicts = {
            label: kernel.verdicts.get((path, label), "target theorem not found in database")
            for label in proofs
        }
        accepted = [label for label, v in verdicts.items() if v is None]
        report[path] = verdicts
        print(f"{path}: {len(accepted)}/{len(proofs)} accepted by the kernel")
        for label, v in verdicts.items():
            if v is not None:
                print(f"    REJECTED {label}: {v[:160]}")
        if args.write_sound:
            out = os.path.splitext(path)[0] + ".kernel_sound.txt"
            blocks = open(path, encoding="utf-8").read().split("THEOREM:")[1:]
            with open(out, "w", encoding="utf-8") as f:
                for block in blocks:
                    if block.split("\n", 1)[0].strip() in accepted:
                        f.write("THEOREM:" + block)

    if args.json_output:
        with open(args.json_output, "w") as f:
            json.dump(report, f, indent=1)


if __name__ == "__main__":
    sys.setrecursionlimit(10000)
    main()

#!/usr/bin/env python3
"""
extractor.py
============

Extract supervised training examples from a Metamath database.

Each training example consists of

    GOAL
        [[ essential hypotheses ]] conclusion

    TARGET
        theorem_label {{ variable : substitution }} ...

The theorem label is the theorem applied at that proof step.
The substitution maps the theorem's mandatory variables to the
expressions used in that application.

The verifier can reconstruct the resulting subgoals directly from
(label, substitution), so they are not stored in the dataset.

  uv run python extractor.py --mm set.mm --output proof_steps.jsonl
  uv run python extractor.py --mm set.mm --output proof_steps.jsonl --training training.txt
  uv run python extractor.py --mm set.mm --output proof_steps.jsonl --limit 100 --verbose
"""

import argparse
import importlib.util
import itertools
import json
import os
import sys
import pandas as pd


# ------------------------------------------------------------
# Load mmverify
# ------------------------------------------------------------
def load_mmverify(path: str):
    spec = importlib.util.spec_from_file_location("mmverify", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


# ------------------------------------------------------------
# Formatting helpers
# ------------------------------------------------------------
def tokens_to_str(tokens):
    return " ".join(tokens)


def format_goal(e_hyps, conclusion):
    if e_hyps:
        hyps = "   ".join(tokens_to_str(h) for h in e_hyps)
        return f"[[ {hyps} ]] {tokens_to_str(conclusion)}"
    return f"[[ ]] {tokens_to_str(conclusion)}"


def format_target(label, subst):
    """
    Convert
        label
        subst

    into
        ax-mp {{ ph : ph }} {{ ps : ch }}
    """
    subst_parts = []

    for var in sorted(subst):
        if value := subst[var]:
            subst_parts.append(f"{{{{ {var} : {tokens_to_str(value)} }}}}")

    if subst_parts:
        return label + " " + " ".join(subst_parts)

    return label


def write_training_example(train_file, goal, label, subst):
    target = format_target(label, subst)
    train_file.write(f"GOAL {goal} " f"PROOFSTEP {target}" "<|endoftext|>\n")


# ------------------------------------------------------------
# Recording MM
# ------------------------------------------------------------
def make_recording_mm(mmv):
    class RecordingMM(mmv.MM):
        """
        MM subclass that records every theorem application.

        Each record contains

            goal
            theorem label
            substitution

        which is all the prover needs for training.
        """

        def __init__(self, records_list, json_out=None, train_out=None):
            super().__init__()
            self.records_list = records_list
            self.json_out = json_out
            self.train_out = train_out
            self.step_count = 0

        def verify(self, stat_label, stat, proof):
            stack = []
            if proof[0] == "(":
                proof = self.decompress_proof(stat, proof)
            theorem_e_hyps = [list(eh) for frame in self.fs for eh in frame.e]

            for label in proof:
                step_type, step_data = self.labels[label]
                if step_type in ("$a", "$p"):
                    distinct, mand_var, hyp, result = step_data
                    npop = len(mand_var) + len(hyp)
                    sp = len(stack) - npop

                    if sp < 0:
                        raise mmv.MMError(f"stack underflow in {stat_label}")

                    # Build substitution
                    subst = {}
                    sp2 = sp

                    for kind, var in mand_var:
                        entry = stack[sp2]
                        if entry[0] != kind:
                            raise mmv.MMError(f"mandatory variable mismatch {entry}")

                        subst[var] = entry[1:]
                        sp2 += 1

                    # Distinct variable conditions
                    for x, y in distinct:
                        x_vars = self.find_vars(subst[x])
                        y_vars = self.find_vars(subst[y])
                        for xv, yv in itertools.product(x_vars, y_vars):
                            if xv == yv:
                                raise mmv.MMError(f"disjoint violation {xv}")
                            if not self.fs.lookup_d(xv, yv):
                                raise mmv.MMError(f"disjoint violation {xv}, {yv}")

                    # Verify essential hypotheses
                    for h in hyp:
                        entry = stack[sp2]
                        expected = self.apply_subst(h, subst)
                        if entry != expected:
                            raise mmv.MMError("essential hypothesis mismatch")
                        sp2 += 1

                    # Compute instantiated conclusion
                    conclusion = self.apply_subst(result, subst)

                    # Ignore syntax/type derivations
                    if not conclusion or conclusion[0] != "|-":
                        del stack[len(stack) - npop :]
                        stack.append(conclusion)
                        continue

                    # Record training example
                    goal = format_goal(theorem_e_hyps, conclusion)

                    record = {
                        "proof_label": stat_label,
                        "goal": goal,
                        "theorem": label,
                        "substitution": subst,
                    }

                    self.records_list.append(record)
                    if self.json_out:
                        self.json_out.write(json.dumps(record) + "\n")

                    if self.train_out:
                        write_training_example(self.train_out, goal, label, subst)

                    self.step_count += 1

                    # Update stack
                    del stack[len(stack) - npop :]
                    stack.append(conclusion)

                elif step_type in ("$e", "$f"):
                    stack.append(step_data)

            # Final verification
            if len(stack) != 1:
                raise mmv.MMError(f"stack has {len(stack)} entries")

            if stack[0] != stat:
                raise mmv.MMError("proved statement does not match")

    return RecordingMM


# ------------------------------------------------------------
# Core extraction function
# ------------------------------------------------------------
def extract_proof_steps(
    mm_path, mmverify_path=None, verbose=False, jsonl_output=None, training_output=None
) -> pd.DataFrame:
    """
    Extract proof steps from a Metamath database.

    Args:
        mm_path: Path to set.mm
        mmverify_path: Path to mmverify.py (optional, auto-detected)
        verbose: Print progress messages
        jsonl_output: Path to save JSONL file (optional)
        training_output: Path to save training text file (optional)

    Returns:
        pandas.DataFrame with columns: proof_label, goal, theorem, substitution
    """
    # Locate mmverify.py
    if mmverify_path is None:
        mmverify_path = os.path.join(
            os.path.dirname(__file__),
            "mmverify.py",
        )

    if not os.path.exists(mmverify_path):
        print(f"Could not find {mmverify_path}")
        sys.exit(1)

    # Load mmverify
    if verbose:
        print(f"Loading {mmverify_path}")
    mmv = load_mmverify(mmverify_path)
    mmv.verbosity = 1 if verbose else 0

    RecordingMM = make_recording_mm(mmv)

    if verbose:
        print(f"Reading {mm_path}")

    records = []

    json_out = None
    train_out = None

    try:
        if jsonl_output:
            json_out = open(jsonl_output, "w", encoding="utf-8")
            if verbose:
                print(f"Writing JSONL to {jsonl_output}")

            if training_output:
                train_out = open(training_output, "w", encoding="utf-8")
                if verbose:
                    print(f"Writing training text to {training_output}")

        mm = RecordingMM(
            records_list=records,
            json_out=json_out,
            train_out=train_out,
        )

        with open(mm_path, "r", encoding="utf-8", errors="replace") as mm_file:
            mm.read(mmv.toks(mm_file))
    finally:
        if json_out:
            json_out.close()
        if train_out:
            train_out.close()

    df = pd.DataFrame(records)

    if verbose:
        print("\nFinished.")
        print(f"Proof steps extracted: {mm.step_count:,}")
        print(f"DataFrame shape: {df.shape}")

    return df


# ------------------------------------------------------------
# CLI Main
# ------------------------------------------------------------
def main():
    parser = argparse.ArgumentParser(
        description="Extract supervised Metamath training data."
    )
    parser.add_argument(
        "--mm",
        required=True,
        help="Path to set.mm",
    )
    parser.add_argument(
        "--mmverify",
        default=None,
        help="Path to mmverify.py",
    )
    parser.add_argument(
        "--output",
        required=True,
        help="Output JSONL file",
    )
    parser.add_argument(
        "--training",
        default=None,
        help="Optional training text file",
    )
    parser.add_argument(
        "--verbose",
        action="store_true",
    )
    args = parser.parse_args()

    df = extract_proof_steps(
        mm_path=args.mm,
        mmverify_path=args.mmverify,
        verbose=args.verbose,
        jsonl_output=args.output,
        training_output=args.training,
    )
    print(f"Returned DataFrame with {len(df)} rows")


if __name__ == "__main__":
    main()

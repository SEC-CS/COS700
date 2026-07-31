#!/usr/bin/env python3
"""
extract_proof_steps.py
======================
Extracts proof steps from set.mm using mmverify.py as the execution engine.

This script subclasses mmverify's MM class and overrides the verify() method
to record each proof step as it happens during verification. Because we are
piggybacking on mmverify's correct implementation, all of the following are
handled correctly for free:
  - Compressed proof decompression
  - Mandatory hypothesis ordering
  - Substitution building and application
  - Scope and frame management

Output formats:
  - proof_steps.jsonl : one JSON record per proof step
  - training.txt      : one training string per proof step (optional)

Usage:
  python extract_proof_steps.py --mm set.mm --output proof_steps.jsonl
  python extract_proof_steps.py --mm set.mm --output proof_steps.jsonl --training training.txt
  python extract_proof_steps.py --mm set.mm --output proof_steps.jsonl --limit 100 --verbose

Requirements:
  mmverify.py must be in the same directory as this script.
"""

import sys
import json
import hashlib
import argparse
import itertools
import collections
import os
import os.path

# ---------------------------------------------------------------------------
# Import mmverify — we need its internals
# ---------------------------------------------------------------------------

# mmverify prints to stderr during normal operation. We silence it by
# temporarily setting verbosity to 0 while loading.
import importlib.util

def load_mmverify(path: str):
    spec = importlib.util.spec_from_file_location("mmverify", path)
    mod  = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod

# ---------------------------------------------------------------------------
# Helper formatting functions
# ---------------------------------------------------------------------------

def tokens_to_str(tokens) -> str:
    """Join a token list into a readable string."""
    return ' '.join(tokens)


def format_goal(e_hyps, conclusion) -> str:
    """
    Format a goal in GPT-f style:
      [[ |- hyp1   |- hyp2 ]] |- conclusion
    or if no hypotheses:
      [[ ]] |- conclusion
    """
    if e_hyps:
        hyp_str = '   '.join(tokens_to_str(h) for h in e_hyps)
        return f"[[ {hyp_str} ]] {tokens_to_str(conclusion)}"
    else:
        return f"[[ ]] {tokens_to_str(conclusion)}"


def format_proofstep(applied_e_hyps, conclusion, subst) -> str:
    """
    Format a proof step in GPT-f style:
      [[ |- hyp1   |- hyp2 ]] |- conclusion {{ var1 : val1 }} {{ var2 : val2 }}

    applied_e_hyps: the essential hypotheses of the applied theorem
                    (after substitution) — these are the new subgoals
    conclusion:     the conclusion of the applied theorem (after substitution)
    subst:          dict mapping variable name -> token list
    """
    if applied_e_hyps:
        hyp_str = '   '.join(tokens_to_str(h) for h in applied_e_hyps)
        hyp_part = f"[[ {hyp_str} ]] "
    else:
        hyp_part = "[[ ]] "

    conc_part = tokens_to_str(conclusion)

    subst_parts = [
        f"{{{{ {var} : {tokens_to_str(val)} }}}}"
        for var, val in sorted(subst.items())
        if val  # skip empty substitutions
    ]
    subst_str = (' ' + ' '.join(subst_parts)) if subst_parts else ''

    return f"{hyp_part}{conc_part}{subst_str}"


def make_hash(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()[:16]


def to_training_sequence(record: dict) -> str:
    return (f"GOAL {record['goal']} "
            f"PROOFSTEP {record['proof_step']}<|endoftext|>")


# ---------------------------------------------------------------------------
# Subclassed MM with recording
# ---------------------------------------------------------------------------

def make_recording_mm(mmv):
    """
    Factory that creates a RecordingMM class using the given mmverify module.
    We use a factory so we can reference mmv.MM as the base class dynamically.
    """

    class RecordingMM(mmv.MM):
        """
        MM subclass that intercepts verify() to record proof steps.

        For each theorem being verified, we capture every $a/$p application
        and record:
          - The current goal (what we are trying to prove at this point)
          - The proof step (which theorem was applied + substitutions)
        """

        def __init__(self, out_f, train_f=None):
            super().__init__()
            # Write directly to disk — no in-memory accumulation
            self._out_f   = out_f    # jsonl output file handle
            self._train_f = train_f  # training txt file handle (optional)
            self._step_count = 0     # running total for progress reporting

        def verify(self, stat_label: str, stat: list, proof: list):
            """
            Override of mmverify's verify().

            We replicate the logic of the original but add recording at the
            point where each step's substitution is fully resolved.

            The original verify() is defined as:

                def verify(self, stat_label, stat, proof):
                    stack = []
                    if proof[0] == '(': proof = self.decompress_proof(...)
                    for label in proof:
                        steptyp, stepdat = self.labels[label]
                        if steptyp in ('$a', '$p'):
                            ... build subst from stack ...
                            ... verify hyps ...
                            del stack[...]
                            stack.append(apply_subst(result, subst))
                        elif steptyp in ('$e', '$f'):
                            stack.append(stepdat)

            We add recording right after subst is built and hyps are verified,
            which is the exact same information the paper's dataset contains.
            """
            stack = []
            stat_type = stat[0]

            # Decompress if needed — this uses mmverify's correct implementation
            if proof[0] == '(':
                proof = self.decompress_proof(stat, proof)

            # The essential hypotheses of the theorem being proved.
            # These appear in [[ ]] in the goal string.
            # We get them from the frame stack at this point in parsing,
            # which is exactly when this theorem's scope is active.
            theorem_e_hyps = [list(eh) for fr in self.fs for eh in fr.e]

            # Steps are written to disk immediately — no list accumulation

            for label in proof:
                steptyp, stepdat = self.labels[label]

                if steptyp in ('$a', '$p'):
                    (distinct, mand_var, hyp, result) = stepdat

                    npop = len(mand_var) + len(hyp)
                    sp = len(stack) - npop

                    if sp < 0:
                        raise mmv.MMError(
                            f'stack underflow in {stat_label}')

                    # --- Build substitution (same as mmverify) ---
                    subst = {}
                    sp2 = sp
                    for (k, v) in mand_var:
                        entry = stack[sp2]
                        if entry[0] != k:
                            raise mmv.MMError(
                                f"stack entry {entry} doesn't match "
                                f"mandatory var hyp ({k}, {v})")
                        subst[v] = entry[1:]
                        sp2 += 1

                    # --- Verify distinct variable conditions ---
                    for x, y in distinct:
                        x_vars = self.find_vars(subst[x])
                        y_vars = self.find_vars(subst[y])
                        for xv, yv in itertools.product(x_vars, y_vars):
                            if xv == yv or not self.fs.lookup_d(xv, yv):
                                raise mmv.MMError(
                                    f"disjoint violation: {xv}, {yv}")

                    # --- Verify essential hypotheses (same as mmverify) ---
                    for h in hyp:
                        entry = stack[sp2]
                        subst_h = self.apply_subst(h, subst)
                        if entry != subst_h:
                            raise mmv.MMError(
                                f"stack entry {entry} doesn't match "
                                f"hypothesis {subst_h}")
                        sp2 += 1

                    # --- Compute conclusion ---
                    conclusion = self.apply_subst(result, subst)

                    # -------------------------------------------------------
                    # RECORDING POINT
                    # At this exact moment:
                    #   subst      = complete variable substitution mapping
                    #   conclusion = what this step proves (after substitution)
                    #   hyp        = essential hyp templates of applied theorem
                    #   label      = name of the theorem being applied
                    # -------------------------------------------------------

                    # The applied theorem's essential hypotheses after subst
                    # — these are the new subgoals this step generates
                    applied_e_hyps = [
                        self.apply_subst(h, subst)
                        for h in hyp
                    ]

                    # Skip type-checking steps ($f style conclusions).
                    # Real proof steps always start with |- (the provability
                    # marker). Steps whose conclusion starts with wff, set,
                    # class etc. are just Metamath bookkeeping and were not
                    # included in the GPT-f dataset.
                    if not conclusion or conclusion[0] != '|-':
                        del stack[len(stack) - npop:]
                        stack.append(conclusion)
                        continue

                    # The goal is the conclusion of this step — what we just proved.
                    # The theorem's own essential hyps form the [[ ]] context.
                    goal_str = format_goal(theorem_e_hyps, conclusion)
                    step_str = format_proofstep(applied_e_hyps, conclusion,
                                                subst)

                    record = {
                        'proof_label':     stat_label,
                        'goal':            goal_str,
                        'proof_step':      step_str,
                        'proof_step_hash': make_hash(step_str),
                        'parent_hash':     [make_hash(goal_str)],
                    }
                    self._out_f.write(json.dumps(record) + '\n')
                    if self._train_f:
                        self._train_f.write(to_training_sequence(record) + '\n')
                    self._step_count += 1

                    # --- Update stack (same as mmverify) ---
                    del stack[len(stack) - npop:]
                    stack.append(conclusion)

                elif steptyp in ('$e', '$f'):
                    stack.append(stepdat)

            # Final checks (same as mmverify)
            if len(stack) != 1:
                raise mmv.MMError(
                    f'stack has {len(stack)} entries at end of {stat_label}')
            if stack[0] != stat:
                raise mmv.MMError(
                    f"proved statement doesn't match in {stat_label}")

            # Steps were written to disk as they were recorded

    return RecordingMM


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description='Extract proof steps from set.mm using mmverify.py'
    )
    parser.add_argument('--mm',       required=True,
                        help='Path to set.mm')
    parser.add_argument('--mmverify', default=None,
                        help='Path to mmverify.py (default: same dir as this script)')
    parser.add_argument('--output',   required=True,
                        help='Output .jsonl file for proof step records')
    parser.add_argument('--training', default=None,
                        help='Output .txt file for training sequences (optional)')
    parser.add_argument('--verbose',  action='store_true',
                        help='Show per-theorem verification messages')
    args = parser.parse_args()

    # --- Find mmverify.py ---
    if args.mmverify:
        mmverify_path = args.mmverify
    else:
        mmverify_path = os.path.join(os.path.dirname(__file__), 'mmverify.py')

    if not os.path.exists(mmverify_path):
        print(f"ERROR: mmverify.py not found at {mmverify_path}")
        print("Either put mmverify.py in the same directory as this script,")
        print("or specify its location with --mmverify <path>")
        sys.exit(1)

    # --- Load mmverify ---
    print(f"Loading mmverify from {mmverify_path} ...")
    mmv = load_mmverify(mmverify_path)

    # Silence mmverify's per-theorem progress messages unless verbose
    if not args.verbose:
        mmv.verbosity = 0

    # --- Build the recording MM and open output files ---
    RecordingMM = make_recording_mm(mmv)

    print(f"Reading and verifying {args.mm} ...")
    print("(This will take a few minutes — mmverify checks every proof)")
    print(f"Writing records to {args.output} as they are verified ...")

    errors = 0
    theorems_ok = 0

    # Open output files up front — records are written immediately as each
    # proof step is verified, so memory usage stays flat throughout.
    with open(args.output, 'w', encoding='utf-8') as out_f:
        train_f = open(args.training, 'w', encoding='utf-8') if args.training else None
        try:
            mm = RecordingMM(out_f, train_f)
            mmv.verbosity = 0 if not args.verbose else 1

            # Wrap verify() to catch per-theorem errors without halting
            original_verify = mm.verify
            def safe_verify(stat_label, stat, proof):
                nonlocal errors, theorems_ok
                try:
                    original_verify(stat_label, stat, proof)
                    theorems_ok += 1
                    if args.verbose:
                        print(f"  OK: {stat_label} "
                              f"(total steps: {mm._step_count:,})")
                except Exception as e:
                    errors += 1
                    if args.verbose:
                        print(f"  ERROR: {stat_label}: {e}", file=sys.stderr)
            mm.verify = safe_verify

            with open(args.mm, 'r', encoding='utf-8', errors='replace') as mm_f:
                mm.read(mmv.toks(mm_f))

        finally:
            if train_f:
                train_f.close()

    print(f"\nDone.")
    print(f"  Theorems verified OK : {theorems_ok:,}")
    print(f"  Theorems with errors : {errors:,}")
    print(f"  Proof steps recorded : {mm._step_count:,}")
    print(f"  JSON records         : {args.output}")
    if args.training:
        print(f"  Training txt         : {args.training}")


if __name__ == '__main__':
    main()

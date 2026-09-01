#!/usr/bin/env python
"""
premise_search.py
==================
A lighter-weight companion to proof_search.py that measures premise
selection in isolation: for each theorem in a split, whether the exact
correct next step, built straight from that record's own "theorem"
and "substitution", shows up anywhere among the model's sampled
candidates for the root goal. Not whether a full proof gets found.

Why this exists: proof_search.py's success rate conflates two very
different skills -- picking the right premise/theorem for a goal, and
correctly chaining many such choices together across subgoals (search
exploration, sampling variance compounding across expansions, dead
ends, etc). When the full search is doing badly, it's hard to tell
which of those is actually the weak link, or whether a change to the
data or model even moved the needle on either one. This script isolates
the first skill: exactly one generate_steps() call per goal -- the same
first-expansion call proof_search() would make on the root goal -- and
an exact string match against the known-correct step. No subgoals, no
recursive search, no expansion budget, no verifier round-trips: one
call, one comparison, per theorem. Re-run this after each data/model/
decoding change as a cheaper, more specific signal than the end-to-end
proof-search success rate.

Usage
-----

    Example: Sample 48 candidates per goal, write hits to found_premises.txt, and print a running summary:
    python premise_search.py --mm data/set.mm --eval data/valid.jsonl --model-module model.py --tactics 48 --verbose      

"""

import argparse
import json
import time

from proof_search import load_mmverify, load_model_from_module


def format_proofstep(theorem: str, substitution: dict) -> str:
    """
    Build the target PROOFSTEP text from a record's theorem + substitution
    fields: "theorem_label {{ var1 : val1 }} {{ var2 : val2 }} ...".

    Kept byte-for-byte identical to format_proofstep() in train_model.py
    and to check_lengths.py's copy of the same function -- all three
    need to agree on exactly what string shape a proofstep target is.
    If you change the format in one place, change it in the other two.
    """
    subst_str = ' '.join(f"{{{{ {v} : {' '.join(val)} }}}}"
                          for v, val in sorted(substitution.items()) if val)
    return f"{theorem}" + (f" {subst_str}" if subst_str else "")


def load_split(split_file: str) -> list[dict]:
    """
    Reads one record per theorem's ROOT goal
    """
    theorems = {}
    order = []
    with open(split_file) as f:
        for line_no, line in enumerate(f, start=1):
            line = line.strip()
            if not line:
                continue
            record = json.loads(line)
            label = record.get('proof_label')
            if label is None:
                raise KeyError(
                    f"{split_file}:{line_no} has no 'proof_label' field "
                    f"-- this record only has these keys: "
                    f"{sorted(record.keys())}"
                )
            if label not in theorems:
                order.append(label)
            theorems[label] = record  # last occurrence wins
    return [theorems[label] for label in order]


def evaluate_premise_selection(
    model,
    split_file:  str,
    n_tactics:   int  = 32,
    limit:       int  = None,
    output_path: str  = None,
    verbose:     bool = False,
) -> dict:
 
    theorems = load_split(split_file)
    if limit is not None:
        theorems = theorems[:limit]
    total = len(theorems)

    out_file = open(output_path, 'w') if output_path else None

    hits = 0
    total_time = 0.0
    results = []

    print(f"\nChecking premise selection on {total} theorem(s) "
          f"({n_tactics} candidates each) ...")

    for i, record in enumerate(theorems):
        label        = record['proof_label']
        root_goal    = record['goal']
        target_step  = format_proofstep(record['theorem'], record['substitution'])

        start = time.time()
        candidates = model.generate_steps(root_goal, n=n_tactics, temperature=1.0)
        elapsed = time.time() - start
        total_time += elapsed

        candidate_texts = [text for text, _ in candidates]
        found = target_step in candidate_texts

        if verbose:
            print(f"[{i+1}/{total}] {label}: "
                  f"{'HIT' if found else 'miss'} "
                  f"({len(candidates)} candidates, {elapsed:.2f}s)")

        if found:
            hits += 1
            if out_file is not None:
                out_file.write(
                    f"THEOREM: {label}\n"
                    f"GOAL: {root_goal}\n"
                    f"STEP: {target_step}\n\n"
                )

        results.append({
            'proof_label': label,
            'found':       found,
            'n_candidates': len(candidates),
            'time_s':      elapsed,
        })

        if (i + 1) % 20 == 0:
            pct = hits / (i + 1) * 100
            print(f"  [{i+1}/{total}] found={hits} ({pct:.1f}%)")

    if out_file is not None:
        out_file.close()

    hit_rate = (hits / total * 100) if total else 0.0
    avg_time = (total_time / total) if total else 0.0

    summary = {
        'total_theorems':   total,
        'premises_found':   hits,
        'premise_hit_rate_%': round(hit_rate, 2),
        'avg_time_s':       round(avg_time, 4),
    }

    print(f"\n{'='*60}")
    print(f"Premise selection results")
    print(f"{'='*60}")
    print(f"  Theorems checked : {total}")
    print(f"  Premises found   : {hits} ({hit_rate:.2f}%)")
    print(f"  Avg time/theorem : {avg_time:.3f}s")
    if output_path:
        print(f"  Hits written to  : {output_path}")
    print(f"{'='*60}")

    return summary, results


def main():
    parser = argparse.ArgumentParser(
        description='Measure premise selection in isolation: does the '
                     "exact correct first step show up among the model's "
                     'sampled candidates for a goal, independent of '
                     'whether a full proof search would ever find it.'
    )
    parser.add_argument('--mm',           required=True,
                         help='Path to set.mm')
    parser.add_argument('--mmverify',     default="data/mmverify.py",
                         help='Path to mmverify.py (default: same dir)')
    parser.add_argument('--model-module', required=True,
                         help='Path to Python file defining Model class')
    parser.add_argument('--eval',         required=True,
                         help='Split file to check, e.g. valid.jsonl')
    parser.add_argument('--tactics',      type=int, default=32,
                         help='Candidates to sample per goal (default: 32)')
    parser.add_argument('--limit',        type=int, default=None,
                         help='Only check the first N theorems in the '
                              'split (default: all)')
    parser.add_argument('--output',       default='found_premises.txt',
                         help='Where to write successfully-found '
                              '(goal, step) pairs (default: '
                              'found_premises.txt)')
    parser.add_argument('--verbose',      action='store_true')
    args = parser.parse_args()

    # mmverify/set.mm aren't actually used for the exact-match check
    # itself -- only load_model_from_module()'s signature needs an `mm`
    # object to hand to Model.set_mm() for any model implementation
    # that wants it (this repo's model.py doesn't, but the loader
    # convention is shared with proof_search.py, so this stays
    # consistent rather than silently skipping it for some models).
    mmverify_path = args.mmverify
    print(f"Loading mmverify from {mmverify_path} ...")
    mmv = load_mmverify(mmverify_path)

    print(f"Loading {args.mm} ...")
    mm = mmv.MM()
    with open(args.mm, 'r', encoding='utf-8', errors='replace') as f:
        mm.read(mmv.toks(f))
    print("Database loaded.")

    model = load_model_from_module(args.model_module, mm)

    evaluate_premise_selection(
        model=model,
        split_file=args.eval,
        n_tactics=args.tactics,
        limit=args.limit,
        output_path=args.output,
        verbose=args.verbose,
    )


if __name__ == '__main__':
    main()
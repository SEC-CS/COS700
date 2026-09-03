#!/usr/bin/env python
"""
subsample_train.py
===================
Produces a representative subset of train.jsonl by sampling a fraction
of its theorems spread evenly across set.mm's complexity ordering --
the same bucketing idea split_dataset uses for validation/test --
instead of truncating to the first N lines (which --max-train-samples
in train_model.py does, and which skews toward the simplest, earliest
theorems in the file).

Use this when you want a bounded, faster-to-train dataset that still
represents the full range of theorem difficulty, e.g. for an interim
evaluation run before committing to the full dataset.

Usage:
    python finetuning/scripts/subsample_train.py --input finetuning/data/train.jsonl \
        --output finetuning/data/train_subset.jsonl --fraction 0.15
"""

import argparse
import json


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", required=True)
    parser.add_argument("--output", required=True)
    parser.add_argument("--fraction", type=float, required=True,
                         help="Fraction of theorems to keep, e.g. 0.15 "
                              "for roughly 15%%")
    args = parser.parse_args()

    # Pass 1: theorem labels in order of first appearance (= complexity
    # order, same reasoning as split_dataset.py).
    label_order = []
    seen = set()
    with open(args.input) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            label = json.loads(line)["proof_label"]
            if label not in seen:
                seen.add(label)
                label_order.append(label)

    n_theorems = len(label_order)
    n_buckets = max(1, round(n_theorems * args.fraction))
    bucket_edges = [round(i * n_theorems / n_buckets) for i in range(n_buckets + 1)]

    kept = set()
    for b in range(n_buckets):
        start, end = bucket_edges[b], bucket_edges[b + 1]
        if start >= end:
            continue
        mid = (start + end - 1) // 2  # deterministic pick: bucket midpoint
        kept.add(label_order[mid])

    print(f"Theorems in input : {n_theorems}")
    print(f"Theorems kept     : {len(kept)} ({len(kept) / n_theorems:.1%})")

    # Pass 2: stream through, keeping only steps from kept theorems.
    n_steps = 0
    with open(args.input) as f_in, open(args.output, "w") as f_out:
        for line in f_in:
            line = line.strip()
            if not line:
                continue
            record = json.loads(line)
            if record["proof_label"] in kept:
                f_out.write(json.dumps(record) + "\n")
                n_steps += 1

    print(f"Steps written     : {n_steps} -> {args.output}")


if __name__ == "__main__":
    main()
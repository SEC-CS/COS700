#!/usr/bin/env python
"""
Build a smaller training set by sampling a fraction of theorems spread evenly across set.mm's
complexity ordering, rather than truncating to the first N lines.
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
        mid = (start + end - 1) // 2
        kept.add(label_order[mid])

    print(f"Theorems in input : {n_theorems}")
    print(f"Theorems kept     : {len(kept)} ({len(kept) / n_theorems:.1%})")

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
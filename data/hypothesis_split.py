#!/usr/bin/env python3
"""
Keep only the theorems that have hypotheses ($e statements), i.e. whose root
goal's [[ ... ]] block is non-empty, from one or more proof-step JSONL splits.

"""

import argparse
import json
from collections import defaultdict


def has_hypotheses(goal: str) -> bool:
    return goal.split("]]", 1)[0].replace("[[", "").strip() != ""


def filter_split(in_path: str, out_path: str) -> list[str]:
    records = defaultdict(list)
    order = []
    with open(in_path) as f:
        for line in f:
            if not line.strip():
                continue
            label = json.loads(line)["proof_label"]
            if label not in records:
                order.append(label)
            records[label].append(line)

    # The last record of a proof is the step that concludes the theorem,
    # which is also the root goal proof search starts from.
    keep = [
        label for label in order if has_hypotheses(json.loads(records[label][-1])["goal"])
    ]
    with open(out_path, "w") as f:
        for label in keep:
            f.writelines(records[label])
    print(f"{in_path}: kept {len(keep)}/{len(order)} theorems with hypotheses -> {out_path}")
    return keep


def main() -> None:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument(
        "--split",
        nargs=2,
        action="append",
        required=True,
        metavar=("IN", "OUT"),
        help="Input split and where to write its hypothesis-only subset",
    )
    args = parser.parse_args()

    kept = [filter_split(src, dst) for src, dst in args.split]
    for (src, _), labels in zip(args.split[1:], kept[1:]):
        if labels != kept[0]:
            raise SystemExit(
                f"{src} selects different theorems from {args.split[0][0]}"
            )


if __name__ == "__main__":
    main()

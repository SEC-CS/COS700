#!/usr/bin/env python3
"""
Convert proof-step JSONL splits into "label + residual" training targets.

Usage
-----
Run from the repository root.
    # one split
    python -m residuals.data.residualise \\
        --split data/01_CLASSICAL_FIRST-ORDER_LOGIC_WITH_EQUALITY/train.jsonl
    # a whole section, writing <split>.residual.jsonl next to each input
    python -m residuals.data.residualise --split .\baseline\data\datasets\longest_theorems\train.jsonl .\baseline\data\datasets\longest_theorems\valid.jsonl .\baseline\data\datasets\longest_theorems\test.jsonl --out-dir residuals/data/longest_theorems

Note: 

The first run parses set.mm (~100s) and caches the label table; later runs
load the cache. Pass --rebuild after set.mm changes.
"""

import argparse
import collections
import json
import statistics
from pathlib import Path

from baseline.utils.formatting import format_proofstep
from residuals.utils.matcher import (
    DEFAULT_CACHE,
    DEFAULT_CAP,
    DEFAULT_MM,
    DEFAULT_MMVERIFY,
    complete,
    determined_key,
    label_table,
)

CLASSES = ("strip", "ranked", "full")


# ---------------------------------------------------------------------------
# The transform
# ---------------------------------------------------------------------------


def residualise(record: dict, table: dict, cap: int = DEFAULT_CAP) -> tuple:
    """
    -> (target, klass, rank)

    `rank` is the 1-based position of the correct substitution among the
    matcher's distinct solutions, or 0 when it is not among them (klass
    "full"). For klass "strip" it is always 1.
    """
    info = table[record["theorem"]]
    subst = record["substitution"]
    rvars = info["rvars"]

    # What the matcher is responsible for recovering, per the ground truth.
    # Older extracted datasets can omit mandatory variables that the current
    # database exposes in the assertion.
    truth = determined_key(
        {v: subst[v] for v in rvars if v in subst}, rvars
    )

    solutions = []
    for candidate in complete(
        info["result"], record["goal"].split("]]", 1)[1].split(), info["kinds"], cap=cap
    ):
        key = determined_key(candidate, rvars)
        if key not in solutions:
            solutions.append(key)

    if truth not in solutions:
        # Unrecoverable, should not happen on clean data.
        step = format_proofstep(record["theorem"], subst)
        return step, "full", 0

    residual = {v: val for v, val in subst.items() if v not in rvars}
    rank = solutions.index(truth) + 1
    klass = "strip" if rank == 1 else "ranked"
    return format_proofstep(record["theorem"], residual), klass, rank


def convert(
    split_path, table: dict, out_path=None, cap: int = DEFAULT_CAP
) -> tuple[list, collections.Counter]:
    """
    Stream one split through `residualise`.

    Each output record is the input record plus `target`, `target_class`
    and `match_rank`. The original `theorem` and `substitution` fields are
    left intact, so the same file can still train a full-substitution
    baseline for the ablation.
    """
    rows = []
    counts = collections.Counter()
    out = open(out_path, "w") if out_path else None
    try:
        with open(split_path) as f:
            for line_no, line in enumerate(f, start=1):
                line = line.strip()
                if not line:
                    continue
                record = json.loads(line)
                for field in ("theorem", "substitution", "goal"):
                    if field not in record:
                        raise KeyError(
                            f"{split_path}:{line_no} has no {field!r} field "
                            f"-- keys present: {sorted(record)}"
                        )
                if record["theorem"] not in table:
                    raise KeyError(
                        f"{split_path}:{line_no} applies {record['theorem']!r}, "
                        f"which is not an $a/$p assertion in the label table "
                        f"-- is the table stale? re-run with --rebuild"
                    )
                target, klass, rank = residualise(record, table, cap=cap)
                counts[klass] += 1
                rows.append((record, target, klass, rank))
                if out:
                    out.write(
                        json.dumps(
                            {
                                **record,
                                "target": target,
                                "target_class": klass,
                                "match_rank": rank,
                            }
                        )
                        + "\n"
                    )
    finally:
        if out:
            out.close()
    return rows, counts


# ---------------------------------------------------------------------------
# Reporting
# ---------------------------------------------------------------------------


def report(split_path, rows, counts, samples: int = 2) -> None:
    n = len(rows)
    if not n:
        print(f"{split_path}: empty")
        return

    print(f"\n{split_path}: {n} steps")
    for klass in CLASSES:
        print(f"  {klass:<7} {counts[klass]:>7}  {counts[klass] / n:7.2%}")

    before = [
        len(format_proofstep(r["theorem"], r["substitution"]).split())
        for r, *_ in rows
    ]
    after = [len(t.split()) for _, t, _, _ in rows]
    print(
        f"\n  target ws-tokens  before  mean {statistics.mean(before):6.1f}"
        f"  median {statistics.median(before):6.1f}"
    )
    print(
        f"                     after  mean {statistics.mean(after):6.1f}"
        f"  median {statistics.median(after):6.1f}"
    )
    print(f"  target tokens saved      {1 - sum(after) / sum(before):7.1%}")

    ranks = [rank for _, _, klass, rank in rows if klass == "ranked"]
    if ranks:
        print(
            f"  substitution candidates search must try, on the "
            f"{len(ranks)} ranked steps: max {max(ranks)}, "
            f"mean {statistics.mean(ranks):.1f}"
        )

    if samples:
        print("\n  samples:")
        shown = collections.Counter()
        for record, target, klass, rank in rows:
            if shown[klass] >= samples:
                continue
            shown[klass] += 1
            print(f"    [{klass}/{rank}] {record['proof_label']}")
            print(f"       goal   {_clip(record['goal'])}")
            print(
                f"       before "
                f"{_clip(format_proofstep(record['theorem'], record['substitution']))}"
            )
            print(f"       after  {_clip(target)}")
            if sum(shown.values()) >= samples * len(CLASSES):
                break


def _clip(s: str, width: int = 96) -> str:
    return s if len(s) <= width else s[: width - 1] + "…"


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def main() -> None:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument(
        "--split",
        required=True,
        nargs="+",
        help="One or more proof-step JSONL files to convert",
    )
    parser.add_argument(
        "--out-dir",
        default=None,
        help="Write <name>.residual.jsonl here for each input split. "
        "Omit to report statistics without writing anything.",
    )
    parser.add_argument("--mm", default=DEFAULT_MM, help="Path to set.mm")
    parser.add_argument("--mmverify", default=DEFAULT_MMVERIFY)
    parser.add_argument(
        "--cache", default=DEFAULT_CACHE, help="Label-table pickle path"
    )
    parser.add_argument(
        "--rebuild",
        action="store_true",
        help="Re-parse set.mm even if the cached label table exists",
    )
    parser.add_argument(
        "--cap",
        type=int,
        default=DEFAULT_CAP,
        help=f"Matcher solutions per goal (default {DEFAULT_CAP}). Proof "
        f"search must use the same value this data was built with.",
    )
    parser.add_argument(
        "--samples",
        type=int,
        default=2,
        help="Example targets to print per class (0 to suppress)",
    )
    args = parser.parse_args()

    table = label_table(
        mm_path=args.mm,
        mmverify_path=args.mmverify,
        cache=args.cache,
        rebuild=args.rebuild,
    )
    print(f"label table: {len(table)} assertions  (cache {args.cache})")

    out_dir = Path(args.out_dir) if args.out_dir else None
    if out_dir:
        out_dir.mkdir(parents=True, exist_ok=True)

    totals = collections.Counter()
    grand = 0
    for split in args.split:
        out_path = (
            out_dir / f"{Path(split).stem}.residual.jsonl" if out_dir else None
        )
        rows, counts = convert(split, table, out_path, cap=args.cap)
        report(split, rows, counts, samples=args.samples)
        if out_path:
            print(f"  -> {out_path}")
        totals.update(counts)
        grand += len(rows)

    if len(args.split) > 1 and grand:
        print(f"\nall splits: {grand} steps")
        for klass in CLASSES:
            print(f"  {klass:<7} {totals[klass]:>7}  {totals[klass] / grand:7.2%}")


if __name__ == "__main__":
    main()

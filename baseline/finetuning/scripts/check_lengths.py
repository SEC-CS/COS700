#!/usr/bin/env python
"""
check_lengths.py
================
Reports the token-length distribution of (GOAL + PROOFSTEP) sequences in
a JSONL file, so --max-length in train_model.py can be set from your
actual data instead of guessed. This matters in both directions:
  - too high wastes VRAM/time padding short sequences unnecessarily
  - too low silently truncates the tail of longer sequences, which can
    cut off part of the PROOFSTEP itself (the actual training target),
    corrupting those examples rather than erroring

Usage:
    python finetuning/scripts/check_lengths.py --input finetuning/data/train.jsonl \
        --base-model Qwen/Qwen2.5-Coder-1.5B
"""

import argparse
import json
import random

from transformers import AutoTokenizer

PROMPT_TEMPLATE = "GOAL: {goal}\nPROOFSTEP:"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", required=True)
    parser.add_argument("--base-model", default="Qwen/Qwen2.5-Coder-1.5B")
    parser.add_argument("--sample-size", type=int, default=50000,
                         help="Reservoir-sample this many lines rather "
                              "than tokenizing a multi-million-line file")
    args = parser.parse_args()

    tokenizer = AutoTokenizer.from_pretrained(args.base_model)

    # Reservoir sampling: one pass, fixed memory, uniform sample even
    # though we don't know the file's total line count up front.
    sample = []
    with open(args.input) as f:
        i = 0
        for line in f:
            line = line.strip()
            if not line:
                continue
            if len(sample) < args.sample_size:
                sample.append(line)
            else:
                j = random.randint(0, i)
                if j < args.sample_size:
                    sample[j] = line
            i += 1

    lengths = []
    for line in sample:
        record = json.loads(line)
        prompt = PROMPT_TEMPLATE.format(goal=record["goal"])
        target = " " + record["proof_step"]
        n_tokens = len(
            tokenizer(prompt + target, add_special_tokens=False)["input_ids"]
        ) + 1  # +1 for the eos token train_model.py appends
        lengths.append(n_tokens)

    lengths.sort()
    n = len(lengths)

    def pct(p):
        return lengths[min(int(n * p), n - 1)]

    print(f"Sampled {n} examples from {args.input}")
    print(f"  min    : {lengths[0]}")
    print(f"  median : {pct(0.50)}")
    print(f"  p90    : {pct(0.90)}")
    print(f"  p95    : {pct(0.95)}")
    print(f"  p99    : {pct(0.99)}")
    print(f"  max    : {lengths[-1]}")
    print()
    print("Pick --max-length around your p99 (or p95 if the tail is "
          "long) -- that truncates only the rare outliers instead of a "
          "meaningful chunk of the dataset.")


if __name__ == "__main__":
    main()
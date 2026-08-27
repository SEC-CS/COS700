#!/usr/bin/env python3

import json
import random
from collections import defaultdict
from pathlib import Path

DATA_DIR = Path(__file__).resolve().parents[1] / "data"
PROOF_STEPS = DATA_DIR / "proof_steps.jsonl"


def format_substitution(substitution):
    """
    Convert
        {
            "ph": ["ph"],
            "ps": ["(", "ph", "->", "ps", ")"]
        }

    into
        SUBST {{ ph : ph }} {{ ps : ( ph -> ps ) }}
    """

    parts = []
    for var in sorted(substitution):
        value = substitution[var]

        if value:
            parts.append(f"{{{{ {var} : {' '.join(value)} }}}}")

    if parts:
        return "SUBST " + " ".join(parts)

    return "SUBST"


def training_example(record):
    subst = format_substitution(record["substitution"])

    return (
        f"GOAL {record['goal']} "
        f"THEOREM {record['theorem']} "
        f"{subst}"
        "<|endoftext|>\n"
    )


# ------------------------------------------------------------
# Load dataset
# ------------------------------------------------------------
theorems = defaultdict(list)

with open(PROOF_STEPS, encoding="utf-8") as f:

    for line in f:
        record = json.loads(line)
        # Every proof step belongs to the theorem currently
        # being proved.
        theorems[record["proof_label"]].append(record)

all_theorems = list(theorems)
num_theorems = len(all_theorems)
num_steps = sum(len(records) for records in theorems.values())

print(f"Theorems   : {num_theorems:,}")
print(f"Proof steps: {num_steps:,}")

# ------------------------------------------------------------
# Build theorem split
# ------------------------------------------------------------
random.seed(42)

NUM_VALID = 1000
NUM_TEST = 1000

bucket_size = num_theorems // (NUM_VALID + NUM_TEST)

buckets = [
    all_theorems[i * bucket_size : (i + 1) * bucket_size]
    for i in range(NUM_VALID + NUM_TEST)
]

sampled = [random.choice(bucket) for bucket in buckets]

valid = set(sampled[:NUM_VALID])
test = set(sampled[NUM_VALID:])
train = set(all_theorems) - valid - test

print()
print("Split")
print(f"  Train : {len(train):,}")
print(f"  Valid : {len(valid):,}")
print(f"  Test  : {len(test):,}")

# ------------------------------------------------------------
# Write datasets
# ------------------------------------------------------------
splits = {
    "train": train,
    "valid": valid,
    "test": test,
}

step_counts = {}

for split_name, theorem_set in splits.items():
    json_path = DATA_DIR / f"{split_name}.jsonl"
    train_path = DATA_DIR / f"{split_name}_training.txt"

    count = 0
    with (
        open(json_path, "w", encoding="utf-8") as json_out,
        open(train_path, "w", encoding="utf-8") as train_out,
    ):
        for theorem in theorem_set:
            for record in theorems[theorem]:
                json_out.write(json.dumps(record) + "\n")
                train_out.write(training_example(record))
                count += 1
    step_counts[split_name] = count

print()
print("Proof steps")

for split in ("train", "valid", "test"):
    print(f"  {split:5s}: " f"{step_counts[split]:,}")

print()
print("Finished.")

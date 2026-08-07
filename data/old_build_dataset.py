import json
import random
from collections import defaultdict
from pathlib import Path

DATA_DIR = Path(__file__).resolve().parents[1] / 'data'
PROOF_STEPS_PATH = DATA_DIR / 'proof_steps.jsonl'

# --- Load all proof steps and group by theorem ---
theorem_steps = defaultdict(list)

with open(PROOF_STEPS_PATH) as f:
    for line in f:
        record = json.loads(line)
        theorem_steps[record['proof_label']].append(line)

# Preserve the order theorems appear in set.mm
# (they are already in order in the jsonl file)
all_theorems = list(theorem_steps.keys())
n = len(all_theorems)
print(f"Total theorems: {n:,}")
print(f"Total proof steps: {sum(len(v) for v in theorem_steps.values()):,}")

# --- Sample 1k validation and 1k test evenly across the file ---
# Divide into 2000 equal-sized buckets and pick one theorem per bucket.
# This ensures coverage of both simple and complex theorems in each split.
bucket_size = n // 2000
buckets = [all_theorems[i * bucket_size:(i + 1) * bucket_size]
           for i in range(2000)]

random.seed(42)
sampled = [random.choice(bucket) for bucket in buckets]

valid_theorems = set(sampled[:1000])
test_theorems  = set(sampled[1000:])
train_theorems = set(all_theorems) - valid_theorems - test_theorems

print(f"\nSplit:")
print(f"  Train theorems : {len(train_theorems):,}")
print(f"  Valid theorems : {len(valid_theorems):,}")
print(f"  Test theorems  : {len(test_theorems):,}")

# --- Write the split files ---
splits = {
    'train': train_theorems,
    'valid': valid_theorems,
    'test':  test_theorems,
}

file_handles = {
    split: {
        'jsonl':    open(DATA_DIR / f'{split}.jsonl', 'w'),
        'training': open(DATA_DIR / f'{split}_training.txt', 'w'),
    }
    for split in splits
}

step_counts = defaultdict(int)

for theorem_label, lines in theorem_steps.items():
    for split, theorem_set in splits.items():
        if theorem_label in theorem_set:
            for line in lines:
                record = json.loads(line)
                file_handles[split]['jsonl'].write(line)
                file_handles[split]['training'].write(
                    f"GOAL {record['goal']} PROOFSTEP {record['proof_step']}"
                    f"<|endoftext|>\n"
                )
                step_counts[split] += 1
            break

for split in splits:
    for f in file_handles[split].values():
        f.close()

print(f"\nProof steps per split:")
for split, count in step_counts.items():
    print(f"  {split:6s} : {count:,}")

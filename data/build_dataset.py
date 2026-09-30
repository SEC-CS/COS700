#!/usr/bin/env python3

import argparse
import json
import random
from collections import defaultdict
from pathlib import Path

"""
Split a jsonl dataset into training, validation, and testing subsets.
"""


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
def load_dataset(filepath: str | Path, verbose=False) -> defaultdict:
    theorems = defaultdict(list)

    with open(filepath, encoding="utf-8") as f:

        for line in f:
            record = json.loads(line)
            # Every proof step belongs to the theorem currently
            # being proved.
            theorems[record["proof_label"]].append(record)

    all_theorems = list(theorems)
    num_steps = sum(len(records) for records in theorems.values())

    if verbose:
        print(f"Theorems   : {len(all_theorems):,}")
        print(f"Proof steps: {num_steps:,}")

    return theorems


# ------------------------------------------------------------
# Build theorem split
# ------------------------------------------------------------
def build_theorem_split(
    theorems: list, percent_valid: int, percent_test: int, verbose=False
) -> dict[str, list]:
    assert 0 <= percent_valid <= 100
    assert 0 <= percent_test <= 100
    assert percent_valid + percent_test <= 100

    random.seed(42)

    sampled = random.sample(theorems, len(theorems))

    index_valid = len(theorems) * percent_valid // 100
    index_test = index_valid + (len(theorems) * percent_test // 100)

    valid = (sampled[:index_valid])
    test = (sampled[index_valid:index_test])
    train = (sampled[index_test:])

    if verbose:
        print("Split")
        print(f"  Train : {len(train):,}")
        print(f"  Valid : {len(valid):,}")
        print(f"  Test  : {len(test):,}")

    return {
        "train": train,
        "valid": valid,
        "test": test,
    }


# ------------------------------------------------------------
# Write datasets
# ------------------------------------------------------------
def output_to_file(
    splits: dict[str, list], theorems: defaultdict, output_dir: str | Path, verbose=False
):
    step_counts = {}

    for split_name, theorem_names in splits.items():
        json_path = Path(output_dir) / f"{split_name}.jsonl"
        train_path = Path(output_dir) / f"{split_name}_training.txt"

        count = 0
        with (
            open(json_path, "w", encoding="utf-8") as json_out,
            open(train_path, "w", encoding="utf-8") as train_out,
        ):
            for theorem_name in theorem_names:
                for record in theorems[theorem_name]:
                    json_out.write(json.dumps(record) + "\n")
                    train_out.write(training_example(record))
                    count += 1
        step_counts[split_name] = count

    if verbose:
        print()
        print("Proof steps")

    for split in ("train", "valid", "test"):
        print(f"  {split:5s}: " f"{step_counts[split]:,}")


def main(
    proof_steps_file: str | Path,
    output_dir: str | Path,
    percent_valid: int,
    percent_test: int,
    verbose=False,
) -> None:
    theorems = load_dataset(proof_steps_file, verbose=verbose)
    splits = build_theorem_split(
        theorems=list(theorems.keys()),
        percent_valid=percent_valid,
        percent_test=percent_test,
        verbose=verbose,
    )
    output_to_file(
        splits=splits,
        theorems=theorems,
        output_dir=output_dir,
        verbose=verbose,
    )


if __name__ == "__main__":
    DATA_DIR = Path(__file__).resolve().parents[1] / "data"
    PROOF_STEPS = DATA_DIR / "proof_steps.jsonl"

    parser = argparse.ArgumentParser(
        description="Split proof-step file into training, validation, and test dataset files."
    )
    parser.add_argument(
        "-i", "--proof-steps", default=PROOF_STEPS, help="Path to proof-step file"
    )
    parser.add_argument(
        "-o", "--output-dir", default=DATA_DIR, help="Directory to output datasets"
    )
    parser.add_argument(
        "-v",
        "--validation",
        type=int,
        default=20,
        help="Percentage of dataset to be used in validation set",
    )
    parser.add_argument(
        "-t",
        "--test",
        type=int,
        default=10,
        help="Percentage of dataset to be used in test set",
    )
    parser.add_argument(
        "--verbose",
        action="store_true",
        help="Print progress messages",
    )
    args = parser.parse_args()
    main(
        proof_steps_file=args.proof_steps,
        output_dir=args.output_dir,
        percent_valid=args.validation,
        percent_test=args.test,
        verbose=args.verbose,
    )

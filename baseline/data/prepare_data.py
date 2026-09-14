import argparse
import os
import json
import pandas as pd
from pathlib import Path
from extractor import extract_proof_steps
from build_dataset import main as build_dataset


def get_trimmed_theorem_set(
    df: pd.DataFrame, longest=True, cutoff=80_000
) -> pd.DataFrame:
    value_counts = df["proof_label"].value_counts(ascending=longest)
    cumsum = value_counts.cumsum()
    cutoff_idx = (cumsum <= cutoff).sum()
    keep_labels = value_counts.index[:cutoff_idx]
    return df[df["proof_label"].isin(keep_labels)]


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Split set.mm into sections")
    parser.add_argument("--mm", required=True, help="Path to set.mm file")
    parser.add_argument(
        "--output-dir",
        default="proof_step_sections",
        help="Path to directory for output files",
    )
    parser.add_argument(
        "--verbose",
        action="store_true",
        help="Print progress messages",
    )
    args = parser.parse_args()

    proof_steps = extract_proof_steps(mm_path=args.mm, verbose=args.verbose)
    shortest_thrms = get_trimmed_theorem_set(proof_steps, longest=False)
    longest_thrms = get_trimmed_theorem_set(proof_steps, longest=True)

    chunk_size = 2_000

    for fname, df in [
        ("all_theorems", proof_steps),
        ("shortest_theorems", shortest_thrms),
        ("longest_theorems", longest_thrms),
    ]:
        output_dir = Path(args.output_dir) / f"{fname}"
        output_path = output_dir / "all.jsonl"
        if not os.path.exists(output_dir):
            os.makedirs(output_dir)
        with open(output_path, "w") as f:
            for start in range(0, len(df), chunk_size):
                chunk = df.iloc[start : start + chunk_size]
                for record in chunk.to_dict(orient="records"):
                    f.write(json.dumps(record, ensure_ascii=False) + "\n")

        build_dataset(
            proof_steps_file=output_path,
            output_dir=output_dir,
            percent_valid=20,
            percent_test=10,
            verbose=args.verbose,
        )

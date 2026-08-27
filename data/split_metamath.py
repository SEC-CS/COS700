import pandas as pd
import argparse
import re
import metamathpy.database as md
import os
import json
from extractor import extract_proof_steps

"""
USAGE:
  uv run python split_metamath.py --mm set.mm
"""


def split_mm_by_headings(filepath, output_dir=None) -> dict[str, str]:
    with open(filepath, "r", encoding="utf-8") as f:
        content = f.read()

    # Pattern matches the ###\ntext\n### heading blocks
    heading_pattern = re.compile(
        r"^\$\(\n(#{3,})\s*\n\s*(.+?)\s*\n\s*#{3,}", re.MULTILINE
    )
    matches = list(heading_pattern.finditer(content))

    if not matches:
        print("No headings found.")
        return {}

    output = {}
    for i, match in enumerate(matches):
        # Section title from capture group 2
        title = match.group(2).strip()
        # Sanitize for filename
        safe_title = re.sub(r"[^\w\-]+", "_", title)[:60]
        numbered_title = f"{i+1:02d}_{safe_title}"

        content_start = match.end()  # Content starts right after the heading ends
        content_end = (
            matches[i + 1].start() if i + 1 < len(matches) else len(content)
        )  # Content ends at the next heading (or end of file)
        section_content = content[content_start:content_end].strip()

        output[numbered_title] = section_content

        if output_dir:
            # Build the new file: heading + body
            heading_full = match.group(0)
            output_path = f"{output_dir}/{numbered_title}.mm"
            with open(output_path, "w", encoding="utf-8") as out:
                out.write(heading_full + "\n")
                out.write(section_content + "\n")
            print(f"Created: {output_path}")

    print(f"\nSplit into {len(matches)} files.")
    return output


def get_theorem_names(content: str) -> list[str]:
    return list(
        dict.fromkeys(
            re.findall(
                r"(\w+)\s+\$[ap]",
                re.sub(r"\$\(.*?\$\)", "", content, flags=re.DOTALL),
                re.DOTALL,
            )
        )
    )


def split_setmm():
    parser = argparse.ArgumentParser(description="Split set.mm into sections")
    parser.add_argument("-i", "--input", required=True, help="Input set.mm file")
    parser.add_argument(
        "-o", "--output-dir", default="sections", help="Output directory"
    )
    args = parser.parse_args()

    split_mm_by_headings(args.input, args.output_dir)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Split set.mm into sections")
    parser.add_argument("--mm", required=True, help="Path to set.mm file")
    parser.add_argument(
        "--chunk-size",
        default=2_000,
        type=int,
        help="Chunk Size to split dataframe when writing to file (lower chunk size reduces memory usage but increases runtime)",
    )
    args = parser.parse_args()

    # Split MM file by maths branches/sections
    branches = split_mm_by_headings(args.mm)
    proof_steps = extract_proof_steps(mm_path="set.mm", verbose=True)

    for branch, mm_content in branches.items():
        theorems = get_theorem_names(mm_content)
        filt = proof_steps["proof_label"].isin(theorems)
        df = proof_steps[filt]

        chunk_size = args.chunk_size
        output_path = f"./proof_step_sections/{branch}.jsonl"

        if not os.path.exists("./proof_step_sections/"):
            os.makedirs("./proof_step_sections/")
        with open(output_path, "w") as f:
            for start in range(0, len(df), chunk_size):
                chunk = df.iloc[start : start + chunk_size]
                for record in chunk.to_dict(orient="records"):
                    f.write(json.dumps(record, ensure_ascii=False) + "\n")

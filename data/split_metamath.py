import pandas as pd
import argparse
import re
import metamathpy.database as md
import os
import json

"""
USAGE:
  uv run python split_metamath.py -d ./sections
"""


def split_by_headings(filepath, output_dir):
    with open(filepath, "r", encoding="utf-8") as f:
        content = f.read()

    # Pattern matches the ###\ntext\n### heading blocks
    heading_pattern = re.compile(
        r"^\$\(\n(#{3,})\s*\n\s*(.+?)\s*\n\s*#{3,}", re.MULTILINE
    )

    matches = list(heading_pattern.finditer(content))

    if not matches:
        print("No headings found.")
        return

    for i, match in enumerate(matches):
        # Section title from capture group 2
        title = match.group(2).strip()
        # Sanitize for filename
        safe_title = re.sub(r"[^\w\-]+", "_", title)[:60]

        # Content starts right after the heading ends
        content_start = match.end()
        # Content ends at the next heading (or end of file)
        content_end = matches[i + 1].start() if i + 1 < len(matches) else len(content)

        section_content = content[content_start:content_end].strip()

        # Build the new file: heading + body
        heading_full = match.group(0)
        output_path = f"{output_dir}/{i+1:02d}_{safe_title}.mm"

        with open(output_path, "w", encoding="utf-8") as out:
            out.write(heading_full + "\n")
            out.write(section_content + "\n")

        print(f"Created: {output_path}")

    print(f"\nSplit into {len(matches)} files.")


def get_theorem_names(filepath: str) -> list[str]:
    db = md.parse(filepath)
    theorems = [rule for rule in db.rules if not "." in rule]
    return theorems


#############################################################################


def split_setmm():
    parser = argparse.ArgumentParser(description="Split set.mm into sections")
    parser.add_argument("-i", "--input", required=True, help="Input set.mm file")
    parser.add_argument(
        "-o", "--output-dir", default="sections", help="Output directory"
    )
    args = parser.parse_args()

    split_by_headings(args.input, args.output_dir)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Split set.mm into sections")
    parser.add_argument(
        "-d", "--directory", help="Directory with all set.mm files", type=str
    )
    parser.add_argument(
        "-c",
        "--chunk-size",
        default=2_000,
        type=int,
        help="Chunk Size to split dataframe when writing to file (lower chunk size reduces memory usage but increases runtime)",
    )
    args = parser.parse_args()

    files = [
        f
        for f in os.listdir(args.directory)
        if os.path.isfile(os.path.join(args.directory, f))
    ]

    proof_steps = pd.read_json(
        path_or_buf="./proof_steps.jsonl",
        lines=True,
    )

    for file in files:
        theorems = get_theorem_names(os.path.join(args.directory, file))
        filt = proof_steps["proof_label"].isin(theorems)
        df = proof_steps[filt]

        chunk_size = args.chunk_size
        output_path = f"./proof_step_sections/{file[:-3]}.jsonl"
        if not os.path.exists("./proof_step_sections/"):
            os.makedirs("./proof_step_sections/")
        with open(output_path, "w") as f:
            for start in range(0, len(df), chunk_size):
                chunk = df.iloc[start : start + chunk_size]
                for record in chunk.to_dict(orient="records"):
                    f.write(json.dumps(record, ensure_ascii=False) + "\n")

        # df[:20].to_json(
        #     f,
        #     orient="records",
        #     lines=True,
        # )

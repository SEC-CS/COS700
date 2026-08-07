import argparse
import re


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


def get_theorem_names(mmfile: str) -> list[str]:
    pass


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Split set.mm into sections")
    parser.add_argument("-i", "--input", required=True, help="Input set.mm file")
    parser.add_argument(
        "-o", "--output-dir", default="sections", help="Output directory"
    )
    args = parser.parse_args()

    split_by_headings(args.input, args.output_dir)

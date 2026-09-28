#!/usr/bin/env python
"""
\

Usage

uv run python -m residuals.finetuning.scripts.train_model --train residuals/data/longest_theorems/train.residual.jsonl --valid residuals/data/longest_theorems/valid.residual.jsonl --base-model Qwen/Qwen2.5-Coder-0.5B --output-dir ./residuals/finetuning/output/finetuned-prover --max-length 250

"""

from baseline.finetuning.scripts.train_model import ProofStepDataset, main


class ResidualStepDataset(ProofStepDataset):
    """Trains on the pre-built residual target rather than rebuilding the
    full proof step from `theorem` + `substitution`."""

    def target_text(self, record: dict) -> str:
        return record["target"]


if __name__ == "__main__":
    main(
        ResidualStepDataset,
        doc=__doc__,
        output_dir="./residuals/finetuning/output/finetuned-prover",
    )

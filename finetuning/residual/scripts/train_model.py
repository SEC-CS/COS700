#!/usr/bin/env python
"""Train residual models, forwarding all other arguments to the training script selected by --mode."""

import argparse
import sys

from finetuning.baseline.scripts.train_model import ProofStepDataset, main as baseline_main

MODES = ("baseline", "modular-thm", "modular-sub")

DEFAULT_OUTPUT_DIRS = {
    "baseline": "./finetuning/residual/output/finetuned-prover",
    "modular-thm": "./finetuning/residual/output/finetuned-classifier",
    "modular-sub": "./finetuning/residual/output/finetuned-substitution",
}


class ResidualStepDataset(ProofStepDataset):
    """Trains on the pre-built residual target rather than rebuilding the
    full proof step from `theorem` + `substitution`."""

    def target_text(self, record: dict) -> str:
        return record["target"]


def _split_mode(argv):
    pre = argparse.ArgumentParser(add_help=False)
    pre.add_argument("--mode", choices=MODES, default="baseline")
    known, rest = pre.parse_known_args(argv)
    return known.mode, rest


def main():
    mode, rest = _split_mode(sys.argv[1:])
    sys.argv = [sys.argv[0]] + rest
    output_dir = DEFAULT_OUTPUT_DIRS[mode]

    if mode == "baseline":
        baseline_main(ResidualStepDataset, doc=__doc__, output_dir=output_dir)
    elif mode == "modular-thm":
        from finetuning.modular.scripts.train_model_thm import main as run
        run(doc=__doc__, output_dir=output_dir)
    else:
        from finetuning.modular.scripts.train_model_sub import (
            ResidualSubstitutionDataset,
            main as run,
        )
        run(
            dataset_cls=ResidualSubstitutionDataset,
            doc=__doc__,
            output_dir=output_dir,
        )

if __name__ == "__main__":
    main()

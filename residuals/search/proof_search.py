#!/usr/bin/env python
r"""
Usage
-----
Run from the repository root. Same flags as the baseline, plus --cap.

Run Both:

$env:PROVER_MODEL_DIR = ".\residuals\finetuning\output\finetuned-prover\longest_theorems_model"

uv run python -m residuals.search.proof_search `
  --mm baseline\data\set.mm `
  --eval residuals\data\longest_theorems\test.residual.jsonl `
  --model-module baseline/search/model.py `
  --proved-output .\residuals\results\longest_theorems_proved.txt `
  --expansions-output .\residuals\results\longest_expansions.csv `
  --attempts 1 `
  --expansions 32 2>&1 | Tee-Object residuals/results/proof_search.log 

--cap must match the value the training data was built with, or the model
was trained to omit variables this search recovers differently.

Optional add to command writes console output to baseline/results/proof_search.log:
2>&1 | Tee-Object residuals/results/proof_search.log 
"""

from baseline.search.proof_search import main as baseline_main
from baseline.utils.formatting import (
    format_proofstep,
    parse_proofstep,
)
from residuals.utils.matcher import (
    DEFAULT_CACHE,
    DEFAULT_CAP,
    complete,
    determined_key,
    label_table,
)


class ResidualModel:
    """
    Wraps a model that predicts "label + residual", turning each prediction
    into the full steps the verifier can actually check.

    Presents the same generate_steps() interface as the wrapped model, so
    the search itself is untouched.
    """

    def __init__(self, model, table: dict, cap: int = DEFAULT_CAP):
        self.model = model
        self.table = table
        self.cap = cap
        self.excluded_labels = set()

    def set_excluded_labels(self, labels: set[str]) -> None:
        self.excluded_labels = set(labels)

    def generate_steps(self, goal_str: str, n: int = 32, temperature: float = 1.0):
        out = []
        seen = set()
        for step_str, logprob in self.model.generate_steps(
            goal_str, n=n, temperature=temperature
        ):
            for full_step in self.complete_step(goal_str, step_str):
                # Two residual predictions can complete to the same step.
                # Keep the first (highest-scoring) occurrence only.
                if full_step not in seen:
                    seen.add(full_step)
                    out.append((full_step, logprob))
        return out

    def complete_step(self, goal_str: str, step_str: str) -> list[str]:
        """
        A predicted residual step -> the full steps to try, in the order the
        matcher returns them.

        A prediction that cannot be completed -- unparseable, an unknown
        label, or a conclusion that does not match this goal at all is dropped.
        """
        target = step_str.strip()

        parsed = parse_proofstep(target)
        if parsed is None:
            return [step_str]

        label, residual = parsed["theorem"], parsed["subst"]

        if label in self.excluded_labels:
            return []

        info = self.table.get(label)
        if info is None:
            return []

        steps = []
        seen = set()

        for candidate in complete(
            info["result"],
            goal_str.split("]]", 1)[1].split(),
            info["kinds"],
            cap=self.cap,
        ):
            key = determined_key(candidate, info["rvars"])
            if key in seen:
                continue
            seen.add(key)
            subst = {v: val for v, val in candidate.items() if v in info["rvars"]}
            subst.update(residual)
            steps.append(format_proofstep(label, subst))

        return steps or [step_str]


def add_args(parser) -> None:
    parser.add_argument(
        "--cap",
        type=int,
        default=DEFAULT_CAP,
        help=f"Substitution candidates the matcher may return per goal "
        f"(default {DEFAULT_CAP}). Must match the value residualise.py "
        f"built the training data with.",
    )
    parser.add_argument(
        "--label-table",
        default=DEFAULT_CACHE,
        help="Cached per-label table from residualise.py. Built from --mm "
        "on first use (~100s) if missing.",
    )


def wrap_model(model, mm, args):
    table = label_table(
        mm_path=args.mm, mmverify_path=args.mmverify, cache=args.label_table
    )
    print(f"Label table: {len(table)} assertions  (cache {args.label_table})")
    return ResidualModel(model, table, cap=args.cap)


if __name__ == "__main__":
    baseline_main(add_args=add_args, wrap_model=wrap_model, doc=__doc__)

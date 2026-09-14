#!/usr/bin/env python
"""
residuals/search/proof_search.py
================================

Proof search for a model trained on "label + residual" targets.

Same search, same verifier, same metrics as the baseline. The one thing
that changes is what sits between the model and the verifier.

A residual-trained model emits a step with the determined variables
missing:

    syl {{ ps : A e. B }}

which the verifier rejects out of hand -- it requires a substitution
covering every mandatory variable of the applied theorem. So each predicted
step is first *completed*: the applied theorem's conclusion is matched
against the goal currently being expanded, and every substitution the
matcher finds is merged with the model's residual to make one full,
verifier-ready candidate step:

    syl {{ ph : ( x = y ) }} {{ ps : A e. B }} {{ ch : ... }}
    syl {{ ph : x }} {{ ps : A e. B }} {{ ch : ... }}          <- alternative
    ...

This is the live counterpart of the `match_rank` that residualise.py
recorded offline. Nothing here knows the rank, and nothing needs to: the
candidates go to the verifier in matcher order and the verifier decides.
The first one that holds is the step search takes -- which is why the
candidates enter as ordinary tactics rather than being resolved behind the
search's back. They are scored, counted and tried exactly like any other
candidate, so `candidates_examined` stays an honest count of verifier work
and the two methods' metrics remain comparable.

A step whose target carried the `!FULL` sentinel already holds a complete
substitution, so it skips matching and goes straight to the verifier.

Because completion happens before the verifier, the proof tree records the
full step -- proofs written by --proved-output are complete and checkable,
not residual fragments.

Usage
-----
Run from the repository root. Same flags as the baseline, plus --cap.

    python -m residuals.search.proof_search --mm data/set.mm --eval data/01/valid.jsonl --model-module residuals/search/model.py --proved-output proved_theorems.txt --attempts 1 --expansions 64

--cap must match the value the training data was built with, or the model
was trained to omit variables this search recovers differently.
"""

from baseline.search.proof_search import main as baseline_main
from residuals.utils.formatting import (
    format_proofstep,
    goal_conclusion,
    parse_target,
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
        label, or a conclusion that does not match this goal at all -- is
        passed through unchanged rather than dropped, so it still reaches
        the verifier, is still rejected there, and is still counted. A
        silently dropped candidate would understate the work search did.
        """
        parsed = parse_target(step_str)
        if parsed is None:
            return [step_str]

        label, residual = parsed["theorem"], parsed["subst"]

        # Sentinel: the model emitted the complete substitution itself,
        # because the matcher could not recover this step at all.
        if parsed["full"]:
            print(f"Residual model emitted !FULL step: {step_str}")
            return [format_proofstep(label, residual)]

        info = self.table.get(label)
        if info is None:
            print(f"Residual model emitted unknown theorem: {step_str}")
            return [step_str] # not a real theorem label, let the verifier reject it

        steps = []
        seen = set()
        for candidate in complete(
            info["result"], goal_conclusion(goal_str), info["kinds"], cap=self.cap
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
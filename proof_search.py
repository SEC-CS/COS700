"""
proof_search.py

Best-first proof search for Metamath.

The model receives

    GOAL
        [[ ... ]] |- ...

and predicts

    THEOREM
        ax-mp

    SUBST
        {{ ph : ... }}
        {{ ps : ... }}

The verifier checks that theorem application and returns the new subgoals.
Usage:
  # Test infrastructure only (no model)
  uv run python proof_search.py --mm data/set.mm --goal "|- ( ph -> ph )" --stub

  # Run heuristic baseline
  uv run python proof_search.py --mm data/set.mm --eval data/valid.jsonl --model models/heuristic_baseline.py

  # Run a learned model
  uv run python proof_search.py --mm data/set.mm --eval data/valid.jsonl --model my_model.py

"""

import argparse
import heapq
import importlib.util
import itertools
import json
import os
import sys
import time
import inspect

from dataclasses import dataclass, field
from typing import Optional


# ------------------------------------------------------------
# Load mmverify
# ------------------------------------------------------------

def load_mmverify(path):

    spec = importlib.util.spec_from_file_location(
        "mmverify",
        path,
    )

    mod = importlib.util.module_from_spec(spec)

    spec.loader.exec_module(mod)

    mod.verbosity = 0

    return mod


# ------------------------------------------------------------
# Stub model
# ------------------------------------------------------------

class StubModel:

    def generate_steps(
        self,
        goal_str,
        n=32,
        temperature=1.0,
    ):
        return []


# ------------------------------------------------------------
# Load external model
# ------------------------------------------------------------

def load_model(module_path):

    spec = importlib.util.spec_from_file_location(
        "model",
        module_path,
    )

    mod = importlib.util.module_from_spec(spec)

    spec.loader.exec_module(mod)

    return mod.Model()

def load_model(module_path, mm):

    spec = importlib.util.spec_from_file_location(
        "model",
        module_path,
    )

    mod = importlib.util.module_from_spec(spec)

    spec.loader.exec_module(mod)

    params = inspect.signature(mod.Model).parameters

    if len(params) == 0:
        return mod.Model()

    return mod.Model(mm)

# ------------------------------------------------------------
# Goal formatting
# ------------------------------------------------------------

def format_goal(e_hyps, conclusion):

    if e_hyps:

        return (
            "[[ "
            + "   ".join(
                " ".join(h)
                for h in e_hyps
            )
            + " ]] "
            + " ".join(conclusion)
        )

    return "[[ ]] " + " ".join(conclusion)


def parse_goal(goal):

    try:

        i = goal.index("[[") + 2
        j = goal.index("]]")

        hyp_block = goal[i:j].strip()

        if hyp_block:
            hyps = [
                h.strip().split()
                for h in hyp_block.split("   ")
            ]
        else:
            hyps = []

        conclusion = goal[j + 2:].strip().split()

        return {
            "hyps": hyps,
            "conclusion": conclusion,
        }

    except Exception:

        return None


# ------------------------------------------------------------
# Parse model output
# ------------------------------------------------------------

def parse_step(step):

    try:

        pieces = step.strip().split(maxsplit=1)

        label = pieces[0]

        subst = {}

        if len(pieces) > 1:

            rest = pieces[1]

            while "{{" in rest:

                start = rest.index("{{")
                end = rest.index("}}")

                text = rest[start + 2:end].strip()

                var, value = text.split(":", 1)

                subst[var.strip()] = value.strip().split()

                rest = rest[end + 2:]

        return {
            "label": label,
            "subst": subst,
        }

    except Exception:

        return None


# ------------------------------------------------------------
# Verifier
# ------------------------------------------------------------

class MetamathVerifier:

    def __init__(self, mm):

        self.mm = mm

    def apply_step(
        self,
        goal_str,
        step_str,
    ):

        goal = parse_goal(goal_str)

        step = parse_step(step_str)

        if goal is None or step is None:
            return None

        if step["label"] not in self.mm.labels:
            return None

        kind, data = self.mm.labels[step["label"]]

        if kind not in ("$a", "$p"):
            return None

        distinct, mand_var, hyp, result = data

        subst = step["subst"]

        #
        # Mandatory variables must all exist.
        #

        for _, var in mand_var:

            if var not in subst:
                return None

        #
        # Conclusion must match.
        #

        conclusion = self.mm.apply_subst(
            result,
            subst,
        )

        if conclusion != goal["conclusion"]:
            return None

        #
        # Distinct variable conditions.
        #

        for x, y in distinct:

            x_vars = self.mm.find_vars(subst[x])

            y_vars = self.mm.find_vars(subst[y])

            for xv, yv in itertools.product(
                x_vars,
                y_vars,
            ):

                if xv == yv:
                    return None

                if not self.mm.fs.lookup_d(
                    xv,
                    yv,
                ):
                    return None

        #
        # Produce new subgoals.
        #

        new_goals = []

        for h in hyp:

            subgoal = self.mm.apply_subst(
                h,
                subst,
            )

            new_goals.append(
                format_goal(
                    goal["hyps"],
                    subgoal,
                )
            )

        return new_goals

# ------------------------------------------------------------
# Priority queue
# ------------------------------------------------------------

@dataclass(order=True)
class QueueEntry:

    priority: float

    logprob: float = field(compare=False)

    goal: str = field(compare=False)


# ------------------------------------------------------------
# Proof search
# ------------------------------------------------------------

def proof_search(
    root_goal,
    model,
    verifier,
    max_expansions=128,
    n_tactics=32,
    temperature=1.0,
):

    queue = []

    heapq.heappush(
        queue,
        QueueEntry(
            priority=0.0,
            logprob=0.0,
            goal=root_goal,
        ),
    )

    proof = {}

    closed = set()

    queued = {root_goal}

    expansions = 0

    while queue and expansions < max_expansions:

        node = heapq.heappop(queue)

        goal = node.goal

        if goal in closed:
            continue

        expansions += 1

        candidates = model.generate_steps(
            goal,
            n=n_tactics,
            temperature=temperature,
        )

        for step, score in candidates:

            subgoals = verifier.apply_step(
                goal,
                step,
            )

            if subgoals is None:
                continue

            proof[goal] = {
                "step": step,
                "subgoals": subgoals,
            }

            if not subgoals:

                closed.add(goal)

            else:

                child_score = node.logprob + score

                for sg in subgoals:

                    if sg in closed:
                        continue

                    if sg in queued:
                        continue

                    queued.add(sg)

                    heapq.heappush(
                        queue,
                        QueueEntry(
                            priority=-child_score,
                            logprob=child_score,
                            goal=sg,
                        ),
                    )

            #
            # One verified theorem application is enough.
            #

            break

        #
        # Propagate solved goals upward.
        #

        changed = True

        while changed:

            changed = False

            for g, info in proof.items():

                if g in closed:
                    continue

                if all(
                    sg in closed
                    for sg in info["subgoals"]
                ):

                    closed.add(g)

                    changed = True

        if root_goal in closed:

            return proof

    return None


# ------------------------------------------------------------
# Count proof size
# ------------------------------------------------------------

def proof_size(tree):

    if tree is None:
        return 0

    return len(tree)


# ------------------------------------------------------------
# Evaluate
# ------------------------------------------------------------

def evaluate(
    split_file,
    model,
    verifier,
    attempts=4,
    max_expansions=128,
    n_tactics=32,
):

    goals = {}

    with open(split_file) as f:

        for line in f:

            record = json.loads(line)

            if record["proof_label"] not in goals:

                goals[
                    record["proof_label"]
                ] = record["goal"]

    total = len(goals)

    proved = 0

    total_steps = 0

    start = time.time()

    for theorem, goal in goals.items():

        success = False

        for _ in range(attempts):

            tree = proof_search(
                goal,
                model,
                verifier,
                max_expansions=max_expansions,
                n_tactics=n_tactics,
            )

            if tree is not None:

                proved += 1

                total_steps += proof_size(tree)

                success = True

                print(theorem)
                print(tree)

                break

        if proved % 100 == 0 and proved:

            print(
                f"{proved}/{total}"
            )

    elapsed = time.time() - start

    print()

    print(f"Theorems : {total}")

    print(f"Proved   : {proved}")

    print(
        f"Success  : {100*proved/total:.2f}%"
    )

    print(
        f"Avg size : "
        f"{total_steps/max(proved,1):.2f}"
    )

    print(
        f"Time     : "
        f"{elapsed:.2f}s"
    )

# ------------------------------------------------------------
# Main
# ------------------------------------------------------------

def main():

    parser = argparse.ArgumentParser(
        description="Metamath proof search"
    )

    parser.add_argument(
        "--mm",
        required=True,
        help="Path to set.mm",
    )

    parser.add_argument(
        "--mmverify",
        default=None,
        help="Path to mmverify.py",
    )

    parser.add_argument(
        "--model",
        default=None,
        help="Python file containing Model",
    )

    parser.add_argument(
        "--stub",
        action="store_true",
        help="Use stub model",
    )

    parser.add_argument(
        "--goal",
        default=None,
        help='Goal such as "|- ( ph -> ph )"',
    )

    parser.add_argument(
        "--eval",
        default=None,
        help="Evaluate a split",
    )

    parser.add_argument(
        "--attempts",
        type=int,
        default=4,
    )

    parser.add_argument(
        "--expansions",
        type=int,
        default=128,
    )

    parser.add_argument(
        "--tactics",
        type=int,
        default=32,
    )

    args = parser.parse_args()

    if not args.stub and not args.model:
        print("Choose --stub or --model")
        sys.exit(1)

    if args.mmverify:

        mmverify_path = args.mmverify

    else:

        mmverify_path = os.path.join(
            os.path.dirname(__file__),
            "data/mmverify.py",
        )

    mmv = load_mmverify(mmverify_path)

    print("Loading database...")

    mm = mmv.MM()

    with open(
        args.mm,
        encoding="utf-8",
        errors="replace",
    ) as f:

        mm.read(
            mmv.toks(f)
        )

    verifier = MetamathVerifier(mm)

#
# Create the model AFTER loading the database.
#

    if args.stub:

        model = StubModel()

    else:

        model = load_model(
            args.model,
            mm,
        )
    #
    # Single goal
    #

    if args.goal:

        root = "[[ ]] " + args.goal

        proof = proof_search(
            root_goal=root,
            model=model,
            verifier=verifier,
            max_expansions=args.expansions,
            n_tactics=args.tactics,
        )

        if proof is None:

            print("No proof found.")

        else:

            print()

            print("Proof found")

            for goal, info in proof.items():

                print()

                print("GOAL")

                print(goal)

                print()

                print("STEP")

                print(info["step"])

        return

    #
    # Evaluation
    #

    if args.eval:

        evaluate(
            split_file=args.eval,
            model=model,
            verifier=verifier,
            attempts=args.attempts,
            max_expansions=args.expansions,
            n_tactics=args.tactics,
        )

        return

    print("Nothing to do.")


if __name__ == "__main__":
    main()

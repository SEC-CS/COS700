"""
heuristic_baseline.py
=====================

Simple non-learning baseline for Metamath proof search.

This model implements the same interface as every learned model:

    generate_steps(goal, n)

It uses no neural network.

Instead it searches through the Metamath database looking for
theorems whose conclusions unify with the current goal.

The returned candidates are

    theorem_label {{ var : substitution }} ...

exactly the same format expected from a trained model.
"""

import itertools

def parse_goal(goal):

    try:

        i = goal.index("[[") + 2
        j = goal.index("]]")

        conclusion = goal[j + 2:].strip().split()

        return conclusion

    except Exception:

        return None

def unify(pattern, target, variables):

    subst = {}

    i = 0
    j = 0

    while i < len(pattern):

        token = pattern[i]

        if token in variables:

            #
            # Extremely simple baseline:
            # variable matches one token.
            #

            if j >= len(target):
                return None

            value = [target[j]]

            if token in subst:

                if subst[token] != value:
                    return None

            else:

                subst[token] = value

            i += 1
            j += 1

        else:

            if j >= len(target):
                return None

            if token != target[j]:
                return None

            i += 1
            j += 1

    if j != len(target):
        return None

    return subst

def format_step(label, subst):

    pieces = [label]

    for var in sorted(subst):

        value = subst[var]

        pieces.append(
            "{{ "
            + var
            + " : "
            + " ".join(value)
            + " }}"
        )

    return " ".join(pieces)

class Model:
    """
    Very simple non-learning baseline.

    For every goal:

      1. Iterate over every theorem.
      2. Attempt to unify its conclusion with the goal.
      3. If successful, emit

            theorem {{ substitutions }}

    ordered exactly as they are encountered in set.mm.

    No learning is performed.
    """

    def __init__(self, mm):

        self.mm = mm

        #
        # Cache all usable theorems.
        #

        self.theorems = []

        for label, (kind, data) in mm.labels.items():

            if kind not in ("$a", "$p"):
                continue

            distinct, mand_var, hyp, result = data

            variables = {
                var
                for _, var in mand_var
            }

            self.theorems.append(
                (
                    label,
                    variables,
                    result,
                )
            )
    def generate_steps(
                self,
                goal_str,
                n=32,
                temperature=1.0,
            ):

        goal = parse_goal(goal_str)

        if goal is None:
            return []

        candidates = []

        for (
            label,
            variables,
            conclusion,
        ) in self.theorems:

            subst = unify(
                conclusion,
                goal,
                variables,
            )

            if subst is None:
                continue

            candidates.append(
                (
                    format_step(
                        label,
                        subst,
                    ),
                    0.0,
                )
            )

            if len(candidates) >= n:
                break

        return candidates



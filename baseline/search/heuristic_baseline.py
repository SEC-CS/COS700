import json
import random
from utils.formatting import parse_goal,  format_proofstep

# Set this to True to rank candidates by training-data usage frequency
# instead of random shuffling. Requires PATH to point at data.
USE_FREQUENCY   = True
PATH = "data/train.jsonl"

class Model:
    """
    Uninformed baseline that proposes proof steps without any learning.

    This is the comparison point against which all learned models are
    evaluated. It uses two simple heuristics:

    1. Random sampling: randomly select theorems from the database and
       try trivial identity substitutions. No knowledge of the goal is used.
       Set USE_FREQUENCY = False

    2. Frequency heuristic: prefer theorems that appear most often in the
       training data (more frequently used theorems are more likely to be
       applicable). This is a weak signal but requires no learning.
       Set USE_FREQUENCY = True

    Because this model does not learn from data, it establishes the floor
    performance achievable without machine learning. Any learned model that
    cannot beat this baseline is not adding value.

    The log probability returned is always 0.0 (uniform) since this model
    has no confidence signal — all candidates are equally (un)informed.

    Before running take note of:
        1. This model is fully deterministic (log_prob always 0.0, no
           temperature effect on candidate selection) — so evaluate() can
           skip retry attempts entirely. 
           So use --attempts 1 flag
        2. Set USE_FREQUENCY above for random sampling/frequency heuristic
        3. Set PATH above to match the --eval flag

        uv run python proof_search.py --mm data/set.mm --eval data/valid.jsonl --demo --model-module models/heuristic_baseline.py --model-name heuristic_baseline --attempts 1

    """

    def __init__(self):
        self.mm = None
        self.candidate_labels = []

        if USE_FREQUENCY:
            print(f"Computing theorem frequencies from {PATH} ...")
            self.theorem_frequencies = count_theorem_frequencies(PATH)
        else:
            self.theorem_frequencies = None

    def set_mm(self, mm):
        """
        Attach the already-loaded Metamath database.
        """
        self.mm = mm

        self.candidate_labels = [
            label for label, (kind, _) in mm.labels.items()
            if kind in ('$a', '$p')
        ]

        if self.theorem_frequencies:
            self.candidate_labels.sort(
                key=lambda l: self.theorem_frequencies.get(l, 0),
                reverse=True
            )
        else:
            random.shuffle(self.candidate_labels)

    def generate_steps(self, goal_str, n=32, temperature=1.0):
        """
        Generate n candidate proof steps using heuristics only.

        Strategy: for each candidate theorem, attempt to build a trivial
        substitution where each variable maps to itself. This will only
        work for theorems whose conclusion already matches the goal
        without non-trivial substitutions — but it costs nothing to try
        and occasionally succeeds on simple goals.

        Returns candidates as (proofstep_string, log_prob) tuples
        with uniform log_prob=0.0 since no confidence signal exists.
        """
        goal = parse_goal(goal_str)
        if goal is None:
            return []

        conclusion = goal['conclusion']
        candidates = []

        for label in self.candidate_labels[:n * 10]:  
            if len(candidates) >= n:
                break

            try:
                kind, data = self.mm.labels[label]
                if kind not in ('$a', '$p'):
                    continue

                _, mand_var, hyp, result = data

                subst = {v: [v] for _, v in mand_var}

                substituted = self.mm.apply_subst(result, subst)
                if substituted != conclusion:
                    continue

                step_str = format_proofstep(label, subst)
                candidates.append((step_str, 0.0))

            except Exception:
                continue

        return candidates

def count_theorem_frequencies(train_jsonl: str) -> dict:
    """
    Count how many times each theorem label appears as an applied step
    in the training data.

    Used to initialise the frequency heuristic in the Model.
    More frequent theorems are tried first on the assumption that commonly
    used theorems are more likely to be applicable to any given goal.

    """
    from collections import Counter
    counts = Counter()
    with open(train_jsonl) as f:
        for line in f:
            record = json.loads(line)
            counts[record['theorem']] += 1
    return dict(counts)

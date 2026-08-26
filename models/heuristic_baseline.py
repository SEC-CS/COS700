import json
import random
from utils.formatting import parse_goal,  format_proofstep

class Model:
    """
    Uninformed baseline that proposes proof steps without any learning.

    This is the comparison point against which all learned models are
    evaluated. It uses two simple heuristics:

    1. Random sampling: randomly select theorems from the database and
       try trivial identity substitutions. No knowledge of the goal is used.

    2. Frequency heuristic: prefer theorems that appear most often in the
       training data (more frequently used theorems are more likely to be
       applicable). This is a weak signal but requires no learning.

    Because this model does not learn from data, it establishes the floor
    performance achievable without machine learning. Any learned model that
    cannot beat this baseline is not adding value.

    The log probability returned is always 0.0 (uniform) since this model
    has no confidence signal — all candidates are equally (un)informed.

    uv run python proof_search.py --mm data/set.mm --eval data/valid.jsonl --model models/heuristic_baseline.py
    """

    def __init__(self, theorem_frequencies: dict = None):
        self.mm = None
        self.candidate_labels = []
        self.theorem_frequencies = theorem_frequencies

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

        for label in self.candidate_labels[:n * 10]:  # oversample, filter down
            if len(candidates) >= n:
                break

            try:
                kind, data = self.mm.labels[label]
                if kind not in ('$a', '$p'):
                    continue

                _, mand_var, hyp, result = data

                # Try identity substitution: each variable maps to itself.
                # This only produces a *valid* step when the theorem's own
                # conclusion, unsubstituted, already equals the goal — but
                # it costs nothing to try and occasionally succeeds.
                subst = {v: [v] for _, v in mand_var}

                substituted = self.mm.apply_subst(result, subst)
                if substituted != conclusion:
                    continue

                # Build the proofstep string: just the applied theorem's
                # label plus its substitution. Subgoals are no longer
                # part of the string — the verifier derives them from
                # the theorem's own hypotheses.
                step_str = format_proofstep(label, subst)
                candidates.append((step_str, 0.0))

            except Exception:
                continue

        return candidates


# ---------------------------------------------------------------------------
# Theorem frequency counter (used to initialise the baseline)
# ---------------------------------------------------------------------------

def count_theorem_frequencies(train_jsonl: str) -> dict:
    """
    Count how many times each theorem label appears as an applied step
    in the training data.

    Used to initialise the frequency heuristic in HeuristicBaselineModel.
    More frequent theorems are tried first on the assumption that commonly
    used theorems are more likely to be applicable to any given goal.

    The new data format records the applied theorem directly in the
    'theorem' field of every step, so we no longer need to use
    'proof_label' (the theorem being *proved*) as an indirect proxy for
    it — we can count the actually-applied label exactly.
    """
    from collections import Counter
    counts = Counter()
    with open(train_jsonl) as f:
        for line in f:
            record = json.loads(line)
            counts[record['theorem']] += 1
    return dict(counts)

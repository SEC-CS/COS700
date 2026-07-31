import sys

sys.path.append("..")

import json
from proof_search import MetamathVerifier, load_model_from_module


def collect_teacher_predictions(
    teacher_model,
    verifier,
    training_goals_file,  # Your training data file
    output_file,
    n_candidates=32,
    temperature=1.0,
):
    """
    Generate training data from the teacher model.
    Each example: (goal_str, candidate_steps_with_logprobs)
    """
    training_data = []

    with open(training_goals_file) as f:
        for line in f:
            record = json.loads(line)
            goal = record["goal"]

            # Get teacher's predictions
            candidates = teacher_model.generate_steps(
                goal, n=n_candidates, temperature=temperature
            )

            # Optionally filter to only valid steps using verifier
            valid_steps = []
            for step_str, logprob in candidates:
                if verifier.apply_step(goal, step_str) is not None:
                    valid_steps.append((step_str, logprob))

            training_data.append(
                {
                    "goal": goal,
                    "candidates": valid_steps,  # Only valid steps
                    "all_candidates": candidates,  # All teacher outputs
                }
            )

    with open(output_file, "w") as f:
        for item in training_data:
            f.write(json.dumps(item) + "\n")

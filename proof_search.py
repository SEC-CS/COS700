"""
proof_search.py
===============
Proof search infrastructure for Metamath theorem proving.

This module provides everything needed to run proof search EXCEPT the model
itself. The model is treated as a pluggable component that is supplied later.

To use this system, implement a model class with the following interface:

    class YourModel:
        def generate_steps(
            self,
            goal_str: str,
            n: int = 32,
            temperature: float = 1.0,
        ) -> list[tuple[str, float]]:
            \"""
            Given a goal string in the format:
              "[[ |- hyp1   |- hyp2 ]] |- conclusion"

            Return a list of (proofstep_string, log_probability) tuples,
            deduplicated and sorted by log probability descending.

            proofstep_string format:
              "[[ |- subgoal1   |- subgoal2 ]] |- conclusion {{ var : val }}"

            log_probability: a float, more negative = less confident.
            \"""
            ...

Three model types are planned for this interface:
  1. A fine-tuned pre-trained language model (e.g. Mistral, LLaMA)
  2. A distilled smaller model trained from the fine-tuned model
  3. A custom neural network architecture built from scratch

All three will slot into this infrastructure without any changes here.

Usage:
  # Prove a single goal
  python proof_search.py --mm set.mm --goal "|- ( ph -> ph )" --model-module my_model.py

  # Evaluate on validation set
  python proof_search.py --mm set.mm --eval valid.jsonl --model-module my_model.py

  # Run in stub mode (no model) to verify infrastructure works
  python proof_search.py --mm set.mm --goal "|- ( ph -> ph )" --stub
"""

import heapq
import json
import argparse
import sys
import itertools
import importlib.util
import os
from dataclasses import dataclass, field
from typing import Optional


# ---------------------------------------------------------------------------
# Load mmverify
# ---------------------------------------------------------------------------

def load_mmverify(path: str):
    """Load mmverify.py as a module from a file path."""
    spec = importlib.util.spec_from_file_location("mmverify", path)
    mod  = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    mod.verbosity = 0  # silence all output
    return mod


# ---------------------------------------------------------------------------
# Stub model — used to test infrastructure without a real model
# ---------------------------------------------------------------------------

class StubModel:
    """
    A placeholder model that always returns empty candidates.

    Used to verify that the proof search infrastructure loads correctly,
    parses goals, calls the verifier, and handles the queue — all without
    needing a real model present.

    Every proof search attempt will fail (no proof found) because no
    candidates are ever generated, but the infrastructure around it
    will be exercised fully.

    Replace this with your real model class when ready.
    """

    def generate_steps(
        self,
        goal_str: str,
        n: int = 32,
        temperature: float = 1.0,
    ) -> list[tuple[str, float]]:
        """Returns no candidates — infrastructure test only."""
        print(f"    [StubModel] Would generate {n} candidates for:")
        print(f"    {goal_str[:100]}")
        return []


# ---------------------------------------------------------------------------
# Model loader — load a real model from an external module
# ---------------------------------------------------------------------------

def load_model_from_module(module_path: str):
    """
    Load a model from an external Python file.

    The external file must define a class called 'Model' that implements
    the generate_steps() interface described at the top of this file.

    Example my_model.py:

        class Model:
            def __init__(self):
                # load your model here
                pass

            def generate_steps(self, goal_str, n=32, temperature=1.0):
                # generate candidate proof steps here
                return [("PROOFSTEP ...", -0.5), ...]

    Usage:
        python proof_search.py --mm set.mm --eval valid.jsonl --model-module my_model.py
    """
    spec = importlib.util.spec_from_file_location("user_model", module_path)
    mod  = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)

    if not hasattr(mod, 'Model'):
        raise ValueError(
            f"{module_path} must define a class called 'Model' "
            f"with a generate_steps() method."
        )

    print(f"Loading model from {module_path} ...")
    model = mod.Model()
    print("Model loaded.")
    return model


# ---------------------------------------------------------------------------
# Metamath verifier wrapper
# ---------------------------------------------------------------------------

class MetamathVerifier:
    """
    Wraps mmverify's MM database to provide step-level verification.

    Once loaded with set.mm, you can call apply_step(goal, proofstep)
    to check whether a candidate tactic is valid for a given goal and,
    if so, what subgoals it generates.
    """

    def __init__(self, mmv, mm):
        self.mmv = mmv
        self.mm  = mm

    def parse_goal(self, goal_str: str) -> Optional[dict]:
        """
        Parse a goal string back into its components.

        Format:  [[ |- hyp1   |- hyp2 ]] |- conclusion

        Returns:
          {
            'e_hyps':     [['|-', 'ph'], ['|-', '(', 'ph', '->', 'ps', ')']],
            'conclusion': ['|-', 'ps'],
          }
        or None if parsing fails.
        """
        try:
            inner_start = goal_str.index('[[') + 2
            inner_end   = goal_str.index(']]')
            hyp_block   = goal_str[inner_start:inner_end].strip()
            conc_block  = goal_str[inner_end + 2:].strip()

            if hyp_block:
                e_hyps = [h.strip().split()
                          for h in hyp_block.split('   ')
                          if h.strip()]
            else:
                e_hyps = []

            conclusion = conc_block.split()
            return {'e_hyps': e_hyps, 'conclusion': conclusion}
        except Exception:
            return None

    def parse_proofstep(self, step_str: str) -> Optional[dict]:
        """
        Parse a proof step string back into its components.

        Format:
          [[ |- subgoal1   |- subgoal2 ]] |- conclusion {{ var1 : val1 }} ...

        Returns:
          {
            'conclusion': ['|-', 'ps'],
            'subgoals':   [['|-', 'ph'], ['|-', '(', 'ph', '->', 'ps', ')']],
            'subst':      {'ph': ['ph'], 'ps': ['ps']},
          }
        or None if parsing fails.
        """
        try:
            subst = {}
            s = step_str

            while '{{' in s:
                start     = s.index('{{')
                end       = s.index('}}', start)
                subst_str = s[start + 2:end].strip()
                colon     = subst_str.index(':')
                var       = subst_str[:colon].strip()
                val       = subst_str[colon + 1:].strip().split()
                subst[var] = val
                s = s[:start] + s[end + 2:]

            s = s.strip()

            inner_start = s.index('[[') + 2
            inner_end   = s.index(']]')
            hyp_block   = s[inner_start:inner_end].strip()
            conc_block  = s[inner_end + 2:].strip()

            if hyp_block:
                subgoals = [h.strip().split()
                            for h in hyp_block.split('   ')
                            if h.strip()]
            else:
                subgoals = []

            conclusion = conc_block.split()

            return {
                'conclusion': conclusion,
                'subgoals':   subgoals,
                'subst':      subst,
            }
        except Exception:
            return None

    def find_applied_label(self, conclusion: list,
                           subst: dict) -> Optional[str]:
        """
        Given a conclusion and substitution, find which theorem in the
        database was applied by searching for a match.
        """
        for label, (kind, data) in self.mm.labels.items():
            if kind not in ('$a', '$p'):
                continue
            _, _, _, result = data
            try:
                substituted = self.mm.apply_subst(result, subst)
                if substituted == conclusion:
                    return label
            except Exception:
                continue
        return None

    def apply_step(self, goal_str: str,
                   proofstep_str: str) -> Optional[list[str]]:
        """
        Try to apply a proof step to a goal.

        Returns a list of new subgoal strings if the step is valid,
        or None if the step is invalid.

        This is the core function called inside the proof search loop.
        """
        goal = self.parse_goal(goal_str)
        step = self.parse_proofstep(proofstep_str)

        if goal is None or step is None:
            return None

        if step['conclusion'] != goal['conclusion']:
            return None

        label = self.find_applied_label(step['conclusion'], step['subst'])
        if label is None:
            return None

        try:
            kind, data = self.mm.labels[label]
            if kind not in ('$a', '$p'):
                return None

            distinct, mand_var, hyp, result = data

            # Check distinct variable conditions
            for x, y in distinct:
                if x not in step['subst'] or y not in step['subst']:
                    continue
                x_vars = self.mm.find_vars(step['subst'][x])
                y_vars = self.mm.find_vars(step['subst'][y])
                for xv, yv in itertools.product(x_vars, y_vars):
                    if xv == yv or not self.mm.fs.lookup_d(xv, yv):
                        return None

            # Compute subgoals
            new_subgoals = []
            for h in hyp:
                subgoal_tokens = self.mm.apply_subst(h, step['subst'])
                subgoal_str    = format_goal(goal['e_hyps'], subgoal_tokens)
                new_subgoals.append(subgoal_str)

            return new_subgoals

        except Exception:
            return None


# ---------------------------------------------------------------------------
# Goal formatting
# ---------------------------------------------------------------------------

def format_goal(e_hyps: list, conclusion: list) -> str:
    if e_hyps:
        hyp_str = '   '.join(' '.join(h) for h in e_hyps)
        return f"[[ {hyp_str} ]] {' '.join(conclusion)}"
    else:
        return f"[[ ]] {' '.join(conclusion)}"


# ---------------------------------------------------------------------------
# Priority queue entry
# ---------------------------------------------------------------------------

@dataclass(order=True)
class GoalEntry:
    """
    Entry in the proof search priority queue.

    Priority is the negated cumulative log probability so that the most
    confident path (highest logprob) is expanded first in the min-heap.
    """
    priority:           float
    cumulative_logprob: float        = field(compare=False)
    goal_str:           str          = field(compare=False)
    parent_goal:        Optional[str] = field(compare=False, default=None)
    applied_step:       Optional[str] = field(compare=False, default=None)


# ---------------------------------------------------------------------------
# Proof search
# ---------------------------------------------------------------------------

def proof_search(
    root_goal_str:  str,
    model,
    verifier:       MetamathVerifier,
    max_expansions: int   = 128,
    n_tactics:      int   = 32,
    temperature:    float = 1.0,
    verbose:        bool  = False,
) -> Optional[dict]:
    """
    Run a proof search for a single goal.

    Parameters
    ----------
    root_goal_str : the goal to prove, in our format e.g. "[[ ]] |- ( ph -> ph )"
    model         : any object implementing generate_steps()
    verifier      : MetamathVerifier loaded with set.mm
    max_expansions: maximum number of goal expansions before giving up
    n_tactics     : number of candidate tactics to sample per goal
    temperature   : sampling temperature passed to the model
    verbose       : print progress

    Returns
    -------
    A proof tree dict if a proof is found:
      { goal_str: { 'step': proofstep_str, 'subgoals': [subgoal_str, ...] } }
    or None if the budget is exhausted without finding a proof.
    """
    proof_tree  = {}
    closed      = set()
    expansions  = 0

    heap = []
    root_entry = GoalEntry(
        priority=0.0,
        cumulative_logprob=0.0,
        goal_str=root_goal_str,
    )
    heapq.heappush(heap, root_entry)
    in_queue = {root_goal_str}

    def is_proved(goal: str) -> bool:
        if goal in closed:
            return True
        if goal not in proof_tree:
            return False
        if all(is_proved(sg) for sg in proof_tree[goal]['subgoals']):
            closed.add(goal)
            return True
        return False

    while heap and expansions < max_expansions:
        entry    = heapq.heappop(heap)
        goal_str = entry.goal_str

        if goal_str in closed:
            continue

        expansions += 1
        if verbose:
            print(f"\n[Expansion {expansions}/{max_expansions}] "
                  f"logprob={entry.cumulative_logprob:.2f}")
            print(f"  Goal: {goal_str[:100]}")

        # Ask the model for candidate tactics
        candidates = model.generate_steps(
            goal_str, n=n_tactics, temperature=temperature)

        for step_str, step_logprob in candidates:
            subgoals = verifier.apply_step(goal_str, step_str)

            if subgoals is None:
                continue

            if verbose:
                print(f"  Valid tactic found.")
                print(f"    Step:     {step_str[:80]}")
                print(f"    Subgoals: {len(subgoals)}")

            proof_tree[goal_str] = {
                'step':     step_str,
                'subgoals': subgoals,
            }

            child_logprob = entry.cumulative_logprob + step_logprob

            for subgoal in subgoals:
                if subgoal not in closed and subgoal not in in_queue:
                    heapq.heappush(heap, GoalEntry(
                        priority=-child_logprob,
                        cumulative_logprob=child_logprob,
                        goal_str=subgoal,
                        parent_goal=goal_str,
                        applied_step=step_str,
                    ))
                    in_queue.add(subgoal)

            if not subgoals:
                closed.add(goal_str)

            if is_proved(root_goal_str):
                if verbose:
                    print(f"\nProof found in {expansions} expansions.")
                return proof_tree

            break  # one valid tactic per expansion

    if verbose:
        print(f"\nNo proof found after {expansions} expansions.")
    return None


# ---------------------------------------------------------------------------
# Evaluation
# ---------------------------------------------------------------------------

def evaluate(
    model,
    verifier:       MetamathVerifier,
    split_file:     str,
    attempts:       int   = 4,
    max_expansions: int   = 128,
    n_tactics:      int   = 32,
    verbose:        bool  = False,
) -> float:
    """
    Evaluate the prover on a validation or test split.

    For each unique theorem in the split, runs `attempts` independent
    proof searches. A theorem is considered proved if any attempt succeeds.

    Returns the percentage of theorems proved.
    """
    # Collect unique theorems — use the first proof step's goal as root goal
    theorem_goals = {}
    with open(split_file) as f:
        for line in f:
            record = json.loads(line)
            label  = record['proof_label']
            if label not in theorem_goals:
                theorem_goals[label] = record['goal']

    theorems = list(theorem_goals.items())
    proved   = 0
    total    = len(theorems)

    print(f"\nEvaluating on {total} theorems ({attempts} attempts each) ...")

    for i, (label, root_goal) in enumerate(theorems):
        theorem_proved = False

        for attempt in range(attempts):
            result = proof_search(
                root_goal_str=root_goal,
                model=model,
                verifier=verifier,
                max_expansions=max_expansions,
                n_tactics=n_tactics,
                verbose=verbose,
            )
            if result is not None:
                theorem_proved = True
                break

        if theorem_proved:
            proved += 1

        if (i + 1) % 10 == 0:
            pct = proved / (i + 1) * 100
            print(f"  [{i+1}/{total}] proved: {proved} ({pct:.1f}%)")

    final_pct = proved / total * 100
    print(f"\nResult: {proved}/{total} = {final_pct:.2f}%")
    return final_pct


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description='Metamath proof search infrastructure'
    )
    parser.add_argument('--mm',           required=True,
                        help='Path to set.mm')
    parser.add_argument('--mmverify',     default=None,
                        help='Path to mmverify.py (default: same dir)')
    parser.add_argument('--model-module', default=None,
                        help='Path to a Python file defining a Model class')
    parser.add_argument('--stub',         action='store_true',
                        help='Use the stub model (no real model needed)')
    parser.add_argument('--goal',         default=None,
                        help='Single goal to prove e.g. "|- ( ph -> ph )"')
    parser.add_argument('--eval',         default=None,
                        help='Evaluate on a split file e.g. valid.jsonl')
    parser.add_argument('--attempts',     type=int, default=4,
                        help='Proof attempts per theorem (default: 4)')
    parser.add_argument('--expansions',   type=int, default=128,
                        help='Max expansions per attempt (default: 128)')
    parser.add_argument('--tactics',      type=int, default=32,
                        help='Tactics sampled per goal (default: 32)')
    parser.add_argument('--verbose',      action='store_true')
    args = parser.parse_args()

    # --- Validate arguments ---
    if not args.stub and not args.model_module:
        print("ERROR: supply either --stub or --model-module <path>")
        print()
        print("  --stub            test the infrastructure without a model")
        print("  --model-module    path to your model file (defines Model class)")
        sys.exit(1)

    if not args.goal and not args.eval:
        print("ERROR: supply either --goal or --eval")
        sys.exit(1)

    # --- Load mmverify ---
    mmverify_path = args.mmverify or os.path.join(
        os.path.dirname(__file__), 'mmverify.py')
    print(f"Loading mmverify from {mmverify_path} ...")
    mmv = load_mmverify(mmverify_path)

    # --- Load set.mm database ---
    print(f"Loading {args.mm} ...")
    mm = mmv.MM()
    with open(args.mm, 'r', encoding='utf-8', errors='replace') as f:
        mm.read(mmv.toks(f))
    print("Database loaded.")

    verifier = MetamathVerifier(mmv, mm)

    # --- Load model ---
    if args.stub:
        print("Using StubModel — no real model loaded.")
        model = StubModel()
    else:
        model = load_model_from_module(args.model_module)

    # --- Run ---
    if args.goal:
        root_goal = f"[[ ]] {args.goal}"
        print(f"\nProving: {root_goal}")
        result = proof_search(
            root_goal_str=root_goal,
            model=model,
            verifier=verifier,
            max_expansions=args.expansions,
            n_tactics=args.tactics,
            verbose=args.verbose,
        )
        if result:
            print("\nProof found!")
            for goal, info in result.items():
                print(f"  GOAL: {goal}")
                print(f"  STEP: {info['step']}")
                print()
        else:
            print("\nNo proof found.")

    elif args.eval:
        evaluate(
            model=model,
            verifier=verifier,
            split_file=args.eval,
            attempts=args.attempts,
            max_expansions=args.expansions,
            n_tactics=args.tactics,
            verbose=args.verbose,
        )


if __name__ == '__main__':
    main()

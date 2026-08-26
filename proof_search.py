"""
proof_search.py
===============
Proof search infrastructure for Metamath theorem proving.

This module provides everything needed to run proof search EXCEPT the
learned model itself. The model is a pluggable component supplied later.

To plug in a model, create a Python file defining a class called 'Model':

    class Model:
        def generate_steps(
            self,
            goal_str: str,
            n: int = 32,
            temperature: float = 1.0,
        ) -> list[tuple[str, float]]:
            \"""
            Input:
              goal_str — goal in the format:
                "[[ |- hyp1   |- hyp2 ]] |- conclusion"

            Output:
              List of (proofstep_string, log_probability) tuples,
              deduplicated, sorted by log_probability descending.

              proofstep_string format:
                "theorem_label {{ var1 : val1 }} {{ var2 : val2 }} ..."

              log_probability: float, more negative = less confident.
            \"""

Usage:
  # Run a fine-tuned model
  uv run python proof_search.py --mm data/set.mm --eval data/valid.jsonl --model-module my_model.py

  # Run a fine-tuned model in demo mode
  uv run python proof_search.py --demo --mm data/set.mm --eval data/valid.jsonl --model-module my_model.py

  # Evaluate on harder theorems only (last 20% of split by position)
  uv run python proof_search.py --mm data/set.mm --eval data/valid.jsonl --model-module my_model.py --hard-only
"""

import heapq
import json
import time
import argparse
import sys
import itertools
import importlib.util
import os
from dataclasses import dataclass, field
from typing import Optional
from utils.formatting import parse_goal, parse_proofstep, format_goal

def load_mmverify(path: str):
    """Load mmverify.py as a module from a file path."""
    spec = importlib.util.spec_from_file_location("mmverify", path)
    mod  = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    mod.verbosity = 0
    return mod

def load_model_from_module(module_path: str, mm):
    """
    Load a model from an external Python file.

    The file must define a class called 'Model' with generate_steps().
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
    if hasattr(model, "set_mm"):
        model.set_mm(mm)
    print("Model loaded.")
    return model


class MetamathVerifier:
    """
    Wraps mmverify's MM database for step-level proof verification.

    The core method is apply_step(goal_str, proofstep_str) which returns
    a list of new subgoal strings if the step is valid, or None if not.
    """

    def __init__(self, mmv, mm):
        self.mmv = mmv
        self.mm  = mm

    def apply_step(self, goal_str: str,
                   proofstep_str: str) -> Optional[list[str]]:
        """
        Validate a proof step against a goal.

        Returns new subgoal strings if valid, None if invalid.
        """
        goal = parse_goal(goal_str)
        step = parse_proofstep(proofstep_str)

        if goal is None or step is None:
            return None

        label = step['theorem']
        subst = step['subst']

        try:
            entry = self.mm.labels.get(label)
            if entry is None:
                return None
            kind, data = entry
            if kind not in ('$a', '$p'):
                return None

            distinct, mand_var, hyp, result = data

            # The predicted substitution must cover every mandatory
            # variable of the theorem being applied (its $f-hypothesis
            # variables). If the model omitted one, the step is
            # incomplete and can't be checked/applied.
            for _, v in mand_var:
                if v not in subst:
                    return None

            # The applied theorem's own conclusion, under the predicted
            # substitution, must equal the current goal's conclusion.
            substituted_result = self.mm.apply_subst(result, subst)
            if substituted_result != goal['conclusion']:
                return None

            # Check distinct variable conditions.
            # Some theorems only hold when certain variables are genuinely
            # distinct — e.g. universal generalisation requires that the
            # bound variable does not appear in the hypotheses.
            # For each ($d x y) constraint declared in the theorem:
            #   - find all variables inside subst(x) and subst(y)
            #   - verify no variable appears in both, AND that any pair
            #     of variables across the two sets are themselves declared
            #     distinct in the current scope.
            # If either check fails the substitution violates the constraint
            # and the step is invalid.
            for x, y in distinct:
                if x not in subst or y not in subst:
                    continue
                x_vars = self.mm.find_vars(subst[x])
                y_vars = self.mm.find_vars(subst[y])
                for xv, yv in itertools.product(x_vars, y_vars):
                    if xv == yv or not self.mm.fs.lookup_d(xv, yv):
                        return None

            # Compute subgoals by applying the substitution to each
            # essential hypothesis of the applied theorem
            new_subgoals = []
            for h in hyp:
                subgoal_tokens = self.mm.apply_subst(h, subst)
                subgoal_str    = format_goal(
                    goal['e_hyps'], subgoal_tokens)
                new_subgoals.append(subgoal_str)

            return new_subgoals

        except Exception:
            return None


@dataclass(order=True)
class GoalEntry:
    priority:           float
    cumulative_logprob: float         = field(compare=False)
    goal_str:           str           = field(compare=False)
    parent_goal:        Optional[str] = field(compare=False, default=None)
    applied_step:       Optional[str] = field(compare=False, default=None)

def proof_search(
    root_goal_str:  str,
    model,
    verifier:       MetamathVerifier,
    max_expansions: int   = 128,
    n_tactics:      int   = 32,
    temperature:    float = 1.0,
    verbose:        bool  = False,
    demo:           bool  = False,
) -> tuple[Optional[dict], dict]:
    """
    Run a proof search for a single goal.

    Returns
    -------
    (proof_tree, metrics)

    proof_tree: dict mapping goal -> {step, subgoals} if proved, else None
    metrics: {
        'expansions':          int   — goal expansions used
        'candidates_examined': int   — total tactics passed to verifier
        'valid_tactics_found': int   — tactics that passed verification
        'search_time_s':       float — wall clock time for this search
        'proved':              bool
    }
    """
    start_time = time.time()

    proof_tree         = {}
    closed             = set()
    expansions         = 0
    candidates_examined = 0
    valid_tactics_found = 0

    heap = []
    heapq.heappush(heap, GoalEntry(
        priority=0.0, cumulative_logprob=0.0, goal_str=root_goal_str))
    in_queue = {root_goal_str}

    def is_proved(goal: str, visiting: set = None) -> bool:
        if visiting is None:
            visiting = set()
        if goal in closed:
            return True
        if goal not in proof_tree:
            return False
        if goal in visiting:
            return False  # cycle — can't prove a goal via itself
        visiting.add(goal)
        result = all(is_proved(sg, visiting) for sg in proof_tree[goal]['subgoals'])
        visiting.discard(goal)
        if result:
            closed.add(goal)
        return result

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
        if demo:
            print(f"\n=== Expansion {expansions}/{max_expansions} "
                  f"(logprob={entry.cumulative_logprob:.2f}) ===")
            print(f"Goal: {goal_str}")

        candidates = model.generate_steps(
            goal_str, n=n_tactics, temperature=temperature)
        if demo:
            print(f"  {len(candidates)} candidate tactic(s) to try:")

        for step_str, step_logprob in candidates:
            candidates_examined += 1
            if demo:
                print(f"  Trying: {step_str}  (logprob={step_logprob:.2f})")
            subgoals = verifier.apply_step(goal_str, step_str)

            if subgoals is None:
                if demo:
                    print(f"    -> invalid")
                continue

            valid_tactics_found += 1
            if verbose:
                print(f"  Valid tactic. Subgoals: {len(subgoals)}")
            if demo:
                if subgoals:
                    print(f"    -> valid, {len(subgoals)} new subgoal(s):")
                    for sg in subgoals:
                        print(f"         {sg}")
                else:
                    print(f"    -> valid, no subgoals remaining (closed)")

            proof_tree[goal_str] = {'step': step_str, 'subgoals': subgoals}

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
                if demo:
                    print(f"\nRoot goal proved after {expansions} expansion(s).")
                elapsed = time.time() - start_time
                metrics = {
                    'expansions':           expansions,
                    'candidates_examined':  candidates_examined,
                    'valid_tactics_found':  valid_tactics_found,
                    'search_time_s':        elapsed,
                    'proved':               True,
                }
                return proof_tree, metrics

            break  # one valid tactic per expansion

    elapsed = time.time() - start_time
    metrics = {
        'expansions':           expansions,
        'candidates_examined':  candidates_examined,
        'valid_tactics_found':  valid_tactics_found,
        'search_time_s':        elapsed,
        'proved':               False,
    }
    return None, metrics



def count_proof_steps(proof_tree: dict) -> int:
    """Count the total number of steps in a completed proof tree."""
    if proof_tree is None:
        return 0
    return sum(1 + len(v['subgoals']) for v in proof_tree.values())


@dataclass
class TheoremResult:
    """All measurements for one theorem across all attempts."""
    label:                  str
    proved:                 bool
    best_search_time_s:     float   
    total_search_time_s:    float   
    total_expansions:       int     
    total_candidates:       int     
    proof_steps:            int     
    attempts_used:          int     
    difficulty_rank:        float   # 0.0 = easiest, 1.0 = hardest (by position)


def evaluate(
    model,
    verifier:        MetamathVerifier,
    split_file:      str,
    model_name:      str  = 'model',
    attempts:        int  = 4,
    max_expansions:  int  = 128,
    n_tactics:       int  = 32,
    hard_only:       bool = False,
    verbose:         bool = False,
    demo:            bool = False,
) -> tuple[dict, list[TheoremResult]]:
    """
    Evaluate the prover on a split and collect all metrics.

    Parameters
    ----------
    hard_only: if True, evaluate only on the hardest 20% of theorems
               Used for the scalability metric.

    Returns
    -------
    (summary, results)

    summary: aggregated metrics dict
    results: per-theorem TheoremResult list
    """
    theorem_goals = {}   
    theorem_order = []   

    with open(split_file) as f:
        for line in f:
            record = json.loads(line)
            label  = record['proof_label']
            if label not in theorem_goals:
                theorem_goals[label] = record['goal']
                theorem_order.append(label)

    if hard_only:
        cutoff = int(len(theorem_order) * 0.8)
        theorem_order = theorem_order[cutoff:]
        print(f"Hard-only mode: evaluating last 20% "
              f"({len(theorem_order)} theorems)")

    total = len(theorem_order)
    print(f"\nEvaluating '{model_name}' on {total} theorems "
          f"({attempts} attempts each, max {max_expansions} expansions) ...")

    results = []
    proved_count = 0

    for i, label in enumerate(theorem_order):
        root_goal    = theorem_goals[label]
        difficulty   = (theorem_order.index(label) / max(total - 1, 1))

        proved            = False
        best_time         = float('inf')
        total_time        = 0.0
        total_expansions  = 0
        total_candidates  = 0
        proof_steps       = 0
        attempts_used     = 0

        for _ in range(attempts):
            attempts_used += 1
            proof_tree, metrics = proof_search(
                root_goal_str=root_goal,
                model=model,
                verifier=verifier,
                max_expansions=max_expansions,
                n_tactics=n_tactics,
                verbose=verbose,
                demo=demo,
            )

            total_time       += metrics['search_time_s']
            total_expansions += metrics['expansions']
            total_candidates += metrics['candidates_examined']

            if proof_tree is not None:
                proved      = True
                best_time   = metrics['search_time_s']
                proof_steps = count_proof_steps(proof_tree)
                break

        if proved:
            proved_count += 1
        if best_time == float('inf'):
            best_time = total_time  

        results.append(TheoremResult(
            label               = label,
            proved              = proved,
            best_search_time_s  = best_time,
            total_search_time_s = total_time,
            total_expansions    = total_expansions,
            total_candidates    = total_candidates,
            proof_steps         = proof_steps,
            attempts_used       = attempts_used,
            difficulty_rank     = difficulty,
        ))

        if (i + 1) % 10 == 0:
            pct = proved_count / (i + 1) * 100
            avg_time = total_time / attempts_used
            print(f"  [{i+1}/{total}] proved={proved_count} "
                  f"({pct:.1f}%) avg_time={avg_time:.2f}s")

    proved_results   = [r for r in results if r.proved]
    n_proved         = len(proved_results)
    success_rate     = n_proved / total * 100

    avg_search_time  = (sum(r.best_search_time_s for r in proved_results)
                        / max(n_proved, 1))
    # Average only over theorems where at least one candidate was examined.
    # Averaging over all theorems (including those where the model returned
    # nothing) would drag the figure toward zero misleadingly.
    active_results   = [r for r in results if r.total_candidates > 0]
    avg_candidates   = (sum(r.total_candidates for r in active_results)
                        / max(len(active_results), 1))
    avg_proof_steps  = (sum(r.proof_steps for r in proved_results)
                        / max(n_proved, 1))

    hard_theorems    = [r for r in results if r.difficulty_rank >= 0.8]
    hard_proved      = sum(1 for r in hard_theorems if r.proved)
    hard_success_rate = (hard_proved / max(len(hard_theorems), 1) * 100)

    summary = {
        'model':                   model_name,
        'total_theorems':          total,
        'proved':                  n_proved,
        'theorem_success_rate_%':  round(success_rate, 2),
        'avg_search_time_s':       round(avg_search_time, 4),
        'avg_candidates_examined': round(avg_candidates, 1),
        'avg_proof_steps':         round(avg_proof_steps, 1),
        'hard_theorem_success_%':  round(hard_success_rate, 2),
    }

    print(f"\n{'='*60}")
    print(f"Results for: {model_name}")
    print(f"{'='*60}")
    print(f"  Theorem success rate      : {n_proved}/{total} "
          f"= {success_rate:.2f}%")
    print(f"  Avg search time (proved)  : {avg_search_time:.4f}s")
    print(f"  Avg candidates examined   : {avg_candidates:.1f} "
          f"(over {len(active_results)} theorems with any candidates)")
    print(f"  Avg proof length (steps)  : {avg_proof_steps:.1f}")
    print(f"  Hard theorem success rate : {hard_proved}/{len(hard_theorems)} "
          f"= {hard_success_rate:.2f}%")
    print(f"{'='*60}")

    return summary, results

def main():
    parser = argparse.ArgumentParser(
        description='Metamath proof search with full evaluation metrics'
    )
    parser.add_argument('--mm',           required=True,
                        help='Path to set.mm')
    parser.add_argument('--mmverify',     default="data/mmverify.py",
                        help='Path to mmverify.py (default: same dir)')
    parser.add_argument('--model-module', default=None,
                        help='Path to Python file defining Model class')
    parser.add_argument('--model-name',   default='learned_model',
                        help='Display name for the model in results')
    parser.add_argument('--train-jsonl',  default=None,
                        help='Training split')
    parser.add_argument('--goal',         default=None,
                        help='Single goal to prove e.g. "|- ( ph -> ph )"')
    parser.add_argument('--eval',         default=None,
                        help='Evaluate on a split file e.g. valid.jsonl')
    parser.add_argument('--attempts',     type=int,  default=4)
    parser.add_argument('--expansions',   type=int,  default=128)
    parser.add_argument('--tactics',      type=int,  default=32)
    parser.add_argument('--hard-only',    action='store_true',
                        help='Evaluate on hardest 20%% of theorems only')
    parser.add_argument('--verbose',      action='store_true')
    parser.add_argument('--demo',         action='store_true',
                        help='Print each candidate tactic tried and the '
                             'resulting subgoals in full, for live demos')
    args = parser.parse_args()

    if not args.goal and not args.eval:
        print("ERROR: supply either --goal or --eval")
        sys.exit(1)

    mmverify_path = args.mmverify or os.path.join(
        os.path.dirname(__file__), 'mmverify.py')
    print(f"Loading mmverify from {mmverify_path} ...")
    mmv = load_mmverify(mmverify_path)

    print(f"Loading {args.mm} ...")
    mm = mmv.MM()
    with open(args.mm, 'r', encoding='utf-8', errors='replace') as f:
        mm.read(mmv.toks(f))
    print("Database loaded.")

    verifier = MetamathVerifier(mmv, mm)

    models = {}

    if args.model_module:
        learned = load_model_from_module(args.model_module, mm)
        models[args.model_name] = learned

    if args.goal:
        model_name, model = next(iter(models.items()))
        root_goal = f"[[ ]] {args.goal}"
        print(f"\nProving: {root_goal}  (model: {model_name})")

        proof_tree, metrics = proof_search(
            root_goal_str=root_goal,
            model=model,
            verifier=verifier,
            max_expansions=args.expansions,
            n_tactics=args.tactics,
            verbose=args.verbose,
            demo=args.demo,
        )

        if proof_tree:
            print("\nProof found!")
            for goal, info in proof_tree.items():
                print(f"  GOAL: {goal}")
                print(f"  STEP: {info['step']}")
        else:
            print("\nNo proof found.")

        print(f"\nMetrics:")
        for k, v in metrics.items():
            print(f"  {k}: {v}")

    elif args.eval:
            model_name, model = next(iter(models.items()))
            evaluate(
                model=model,
                verifier=verifier,
                split_file=args.eval,
                model_name=model_name,
                attempts=args.attempts,
                max_expansions=args.expansions,
                n_tactics=args.tactics,
                hard_only=args.hard_only,
                verbose=args.verbose,
                demo=args.demo,
            )


if __name__ == '__main__':
    main()

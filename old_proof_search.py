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
                "[[ |- subgoal1   |- subgoal2 ]] |- conclusion {{ var : val }}"

              log_probability: float, more negative = less confident.
            \"""

Three model types are planned:
  1. Fine-tuned pre-trained language model (e.g. Mistral, LLaMA)
  2. Distilled smaller model trained from the fine-tuned model
  3. Custom neural network architecture built from scratch

All three slot in without changing anything in this file.

A heuristic baseline model is included here for comparison.

Usage:
  # Test infrastructure only (no model)
  python proof_search.py --mm set.mm --goal "|- ( ph -> ph )" --stub

  # Run heuristic baseline
  python proof_search.py --mm set.mm --eval valid.jsonl --baseline

  # Run a learned model
  python proof_search.py --mm set.mm --eval valid.jsonl --model-module my_model.py

  # Compare all available models and write results to CSV
  python proof_search.py --mm set.mm --eval valid.jsonl --baseline --compare-all --output results.csv

  # Evaluate on harder theorems only (last 20% of split by position)
  python proof_search.py --mm set.mm --eval valid.jsonl --model-module my_model.py --hard-only
"""

import heapq
import json
import time
import csv
import random
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
    mod.verbosity = 0
    return mod


# ---------------------------------------------------------------------------
# Stub model — tests infrastructure without any model
# ---------------------------------------------------------------------------

class StubModel:
    """
    Placeholder that always returns no candidates.

    Used to confirm the infrastructure (loading, parsing, queue, verifier)
    all work correctly before any model exists. Every proof search will
    fail (correctly) because no tactics are ever proposed.
    """

    def generate_steps(self, goal_str, n=32, temperature=1.0):
        print(f"    [StubModel] Would generate {n} candidates for:")
        print(f"    {goal_str[:100]}")
        return []


# ---------------------------------------------------------------------------
# Heuristic baseline model
# ---------------------------------------------------------------------------

class HeuristicBaselineModel:
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
    """

    def __init__(self, mm, theorem_frequencies: dict = None):
        """
        mm: the loaded mmverify MM database
        theorem_frequencies: optional dict of {label: count} from training data.
                             If provided, more frequent theorems are tried first.
                             If None, theorems are sampled randomly.
        """
        self.mm = mm

        # Collect all axioms and proven theorems as candidate labels
        self.candidate_labels = [
            label for label, (kind, _) in mm.labels.items()
            if kind in ('$a', '$p')
        ]

        if theorem_frequencies:
            # Sort by frequency descending so common theorems come first
            self.candidate_labels.sort(
                key=lambda l: theorem_frequencies.get(l, 0),
                reverse=True
            )
        else:
            random.shuffle(self.candidate_labels)

        self.theorem_frequencies = theorem_frequencies

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
        goal = _parse_goal(goal_str)
        if goal is None:
            return []

        conclusion = goal['conclusion']
        e_hyps     = goal['e_hyps']
        candidates = []

        for label in self.candidate_labels[:n * 10]:  # oversample, filter down
            if len(candidates) >= n:
                break

            try:
                kind, data = self.mm.labels[label]
                if kind not in ('$a', '$p'):
                    continue

                _, mand_var, hyp, result = data

                # Try identity substitution: each variable maps to itself
                subst = {v: [v] for _, v in mand_var}

                substituted = self.mm.apply_subst(result, subst)
                if substituted != conclusion:
                    continue

                # Build the proofstep string
                applied_e_hyps = [
                    self.mm.apply_subst(h, subst) for h in hyp
                ]
                step_str = _format_proofstep(applied_e_hyps, conclusion, subst)
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
    """
    from collections import Counter
    counts = Counter()
    with open(train_jsonl) as f:
        for line in f:
            record = json.loads(line)
            # The applied theorem label is embedded in the proof_step string.
            # We count the proof_label as a proxy (the theorem being proved
            # tells us which theorems its proof uses, indirectly).
            counts[record['proof_label']] += 1
    return dict(counts)


# ---------------------------------------------------------------------------
# Model loader
# ---------------------------------------------------------------------------

def load_model_from_module(module_path: str):
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
    print("Model loaded.")
    return model


# ---------------------------------------------------------------------------
# Metamath verifier wrapper
# ---------------------------------------------------------------------------

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
        Also returns the number of candidates examined (always 1 here —
        the caller accumulates this across all candidates tried).
        """
        goal = _parse_goal(goal_str)
        step = _parse_proofstep(proofstep_str)

        if goal is None or step is None:
            return None

        if step['conclusion'] != goal['conclusion']:
            return None

        label = self._find_applied_label(step['conclusion'], step['subst'])
        if label is None:
            return None

        try:
            kind, data = self.mm.labels[label]
            if kind not in ('$a', '$p'):
                return None

            distinct, mand_var, hyp, result = data

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
                if x not in step['subst'] or y not in step['subst']:
                    continue
                x_vars = self.mm.find_vars(step['subst'][x])
                y_vars = self.mm.find_vars(step['subst'][y])
                for xv, yv in itertools.product(x_vars, y_vars):
                    if xv == yv or not self.mm.fs.lookup_d(xv, yv):
                        return None

            # Compute subgoals by applying the substitution to each
            # essential hypothesis of the applied theorem
            new_subgoals = []
            for h in hyp:
                subgoal_tokens = self.mm.apply_subst(h, step['subst'])
                subgoal_str    = _format_goal(
                    goal['e_hyps'], subgoal_tokens)
                new_subgoals.append(subgoal_str)

            return new_subgoals

        except Exception:
            return None

    def _find_applied_label(self, conclusion: list,
                            subst: dict) -> Optional[str]:
        """Find which theorem was applied by matching conclusion + subst."""
        for label, (kind, data) in self.mm.labels.items():
            if kind not in ('$a', '$p'):
                continue
            _, _, _, result = data
            try:
                if self.mm.apply_subst(result, subst) == conclusion:
                    return label
            except Exception:
                continue
        return None


# ---------------------------------------------------------------------------
# Formatting helpers (shared between verifier, baseline, and search)
# ---------------------------------------------------------------------------

def _parse_goal(goal_str: str) -> Optional[dict]:
    try:
        inner_start = goal_str.index('[[') + 2
        inner_end   = goal_str.index(']]')
        hyp_block   = goal_str[inner_start:inner_end].strip()
        conc_block  = goal_str[inner_end + 2:].strip()
        e_hyps = ([h.strip().split() for h in hyp_block.split('   ')
                   if h.strip()] if hyp_block else [])
        return {'e_hyps': e_hyps, 'conclusion': conc_block.split()}
    except Exception:
        return None


def _parse_proofstep(step_str: str) -> Optional[dict]:
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
        subgoals = ([h.strip().split() for h in hyp_block.split('   ')
                     if h.strip()] if hyp_block else [])
        return {'conclusion': conc_block.split(),
                'subgoals': subgoals, 'subst': subst}
    except Exception:
        return None


def _format_goal(e_hyps: list, conclusion: list) -> str:
    if e_hyps:
        return f"[[ {'   '.join(' '.join(h) for h in e_hyps)} ]] {' '.join(conclusion)}"
    return f"[[ ]] {' '.join(conclusion)}"


def _format_proofstep(e_hyps: list, conclusion: list, subst: dict) -> str:
    hyp_part  = (f"[[ {'   '.join(' '.join(h) for h in e_hyps)} ]] "
                 if e_hyps else "[[ ]] ")
    subst_str = ' '.join(f"{{{{ {v} : {' '.join(val)} }}}}"
                         for v, val in sorted(subst.items()) if val)
    return f"{hyp_part}{' '.join(conclusion)}" + (f" {subst_str}" if subst_str else "")


# ---------------------------------------------------------------------------
# Priority queue entry
# ---------------------------------------------------------------------------

@dataclass(order=True)
class GoalEntry:
    priority:           float
    cumulative_logprob: float         = field(compare=False)
    goal_str:           str           = field(compare=False)
    parent_goal:        Optional[str] = field(compare=False, default=None)
    applied_step:       Optional[str] = field(compare=False, default=None)


# ---------------------------------------------------------------------------
# Proof search — returns result dict AND metrics
# ---------------------------------------------------------------------------

def proof_search(
    root_goal_str:  str,
    model,
    verifier:       MetamathVerifier,
    max_expansions: int   = 128,
    n_tactics:      int   = 32,
    temperature:    float = 1.0,
    verbose:        bool  = False,
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

        candidates = model.generate_steps(
            goal_str, n=n_tactics, temperature=temperature)

        for step_str, step_logprob in candidates:
            candidates_examined += 1
            subgoals = verifier.apply_step(goal_str, step_str)

            if subgoals is None:
                continue

            valid_tactics_found += 1
            if verbose:
                print(f"  Valid tactic. Subgoals: {len(subgoals)}")

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


# ---------------------------------------------------------------------------
# Proof length counter
# ---------------------------------------------------------------------------

def count_proof_steps(proof_tree: dict) -> int:
    """Count the total number of steps in a completed proof tree."""
    if proof_tree is None:
        return 0
    return sum(1 + len(v['subgoals']) for v in proof_tree.values())


# ---------------------------------------------------------------------------
# Evaluation with full metrics
# ---------------------------------------------------------------------------

@dataclass
class TheoremResult:
    """All measurements for one theorem across all attempts."""
    label:                  str
    proved:                 bool
    best_search_time_s:     float   # fastest successful attempt (or last attempt)
    total_search_time_s:    float   # sum across all attempts
    total_expansions:       int     # sum across all attempts
    total_candidates:       int     # total tactics passed to verifier
    proof_steps:            int     # steps in the found proof (0 if not proved)
    attempts_used:          int     # how many attempts before success (or max)
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
) -> tuple[dict, list[TheoremResult]]:
    """
    Evaluate the prover on a split and collect all metrics.

    Parameters
    ----------
    hard_only: if True, evaluate only on the hardest 20% of theorems
               (those appearing latest in the file, i.e. most complex).
               Used for the scalability metric.

    Returns
    -------
    (summary, results)

    summary: aggregated metrics dict
    results: per-theorem TheoremResult list
    """
    # --- Load theorems ---
    theorem_goals = {}   # label -> root goal string
    theorem_order = []   # labels in file order (proxy for difficulty)

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

        for attempt in range(attempts):
            attempts_used += 1
            proof_tree, metrics = proof_search(
                root_goal_str=root_goal,
                model=model,
                verifier=verifier,
                max_expansions=max_expansions,
                n_tactics=n_tactics,
                verbose=verbose,
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
            best_time = total_time  # use total if never proved

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

    # --- Aggregate metrics ---
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

    # Scalability: success rate on hard (top 20% difficulty) theorems
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


# ---------------------------------------------------------------------------
# Comparison runner
# ---------------------------------------------------------------------------

def run_comparison(
    models:         dict,       # {name: model_object}
    verifier:       MetamathVerifier,
    split_file:     str,
    output_csv:     str  = None,
    attempts:       int  = 4,
    max_expansions: int  = 128,
    n_tactics:      int  = 32,
    verbose:        bool = False,
):
    """
    Evaluate multiple models on the same split and print a comparison table.

    Models are evaluated in the order given. Results are written to a CSV
    if output_csv is specified.

    Training cost (time and memory) is NOT measured here because the models
    are loaded already trained — training cost should be recorded separately
    during the training runs for each model and added to the CSV manually.
    """
    all_summaries = []

    for name, model in models.items():
        summary, _ = evaluate(
            model=model,
            verifier=verifier,
            split_file=split_file,
            model_name=name,
            attempts=attempts,
            max_expansions=max_expansions,
            n_tactics=n_tactics,
            verbose=verbose,
        )
        all_summaries.append(summary)

    # Print comparison table
    metrics = [
        ('theorem_success_rate_%',  'Success rate (%)'),
        ('avg_search_time_s',       'Avg search time (s)'),
        ('avg_candidates_examined', 'Avg candidates examined'),
        ('avg_proof_steps',         'Avg proof steps'),
        ('hard_theorem_success_%',  'Hard theorem success (%)'),
    ]

    col_w = 28
    print(f"\n{'COMPARISON TABLE':=^{col_w * (len(all_summaries) + 1)}}")
    header = f"{'Metric':<{col_w}}" + ''.join(
        f"{s['model']:>{col_w}}" for s in all_summaries)
    print(header)
    print('-' * len(header))

    for key, display_name in metrics:
        row = f"{display_name:<{col_w}}"
        for s in all_summaries:
            row += f"{str(s.get(key, 'N/A')):>{col_w}}"
        print(row)

    # Write CSV
    if output_csv:
        with open(output_csv, 'w', newline='') as f:
            fieldnames = list(all_summaries[0].keys())
            writer = csv.DictWriter(f, fieldnames=fieldnames)
            writer.writeheader()
            writer.writerows(all_summaries)
        print(f"\nResults written to {output_csv}")
        print("Note: add training_time_s and training_memory_gb columns "
              "manually from your training run logs.")


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description='Metamath proof search with full evaluation metrics'
    )
    parser.add_argument('--mm',           required=True,
                        help='Path to set.mm')
    parser.add_argument('--mmverify',     default=None,
                        help='Path to mmverify.py (default: same dir)')
    parser.add_argument('--model-module', default=None,
                        help='Path to Python file defining Model class')
    parser.add_argument('--model-name',   default='learned_model',
                        help='Display name for the model in results')
    parser.add_argument('--stub',         action='store_true',
                        help='Use stub model (infrastructure test only)')
    parser.add_argument('--baseline',     action='store_true',
                        help='Run heuristic baseline model')
    parser.add_argument('--train-jsonl',  default=None,
                        help='Training split for baseline frequency heuristic')
    parser.add_argument('--compare-all',  action='store_true',
                        help='Run all available models and print comparison')
    parser.add_argument('--goal',         default=None,
                        help='Single goal to prove e.g. "|- ( ph -> ph )"')
    parser.add_argument('--eval',         default=None,
                        help='Evaluate on a split file e.g. valid.jsonl')
    parser.add_argument('--attempts',     type=int,  default=4)
    parser.add_argument('--expansions',   type=int,  default=128)
    parser.add_argument('--tactics',      type=int,  default=32)
    parser.add_argument('--hard-only',    action='store_true',
                        help='Evaluate on hardest 20%% of theorems only')
    parser.add_argument('--output',       default=None,
                        help='CSV file to write comparison results')
    parser.add_argument('--verbose',      action='store_true')
    args = parser.parse_args()

    if not args.stub and not args.baseline and not args.model_module:
        print("ERROR: supply one of --stub, --baseline, or --model-module")
        sys.exit(1)

    if not args.goal and not args.eval:
        print("ERROR: supply either --goal or --eval")
        sys.exit(1)

    # --- Load mmverify and database ---
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

    # --- Build models dict ---
    models = {}

    if args.stub:
        models['stub'] = StubModel()

    if args.baseline:
        freqs = None
        if args.train_jsonl:
            print("Counting theorem frequencies from training data ...")
            freqs = count_theorem_frequencies(args.train_jsonl)
        models['heuristic_baseline'] = HeuristicBaselineModel(mm, freqs)

    if args.model_module:
        learned = load_model_from_module(args.model_module)
        models[args.model_name] = learned

    # --- Single goal mode ---
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

    # --- Evaluation mode ---
    elif args.eval:
        if args.compare_all and len(models) > 1:
            run_comparison(
                models=models,
                verifier=verifier,
                split_file=args.eval,
                output_csv=args.output,
                attempts=args.attempts,
                max_expansions=args.expansions,
                n_tactics=args.tactics,
                verbose=args.verbose,
            )
        else:
            # Single model evaluation
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
            )


if __name__ == '__main__':
    main()

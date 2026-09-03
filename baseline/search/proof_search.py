"""
proof_search.py
===============

See help with `python proof_search.py --help` for usage.

Usage example:
# Run proof search with 1 attempt and 64 expansions, writing proved theorems to proved_theorems.txt and expansion counts to expansions.csv:
uv run python proof_search.py --mm data/set.mm --eval data/valid.jsonl --model-module model.py --proved-output proved_theorems.txt --expansions-output expansions.csv --attempts 1 --expansions 64
   
  
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
    heartbeat_every: int  = 20,
) -> tuple[Optional[dict], dict]:
    """
    Run a proof search for a single goal using Best-First Search.

    Returns
    -------
    (proof_tree, metrics)

    proof_tree: dict mapping goal -> list of derivations tried for that goal.
        Use extract_proof(root_goal, proof_tree) to pull out the single
        derivation that actually proves the theorem.
    metrics: {
        'expansions':          int   — goal expansions used
        'candidates_examined': int   — total tactics passed to verifier
        'valid_tactics_found': int   — tactics that passed verification
        'search_time_s':       float — wall clock time for this search
        'proved':              bool
    }
    """
    start_time = time.time()

    proof_tree          = {}
    closed              = set()
    expansions          = 0
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
        if goal not in proof_tree or not proof_tree[goal]:
            return False
        if goal in visiting:
            return False  # cycle — can't prove a goal via itself
        visiting.add(goal)
        result = any(
            all(is_proved(sg, visiting) for sg in alt['subgoals'])
            for alt in proof_tree[goal]
        )
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

        if heartbeat_every and expansions % heartbeat_every == 0:
            elapsed = time.time() - start_time
            preview = goal_str if len(goal_str) <= 60 else goal_str[:57] + "..."
            print(f"    ... still searching: expansion {expansions}/"
                  f"{max_expansions}, {valid_tactics_found} valid tactic(s) "
                  f"so far, {elapsed:.0f}s elapsed  (on: {preview})",
                  flush=True)

        candidates = model.generate_steps(
            goal_str, n=n_tactics, temperature=temperature)

        if demo and len(candidates) != 0:
            print(f"\n=== Expansion {expansions}/{max_expansions} "
                  f"(logprob={entry.cumulative_logprob:.2f}) ===")
            print(f"Goal: {goal_str}")
            print(f"  {len(candidates)} candidate tactic(s) to try:")

        proof_tree.setdefault(goal_str, [])

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

            proof_tree[goal_str].append({'step': step_str, 'subgoals': subgoals})

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

            # Best-First Search: Commit to the first valid tactic found for
            # this goal expansion and move on to the next highest-priority node.
            break

    elapsed = time.time() - start_time
    metrics = {
        'expansions':           expansions,
        'candidates_examined':  candidates_examined,
        'valid_tactics_found':  valid_tactics_found,
        'search_time_s':        elapsed,
        'proved':               False,
    }
    return None, metrics


def format_duration(seconds: float) -> str:
    """Human-readable duration for progress lines, e.g. 7290 -> '2h1m'."""
    seconds = max(0, int(seconds))
    h, rem = divmod(seconds, 3600)
    m, s = divmod(rem, 60)
    if h:
        return f"{h}h{m}m"
    if m:
        return f"{m}m{s}s"
    return f"{s}s"


def count_proof_steps(proof_tree: dict) -> int:
    """Count the total number of steps in a completed proof tree."""
    if proof_tree is None:
        return 0
    return sum(1 + len(v['subgoals']) for v in proof_tree.values())


def extract_proof(root_goal: str, proof_tree: dict) -> Optional[dict]:
    """
    Extracts a clean {goal: {step, subgoals}} tree top-down from root_goal,
    picking the alternative derivation whose subgoals are fully provable.
    """
    clean = {}
    memo  = {}

    def provable(goal: str, visiting: set) -> bool:
        if goal in memo:
            return memo[goal]
        if goal not in proof_tree or goal in visiting:
            memo[goal] = False
            return False
        visiting.add(goal)
        for alt in proof_tree[goal]:
            if all(provable(sg, visiting) for sg in alt['subgoals']):
                clean[goal] = alt
                visiting.discard(goal)
                memo[goal] = True
                return True
        visiting.discard(goal)
        memo[goal] = False
        return False

    if not provable(root_goal, set()):
        return None
    return clean


def format_proved_theorem(label: str, root_goal: str, clean_proof: dict) -> str:
    """
    Render one fully-proved theorem as a text block: its label, root
    goal, and every step of its actual proof as
    "theorem_label {{ var : val }} ...".
    """
    lines = [f"THEOREM: {label}", f"GOAL: {root_goal}"]
    for goal, info in clean_proof.items():
        lines.append(f"  GOAL: {goal}")
        lines.append(f"  STEP: {info['step']}")
    lines.append("")
    return "\n".join(lines)


@dataclass
class TheoremResult:
    """All measurements for one theorem across all attempts."""
    label:                  str
    proved:                 bool
    best_search_time_s:     float   
    best_expansions:        int     
    total_search_time_s:    float   
    total_expansions:       int     
    total_candidates:       int     
    proof_steps:            int     
    attempts_used:          int     
    difficulty_rank:        float   


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
    proved_output:   str  = None,
    expansions_output: str = None,
    progress_every:  int  = 1,
    heartbeat_every: int  = 20,
) -> tuple[dict, list[TheoremResult]]:
    """
    Evaluate the prover on a split and collect all metrics.
    """
    theorem_goals = {}   
    theorem_order = []   

    with open(split_file) as f:
        for line in f:
            record = json.loads(line)
            label  = record['proof_label']
            if label not in theorem_goals:
                theorem_order.append(label)
            theorem_goals[label] = record['goal']

    if hard_only:
        cutoff = int(len(theorem_order) * 0.8)
        theorem_order = theorem_order[cutoff:]
        print(f"Hard-only mode: evaluating last 20% "
              f"({len(theorem_order)} theorems)")

    total = len(theorem_order)
    print(f"\nEvaluating '{model_name}' on {total} theorems "
          f"({attempts} attempts each, max {max_expansions} expansions) ...",
          flush=True)

    overall_start = time.time()

    results = []
    proved_count = 0
    theorems_written = 0  

    proved_file = open(proved_output, 'w') if proved_output else None

    expansions_file = None
    if expansions_output:
        expansions_file = open(expansions_output, 'w')
        expansions_file.write("proof_label,expansions\n")

    for i, label in enumerate(theorem_order):
        root_goal    = theorem_goals[label]
        difficulty   = (theorem_order.index(label) / max(total - 1, 1))

        if heartbeat_every:
            print(f"  [{i+1}/{total}] starting {label} ...", flush=True)

        proved            = False
        best_time         = float('inf')
        best_expansions   = -1
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
                heartbeat_every=heartbeat_every,
            )

            total_time       += metrics['search_time_s']
            total_expansions += metrics['expansions']
            total_candidates += metrics['candidates_examined']

            if proof_tree is not None:
                proved      = True
                best_time   = metrics['search_time_s']
                best_expansions = metrics['expansions']
                if expansions_file is not None:
                    expansions_file.write(f"{label},{best_expansions}\n")
                clean_proof = extract_proof(root_goal, proof_tree)
                proof_steps = count_proof_steps(clean_proof)
                if proved_file is not None and clean_proof is not None:
                    proved_file.write(
                        format_proved_theorem(label, root_goal, clean_proof))
                    theorems_written += 1
                break

        if proved:
            proved_count += 1
        if best_time == float('inf'):
            best_time = total_time  

        results.append(TheoremResult(
            label               = label,
            proved              = proved,
            best_search_time_s  = best_time,
            best_expansions     = best_expansions,
            total_search_time_s = total_time,
            total_expansions    = total_expansions,
            total_candidates    = total_candidates,
            proof_steps         = proof_steps,
            attempts_used       = attempts_used,
            difficulty_rank     = difficulty,
        ))

        if progress_every and (i + 1) % progress_every == 0:
            elapsed  = time.time() - overall_start
            avg_time = elapsed / (i + 1)
            eta      = avg_time * (total - (i + 1))
            pct      = proved_count / (i + 1) * 100
            print(f"  [{i+1}/{total}] {label}  proved={proved_count} "
                  f"({pct:.1f}%)  elapsed={format_duration(elapsed)}  "
                  f"eta={format_duration(eta)}", flush=True)

    if proved_file is not None:
        proved_file.close()
    if expansions_file is not None:
        expansions_file.close()

    proved_results   = [r for r in results if r.proved]
    n_proved         = len(proved_results)
    success_rate     = n_proved / total * 100

    avg_search_time  = (sum(r.best_search_time_s for r in proved_results)
                        / max(n_proved, 1))
    avg_expansions_used = (sum(r.best_expansions for r in proved_results)
                           / max(n_proved, 1))
    max_expansions_used = (max((r.best_expansions for r in proved_results),
                                default=0))
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
        'avg_expansions_used':     round(avg_expansions_used, 1),
        'max_expansions_used':     max_expansions_used,
        'avg_candidates_examined': round(avg_candidates, 1),
        'avg_proof_steps':         round(avg_proof_steps, 1),
        'hard_theorem_success_%':  round(hard_success_rate, 2),
        'theorems_written_to_file': theorems_written,
    }

    print(f"\n{'='*60}")
    print(f"Results for: {model_name}")
    print(f"{'='*60}")
    print(f"  Theorem success rate      : {n_proved}/{total} "
          f"= {success_rate:.2f}%")
    print(f"  Avg search time (proved)  : {avg_search_time:.4f}s")
    print(f"  Expansions used (proved)  : avg={avg_expansions_used:.1f}, "
          f"max={max_expansions_used}  (out of a budget of "
          f"{max_expansions} -- max_expansions can likely be lowered "
          f"toward the max shown here, with a little headroom, without "
          f"losing any of these successes)")
    print(f"  Avg candidates examined   : {avg_candidates:.1f} "
          f"(over {len(active_results)} theorems with any candidates)")
    print(f"  Avg proof length (steps)  : {avg_proof_steps:.1f}")
    print(f"  Hard theorem success rate : {hard_proved}/{len(hard_theorems)} "
          f"= {hard_success_rate:.2f}%")
    if proved_output:
        print(f"  Theorems written to file  : {theorems_written} "
              f"(fully closed proofs only -- {proved_output})")
        assert theorems_written == n_proved, (
            "theorems_written should always equal n_proved: every "
            "theorem counted as proved gets a clean extracted proof "
        )
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
                        help='Single goal to prove, in full -- same '
                             'shape as a JSONL "goal" field, e.g. '
                             '"[[ ]] |- ( ph -> ph )" for no hypotheses, '
                             'or "[[ |- ph ]] |- ( ph \\/ ps )" with one')
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
    parser.add_argument('--proved-output', default=None,
                        help='Path to write every fully-proved theorem '
                             '(only the steps actually used in its '
                             'finished proof) to as a text file, '
                             'during --eval')
    parser.add_argument('--expansions-output', default=None,
                        help='Path to write a CSV of proof_label,'
                             'expansions -- the number of expansions '
                             'the successful attempt used -- for every '
                             'proved theorem, during --eval')
    parser.add_argument('--progress-every', type=int, default=1,
                         help='Print a progress line (with elapsed '
                              'time and ETA) every this many theorems '
                              'during --eval (default: 1, i.e. every '
                              'theorem)')
    parser.add_argument('--heartbeat-every', type=int, default=20,
                         help='Print a "starting theorem" line and a '
                              '"still searching" line every this many '
                              'expansions, so a slow theorem is '
                              'distinguishable from a hang (default: '
                              '20; 0 disables both)')
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
        root_goal = args.goal
        print(f"\nProving: {root_goal}  (model: {model_name})")

        proof_tree, metrics = proof_search(
            root_goal_str=root_goal,
            model=model,
            verifier=verifier,
            max_expansions=args.expansions,
            n_tactics=args.tactics,
            verbose=args.verbose,
            demo=args.demo,
            heartbeat_every=args.heartbeat_every,
        )

        if proof_tree:
            print("\nProof found!")
            clean_proof = extract_proof(root_goal, proof_tree)
            for goal, info in (clean_proof or {}).items():
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
                proved_output=args.proved_output,
                expansions_output=args.expansions_output,
                progress_every=args.progress_every,
                heartbeat_every=args.heartbeat_every,
            )


if __name__ == '__main__':
    main()
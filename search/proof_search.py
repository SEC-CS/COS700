"""
Run verifier-checked proof search with a model over each theorem in an evaluation split,
recording proved theorems and expansion counts.
"""

import argparse
import heapq
import importlib.util
import json
import os
import sys
import time
from dataclasses import dataclass, field
from typing import Optional

from utils.formatting import (
    format_goal,
    format_proofstep,
    parse_goal,
    parse_proofstep,
)
from utils.grammar import Grammar, make_scoped_mm
from utils.matcher import (
    DEFAULT_CACHE,
    DEFAULT_CAP,
    complete,
    determined_key,
    label_table,
)


def load_mmverify(path: str):
    """Load mmverify.py as a module from a file path."""
    spec = importlib.util.spec_from_file_location("mmverify", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    mod.verbosity = 0
    return mod


def load_model_from_module(
    module_path: str,
    mm,
    model_dir: str | None = None,
    base_model_module: str | None = None,
):
    """
    Load a model from an external Python file.

    The file must define a class called 'Model' with generate_steps().
    If model_dir is given, it is passed to Model(model_dir).
    """
    spec = importlib.util.spec_from_file_location("user_model", module_path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)

    if not hasattr(mod, "Model"):
        raise ValueError(
            f"{module_path} must define a class called 'Model' "
            f"with a generate_steps() method."
        )

    print(f"Loading model from {module_path} ...")
    if base_model_module is not None:
        model = mod.Model(model_dir=model_dir, base_model_module=base_model_module)
    else:
        model = mod.Model(model_dir=model_dir) if model_dir else mod.Model()
    if hasattr(model, "set_mm"):
        model.set_mm(mm)
    print("Model loaded.")
    return model


def load_module_from_path(module_path: str):
    """Import a Python module from a file path."""
    spec = importlib.util.spec_from_file_location("user_model_module", module_path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def detect_model_module_from_argv(argv: list[str]) -> str | None:
    for i, arg in enumerate(argv):
        if arg == "--model-module" and i + 1 < len(argv):
            return argv[i + 1]
        if arg.startswith("--model-module="):
            return arg.split("=", 1)[1]
    return None

class MetamathVerifier:
    """
    Wraps mmverify's MM database for step-level proof verification.

    The core method is apply_step(goal_str, proofstep_str) which returns
    a list of new subgoal strings if the step is valid, or None if not.

    """

    def __init__(self, mmv, mm):
        self.mmv = mmv
        self.mm = mm
        self.grammar = Grammar(mm)
        self.position = {label: i for i, label in enumerate(mm.labels)}
        self.target = None

    def set_target(self, label: Optional[str]) -> None:
        if label is not None and label not in self.mm.scopes:
            raise KeyError(f"{label} is not a $p in the database")
        self.target = label

    def apply_step(self, goal_str: str, proofstep_str: str) -> Optional[list[str]]:
        """
        Validate a proof step against a goal.

        Returns new subgoal strings if valid, None if invalid.
        """
        goal = parse_goal(goal_str)
        step = parse_proofstep(proofstep_str)

        if goal is None or step is None:
            return None

        label = step["theorem"]
        subst = step["subst"]

        try:
            entry = self.mm.labels.get(label)
            if entry is None:
                return None
            kind, data = entry
            if kind not in ("$a", "$p"):
                return None

            distinct, mand_var, hyp, result = data

            for _, v in mand_var:
                if v not in subst:
                    return None

            substituted_result = self.mm.apply_subst(result, subst)
            if substituted_result != goal["conclusion"]:
                return None

            if self.target is not None:
                if self.position[label] >= self.position[self.target]:
                    return None
                scope = self.mm.scopes[self.target]
            else:
                scope = (None, None)
            if self.grammar.step_violation(mand_var, distinct, subst, scope):
                return None

            new_subgoals = []
            for h in hyp:
                subgoal_tokens = self.mm.apply_subst(h, subst)
                subgoal_str = format_goal(goal["e_hyps"], subgoal_tokens)
                new_subgoals.append(subgoal_str)

            return new_subgoals

        except Exception:
            return None


# Step recorded for a goal closed by one of the theorem's own hypotheses.
# "$e" can never be a database label, so it cannot collide with a theorem.
HYPOTHESIS_STEP = "$e"


@dataclass(order=True)
class GoalEntry:
    priority: float
    cumulative_logprob: float = field(compare=False)
    goal_str: str = field(compare=False)
    parent_goal: Optional[str] = field(compare=False, default=None)
    applied_step: Optional[str] = field(compare=False, default=None)


def proof_search(
    root_goal_str: str,
    model,
    verifier: MetamathVerifier,
    max_expansions: int = 128,
    n_tactics: int = 32,
    temperature: float = 1.0,
    verbose: bool = False,
    demo: bool = False,
    heartbeat_every: int = 20,
    excluded_labels: set[str] = None,
    max_valid_per_goal: int = 1,
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
    if max_valid_per_goal < 1:
        raise ValueError("max_valid_per_goal must be at least 1")

    excluded_labels = excluded_labels or set()

    # Residual models can avoid expensive completion for labels that are not
    # allowed in this search. Other model implementations are filtered below.
    set_excluded_labels = getattr(model, "set_excluded_labels", None)
    if set_excluded_labels is not None:
        set_excluded_labels(excluded_labels)

    proof_tree = {}
    closed = set()
    expansions = 0
    candidates_examined = 0
    valid_tactics_found = 0

    def close_by_hypothesis(goal_str: str) -> bool:
        # A goal identical to one of the theorem's own $e hypotheses is
        # proved by citing that hypothesis; no theorem application can close it.
        goal = parse_goal(goal_str)
        if goal is None or goal["conclusion"] not in goal["e_hyps"]:
            return False
        proof_tree[goal_str] = [
            {"step": HYPOTHESIS_STEP, "subgoals": [], "candidate_rank": 1}
        ]
        closed.add(goal_str)
        return True

    if close_by_hypothesis(root_goal_str):
        metrics = {
            "expansions": 0,
            "candidates_examined": 0,
            "valid_tactics_found": 0,
            "search_time_s": time.time() - start_time,
            "proved": True,
        }
        return proof_tree, metrics

    heap = []
    heapq.heappush(
        heap, GoalEntry(priority=0.0, cumulative_logprob=0.0, goal_str=root_goal_str)
    )
    in_queue = {root_goal_str}

    def root_proved() -> bool:
        changed = True
        while changed:
            changed = False
            for goal, alternatives in proof_tree.items():
                if goal in closed:
                    continue
                if any(
                    all(subgoal in closed for subgoal in alt["subgoals"])
                    for alt in alternatives
                ):
                    closed.add(goal)
                    changed = True
        return root_goal_str in closed

    while heap and expansions < max_expansions:
        entry = heapq.heappop(heap)
        goal_str = entry.goal_str

        if goal_str in closed:
            continue

        expansions += 1

        if heartbeat_every and expansions % heartbeat_every == 0:
            elapsed = time.time() - start_time
            preview = goal_str if len(goal_str) <= 60 else goal_str[:57] + "..."
            print(
                f"    ... still searching: expansion {expansions}/"
                f"{max_expansions}, {valid_tactics_found} valid tactic(s) "
                f"so far, {elapsed:.0f}s elapsed  (on: {preview})",
                flush=True,
            )

        candidates = model.generate_steps(
            goal_str, n=n_tactics, temperature=temperature
        )

        if demo and len(candidates) != 0:
            print(
                f"\n=== Expansion {expansions}/{max_expansions} "
                f"(logprob={entry.cumulative_logprob:.2f}) ==="
            )
            print(f"Goal: {goal_str}")
            print(f"  {len(candidates)} candidate tactic(s) to try:")

        proof_tree.setdefault(goal_str, [])

        valid_candidate_ranks = {}
        seen_steps = set()
        for step_str, step_logprob in candidates:
            if step_str in seen_steps:
                continue
            seen_steps.add(step_str)

            parsed_step = parse_proofstep(step_str)
            if parsed_step is not None and parsed_step["theorem"] in excluded_labels:
                continue

            candidate_key_fn = getattr(model, "candidate_group_key", None)
            if candidate_key_fn is not None:
                candidate_key = candidate_key_fn(step_str)
            elif parsed_step is not None:
                candidate_key = (
                    parsed_step["theorem"],
                    tuple(
                        sorted(
                            (var, tuple(value))
                            for var, value in parsed_step["subst"].items()
                        )
                    ),
                )
            else:
                candidate_key = step_str

            if (
                len(valid_candidate_ranks) >= max_valid_per_goal
                and candidate_key not in valid_candidate_ranks
            ):
                break

            candidates_examined += 1
            if demo:
                print(f"  Trying: {step_str}  (logprob={step_logprob:.2f})")
            subgoals = verifier.apply_step(goal_str, step_str)

            if subgoals is None:
                if demo:
                    print(f"    -> invalid")
                continue

            valid_tactics_found += 1
            candidate_rank = valid_candidate_ranks.get(candidate_key)
            if candidate_rank is None:
                candidate_rank = len(valid_candidate_ranks) + 1
                valid_candidate_ranks[candidate_key] = candidate_rank
            if verbose:
                print(f"  Valid tactic. Subgoals: {len(subgoals)}")
            if demo:
                if subgoals:
                    print(f"    -> valid, {len(subgoals)} new subgoal(s):")
                    for sg in subgoals:
                        print(f"         {sg}")
                else:
                    print(f"    -> valid, no subgoals remaining (closed)")

            proof_tree[goal_str].append(
                {
                    "step": step_str,
                    "subgoals": subgoals,
                    "candidate_rank": candidate_rank,
                }
            )

            child_logprob = entry.cumulative_logprob + step_logprob
            for subgoal in subgoals:
                if subgoal in closed or close_by_hypothesis(subgoal):
                    continue
                if subgoal not in in_queue:
                    heapq.heappush(
                        heap,
                        GoalEntry(
                            priority=-child_logprob,
                            cumulative_logprob=child_logprob,
                            goal_str=subgoal,
                            parent_goal=goal_str,
                            applied_step=step_str,
                        ),
                    )
                    in_queue.add(subgoal)

            if not subgoals:
                closed.add(goal_str)

            if root_proved():
                if demo:
                    print(f"\nRoot goal proved after {expansions} expansion(s).")
                elapsed = time.time() - start_time
                metrics = {
                    "expansions": expansions,
                    "candidates_examined": candidates_examined,
                    "valid_tactics_found": valid_tactics_found,
                    "search_time_s": elapsed,
                    "proved": True,
                }
                return proof_tree, metrics

    elapsed = time.time() - start_time
    metrics = {
        "expansions": expansions,
        "candidates_examined": candidates_examined,
        "valid_tactics_found": valid_tactics_found,
        "search_time_s": elapsed,
        "proved": False,
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
    return sum(
        1 + len(v["subgoals"])
        for v in proof_tree.values()
        if v["step"] != HYPOTHESIS_STEP
    )


def extract_proof(root_goal: str, proof_tree: dict) -> Optional[dict]:
    """
    Extracts a clean {goal: {step, subgoals}} tree from root_goal, holding
    only the goals its proof uses, subgoals before the goals they prove.

    """
    chosen = {}
    changed = True
    while changed:
        changed = False
        for goal, alternatives in proof_tree.items():
            if goal in chosen:
                continue
            for alt in alternatives:
                if all(subgoal in chosen for subgoal in alt["subgoals"]):
                    chosen[goal] = alt
                    changed = True
                    break

    if root_goal not in chosen:
        return None

    clean = {}

    def collect(goal: str) -> None:
        if goal in clean:
            return
        for subgoal in chosen[goal]["subgoals"]:
            collect(subgoal)
        clean[goal] = chosen[goal]

    collect(root_goal)
    return clean


def format_proved_theorem(
    label: str, root_goal: str, clean_proof: dict, expansions: int
) -> str:
    """
    Render one fully-proved theorem as a text block: its label, root
    goal, and every step of its actual proof as
    "theorem_label {{ var : val }} ...".
    """
    lines = [f"THEOREM: {label}", f"GOAL: {root_goal}", f"EXPANSIONS: {expansions}"]
    for goal, info in clean_proof.items():
        lines.append(f"  GOAL: {goal}")
        lines.append(f"  STEP: {info['step']}")
    lines.append("")
    return "\n".join(lines)


@dataclass
class TheoremResult:
    """All measurements for one theorem across all attempts."""

    label: str
    proved: bool
    best_search_time_s: float
    best_expansions: int
    total_search_time_s: float
    total_expansions: int
    total_candidates: int
    proof_steps: int
    attempts_used: int
    input_tokens: int = 0
    output_tokens: int = 0


def find_token_counts(model) -> Optional[dict]:
    """
    Returns the running {input_tokens, output_tokens} totals of the model
    that actually runs the network, unwrapping residual adapters (which
    keep the model they wrap in `.model`). None if the model doesn't count.
    """
    while model is not None:
        counts = getattr(model, "token_counts", None)
        if isinstance(counts, dict):
            return counts
        model = getattr(model, "model", None)
    return None


def evaluate(
    model,
    verifier: MetamathVerifier,
    split_file: str,
    model_name: str = "model",
    attempts: int = 4,
    max_expansions: int = 128,
    n_tactics: int = 32,
    verbose: bool = False,
    demo: bool = False,
    proved_output: str = None,
    expansions_output: str = None,
    tokens_output: str = None,
    progress_every: int = 1,
    heartbeat_every: int = 20,
    temperature: float = 1.0,
    max_valid_per_goal: int = 1,
    stats_output: str = None,
    seed: int = None,
) -> tuple[dict, list[TheoremResult]]:
    """
    Evaluate the prover on a split and collect all metrics.
    """
    theorem_goals = {}
    theorem_order = []

    with open(split_file) as f:
        for line in f:
            record = json.loads(line)
            label = record["proof_label"]
            if label not in theorem_goals:
                theorem_order.append(label)
            theorem_goals[label] = record["goal"]

    total = len(theorem_order)
    print(
        f"\nEvaluating '{model_name}' on {total} theorems "
        f"({attempts} attempts each, max {max_expansions} expansions, "
        f"up to {max_valid_per_goal} valid candidates per goal) ...",
        flush=True,
    )

    overall_start = time.time()

    results = []
    proved_count = 0
    theorems_written = 0

    proved_file = open(proved_output, "w") if proved_output else None

    expansions_file = None
    if expansions_output:
        expansions_file = open(expansions_output, "w")
        expansions_file.write(
            "proof_label,expansions,non_first_candidate_steps,max_candidate_rank\n"
        )

    token_counts = find_token_counts(model)
    tokens_file = None
    if tokens_output:
        tokens_file = open(tokens_output, "w")
        tokens_file.write(
            "proof_label,proved,attempts,expansions,input_tokens,output_tokens\n"
        )

    for i, label in enumerate(theorem_order):
        root_goal = theorem_goals[label]

        if heartbeat_every:
            print(f"  [{i + 1}/{total}] starting {label} ...", flush=True)

        proved = False
        best_time = float("inf")
        best_expansions = -1
        total_time = 0.0
        total_expansions = 0
        tokens_before = dict(token_counts) if token_counts else None
        total_candidates = 0
        proof_steps = 0
        attempts_used = 0
        non_first_candidate_steps = 0
        max_candidate_rank = 0

        verifier.set_target(label)
        for _ in range(attempts):
            attempts_used += 1
            proof_tree, metrics = proof_search(
                root_goal_str=root_goal,
                model=model,
                verifier=verifier,
                max_expansions=max_expansions,
                n_tactics=n_tactics,
                max_valid_per_goal=max_valid_per_goal,
                temperature=temperature,
                verbose=verbose,
                demo=demo,
                heartbeat_every=heartbeat_every,
                excluded_labels={label},
            )

            total_time += metrics["search_time_s"]
            total_expansions += metrics["expansions"]
            total_candidates += metrics["candidates_examined"]

            if proof_tree is not None:
                proved = True
                best_time = metrics["search_time_s"]
                best_expansions = metrics["expansions"]
                clean_proof = extract_proof(root_goal, proof_tree)
                proof_steps = count_proof_steps(clean_proof)
                if clean_proof is not None:
                    candidate_ranks = [
                        step.get("candidate_rank", 1)
                        for step in clean_proof.values()
                    ]
                    non_first_candidate_steps = sum(
                        rank > 1 for rank in candidate_ranks
                    )
                    max_candidate_rank = max(candidate_ranks, default=1)
                    if expansions_file is not None:
                        expansions_file.write(
                            f"{label},{best_expansions},"
                            f"{non_first_candidate_steps},{max_candidate_rank}\n"
                        )
                        expansions_file.flush()
                    print(
                        f"  PROVED {label}: selected path uses "
                        f"{non_first_candidate_steps} non-first candidate "
                        f"step(s), max candidate rank {max_candidate_rank}",
                        flush=True,
                    )
                if proved_file is not None and clean_proof is not None:
                    proved_file.write(
                        format_proved_theorem(
                            label, root_goal, clean_proof, total_expansions
                        )
                    )
                    proved_file.flush()
                    theorems_written += 1

                break

        if proved:
            proved_count += 1
        if best_time == float("inf"):
            best_time = total_time

        input_tokens = output_tokens = 0
        if token_counts is not None:
            input_tokens = token_counts["input_tokens"] - tokens_before["input_tokens"]
            output_tokens = (
                token_counts["output_tokens"] - tokens_before["output_tokens"]
            )
        if tokens_file is not None:
            tokens_file.write(
                f"{label},{proved},{attempts_used},{total_expansions},"
                f"{input_tokens},{output_tokens}\n"
            )
            tokens_file.flush()

        results.append(
            TheoremResult(
                label=label,
                proved=proved,
                best_search_time_s=best_time,
                best_expansions=best_expansions,
                total_search_time_s=total_time,
                total_expansions=total_expansions,
                total_candidates=total_candidates,
                proof_steps=proof_steps,
                attempts_used=attempts_used,
                input_tokens=input_tokens,
                output_tokens=output_tokens,
            )
        )

        if progress_every and (i + 1) % progress_every == 0:
            elapsed = time.time() - overall_start
            avg_time = elapsed / (i + 1)
            eta = avg_time * (total - (i + 1))
            pct = proved_count / (i + 1) * 100
            print(
                f"  [{i + 1}/{total}] {label}  proved={proved_count} "
                f"({pct:.1f}%)  elapsed={format_duration(elapsed)}  "
                f"eta={format_duration(eta)}",
                flush=True,
            )

    if proved_file is not None:
        proved_file.close()
    if expansions_file is not None:
        expansions_file.close()
    if tokens_file is not None:
        tokens_file.close()

    proved_results = [r for r in results if r.proved]
    n_proved = len(proved_results)
    success_rate = n_proved / total * 100

    avg_search_time = sum(r.best_search_time_s for r in proved_results) / max(
        n_proved, 1
    )
    avg_expansions_used = sum(r.best_expansions for r in proved_results) / max(
        n_proved, 1
    )
    max_expansions_used = max((r.best_expansions for r in proved_results), default=0)
    active_results = [r for r in results if r.total_candidates > 0]
    avg_candidates = sum(r.total_candidates for r in active_results) / max(
        len(active_results), 1
    )
    avg_proof_steps = sum(r.proof_steps for r in proved_results) / max(n_proved, 1)

    # Token usage covers every attempt on every theorem, proved or not.
    total_input_tokens = sum(r.input_tokens for r in results)
    total_output_tokens = sum(r.output_tokens for r in results)
    all_expansions = sum(r.total_expansions for r in results)
    avg_input_tokens = total_input_tokens / max(total, 1)
    avg_output_tokens = total_output_tokens / max(total, 1)
    input_per_expansion = total_input_tokens / max(all_expansions, 1)
    output_per_expansion = total_output_tokens / max(all_expansions, 1)

    elapsed = time.time() - overall_start
    summary = {
        "model": model_name,
        "total_theorems": total,
        "proved": n_proved,
        "theorem_success_rate_%": round(success_rate, 2),
        "avg_search_time_s": round(avg_search_time, 4),
        "avg_expansions_used": round(avg_expansions_used, 1),
        "max_expansions_used": max_expansions_used,
        "avg_candidates_examined": round(avg_candidates, 1),
        "avg_proof_steps": round(avg_proof_steps, 1),
        "elapsed_time_s": round(elapsed, 2),
        "theorems_written_to_file": theorems_written,
        "total_input_tokens": total_input_tokens,
        "total_output_tokens": total_output_tokens,
        "avg_input_tokens_per_theorem": round(avg_input_tokens, 1),
        "avg_output_tokens_per_theorem": round(avg_output_tokens, 1),
        "avg_input_tokens_per_expansion": round(input_per_expansion, 1),
        "avg_output_tokens_per_expansion": round(output_per_expansion, 1),
    }

    print(f"\n{'=' * 60}")
    print(f"Results for: {model_name}")
    print(f"{'=' * 60}")
    print(f"  Theorem success rate      : {n_proved}/{total} = {success_rate:.2f}%")
    print(f"  Avg search time (proved)  : {avg_search_time:.4f}s")
    print(f"  Elapsed time              : {elapsed:.2f}s")
    print(
        f"  Expansions used (proved)  : avg={avg_expansions_used:.1f}, "
        f"max={max_expansions_used}  (out of a budget of "
        f"{max_expansions} -- max_expansions can likely be lowered "
        f"toward the max shown here, with a little headroom, without "
        f"losing any of these successes)"
    )
    print(
        f"  Avg candidates examined   : {avg_candidates:.1f} "
        f"(over {len(active_results)} theorems with any candidates)"
    )
    print(f"  Avg proof length (steps)  : {avg_proof_steps:.1f}")
    print(
        f"  Tokens (all attempts)     : input={total_input_tokens}, "
        f"output={total_output_tokens}  (per theorem: "
        f"{avg_input_tokens:.1f} in / {avg_output_tokens:.1f} out; per "
        f"expansion: {input_per_expansion:.1f} in / "
        f"{output_per_expansion:.1f} out)"
    )

    if proved_output:
        print(
            f"  Theorems written to file  : {theorems_written} "
            f"(fully closed proofs only -- {proved_output})"
        )
        assert theorems_written == n_proved, (
            "theorems_written should always equal n_proved: every "
            "theorem counted as proved gets a clean extracted proof "
        )
    print(f"{'=' * 60}")

    stats_path = stats_output or os.path.join(os.getcwd(), "stats.txt")
    stats_lines = [
        f"Results for: {model_name}",
        f"Seed                      : {seed}",
        f"Theorem success rate      : {n_proved}/{total} = {success_rate:.2f}%",
        f"Avg search time (proved)  : {avg_search_time:.4f}s",
        f"Elapsed time              : {elapsed:.2f}s",
        (
            f"Expansions used (proved)  : avg={avg_expansions_used:.1f}, "
            f"max={max_expansions_used}  (out of a budget of {max_expansions})"
        ),
        (
            f"Avg candidates examined   : {avg_candidates:.1f} "
            f"(over {len(active_results)} theorems with any candidates)"
        ),
        f"Avg proof length (steps)  : {avg_proof_steps:.1f}",
        (
            f"Tokens (all attempts)     : input={total_input_tokens}, "
            f"output={total_output_tokens}  (per theorem: "
            f"{avg_input_tokens:.1f} in / {avg_output_tokens:.1f} out; per "
            f"expansion: {input_per_expansion:.1f} in / "
            f"{output_per_expansion:.1f} out)"
        ),
    ]
    if proved_output:
        stats_lines.append(
            f"Theorems written to file  : {theorems_written} "
            f"(fully closed proofs only -- {proved_output})"
        )
    stats_lines.append("")
    stats_lines.append(json.dumps(summary, indent=2, sort_keys=True))
    with open(stats_path, "w", encoding="utf-8") as stats_file:
        stats_file.write("\n".join(stats_lines) + "\n")
    print(f"  Results written to {stats_path}")

    return summary, results


def main(add_args=None, wrap_model=None, doc=None):
    """
    The whole evaluation run.

    `add_args` and `wrap_model` are the only things a variant method is
    expected to change -- see residuals/search/proof_search.py -- so that
    any difference in results comes from the method, not from a drifted
    search parameter. `wrap_model(model, mm, args)` returns the model the
    search will actually call.
    """
    parser = argparse.ArgumentParser(
        description=doc or "Metamath proof search with full evaluation metrics"
    )
    parser.add_argument("--mm", required=True, help="Path to set.mm")
    parser.add_argument(
        "--mmverify",
        default="data/mmverify.py",
        help="Path to mmverify.py (default: same dir)",
    )
    parser.add_argument(
        "--model-module", default=None, help="Path to Python file defining Model class"
    )
    parser.add_argument(
        "--model-name",
        default="learned_model",
        help="Display name for the model in results",
    )
    parser.add_argument("--train-jsonl", default=None, help="Training split")
    parser.add_argument(
        "--goal",
        default=None,
        help="Single goal to prove, in full -- same "
        'shape as a JSONL "goal" field, e.g. '
        '"[[ ]] |- ( ph -> ph )" for no hypotheses, '
        'or "[[ |- ph ]] |- ( ph \\/ ps )" with one',
    )
    parser.add_argument(
        "--eval", default=None, help="Evaluate on a split file e.g. valid.jsonl"
    )
    parser.add_argument("--attempts", type=int, default=4)
    parser.add_argument("--expansions", type=int, default=128)
    parser.add_argument("--tactics", type=int, default=32)
    parser.add_argument("--max-valid-per-goal", type=int, default=1)
    parser.add_argument("--temperature", type=float, default=1.0)
    parser.add_argument(
        "--seed",
        type=int,
        default=None,
        help="Seed for python, numpy and torch RNGs so a search run "
        "can be reproduced (default: unseeded)",
    )
    parser.add_argument("--verbose", action="store_true")
    parser.add_argument(
        "--demo",
        action="store_true",
        help="Print each candidate tactic tried and the "
        "resulting subgoals in full, for live demos",
    )
    parser.add_argument(
        "--proved-output",
        default=None,
        help="Path to write every fully-proved theorem "
        "(only the steps actually used in its "
        "finished proof) to as a text file, "
        "during --eval",
    )
    parser.add_argument(
        "--expansions-output",
        default=None,
        help="Path to write a CSV of proof_label,"
        "expansions -- the number of expansions "
        "the successful attempt used -- for every "
        "proved theorem, during --eval",
    )
    parser.add_argument(
        "--tokens-output",
        default=None,
        help="Path to write a CSV of input and output token counts "
        "for every theorem (proved or not), during --eval",
    )
    parser.add_argument(
        "--stats-output",
        default=None,
        help="Path to write the summary stats to during --eval "
        "(default: stats.txt in the working directory)",
    )
    parser.add_argument(
        "--progress-every",
        type=int,
        default=1,
        help="Print a progress line (with elapsed "
        "time and ETA) every this many theorems "
        "during --eval (default: 1, i.e. every "
        "theorem)",
    )
    parser.add_argument(
        "--heartbeat-every",
        type=int,
        default=20,
        help='Print a "starting theorem" line and a '
        '"still searching" line every this many '
        "expansions, so a slow theorem is "
        "distinguishable from a hang (default: "
        "20; 0 disables both)",
    )
    parser.add_argument(
        "--model-dir",
         help="Directory containing the trained model weights"
    )

    # Allow a model module to contribute its own CLI arguments and wrapping
    # logic without requiring a separate search entrypoint.
    model_module = detect_model_module_from_argv(sys.argv[1:])
    if model_module and add_args is None:
        module = load_module_from_path(model_module)
        if hasattr(module, "add_args"):
            add_args = module.add_args
        if hasattr(module, "wrap_model"):
            wrap_model = module.wrap_model

    if add_args is not None:
        add_args(parser)
    args = parser.parse_args()

    if args.max_valid_per_goal < 1:
        parser.error("--max-valid-per-goal must be at least 1")

    if not args.goal and not args.eval:
        print("ERROR: supply either --goal or --eval")
        sys.exit(1)

    if args.seed is not None:
        from transformers import set_seed

        set_seed(args.seed)
        print(f"Seed: {args.seed}")

    mmverify_path = args.mmverify or os.path.join(
        os.path.dirname(__file__), "mmverify.py"
    )
    print(f"Loading mmverify from {mmverify_path} ...")
    mmv = load_mmverify(mmverify_path)

    print(f"Loading {args.mm} ...")
    mm = make_scoped_mm(mmv)()
    with open(args.mm, "r", encoding="utf-8", errors="replace") as f:
        mm.read(mmv.toks(f))
    print("Database loaded.")

    verifier = MetamathVerifier(mmv, mm)

    models = {}

    if args.model_module:
        learned = load_model_from_module(
            args.model_module,
            mm,
            model_dir=args.model_dir,
            base_model_module=getattr(args, "base_model_module", None),
        )
        if wrap_model is not None:
            learned = wrap_model(learned, mm, args)
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
            max_valid_per_goal=args.max_valid_per_goal,
            verbose=args.verbose,
            demo=args.demo,
            heartbeat_every=args.heartbeat_every,
            excluded_labels=set(),
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
            max_valid_per_goal=args.max_valid_per_goal,
            temperature=args.temperature,
            verbose=args.verbose,
            demo=args.demo,
            proved_output=args.proved_output,
            expansions_output=args.expansions_output,
            tokens_output=args.tokens_output,
            stats_output=args.stats_output,
            seed=args.seed,
            progress_every=args.progress_every,
            heartbeat_every=args.heartbeat_every,
        )


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""
Combine each model's full-test-set run with its hypothesis-set run into one
result over the whole test set.

Run from anywhere:  uv run python results/concat_runs.py [--seeds 1 2 3]
"""

import argparse
import csv
import json
import re
import sys
from pathlib import Path

RESULTS = Path(__file__).resolve().parent
ROOT = RESULTS.parent
sys.path.insert(0, str(ROOT))

from search.kernel_check import load_mmverify, parse_proved_file  # noqa: E402
from search.proof_search import HYPOTHESIS_STEP, count_proof_steps  # noqa: E402
from utils.formatting import parse_goal, parse_proofstep  # noqa: E402

MODELS = ["baseline", "modular", "residual/baseline", "residual/modular"]
TEST_SPLIT = ROOT / "data/longest_theorems/test.jsonl"
HYP_SPLIT = ROOT / "data/longest_theorems/test_hyp.jsonl"


def split_labels(path: Path) -> list[str]:
    with open(path) as f:
        return list(dict.fromkeys(json.loads(line)["proof_label"] for line in f))


def load_run(run_dir: Path, seed: int) -> dict | None:
    """Everything one finished run wrote, or None if it is missing or unfinished."""
    paths = {
        "proved": run_dir / f"longest_theorems_proved_seed{seed}.txt",
        "stats": run_dir / f"longest_stats_seed{seed}.txt",
        "kernel": run_dir / f"longest_kernel_seed{seed}.json",
        "tokens": run_dir / f"longest_tokens_seed{seed}.csv",
        "expansions": run_dir / f"longest_expansions_seed{seed}.csv",
    }
    missing = [p.name for p in paths.values() if not p.exists()]
    if missing:
        return {"missing": missing}
    text = paths["stats"].read_text(encoding="utf-8")
    (verdicts,) = json.loads(paths["kernel"].read_text()).values()
    return {
        "paths": paths,
        "proofs": parse_proved_file(str(paths["proved"])),
        "blocks": re.findall(
            r"^THEOREM: (\S+)\nGOAL: .*\nEXPANSIONS: (\d+)", paths["proved"].read_text(), re.M
        ),
        "stats": json.loads(text[text.index("{"):]),
        "stats_text": text,
        "verdicts": verdicts,
        "tokens": {r["proof_label"]: r for r in csv.DictReader(open(paths["tokens"]))},
        "expansions": {
            r["proof_label"]: int(r["expansions"])
            for r in csv.DictReader(open(paths["expansions"]))
        },
    }


def pruned(proof: dict, mm) -> dict:
    """The proof tree reachable from the root, subgoals before goals, root last."""
    prefix = proof["root"].split("]]", 1)[0] + "]]"
    clean = {}

    def visit(conclusion: str) -> None:
        goal = f"{prefix} {conclusion}"
        if goal in clean:
            return
        step = proof["steps"][conclusion]
        subgoals = []
        if step != HYPOTHESIS_STEP:
            parsed = parse_proofstep(step)
            hyps = mm.labels[parsed["theorem"]][1][2]
            subgoals = [
                f"{prefix} {' '.join(mm.apply_subst(h, parsed['subst']))}" for h in hyps
            ]
            for subgoal in subgoals:
                visit(subgoal.split("]]", 1)[1].strip())
        clean[goal] = {"step": step, "subgoals": subgoals}

    visit(proof["root"].split("]]", 1)[1].strip())
    return clean


def stat_line(text: str, name: str) -> str:
    return re.search(rf"^{re.escape(name)}\s*:\s*(.*)$", text, re.M).group(1)


def concat(model: str, seed: int, mm, hyp_labels: set, test_labels: list) -> str:
    test_dir = RESULTS / model
    test, hyp = load_run(test_dir, seed), load_run(test_dir / "hyp", seed)
    for name, run in (("test", test), ("hyp", hyp)):
        if "missing" in run:
            return f"skipped: {name} run has no {', '.join(run['missing'])}"

    # theorems without hypotheses from the test run, with hypotheses from the hyp run
    parts = [(test, lambda lab: lab not in hyp_labels), (hyp, lambda lab: lab in hyp_labels)]
    out_lines, lengths, expansions, kept = [], [], [], []
    superseded = 0
    for run, belongs in parts:
        for label, expansions_used in run["blocks"]:
            if not belongs(label):
                superseded += 1
                continue
            if run["verdicts"].get(label, "missing") is not None:
                continue
            clean = pruned(run["proofs"][label], mm)
            lengths.append(count_proof_steps(clean))
            expansions.append(run["expansions"][label])
            kept.append(label)
            out_lines += [
                f"THEOREM: {label}",
                f"GOAL: {run['proofs'][label]['root']}",
                f"EXPANSIONS: {expansions_used}",
            ]
            for goal, info in clean.items():
                out_lines += [f"  GOAL: {goal}", f"  STEP: {info['step']}"]
    proved_path = test_dir / f"longest_theorems_proved_seed{seed}_concat.txt"
    proved_path.write_text("\n".join(out_lines) + "\n" if out_lines else "", encoding="utf-8")

    # tokens over every theorem in the test set, each from the run that owns it
    token_rows = [
        (hyp if label in hyp_labels else test)["tokens"][label] for label in test_labels
    ]
    in_tok = sum(int(r["input_tokens"]) for r in token_rows)
    out_tok = sum(int(r["output_tokens"]) for r in token_rows)
    all_exp = sum(int(r["expansions"]) for r in token_rows)

    n, total = len(kept), len(test_labels)
    n_test = sum(1 for lab in kept if lab not in hyp_labels)
    n_hyp = n - n_test
    t_elapsed, h_elapsed = test["stats"]["elapsed_time_s"], hyp["stats"]["elapsed_time_s"]
    exp_test = sum(int(r["expansions"]) for lab, r in test["tokens"].items() if lab not in hyp_labels)
    exp_hyp = sum(int(r["expansions"]) for r in hyp["tokens"].values())
    sources = (
        test["paths"]["proved"].relative_to(ROOT).as_posix(),
        hyp["paths"]["proved"].relative_to(ROOT).as_posix(),
    )

    def fmt_time(value):
        return "n/a" if value is None else f"{value:.4f}s"

    text = [
        f"Results for: {test['stats']['model']} (test run + hyp run)",
        f"Seed                      : {seed}",
        f"Theorem success rate      : {n}/{total} = {n / total * 100:.2f}%  "
        f"(test run, no hypotheses: {n_test}/{total - len(hyp_labels)}; "
        f"hyp run: {n_hyp}/{len(hyp_labels)})",
        f"Avg search time (proved)  : test run {fmt_time(test['stats'].get('avg_search_time_s'))}; "
        f"hyp run {fmt_time(hyp['stats'].get('avg_search_time_s'))}",
        f"Elapsed time              : test run {t_elapsed:.2f}s; hyp run {h_elapsed:.2f}s",
        f"Expansions used (proved)  : avg={sum(expansions) / max(n, 1):.1f}, "
        f"max={max(expansions, default=0)}  (out of a budget of 32)",
        f"Expansions used (all)     : {exp_test + exp_hyp} (test run, theorems without "
        f"hypotheses: {exp_test}; hyp run: {exp_hyp})",
        f"Avg candidates examined   : test run {stat_line(test['stats_text'], 'Avg candidates examined')}; "
        f"hyp run {stat_line(hyp['stats_text'], 'Avg candidates examined')}",
        f"Avg proof length (steps)  : {sum(lengths) / max(n, 1):.1f}",
        f"Tokens (all attempts)     : input={in_tok}, output={out_tok}  (per theorem: "
        f"{in_tok / total:.1f} in / {out_tok / total:.1f} out; per expansion: "
        f"{in_tok / max(all_exp, 1):.1f} in / {out_tok / max(all_exp, 1):.1f} out)",
        f"Theorems written to file  : {n} (kernel-accepted proofs only -- "
        f"{proved_path.relative_to(ROOT).as_posix()})",
        f"Sources                   : {sources[0]} (theorems without hypotheses) + "
        f"{sources[1]} (theorems with hypotheses)",
    ]
    stats_path = test_dir / f"longest_stats_seed{seed}_concat.txt"
    stats_path.write_text("\n".join(text) + "\n", encoding="utf-8")
    note = f", {superseded} test-run proofs of hypothesis theorems superseded" if superseded else ""
    return f"{n}/{total} ({n_test} test + {n_hyp} hyp){note}"


def main() -> None:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("--seeds", type=int, nargs="+", default=[1, 2, 3])
    args = parser.parse_args()

    test_labels = split_labels(TEST_SPLIT)
    hyp_labels = set(split_labels(HYP_SPLIT))
    assert hyp_labels <= set(test_labels), "hyp split is not a subset of the test split"

    mmv = load_mmverify(str(ROOT / "data/mmverify.py"))
    mmv.vprint = lambda *a, **k: None
    mm = mmv.MM()
    mm.verify = lambda *a, **k: None
    with open(ROOT / "data/set.mm", encoding="utf-8", errors="replace") as f:
        mm.read(mmv.toks(f))

    for model in MODELS:
        for seed in args.seeds:
            print(f"{model} seed{seed}: {concat(model, seed, mm, hyp_labels, test_labels)}")


if __name__ == "__main__":
    main()

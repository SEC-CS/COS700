import importlib.util
import os

from utils.formatting import format_proofstep, parse_proofstep
from utils.matcher import (
    DEFAULT_CACHE,
    DEFAULT_CAP,
    complete,
    determined_key,
    label_table,
)


def _load_base_model(base_model_module: str, model_dir: str | None = None):
    spec = importlib.util.spec_from_file_location("base_model", base_model_module)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)

    if not hasattr(mod, "Model"):
        raise ValueError(
            f"{base_model_module} must define a class called 'Model' with a generate_steps() method."
        )

    model = mod.Model(model_dir=model_dir) if model_dir else mod.Model()
    return model


class Model:
    """Thin adapter for an underlying model; residual completion is applied by wrap_model()."""

    def __init__(self, model_dir: str | None = None, base_model_module: str | None = None):
        self.base_model_module = (
            base_model_module
            or os.environ.get("PROVER_BASE_MODEL_MODULE")
            or "models/baseline/model.py"
        )
        self.model = _load_base_model(self.base_model_module, model_dir=model_dir)
        self.model.allow_empty_substitution = True

    def set_mm(self, mm):
        if hasattr(self.model, "set_mm"):
            self.model.set_mm(mm)

    def set_empty_substitution_labels(self, labels: set[str]) -> None:
        setter = getattr(self.model, "set_empty_substitution_labels", None)
        if setter is not None:
            setter(labels)

    def generate_steps(self, goal_str: str, n: int = 32, temperature: float = 1.0):
        return self.model.generate_steps(goal_str, n=n, temperature=temperature)


class ResidualModel:
    """Wraps a model output that is only the residual fragment, completing it with the matcher."""

    def __init__(self, model, table: dict, cap: int = DEFAULT_CAP):
        self.model = model
        self.table = table
        self.cap = cap
        self.excluded_labels = set()
        set_empty_substitution_labels = getattr(
            model, "set_empty_substitution_labels", None
        )
        if set_empty_substitution_labels is not None:
            set_empty_substitution_labels(
                {
                    label
                    for label, info in table.items()
                    if not (set(info["kinds"]) - info["rvars"])
                }
            )

    def set_excluded_labels(self, labels: set[str]) -> None:
        self.excluded_labels = set(labels)

    def candidate_group_key(self, step_str: str) -> tuple:
        parsed = parse_proofstep(step_str)
        if parsed is None:
            return (step_str,)

        label = parsed["theorem"]
        info = self.table.get(label)
        if info is None:
            return (
                label,
                tuple(
                    sorted(
                        (var, tuple(value))
                        for var, value in parsed["subst"].items()
                    )
                ),
            )

        residual = tuple(
            sorted(
                (var, tuple(value))
                for var, value in parsed["subst"].items()
                if var not in info["rvars"]
            )
        )
        return label, residual

    def generate_steps(self, goal_str: str, n: int = 32, temperature: float = 1.0):
        out = []
        seen = set()
        for step_str, logprob in self.model.generate_steps(
            goal_str, n=n, temperature=temperature
        ):
            for full_step in self.complete_step(goal_str, step_str):
                if full_step not in seen:
                    seen.add(full_step)
                    out.append((full_step, logprob))
        return out

    def complete_step(self, goal_str: str, step_str: str) -> list[str]:
        target = step_str.strip()
        label = target.split(maxsplit=1)[0] if target else ""
        substitution_start = target.find("{{")
        residual_step = (
            f"{label} {target[substitution_start:]}"
            if substitution_start >= 0
            else label
        )
        parsed = parse_proofstep(residual_step)
        if parsed is None:
            return [step_str]

        label, residual = parsed["theorem"], parsed["subst"]
        if label in self.excluded_labels:
            return []

        info = self.table.get(label)
        if info is None:
            return []

        residual = {
            var: value
            for var, value in residual.items()
            if var not in info["rvars"]
        }

        steps = []
        seen = set()
        for candidate in complete(
            info["result"],
            goal_str.split("]]", 1)[1].split(),
            info["kinds"],
            cap=self.cap,
        ):
            key = determined_key(candidate, info["rvars"])
            if key in seen:
                continue
            seen.add(key)
            subst = {v: val for v, val in candidate.items() if v in info["rvars"]}
            subst.update(residual)
            steps.append(format_proofstep(label, subst))

        return steps or [step_str]


def add_args(parser) -> None:
    parser.add_argument(
        "--base-model-module",
        default=None,
        help="Path to the underlying model module to wrap with residual completion.",
    )
    parser.add_argument(
        "--cap",
        type=int,
        default=DEFAULT_CAP,
        help=f"Substitution candidates the matcher may return per goal (default {DEFAULT_CAP}).",
    )
    parser.add_argument(
        "--label-table",
        default=DEFAULT_CACHE,
        help="Cached per-label table from residualise.py.",
    )


def wrap_model(model, mm, args):
    table = label_table(
        mm_path=args.mm,
        mmverify_path=args.mmverify,
        cache=args.label_table,
    )
    print(f"Label table: {len(table)} assertions  (cache {args.label_table})")
    return ResidualModel(model, table, cap=args.cap)
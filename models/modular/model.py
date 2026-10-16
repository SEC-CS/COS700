import os
from pathlib import Path

import torch
from transformers import (
    AutoModelForCausalLM,
    AutoModelForSequenceClassification,
    AutoTokenizer,
)

THEOREM_MODEL_DIR = os.environ.get(
    "THEOREM_MODEL_DIR", "finetuning/modular/output/finetuned-classifier/final"
)
SUBSTITUTION_MODEL_DIR = os.environ.get(
    "SUBSTITUTION_MODEL_DIR", "finetuning/modular/output/finetuned-substitution/final"
)
K_THEOREMS = int(os.environ.get("K_THEOREMS", "5"))
MAX_NEW_SUBSTITUTION_TOKENS = int(os.environ.get("MAX_NEW_SUBSTITUTION_TOKENS", "64"))
# Should match --max-length used when training the classifier.
THEOREM_MAX_LENGTH = int(os.environ.get("THEOREM_MAX_LENGTH", "400"))
SUBSTITUTION_PROMPT_BATCH_SIZE = int(
    os.environ.get("SUBSTITUTION_PROMPT_BATCH_SIZE", "5")
)
if SUBSTITUTION_PROMPT_BATCH_SIZE < 1:
    raise ValueError("SUBSTITUTION_PROMPT_BATCH_SIZE must be at least 1")

# Must match PROMPT_TEMPLATE in train_model_sub.py exactly -- the
# substitution model was trained to expect this exact prompt shape.
SUBSTITUTION_PROMPT_TEMPLATE = (
    "GOAL: {goal}\n"
    "MANDVARS: {mandvars}\n"
    "HYP: {hyp}\n"
    "RESULT: {result}\n"
    "SUBSTITUTION:"
)


def parse_substitution(text: str) -> dict:
    """
    Parses "{{ ph : ph }} {{ ps : ps ch }}" into
    {"ph": ["ph"], "ps": ["ps", "ch"]}.

    Kept in sync with train_model_sub.py's version -- duplicated here
    (rather than imported) so model.py can be pointed at by
    proof_search.py's --model-module without depending on the training
    scripts' package layout being importable at runtime.
    """
    substitution = {}
    for chunk in text.split("}}"):
        chunk = chunk.strip()
        if not chunk or "{{" not in chunk:
            continue
        body = chunk.split("{{", 1)[1].strip()
        if ":" not in body:
            continue
        var, value_str = body.split(":", 1)
        substitution[var.strip()] = value_str.strip().split()
    return substitution


class Model:
    def __init__(self, model_dir: str | None = None):
        if model_dir:
            root = Path(model_dir)
            theorem_dir = root / "modular-thm" / "final"
            substitution_dir = root / "modular-sub" / "final"
        else:
            theorem_dir = THEOREM_MODEL_DIR
            substitution_dir = SUBSTITUTION_MODEL_DIR

        if not theorem_dir or not substitution_dir:
            raise ValueError(
                "Pass --model-dir or set THEOREM_MODEL_DIR / SUBSTITUTION_MODEL_DIR"
            )

        has_cuda = torch.cuda.is_available()
        self.device = torch.device("cuda" if has_cuda else "cpu")
        if has_cuda:
            self.compute_dtype = (
                torch.bfloat16 if torch.cuda.is_bf16_supported() else torch.float16
            )
        else:
            self.compute_dtype = torch.float32

        print(f"Loading theorem classifier from {theorem_dir} ...")
        self.theorem_tokenizer = AutoTokenizer.from_pretrained(theorem_dir)
        # Training used left padding (the classifier pools the last token).
        self.theorem_tokenizer.padding_side = "left"
        if self.theorem_tokenizer.pad_token is None:
            self.theorem_tokenizer.pad_token = self.theorem_tokenizer.eos_token
        self.theorem_model = AutoModelForSequenceClassification.from_pretrained(
            theorem_dir, dtype=self.compute_dtype
        ).to(self.device)
        self.theorem_model.eval()
        # config.json stores id2label; JSON keys may come back as strings,
        # so normalise them to ints for indexing with tensor .item() values.
        self.id2label = {
            int(i): label for i, label in self.theorem_model.config.id2label.items()
        }

        print(f"Loading substitution model from {substitution_dir} ...")
        self.substitution_tokenizer = AutoTokenizer.from_pretrained(substitution_dir)
        self.substitution_tokenizer.padding_side = "left"
        if self.substitution_tokenizer.pad_token is None:
            self.substitution_tokenizer.pad_token = self.substitution_tokenizer.eos_token
        self.substitution_model = AutoModelForCausalLM.from_pretrained(
            substitution_dir, dtype=self.compute_dtype
        ).to(self.device)
        self.substitution_model.eval()

        self.mm = None
        self._theorem_info_cache = {}
        self.empty_substitution_labels = set()
        # Running totals read by search/proof_search.py: prompt tokens fed
        # to the classifier and the substitution model, and tokens the
        # substitution model generated (up to EOS), summed over every
        # returned sequence. The classifier generates no tokens.
        self.token_counts = {"input_tokens": 0, "output_tokens": 0}

    def set_mm(self, mm):
        self.mm = mm
        self._theorem_info_cache = {}

    def set_empty_substitution_labels(self, labels: set[str]) -> None:
        self.empty_substitution_labels = set(labels)

    def _theorem_info(self, theorem: str) -> dict | None:
        """Returns the mandvars/hyp/result text fields for a theorem, in
        exactly the format train_model_sub.format_theorem_info() used, or
        None if the label is unknown or not a $a/$p statement."""
        if theorem in self._theorem_info_cache:
            return self._theorem_info_cache[theorem]
        if self.mm is None:
            raise RuntimeError("set_mm() must be called before generate_steps()")

        info = None
        entry = self.mm.labels.get(theorem)
        if entry is not None and entry[0] in ("$a", "$p"):
            _distinct, mand_var, hyp, result = entry[1]
            info = {
                "mandvars": ", ".join(f"{tc} {v}" for tc, v in mand_var),
                "hyp": " ; ".join(" ".join(tokens) for tokens in hyp),
                "result": " ".join(result),
            }
        self._theorem_info_cache[theorem] = info
        return info

    def _top_theorem_candidates(self, goal_str: str, k: int) -> list[tuple[str, float]]:
        """Returns up to k (theorem_label, logprob) pairs, most likely first."""
        inputs = self.theorem_tokenizer(
            goal_str,
            truncation=True,
            max_length=THEOREM_MAX_LENGTH,
            return_tensors="pt",
        ).to(self.device)
        self.token_counts["input_tokens"] += inputs["input_ids"].shape[1]

        with torch.no_grad():
            logits = self.theorem_model(**inputs).logits[0]
        log_probs = torch.log_softmax(logits.float(), dim=-1)

        k = min(k, log_probs.shape[0])
        top_log_probs, top_indices = torch.topk(log_probs, k)

        return [
            (self.id2label[idx.item()], logprob.item())
            for logprob, idx in zip(top_log_probs, top_indices)
        ]

    def _sample_substitutions(
        self,
        goal_str: str,
        theorem_candidates: list[tuple[str, float]],
        n: int,
        temperature: float,
    ) -> list[tuple[str, float, float]]:
        """
        Samples substitutions for all theorem prompts in one generation
        batch. Each result is (theorem, substitution_text, combined_logprob).
        """
        prompts = []
        prompt_theorems = []
        results = []
        for theorem, theorem_logprob in theorem_candidates:
            if theorem in self.empty_substitution_labels:
                results.append((theorem, "", theorem_logprob))
                continue
            info = self._theorem_info(theorem)
            if info is None:
                continue
            prompts.append(
                SUBSTITUTION_PROMPT_TEMPLATE.format(goal=goal_str, **info)
            )
            prompt_theorems.append((theorem, theorem_logprob))

        if not prompts:
            return results

        # Greedy decoding can't produce multiple distinct return
        # sequences, so temperature<=0 falls back to a single greedy
        # candidate for this theorem instead of n sampled ones.
        do_sample = temperature > 0
        num_return_sequences = n if do_sample else 1
        eos_id = self.substitution_tokenizer.eos_token_id
        for start in range(0, len(prompts), SUBSTITUTION_PROMPT_BATCH_SIZE):
            prompt_batch = prompts[start : start + SUBSTITUTION_PROMPT_BATCH_SIZE]
            theorem_batch = prompt_theorems[
                start : start + SUBSTITUTION_PROMPT_BATCH_SIZE
            ]
            inputs = self.substitution_tokenizer(
                prompt_batch,
                add_special_tokens=False,
                padding=True,
                return_tensors="pt",
            ).to(self.device)
            prompt_len = inputs["input_ids"].shape[1]
            self.token_counts["input_tokens"] += int(
                inputs["attention_mask"].sum().item()
            )

            with torch.inference_mode():
                outputs = self.substitution_model.generate(
                    **inputs,
                    max_new_tokens=MAX_NEW_SUBSTITUTION_TOKENS,
                    do_sample=do_sample,
                    temperature=temperature if do_sample else None,
                    num_return_sequences=num_return_sequences,
                    output_scores=True,
                    return_dict_in_generate=True,
                    pad_token_id=self.substitution_tokenizer.pad_token_id,
                )

            transition_scores = self.substitution_model.compute_transition_scores(
                outputs.sequences, outputs.scores, normalize_logits=True
            )

            for output_index, (sequence, scores) in enumerate(
                zip(outputs.sequences, transition_scores)
            ):
                prompt_index = output_index // num_return_sequences
                theorem, theorem_logprob = theorem_batch[prompt_index]
                generated_ids = sequence[prompt_len:]

                eos_positions = (generated_ids == eos_id).nonzero()
                length = (
                    eos_positions[0].item()
                    if len(eos_positions)
                    else len(generated_ids)
                )

                self.token_counts["output_tokens"] += length

                text = self.substitution_tokenizer.decode(
                    generated_ids[:length], skip_special_tokens=True
                ).strip()
                logprob = scores[:length].sum().item()
                results.append((theorem, text, theorem_logprob + logprob))

        return results

    def generate_steps(
        self, goal_str: str, n: int = 32, temperature: float = 1.0
    ) -> list[tuple[str, float]]:
        """
        Returns up to n (step_str, cumulative_logprob) candidates, each
        step_str formatted as "theorem {{ var : val }} ..." ready for
        MetamathVerifier.apply_step() / utils.formatting.parse_proofstep().
        """
        theorem_candidates = self._top_theorem_candidates(goal_str, K_THEOREMS)
        if not theorem_candidates:
            return []

        per_theorem = max(1, -(-n // len(theorem_candidates)))  # ceil division
        candidates = []
        for theorem, substitution_text, combined_logprob in self._sample_substitutions(
            goal_str, theorem_candidates, per_theorem, temperature
        ):
            substitution = parse_substitution(substitution_text)
            if not substitution and not getattr(self, "allow_empty_substitution", False):
                continue
            step_str = f"{theorem} {substitution_text}"
            candidates.append((step_str, combined_logprob))

        best_by_step = {}
        for step_str, logprob in candidates:
            if step_str not in best_by_step or logprob > best_by_step[step_str]:
                best_by_step[step_str] = logprob

        ranked = sorted(best_by_step.items(), key=lambda pair: pair[1], reverse=True)
        return ranked[:n]

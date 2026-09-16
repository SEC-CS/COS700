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

        print(f"Loading theorem classifier from {theorem_dir} ...")
        self.theorem_tokenizer = AutoTokenizer.from_pretrained(theorem_dir)
        # Training used left padding (the classifier pools the last token).
        self.theorem_tokenizer.padding_side = "left"
        if self.theorem_tokenizer.pad_token is None:
            self.theorem_tokenizer.pad_token = self.theorem_tokenizer.eos_token
        self.theorem_model = AutoModelForSequenceClassification.from_pretrained(
            theorem_dir
        ).to(self.device)
        self.theorem_model.eval()
        # config.json stores id2label; JSON keys may come back as strings,
        # so normalise them to ints for indexing with tensor .item() values.
        self.id2label = {
            int(i): label for i, label in self.theorem_model.config.id2label.items()
        }

        print(f"Loading substitution model from {substitution_dir} ...")
        self.substitution_tokenizer = AutoTokenizer.from_pretrained(substitution_dir)
        if self.substitution_tokenizer.pad_token is None:
            self.substitution_tokenizer.pad_token = self.substitution_tokenizer.eos_token
        self.substitution_model = AutoModelForCausalLM.from_pretrained(
            substitution_dir
        ).to(self.device)
        self.substitution_model.eval()

        self.mm = None  # set via set_mm(); needed for the substitution prompt
        self._theorem_info_cache = {}

    def set_mm(self, mm):
        self.mm = mm
        self._theorem_info_cache = {}

    # -----------------------------------------------------------------
    # Theorem structural info (from the .mm database)
    # -----------------------------------------------------------------

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

    # -----------------------------------------------------------------
    # Step 1: theorem candidates
    # -----------------------------------------------------------------

    def _top_theorem_candidates(self, goal_str: str, k: int) -> list[tuple[str, float]]:
        """Returns up to k (theorem_label, logprob) pairs, most likely first."""
        inputs = self.theorem_tokenizer(
            goal_str,
            truncation=True,
            max_length=THEOREM_MAX_LENGTH,
            return_tensors="pt",
        ).to(self.device)

        with torch.no_grad():
            logits = self.theorem_model(**inputs).logits[0]
        log_probs = torch.log_softmax(logits.float(), dim=-1)

        k = min(k, log_probs.shape[0])
        top_log_probs, top_indices = torch.topk(log_probs, k)

        return [
            (self.id2label[idx.item()], logprob.item())
            for logprob, idx in zip(top_log_probs, top_indices)
        ]

    # -----------------------------------------------------------------
    # Step 2: substitution candidates for one theorem
    # -----------------------------------------------------------------

    def _sample_substitutions(
        self, goal_str: str, theorem: str, n: int, temperature: float
    ) -> list[tuple[str, float]]:
        """
        Returns up to n (substitution_text, logprob) pairs for this
        (goal, theorem) pair. logprob is the summed log-probability the
        model assigned to the generated tokens, so it's directly
        comparable across different candidates and lengths in the same
        way a causal LM's sequence log-probability normally is.
        """
        info = self._theorem_info(theorem)
        if info is None:
            return []

        prompt = SUBSTITUTION_PROMPT_TEMPLATE.format(goal=goal_str, **info)
        inputs = self.substitution_tokenizer(
            prompt, add_special_tokens=False, return_tensors="pt"
        ).to(self.device)
        prompt_len = inputs["input_ids"].shape[1]

        # Greedy decoding can't produce multiple distinct return
        # sequences, so temperature<=0 falls back to a single greedy
        # candidate for this theorem instead of n sampled ones.
        do_sample = temperature > 0
        num_return_sequences = n if do_sample else 1

        with torch.no_grad():
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

        eos_id = self.substitution_tokenizer.eos_token_id
        results = []
        for sequence, scores in zip(outputs.sequences, transition_scores):
            generated_ids = sequence[prompt_len:]

            # Truncate at the first EOS: anything after it is just
            # batch padding from a shorter sequence sharing this batch,
            # not something the model actually "chose" to generate.
            eos_positions = (generated_ids == eos_id).nonzero()
            length = eos_positions[0].item() if len(eos_positions) else len(generated_ids)

            text = self.substitution_tokenizer.decode(
                generated_ids[:length], skip_special_tokens=True
            ).strip()
            logprob = scores[:length].sum().item()
            results.append((text, logprob))

        return results

    # -----------------------------------------------------------------
    # Public interface expected by proof_search.py
    # -----------------------------------------------------------------

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

        # Spread the n requested candidates evenly across the theorems
        # we're trying; some theorems may return fewer usable
        # candidates than requested (e.g. malformed generations get
        # dropped below), which is fine -- proof_search.py just works
        # with however many valid candidates come back.
        per_theorem = max(1, -(-n // len(theorem_candidates)))  # ceil division

        candidates = []
        for theorem, theorem_logprob in theorem_candidates:
            for substitution_text, substitution_logprob in self._sample_substitutions(
                goal_str, theorem, per_theorem, temperature
            ):
                substitution = parse_substitution(substitution_text)
                if not substitution:
                    # Malformed generation (or None substitution) --
                    # skip rather than hand proof_search.py a step
                    # string that could never verify anyway.
                    continue
                step_str = f"{theorem} {substitution_text}"
                combined_logprob = theorem_logprob + substitution_logprob
                candidates.append((step_str, combined_logprob))

        # Best candidates first, then cap at n as promised by the
        # interface, since we may have generated slightly more than n
        # across all theorems due to the ceil division above.
        candidates.sort(key=lambda pair: pair[1], reverse=True)
        return candidates[:n]

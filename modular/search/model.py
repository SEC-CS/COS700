#!/usr/bin/env python
"""
model.py
========
Integrates the two fine-tuned models from train_model.py (theorem
classifier) and train_substitution_model.py (substitution generator)
into a single `Model` with the generate_steps() interface proof_search.py
expects.

Pipeline, per goal
-------------------
1. THEOREM: the classifier scores every theorem in its label vocabulary
   and we keep the top K_THEOREMS by probability -- not just the single
   best one, since best-first search benefits from multiple candidate
   tactics per expansion, and a lower-probability theorem might still be
   the one that actually leads to a proof.
2. SUBSTITUTION: for each of those K candidate theorems, we prompt the
   substitution model with (goal, theorem) and sample several completions,
   giving us a spread of substitution guesses per theorem.
3. COMBINE: each (theorem, substitution) pair's score is
   log P(theorem | goal) + log P(substitution | goal, theorem) -- the
   two models' log-probabilities simply add, since the second model's
   prediction is conditioned on the first's output. This combined score
   is what fills GoalEntry.cumulative_logprob back in proof_search.py, so
   the search still prioritizes the same way it would if a single model
   had produced these scores directly.

Compatibility note
-------------------
The final step string this produces, f"{theorem} {substitution_text}",
must match what utils.formatting.parse_proofstep() expects to parse
("theorem_label {{ var1 : val1 }} {{ var2 : val2 }} ..."). This works
as long as train_substitution_model.py's format_substitution() -- which
the substitution model was trained to reproduce -- matches that same
format. If you changed one, check the other.

Configuration
--------------
proof_search.py instantiates this class with no arguments
(`model = mod.Model()`), so paths are read from environment variables
with defaults matching the two training scripts' --output-dir defaults:

    THEOREM_MODEL_DIR       (default: modular/finetuning/output/finetuned-classifier/final)
    SUBSTITUTION_MODEL_DIR  (default: modular/finetuning/output/finetuned-substitution/final)
    K_THEOREMS              (default: 5)  -- how many candidate theorems to try per goal
"""

import os

import torch
from transformers import (
    AutoModelForCausalLM,
    AutoModelForSequenceClassification,
    AutoTokenizer,
)

THEOREM_MODEL_DIR = os.environ.get(
    "THEOREM_MODEL_DIR", "modular/finetuning/output/finetuned-classifier/final"
)
SUBSTITUTION_MODEL_DIR = os.environ.get(
    "SUBSTITUTION_MODEL_DIR", "modular/finetuning/output/finetuned-substitution/final"
)
K_THEOREMS = int(os.environ.get("K_THEOREMS", "5"))
MAX_NEW_SUBSTITUTION_TOKENS = int(os.environ.get("MAX_NEW_SUBSTITUTION_TOKENS", "64"))

# Must match train_substitution_model.py's PROMPT_TEMPLATE exactly --
# the substitution model was trained to expect this exact prompt shape.
SUBSTITUTION_PROMPT_TEMPLATE = "GOAL: {goal}\nTHEOREM: {theorem}\nSUBSTITUTION:"


def parse_substitution(text: str) -> dict:
    """
    Parses "{{ ph : ph }} {{ ps : ps ch }}" into
    {"ph": ["ph"], "ps": ["ps", "ch"]}.

    Kept in sync with train_substitution_model.py's version -- duplicated
    here (rather than imported) so model.py can be pointed at by
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
    def __init__(self):
        has_cuda = torch.cuda.is_available()
        self.device = torch.device("cuda" if has_cuda else "cpu")

        print(f"Loading theorem classifier from {THEOREM_MODEL_DIR} ...")
        self.theorem_tokenizer = AutoTokenizer.from_pretrained(THEOREM_MODEL_DIR)
        self.theorem_model = AutoModelForSequenceClassification.from_pretrained(
            THEOREM_MODEL_DIR
        ).to(self.device)
        self.theorem_model.eval()
        # id2label comes back from config.json with string keys; the
        # classifier's logits are indexed by integer position, so we
        # need int keys to look labels up by argmax/topk index.
        self.id2label = {
            int(idx): label for idx, label in self.theorem_model.config.id2label.items()
        }

        print(f"Loading substitution model from {SUBSTITUTION_MODEL_DIR} ...")
        self.substitution_tokenizer = AutoTokenizer.from_pretrained(
            SUBSTITUTION_MODEL_DIR
        )
        self.substitution_model = AutoModelForCausalLM.from_pretrained(
            SUBSTITUTION_MODEL_DIR
        ).to(self.device)
        self.substitution_model.eval()

        self.mm = None  # set via set_mm(), unused here but kept for the interface

    def set_mm(self, mm):
        self.mm = mm

    # -----------------------------------------------------------------
    # Step 1: theorem candidates
    # -----------------------------------------------------------------

    def _top_theorem_candidates(self, goal_str: str, k: int) -> list[tuple[str, float]]:
        """Returns up to k (theorem_label, logprob) pairs, most likely first."""
        inputs = self.theorem_tokenizer(
            goal_str, truncation=True, return_tensors="pt"
        ).to(self.device)

        with torch.no_grad():
            logits = self.theorem_model(**inputs).logits[0]
        log_probs = torch.log_softmax(logits, dim=-1)

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
        prompt = SUBSTITUTION_PROMPT_TEMPLATE.format(goal=goal_str, theorem=theorem)
        inputs = self.substitution_tokenizer(prompt, return_tensors="pt").to(
            self.device
        )
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

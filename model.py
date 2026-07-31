"""
model.py
========
Implements the Model interface proof_search.py expects (see the docstring
at the top of that file): a class with generate_steps(goal_str, n,
temperature) -> list[(proofstep_str, log_probability)].

This loads the model saved by train_model.py and uses it to sample
candidate proof steps for a given goal, computing an actual sequence
log-probability for each so the search's priority queue (which orders by
cumulative log-probability) behaves correctly.

Usage:
    python proof_search.py --mm set.mm --goal "|- ( ph -> ph )" \
        --model-module model.py

    python proof_search.py --mm set.mm --eval valid.jsonl \
        --model-module model.py
"""

import os

import torch
from transformers import AutoModelForCausalLM, AutoTokenizer

# Point this at the directory train_model.py saved (<output-dir>/final).
MODEL_DIR = os.environ.get("PROVER_MODEL_DIR", "./finetuning/output/finetuned-prover/final")

PROMPT_TEMPLATE = "GOAL: {goal}\nPROOFSTEP:"

# Sub-batch size for generation -- keeps peak memory bounded when n is
# large (e.g. n=32) instead of generating all candidates in one shot.
GEN_SUB_BATCH = 8
MAX_NEW_TOKENS = 128


class Model:
    def __init__(self, model_dir: str = MODEL_DIR, device: str = None):
        self.device = device or ("cuda" if torch.cuda.is_available() else "cpu")
        self.tokenizer = AutoTokenizer.from_pretrained(model_dir)
        if self.tokenizer.pad_token is None:
            self.tokenizer.pad_token = self.tokenizer.eos_token

        self.model = AutoModelForCausalLM.from_pretrained(
            model_dir, torch_dtype=torch.bfloat16
        ).to(self.device)
        self.model.eval()

    @torch.no_grad()
    def generate_steps(
        self,
        goal_str: str,
        n: int = 32,
        temperature: float = 1.0,
    ) -> list[tuple[str, float]]:
        prompt = PROMPT_TEMPLATE.format(goal=goal_str)
        inputs = self.tokenizer(prompt, return_tensors="pt").to(self.device)
        prompt_len = inputs["input_ids"].shape[1]
        eos_id = self.tokenizer.eos_token_id

        # text -> best log-probability seen for that exact string
        candidates: dict[str, float] = {}

        remaining = n
        while remaining > 0:
            k = min(GEN_SUB_BATCH, remaining)
            outputs = self.model.generate(
                **inputs,
                do_sample=True,
                temperature=max(temperature, 1e-4),
                top_p=0.95,
                num_return_sequences=k,
                max_new_tokens=MAX_NEW_TOKENS,
                pad_token_id=self.tokenizer.pad_token_id,
                eos_token_id=eos_id,
                output_scores=True,
                return_dict_in_generate=True,
            )

            # Per-token log-probabilities for every generated position.
            transition_scores = self.model.compute_transition_scores(
                outputs.sequences, outputs.scores, normalize_logits=True
            )

            for i in range(k):
                full_ids = outputs.sequences[i][prompt_len:].tolist()

                # Sequences that finish early are right-padded up to the
                # batch's max length. Cut at the first EOS so neither the
                # decoded text nor the summed log-probability includes
                # padding that isn't part of the model's actual output.
                gen_len = full_ids.index(eos_id) if eos_id in full_ids else len(full_ids)
                gen_ids = full_ids[:gen_len]

                logprob = transition_scores[i][:gen_len].sum().item()
                text = self.tokenizer.decode(gen_ids, skip_special_tokens=True).strip()

                if text and (text not in candidates or logprob > candidates[text]):
                    candidates[text] = logprob

            remaining -= k

        ranked = sorted(candidates.items(), key=lambda kv: kv[1], reverse=True)
        return ranked[:n]

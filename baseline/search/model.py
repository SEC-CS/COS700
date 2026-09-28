"""
Implements the Model interface proof_search.py and premis_search.py expects.

Format required by proof_search.py:
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
"""

import os
import sys

import torch
from transformers import AutoModelForCausalLM, AutoTokenizer

# Point this at the directory train_model.py saved (<output-dir>/final).
if not os.environ.get("PROVER_MODEL_DIR"):
    print(
        "Please set PROVER_MODEL_DIR to the directory containing the trained model, e.g.:\n"
        "  $env:PROVER_MODEL_DIR = '.\\baseline\\finetuning\\output\\longest_theorems\\final'"
    )
    sys.exit(1)
MODEL_DIR = os.environ.get("PROVER_MODEL_DIR")

PROMPT_TEMPLATE = "GOAL: {goal}\nPROOFSTEP:"

MAX_NEW_TOKENS = 128

# Set PROVER_DEBUG_GENLEN=1 to print how many tokens generations are
# actually using. If the reported max/mean sit well under MAX_NEW_TOKENS,
# that constant is safe to lower -- every unused token budget is wasted
# decode steps the whole sub-batch waits on. Off by default: adds a single
# cheap counter increment per candidate and nothing else.
_DEBUG_GEN_LEN = os.environ.get("PROVER_DEBUG_GENLEN") == "1"


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
        self._gen_batch_size = None
        self._successes_since_shrink = 0
        self._growth_patience = 20

        if _DEBUG_GEN_LEN:
            self._genlen_count = 0
            self._genlen_sum = 0
            self._genlen_max = 0

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

        batch_size = self._gen_batch_size or n
        remaining = n

        consecutive_oom_at_floor = 0
        MAX_OOM_AT_FLOOR = 3

        while remaining > 0:
            k = min(batch_size, remaining)
            try:
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

                transition_scores = self.model.compute_transition_scores(
                    outputs.sequences, outputs.scores, normalize_logits=True
                )
                # Decrease batch if OOM
            except torch.cuda.OutOfMemoryError:
                torch.cuda.empty_cache()
                if batch_size == 1:
                    consecutive_oom_at_floor += 1
                    if consecutive_oom_at_floor >= MAX_OOM_AT_FLOOR:
                        raise RuntimeError(
                            f"generate_steps() OOM'd {MAX_OOM_AT_FLOOR} times "
                            f"possible mem leak or goal too large for GPU. "
                        ) from None
                else:
                    consecutive_oom_at_floor = 0
                batch_size = max(1, batch_size // 2)
                self._gen_batch_size = batch_size
                self._successes_since_shrink = 0
                continue

            consecutive_oom_at_floor = 0
            self._gen_batch_size = batch_size

            if batch_size < n:
                self._successes_since_shrink += 1
                if self._successes_since_shrink >= self._growth_patience:
                    grown = min(batch_size * 2, n)
                    if _DEBUG_GEN_LEN:
                        print(
                            f"[gen_batch] {self._successes_since_shrink} "
                            f"OOM-free calls at {batch_size} -- "
                            f"trying {grown}"
                        )
                    batch_size = grown
                    self._gen_batch_size = grown
                    self._successes_since_shrink = 0

            for i in range(k):
                full_ids = outputs.sequences[i][prompt_len:].tolist()

                gen_len = (
                    full_ids.index(eos_id) if eos_id in full_ids else len(full_ids)
                )
                gen_ids = full_ids[:gen_len]

                logprob = transition_scores[i][:gen_len].sum().item()
                text = self.tokenizer.decode(gen_ids, skip_special_tokens=True).strip()

                if text and (text not in candidates or logprob > candidates[text]):
                    candidates[text] = logprob

            remaining -= k

        ranked = sorted(candidates.items(), key=lambda kv: kv[1], reverse=True)
        return ranked[:n]

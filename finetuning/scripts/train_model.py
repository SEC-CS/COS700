#!/usr/bin/env python
"""
train_model.py
===============
Fine-tunes a pre-trained causal language model on extracted Metamath
proof steps (methodology section 4a).

Training objective: conditional language modelling. Given a GOAL, predict
the PROOFSTEP. Loss is masked on the GOAL portion of each sequence so the
model only receives gradient signal from learning to generate correct
tactics -- exactly the setup described in the methodology doc, and the
same one used by the GPT-f paper.

Expected input format
----------------------
--train / --valid point to JSONL files, one record per proof step:

    {"proof_label":  "xornan",
     "goal":         "[[ ]] |- ( ( ph \\/_ ps ) <-> ( ( ph \\/ ps ) /\\ -. ( ph /\\ ps ) ) )",
     "theorem":      "xor2",
     "substitution": {"ph": ["ph"], "ps": ["ps"]}}

i.e. "theorem" is the label of the axiom/theorem applied at this proof
step, and "substitution" maps its mandatory variables to their
substituted token lists. This matches the fields extract_proof_steps.py
actually writes and the fields evaluate() in proof_search.py already
reads (proof_label, goal).

The training TARGET (the PROOFSTEP text the model has to learn to
generate) is built from theorem + substitution by format_proofstep()
below, which mirrors _format_proofstep() in proof_search.py exactly --
producing "theorem_label {{ var1 : val1 }} {{ var2 : val2 }} ..." --
since that's the exact string proof_search.py's _parse_proofstep() will
parse back out of the model's generations at search time. Keep the two
functions in sync if either changes.

These records need to be split into train/valid/test files first --
see split_dataset.py -- before pointing --train/--valid at them.

Output
------
A single directory containing the fine-tuned model's weights, config, and
tokenizer -- loadable with a plain AutoModelForCausalLM.from_pretrained()
call, per the methodology doc. If --use-lora is on (the default), LoRA
adapters are trained for efficiency and merged back into the base model
before saving, so the *saved* artifact is a normal, adapter-free model.

Usage
-----
    pip install torch transformers peft accelerate bitsandbytes

    python -m finetuning.scripts.train_model --train finetuning/data/train.jsonl --valid finetuning/data/valid.jsonl --base-model Qwen/Qwen2.5-Coder-0.5B --output-dir ./finetuning/output/finetuned-prover --epochs 1 --batch-size 8 --grad-accum 4 --max-length 512 --max-valid-samples 2000 --eval-steps 5000 --save-steps 5000


Then point proof_search.py at the result via model.py (see that file).
"""

import argparse
import json
import os

import torch
from torch.utils.data import Dataset
from transformers import (
    AutoModelForCausalLM,
    AutoTokenizer,
    Trainer,
    TrainingArguments,
)

PROMPT_TEMPLATE = "GOAL: {goal}\nPROOFSTEP:"


def format_proofstep(theorem: str, substitution: dict) -> str:
    """
    Build the target PROOFSTEP text from a record's theorem + substitution
    fields: "theorem_label {{ var1 : val1 }} {{ var2 : val2 }} ...".

    This must stay byte-for-byte in sync with _format_proofstep() in
    proof_search.py -- that's the function whose *parser* counterpart,
    _parse_proofstep(), will be run on the model's generations during
    proof search, so the model needs to be trained on exactly the string
    shape it will be evaluated against.
    """
    subst_str = " ".join(
        f"{{{{ {v} : {' '.join(val)} }}}}"
        for v, val in sorted(substitution.items())
        if val
    )
    return f"{theorem}" + (f" {subst_str}" if subst_str else "")


# ---------------------------------------------------------------------------
# Dataset
# ---------------------------------------------------------------------------


class ProofStepDataset(Dataset):
    """
    Reads a JSONL file of {goal, proof_step} records and tokenizes each into
    a single (prompt + target) sequence, with labels for the prompt tokens
    set to -100 so the loss is only computed over the PROOFSTEP portion.
    """

    def __init__(
        self,
        jsonl_path: str,
        tokenizer,
        max_length: int = 512,
        max_examples: int = None,
    ):
        self.examples = []
        with open(jsonl_path) as f:
            for line_no, line in enumerate(f, start=1):
                if max_examples is not None and len(self.examples) >= max_examples:
                    break
                line = line.strip()
                if not line:
                    continue
                record = json.loads(line)
                try:
                    proof_step = format_proofstep(
                        record["theorem"], record["substitution"]
                    )
                    goal = record["goal"]
                except KeyError as e:
                    raise KeyError(
                        f"{jsonl_path}:{line_no} is missing field {e} -- "
                    ) from e
                self.examples.append((goal, proof_step))
        self.tokenizer = tokenizer
        self.max_length = max_length

    def __len__(self):
        return len(self.examples)

    def __getitem__(self, idx):
        goal, proofstep = self.examples[idx]
        prompt = PROMPT_TEMPLATE.format(goal=goal)
        target = " " + proofstep + self.tokenizer.eos_token

        prompt_ids = self.tokenizer(prompt, add_special_tokens=False)["input_ids"]
        target_ids = self.tokenizer(target, add_special_tokens=False)["input_ids"]

        input_ids = (prompt_ids + target_ids)[: self.max_length]
        labels = ([-100] * len(prompt_ids) + target_ids)[: self.max_length]

        return {
            "input_ids": input_ids,
            "labels": labels,
            "attention_mask": [1] * len(input_ids),
        }


class PadCollator:
    """Dynamically pads a batch of variable-length examples."""

    def __init__(self, tokenizer):
        self.tokenizer = tokenizer

    def __call__(self, batch):
        max_len = max(len(x["input_ids"]) for x in batch)
        pad_id = self.tokenizer.pad_token_id

        input_ids, attention_mask, labels = [], [], []
        for x in batch:
            pad_len = max_len - len(x["input_ids"])
            input_ids.append(x["input_ids"] + [pad_id] * pad_len)
            attention_mask.append(x["attention_mask"] + [0] * pad_len)
            labels.append(x["labels"] + [-100] * pad_len)

        return {
            "input_ids": torch.tensor(input_ids, dtype=torch.long),
            "attention_mask": torch.tensor(attention_mask, dtype=torch.long),
            "labels": torch.tensor(labels, dtype=torch.long),
        }


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--train", required=True, help="Path to train.jsonl")
    parser.add_argument("--valid", required=True, help="Path to valid.jsonl")
    parser.add_argument(
        "--base-model",
        default="Qwen/Qwen2.5-Coder-0.5B",
        help="HF hub id or local path of the base model",
    )
    parser.add_argument("--output-dir", default="./finetuning/output/finetuned-prover")
    parser.add_argument("--epochs", type=float, default=2)
    parser.add_argument("--batch-size", type=int, default=6)
    parser.add_argument(
        "--eval-batch-size",
        type=int,
        default=None,
        help="Batch size for validation passes. Eval has "
        "no backward pass, so this can usually be "
        "set higher than --batch-size without OOM. "
        "Defaults to --batch-size if unset.",
    )
    parser.add_argument("--grad-accum", type=int, default=4)
    parser.add_argument(
        "--lr",
        type=float,
        default=1e-4,
        help="Learning rate (default 1e-4 is tuned for "
        "small datasets; use 2e-4 for larger datasets)",
    )
    parser.add_argument("--max-length", type=int, default=400)
    parser.add_argument("--eval-steps", type=int, default=250)
    parser.add_argument("--save-steps", type=int, default=250)
    parser.add_argument(
        "--max-steps",
        type=int,
        default=-1,
        help="Cap training at this many optimizer steps, "
        "overriding --epochs. Use for a quick smoke "
        "test, e.g. --max-steps 300",
    )
    parser.add_argument(
        "--max-train-samples",
        type=int,
        default=None,
        help="Only read the first N examples from --train "
        "(skips tokenizing the whole file -- useful "
        "for a quick test run)",
    )
    parser.add_argument(
        "--max-valid-samples",
        type=int,
        default=None,
        help="Only read the first N examples from --valid",
    )
    parser.add_argument(
        "--use-lora",
        dest="use_lora",
        action="store_true",
        default=True,
        help="Train LoRA adapters (default)",
    )
    parser.add_argument(
        "--no-lora",
        dest="use_lora",
        action="store_false",
        help="Full fine-tune instead of LoRA",
    )
    parser.add_argument(
        "--lora-rank",
        type=int,
        default=16,
        help="LoRA rank r (default 8 for small datasets; "
        "use 16 for larger datasets)",
    )
    parser.add_argument(
        "--lora-alpha",
        type=int,
        default=32,
        help="LoRA alpha scaling (default 16; keep alpha/r ≈ 2)",
    )
    parser.add_argument(
        "--load-in-4bit",
        action="store_true",
        help="QLoRA: quantize the base model to 4-bit "
        "before attaching LoRA adapters",
    )
    parser.add_argument(
        "--gradient-checkpointing",
        dest="grad_ckpt",
        action="store_true",
        default=None,
        help="Force gradient checkpointing on (trades "
        "speed for memory -- lets you fit a bigger "
        "batch). Default: off with LoRA, on for a "
        "full fine-tune.",
    )
    parser.add_argument(
        "--no-gradient-checkpointing", dest="grad_ckpt", action="store_false"
    )
    parser.add_argument(
        "--num-workers", type=int, default=2, help="Dataloader worker processes"
    )
    args = parser.parse_args()
    if args.grad_ckpt is None:
        args.grad_ckpt = not args.use_lora

    # --- Detect what hardware is actually available and pick a matching
    # --- precision, instead of assuming bf16 + GPU are there. -----------
    has_cuda = torch.cuda.is_available()
    use_bf16 = has_cuda and torch.cuda.is_bf16_supported()
    use_fp16 = has_cuda and not use_bf16

    if has_cuda:
        gpu_name = torch.cuda.get_device_name(0)
        precision = "bf16" if use_bf16 else "fp16"
        print(f"GPU detected: {gpu_name} -- training in {precision}.")
        compute_dtype = torch.bfloat16 if use_bf16 else torch.float16
        # Free speed on Ampere+ (RTX 30/40-series and newer): lets matmuls
        # use TF32 internally without affecting the bf16/fp16 training
        # precision set above.
        torch.backends.cuda.matmul.allow_tf32 = True
        torch.backends.cudnn.allow_tf32 = True
    else:
        precision = "fp32 (CPU)"
        compute_dtype = torch.float32
        print("No CUDA GPU detected -- falling back to CPU.")
        print("WARNING: fine-tuning a 1.5B-parameter model on ~3M examples")
        print("on CPU is not practically feasible (this would take weeks")
        print("to months). If you have an NVIDIA GPU in this machine, check")
        print("that torch was installed with CUDA support:")
        print('  python -c "import torch; print(torch.cuda.is_available())"')
        print("If that prints False on a machine with an NVIDIA GPU, your")
        print("torch install is CPU-only -- reinstall from")
        print("https://pytorch.org/get-started/locally/ with the matching")
        print("CUDA version selected. If there's no GPU at all, consider a")
        print("hosted GPU (Colab, Kaggle, a university cluster) instead.")

    if args.load_in_4bit and not has_cuda:
        print("--load-in-4bit requires a CUDA GPU; ignoring it on CPU.")
        args.load_in_4bit = False

    tokenizer = AutoTokenizer.from_pretrained(args.base_model)
    if tokenizer.pad_token is None:
        tokenizer.pad_token = tokenizer.eos_token

    model_kwargs = dict(dtype=compute_dtype)
    if args.load_in_4bit:
        from transformers import BitsAndBytesConfig

        model_kwargs["quantization_config"] = BitsAndBytesConfig(
            load_in_4bit=True,
            bnb_4bit_compute_dtype=compute_dtype,
            bnb_4bit_quant_type="nf4",
        )

    model = AutoModelForCausalLM.from_pretrained(
        args.base_model, attn_implementation="sdpa", **model_kwargs
    )
    model.config.pad_token_id = tokenizer.pad_token_id

    if args.use_lora:
        from peft import LoraConfig, TaskType, get_peft_model

        if args.load_in_4bit:
            from peft import prepare_model_for_kbit_training

            model = prepare_model_for_kbit_training(
                model, use_gradient_checkpointing=args.grad_ckpt
            )
        lora_config = LoraConfig(
            task_type=TaskType.CAUSAL_LM,
            r=args.lora_rank,
            lora_alpha=args.lora_alpha,
            lora_dropout=0.05,
            target_modules=[
                "q_proj",
                "k_proj",
                "v_proj",
                "o_proj",
                "gate_proj",
                "up_proj",
                "down_proj",
            ],
        )
        model = get_peft_model(model, lora_config)
        model.print_trainable_parameters()
    else:
        model.gradient_checkpointing_enable()

    train_dataset = ProofStepDataset(
        args.train, tokenizer, args.max_length, max_examples=args.max_train_samples
    )
    valid_dataset = ProofStepDataset(
        args.valid, tokenizer, args.max_length, max_examples=args.max_valid_samples
    )
    collator = PadCollator(tokenizer)

    print(f"Train examples: {len(train_dataset)}")
    print(f"Valid examples: {len(valid_dataset)}")

    training_args = TrainingArguments(
        output_dir=os.path.join(args.output_dir, "checkpoints"),
        num_train_epochs=args.epochs,
        max_steps=args.max_steps,
        per_device_train_batch_size=args.batch_size,
        per_device_eval_batch_size=args.eval_batch_size or args.batch_size,
        gradient_accumulation_steps=args.grad_accum,
        learning_rate=args.lr,
        warmup_ratio=0.03,
        lr_scheduler_type="cosine",
        logging_steps=50,
        eval_strategy="steps",
        eval_steps=args.eval_steps,
        save_strategy="steps",
        save_steps=args.save_steps,
        save_total_limit=3,
        bf16=use_bf16,
        fp16=use_fp16,
        use_cpu=not has_cuda,
        gradient_checkpointing=args.grad_ckpt,
        dataloader_num_workers=args.num_workers,
        dataloader_pin_memory=has_cuda,
        report_to="none",
    )

    trainer = Trainer(
        model=model,
        args=training_args,
        train_dataset=train_dataset,
        eval_dataset=valid_dataset,
        data_collator=collator,
    )

    trainer.train()

    # Merge LoRA adapters (if used) so the saved artifact is a plain model
    # directory -- weights + config + tokenizer, loadable with a single
    # AutoModelForCausalLM.from_pretrained() call, per the methodology.
    if args.use_lora:
        model = model.merge_and_unload()

    final_dir = os.path.join(args.output_dir, "final")
    model.save_pretrained(final_dir)

    tokenizer.save_pretrained(final_dir)
    print(f"Saved fine-tuned model to {final_dir}")


if __name__ == "__main__":
    main()

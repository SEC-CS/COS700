#!/usr/bin/env python
"""
train_substitution_model.py
============================
Fine-tunes a pre-trained causal language model to predict a theorem's
SUBSTITUTION, given the GOAL and that theorem's own structural
definition (its mandatory variables, essential hypotheses, and
conclusion) -- NOT the theorem's name/label.

Why the theorem's structure instead of its name
-------------------------------------------------
Feeding the model a bare label like "xor2" forces it to memorize, per
theorem name, what variables that theorem has and what shape its
conclusion takes -- that knowledge doesn't transfer to a theorem it
saw rarely or never during training.

Feeding it the theorem's actual mandatory variables, hypotheses, and
conclusion instead gives the model the same information a human proving
the goal by hand would use: the conclusion's shape can be pattern-matched
against the goal's own shape to work out most variable values (since the
conclusion, once correctly substituted, must equal the goal), and the
mandatory variable list tells the model exactly which variables it needs
to produce values for in the first place.

Where this structural info comes from
---------------------------------------
The JSONL only stores each record's theorem NAME. To turn that into its
actual definition, this script loads the real .mm database (the same way
proof_search.py does, via mmverify.py) and looks the label up in
mm.labels: `(distinct, mand_var, hyp, result) = mm.labels[theorem][1]`.
The theorem name itself is discarded after this lookup -- it never
appears in the model's input.

`distinct` ($d disjointness constraints) is deliberately left out of the
prompt: it's a validity check the verifier applies AFTER a substitution
is proposed, not information that helps produce the substitution's
token values in the first place.

ASSUMPTION TO VERIFY: this assumes mand_var entries are
(typecode, varname) tuples, matching how proof_search.py destructures
them (`for _, v in mand_var`). If your mmverify.py stores them the other
way round, swap the unpacking in format_theorem_info() below.

Expected input format
----------------------
--train / --valid point to JSONL files, one record per proof step:

    {"proof_label":  "xornan",
     "goal":         "[[ ]] |- ( ( ph \\/_ ps ) <-> ( ( ph \\/ ps ) /\\ -. ( ph /\\ ps ) ) )",
     "theorem":      "xor2",
     "substitution": {"ph": ["ph"], "ps": ["ps"]}}

"goal" goes into the prompt as-is. "theorem" is used only to look up
that theorem's definition in the .mm database (see above) -- it is not
itself part of the model's input. "substitution" is turned into the
generation TARGET by format_substitution() below.

IMPORTANT: format_substitution()/parse_substitution() below are a
reasonable default ("{{ var : val }} {{ var : val }} ..."), but they are
NOT guaranteed to match your existing proof_search.py parsing logic. If
proof_search.py already has a substitution parser, keep these two
functions in sync with it (or better, import the real one) -- otherwise
this model will learn to produce a format nothing downstream can read.

Output
------
A single directory containing the fine-tuned model's weights, config,
and tokenizer -- loadable with a plain AutoModelForCausalLM.from_pretrained()
call. If --use-lora is on (the default), LoRA adapters are trained for
efficiency and merged back into the base model before saving, so the
*saved* artifact is a normal, adapter-free model.

Usage
-----
    pip install torch transformers peft accelerate bitsandbytes

    python -m finetuning.scripts.train_substitution_model --mm data/set.mm --mmverify data/mmverify.py --train finetuning/data/train.jsonl --valid finetuning/data/valid.jsonl --base-model Qwen/Qwen2.5-Coder-0.5B --output-dir ./finetuning/output/finetuned-substitution --epochs 1 --batch-size 8 --grad-accum 4 --max-length 512 --max-valid-samples 2000 --eval-steps 5000 --save-steps 5000
    (
        uv run python -m modular.finetuning.scripts.train_model_sub
          --mm baseline/data/set.mm
          --mmverify baseline/data/mmverify.py
          --train baseline/data/small_datasets/longest_theorems/train.jsonl
          --valid baseline/data/small_datasets/longest_theorems/valid.jsonl
          --base-model Qwen/Qwen2.5-Coder-0.5B
          --output-dir ./modular/finetuning/output/finetuned-substitution
          --epochs 1
          --batch-size 8
          --grad-accum 4
          --max-length 512
          --max-valid-samples 2000
          --eval-steps 5000
          --save-steps 5000
    )
"""

import argparse
import importlib.util
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

PROMPT_TEMPLATE = (
    "GOAL: {goal}\n"
    "MANDVARS: {mandvars}\n"
    "HYP: {hyp}\n"
    "RESULT: {result}\n"
    "SUBSTITUTION:"
)


# ---------------------------------------------------------------------------
# .mm database loading and theorem-info lookup
# ---------------------------------------------------------------------------


def load_mmverify(path: str):
    """Load mmverify.py as a module from a file path (same approach as
    proof_search.py's load_mmverify, duplicated here so this script has
    no import dependency on proof_search.py)."""
    spec = importlib.util.spec_from_file_location("mmverify", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    mod.verbosity = 0
    return mod


def load_mm_database(mm_path: str, mmverify_path: str):
    """Loads the .mm database and returns the mm object, whose .labels
    dict is what format_theorem_info()/build_theorem_info_cache() below
    look theorems up in."""
    mmv = load_mmverify(mmverify_path)
    mm = mmv.MM()
    with open(mm_path, "r", encoding="utf-8", errors="replace") as f:
        mm.read(mmv.toks(f))
    return mm


def format_theorem_info(mand_var: list, hyp: list, result: list) -> dict:
    """
    Turns a theorem's raw (mand_var, hyp, result) -- as stored in
    mm.labels -- into the three text fields the prompt template needs.

    mand_var: list of (typecode, varname) tuples -- see the ASSUMPTION
        note at the top of this file if this order is wrong for your
        mmverify.py.
    hyp:      list of essential hypotheses, each a list of tokens.
    result:   the theorem's conclusion, a list of tokens.
    """
    mandvars_str = ", ".join(f"{typecode} {var}" for typecode, var in mand_var)
    hyp_str = " ; ".join(" ".join(tokens) for tokens in hyp)
    result_str = " ".join(result)
    return {"mandvars": mandvars_str, "hyp": hyp_str, "result": result_str}


def build_theorem_info_cache(mm, labels_needed: set) -> dict:
    """
    Looks up every label in labels_needed once and caches its formatted
    theorem-info fields, so a training set with many repeated theorems
    doesn't repeat the same mm.labels lookup and formatting work for
    every single example that uses it.

    Labels missing from mm.labels, or not a $a/$p statement, are left
    out of the returned cache; callers use that to skip such examples.
    """
    cache = {}
    for label in labels_needed:
        entry = mm.labels.get(label)
        if entry is None:
            continue
        kind, data = entry
        if kind not in ("$a", "$p"):
            continue
        _distinct, mand_var, hyp, result = data
        cache[label] = format_theorem_info(mand_var, hyp, result)
    return cache


# ---------------------------------------------------------------------------
# Substitution <-> text formatting
# ---------------------------------------------------------------------------


def format_substitution(substitution: dict) -> str:
    """
    Turns {"ph": ["ph"], "ps": ["ps", "ch"]} into the generation target
    text: "{{ ph : ph }} {{ ps : ps ch }}".

    Variable order follows the dict's own key order (i.e. whatever order
    it was written in the JSONL record), on the assumption that this
    already matches the theorem's canonical mandatory-variable order. If
    that assumption doesn't hold for your data, sort the keys explicitly
    here instead.
    """
    parts = []
    for var, value_tokens in substitution.items():
        value_str = " ".join(value_tokens)
        parts.append(f"{{{{ {var} : {value_str} }}}}")
    return " ".join(parts)


def parse_substitution(text: str) -> dict:
    """
    Inverse of format_substitution(): parses "{{ ph : ph }} {{ ps : ps ch }}"
    back into {"ph": ["ph"], "ps": ["ps", "ch"]}.

    Used at inference time to turn the model's generated text back into a
    usable substitution dict. Malformed generations (the model can always
    produce garbage) are skipped rather than raising, since a caller
    doing proof search needs to keep going even if one candidate is bad.
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


# ---------------------------------------------------------------------------
# Dataset
# ---------------------------------------------------------------------------


class SubstitutionDataset(Dataset):
    """
    Reads a JSONL file of {goal, theorem, substitution} records and
    tokenizes each into a single (prompt + target) sequence, with labels
    for the prompt tokens set to -100 so the loss is only computed over
    the SUBSTITUTION portion.

    The prompt is built from the goal plus theorem_info_cache[theorem]
    (mandatory variables, hypotheses, conclusion) -- never from the
    theorem's name itself.
    """

    def __init__(
        self,
        jsonl_path: str,
        tokenizer,
        theorem_info_cache: dict,
        max_length: int = 512,
        max_examples: int = None,
    ):
        self.examples = []
        skipped_unknown_theorem = 0

        with open(jsonl_path) as f:
            for line_no, line in enumerate(f, start=1):
                if max_examples is not None and len(self.examples) >= max_examples:
                    break
                line = line.strip()
                if not line:
                    continue
                record = json.loads(line)
                try:
                    goal = record["goal"]
                    theorem = record["theorem"]
                    substitution_text = format_substitution(record["substitution"])
                except KeyError as e:
                    raise KeyError(f"{jsonl_path}:{line_no} is missing field {e}") from e

                # A theorem missing from the .mm database (or not a
                # $a/$p statement) has no structural info to build a
                # prompt from, so this example can't be used.
                if theorem not in theorem_info_cache:
                    skipped_unknown_theorem += 1
                    continue

                self.examples.append(
                    (goal, theorem_info_cache[theorem], substitution_text)
                )

        if skipped_unknown_theorem:
            print(
                f"WARNING: {jsonl_path} contained {skipped_unknown_theorem} example(s) "
                "whose theorem was missing from the .mm database (or not a $a/$p "
                "statement); they were skipped."
            )

        self.tokenizer = tokenizer
        self.max_length = max_length

    def __len__(self):
        return len(self.examples)

    def __getitem__(self, idx):
        goal, theorem_info, substitution_text = self.examples[idx]
        prompt = PROMPT_TEMPLATE.format(goal=goal, **theorem_info)
        target = " " + substitution_text + self.tokenizer.eos_token

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


def collect_theorem_labels(*jsonl_paths: str) -> set:
    """Scans one or more JSONL files and returns every distinct theorem
    label used, so the .mm lookup cache can be built once up front."""
    labels = set()
    for path in jsonl_paths:
        with open(path) as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                labels.add(json.loads(line)["theorem"])
    return labels


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mm", required=True, help="Path to the .mm database (e.g. set.mm)")
    parser.add_argument(
        "--mmverify", required=True, help="Path to mmverify.py, used to parse --mm"
    )
    parser.add_argument("--train", required=True, help="Path to train.jsonl")
    parser.add_argument("--valid", required=True, help="Path to valid.jsonl")
    parser.add_argument(
        "--base-model",
        default="Qwen/Qwen2.5-Coder-0.5B",
        help="HF hub id or local path of the base model",
    )
    parser.add_argument("--output-dir", default="./finetuning/output/finetuned-substitution")
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
        help="LoRA alpha scaling (default 16; keep alpha/r ~= 2)",
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
        torch.backends.cuda.matmul.allow_tf32 = True
        torch.backends.cudnn.allow_tf32 = True
    else:
        precision = "fp32 (CPU)"
        compute_dtype = torch.float32
        print("No CUDA GPU detected -- falling back to CPU.")
        print("WARNING: fine-tuning on CPU with a large dataset is not")
        print("practically feasible (this could take weeks to months). If")
        print("you have an NVIDIA GPU in this machine, check that torch")
        print("was installed with CUDA support:")
        print('  python -c "import torch; print(torch.cuda.is_available())"')
        print("If that prints False on a machine with an NVIDIA GPU, your")
        print("torch install is CPU-only -- reinstall from")
        print("https://pytorch.org/get-started/locally/ with the matching")
        print("CUDA version selected. If there's no GPU at all, consider a")
        print("hosted GPU (Colab, Kaggle, a university cluster) instead.")

    if args.load_in_4bit and not has_cuda:
        print("--load-in-4bit requires a CUDA GPU; ignoring it on CPU.")
        args.load_in_4bit = False

    # --- Load the .mm database once and look up every theorem this run
    # --- will need, so each JSONL example's prompt can be built from
    # --- that theorem's actual mandatory variables/hypotheses/result
    # --- instead of its bare name. --------------------------------------
    print(f"Loading .mm database from {args.mm} ...")
    mm = load_mm_database(args.mm, args.mmverify)
    labels_needed = collect_theorem_labels(args.train, args.valid)
    theorem_info_cache = build_theorem_info_cache(mm, labels_needed)
    print(
        f"Resolved structural info for {len(theorem_info_cache)}/"
        f"{len(labels_needed)} distinct theorem labels."
    )

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

    train_dataset = SubstitutionDataset(
        args.train,
        tokenizer,
        theorem_info_cache,
        args.max_length,
        max_examples=args.max_train_samples,
    )
    valid_dataset = SubstitutionDataset(
        args.valid,
        tokenizer,
        theorem_info_cache,
        args.max_length,
        max_examples=args.max_valid_samples,
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

    if args.use_lora:
        model = model.merge_and_unload()

    final_dir = os.path.join(args.output_dir, "final")
    model.save_pretrained(final_dir)
    tokenizer.save_pretrained(final_dir)
    print(f"Saved fine-tuned substitution model to {final_dir}")


if __name__ == "__main__":
    main()

#!/usr/bin/env python
"""
Fine-tune a sequence classifier that predicts which theorem label applies to a proof goal.
The label vocabulary is built from --train and saved alongside the model as label_map.json.
"""

import argparse
import json
import os

import numpy as np
import torch
from torch.utils.data import Dataset
from transformers import (
    AutoModelForSequenceClassification,
    AutoTokenizer,
    DataCollatorWithPadding,
    Trainer,
    TrainingArguments,
)

from utils.training_stats import train_and_record_time


def build_label_vocab(jsonl_path: str) -> dict:
    """
    Scans a JSONL file once and returns a {theorem_name: class_index}
    mapping, sorted alphabetically for a deterministic, reproducible
    ordering across runs.

    The label vocabulary is built ONLY from --train. --valid is checked
    against it later (see ProofLabelDataset) rather than contributing new
    labels itself, because a class the model never saw during training
    can never be predicted correctly regardless of how it's encoded.
    """
    labels = set()
    with open(jsonl_path) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            record = json.loads(line)
            labels.add(record["theorem"])
    return {label: idx for idx, label in enumerate(sorted(labels))}


class ProofLabelDataset(Dataset):
    """
    Reads a JSONL file of {goal, theorem} records and tokenizes each GOAL
    on its own -- no target text is appended, because the label is a
    single class index, not generated text.
    """

    def __init__(
        self,
        jsonl_path: str,
        tokenizer,
        label2id: dict,
        max_length: int = 512,
        max_examples: int = None,
    ):
        self.examples = []
        skipped_unseen_label = 0

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
                except KeyError as e:
                    raise KeyError(f"{jsonl_path}:{line_no} is missing field {e}") from e

                if theorem not in label2id:
                    skipped_unseen_label += 1
                    continue

                self.examples.append((goal, label2id[theorem]))

        if skipped_unseen_label:
            print(
                f"WARNING: {jsonl_path} contained {skipped_unseen_label} example(s) "
                "whose theorem label never appeared in --train; they were skipped "
                "because the model has no class index for them."
            )

        self.tokenizer = tokenizer
        self.max_length = max_length

    def __len__(self):
        return len(self.examples)

    def __getitem__(self, idx):
        goal, label_id = self.examples[idx]
        encoded = self.tokenizer(
            goal,
            truncation=True,
            max_length=self.max_length,
        )
        encoded["labels"] = label_id
        return encoded


def compute_metrics(eval_pred):
    """Plain top-1 accuracy: fraction of examples where the highest-scoring
    class matches the true theorem label."""
    logits, labels = eval_pred
    predictions = np.argmax(logits, axis=-1)
    accuracy = (predictions == labels).mean()
    return {"accuracy": accuracy}


def main(
    dataset_cls=ProofLabelDataset,
    doc=__doc__,
    output_dir="./finetuning/modular/output/finetuned-classifier",
):
    parser = argparse.ArgumentParser(description=doc)
    parser.add_argument("--train", required=True, help="Path to train.jsonl")
    parser.add_argument("--valid", required=True, help="Path to valid.jsonl")
    parser.add_argument(
        "--base-model",
        default="Qwen/Qwen2.5-Coder-0.5B",
        help="HF hub id or local path of the base model",
    )
    parser.add_argument("--output-dir", default=output_dir)
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

    label2id = build_label_vocab(args.train)
    id2label = {idx: label for label, idx in label2id.items()}
    print(f"Label vocabulary: {len(label2id)} distinct theorem labels")

    tokenizer = AutoTokenizer.from_pretrained(args.base_model)
    if tokenizer.pad_token is None:
        tokenizer.pad_token = tokenizer.eos_token
    # Sequence classification pools the last non-pad token, so pad on the left.
    tokenizer.padding_side = "left"

    model_kwargs = dict(dtype=compute_dtype)
    if args.load_in_4bit:
        from transformers import BitsAndBytesConfig

        model_kwargs["quantization_config"] = BitsAndBytesConfig(
            load_in_4bit=True,
            bnb_4bit_compute_dtype=compute_dtype,
            bnb_4bit_quant_type="nf4",
        )

    model = AutoModelForSequenceClassification.from_pretrained(
        args.base_model,
        num_labels=len(label2id),
        id2label=id2label,
        label2id=label2id,
        attn_implementation="sdpa",
        **model_kwargs,
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
            task_type=TaskType.SEQ_CLS,
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
            # The classification head is newly initialised, so LoRA must train it too.
            modules_to_save=["score"],
        )
        model = get_peft_model(model, lora_config)
        model.print_trainable_parameters()
    else:
        model.gradient_checkpointing_enable()

    train_dataset = dataset_cls(
        args.train,
        tokenizer,
        label2id,
        args.max_length,
        max_examples=args.max_train_samples,
    )
    valid_dataset = dataset_cls(
        args.valid,
        tokenizer,
        label2id,
        args.max_length,
        max_examples=args.max_valid_samples,
    )
    collator = DataCollatorWithPadding(tokenizer)

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
        compute_metrics=compute_metrics,
    )

    train_and_record_time(trainer, args.output_dir)

    if args.use_lora:
        model = model.merge_and_unload()

    final_dir = os.path.join(args.output_dir, "final")
    model.save_pretrained(final_dir)
    tokenizer.save_pretrained(final_dir)

    with open(os.path.join(final_dir, "label_map.json"), "w") as f:
        json.dump({"label2id": label2id, "id2label": id2label}, f, indent=2)

    print(f"Saved fine-tuned classifier to {final_dir}")


if __name__ == "__main__":
    main()

import json
import os
import time

import torch


def train_and_record_time(trainer, output_dir: str) -> dict:
    """
    Runs `trainer.train()` and writes how long it took to
    `<output_dir>/training_time.json`, so the architectures can be compared
    on training cost as well as search results.

    `train_seconds` is the wall-clock time of `trainer.train()` only -- model
    loading, tokenisation and saving the final model are excluded. It does
    include the periodic validation passes and checkpoint saves.
    """
    start = time.perf_counter()
    result = trainer.train()
    train_seconds = time.perf_counter() - start

    stats = {
        "train_seconds": round(train_seconds, 2),
        "train_hours": round(train_seconds / 3600, 4),
        "global_steps": result.global_step,
        "train_examples": len(trainer.train_dataset),
        "device": torch.cuda.get_device_name(0)
        if torch.cuda.is_available()
        else "cpu",
        **result.metrics,
    }

    os.makedirs(output_dir, exist_ok=True)
    path = os.path.join(output_dir, "training_time.json")
    with open(path, "w") as f:
        json.dump(stats, f, indent=2)

    h, rem = divmod(int(train_seconds), 3600)
    m, s = divmod(rem, 60)
    print(f"Training took {h}h {m:02d}m {s:02d}s -- wrote {path}")
    return stats

# COS700

## Project layout

- [data](data): data preparation scripts and generated data splits.
- [finetuning/scripts](finetuning/scripts): fine-tuning scripts.
- [finetuning/data](finetuning/data): fine-tuning datasets and training artifacts.
- [finetuning/output](finetuning/output): saved fine-tuned model artifacts.
- [mmverify.py](mmverify.py), [model.py](model.py), and [proof_search.py](proof_search.py): proof verification and model inference.

## Workflow

1. Extract proof steps into [finetuning/data](finetuning/data) with the data-preparation script in [data](data).
2. Split the data with [data/train_valid_test.py](data/train_valid_test.py).
3. Train with [finetuning/scripts/train_model.py](finetuning/scripts/train_model.py).
4. Run inference with [model.py](model.py) and [proof_search.py](proof_search.py).
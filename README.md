# COS700

## Project layout

- [data](data): data preparation scripts and generated data splits.
- [finetuning](finetuning): training scripts for the baseline, modular and residual models.
- [models](models): model wrappers used during search.
- [search](search): proof search and premise search evaluation.
- [utils](utils): shared formatting and substitution-matching helpers.
- [results](results): proof search outputs and the comparison notebook.

## Requirements

- Python 3.12
- [uv](https://docs.astral.sh/uv/)
- [just](https://github.com/casey/just)
- A GPU is recommended for fine-tuning and proof search.

## Workflow

All steps are run through the [justfile](justfile) from the repository root. Run `just` to list every recipe.

Recipes that take a `size` argument accept either `longest` or `shortest`, selecting the longest or shortest theorems dataset.

### 1. Install dependencies

```sh
just sync
```

### 2. Prepare the data

```sh
just data
```

This builds the theorem splits from `data/set.mm` into `data/<size>_theorems/` and then builds the residual splits into `data/residual/<size>_theorems/`. The steps can also be run individually:

```sh
just prepare_data
just prepare_residual longest
```

### 3. Fine-tune the models

```sh
just finetune
```

This trains every model on both dataset sizes. To train a single model:

| Recipe | Model | Output |
|---|---|---|
| `just finetune_baseline <size>` | Baseline | `finetuning/baseline/output/` |
| `just finetune_modular_thm <size>` | Modular theorem classifier | `finetuning/modular/output/` |
| `just finetune_modular_sub <size>` | Modular substitution generator | `finetuning/modular/output/` |
| `just finetune_residual_baseline <size>` | Residual baseline | `finetuning/residual/output/` |
| `just finetune_residual_modular_thm <size>` | Residual theorem classifier | `finetuning/residual/output/` |
| `just finetune_residual_modular_sub <size>` | Residual substitution generator | `finetuning/residual/output/` |

The base model (`Qwen/Qwen2.5-Coder-0.5B`) and maximum sequence length are set by the `base_model` and `max_length` variables at the top of the justfile and can be overridden on the command line:

```sh
just max_length=512 finetune_baseline longest
```

The modular search recipes need both the theorem and the substitution models for a size to be trained first.

### 4. Run proof search

```sh
just proof_search
```

This evaluates every model on the test split of both dataset sizes and writes proved theorems and expansion counts to `results/`. To evaluate a single model:

```sh
just proof_search_baseline <size>
just proof_search_modular <size>
just proof_search_residual_baseline <size>
just proof_search_residual_modular <size> [attempts] [temperature] [max_valid_per_goal]
```

For example, `just proof_search_residual_modular longest 3 0.8` runs three attempts per theorem at temperature 0.8.

### Run everything

```sh
just all
```

This runs data preparation, fine-tuning and proof search in order.

### Compare results

Open [results/model_comparisons.ipynb](results/model_comparisons.ipynb) to compare the theorems proved by each model.

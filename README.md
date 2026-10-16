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
| `just finetune_baseline <size> [seed]` | Baseline | `finetuning/baseline/output/` |
| `just finetune_modular_thm <size> [seed]` | Modular theorem classifier | `finetuning/modular/output/` |
| `just finetune_modular_sub <size> [seed]` | Modular substitution generator | `finetuning/modular/output/` |
| `just finetune_residual_baseline <size> [seed]` | Residual baseline | `finetuning/residual/output/` |
| `just finetune_residual_modular_thm <size> [seed]` | Residual theorem classifier | `finetuning/residual/output/` |
| `just finetune_residual_modular_sub <size> [seed]` | Residual substitution generator | `finetuning/residual/output/` |

The base model (`Qwen/Qwen2.5-Coder-0.5B`) and maximum sequence length are set by the `base_model` and `max_length` variables at the top of the justfile and can be overridden on the command line:

```sh
just max_length=512 finetune_baseline longest
```

Fine-tuning is seeded with the same `seed` justfile variable (default `0`) as proof search, or a seed can be passed explicitly, e.g. `just finetune 1` or `just finetune_baseline longest 1`. The seed is recorded in each model's `training_time.json`.

The modular search recipes need both the theorem and the substitution models for a size to be trained first.

### 4. Run proof search

```sh
just proof_search
```

This evaluates every model on the test split of both dataset sizes and writes proved theorems and expansion counts to `results/`. To evaluate a single model:

```sh
just proof_search_baseline <size> [seed]
just proof_search_modular <size> [seed]
just proof_search_residual_baseline <size> [seed]
just proof_search_residual_modular <size> [seed] [attempts] [temperature] [max_valid_per_goal]
```

For example, `just proof_search_residual_modular longest 0 3 0.8` runs three attempts per theorem at temperature 0.8 with seed 0.

Every run is seeded (default `0`, set by the `seed` variable at the top of the justfile), and the seed is part of each output file name -- `<size>_expansions_seed<seed>.csv`, `<size>_theorems_proved_seed<seed>.txt`, `<size>_tokens_seed<seed>.csv` and `<size>_stats_seed<seed>.txt` -- so runs with different seeds do not overwrite each other. The tokens CSV records, for every test theorem, the prompt tokens fed to the model(s) and the tokens generated, summed over all attempts; the stats file gives the totals and the averages per theorem and per expansion:

```sh
just proof_search 1            # every model, seed 1
just proof_search_baseline longest 2
```

### Run everything

```sh
just all
```

This runs data preparation, fine-tuning and proof search in order.

### Compare results

Open [results/model_comparisons.ipynb](results/model_comparisons.ipynb) to compare the theorems proved by each model.

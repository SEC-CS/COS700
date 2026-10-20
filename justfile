list:
  just --list

# run uv sync
sync:
  uv sync

# run data preparations
data:
  just prepare_data
  just prepare_residual longest
  just prepare_residual shortest
  just prepare_hyp longest
  just prepare_hyp shortest

# (note need set.mm)
prepare_data:
  uv run python data/prepare_data.py --mm data/set.mm --output-dir data/

# (argument is either 'longest' or 'shortest')
prepare_residual size:
  uv run python -m data.residualise \
    --split \
      data/{{size}}_theorems/train.jsonl \
      data/{{size}}_theorems/valid.jsonl \
      data/{{size}}_theorems/test.jsonl  \
    --out-dir data/residual/{{size}}_theorems

# test split restricted to theorems with hypotheses, plain and residual (run after prepare_residual)
prepare_hyp size:
  uv run python data/hypothesis_split.py \
    --split data/{{size}}_theorems/test.jsonl data/{{size}}_theorems/test_hyp.jsonl \
    --split data/residual/{{size}}_theorems/test.residual.jsonl data/residual/{{size}}_theorems/test_hyp.residual.jsonl

data_dir   := "data/"
base_model := "Qwen/Qwen2.5-Coder-0.5B"
max_length := "350"
seed       := "0"

common_args := "--base-model " + base_model + " --max-length " + max_length

# finetune all the models
finetune seed=seed:
  just finetune_baseline longest {{seed}}
  just finetune_modular_thm longest {{seed}}
  just finetune_modular_sub longest {{seed}}
  just finetune_residual_baseline longest {{seed}}
  just finetune_residual_modular_thm longest {{seed}}
  just finetune_residual_modular_sub longest {{seed}}

# (argument is either 'longest' or 'shortest')
finetune_baseline size seed=seed:
  uv run python -m finetuning.baseline.scripts.train_model \
    --train {{data_dir}}/{{size}}_theorems/train.jsonl \
    --valid {{data_dir}}/{{size}}_theorems/valid.jsonl \
    --output-dir finetuning/baseline/output/{{size}}_theorems \
    --seed {{seed}} \
    {{common_args}}

# (argument is either 'longest' or 'shortest')
finetune_modular_thm size seed=seed:
  uv run python -m finetuning.modular.scripts.train_model_thm \
    --train {{data_dir}}/{{size}}_theorems/train.jsonl \
    --valid {{data_dir}}/{{size}}_theorems/valid.jsonl \
    --output-dir finetuning/modular/output/{{size}}_theorems/modular-thm/ \
    --seed {{seed}} \
    {{common_args}}

# (argument is either 'longest' or 'shortest')
finetune_modular_sub size seed=seed:
  uv run python -m finetuning.modular.scripts.train_model_sub \
    --train {{data_dir}}/{{size}}_theorems/train.jsonl \
    --valid {{data_dir}}/{{size}}_theorems/valid.jsonl \
    --output-dir finetuning/modular/output/{{size}}_theorems/modular-sub/ \
    --mm data/set.mm \
    --mmverify data/mmverify.py \
    --seed {{seed}} \
    {{common_args}}

# (argument is either 'longest' or 'shortest')
finetune_residual_baseline size seed=seed:
  uv run python -m finetuning.residual.scripts.train_model \
    --train {{data_dir}}/residual/{{size}}_theorems/train.residual.jsonl \
    --valid {{data_dir}}/residual/{{size}}_theorems/valid.residual.jsonl \
    --mode baseline \
    --output-dir finetuning/residual/output/{{size}}_theorems/baseline/ \
    --seed {{seed}} \
    {{common_args}}

# (argument is either 'longest' or 'shortest')
finetune_residual_modular_thm size seed=seed:
  uv run python -m finetuning.residual.scripts.train_model \
    --train {{data_dir}}/residual/{{size}}_theorems/train.residual.jsonl \
    --valid {{data_dir}}/residual/{{size}}_theorems/valid.residual.jsonl \
    --mode modular-thm \
    --output-dir finetuning/residual/output/{{size}}_theorems/modular-thm/ \
    --seed {{seed}} \
    {{common_args}}

# (argument is either 'longest' or 'shortest')
finetune_residual_modular_sub size seed=seed:
  uv run python -m finetuning.residual.scripts.train_model \
    --train {{data_dir}}/residual/{{size}}_theorems/train.residual.jsonl \
    --valid {{data_dir}}/residual/{{size}}_theorems/valid.residual.jsonl \
    --mode modular-sub \
    --output-dir finetuning/residual/output/{{size}}_theorems/modular-sub/ \
    --mm data/set.mm \
    --mmverify data/mmverify.py \
    --seed {{seed}} \
    {{common_args}}

# (split is 'test' for the full test set or 'test_hyp' for only the theorems with hypotheses)
proof_search seed=seed split="test":
  just proof_search_baseline longest {{seed}} {{split}}
  just proof_search_modular longest {{seed}} {{split}}
  just proof_search_residual_baseline longest {{seed}} {{split}}
  just proof_search_residual_modular longest {{seed}} {{split}}

# all four architectures on seeds 1, 2 and 3
proof_search_seeds split="test":
  just proof_search 1 {{split}}
  just proof_search 2 {{split}}
  just proof_search 3 {{split}}

# kernel-check the proofs a search wrote (run by every proof_search_* recipe)
kernel_check proved json:
  uv run python -m search.kernel_check {{proved}} --json-output {{json}}

# (size is 'longest' or 'shortest'; split is 'test' or 'test_hyp', whose results go to a hyp/ subfolder)
proof_search_baseline size seed=seed split="test" out_dir=(if split == "test" { "." } else if split == "test_hyp" { "hyp" } else { error("split must be 'test' or 'test_hyp', not '" + split + "'") }):
  mkdir -p results/baseline/{{out_dir}}
  uv run python -m search.proof_search     --mm data/set.mm     --mmverify data/mmverify.py     --eval {{data_dir}}/{{size}}_theorems/{{split}}.jsonl     --model-module models/baseline/model.py     --model-dir finetuning/baseline/output/{{size}}_theorems/final     --expansions-output results/baseline/{{out_dir}}/{{size}}_expansions_seed{{seed}}.csv     --proved-output results/baseline/{{out_dir}}/{{size}}_theorems_proved_seed{{seed}}.txt     --stats-output results/baseline/{{out_dir}}/{{size}}_stats_seed{{seed}}.txt     --tokens-output results/baseline/{{out_dir}}/{{size}}_tokens_seed{{seed}}.csv     --seed {{seed}}     --attempts 1     --expansions 32     --max-valid-per-goal 3
  just kernel_check results/baseline/{{out_dir}}/{{size}}_theorems_proved_seed{{seed}}.txt results/baseline/{{out_dir}}/{{size}}_kernel_seed{{seed}}.json

# (size is 'longest' or 'shortest'; split is 'test' or 'test_hyp', whose results go to a hyp/ subfolder)
proof_search_modular size seed=seed split="test" out_dir=(if split == "test" { "." } else if split == "test_hyp" { "hyp" } else { error("split must be 'test' or 'test_hyp', not '" + split + "'") }):
  mkdir -p results/modular/{{out_dir}}
  uv run python -m search.proof_search     --mm data/set.mm     --mmverify data/mmverify.py     --eval {{data_dir}}/{{size}}_theorems/{{split}}.jsonl     --model-module models/modular/model.py     --model-dir finetuning/modular/output/{{size}}_theorems/     --expansions-output results/modular/{{out_dir}}/{{size}}_expansions_seed{{seed}}.csv     --proved-output results/modular/{{out_dir}}/{{size}}_theorems_proved_seed{{seed}}.txt     --stats-output results/modular/{{out_dir}}/{{size}}_stats_seed{{seed}}.txt     --tokens-output results/modular/{{out_dir}}/{{size}}_tokens_seed{{seed}}.csv     --seed {{seed}}     --attempts 1     --expansions 32     --max-valid-per-goal 3
  just kernel_check results/modular/{{out_dir}}/{{size}}_theorems_proved_seed{{seed}}.txt results/modular/{{out_dir}}/{{size}}_kernel_seed{{seed}}.json

# (size is 'longest' or 'shortest'; split is 'test' or 'test_hyp', whose results go to a hyp/ subfolder)
proof_search_residual_baseline size seed=seed split="test" out_dir=(if split == "test" { "." } else if split == "test_hyp" { "hyp" } else { error("split must be 'test' or 'test_hyp', not '" + split + "'") }):
  mkdir -p results/residual/baseline/{{out_dir}}
  uv run python -m search.proof_search     --mm data/set.mm     --mmverify data/mmverify.py     --eval data/residual/{{size}}_theorems/{{split}}.residual.jsonl     --model-module models/residual/model.py     --base-model-module models/baseline/model.py     --model-dir finetuning/residual/output/{{size}}_theorems/baseline/final     --label-table data/residual/label_table.pkl     --cap 3     --expansions-output results/residual/baseline/{{out_dir}}/{{size}}_expansions_seed{{seed}}.csv     --proved-output results/residual/baseline/{{out_dir}}/{{size}}_theorems_proved_seed{{seed}}.txt     --stats-output results/residual/baseline/{{out_dir}}/{{size}}_stats_seed{{seed}}.txt     --tokens-output results/residual/baseline/{{out_dir}}/{{size}}_tokens_seed{{seed}}.csv     --seed {{seed}}     --attempts 1     --expansions 32     --max-valid-per-goal 3
  just kernel_check results/residual/baseline/{{out_dir}}/{{size}}_theorems_proved_seed{{seed}}.txt results/residual/baseline/{{out_dir}}/{{size}}_kernel_seed{{seed}}.json

# (size is 'longest' or 'shortest'; split is 'test' or 'test_hyp', whose results go to a hyp/ subfolder)
proof_search_residual_modular size seed=seed split="test" attempts="1" temperature="1.0" max_valid_per_goal="3" out_dir=(if split == "test" { "." } else if split == "test_hyp" { "hyp" } else { error("split must be 'test' or 'test_hyp', not '" + split + "'") }):
  mkdir -p results/residual/modular/{{out_dir}}
  uv run python -m search.proof_search     --mm data/set.mm     --mmverify data/mmverify.py     --eval data/residual/{{size}}_theorems/{{split}}.residual.jsonl     --model-module models/residual/model.py     --base-model-module models/modular/model.py     --model-dir finetuning/residual/output/{{size}}_theorems/     --label-table data/residual/label_table.pkl     --cap 3     --expansions-output results/residual/modular/{{out_dir}}/{{size}}_expansions_seed{{seed}}.csv     --proved-output results/residual/modular/{{out_dir}}/{{size}}_theorems_proved_seed{{seed}}.txt     --stats-output results/residual/modular/{{out_dir}}/{{size}}_stats_seed{{seed}}.txt     --tokens-output results/residual/modular/{{out_dir}}/{{size}}_tokens_seed{{seed}}.csv     --seed {{seed}}     --attempts {{attempts}}     --expansions 32     --temperature {{temperature}}     --max-valid-per-goal {{max_valid_per_goal}}
  just kernel_check results/residual/modular/{{out_dir}}/{{size}}_theorems_proved_seed{{seed}}.txt results/residual/modular/{{out_dir}}/{{size}}_kernel_seed{{seed}}.json

all:
  just data
  just finetune
  just proof_search

official_runs:
  just sync
  just data
  just finetune 42
  just proof_search_seeds test

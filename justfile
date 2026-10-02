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

data_dir   := "data/"
base_model := "Qwen/Qwen2.5-Coder-0.5B"
max_length := "350"

common_args := "--base-model " + base_model + " --max-length " + max_length

# finetune all the models
finetune:
  just finetune_baseline longest
  just finetune_baseline shortest
  just finetune_modular_thm longest
  just finetune_modular_thm shortest
  just finetune_modular_sub longest
  just finetune_modular_sub shortest
  just finetune_residual_baseline longest
  just finetune_residual_baseline shortest
  just finetune_residual_modular_thm longest
  just finetune_residual_modular_thm shortest
  just finetune_residual_modular_sub longest
  just finetune_residual_modular_sub shortest
  

# (argument is either 'longest' or 'shortest')
finetune_baseline size:
  uv run python -m finetuning.baseline.scripts.train_model \
    --train {{data_dir}}/{{size}}_theorems/train.jsonl \
    --valid {{data_dir}}/{{size}}_theorems/valid.jsonl \
    --output-dir finetuning/baseline/output/{{size}}_theorems \
    {{common_args}}

# (argument is either 'longest' or 'shortest')
finetune_modular_thm size:
  uv run python -m finetuning.modular.scripts.train_model_thm \
    --train {{data_dir}}/{{size}}_theorems/train.jsonl \
    --valid {{data_dir}}/{{size}}_theorems/valid.jsonl \
    --output-dir finetuning/modular/output/{{size}}_theorems/modular-thm/ \
    {{common_args}}

# (argument is either 'longest' or 'shortest')
finetune_modular_sub size:
  uv run python -m finetuning.modular.scripts.train_model_sub \
    --train {{data_dir}}/{{size}}_theorems/train.jsonl \
    --valid {{data_dir}}/{{size}}_theorems/valid.jsonl \
    --output-dir finetuning/modular/output/{{size}}_theorems/modular-sub/ \
    --mm data/set.mm \
    --mmverify data/mmverify.py \
    {{common_args}}

# (argument is either 'longest' or 'shortest')
finetune_residual_baseline size:
  uv run python -m finetuning.residual.scripts.train_model \
    --train {{data_dir}}/residual/{{size}}_theorems/train.residual.jsonl \
    --valid {{data_dir}}/residual/{{size}}_theorems/valid.residual.jsonl \
    --mode baseline \
    --output-dir finetuning/residual/output/{{size}}_theorems/baseline/ \
    {{common_args}}

# (argument is either 'longest' or 'shortest')
finetune_residual_modular_thm size:
  uv run python -m finetuning.residual.scripts.train_model \
    --train {{data_dir}}/residual/{{size}}_theorems/train.residual.jsonl \
    --valid {{data_dir}}/residual/{{size}}_theorems/valid.residual.jsonl \
    --mode modular-thm \
    --output-dir finetuning/residual/output/{{size}}_theorems/modular-thm/ \
    {{common_args}}

# (argument is either 'longest' or 'shortest')
finetune_residual_modular_sub size:
  uv run python -m finetuning.residual.scripts.train_model \
    --train {{data_dir}}/residual/{{size}}_theorems/train.residual.jsonl \
    --valid {{data_dir}}/residual/{{size}}_theorems/valid.residual.jsonl \
    --mode modular-sub \
    --output-dir finetuning/residual/output/{{size}}_theorems/modular-sub/ \
    --mm data/set.mm \
    --mmverify data/mmverify.py \
    {{common_args}}

proof_search:
  just proof_search_baseline longest
  just proof_search_baseline shortest 
  just proof_search_modular longest 
  just proof_search_modular shortest 
  just proof_search_residual_baseline longest 
  just proof_search_residual_baseline shortest 
  just proof_search_residual_modular longest 
  just proof_search_residual_modular shortest 

# (size argument is either 'longest' or 'shortest')
proof_search_baseline size:
  uv run python -m search.proof_search \
    --mm data/set.mm \
    --mmverify data/mmverify.py \
    --eval {{data_dir}}/{{size}}_theorems/test.jsonl \
    --model-module models/baseline/model.py \
    --model-dir finetuning/baseline/output/{{size}}_theorems/final \
    --expansions-output results/baseline/{{size}}_expansions.csv \
    --proved-output results/baseline/{{size}}_theorems_proved.txt \
    --attempts 1 \
    --expansions 32
    
    
# (size argument is either 'longest' or 'shortest')
proof_search_modular size:
  uv run python -m search.proof_search \
    --mm data/set.mm \
    --mmverify data/mmverify.py \
    --eval {{data_dir}}/{{size}}_theorems/test.jsonl \
    --model-module models/modular/model.py \
    --model-dir finetuning/modular/output/{{size}}_theorems/ \
    --expansions-output results/modular/{{size}}_expansions.csv \
    --proved-output results/modular/{{size}}_theorems_proved.txt \
    --attempts 1 \
    --expansions 32

# (size argument is either 'longest' or 'shortest')
proof_search_residual_baseline size:
  uv run python -m search.proof_search \
    --mm data/set.mm \
    --mmverify data/mmverify.py \
    --eval data/residual/{{size}}_theorems/test.residual.jsonl \
    --model-module models/residual/model.py \
    --base-model-module models/baseline/model.py \
    --model-dir finetuning/residual/output/{{size}}_theorems/baseline/final \
    --label-table data/residual/label_table.pkl \
    --cap 8 \
    --expansions-output results/residual/baseline/{{size}}_expansions.csv \
    --proved-output results/residual/baseline/{{size}}_theorems_proved.txt \
    --attempts 1 \
    --expansions 32

# (size argument is either 'longest' or 'shortest')
proof_search_residual_modular size:
  uv run python -m search.proof_search \
    --mm data/set.mm \
    --mmverify data/mmverify.py \
    --eval data/residual/{{size}}_theorems/test.residual.jsonl \
    --model-module models/residual/model.py \
    --base-model-module models/modular/model.py \
    --model-dir finetuning/residual/output/{{size}}_theorems/ \
    --label-table data/residual/label_table.pkl \
    --cap 8 \
    --expansions-output results/residual/modular/{{size}}_expansions.csv \
    --proved-output results/residual/modular/{{size}}_theorems_proved.txt \
    --attempts 1 \
    --expansions 32

all:
  just data
  just finetune
  just proof_search

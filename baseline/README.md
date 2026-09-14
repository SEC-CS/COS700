# Commands

First extract / create the datasets by running the following from inside the `baseline/data` directory

```sh
uv run prepare_data.py --mm set.mm --output-dir datasets --verbose
```

Next, from the root of this repo we can run

```sh
uv run python -m baseline.finetuning.scripts.train_model \
  --train ./baseline/data/datasets/shortest_theorems/train.jsonl \
  --valid ./baseline/data/datasets/shortest_theorems/valid.jsonl \
  --base-model Qwen/Qwen2.5-Coder-0.5B \
  --output-dir ./baseline/finetuning/output/finetuned-prover
```

Optionally, you can add this line to the start of the command if you run out of memory on an nvidia GPU: `PYTORCH_CUDA_ALLOC_CONF=expandable_segments:True \`

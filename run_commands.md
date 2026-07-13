# Both files in same directory
```bash
python extract_proof_steps.py --mm set.mm --output proof_steps.jsonl
```

# Also produce training sequences
```bash
python extract_proof_steps.py --mm set.mm --output proof_steps.jsonl --training training.txt
```

# See per-theorem detail
```bash
python extract_proof_steps.py --mm set.mm --output proof_steps.jsonl --verbose
```

# See the first record
```bash
head -1 proof_steps.jsonl | python3 -m json.tool
```

# See how many records total
```bash
wc -l proof_steps.jsonl
```

# See file size
```bash
du -sh proof_steps.jsonl
```

# See a random record from the middle
```bash
sed -n '50000p' proof_steps.jsonl | python3 -m json.tool
```

# See the first 5 records nicely formatted
```bash
head -5 proof_steps.jsonl | while read line; do echo "$line" | python3 -m json.tool; echo "---"; done
```

# Check what theorem labels appear in the first 20 records
```bash
head -20 proof_steps.jsonl | python3 -c "
import sys, json
for line in sys.stdin:
    r = json.loads(line)
    print(r['proof_label'], '|', r['goal'][:60])
"
```

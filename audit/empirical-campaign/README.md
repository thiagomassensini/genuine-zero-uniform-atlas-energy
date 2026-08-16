# Locked empirical campaign sources

This directory contains the exact Python import closure used by the
`coercivity_56_guard1024` campaign, plus the aggregation script. The source
hashes, Python version, NumPy version, and SciPy version are locked in
[`../empirical-evidence.json`](../empirical-evidence.json). The raw commands,
environment record, and all 56 JSON/CSV/log/status result groups are stored in
[`../coercivity_56_guard1024_results.tar.gz`](../coercivity_56_guard1024_results.tar.gz).

The operator file has the local import name
`native_carry_primitive_real_operator_all_bases_fixed.py`; its bytes and
SHA-256 are identical to the pinned upstream operator source recorded in the
evidence manifest.

To inspect or replay a job without changing the locked archive:

```bash
scratch="$(mktemp -d)"
cp audit/empirical-campaign/*.py "$scratch/"
tar -xzf audit/coercivity_56_guard1024_results.tar.gz -C "$scratch"
python3.12 -m venv "$scratch/.venv"
"$scratch/.venv/bin/pip" install -r audit/empirical-campaign/requirements.txt
cd "$scratch"
cp coercivity_56_guard1024/M8192_c4.json reference-M8192-c4.json
"$scratch/.venv/bin/python" native_carry_transverse_coercivity_certificate_lab.py \
  --cameras 2,3,4,5,6,7 \
  --cutoffs 8192 \
  --windows 13.8:14.4,20.7:21.3,24.7:25.3,30.1:30.8,32.6:33.2,37.2:38.0 \
  --sigma-min 0.49 --sigma-max 0.51 --t-min 10 --t-max 40 \
  --certify 8192:4 --sigma-bins 8 --time-bins 120 \
  --maximum-cells 1000000 --minimum-sigma-radius 5e-10 \
  --minimum-time-radius 8e-10 --guard-multiplier 1024 \
  --json-out rerun-M8192-c4.json --csv-out rerun-M8192-c4.csv
```

Each archived `.cmd` file records the exact command for its job. A full replay
is expensive and float64 results need not be byte-identical across platforms.
The archive is numerical evidence, not interval arithmetic and not a Lean
proof object.

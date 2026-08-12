#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

bash scripts/static_audit.sh
lake build --wfail GenuineZeroUniformAtlasEnergy
lake build --wfail GenuineZeroUniformAtlasEnergy.Audit

audit_output="$(mktemp)"
trap 'rm -f "$audit_output"' EXIT
lake env lean GenuineZeroUniformAtlasEnergy/Audit.lean 2>&1 | tee "$audit_output"
python3 scripts/check_axiom_output.py "$audit_output"

echo "kernel audit passed"

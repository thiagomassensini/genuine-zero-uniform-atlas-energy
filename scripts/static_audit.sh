#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

lean_roots=(GenuineZeroUniformAtlasEnergy GenuineZeroUniformAtlasEnergy.lean)

if command -v rg >/dev/null 2>&1; then
  if rg -n --glob '*.lean' \
      '(^|[^A-Za-z])(sorry|admit|axiom|unsafe)([^A-Za-z]|$)' \
      "${lean_roots[@]}"; then
    echo "static audit failed: local Lean trust escape found" >&2
    exit 1
  fi

  import_stream() {
    rg -o '^import[[:space:]]+GenuineZeroUniformAtlasEnergy(\.[A-Za-z0-9_.]+)?' \
      --glob '*.lean' "${lean_roots[@]}"
  }
else
  if grep -RInE --include='*.lean' \
      '(^|[^A-Za-z])(sorry|admit|axiom|unsafe)([^A-Za-z]|$)' \
      "${lean_roots[@]}"; then
    echo "static audit failed: local Lean trust escape found" >&2
    exit 1
  fi

  import_stream() {
    grep -RhoE --include='*.lean' \
      '^import[[:space:]]+GenuineZeroUniformAtlasEnergy(\.[A-Za-z0-9_.]+)?' \
      "${lean_roots[@]}"
  }
fi

while IFS= read -r module; do
  path="${module//./\/}.lean"
  if [[ ! -f "$path" ]]; then
    echo "static audit failed: unresolved local import $module ($path)" >&2
    exit 1
  fi
done < <(
  import_stream \
    | awk '{print $2}' \
    | sort -u
)

python3 -m json.tool .zenodo.json >/dev/null
python3 -m json.tool audit/theorem-registry.json >/dev/null
python3 -m json.tool audit/theorem-registry-0.7.0.json >/dev/null
python3 -m json.tool audit/claim-ledger.json >/dev/null
python3 -m json.tool audit/empirical-evidence.json >/dev/null
python3 scripts/check_empirical_evidence.py
python3 scripts/check_registry.py

python3 scripts/check_github_markdown.py

bash -n scripts/audit.sh scripts/static_audit.sh

echo "static audit passed: sources, registry, claims, evidence, metadata, and Markdown"

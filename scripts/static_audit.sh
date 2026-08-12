#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

if rg -n --glob '*.lean' \
    '(^|[^A-Za-z])(sorry|admit|axiom|unsafe)([^A-Za-z]|$)' \
    GenuineZeroUniformAtlasEnergy GenuineZeroUniformAtlasEnergy.lean; then
  echo "static audit failed: local Lean trust escape found" >&2
  exit 1
fi

while IFS= read -r module; do
  path="${module//./\/}.lean"
  if [[ ! -f "$path" ]]; then
    echo "static audit failed: unresolved local import $module ($path)" >&2
    exit 1
  fi
done < <(
  rg -o '^import[[:space:]]+GenuineZeroUniformAtlasEnergy(\.[A-Za-z0-9_.]+)?' \
    --glob '*.lean' GenuineZeroUniformAtlasEnergy GenuineZeroUniformAtlasEnergy.lean \
    | awk '{print $2}' \
    | sort -u
)

python3 -m json.tool .zenodo.json >/dev/null
python3 -m json.tool audit/theorem-registry.json >/dev/null
python3 -m json.tool audit/claim-ledger.json >/dev/null
python3 scripts/check_registry.py

python3 scripts/check_github_markdown.py

bash -n scripts/audit.sh scripts/static_audit.sh

echo "static audit passed: sources, registry, claims, metadata, and Markdown"

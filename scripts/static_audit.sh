#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

lean_roots=(GenuineZeroUniformAtlasEnergy GenuineZeroUniformAtlasEnergy.lean)

# Empirical campaign files are retained as reproducibility provenance only.
# The kernel build, registry, release metadata, and publication audit do not
# depend on a floating-point witness or on the 56-job campaign archive.

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

if grep -RInE --include='*.lean' \
    'IsNativeCarryRealOperatorZero|NativeZero|IsGenuineZero|= 0 →|→ .* = 0' \
    GenuineZeroUniformAtlasEnergy/NativeGeometry.lean; then
  echo "NativeGeometry.lean contains a forbidden zero-level premise" >&2
  exit 1
fi

python3 -m json.tool .zenodo.json >/dev/null
python3 -m json.tool audit/theorem-registry.json >/dev/null
python3 -m json.tool audit/theorem-registry-0.7.0.json >/dev/null
python3 -m json.tool audit/theorem-registry-0.8.0.json >/dev/null
python3 -m json.tool audit/claim-ledger.json >/dev/null
python3 -m json.tool lake-manifest.json >/dev/null
python3 scripts/check_registry.py
python3 scripts/check_github_markdown.py

bash -n scripts/audit.sh scripts/static_audit.sh

test -s docs/RELEASE_0.8.0.md
test -s audit/THEOREM_REGISTRY.md
test -s audit/CLAIM_LEDGER.md

echo "static audit passed: kernel sources, registry, claims, metadata, and Markdown"

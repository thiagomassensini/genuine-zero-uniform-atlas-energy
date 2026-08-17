#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

# Empirical campaign files are retained as reproducibility provenance only.
# The kernel build, registry, release metadata, and publication audit do not
# depend on a floating-point witness or on the 56-job campaign archive.

if grep -RInE --include='*.lean' --include='*.py' --include='*.sh' \
  '(^|[^[:alnum:]_])(sorry|admit|axiom)([^[:alnum:]_]|$)|unsafe|False\.elim|Classical\.choice' \
  GenuineZeroUniformAtlasEnergy scripts; then
  echo "forbidden source construct found"
  exit 1
fi

if grep -RInE --include='*.lean' \
  'IsNativeCarryRealOperatorZero|NativeZero|IsGenuineZero|= 0 →|→ .* = 0' \
  GenuineZeroUniformAtlasEnergy/NativeGeometry.lean; then
  echo "NativeGeometry.lean contains a forbidden zero-level premise"
  exit 1
fi

python3 scripts/check_registry.py
python3 scripts/check_github_markdown.py

python3 - <<'PY'
import json
from pathlib import Path

for path in [
    Path('audit/theorem-registry.json'),
    Path('audit/theorem-registry-0.7.0.json'),
    Path('audit/theorem-registry-0.8.0.json'),
    Path('audit/claim-ledger.json'),
    Path('.zenodo.json'),
    Path('lake-manifest.json'),
]:
    json.loads(path.read_text())
PY

for path in GenuineZeroUniformAtlasEnergy/*.lean; do
  test -s "$path"
done

test -s GenuineZeroUniformAtlasEnergy.lean
test -s README.md
test -s docs/FORMALIZATION_SCOPE.md
test -s docs/THEOREM_MAP.md
test -s docs/SOURCE_PROVENANCE.md
test -s docs/CONCEPTUAL_AUDIT.md
test -s docs/LOWER_BOUND_STATUS.md
test -s docs/RELEASE_0.8.0.md
test -s audit/THEOREM_REGISTRY.md
test -s audit/CLAIM_LEDGER.md

echo "static audit passed: kernel sources, registry, claims, metadata, and Markdown"

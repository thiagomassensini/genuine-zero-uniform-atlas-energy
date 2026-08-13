#!/usr/bin/env python3
"""Cross-check local theorems, audit order, claims, versions, and source lock."""

from __future__ import annotations

import json
import re
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
MODULES = [
    ROOT / "GenuineZeroUniformAtlasEnergy/NativeGeometry.lean",
    ROOT / "GenuineZeroUniformAtlasEnergy/Budget.lean",
    ROOT / "GenuineZeroUniformAtlasEnergy/TiltedCenter.lean",
    ROOT / "GenuineZeroUniformAtlasEnergy/Capstone.lean",
]
PREFIX = "GenuineZeroUniformAtlasEnergy."
EXPECTED_CPFORMAL_REV = "537028681ae6a775c083a1e2fb6e67db24697b82"
EXPECTED_MATHLIB_REV = "81a5d257c8e410db227a6665ed08f64fea08e997"


def fail(message: str) -> None:
    raise SystemExit(f"registry check failed: {message}")


registry = json.loads((ROOT / "audit/theorem-registry.json").read_text())
entries = registry["theorems"]
if registry["count"] != len(entries):
    fail("declared theorem count differs from registry length")

expected_ids = [f"GZUAE-{index:03d}" for index in range(1, len(entries) + 1)]
ids = [entry["id"] for entry in entries]
qualified = [entry["qualified"] for entry in entries]
if ids != expected_ids:
    fail("theorem IDs are not contiguous and ordered")
if len(set(qualified)) != len(qualified):
    fail("qualified theorem names are not unique")

source_names: list[str] = []
for module in MODULES:
    text = module.read_text()
    names = re.findall(
        r"^(?:@\[[^\n]*\]\s*)?theorem\s+([A-Za-z0-9_']+)",
        text,
        re.MULTILINE,
    )
    source_names.extend(PREFIX + name for name in names)
if source_names != qualified:
    fail("registry order or content differs from local theorem declarations")

audit_text = (ROOT / "GenuineZeroUniformAtlasEnergy/Audit.lean").read_text()
audit_names = re.findall(r"^#print axioms\s+(\S+)\s*$", audit_text, re.MULTILINE)
if audit_names != qualified:
    fail("Audit.lean order or content differs from theorem registry")

ledger = json.loads((ROOT / "audit/claim-ledger.json").read_text())
if ledger["registry_count"] != len(entries):
    fail("claim ledger registry_count is stale")
claims = ledger["claims"]
if ledger["count"] != len(claims):
    fail("declared claim count differs from ledger length")
actual_statuses = Counter(claim["status"] for claim in claims)
if dict(actual_statuses) != ledger["status_counts"]:
    fail("claim status_counts is stale")

known_ids = set(ids)
used_ids: set[str] = set()
for claim in claims:
    theorem_ids = claim.get("theorem_ids", [])
    unknown = set(theorem_ids) - known_ids
    if unknown:
        fail(f"claim {claim['id']} cites unknown IDs: {sorted(unknown)}")
    used_ids.update(theorem_ids)
if used_ids != known_ids:
    fail(f"claim coverage differs from registry: {sorted(known_ids ^ used_ids)}")

manifest = json.loads((ROOT / "lake-manifest.json").read_text())
packages = {package["name"]: package for package in manifest["packages"]}
if packages["CPFormal"]["rev"] != EXPECTED_CPFORMAL_REV:
    fail("CPFormal manifest revision differs from the audited source lock")
if packages["mathlib"]["rev"] != EXPECTED_MATHLIB_REV:
    fail("Mathlib manifest revision differs from the audited source lock")

lakefile = (ROOT / "lakefile.toml").read_text()
version_match = re.search(r'^version\s*=\s*"([^"]+)"', lakefile, re.MULTILINE)
if version_match is None:
    fail("lakefile version is missing")
version = version_match.group(1)
if registry["release"] != version or ledger["release"] != version:
    fail("audit release versions differ from lakefile.toml")

zenodo = json.loads((ROOT / ".zenodo.json").read_text())
if zenodo["version"] != version:
    fail("Zenodo version differs from lakefile.toml")
citation = (ROOT / "CITATION.cff").read_text()
if not re.search(rf"^version:\s*{re.escape(version)}\s*$", citation, re.MULTILINE):
    fail("CITATION.cff version differs from lakefile.toml")

print(
    f"registry check passed: {len(entries)} theorems, "
    f"{len(claims)} claims, exact dependency lock"
)

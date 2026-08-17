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
    ROOT / "GenuineZeroUniformAtlasEnergy/TransverseCapstone.lean",
    ROOT / "GenuineZeroUniformAtlasEnergy/NativeTransverseBridge.lean",
    ROOT / "GenuineZeroUniformAtlasEnergy/NativeTransverseHessian.lean",
    ROOT / "GenuineZeroUniformAtlasEnergy/NativeCutoffTail.lean",
    ROOT / "GenuineZeroUniformAtlasEnergy/EmpiricalCameraGeometry.lean",
    ROOT / "GenuineZeroUniformAtlasEnergy/EmpiricalCameraOperator.lean",
    ROOT / "GenuineZeroUniformAtlasEnergy/NativeCutoffAsymptotic.lean",
    ROOT / "GenuineZeroUniformAtlasEnergy/AsymptoticCoercivity.lean",
    ROOT / "GenuineZeroUniformAtlasEnergy/EmpiricalStackProjection.lean",
    ROOT / "GenuineZeroUniformAtlasEnergy/EmpiricalFullEvenContinuation.lean",
    ROOT / "GenuineZeroUniformAtlasEnergy/UniformCoercivityOn.lean",
    ROOT / "GenuineZeroUniformAtlasEnergy/NativeCutoffGlobalRemainder.lean",
    ROOT / "GenuineZeroUniformAtlasEnergy/EmpiricalCollectiveEnergyAsymptotic.lean",
    ROOT / "GenuineZeroUniformAtlasEnergy/NativeCutoffLogJet.lean",
    ROOT / "GenuineZeroUniformAtlasEnergy/NativeCutoffDifferentiatedRemainder.lean",
]
EXPECTED_CPFORMAL_REV = "537028681ae6a775c083a1e2fb6e67db24697b82"
EXPECTED_MATHLIB_REV = "81a5d257c8e410db227a6665ed08f64fea08e997"


def fail(message: str) -> None:
    raise SystemExit(f"registry check failed: {message}")


def qualified_theorems(path: Path) -> list[str]:
    """Collect theorem names while respecting Lean namespace nesting.

    The registry includes declarations from nested namespaces such as
    `EmpiricalCamera` and `PhaseProjectionData`. Anonymous and named
    `section` blocks affect scoping but do not contribute name components, so
    both kinds of scope are tracked explicitly until their matching `end`.
    """

    scopes: list[tuple[str, str | None]] = []
    names: list[str] = []
    theorem_pattern = re.compile(
        r"^(?:@\[[^\n]*\]\s*)?theorem\s+([A-Za-z0-9_.']+)"
    )
    namespace_pattern = re.compile(r"^namespace\s+([A-Za-z0-9_.']+)\s*$")
    section_pattern = re.compile(
        r"^(?:noncomputable\s+)?section(?:\s+([A-Za-z0-9_']+))?\s*$"
    )
    end_pattern = re.compile(r"^end(?:\s+([A-Za-z0-9_.']+))?\s*$")

    for raw_line in path.read_text().splitlines():
        line = raw_line.strip()
        namespace_match = namespace_pattern.match(line)
        if namespace_match is not None:
            scopes.append(("namespace", namespace_match.group(1)))
            continue
        section_match = section_pattern.match(line)
        if section_match is not None:
            scopes.append(("section", section_match.group(1)))
            continue
        end_match = end_pattern.match(line)
        if end_match is not None:
            if not scopes:
                fail(f"unmatched end in {path.relative_to(ROOT)}")
            closing_name = end_match.group(1)
            scope_kind, scope_name = scopes.pop()
            if closing_name is not None and closing_name != scope_name:
                fail(
                    f"scope mismatch in {path.relative_to(ROOT)}: "
                    f"end {closing_name} closes {scope_kind} {scope_name}"
                )
            continue
        theorem_match = theorem_pattern.match(line)
        if theorem_match is None:
            continue
        namespace = ".".join(
            scope_name
            for scope_kind, scope_name in scopes
            if scope_kind == "namespace" and scope_name is not None
        )
        theorem_name = theorem_match.group(1)
        names.append(f"{namespace}.{theorem_name}" if namespace else theorem_name)

    if scopes:
        fail(f"unclosed scope in {path.relative_to(ROOT)}")
    return names


base_registry = json.loads((ROOT / "audit/theorem-registry.json").read_text())
base_entries = base_registry["theorems"]
if base_registry["count"] != len(base_entries):
    fail("declared base theorem count differs from registry length")

extension_path = ROOT / "audit/theorem-registry-0.9.0.json"
extension = json.loads(extension_path.read_text())
extension_entries = extension["theorems"]
if extension["count"] != len(extension_entries):
    fail("declared extension theorem count differs from extension length")
if extension["base_release"] != base_registry["release"]:
    fail("registry extension does not name the locked base release")
if extension["start"] != len(base_entries) + 1:
    fail("registry extension does not start after the locked base registry")

entries = base_entries + extension_entries
expected_ids = [f"GZUAE-{index:03d}" for index in range(1, len(entries) + 1)]
ids = [entry["id"] for entry in entries]
qualified = [entry["qualified"] for entry in entries]
if ids != expected_ids:
    fail("theorem IDs are not contiguous and ordered")
if len(set(qualified)) != len(qualified):
    fail("qualified theorem names are not unique")

source_names: list[str] = []
for module in MODULES:
    source_names.extend(qualified_theorems(module))
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
if extension["release"] != version or ledger["release"] != version:
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

#!/usr/bin/env python3
"""Validate one Lean dependency report per registered theorem."""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def fail(message: str) -> None:
    raise SystemExit(f"foundational dependency check failed: {message}")


if len(sys.argv) != 2:
    fail("usage: check_axiom_output.py AXIOM_OUTPUT")

output = Path(sys.argv[1]).read_text()
base_registry = json.loads((ROOT / "audit/theorem-registry.json").read_text())
extension = json.loads(
    (ROOT / "audit/theorem-registry-0.11.0.json").read_text()
)
expected = [
    entry["qualified"]
    for entry in base_registry["theorems"] + extension["theorems"]
]

pattern = re.compile(
    r"'([^']+)' (does not depend on any axioms|depends on axioms: \[(.*?)\])",
    re.DOTALL,
)
matches = list(pattern.finditer(output))
names = [match.group(1) for match in matches]
if names != expected:
    fail("output declarations differ from the ordered combined theorem registry")

for match in matches:
    raw = match.group(3)
    dependencies = set() if raw is None else {
        item.strip()
        for item in raw.replace("\n", " ").split(",")
        if item.strip()
    }
    unexpected = dependencies - ALLOWED
    if unexpected:
        fail(
            f"{match.group(1)} uses non-allowlisted dependencies: "
            f"{sorted(unexpected)}"
        )

print(f"foundational dependency check passed: {len(matches)} theorem reports")

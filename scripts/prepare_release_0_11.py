#!/usr/bin/env python3
"""Prepare the audited v0.11.0 concrete limit/confinement release."""

from __future__ import annotations

import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
VERSION = "0.11.0"
NEW_THEOREMS = [
    ("GZUAE-149", "empiricalPlaneParameter_re",
     "GenuineZeroUniformAtlasEnergy.empiricalPlaneParameter_re"),
    ("GZUAE-150", "empiricalPlaneParameter_im",
     "GenuineZeroUniformAtlasEnergy.empiricalPlaneParameter_im"),
    ("GZUAE-151", "finiteEmpiricalCollectiveRawEnergyPlane_tendsto",
     "GenuineZeroUniformAtlasEnergy.finiteEmpiricalCollectiveRawEnergyPlane_tendsto"),
    ("GZUAE-152", "empiricalCollectiveRawEnergy_eq_zero_of_genuine_zero",
     "GenuineZeroUniformAtlasEnergy.empiricalCollectiveRawEnergy_eq_zero_of_genuine_zero"),
    ("GZUAE-153", "empiricalCollectiveRawEnergyPlane_eq_zero_of_genuine_zero",
     "GenuineZeroUniformAtlasEnergy.empiricalCollectiveRawEnergyPlane_eq_zero_of_genuine_zero"),
    ("GZUAE-154", "genuineZero_in_region_forces_re_eq_half_of_eventual_empiricalCoercivity",
     "GenuineZeroUniformAtlasEnergy.genuineZero_in_region_forces_re_eq_half_of_eventual_empiricalCoercivity"),
    ("GZUAE-155", "genuineZero_forces_re_eq_half_of_eventual_empiricalStripCoercivity",
     "GenuineZeroUniformAtlasEnergy.genuineZero_forces_re_eq_half_of_eventual_empiricalStripCoercivity"),
    ("GZUAE-156", "genuineZero_forces_re_eq_half_of_eventual_globalEmpiricalCoercivity",
     "GenuineZeroUniformAtlasEnergy.genuineZero_forces_re_eq_half_of_eventual_globalEmpiricalCoercivity"),
]


def read(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def write(path: str, content: str) -> None:
    target = ROOT / path
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(content, encoding="utf-8")


def replace_once(text: str, old: str, new: str, label: str) -> str:
    if old not in text:
        raise SystemExit(f"missing marker for {label}: {old!r}")
    return text.replace(old, new, 1)


# 1. Cumulative theorem extension.
ext = json.loads(read("audit/theorem-registry-0.10.0.json"))
ext["release"] = VERSION
for theorem_id, name, qualified in NEW_THEOREMS:
    ext["theorems"].append({
        "id": theorem_id,
        "name": name,
        "qualified": qualified,
    })
ext["count"] = len(ext["theorems"])
write("audit/theorem-registry-0.11.0.json", json.dumps(ext, indent=2) + "\n")

# 2. Claim ledger.
ledger = json.loads(read("audit/claim-ledger.json"))
ledger["release"] = VERSION
ledger["registry_count"] = 156
ledger["count"] = 24
ledger["status_counts"] = {"KERNEL_CHECKED": 24}
ledger["claims"].append({
    "id": "GZUAE-CON-001",
    "claim": (
        "The faithful finite C2--C7 collective raw energy converges pointwise "
        "to the concrete infinite empirical energy throughout sigma > -1; a "
        "Genuine zero in the critical strip annihilates that limiting energy; "
        "and any supplied eventual positive finite regional, strip-wide, or "
        "global coercivity certificate therefore confines the zero to sigma "
        "equals one-half. The theorem discharges the concrete limit and "
        "zero-to-energy hypotheses but does not prove the eventual finite "
        "coercivity certificate itself."
    ),
    "status": "KERNEL_CHECKED",
    "theorem_ids": [item[0] for item in NEW_THEOREMS],
})
write("audit/claim-ledger.json", json.dumps(ledger, indent=2) + "\n")

# 3. Ordered axiom audit.
audit_path = "GenuineZeroUniformAtlasEnergy/Audit.lean"
audit = read(audit_path).rstrip() + "\n"
for _theorem_id, _name, qualified in NEW_THEOREMS:
    line = f"#print axioms {qualified}\n"
    if line not in audit:
        audit += line
write(audit_path, audit)

# 4. Registry checker and axiom checker.
check_registry_path = "scripts/check_registry.py"
check_registry = read(check_registry_path)
module_marker = (
    '    ROOT / "GenuineZeroUniformAtlasEnergy/NativeCutoffExactScaledTailCauchy.lean",\n'
)
module_insert = module_marker + (
    '    ROOT / "GenuineZeroUniformAtlasEnergy/EmpiricalLimitConfinement.lean",\n'
)
if "EmpiricalLimitConfinement.lean" not in check_registry:
    check_registry = replace_once(
        check_registry, module_marker, module_insert, "registry module list"
    )
check_registry = check_registry.replace(
    'extension_path = ROOT / "audit/theorem-registry-0.10.0.json"',
    'extension_path = ROOT / "audit/theorem-registry-0.11.0.json"',
)
write(check_registry_path, check_registry)

axiom_path = "scripts/check_axiom_output.py"
axiom = read(axiom_path).replace(
    'audit/theorem-registry-0.10.0.json',
    'audit/theorem-registry-0.11.0.json',
)
write(axiom_path, axiom)

# 5. Static audit: retain historical registry and add the new one.
static_path = "scripts/static_audit.sh"
static = read(static_path)
if "theorem-registry-0.11.0.json" not in static:
    static = replace_once(
        static,
        "python3 -m json.tool audit/theorem-registry-0.10.0.json >/dev/null\n",
        "python3 -m json.tool audit/theorem-registry-0.10.0.json >/dev/null\n"
        "python3 -m json.tool audit/theorem-registry-0.11.0.json >/dev/null\n",
        "static audit registry",
    )
static = replace_once(
    static,
    "test -s docs/RELEASE_0.10.0.md\n",
    "test -s docs/RELEASE_0.10.0.md\n"
    "test -s docs/RELEASE_0.11.0.md\n",
    "static audit release notes",
)
write(static_path, static)

# 6. Version and publication metadata.
lakefile = read("lakefile.toml").replace('version = "0.10.0"', 'version = "0.11.0"')
write("lakefile.toml", lakefile)

citation = read("CITATION.cff")
citation = citation.replace("version: 0.10.0", "version: 0.11.0")
old_abstract = """abstract: >-\n  A Lean 4 formalization of the exact identity between the native real-camera\n  and Genuine zero, the sharp critical cutoff-tail and collective raw-energy\n  expansions, and exact logarithmic first and second cutoff jets. Version\n  0.10.0 proves holomorphy of the exact scaled explicit-radius tail on a\n  critical neighborhood, a uniform Cauchy-circle majorant, and explicit\n  O(1/M) bounds for its value, first complex derivative, and second complex\n  derivative. Together with the 0.9.0 transport theorem, these estimates close\n  the analytic differentiated-remainder input without numerical premises.\n  Empirical cutoff-doubling campaigns remain discovery provenance rather than\n  kernel assumptions.\n"""
new_abstract = """abstract: >-\n  A Lean 4 formalization of the native real-camera/Genuine zero identity, the\n  faithful C2--C7 cutoff operator, sharp critical cutoff-tail and raw-energy\n  asymptotics, and exact logarithmic cutoff jets. Version 0.11.0 proves that\n  the concrete finite six-camera raw energy converges pointwise to its infinite\n  empirical energy, proves that a Genuine zero annihilates that limit energy,\n  and packages regional, strip-wide, and global confinement consequences from\n  an eventual positive finite coercivity certificate. The certificate itself\n  remains a separate quantitative hypothesis; floating-point evidence is not\n  imported into the kernel.\n"""
citation = replace_once(citation, old_abstract, new_abstract, "citation abstract")
if "  - pointwise energy limit\n" not in citation:
    citation = citation.replace(
        "  - collective energy asymptotic\n",
        "  - collective energy asymptotic\n  - pointwise energy limit\n  - conditional confinement capstone\n",
    )
write("CITATION.cff", citation)

zenodo = json.loads(read(".zenodo.json"))
zenodo["version"] = VERSION
zenodo["description"] = (
    "Lean 4 formalization of the native real-camera/Genuine zero identity, "
    "faithful empirical C2--C7 camera geometry, sharp cutoff-tail and "
    "collective raw-energy asymptotics, logarithmic cutoff jets, and exact "
    "scaled-tail value/derivative bounds. Version 0.11.0 proves the concrete "
    "pointwise convergence of the finite six-camera raw energy to its infinite "
    "empirical energy, proves that Genuine vanishing annihilates the limit "
    "energy, and derives regional, strip-wide, and global confinement "
    "capstones from an eventual positive finite coercivity certificate. The "
    "finite coercivity certificate remains an explicit hypothesis; empirical "
    "cutoff campaigns remain discovery and reproducibility provenance only."
)
for keyword in ["pointwise energy limit", "conditional confinement capstone"]:
    if keyword not in zenodo["keywords"]:
        zenodo["keywords"].append(keyword)
write(".zenodo.json", json.dumps(zenodo, indent=2) + "\n")

release_workflow_path = ".github/workflows/release.yml"
release_workflow = read(release_workflow_path).replace(
    '--title "$TAG — Exact scaled-tail analytic bounds"',
    '--title "$TAG — Concrete empirical limit and confinement bridge"',
)
write(release_workflow_path, release_workflow)

# 7. Restore the authoritative audit workflow, removing temporary diagnostics.
write(".github/workflows/lean-audit.yml", """name: Lean theorem audit

on:
  pull_request:
  push:
    branches:
      - main
  workflow_dispatch:

permissions:
  contents: read

env:
  AUDITED_SHA: ${{ github.event.pull_request.head.sha || github.sha }}

concurrency:
  group: genuine-zero-atlas-energy-${{ github.event_name }}-${{ github.event.pull_request.number || github.sha }}
  cancel-in-progress: ${{ github.event_name == 'pull_request' }}

jobs:
  audit:
    name: Exact-checkout Lean theorem audit
    runs-on: ubuntu-24.04
    timeout-minutes: 90

    steps:
      - name: Check out the exact audited commit
        uses: actions/checkout@11d5960a326750d5838078e36cf38b85af677262 # v4.4.0
        with:
          ref: ${{ env.AUDITED_SHA }}
          fetch-depth: 0
          persist-credentials: false

      - name: Reject a synthetic or dirty checkout
        shell: bash
        run: |
          set -euo pipefail
          test "$(git rev-parse HEAD)" = "$AUDITED_SHA"
          test -z "$(git status --porcelain --untracked-files=all)"

      - name: Run static source and publication audit
        run: bash scripts/static_audit.sh

      - name: Set up pinned Lean and Mathlib cache
        uses: leanprover/lean-action@38fbc41a8c28c4cbaec22d7f7de508ec2e7c0dd9 # v1.5.0
        with:
          build: false
          test: false
          lint: false
          use-github-cache: true
          use-mathlib-cache: true

      - name: Build public library with warnings as errors
        run: lake build --wfail GenuineZeroUniformAtlasEnergy

      - name: Build ordered kernel dependency audit
        run: lake build --wfail GenuineZeroUniformAtlasEnergy.Audit

      - name: Check foundational dependency allowlist
        shell: bash
        run: |
          set -euo pipefail
          lake env lean GenuineZeroUniformAtlasEnergy/Audit.lean 2>&1 \\
            | tee /tmp/genuine-zero-uniform-atlas-energy-axioms.txt
          python3 scripts/check_axiom_output.py \\
            /tmp/genuine-zero-uniform-atlas-energy-axioms.txt
""")

# 8. Release notes.
write("docs/RELEASE_0.11.0.md", """# v0.11.0 — Concrete empirical limit and confinement bridge

Version `0.11.0` closes the concrete pointwise-limit side of the confinement
pipeline for the faithful empirical C2--C7 operator.

## Concrete infinite energy

The release defines the infinite collective raw energy

```math
E_\infty(s)=\sum_{b=2}^{7}\left|\Chi_b(s)\right|^2
```

and its real-plane form at `s=sigma+i*time`. Absolute summability of every
empirical block series now gives the actual pointwise convergence

```math
E_M(\sigma,t)\longrightarrow E_\infty(\sigma,t)
```

throughout `sigma > -1`. The limit is no longer an abstract supplied function.

## Genuine zero to limit-energy zero

On the Genuine critical strip, each faithful camera characteristic is its
limiting camera factor times `genuineContinuation`. Therefore

```math
\mathrm{Genuine}(s)=0
\Longrightarrow
\forall b,\;\Chi_b(s)=0
\Longrightarrow
E_\infty(s)=0.
```

This implication requires no nonvanishing statement about the camera factors.

## Concrete confinement capstones

Combining the concrete pointwise limit with the previously proved regional
limit-passage theorem gives three public capstones:

- an arbitrary-region theorem;
- a theorem on the real-plane Genuine strip;
- a global-finite-coercivity specialization.

Each says that an eventual positive finite coercivity certificate implies
that every Genuine zero in the certified region has

```math
\operatorname{Re}(s)=\frac12.
```

The pointwise convergence and zero-to-energy bridge are discharged by Lean;
only the eventual finite coercivity certificate remains a quantitative input.

## Formal surface

Version `0.11.0` contains:

- 156 ordered public theorem reports;
- 24 claims marked `KERNEL_CHECKED`;
- exact CPFormal and Mathlib source locks;
- GitHub-Actions-only public build, ordered `#print axioms` audit, and
  foundational dependency allowlist.

## Deliberate boundary

This release does **not** prove the eventual finite coercivity hypothesis.
In particular it does not yet identify the concrete moving minimizer, prove a
numerical phase floor greater than four, or certify the compact complement
between zero valleys. The release closes the concrete limit and final logical
implication so that the remaining frontier is one finite, cutoff-uniform lower
bound rather than an unspecified passage-to-limit gap.

The float64 and high-precision cutoff campaigns remain discovery and
reproducibility provenance only; no numerical witness is a Lean premise.
""")

# 9. Human-readable audit summaries.
claim_md_path = "audit/CLAIM_LEDGER.md"
claim_md = read(claim_md_path)
new_claim_row = (
    "| `GZUAE-CON-001` | `KERNEL_CHECKED` | Concrete finite C2--C7 raw energy "
    "converges pointwise to the infinite empirical energy; Genuine vanishing "
    "annihilates that limit; supplied eventual positive finite regional or "
    "global coercivity therefore confines the zero to `sigma = 1/2`. The "
    "finite coercivity premise remains explicit. |\n"
)
if "GZUAE-CON-001" not in claim_md:
    marker = "\nRelease `0.10.0` records 23 claims covering 148 ordered theorem reports."
    claim_md = replace_once(claim_md, marker, "\n" + new_claim_row + marker,
                            "claim ledger row")
claim_md = claim_md.replace(
    "Release `0.10.0` records 23 claims covering 148 ordered theorem reports.",
    "Release `0.11.0` records 24 claims covering 156 ordered theorem reports.",
)
claim_md = claim_md.replace(
    "Both the algebraic differentiated-remainder transport and the\nthree analytic exact-tail inputs are now closed.\n\nThe concrete reoptimized microscopic coefficient, the moving finite minimizer,\nand a cutoff-uniform global coercivity constant remain outside this release.",
    "The exact-tail, differentiated-remainder, concrete pointwise-energy limit,\nand final conditional confinement bridges are now closed.\n\nThe concrete reoptimized microscopic coefficient, the moving finite minimizer,\nand an eventual cutoff-uniform finite coercivity certificate remain outside\nthis release.",
)
write(claim_md_path, claim_md)

write("audit/THEOREM_REGISTRY.md", """# Theorem Registry

Release `0.11.0` contains 156 ordered public theorem reports. The locked
`0.6.0` base surface remains in
[`theorem-registry.json`](theorem-registry.json). The current cumulative
extension is
[`theorem-registry-0.11.0.json`](theorem-registry-0.11.0.json); the historical
`0.7.0` through `0.10.0` extensions are retained for provenance and are not
renumbered.

The combined registry is checked against declarations in every public module,
including `NativeCutoffExactScaledTailCauchy.lean` and the new
`EmpiricalLimitConfinement.lean`; against the ordered `#print axioms` commands
in `Audit.lean`; and against complete claim-ledger coverage.

The `0.11.0` cumulative extension retains the thirteen post-`0.6.0` cutoff and
jet reports through `0.10.0` and adds eight concrete limit/confinement reports:
real-plane parameter coordinates, pointwise finite-energy convergence, the
Genuine-zero limit-energy identity, and regional, strip-wide, and global
conditional confinement capstones.

The empirical cutoff campaigns remain discovery and reproducibility
provenance only. The concrete pointwise-limit gap is closed; the remaining
frontier is the eventual positive finite coercivity certificate, including the
moving minimizer and compact-complement estimates.
""")

# 10. Mathematical documentation.
readme_path = "README.md"
readme = read(readme_path)
section = """## Concrete pointwise limit and confinement bridge

The faithful finite C2--C7 energy now has a concrete infinite counterpart

```math
E_\infty(\sigma,t)
=\sum_{b=2}^{7}\left|\Chi_b(\sigma+i t)\right|^2.
```

Lean proves directly from absolute summability that

```math
E_M(\sigma,t)\longrightarrow E_\infty(\sigma,t)
```

for every `sigma > -1`. On the Genuine critical strip, a Genuine zero makes
every faithful limiting camera vanish and hence gives `E_infinity = 0`.
Consequently, if a positive finite transverse coercivity certificate holds
eventually on a region, the limiting energy inherits it and every Genuine zero
inside that region satisfies

```math
\boxed{\operatorname{Re}(s)=\frac12.}
```

This closes the concrete limit and final logical implication. The eventual
finite coercivity certificate itself remains the quantitative frontier; it is
not inferred from the float64 campaign.

"""
if "## Concrete pointwise limit and confinement bridge" not in readme:
    readme = replace_once(readme, "## Consolidation theorem\n",
                          section + "## Consolidation theorem\n",
                          "README limit section")
readme = readme.replace(
    "`UniformCoercivityOn.lean`: region-restricted implication and limit-passage\n  interfaces, applicable in particular to a compact region;\n",
    "`UniformCoercivityOn.lean`: region-restricted implication and abstract\n  limit-passage interfaces;\n- `EmpiricalLimitConfinement.lean`: concrete pointwise C2--C7 energy limit,\n  Genuine-zero limit-energy identity, and conditional regional/global\n  confinement capstones;\n",
)
readme = readme.replace(
    "[the v0.6.0 release\nnotes](docs/RELEASE_0.6.0.md)",
    "[the v0.11.0 release\nnotes](docs/RELEASE_0.11.0.md)",
)
write(readme_path, readme)

lower_path = "docs/LOWER_BOUND_STATUS.md"
lower = read(lower_path)
insert_marker = (
    "- passage of an eventual cutoff-uniform coercivity inequality to a pointwise\n"
    "  limiting energy, globally or on a fixed region.\n"
)
insert_text = insert_marker + (
    "- the faithful finite C2--C7 collective raw energy converges pointwise to\n"
    "  the concrete infinite empirical energy throughout `sigma > -1`;\n"
    "- a Genuine zero in the strip annihilates that concrete limiting energy;\n"
    "- regional, strip-wide, and global capstones now combine those concrete\n"
    "  facts with a supplied eventual positive finite coercivity certificate to\n"
    "  force `sigma = 1/2`.\n"
)
if "faithful finite C2--C7 collective raw energy converges pointwise" not in lower:
    lower = replace_once(lower, insert_marker, insert_text,
                         "lower-bound concrete limit bullets")
lower = lower.replace(
    "3. uniform cutoff expansions for the characteristic derivatives and Hessian\n   used by the reoptimized clock; the scalar characteristic and fixed-time\n   collective-energy expansions now have explicit `K/M` and `O_t(M^(-4))`\n   forms;\n4. an explicit `C/M` bridge from the concrete reoptimized coefficient to the\n   algebraic phase model;\n5. a certified compact-complement argument covering transitions between zero\n   valleys.\n",
    "3. an explicit bridge from the concrete moving minimizer/reoptimized\n   coefficient to the algebraic phase model, using the now-proved value and\n   first/second derivative tail bounds;\n4. an eventual positive finite coercivity certificate on the desired region;\n5. a certified compact-complement argument covering transitions between zero\n   valleys.\n",
)
lower = lower.replace(
    "plus fixed-time tail/energy asymptotics and conditional\ncoefficient-sequence and limit theorems.",
    "plus fixed-time tail/energy asymptotics, the concrete pointwise energy\nlimit, and conditional confinement theorems whose finite coercivity premise is\nstill explicit.",
)
write(lower_path, lower)

theorem_map_path = "docs/THEOREM_MAP.md"
theorem_map = read(theorem_map_path)
map_section = """
## Concrete empirical limit and conditional confinement

| Lean declaration | Mathematical content |
| --- | --- |
| `empiricalPlaneParameter_re` | The real coordinate of the empirical real-plane parameter is exactly `sigma`. |
| `empiricalPlaneParameter_im` | The imaginary coordinate is exactly the phase time. |
| `finiteEmpiricalCollectiveRawEnergyPlane_tendsto` | For every fixed `sigma > -1` and time, the faithful finite C2--C7 raw energy converges pointwise to the concrete infinite empirical energy. |
| `empiricalCollectiveRawEnergy_eq_zero_of_genuine_zero` | A Genuine zero in the strip annihilates every faithful limiting camera and hence the infinite collective raw energy. |
| `empiricalCollectiveRawEnergyPlane_eq_zero_of_genuine_zero` | Real-plane form of the same limit-energy zero identity. |
| `genuineZero_in_region_forces_re_eq_half_of_eventual_empiricalCoercivity` | On any region contained in the Genuine strip, eventual positive finite empirical coercivity passes through the now-concrete pointwise limit and confines every Genuine zero to `sigma = 1/2`. |
| `genuineZero_forces_re_eq_half_of_eventual_empiricalStripCoercivity` | Strip-wide specialization of the concrete confinement bridge. |
| `genuineZero_forces_re_eq_half_of_eventual_globalEmpiricalCoercivity` | A supplied eventual global finite empirical coercivity certificate implies strip-wide Genuine-zero confinement. |

These theorems close the concrete convergence and final logical implication.
They do not prove the eventual finite coercivity premise.

"""
if "## Concrete empirical limit and conditional confinement" not in theorem_map:
    theorem_map = replace_once(
        theorem_map,
        "The authoritative machine-readable order is\n",
        map_section + "The authoritative machine-readable order is\n",
        "theorem map concrete limit section",
    )
write(theorem_map_path, theorem_map)

scope_path = "docs/FORMALIZATION_SCOPE.md"
scope = read(scope_path)
scope_section = """
## Concrete limit/confinement closure in v0.11.0

Lean now defines the actual infinite raw energy of the faithful C2--C7 stack
and proves pointwise convergence of the finite raw energies throughout
`sigma > -1`. It also proves that Genuine vanishing in the strip annihilates
that limiting energy. Those facts are combined with the regional limit theorem
in concrete capstones: any supplied eventual positive finite coercivity
certificate confines every Genuine zero in the certified region to real part
one-half.

The release does not promote a float64 certificate to a theorem. Proving the
eventual finite coercivity premise, including the moving minimizer and compact
complement, remains the quantitative frontier.

"""
if "## Concrete limit/confinement closure in v0.11.0" not in scope:
    scope += "\n" + scope_section
write(scope_path, scope)

print("prepared v0.11.0 release metadata and documentation")

# v0.17.0 — Arbitrary-multiplicity near-axis certificate

Version `0.17.0` closes the qualitative local near-axis gate for every
critical Genuine zero equipped with arbitrary positive finite analytic
multiplicity.

The release remains native-first. No numerical zero height, finite zero table,
simplicity premise, floating-point certificate, explicit formula, functional
equation, or Euler product is used as a Lean premise.

## Analytic isolation at every finite multiplicity

A nonzero leading analytic jet prevents the Genuine continuation from
vanishing identically near a zero. Lean applies the analytic zero dichotomy to
prove punctured-neighborhood nonvanishing for every finite multiplicity.

Each critical-line center therefore admits a horizontal radius `r` with

```math
0<r\le\frac12
```

such that the Genuine continuation is nonzero on the punctured horizontal
window at the center's height.

## Canonical near-axis certificate

The release selects one such positive radius at every critical Genuine zero
carrying finite multiplicity data and packages the resulting union of
near-axis windows. Membership in this union implies Genuine nonvanishing.

The construction is qualitative: the radius may depend on the center. No
uniform numerical lower radius is asserted.

## Exact remaining gate

The final capstone now takes one explicit complementary certificate:
nonvanishing at off-critical points of the critical strip lying outside the
certified near-axis region. Lean proves that this complement certificate,
together with the canonical near-axis certificate, gives final Genuine zero
confinement and the existing strong nonvanishing formulation.

This release does not supply that complement certificate and does not claim an
unconditional global strip-wide theorem.

## Audit and publication

GitHub Actions validates the exact checkout, pinned dependency lock, canonical
readout bridge, final frontier probe, static publication audit, full public
library with warnings as errors, ordered kernel audit, and foundational axiom
allowlist. A successful audit on the exact merged `main` SHA triggers the
audited `v0.17.0` tag and GitHub release used by the Zenodo integration.

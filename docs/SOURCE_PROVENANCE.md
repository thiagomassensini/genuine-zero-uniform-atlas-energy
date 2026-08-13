# Source Provenance

## Exact dependency lock

The formal proof has one direct theory dependency:

- repository: [`thiagomassensini/primos`](https://github.com/thiagomassensini/primos);
- Lean package: `CPFormal`;
- pinned release: `v0.62.0`;
- resolved commit: [`537028681ae6a775c083a1e2fb6e67db24697b82`](https://github.com/thiagomassensini/primos/commit/537028681ae6a775c083a1e2fb6e67db24697b82);
- Lean toolchain: `v4.32.0`;
- Mathlib input revision: `v4.32.0`;
- resolved Mathlib commit: `81a5d257c8e410db227a6665ed08f64fea08e997`.

The lock is recorded in `lakefile.toml`, `lean-toolchain`, and
`lake-manifest.json`.

## Upstream theorem chain used

The native/Genuine identity comes from
`CpGenuineNativeRealBoundaryCrosswalk`:

- `nativeCarryRealPlaneEnergy_sample`;
- `nativeCarryRealPlaneComplexPackaging_finiteChartAt_eq_dirichlet`;
- `nativeCarryRealBoundaryClosure_iff_genuineContinuation_zero`.

The atlas ledger comes from `CpTfvdSeededFiniteBesselConservation` and its
radial factorization dependency:

- `finiteSeededTfvdBesselEnergy`;
- `finiteCanonicalSeededTfvdGreenRadialClosureObservable_eq_radialDifference_mul_pairing`.

The tilted-center theorem uses the completed interfaces exported through
`CpGenuineCarryTiltFrontier`, with the relevant declarations originating in
`CpBracketGreenBoundary`, `CpBracketGreenFlux`, `CpFiniteGreenPositivity`, and
`CpTiltRigidity`:

- `finiteBracketCoupledCpGreenFlux_eq_radialDifference_mul_pairing`;
- `finiteBracketCoupledSignedBoundary_tendsto_zero_of_genuine_zero`;
- `finiteReflectedGradientPairing_re_pos`;
- `cpTiltAtSigma_eq_zero_iff_half`;
- `branchDefect_eq_zero_iff_cpTiltAtSigma_eq_zero_of_admissible_center`;
- `coupledFlux_tendsto_zero_iff_criticalDisplacement_eq_zero`.

The local proof specializes these exact interfaces to the native parameter
`1/2 + i t`, subtracts the already-defined boundary from the already-defined
total flux, and introduces no competing zero definition. Its off-equilibrium
capstone composes the same boundary limit, positive-center characterization,
and flux-closure equivalence without adding another analytic assumption.

## Why no source trees are copied

Lake checks out the exact upstream commit and its exact Mathlib dependency.
No loose copy of a theorem file is placed in this repository. This avoids
duplicate definitions and makes every imported result traceable to one Git
revision.

Other carry repositories remain conceptually related, but their source trees
are not required to compile this theorem. Minimal dependencies make the audit
stronger and do not imply different underlying mathematics.

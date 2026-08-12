# Source Provenance

## Exact dependency lock

The formal proof has one direct theory dependency:

- repository: [`thiagomassensini/primos`](https://github.com/thiagomassensini/primos);
- Lean package: `CPFormal`;
- pinned commit: [`0c64a8366ded96a3242cbe0888c55144442c570b`](https://github.com/thiagomassensini/primos/commit/0c64a8366ded96a3242cbe0888c55144442c570b);
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

The local proof specializes these exact interfaces to the native parameter
`1/2 + i t` and introduces no competing zero definition.

## Why no source trees are copied

Lake checks out the exact upstream commit and its exact Mathlib dependency.
No loose copy of a theorem file is placed in this repository. This avoids
duplicate definitions and makes every imported result traceable to one Git
revision.

Other carry repositories remain conceptually related, but their source trees
are not required to compile this theorem. Minimal dependencies make the audit
stronger and do not imply different underlying mathematics.

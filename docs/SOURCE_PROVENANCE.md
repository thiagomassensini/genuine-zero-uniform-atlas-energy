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

The empirical-camera continuation and cutoff work additionally use these
kernel-checked CPFormal interfaces:

- `realCpPairBracket` and `realCpSaturatedBracket`;
- `bracketedDirichletChart_eq_naturalCameraFactor_mul_genuineContinuation`;
- `alignedC2BracketedDirichletChart_eq_factor_mul_genuineContinuation`;
- `pairedAltChannel_eq_genuineContinuation`;
- `naturalEvenCameraFactor` and `naturalOddCameraFactor`;
- the centered-second-difference derivative estimates and shifted
  `p`-series summability lemmas.

## Locked empirical source

The exact six-camera geometry was audited against:

- repository: [`thiagomassensini/finite-native-carry-operator`](https://github.com/thiagomassensini/finite-native-carry-operator);
- commit: [`00e9d6beb17226545abf5ddf90bbfede6c7146b0`](https://github.com/thiagomassensini/finite-native-carry-operator/commit/00e9d6beb17226545abf5ddf90bbfede6c7146b0);
- file: `laboratory/native_carry_primitive_real_operator_all_bases.py`;
- file SHA-256:
  `c68d4bb274f36eb4dc5572afe64394787876f64bc8f2e50573654f2ab712ecee`.

That source uses labels `2,3,4,5,6,7`, periods `4,3,4,5,6,7`, and second
radius moments `1,1,5,5,14,14`. In particular, the empirical cameras labelled
four and six retain the antipodal radii two and three. CPFormal's natural even
camera uses `halfRange b = (b-1)/2` and intentionally omits those middle
channels. The local formalization therefore defines the full-even channels
explicitly instead of identifying two different operators.

## Numerical evidence boundary

The separate 56-job float64 campaign is recorded in
[`audit/empirical-evidence.json`](../audit/empirical-evidence.json). Its
[locked result bundle](../audit/coercivity_56_guard1024_results.tar.gz) is
included in the repository and has SHA-256
`6aabb89cb3e460ae3142a6e82341d3597b9afe3d632151d76c6de186824053ae`.
The exact eight-file runtime import closure and the aggregation utility are
included under
[`audit/empirical-campaign`](../audit/empirical-campaign/README.md), with
Python, NumPy, SciPy, and every source hash locked in the manifest. The record
is provenance and motivation, not a Lean proof object. Static audit requires
the status `NUMERICAL_FLOAT64_EVIDENCE_NOT_KERNEL_CHECKED`, checks the source
import closure, camera tables, exact campaign grid, and every archived JSON
status, then hashes the included bundle byte for byte.

## Why no source trees are copied

Lake checks out the exact upstream commit and its exact Mathlib dependency.
No loose copy of a theorem file is placed in this repository. This avoids
duplicate definitions and makes every imported result traceable to one Git
revision.

Other carry repositories remain conceptually related, but their source trees
are not required to compile this theorem. Minimal dependencies make the audit
stronger and do not imply different underlying mathematics.

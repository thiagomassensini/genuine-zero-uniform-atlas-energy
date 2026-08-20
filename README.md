# Genuine Zero Uniform Atlas Energy

Lean 4 formalization of positional carry geometry, the native/Genuine zero
identity, exact finite cutoff control, and the transverse-energy route toward
uniform zero confinement.

The project is deliberately native-first. The half-abscissa comes from the
quadratic amplitude law of carry depth:

```math
n=b^k m
\quad\Longrightarrow\quad
\text{mass}=b^{-k},
\qquad
\text{amplitude}=b^{-k/2}.
```

Thus the distinguished real coordinate is

```math
\sigma=\frac12.
```

No external zero list, floating-point witness, explicit formula, functional
equation, or Euler product is used as a premise for the native geometric
route.

## Core architecture

For a fixed camera family and cutoff, the real native state is

```math
u_t(n)
=
n^{-1/2}
\bigl(\cos(-t\log n),\sin(-t\log n)\bigr).
```

Each camera applies its positional seeds and centered carry brackets. Stacking
the primitive resultants gives the collective observation map `C`, with
positive visibility operator `K=C^*C`.

The exact zero condition is

```math
C u_t=0
\quad\Longleftrightarrow\quad
\langle u_t,Ku_t\rangle=0.
```

The complex notation used in bridge modules is only a lossless shorthand for
the native real two-plane.

## Exact cutoff route

The faithful empirical package uses the cameras `2,3,4,5,6,7`, including the
antipodal channels of the even cameras. The library contains:

- exact finite characteristic and unresolved-tail identities;
- critical-line amplitude and raw-energy bounds;
- exact logarithmic cutoff jets;
- differentiated remainder and Cauchy estimates;
- finite-to-limit collective-energy transport;
- the concrete limit-confinement capstone;
- an audited comparison with the canonical arithmetic nonlocal readout;
- an exact crosswalk to the spectral-Weyl camera geometry;
- all-order camerawise derivative-tail estimates;
- an explicit Euclidean bound for the finite six-camera second-jet stack;
- fixed inverse-cutoff second-jet constants and curvature bounds;
- a concrete local Schur estimate with no external second-jet premise.

The comparison layers remain lateral. They do not replace the native
carry-geometric proof architecture.

## Version 0.17.0: arbitrary-multiplicity near-axis certificate

Version `0.17.0` closes the qualitative local near-axis gate for every
critical Genuine zero carrying arbitrary positive finite analytic
multiplicity. Analyticity and the nonzero leading jet isolate each zero and
supply a positive punctured horizontal window on which the Genuine
continuation does not vanish.

The selected radius may depend on the zero. No numerical zero list, height
bound, simplicity hypothesis, or unjustified global radius floor is imported.
The final capstone now has one explicit residual input: nonvanishing at
off-critical strip points outside the union of the certified near-axis
windows. This release does not provide that complement certificate and does
not claim unconditional global confinement.

Detailed status:

- [Quantitative empirical jet gates](docs/QUANTITATIVE_EMPIRICAL_JET_GATES.md)
- [Lower-bound status](docs/LOWER_BOUND_STATUS.md)
- [Microscopic coercivity bridge](docs/MICROSCOPIC_COERCIVITY_BRIDGE.md)
- [Release notes 0.17.0](docs/RELEASE_0.17.0.md)

## What is proved and what remains

Kernel-checked now:

- the exact moving-clock completed square;
- the finite residual and corrected first-jet packages;
- stack-level pairing and energy perturbation inequalities;
- reduction of the local Schur coefficient to primitive jet bounds;
- abstract eventual positivity from any positive phase floor;
- exact empirical-to-spectral camera equality;
- all-order camerawise derivative-tail transport;
- exact finite/infinite/tail second-jet identity;
- explicit camerawise and six-camera finite second-jet bounds;
- fixed inverse-cutoff second-jet tail constants;
- a cutoff-independent finite second-jet stack bound;
- fixed inverse-cutoff bounds for both curvature coordinates;
- downstream local Schur specialization without an external second-jet bound;
- fixed inverse-cutoff corrected and raw first-jet stack bounds;
- eventual positive corrected/raw clock-Gram and temporal-denominator floors;
- a corrected finite-energy floor and local Schur inverse-cutoff approximation;
- fixed residual, pairing, radial-gradient, and denominator perturbation channels;
- eventual positive corrected microscopic coercivity at presented simple zeros;
- all previously released carry, Green, cutoff, and limit theorems.

Still required for the final unconditional global statement:

- compact-complement nonvanishing outside the certified near-axis region;
- exact near-axis/complement coverage for the chosen global route;
- one global cutoff and lower bound across all local windows if the energy
  route is retained;
- the final unconditional strip-wide stitching theorem.

This distinction is enforced in the publication metadata. Version `0.17.0`
does not promote the complement certificate or an unconditional confinement
theorem.

## Audit surface

The canonical workflow checks the exact commit and pinned dependency graph,
then runs:

```text
lake build --wfail GenuineZeroUniformAtlasEnergy.ArithmeticReadoutBridge
lake build --wfail GenuineZeroUniformAtlasEnergy.FinalConfinementProbe
bash scripts/static_audit.sh
lake build --wfail GenuineZeroUniformAtlasEnergy
lake build --wfail GenuineZeroUniformAtlasEnergy.Audit
```

The final step checks the foundational axiom allowlist. The static audit rejects
local `sorry`, `admit`, `axiom`, and `unsafe`, validates metadata, registries,
claims, local imports, and GitHub Markdown.

A successful audit on `main` triggers `.github/workflows/release.yml`, which
creates the versioned GitHub tag and release used by the Zenodo integration.

## Promoted registry and release manifest

The promoted registry remains the immutable `0.12.0` snapshot:

- `156` ordered theorem IDs;
- `24` claims;
- unchanged pinned dependencies.

The `0.17.0` release manifest records the new public-build modules separately.
This prevents a software release from silently rewriting an earlier published
claim surface.

- [Theorem registry status](audit/THEOREM_REGISTRY.md)
- [Claim ledger](audit/CLAIM_LEDGER.md)
- [Release manifest](audit/RELEASE_MANIFEST_0.17.0.md)

## Repository layout

```text
GenuineZeroUniformAtlasEnergy/
  NativeGeometry.lean
  NativeCutoffTail.lean
  NativeCutoffAsymptotic.lean
  NativeCutoffLogJet.lean
  NativeCutoffDifferentiatedRemainder.lean
  NativeCutoffExactScaledTail*.lean
  EmpiricalCameraGeometry.lean
  EmpiricalCameraOperator.lean
  EmpiricalCameraHigherDerivativeCrosswalk.lean
  EmpiricalStackProjection.lean
  EmpiricalTransverseDataCrosswalk.lean
  MicroscopicCoercivityFrontier.lean
  MicroscopicJetTransfer.lean
  MicroscopicPrimitiveJetBounds.lean
  EmpiricalFiniteTransverseData.lean
  EmpiricalFiniteResidualBound.lean
  EmpiricalFiniteCorrectedData.lean
  EmpiricalFiniteFirstJetBound.lean
  EmpiricalFinitePairingBound.lean
  EmpiricalFiniteEnergyBound.lean
  EmpiricalFiniteCurvatureBound.lean
  EmpiricalFiniteSecondJetBound.lean
  EmpiricalSecondJetGateClosure.lean
  EmpiricalSecondJetDownstreamClosure.lean
  EmpiricalDenominatorFloors.lean
  EmpiricalEnergyLocalGateClosure.lean
  EmpiricalNonJetGateClosure.lean
  EmpiricalMicroscopicPositiveGate.lean
  EmpiricalLimitConfinement.lean
  FinalConfinementProbe.lean
  ArithmeticReadoutBridge.lean
audit/
docs/
scripts/
```

## Build

The repository pins Lean and every external dependency. The authoritative
validation is GitHub Actions:

```bash
lake update
lake exe cache get
lake build --wfail GenuineZeroUniformAtlasEnergy
lake build --wfail GenuineZeroUniformAtlasEnergy.Audit
```

Local builds are useful for development, but a release is created only from an
exact audited `main` commit.

## Citation and license

Release metadata is stored in `CITATION.cff` and `.zenodo.json`. The software is
released under the MIT License.

# v0.16.0 — Concrete finite microscopic positivity closure

Version `0.16.0` closes the concrete local gate scheduled after the complete
second-jet closure in `v0.15.0`. At every presented critical simple zero, the
finite corrected microscopic coefficient is eventually positive with a
cutoff-independent lower bound.

The release remains native-first. No numerical height, zero table,
floating-point certificate, explicit formula, functional equation, or Euler
product is used as a Lean premise.

## Fixed first-jet and denominator controls

The corrected and raw six-camera first-jet errors now receive fixed constants
independent of the cutoff:

```math
\left\|V_M-V_\infty\right\|
\le \frac{C_V(t)}{M}.
```

These estimates propagate through the quadratic clock Gram. At every presented
critical simple zero, Lean proves eventual floors for:

- the corrected finite clock Gram;
- the raw finite clock Gram used by the Hessian;
- the temporal Schur denominator.

In particular, the denominator is eventually bounded below by one quarter of
the positive limiting clock Gram.

## Corrected energy and local Schur coefficient

The corrected reoptimized finite energy is eventually within a fixed
`C_E(t)/M` neighborhood of its exact phase model and therefore satisfies

```math
\frac{\rho(t)}{2}
\le E_M^{\mathrm{corr}}(t)
```

for all sufficiently large cutoffs.

The concrete local Schur coefficient likewise satisfies a fixed
inverse-cutoff approximation to the limiting clock Gram:

```math
\left|c_M(t)-\kappa(t)\right|
\le \frac{C_c(t)}{M}.
```

## Remaining non-jet channels

The release supplies fixed inverse-cutoff constants for the channels not
discharged by the second-jet theorem:

- the naturally scaled six-camera residual;
- the corrected residual/clock pairing;
- the corrected radial-gradient difference;
- a cutoff-independent bound for the finite/model gradient sum;
- the gradient-square perturbation;
- the model-energy denominator perturbation.

All constants may depend on the fixed presented time and the stored camera
family, but never on the cutoff.

## Concrete microscopic positivity

Combining the denominator floors, corrected energy floor, local Schur
approximation, and non-jet channels gives the public theorem

`eventually_finiteEmpiricalCorrectedMicroscopicCoercivity_ge_half_phaseFloor`.

Its conclusion is

```math
\frac{\mathrm{phaseFloor}(t)}{2}
\le c_M^{\mathrm{micro}}(t)
```

eventually in `M`. The existential companion exports one concrete positive
constant for the local finite gate.

## Multiplicity and global scope

This is deliberately a simple-zero theorem. Here `M` is the finite cutoff and
`m` is analytic multiplicity. The current quadratic clock uses a nonzero first
derivative and therefore belongs to the `m=1` sector.

For `m>1`, the correct local leading energy has order `2m`; forcing a
quadratic lower bound would be false. A later route may instead transport an
arbitrary-multiplicity near-axis nonvanishing certificate.

This release does not promote:

- arbitrary-multiplicity near-axis transport;
- compact-complement nonvanishing;
- exact near/complement coverage;
- one strip-wide cutoff and lower bound across all local windows;
- an unconditional global confinement theorem.

## Audit and publication

The promoted theorem registry and claim ledger remain the immutable `0.12.0`
snapshots: `156` ordered theorem IDs and `24` claims. Version `0.16.0`
adds four public-build-checked modules without relabelling the local simple-zero
result as a global claim:

- `EmpiricalDenominatorFloors`;
- `EmpiricalEnergyLocalGateClosure`;
- `EmpiricalNonJetGateClosure`;
- `EmpiricalMicroscopicPositiveGate`.

GitHub Actions validates the exact checkout, pinned dependency lock, canonical
bridge, final frontier probe, static publication audit, full public library
with warnings as errors, ordered kernel audit, and foundational axiom
allowlist. A successful audit on `main` triggers the audited `v0.16.0` tag
and GitHub release used by the Zenodo integration.

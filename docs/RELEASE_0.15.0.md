# v0.15.0 — Complete quantitative second-jet closure

Version `0.15.0` completes the first quantitative gate after the exact
six-camera second-jet crosswalk released in `v0.14.0`. The finite second jet is
now not only identified and bounded at its natural Cauchy rate; every concrete
downstream use receives a cutoff-independent bound, and the local Schur ledger
no longer accepts an external second-jet premise.

The release preserves the Genuine-first and native-first architecture. It uses
no supplied height, zero table, floating-point certificate, explicit formula,
functional equation, or Euler product as a premise for the native geometric
route.

## Logarithmic absorption

The order-two derivative tail from `v0.14.0` satisfies

```math
\left\|T_{b,M}''\!\left(\frac12+it\right)\right\|
\le
2C_b(t)M^{-3/2}\log(M)^2.
```

Lean now proves the elementary estimate

```math
M^{-3/2}\log(M)^2\le\frac{16}{M}
```

for positive integer cutoffs. Consequently, each camera receives a fixed
constant `C_{b,2}(t)`, independent of `M`, such that

```math
\left\|T_{b,M}''\!\left(\frac12+it\right)\right\|
\le
\frac{C_{b,2}(t)}{M}.
```

No maximization over numerical cutoffs is inserted into this step.

## Uniform finite second-jet stack

The exact prefix-tail identity remains

```math
\chi_{b,M}''=\chi_b''-T_{b,M}''.
```

Combining it with the inverse-cutoff estimate produces fixed camerawise bounds
and one Euclidean six-camera constant `B_2(t)` satisfying

```math
\left\|
\texttt{finiteEmpiricalCameraSecondDerivativeStack}\;M\;
  \left(\frac12+it\right)
\right\|
\le B_2(t)
```

once the existing Cauchy threshold is met. The constant may depend on the
fixed time and stored camera family, but never on the cutoff.

## Curvature channels

At a presented critical zero, the finite residual already has an inverse-cutoff
bound. Pairing that residual with the fixed second-jet stack gives a single
constant `C_curv(t)` with

```math
|a_M|\le\frac{C_{\mathrm{curv}}(t)}{M},
\qquad
|b_M|\le\frac{C_{\mathrm{curv}}(t)}{M}.
```

Thus the second derivative contributes a completely explicit vanishing channel
to the finite transverse Schur coefficient.

## Downstream Schur closure

The generic curvature module retains a reusable theorem that accepts an
arbitrary supplied second-jet bound. The concrete empirical route now has a
specialized theorem using the canonical `B_2(t)` automatically.

Its public statement receives only the positive temporal denominator floor
scheduled for the next gate. No `secondJetBound` hypothesis survives in the
actual finite empirical coercivity route.

## Multiplicity scope

The camera identities, all-order derivative-tail theorem, logarithmic
absorption, and uniform second-jet estimate do not assume simplicity.

Simplicity enters only in the later quadratic moving-clock argument, whose
clock direction is built from the first derivative. Therefore:

```math
m=1
```

is the quadratic sector, while a zero of multiplicity `m>1` requires a leading
energy analysis of order `2m`. The analytic multiplicity `m` and finite cutoff
`M` remain distinct parameters.

## Remaining quantitative stages

Exactly four stages remain visible:

1. cutoff-independent positive floors for the finite clock Gram, corrected
   reoptimized energy, and temporal Schur denominator;
2. fixed constants for the remaining non-jet perturbation channels;
3. the concrete local microscopic-positivity theorem;
4. the compact-complement and strip-wide stitching theorem.

The second-jet estimate and its curvature contribution are no longer among the
open obligations.

## Audit and publication

The promoted theorem registry and claim ledger remain the immutable `0.12.0`
snapshots: `156` ordered theorem IDs and `24` claims. Version `0.15.0` adds two
public-build-checked modules without relabelling them as a new unconditional
claim:

- `EmpiricalSecondJetGateClosure`;
- `EmpiricalSecondJetDownstreamClosure`.

GitHub Actions validates the exact checkout, pinned dependency lock, canonical
bridge, final frontier probe, static publication audit, full public library
with warnings as errors, ordered kernel audit, and foundational axiom
allowlist. A successful audit on `main` triggers the audited `v0.15.0` tag and
GitHub release used by the Zenodo integration.

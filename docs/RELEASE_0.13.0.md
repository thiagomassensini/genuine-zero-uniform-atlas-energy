# v0.13.0 — Microscopic coercivity bridge

Version `0.13.0` turns the pointwise transverse model into a concrete
six-camera perturbation ledger. The release preserves the Genuine-first and
native-first architecture: carry geometry, quadratic amplitude, exact cutoff
control, and the real native operator remain upstream of every comparison
layer.

## Exact moving-clock crosswalk

The phase-rotated cutoff/tangent pairing is split into real and imaginary
coordinates. The clock envelope is completed exactly:

```math
\mathcal E_{\mathrm{clock}}(x,y,\tau)
=
\left(\rho+\frac{x^2}{\kappa}\right)
+
\kappa\left(\tau-\frac{y}{\kappa}\right)^2.
```

At the minimizing clock displacement, the leading energy is therefore

```math
E_0
=
\rho+\frac{x^2}{\kappa}.
```

The positive quantity `rho` supplies the fixed model-denominator floor.

## Microscopic coefficient and perturbation ledger

The finite microscopic coefficient is organized as

```math
c_{\mathrm{micro},M}
=
c_{\mathrm{local},M}
-
\frac{g_M^2}{4E_M}.
```

The exact ledger separates its error from the phase model into three channels:

1. local Schur-coefficient error;
2. radial-gradient square error;
3. reoptimized-energy denominator error.

`MicroscopicPrimitiveJetBounds.lean` reduces the quotient channels to primitive
bounds for gradient difference and sum, energy difference, curvature, and
strictly positive denominator floors.

## Concrete six-camera data

The release packages the following concrete finite objects:

- the phase-normalized scaled residual;
- the logarithmically corrected first jet
  `chi'_M + log(M) chi_M`;
- the phase pairing and radial gradient;
- the clock Gram scalar;
- the corrected reoptimized energy;
- the raw transverse Hessian jet and its Schur coefficient.

The residual and corrected first-jet stack errors are assembled from the
existing exact camerawise Cauchy estimates. Pairing, energy, and curvature
bounds are then derived by norm and Schur-complement inequalities.

## Retired historical threshold

The abstract eventual-positivity theorem no longer requires the historical
condition `phaseFloor > 4`. A strictly positive phase floor is sufficient once
the three perturbation channels vanish along the cutoff.

This is a real strengthening of the abstract bridge, but not an unconditional
global confinement theorem.

## Remaining obligations

The release deliberately leaves the following gates visible:

- uniform finite clock-Gram and reoptimized-energy floors;
- a uniform temporal Schur-denominator floor;
- an explicit second-jet bound with the required cutoff rate;
- conversion of the displayed stack bounds to fixed `C/M` constants;
- compact-complement and regional coverage needed for the final global
  confinement statement.

No floating-point witness, supplied height list, or empirical certificate is
imported into the Lean kernel.

## Audit and publication

The promoted theorem registry and claim ledger remain the immutable `0.12.0`
snapshots: `156` ordered theorem IDs and `24` claims. Version `0.13.0` adds
public-build-checked bridge modules without promoting a new unconditional
confinement claim.

GitHub Actions validates the exact checkout, pinned dependency lock, canonical
bridge, final frontier probe, static publication audit, full public library
with warnings as errors, ordered kernel audit, and foundational axiom
allowlist. A successful audit on `main` triggers the versioned GitHub tag and
release consumed by the Zenodo integration.

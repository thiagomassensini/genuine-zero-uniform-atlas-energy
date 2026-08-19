# Lower-bound and microscopic-coercivity status

## Current statement

The release contains an exact finite-to-model ledger for the microscopic
coefficient

```math
c_{\mathrm{micro},M}
=
c_{\mathrm{local},M}
-
\frac{g_M^2}{4E_M}.
```

The moving-clock model is identified exactly with

```math
E_{0,M}
=
\rho+\frac{x_M^2}{\kappa}.
```

The abstract transfer theorem proves eventual strict positivity from a
strictly positive phase-model floor and perturbation channels that tend to
zero.

## Closed in Lean

- exact critical cutoff-tail value, first-jet, and second-jet formulas;
- exact Cauchy bounds for the scaled tail and differentiated remainder;
- exact phase rotation and moving-clock completed square;
- concrete six-camera residual, corrected first jet, pairing, energy, and
  transverse-jet definitions;
- reduction of the gradient channel to difference and sum bounds;
- reduction of the energy channel to residual, pairing, and clock-Gram bounds;
- reduction of the local Schur channel to first-jet, second-jet, and temporal
  denominator bounds;
- abstract eventual positivity from any positive phase floor;
- exact identification of the empirical camera stencils with the
  spectral-Weyl camera stencils;
- all-order camerawise derivative-tail bounds;
- exact finite/infinite/tail second-jet crosswalk;
- explicit camerawise and six-camera finite second-jet bounds with the
  `M^(-3/2) log(M)^2` rate at order two.

## Historical condition removed

The old sufficient condition `phaseFloor > 4` is no longer the gate. The
current abstract theorem only needs `phaseFloor > 0`, together with vanishing
finite perturbation channels.

## Still open

- a uniform positive lower floor for the finite corrected clock Gram;
- a uniform positive lower floor for the finite reoptimized energy;
- a uniform positive lower floor for
  `|kappa_M-a_M|`;
- fixed constants converting the displayed stack errors to `C/M` bounds;
- the concrete local microscopic-positivity specialization;
- compact-complement and regional coverage for the final global statement.

## Multiplicity scope

The second-jet identities and tail estimates do not require simplicity. The
present quadratic moving-clock coercivity route does: its clock Gram is built
from the first derivative, so it is the analytic multiplicity-one sector. A
zero of multiplicity `m>1` requires a leading energy analysis of order `2m`.
The cutoff `M` and the multiplicity `m` are unrelated parameters.

## Scope firewall

The current result is a concrete, kernel-checked sufficient route. It does not
assert that every remaining uniform estimate has already been proved, and it
does not identify numerical minima, external height lists, or readout-domain
equivalences with an unconditional confinement theorem.

See `MICROSCOPIC_COERCIVITY_BRIDGE.md` for the detailed ledger and
`QUANTITATIVE_EMPIRICAL_JET_GATES.md` for the ordered continuation plan.

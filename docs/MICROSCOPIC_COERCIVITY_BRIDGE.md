# Microscopic coercivity bridge

## Purpose

This document records the exact status of the finite microscopic transverse
coercivity route. It distinguishes kernel-checked algebra from the uniform
analytic estimates that still have to be supplied.

## Model coefficient

For phase projection `x`, positive clock Gram `kappa`, transverse mass `rho`,
and local coefficient `c_local`, the model coefficient is

```math
c_{\mathrm{phase}}(x)
=
c_{\mathrm{local}}
-
\frac{(2x)^2}
{4\left(\rho+x^2/\kappa\right)}.
```

The phase denominator is the exact value of the quadratic clock envelope at
its minimizing displacement:

```math
\mathcal E_{\mathrm{clock}}(x,y,\tau_*)
=
\rho+\frac{x^2}{\kappa}.
```

## Finite coefficient

For cutoff `M`, Lean defines concrete sequences

```math
E_M,\qquad g_M,\qquad c_M
```

and the microscopic coefficient

```math
c_{\mathrm{micro},M}
=
c_M-\frac{g_M^2}{4E_M}.
```

The corrected first jet is

```math
\chi'_M(s)+\log(M)\chi_M(s).
```

This correction removes the logarithmic cutoff phase before comparison with
the infinite clock tangent.

## Exact perturbation channels

The difference between the finite and model coefficients is split into:

```math
|c_M-\kappa|,
```

```math
\left|
\frac{g_M^2-(2x_M)^2}{4E_M}
\right|,
```

and

```math
\left|
\frac{(2x_M)^2(E_{0,M}-E_M)}
{4E_ME_{0,M}}
\right|.
```

The primitive bounds reduce these channels to:

- `|g_M-2x_M|` and `|g_M+2x_M|`;
- `|E_M-E_{0,M}|`;
- `|kappa_M-kappa|`, `|a_M|`, and `|b_M|`;
- positive floors for `|E_M|`, `E_{0,M}`, and `|kappa_M-a_M|`.

## What the cutoff theorems already provide

The existing exact tail and Cauchy modules supply:

- a six-camera scaled residual bound;
- a six-camera corrected first-jet bound;
- phase rotation with unit norm;
- exact identification of the leading energy with
  `rho + x_M^2 / kappa`;
- exact reconstruction of the finite transverse jet.

The new pairing, energy, and curvature modules transport those estimates into
the three microscopic channels.

## Eventual positivity

The abstract theorem has the following shape:

```math
c_{\mathrm{phase}}(x_M)\ge \delta>0,
\qquad
\varepsilon_M\longrightarrow0
```

implies

```math
\exists c>0,\quad
\forall^{\infty}M,\quad
c\le c_{\mathrm{micro},M}.
```

Only `delta > 0` is required. The former threshold `delta > 4` is not part of
the current theorem.

## Remaining gate

A final application still needs uniform, concrete constants for the finite
energy and Schur denominators, the second jet, and the compact complement.
Until those estimates and the regional gluing are supplied, the bridge is a
kernel-checked sufficient route rather than an unconditional global
confinement theorem.

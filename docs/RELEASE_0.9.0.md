# v0.9.0 — Differentiated cutoff-remainder transport

Version `0.9.0` closes the algebraic interface between a twice controlled
scaled cutoff remainder and the exact logarithmic cutoff jets introduced in
`0.8.0`.

## Exact jet-error transport

Let `exact`, `exactFirst`, and `exactSecond` describe a scaled amplitude and
its first two complex derivatives. Let `model`, `modelFirst`, and
`modelSecond` describe a comparison model. If, at the parameter under study,
all three discrepancies satisfy the common bound

```math
\|exact-model\|\le Kr,
\qquad
\|exactFirst-modelFirst\|\le Kr,
\qquad
\|exactSecond-modelSecond\|\le Kr,
```

then the kernel verifies

```math
\|J_{1,M}(exact)-J_{1,M}(model)\|
\le
\|M^{-s-1}\|\,(1+\|\log M\|)Kr,
```

and

```math
\|J_{2,M}(exact)-J_{2,M}(model)\|
\le
\|M^{-s-1}\|\,(1+\|\log M\|)^2Kr.
```

The factors are not inserted estimates. They are the exact result of
subtracting the first and second product-rule jets through `M^(-s-1)` and then
applying the triangle inequality.

The public capstones are:

- `cutoffModel_first_second_jet_error_bounds`;
- `cutoffModel_first_second_jet_error_bounds_of_common_rate`;
- `cutoffModel_differentiated_remainder_gate`.

The last theorem packages, in one statement, the exact `HasDerivAt` jets for
both amplitudes and the two transported error estimates.

## Discovery provenance remains separate

The dyadic `M -> 2M` float64 campaign and the later high-precision checks were
used to discover and independently validate the cutoff profile. No numerical
value, selected minimum, fitted coefficient, or empirical table is imported
into the new theorems or required by the release audit.

## Formal surface

Version `0.9.0` contains:

- 144 ordered public theorems;
- 22 `KERNEL_CHECKED` claims;
- an exact source lock to CPFormal and Mathlib;
- a GitHub-Actions-only Lean and foundational-dependency audit.

## Deliberate boundary

This release closes the **transport** part of the differentiated-remainder
gate. It does not yet prove, for the exact cutoff tail, the three analytic
bounds on the scaled value, first derivative, and second derivative that feed
the interface.

The next analytic target is therefore precise: construct explicit functions
`exactFirst` and `exactSecond` for the scaled exact tail and prove a common
rate such as

```math
r_M=\frac{1}{M^q}
```

or a sharper three-term rate. Once those estimates are supplied, the present
capstone automatically produces the required
`(1+||log M||)^2/M^q` second-jet control and connects it to the existing
vanishing-error phase-floor theorem.

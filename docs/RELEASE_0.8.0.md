# v0.8.0 — Logarithmic cutoff jets and vanishing-error coercivity

This release formalizes the analytic layer selected by the independent
pre-Lean numerical validation. The cutoff-doubling experiments were used to
discover and check the model, but no floating-point value is imported into a
Lean theorem or required by the release audit.

## Exact logarithmic jet bridge

For a positive integer cutoff `M`, define the analytic factor

```math
M^{-s-1}.
```

If `A(s)` has first and second complex derivatives `A'(s)` and `A''(s)`, the
kernel now verifies the exact product-rule identities

```math
\frac{d}{ds}\left[M^{-s-1}A(s)\right]
=M^{-s-1}\left(A'(s)-\log(M)A(s)\right),
```

and

```math
\frac{d^2}{ds^2}\left[M^{-s-1}A(s)\right]
=M^{-s-1}\left(A''(s)-2\log(M)A'(s)+\log(M)^2A(s)\right).
```

The public capstone is
`cutoffModel_first_second_logarithmic_jets`.

## Vanishing-error phase-floor transport

The previous phase theorem used the special error profile `C/M`. Version
`0.8.0` proves the correct general interface: if a supplied approximation
error tends to zero, then every strict lower target below the symbolic phase
floor eventually holds. In particular, a supplied microscopic coefficient is
eventually at least four whenever `4 < phaseFloor`.

The public capstones are:

- `PhaseProjectionData.eventually_microscopicCoercivity_lower_bound_of_vanishing_error`;
- `PhaseProjectionData.eventually_microscopicCoercivity_ge_four_of_vanishing_error`.

## Discovery provenance is not a proof dependency

The `M -> 2M` float64 campaign and later high-precision checks remain useful
for reproducing how the closed cutoff identity and logarithmic derivative
profile were found. They are not theorem premises, kernel objects, or release
gates. The mandatory audit now checks Lean sources, the ordered theorem
registry, claims, metadata, Markdown, and the locked dependency revisions.

## Formal surface

Version `0.8.0` contains:

- 141 ordered public theorems;
- 21 `KERNEL_CHECKED` claims;
- an exact source lock to CPFormal and Mathlib;
- a GitHub-Actions-only Lean and axiom audit.

## Deliberate boundary

This release does not yet prove that the exact cutoff tail satisfies the full
three-term differentiated remainder suggested by the numerical validation.
It also does not identify the concrete reoptimized microscopic coefficient,
control all moving valleys uniformly, or prove a cutoff-independent global
coercivity constant. The next analytic gate is to feed an explicit
`(1+log M)^2/M^q` remainder into the exact jet bridge formalized here.

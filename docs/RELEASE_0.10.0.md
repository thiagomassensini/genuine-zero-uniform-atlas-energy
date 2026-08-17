# v0.10.0 — Exact scaled-tail analytic bounds

Version `0.10.0` closes the analytic input left open by the differentiated
cutoff-remainder transport in `0.9.0`.

## Exact scaled tail

For a positive cutoff `M`, let

```math
\mathcal E_M(s)
=
M^{s+1}T_M(s)-A(s)
```

be the exact scaled explicit-radius cutoff-tail error. The release proves that
`mathcal E_M` is holomorphic on the open ball of radius `1/2` centered at every
critical-line point

```math
s_0=\frac12+i t.
```

The proof is analytic and source-based. Each shifted explicit-radius block is
holomorphic, and on that ball its norm is dominated by one summable quadratic
p-series whose coefficient is independent of the tail index.

## Uniform Cauchy circle

On the closed ball of radius

```math
r=\frac14
```

around `s_0`, the real part remains at least `1/4`. The pointwise exact-tail
estimate is therefore bounded by one explicit circle constant

```math
C_h(t)
=
A_t(A_t+1)(A_t+2)
\bigl(S_2(h)+2S_3(h)\bigr),
```

where

```math
A_t=\left\|\frac12+i t\right\|+\frac14.
```

Consequently every point on the Cauchy circle satisfies

```math
\|\mathcal E_M(s)\|\le \frac{C_h(t)}{M}.
```

## The three analytic bounds

Cauchy's estimate now gives, at `s_0`,

```math
\|\mathcal E_M(s_0)\|
\le
\frac{C_h(t)}{M},
```

```math
\|\mathcal E_M'(s_0)\|
\le
\frac{C_h(t)}{M r}
=
\frac{4C_h(t)}{M},
```

and

```math
\|\mathcal E_M''(s_0)\|
\le
\frac{2C_h(t)}{M r^2}
=
\frac{32C_h(t)}{M}.
```

The ordered public theorem reports are:

- `norm_nativeExplicitRadiusScaledTailError_critical_value_le`;
- `norm_nativeExplicitRadiusScaledTailError_critical_first_le`;
- `norm_nativeExplicitRadiusScaledTailError_critical_second_le`;
- `nativeExplicitRadiusScaledTailError_critical_three_bounds`.

The last statement packages the three estimates without adding a fourth
analytic hypothesis.

## Connection to the logarithmic cutoff jets

Version `0.9.0` already proved the exact transport of supplied scaled value,
first-derivative, and second-derivative errors through the factor `M^(-s-1)`.
The present release supplies those three inputs for the exact scaled tail.
Therefore the first transported jet acquires exactly one `log M` loss and the
second acquires exactly the square `(1+||log M||)^2`, with the underlying
analytic rate now proved rather than assumed.

## Formal surface

Version `0.10.0` contains:

- 148 ordered public theorem reports;
- 23 `KERNEL_CHECKED` claims;
- an exact source lock to CPFormal and Mathlib;
- a GitHub-Actions-only Lean build, ordered `#print axioms` audit, and
  foundational allowlist check.

## Discovery provenance and non-claims

The `M -> 2M` float64 campaign and later high-precision checks helped identify
the correct scaled profile and logarithmic losses. No decimal value, selected
minimum, fitted coefficient, or empirical table enters these proofs.

This release does not identify a moving finite minimizer, prove a concrete
reoptimized microscopic coefficient, or establish a cutoff-uniform global
coercivity constant. Those remain separate geometric gates; the exact scaled
value and its first two complex derivatives are no longer among the missing
analytic inputs.

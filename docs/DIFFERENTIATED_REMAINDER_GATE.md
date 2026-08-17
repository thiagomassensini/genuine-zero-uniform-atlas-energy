# Differentiated cutoff-remainder gate

## Purpose

The fixed-time critical tail theorem controls the scaled cutoff value. The
coercivity step also needs the scaled first and second complex derivatives.
Version `0.10.0` closes both parts of this gate: the analytic exact-tail bounds
and their exact logarithmic transport through the cutoff factor.

## Exact transport

Write the unscaled cutoff model as

```math
T_M(s)=M^{-s-1}A_M(s).
```

Let `A_M` be compared with a model `B_M`. Suppose their scaled discrepancies
at one parameter satisfy

```math
\|A_M-B_M\|\le e_0,
\qquad
\|A_M'-B_M'\|\le e_1,
\qquad
\|A_M''-B_M''\|\le e_2.
```

The exact product rule gives

```math
T_M'(s)=M^{-s-1}\left(A_M'(s)-\log(M)A_M(s)\right)
```

and

```math
T_M''(s)=M^{-s-1}\left(
A_M''(s)-2\log(M)A_M'(s)+\log(M)^2A_M(s)
\right).
```

Subtracting the corresponding model jets and applying the norm inequality
yields the kernel-checked bounds

```math
\|T_M'-S_M'\|
\le
\|M^{-s-1}\|\left(e_1+\|\log M\|e_0\right)
```

and

```math
\|T_M''-S_M''\|
\le
\|M^{-s-1}\|\left(
e_2+2\|\log M\|e_1+\|\log M\|^2e_0
\right).
```

For a common estimate `e_0,e_1,e_2 <= K r_M`, these become

```math
\|T_M'-S_M'\|
\le
\|M^{-s-1}\|(1+\|\log M\|)K r_M
```

and

```math
\|T_M''-S_M''\|
\le
\|M^{-s-1}\|(1+\|\log M\|)^2K r_M.
```

The public transport capstone is
`cutoffModel_differentiated_remainder_gate`.

## Exact-tail analytic input

For the exact scaled explicit-radius tail error

```math
\mathcal E_M(s)=M^{s+1}T_M(s)-A(s),
```

Lean proves holomorphy on the radius-`1/2` ball around every critical-line
point `s_0=1/2+it`. Each shifted block is dominated there by one summable
quadratic p-series.

On the radius-`1/4` Cauchy circle around `s_0`, the real part is at least
`1/4`, so the exact pointwise remainder estimate admits one uniform explicit
constant `C_h(t)`. Cauchy's estimate then gives

```math
\|\mathcal E_M(s_0)\|\le \frac{C_h(t)}{M},
```

```math
\|\mathcal E_M'(s_0)\|\le \frac{4C_h(t)}{M},
```

and

```math
\|\mathcal E_M''(s_0)\|\le \frac{32C_h(t)}{M}.
```

The public analytic reports are:

- `norm_nativeExplicitRadiusScaledTailError_critical_value_le`;
- `norm_nativeExplicitRadiusScaledTailError_critical_first_le`;
- `norm_nativeExplicitRadiusScaledTailError_critical_second_le`;
- `nativeExplicitRadiusScaledTailError_critical_three_bounds`.

The final theorem packages the three estimates. It does not add another
analytic premise.

## Completed chain

The formal chain is now

```math
\text{exact block holomorphy}
\Longrightarrow
\text{uniform critical Cauchy bound}
\Longrightarrow
(e_0,e_1,e_2)=O(1/M)
\Longrightarrow
\text{first/second logarithmic cutoff-jet control}.
```

No numerical table, fitted coefficient, selected height, or floating-point
minimum enters any implication.

## Remaining geometric frontier

The current theorems do not identify a moving finite minimizer, prove a
concrete reoptimized microscopic coefficient, or establish a cutoff-uniform
global coercivity constant. The empirical `M -> 2M` campaign remains discovery
provenance for those later geometric questions, not a theorem premise.

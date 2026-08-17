# Differentiated cutoff-remainder gate

## Purpose

The fixed-time critical tail theorem controls the scaled cutoff value. The next
coercivity step needs the scaled first and second derivatives as well. This
document separates the part now proved in Lean from the analytic estimates
still required.

## Exact transport now closed

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

Subtracting the corresponding model jets and applying the norm inequality now
yields kernel-checked bounds

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

For one common estimate `e_0,e_1,e_2 <= K r_M`, these become

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

The public Lean capstone is
`cutoffModel_differentiated_remainder_gate`.

## Analytic input still required

The exact cutoff tail must now be supplied with functions representing its
scaled first and second complex derivatives. The remaining proof must establish
explicit estimates for all three discrepancies against the chosen comparison
model:

```math
\|A_M-B_M\|,
\qquad
\|A_M'-B_M'\|,
\qquad
\|A_M''-B_M''\|.
```

A sufficient target is a common rate

```math
r_M=M^{-q}
```

with `q > 0`, or the sharper rate produced by a complete differentiated
three-term expansion. The new transport theorem then supplies the full
logarithmic loss automatically.

## Intended analytic route

The proof should stay independent of numerical tables.

1. Differentiate each explicit-radius block with respect to `s` before taking
   the infinite tail.
2. Bound the differentiated local Taylor remainders. Each derivative introduces
   at most one additional logarithmic factor in the integer variable.
3. Prove summability uniformly on the required critical compact set, permitting
   termwise differentiation of the tail.
4. Sum the first- and second-derivative remainders by an integral comparison.
5. Differentiate the scalar sum-versus-primitive defect and bound its two jets.
6. Combine the scalar and local contributions into explicit constants
   `K_0`, `K_1`, and `K_2` independent of `M`.
7. Feed those estimates into
   `cutoffModel_differentiated_remainder_gate` and then into the existing
   vanishing-error phase-floor theorem.

## Non-claims

The current interface does not identify a moving finite minimizer, prove a
cutoff-uniform global coercivity constant, or import the `M -> 2M` float64
campaign as a theorem premise. The numerical campaign remains evidence for
which analytic model to prove, not evidence substituted for the proof.

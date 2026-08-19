# Quantitative empirical jet gates

## Status

Gate 1 is fully closed on the current branch.

Release `v0.14.0` supplied the exact empirical-to-spectral camera crosswalk,
the all-order derivative-tail estimate, and the explicit six-camera finite
second-jet bound. The current branch finishes the quantitative consumption of
that result: it absorbs the logarithmic tail into a fixed inverse-cutoff
constant, constructs a cutoff-independent stack bound, derives fixed `C/M`
bounds for both curvature coordinates, and specializes the local Schur ledger
so that it no longer accepts an external `secondJetBound` argument.

Exactly four gates remain: denominator floors, the non-jet fixed constants,
concrete local positivity, and the compact-complement stitch. Humanity has
therefore been denied the opportunity to rename the same second-jet hypothesis
four times and call it progress.

## Fixed setting

Work at a fixed real `time` with

```math
G\left(\frac12+i\,\mathrm{time}\right)=0.
```

The exact camera and tail identities below do not require simplicity. The
existing quadratic moving-clock route later retains the explicit
nondegeneracy hypothesis

```math
G'\left(\frac12+i\,\mathrm{time}\right)\ne0.
```

This is the analytic multiplicity-one sector. The cutoff `M` and zero
multiplicity `m` are unrelated parameters.

## Gate 1: fully closed

The empirical camera geometry is identified exactly with the
`NativeCarrySpectralWeyl.Camera` geometry:

- radius sets;
- aligned centers;
- seeds;
- centered bracket blocks;
- finite characteristics;
- infinite characteristics.

Consequently, for every derivative order `r` and every cutoff satisfying
`Real.exp 2 <= M`, Lean proves

```math
\left\|
\chi_b^{(r)}\!\left(\frac12+it\right)
-
\chi_{b,M}^{(r)}\!\left(\frac12+it\right)
\right\|
\le
r!\,C_b(t)\,M^{-3/2}\log(M)^r.
```

At order two, the exact prefix-tail identity gives

```math
\chi_{b,M}''
=
\chi_b''-T_{b,M}'',
```

and hence

```math
\left\|T_{b,M}''\!\left(\frac12+it\right)\right\|
\le
2C_b(t)M^{-3/2}\log(M)^2.
```

The camerawise bounds are aggregated into the explicit Euclidean quantity
`empiricalFiniteSecondJetStackBound`, with

```math
\left\|
\texttt{finiteEmpiricalCameraSecondDerivativeStack}\;M\;
  \left(\frac12+it\right)
\right\|
\le
\texttt{empiricalFiniteSecondJetStackBound}\;M\;t.
```

The current branch then proves the elementary absorption

```math
M^{-3/2}\log(M)^2\le\frac{16}{M},
```

and defines fixed camerawise constants `C_{b,2}(t)` such that

```math
\left\|T_{b,M}''\!\left(\frac12+it\right)\right\|
\le
\frac{C_{b,2}(t)}{M}.
```

It follows that one fixed quantity `B_2(t)`, independent of `M`, satisfies

```math
\left\|
\texttt{finiteEmpiricalCameraSecondDerivativeStack}\;M\;
  \left(\frac12+it\right)
\right\|
\le B_2(t).
```

Combining this with the existing raw residual rate gives a fixed curvature
constant `C_curv(t)` with

```math
|a_M|\le\frac{C_{\mathrm{curv}}(t)}{M},
\qquad
|b_M|\le\frac{C_{\mathrm{curv}}(t)}{M}.
```

Finally, the concrete local Schur estimate is specialized to `B_2(t)`. Its
statement now receives only the positive denominator floor scheduled for Gate
2; no second-jet hypothesis survives downstream.

No individual cutoff, supplied height, floating-point certificate, or
simplicity assumption is used in the second-jet analysis itself.

## Gate 2: denominator floors

The next stage must derive cutoff-independent eventual positive floors for:

```math
|\kappa_M|,
\qquad
|\kappa_M-a_M|,
\qquad
|E_M|.
```

The limiting energy floor must come from

```math
\rho+\frac{x_M^2}{\kappa}\ge\rho>0,
```

not from a fitted finite-cutoff value.

## Gate 3: remaining fixed inverse-cutoff constants

The curvature contribution of the second jet is already closed:

```math
|a_M|,|b_M|\le\frac{C_{\mathrm{curv}}(t)}{M}.
```

The remaining residual, corrected first-jet, pairing, clock-Gram, gradient,
and energy ledgers must be assembled into constants independent of `M` so that

```math
|E_M-E_{0,M}|\le\frac{C_E}{M},
```

```math
|g_M-2x_M|\le\frac{C_g}{M},
```

```math
|c_M-\kappa|\le\frac{C_c}{M}.
```

Any remaining logarithmic factors must be absorbed through proved inequalities,
not through numerical cutoff inspection. The second jet is no longer among
those obligations.

## Gate 4: concrete local positivity

The fixed bounds and floors must be supplied to the existing primitive
microscopic transfer theorem to obtain

```math
\exists c>0,\quad
\forall^{\infty}M,\quad
c\le
\texttt{finiteEmpiricalCorrectedMicroscopicCoercivity}\;M\;\mathrm{time}.
```

All assumptions remain visible, including the presented critical simple zero.

## Gate 5: compact complement and strip stitching

Only after the local theorem is closed should the continuation prove:

1. a cutoff-independent microscopic region;
2. a cutoff-independent positive complementary region;
3. exact coverage of the empirical critical strip;
4. the final application of the existing stitching and confinement capstones.

A changing controlling valley or a cutoff-dependent cover does not discharge
this gate.

## Scope firewall

The quantitative continuation does not:

- redefine the Genuine or native zero predicate;
- import numerical zero locations into Lean;
- use a floating-point certificate as a proof premise;
- replace the carry-geometric route by the lateral arithmetic readout;
- claim a Hermite-Biehler, de Branges, or self-adjoint height realization;
- promote the multiplicity-one quadratic theorem to arbitrary multiplicity;
- promote local positivity to global confinement before the compact complement
  is proved;
- alter the immutable `v0.12.0` theorem registry or claim ledger.

## Validation discipline

GitHub Actions on the exact commit is the validation authority. Every promoted
commit must preserve:

- the pinned dependency lock;
- the no-`sorry`/no-`axiom` source audit;
- the public build with warnings as errors;
- the ordered kernel audit;
- the foundational dependency allowlist;
- the Markdown and publication checks.

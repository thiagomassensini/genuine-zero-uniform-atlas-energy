# Quantitative empirical jet gates

## Status

Gate 1 was closed and packaged in release `v0.14.0`.

The release proves the exact empirical-to-spectral camera crosswalk, transports
the all-order derivative-tail estimate, and derives the explicit six-camera
finite second-jet bound. Gates 2 through 5 are intentionally separated into a
subsequent PR so this release does not pretend that denominator floors,
cutoff-independent constants, local positivity, and the compact complement are
the same theorem wearing different hats.

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

## Gate 1: closed in `v0.14.0`

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

No individual cutoff, supplied height, or floating-point certificate is used.

## Gate 2: denominator floors

The next PR must derive cutoff-independent eventual positive floors for:

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

## Gate 3: fixed inverse-cutoff constants

The explicit residual, first-jet, pairing, energy, and curvature estimates must
be converted into constants independent of `M`:

```math
|E_M-E_{0,M}|\le\frac{C_E}{M},
```

```math
|g_M-2x_M|\le\frac{C_g}{M},
```

```math
|c_M-\kappa|\le\frac{C_c}{M}.
```

Remaining logarithmic factors must be absorbed through proved eventual
inequalities, not through numerical cutoff inspection.

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

Only after the local theorem is closed should the next PR prove:

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

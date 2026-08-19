# Quantitative empirical jet gates

## Status

This document is the working contract for the quantitative continuation after
`v0.13.0`.

The preceding release closes the exact moving-clock algebra, the concrete
finite residual/first-jet/pairing/energy data, the primitive Schur ledger, and
the abstract implication

```math
\text{three explicit } C_i/M \text{ channels}
\Longrightarrow
\text{eventual positive microscopic coercivity}.
```

The present branch must discharge those quantitative hypotheses for the actual
six-camera finite operator. It must not replace them with a new certificate,
a numerical premise, or an equivalent restatement of the final confinement
claim.

## Fixed hypotheses and target

Work at a fixed real `time` such that

```math
G\left(\frac12+i\,\mathrm{time}\right)=0
```

and retain the explicit simplicity/nondegeneracy hypothesis

```math
G'\left(\frac12+i\,\mathrm{time}\right)\ne0.
```

For the finite corrected empirical data, write

```math
E_M
=
\text{finite corrected reoptimized energy},
```

```math
g_M
=
\text{finite corrected radial gradient},
```

```math
c_M
=
\text{finite local Schur coefficient}.
```

Let `x_M` be the finite phase projection, and let the limiting admissible data
be `(kappa,rho,alphaSq)`. The local target is a theorem of the form

```math
\exists c>0,\quad
\forall^{\infty} M,\quad
c\le
c_M-\frac{g_M^2}{4E_M}.
```

The existing `MicroscopicJetTransfer` and `MicroscopicPrimitiveJetBounds`
modules already reduce this to explicit primitive estimates. This branch must
supply those estimates rather than duplicate the quotient algebra.

## Gate 1: explicit finite second-jet bound

Construct a camerawise bound for

```math
\left\|\chi''_{b,M}\left(\frac12+i t\right)\right\|.
```

The proof must use the already formalized exact cutoff-tail identity and the
value/first/second Cauchy bounds for the scaled tail. Transport through
`M^{-s-1}` must keep the exact logarithmic losses visible. The expected shape
is

```math
M^{-3/2}
\left(A_{b,2}(t)
+2\log(M)A_{b,1}(t)
+\log(M)^2A_{b,0}(t)
+\frac{R_{b,2}(M,t)}{M}
\right).
```

The six camerawise estimates must then be aggregated into one Euclidean stack
bound for `finiteEmpiricalCameraSecondDerivativeStack`.

No individual cutoff is to be formalized. The statement must be uniform in
`M` once `1 <= M` is supplied.

## Gate 2: finite denominator floors

Derive eventual positive floors from the limiting positive model quantities
and the explicit perturbation bounds.

The required floors are:

1. a finite clock-Gram floor

```math
0<\kappa_{\mathrm{floor}}
\le
\left|\kappa_M\right|;
```

2. a temporal Schur-denominator floor

```math
0<d_{\mathrm{floor}}
\le
\left|\kappa_M-a_M\right|;
```

3. a corrected finite-energy floor

```math
0<E_{\mathrm{floor}}
\le
|E_M|.
```

The limiting model-energy floor should come directly from

```math
\rho+\frac{x_M^2}{\kappa}\ge\rho>0,
```

not from a fitted cutoff value.

## Gate 3: fixed inverse-cutoff constants

Convert the explicit residual, first-jet, pairing, energy, and curvature
bounds into fixed constants independent of `M`:

```math
|E_M-E_{0,M}|\le\frac{C_E}{M},
```

```math
|g_M-2x_M|\le\frac{C_g}{M},
```

```math
|c_M-\kappa|\le\frac{C_c}{M}.
```

Logarithmic remnants must be absorbed by proved elementary inequalities, for
example eventual bounds for expressions of the form

```math
\frac{\log(M)^j}{M^q}.
```

The constants may depend on the fixed `time` and the six-camera geometry, but
not on the cutoff.

## Gate 4: concrete local positivity

Feed the three fixed bounds and the denominator floors into
`PhaseProjectionData.eventually_positive_quadraticMicroscopicCoercivity_of_primitive_bounds`.

The resulting theorem should specialize the abstract sequence statement to

```math
finiteEmpiricalCorrectedMicroscopicCoercivity M time.
```

The expected public endpoint is:

```math
\exists c>0,\quad
\forall^{\infty}M,\quad
c\le
finiteEmpiricalCorrectedMicroscopicCoercivity\;M\;time.
```

All assumptions must remain visible. In particular, this theorem is local at a
presented critical simple zero until the regional argument is supplied.

## Gate 5: compact complement and strip stitching

Only after the local theorem is kernel-checked should the branch attack the
complementary region.

The final quantitative stitch requires:

1. one microscopic region controlled by the local jet theorem;
2. one complementary region with an eventual positive coercivity certificate;
3. an exact coverage theorem for the empirical critical strip;
4. application of the existing strip-stitching and confinement capstones.

The region and constants must be cutoff-independent. A changing controlling
valley or a cutoff-dependent cover does not discharge this gate.

## Proposed module order

1. `EmpiricalFiniteSecondJetBound.lean`
2. `EmpiricalFiniteDenominatorFloors.lean`
3. `EmpiricalQuantitativeJetConstants.lean`
4. `EmpiricalMicroscopicPositiveGate.lean`
5. `EmpiricalStripQuantitativeStitch.lean`

Each module should compile before the next is introduced. The public root
library should import a module only after its claims are stable.

## Scope firewall

This branch does not:

- redefine the Genuine or native zero predicate;
- import numerical zero locations into Lean;
- use a floating-point certificate as a proof premise;
- replace the carry-geometric route by the lateral arithmetic readout;
- claim a Hermite-Biehler, de Branges, or self-adjoint height realization;
- promote the local simple-zero theorem to global confinement before the
  compact-complement certificate is proved;
- alter the immutable `v0.13.0` theorem registry or claim ledger retroactively.

The separate height-operator laboratories remain research probes. Their own
documented gate is global one-sided factorization and self-adjoint-limit
realization, not the finite empirical coercivity calculation performed here.

## Validation discipline

GitHub Actions on the exact branch commit is the validation authority.

Every promoted commit must preserve:

- the pinned dependency lock;
- the no-`sorry`/no-`axiom` source audit;
- the public build with warnings as errors;
- the ordered kernel audit;
- the foundational dependency allowlist;
- the Markdown and publication checks.

The branch remains a draft until all five gates above are either closed or
explicitly separated into a subsequent PR without overstating the result.

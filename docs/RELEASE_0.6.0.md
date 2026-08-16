# Genuine Zero Uniform Atlas Energy v0.6.0

## Exact empirical camera family

This release formalizes the six cutoff cameras used by the numerical operator:

```text
label    2  3  4  5  6  7
period   4  3  4  5  6  7
S2       1  1  5  5 14 14
```

The cameras labelled four and six retain their antipodal radii two and three.
They are therefore not identified with CPFormal's natural even cameras, which
omit the middle residue class. The new full-even continuation restores those
channels explicitly.

## Six-camera cutoff operator

Lean now defines the seed, centered blocks, finite prefixes, infinite
characteristics, unresolved tails, camera-indexed vectors, and collective raw
energy for the complete empirical family. On `re(s) > -1`, every component is
absolutely summable and splits exactly into finite prefix plus tail.

At a common critical-line Genuine zero, the six finite residues are exactly
the negative unresolved tails. For each fixed time, every amplitude is bounded
by a displayed time-dependent multiple of `M^(-3/2)`, and the collective raw
energy is bounded by the corresponding sum of squared majorants of order
`M^(-3)`.

## Proposed leading-tail model and logarithmic phase

For independent period `b` and retained radius `h`, the local Taylor
calculation identifies the candidate tail-model coefficient

```math
A^{\mathrm{tail}}_{b,h}(s)=sS_2(h)b^{-s-2}.
```

On the critical line, this candidate cutoff monomial has the exact phase
identity

```math
M^{-s-1}=M^{-3/2}
\exp(-it\log M).
```

The proposed finite resonant residue has model vector
`A_res = -A_tail`. Lean proves that identity coordinatewise and checks the
exact collective squared norm

```math
\lVert A^{\mathrm{res}}(t)\rVert^2
=
\left\lVert\frac12+it\right\rVert^2
\frac{132244271}{1778112000}.
```

The analytic remainder theorems in this release are stated only at the strength
actually proved by the kernel: the local block remainder is explicit, while
the global tail remainder is not bounded and scaled-tail convergence is not
proved. The model must not be read as a numerical certificate for a Genuine
zero or as the derivative-level estimate required by the finite
reoptimization step.

## Structural projected lower bound

The finite-residue model vector and limiting complex-derivative model direction
are placed in the complex Euclidean six-camera space. The equal-period pair
C2/C4 has residue-model coordinates in the ratio five, while its limiting
factors provably fail to have that ratio on the critical line. Therefore, when
`Re(s)=1/2` and the Genuine derivative is nonzero, the two vectors are not
collinear. This release does not identify the complex-derivative model
direction with the real time derivative of the empirical stack.

Lean derives strict Cauchy--Schwarz, positive derivative-direction norm,
positive residue-model amplitude, and a strictly positive transverse Gram
remainder `rho`. The algebraic phase-projection model is then bounded below,
for every logarithmic phase, by the symbolic positive floor

```math
c_{\mathrm{floor}}
=
\frac{\kappa\rho}{\lVert A^{\mathrm{res}}\rVert^2}>0.
```

If a supplied coefficient sequence approximates the algebraic model with
`C/M` error and a separate exact argument proves that this floor is greater
than four, Lean proves that the supplied sequence is eventually at least four.
No theorem identifies that sequence with the concrete reoptimized finite
operator.

## Conditional passage to the limit

Both global and arbitrary-region interfaces now prove that an eventual cutoff-
uniform coercivity inequality passes to a supplied pointwise limiting energy.
The regional interface is applicable to a compact region but does not encode
or certify one. The finite lower-bound and convergence hypotheses remain
explicit assumptions.

## Source-complete numerical evidence

The 56-job float64 campaign, its approximately 155 KiB result bundle, and the
exact eight-file runtime import closure plus aggregation script are included.
They are locked by source commit, per-file hashes, runtime versions, bundle
hash, camera geometry, exact grid, and result counts in
`audit/empirical-evidence.json`. Static audit parses the source closure and all
56 archived JSON results, cross-checks their statuses against the manifest,
verifies the bundle byte for byte, and enforces the status
`NUMERICAL_FLOAT64_EVIDENCE_NOT_KERNEL_CHECKED`.

Under its float64 guard, the campaign classified the coefficient-four jobs at
cutoffs 8192, 12288, and 16384 as
`CERTIFIED_NONNEGATIVE_ON_COMPACT`. Results at larger cutoffs were limited by
that declared guard. These facts motivate the proposed leading-tail and
coercivity interfaces; they are not interval certificates or Lean theorems.

## Public audit surface

Release `0.6.0` contains:

- 132 ordered public theorem dependency reports;
- 17 claims marked `KERNEL_CHECKED`;
- exact CPFormal and Mathlib dependency locks;
- one separately validated 56-job empirical evidence record whose status is
  explicitly non-kernel;
- no local `sorry`, `admit`, `axiom`, or `unsafe` declaration;
- a foundational dependency allowlist restricted to `propext`,
  `Classical.choice`, and `Quot.sound`.

## Exact scope boundary

Release `0.6.0` does not claim:

- that a recorded decimal is exactly a zero of `genuineContinuation`;
- simplicity or a certified numerical lower bound for its derivative;
- a global bound for `nativeExplicitRadiusTailRemainder` or scaled-tail
  convergence;
- the derivative and Hessian remainder estimates needed to prove the concrete
  finite `C/M` reoptimization error;
- an identification of the supplied coefficient sequence with the concrete
  reoptimized finite operator;
- a kernel-checked interval certificate for the complement of the local zero
  valleys;
- the unconditional numerical inequality `c >= 4` for every sufficiently
  large cutoff.

The release closes the faithful six-camera geometry, exact operator/tail
packaging, full-even semantic gap, local remainder and candidate model
geometry, exact monomial phase, strict positivity of the symbolic algebraic
projection floor under a nonzero-derivative hypothesis, and conditional
global/arbitrary-region limit interfaces.

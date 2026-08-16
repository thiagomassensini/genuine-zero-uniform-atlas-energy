# Operator Lower-Bound Status

This page separates three different statements that must not be conflated:
the kernel-checked structural lower bound, the finite numerical campaign, and
the still-open numerical constant for the concrete operator.

## Kernel-checked closure

Lean proves the following facts for the faithful empirical stack C2--C7:

- the exact periods and retained radii, including the C4/C6 antipodal
  channels;
- absolute convergence and exact finite-prefix plus cutoff-tail identities;
- the complete stack and collective raw-energy tail identities at a common
  zero;
- for each fixed critical time, displayed time-dependent `M^(-3/2)` amplitude
  and `M^(-3)` collective-energy upper bounds;
- the exact phase `M^(-3/2) exp(-it log M)` of the proposed tail monomial and
  the rational collective model geometry coefficient
  `132244271/1778112000`;
- the accumulated local cubic Taylor remainder is bounded explicitly by
  `O(M^(-5/2))`, hence by `O(1/M)` after the natural critical rescaling;
- the coordinate identity between the proposed tail model `+A_tail` and finite
  resonant-residue model `A_res = -A_tail`, together with their common squared
  norm;
- non-collinearity of the finite-residue model vector and limiting
  complex-derivative model direction when `Re(s)=1/2` and the Genuine
  derivative is nonzero, without identifying that model direction with the
  real time derivative of the empirical stack;
- strict positivity of the transverse projection remainder `rho` and of the
  phase-independent symbolic floor;
- an eventual supplied coefficient sequence at least four from two explicit
  hypotheses: a phase floor strictly greater than four and a uniform `C/M`
  approximation to the algebraic phase model;
- passage of an eventual cutoff-uniform coercivity inequality to a pointwise
  limiting energy, globally or on a fixed region.

The last two bullets are implication theorems. They do not discharge their
quantitative hypotheses for the concrete operator.

## Locked numerical evidence

The external campaign scanned the compact rectangle
`[0.49,0.51] x [10,40]` on seven cutoffs and eight candidate coefficients.
Among 56 jobs, the campaign classified 18 as
`CERTIFIED_NONNEGATIVE_ON_COMPACT` under its float64 guard, two as
counterexamples, and 36 as unresolved resource-limit results. The
coefficient-four jobs received that guarded campaign status for cutoffs 8192,
12288, and 16384.

The campaign used float64 center jets with an explicit guard and independent
long-double witness reevaluation. It was not interval arithmetic and is not a
Lean proof object. The exact provenance is locked in
[`audit/empirical-evidence.json`](../audit/empirical-evidence.json).

## Why `phaseFloor > 4` is not a theorem

Exploratory calculations placed the model floor above four, but their inputs
and method are not part of the locked 56-job evidence bundle. This repository
therefore publishes no decimal floor. Proving `phaseFloor > 4` requires exact
enclosures for a Genuine zero, its derivative, and the relevant projection,
not another floating-point evaluation.

The remaining analytic bridge must provide:

1. a proof object locating a Genuine zero in an exact interval;
2. a certified nonzero derivative and quantitative derivative lower bound;
3. a bound for the remaining complex Euler defect, then the complete global
   tail remainder and uniform cutoff expansions for the characteristic and
   the derivatives used by the reoptimized clock;
4. an explicit `C/M` bridge from the concrete reoptimized coefficient to the
   algebraic phase model;
5. a certified compact-complement argument covering transitions between zero
   valleys.

Until those objects exist, the honest machine-checked conclusion is a strictly
positive symbolic model floor when `Re(s)=1/2` and the Genuine derivative is
nonzero, plus conditional coefficient-sequence and limit theorems. It is not
the unconditional numerical statement `c >= 4` for the full concrete
operator.

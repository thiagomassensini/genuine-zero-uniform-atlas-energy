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
- the exact phase `M^(-3/2) exp(-it log M)` of the leading tail monomial and
  the rational collective model geometry coefficient
  `132244271/1778112000`;
- the complete named scalar tail remainder, combining the leading-series
  defect with the accumulated local Taylor remainder, is bounded by an
  explicit `K M^(-5/2)`; after critical rescaling the cutoff tail differs from
  its exact leading coefficient by at most `K/M`;
- the naturally scaled collective tail energy is exactly `M^3` times the raw
  tail energy, and the scaled energy differs from the exact coefficient norm
  by the displayed sum of camerawise terms
  `2 ||A_b|| K_b/M + K_b^2/M^2`;
- consequently the collective tail energy has the explicit expansion

  ```math
  E_M(t)=
  \left\lVert\frac12+i t\right\rVert^2
  \frac{132244271}{1778112000}M^{-3}
  +O_t(M^{-4}),
  ```

  with a concrete inequality replacing the unnamed `O_t`; at a common
  six-camera resonance the same expansion holds for the finite raw energy;
- the coordinate identity between the tail coefficient `+A_tail` and finite
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
- the faithful finite C2--C7 collective raw energy converges pointwise to
  the concrete infinite empirical energy throughout `sigma > -1`;
- a Genuine zero in the strip annihilates that concrete limiting energy;
- regional, strip-wide, and global capstones now combine those concrete
  facts with a supplied eventual positive finite coercivity certificate to
  force `sigma = 1/2`.

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
3. an explicit bridge from the concrete moving minimizer/reoptimized
   coefficient to the algebraic phase model, using the now-proved value and
   first/second derivative tail bounds;
4. an eventual positive finite coercivity certificate on the desired region;
5. a certified compact-complement argument covering transitions between zero
   valleys.

Until those objects exist, the honest machine-checked conclusion is a strictly
positive symbolic model floor when `Re(s)=1/2` and the Genuine derivative is
nonzero, plus fixed-time tail/energy asymptotics, the concrete pointwise energy
limit, and conditional confinement theorems whose finite coercivity premise is
still explicit. It is not the unconditional numerical
statement `c >= 4` for the full concrete operator.

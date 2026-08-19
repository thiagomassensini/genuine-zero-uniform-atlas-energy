# v0.14.0 — Exact six-camera second-jet crosswalk

Version `0.14.0` closes the first quantitative continuation gate after
`v0.13.0`: the finite empirical second derivative is now connected exactly to
the infinite camera characteristic and to an explicit decaying cutoff tail.
The release preserves the Genuine-first and native-first architecture and does
not import a numerical height, zero table, or floating-point certificate into
Lean.

## Exact camera geometry crosswalk

The six empirical cameras are identified with the corresponding
`NativeCarrySpectralWeyl.Camera` objects at the level of their actual finite
geometry:

- the radius sets agree exactly;
- the aligned centers agree, including the special period-four camera labelled
  two;
- each seed agrees;
- each centered bracket block agrees;
- the complete finite and infinite characteristic functions agree.

This is an equality of functions, not merely a comparison of asymptotic
coefficients.

## All-order derivative-tail transport

The existing spectral-Weyl derivative theorem can therefore be reused without
rebuilding a second Cauchy argument. For every derivative order `r`, every
empirical camera `b`, and every cutoff satisfying `exp(2) <= M`, Lean proves

```math
\left\|
\chi_b^{(r)}\!\left(\frac12+it\right)
-
\chi_{b,M}^{(r)}\!\left(\frac12+it\right)
\right\|
\le
r!\,C_b(t)\,M^{-3/2}\log(M)^r.
```

The constant depends on the fixed camera and time, not on the cutoff.

## Exact second-jet ledger

The prefix-tail identity is differentiated twice as an identity of analytic
functions:

```math
\chi_{b,M}''
=
\chi_b''-T_{b,M}''.
```

Consequently,

```math
\left\|T_{b,M}''\!\left(\frac12+it\right)\right\|
\le
2C_b(t)M^{-3/2}\log(M)^2,
```

and

```math
\left\|\chi_{b,M}''\!\left(\frac12+it\right)\right\|
\le
\left\|\chi_b''\!\left(\frac12+it\right)\right\|
+
2C_b(t)M^{-3/2}\log(M)^2.
```

The six camerawise inequalities are aggregated into one explicit Euclidean
bound for `finiteEmpiricalCameraSecondDerivativeStack`.

## Multiplicity firewall

The camera crosswalk, prefix-tail identity, and derivative estimates do not
assume that the presented Genuine zero is simple. Simplicity enters only later,
when the existing quadratic moving-clock route requires a nonzero first jet.
Thus this release does not confuse the cutoff `M` with the analytic
multiplicity `m`:

```math
m=1
\quad\text{is the quadratic sector,}
```

while a zero of multiplicity `m>1` requires a leading energy analysis of order
`2m` rather than a false quadratic floor.

## Remaining quantitative gates

The following obligations are deliberately moved to the next PR:

- eventual positive floors for the finite clock Gram, corrected energy, and
  temporal Schur denominator;
- absorption of logarithmic remnants into fixed cutoff-independent `C/M`
  constants;
- the concrete local microscopic-positivity theorem;
- the cutoff-independent compact complement and strip-wide stitching.

Closing the second-jet gate does not by itself promote local simple-zero
coercivity to an unconditional global confinement theorem.

## Audit and publication

The promoted theorem registry and claim ledger remain the immutable `0.12.0`
snapshots: `156` ordered theorem IDs and `24` claims. Version `0.14.0` adds two
public-build-checked modules without relabelling them as a new unconditional
claim:

- `EmpiricalCameraHigherDerivativeCrosswalk`;
- `EmpiricalFiniteSecondJetBound`.

GitHub Actions validates the exact checkout, pinned dependency lock, canonical
bridge, frontier probe, static publication audit, full public library with
warnings as errors, ordered kernel audit, and foundational axiom allowlist. A
successful audit on `main` triggers the audited `v0.14.0` tag and GitHub release
used by the Zenodo integration.

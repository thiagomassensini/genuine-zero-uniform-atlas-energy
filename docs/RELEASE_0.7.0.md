# Release 0.7.0 — Sharp cutoff tail and collective energy asymptotic

This release turns the faithful empirical C2--C7 cutoff observation into a
kernel-checked fixed-time asymptotic with an explicit remainder.

## Exact critical tail expansion

For every empirical camera, positive cutoff `M`, and critical parameter

```math
s_t=\frac12+i t,
```

the unresolved cutoff tail has the sharp leading model

```math
T_{b,h,M}(s_t)=C_{b,h}(s_t)M^{-s_t-1}+R_{b,h,M}(t),
```

with a completely explicit cutoff-independent constant `K_{b,h}(t)` such that

```math
\lVert R_{b,h,M}(t)\rVert\le K_{b,h}(t)M^{-5/2}.
```

Equivalently,

```math
\left\lVert M^{s_t+1}T_{b,h,M}(s_t)-C_{b,h}(s_t)\right\rVert
\le \frac{K_{b,h}(t)}{M}.
```

The proof separates and controls both contributions: the scalar
sum-versus-primitive defect and the accumulated local Taylor remainder.

## Collective raw-energy expansion

Let `A(t)` be the faithful six-camera leading coefficient vector. Lean proves
that the naturally scaled collective tail energy is exactly `M^3` times the
unscaled tail energy and obtains the explicit quadratic error estimate

```math
\left|M^3E_M(t)-\lVert A(t)\rVert^2\right|
\le
\sum_b\left(
  \frac{2\lVert A_b(t)\rVert K_b(t)}{M}
  +\frac{K_b(t)^2}{M^2}
\right).
```

Therefore

```math
E_M(t)=\lVert A(t)\rVert^2M^{-3}+O_t(M^{-4})
```

with the remainder displayed as an actual inequality rather than an unnamed
asymptotic symbol.

For the exact C2--C7 geometry,

```math
\lVert A(t)\rVert^2
=
\left\lVert\frac12+i t\right\rVert^2
\frac{132244271}{1778112000}.
```

At a common six-camera resonance, the finite raw characteristic energy is
exactly the unresolved tail energy, so the same leading coefficient and
explicit `O_t(M^{-4})` remainder apply to the finite operator.

## Public audit surface

Release `0.7.0` contains:

- 138 ordered public theorem reports;
- 20 claims marked `KERNEL_CHECKED`;
- three new public capstones:
  - `empiricalScaledCollectiveCutoffTailEnergy_eq`;
  - `abs_empiricalCollectiveCutoffTailEnergy_sub_leading_div_cube_le`;
  - `empiricalSixCameraCriticalRawEnergy_explicit_remainder`.

The locked `0.6.0` theorem registry is extended by
`audit/theorem-registry-0.7.0.json`, preserving the previous numbering while
adding `GZUAE-136` through `GZUAE-138`.

## Deliberate boundary

This release is a fixed-time energy theorem. It does not yet prove:

- expansions for the sigma or time derivatives of the finite characteristic;
- Hessian or Schur-envelope expansions with explicit cutoff error;
- the finite time-reoptimization bridge;
- an unconditional numerical floor such as `c >= 4` for the full compact
  coercivity problem;
- passage of that concrete lower bound to the infinite limiting energy.

Those are the next analytic gates. No floating-point minimum, decimal zero, or
empirical branch-and-bound output is imported as a proof object.

## Reproducibility

The release is produced only after the exact merged `main` commit passes:

```bash
lake build --wfail GenuineZeroUniformAtlasEnergy
lake build --wfail GenuineZeroUniformAtlasEnergy.Audit
./scripts/audit.sh
```

The audit cross-checks the combined theorem registry, ordered kernel
dependency reports, complete claim coverage, source lock, release metadata,
and the foundational axiom allowlist.

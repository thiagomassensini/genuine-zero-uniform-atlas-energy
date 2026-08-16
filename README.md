# Genuine Zero Uniform Atlas Energy

Lean 4 formalization of one positional carry geometry, one native/Genuine zero,
one optimal energy budget, and the faithful empirical six-camera cutoff
operator with a structural projected coercivity floor.

The construction starts before any zero is considered. At real phase time
`t`, the native positional wave is

```math
u_t(n)
=
n^{-1/2}
\bigl(\cos(-t\log n),\sin(-t\log n)\bigr).
```

Lean proves its quadratic energy directly:

```math
\lVert u_t(n)\rVert^2=n^{-1}.
```

More generally, for every positional base `b > 1`, positive depth `k`, and
arbitrary real rotation angle, Lean checks the exact rigidity theorem

```math
\text{quadratic shell energy}=b^{-k}
\quad\Longleftrightarrow\quad
\sigma=\frac12.
```

Thus the amplitude `n^(-1/2)` is the square-root realization of inverse carry
mass. The real coordinate pair and its complex notation represent the same
quantity; complex packaging preserves every finite camera computation.

## One computation and one zero

For every finite cutoff, Lean proves that packaging the real native resultant
produces literally the Genuine finite Dirichlet chart:

```math
\mathrm{pack}
\bigl(\mathrm{NativeChart}_{3,M}(t)\bigr)
=
\mathrm{GenuineChart}_{3,M}\left(\frac12+it\right).
```

Passing through the already-proved common limit gives

```math
\boxed{
\mathrm{NativeBoundaryCloses}_3(t)
\iff
\mathrm{Genuine}\left(\frac12+it\right)=0.
}
```

This is the same vanishing computation written in real-pair and
complex-coordinate notation.

## One uniform atlas-energy budget

For a cutoff `M` and finite prime atlas `S`, define the native seeded TFVD
radial-defect energy

```math
E_{M,S}(t)
=
\sum_{p\in S}
\frac{\mathcal O_{p,M}(\frac12+it)^2}{p-1}.
```

The observable contains the transverse factor

```math
p^{\delta}-p^{-\delta},
\qquad
\delta=\mathrm{Re}\left(\frac12+it\right)-\frac12=0.
```

Consequently Lean proves, at every time and before assuming a zero,

```math
\boxed{
\forall M,\ \forall S,
\qquad E_{M,S}(t)=0.
}
```

A real number `C` is a uniform budget when it bounds every positive cutoff and
every finite atlas. Lean then proves

```math
C\text{ is a uniform budget}
\iff
C\ge0,
```

and

```math
C\text{ is the optimal budget}
\iff
C=0.
```

Hence the optimal budget exists uniquely. A common native/Genuine zero
inherits that structural budget; the zero does not create it or select the
quadratic amplitude.

The zero value here belongs to the **radial-defect ledger**. The underlying
native wave has energy `n⁻¹`; it is the deviation from that native quadratic
geometry that vanishes.

## The tilted center left after boundary telescoping

Let the finite tilted center be the difference between the independently
defined total coupled Green flux and its coupled signed boundary:

```math
\mathcal C_{p,M}(s)
=
\mathcal F_{p,M}(s)-\mathcal B_M(s).
```

Lean proves the exact factorization

```math
\boxed{
\mathcal C_{p,M}(s)
=
D_p\!\left(\mathrm{Re}(s)-\frac12\right)
P_M(s),
}
```

where `P_M(s) > 0` for every positive cutoff in the Genuine strip. Therefore,
for an odd prime camera and an admissible tilt center,

```math
\boxed{
\mathcal C_{p,M}(s)=0
\iff
\mathrm{Re}(s)=\frac12
\iff
\mathrm{Tilt}_{p}(\mathrm{Re}\,s)=0
\iff
\mathrm{BranchDefect}_{p}(\mathrm{Re}\,s)=0.
}
```

In particular, a nonzero carry tilt produces a nonzero surviving center at
every nonempty cutoff; the positive pairing rules out hidden cancellation.

At the common native/Genuine zero, the boundary already telescopes. Lean then
proves

```math
\mathcal F_{p,M}(s)\longrightarrow0
\iff
\mathrm{Tilt}_{p}(\mathrm{Re}\,s)=0.
```

The zero predicate is not changed when the radial coordinate is varied. Lean
also records the complementary off-equilibrium statement. If a Genuine zero
in the strip is presented with `Re(s) ≠ 1/2`, then

```math
\mathcal B_M(s)\longrightarrow0,
\qquad
\mathcal C_{p,M}(s)\ne0\quad(M>0),
\qquad
\mathcal F_{p,M}(s)\not\longrightarrow0.
```

Thus the same zero remains a zero. Boundary telescoping removes the legs, and
the surviving Green center exposes the nonzero tilt; the diagnostic channel
does not redefine or revoke the zero.

On the native parameter `s = 1/2 + i t`, the quadratic carry geometry has
already annihilated that tilt and its quadratic branch defect. Consequently
the boundary tends to zero, the center vanishes at every cutoff, and the total
flux tends to zero. This adds no new kind of zero: it identifies the center
that detects departure from the same native/Genuine zero geometry.

## Concrete transverse camera geometry

For every odd prime camera `p` and finite cutoff `M`, Lean defines the entire
characteristic

```math
\Chi_{p,M}(s)
=
\mathrm{FiniteChart}_{p,M}(n\mapsto n^{-s}).
```

At `s = sigma + i*time`, this is literally the complex packaging of the
primitive real camera. Its two real tangent directions obey

```math
\partial_t\Chi_{p,M}
=
i\,\partial_\sigma\Chi_{p,M}.
```

Multiplication by `i` is the real quarter-turn `J(x,y)=(-y,x)`. Therefore the
radial and angular tangents have equal Euclidean norm and zero pairing.

The associated raw visibility is

```math
E_{p,M}(\sigma,t)
=
\lVert\Chi_{p,M}(\sigma+i t)\rVert_{\mathbb R^2}^2.
```

It is exactly the primitive camera's Euclidean resultant energy. No division
by cutoff, coordinate count, state norm, or bracket-coordinate energy is used.
Writing

```math
\kappa=\lVert\Chi'\rVert^2,
\qquad
a=\langle\Chi,\Chi''\rangle,
\qquad
b=\langle\Chi,J\Chi''\rangle,
```

Lean proves

```math
D^2E_{p,M}
=
2\begin{pmatrix}
\kappa+a & b\\
b & \kappa-a
\end{pmatrix}.
```

The same jet has trace `4*kappa`, determinant
`4*(kappa^2-a^2-b^2)`, explicit algebraic eigenvalues, and a Schur-envelope
coercivity coefficient. At an exact finite primitive-camera zero, `a=b=0`:
the Hessian is isotropic, the first-order minimizing-clock slope is zero, and
both algebraic eigenvalues equal `2*kappa`.

This closes the finite componentwise operator-to-jet bridge.

## Faithful six-camera cutoff operator

The empirical family is indexed by labels `2,3,4,5,6,7`, with periods
`4,3,4,5,6,7` and second radius moments `1,1,5,5,14,14`. The cameras labelled
four and six retain their antipodal radii two and three. Lean models those
channels directly; it does not replace them by the natural even-camera
geometry that omits the middle channel.

For each camera Lean defines its seed, finite prefix, infinite characteristic,
unresolved tail, and raw quadratic energy. At a common critical-line Genuine
zero, the complete finite stack is exactly the negative tail stack and

```math
E_M
=
\sum_{b=2}^{7}\lVert\mathrm{Tail}_{b,M}\rVert^2.
```

For each fixed time, every component has a displayed time-dependent
`M^(-3/2)` amplitude majorant and the collective energy has the corresponding
`M^(-3)` upper bound. The restored full-even continuation proves that the
C4/C6 characteristics use their faithful factors times the same
`genuineContinuation`, so the common-zero hypothesis is not an independent
numerical assumption.

## Proposed tail model and projected floor

For period `b` and retained radius `h`, the local Taylor calculation proposes
the tail-model coefficient

```math
A^{mathrm{tail}}_{b,h}(s)=sS_2(h)b^{-s-2}.
```

Lean proves an explicit local remainder of order `(k+1)^(-7/2)` and the exact
phase of the candidate cutoff monomial

```math
M^{-s-1}=M^{-3/2}\exp(-it\log M),
```

The finite resonant residue uses the opposite model vector
`A_res = -A_tail`. Lean proves this coordinatewise and proves that its
collective squared norm is

```math
\lVert A^{\mathrm{res}}(t)\rVert^2
=
\left\lVert\frac12+it\right\rVert^2
\frac{132244271}{1778112000}.
```

The global remainder after summing this local model is still an explicit
named object, but this release does not yet prove its `O(M^(-5/2))` bound.
Accordingly the coefficient is documented as a leading model, not as a
completed sharp cutoff-tail asymptotic.

In the complex Euclidean six-camera space, the proposed finite-residue vector
and limiting complex-derivative model direction are provably non-collinear
when `Re(s)=1/2` and the Genuine derivative is nonzero. This release does not
identify that model direction with the real time derivative of the empirical
stack. Strict Cauchy--Schwarz gives

```math
\rho
=
\lVert A^{\mathrm{res}}\rVert^2
-
\frac{|\langle A^{\mathrm{res}},V\rangle|^2}{\lVert V\rVert^2}
>0,
```

and the algebraic phase-projection model has the phase-independent symbolic
floor

```math
c_{\mathrm{floor}}
=
\frac{\kappa\rho}{\lVert A^{\mathrm{res}}\rVert^2}>0.
```

Lean additionally proves two conditional closure steps: if a supplied
coefficient sequence approximates this algebraic model with uniform `C/M`
error and `c_floor > 4`, then that sequence is eventually at least four; and
an eventual cutoff-uniform coercivity inequality passes to a supplied
pointwise energy limit, globally or on a fixed region. No theorem identifies
that supplied sequence with the concrete reoptimized finite operator. The
numerical hypotheses are not silently imported from the float64 campaign.
The complete 56-job result bundle and its exact nine-file source/aggregation
closure are included under `audit/`; their SHA-256 values, import closure,
archive grid, result counts, and explicitly non-kernel status are enforced by
the static audit.

## Consolidation theorem

The public capstone is
`zeroIdentity_with_uniqueUniformAtlasEnergyBudget`. For every real time, it
packages both results:

```math
\left(
\mathrm{NativeZero}(t)
\iff
\mathrm{Genuine}\left(\frac12+it\right)=0
\right)
\quad\land\quad
\exists!C,\ C\text{ is the optimal full-atlas budget}.
```

No functional equation, famous-function symmetry, primality hypothesis on the
positional base, or alternative number system selects `1/2`. Its provenance is
the quadratic carry amplitude itself.

See [the formalization scope](docs/FORMALIZATION_SCOPE.md), [the theorem
map](docs/THEOREM_MAP.md), [the lower-bound status](docs/LOWER_BOUND_STATUS.md),
[the conceptual audit](docs/CONCEPTUAL_AUDIT.md), [the exact source
lock](docs/SOURCE_PROVENANCE.md), and [the v0.6.0 release
notes](docs/RELEASE_0.6.0.md).

## Reproducible dependency lock

The project pins:

- Lean `v4.32.0`;
- Mathlib `v4.32.0`, resolved to the exact commit in `lake-manifest.json`;
- [`thiagomassensini/primos`](https://github.com/thiagomassensini/primos)
  (`CPFormal`) at tag `v0.62.0`, resolved to commit
  [`537028681ae6a775c083a1e2fb6e67db24697b82`](https://github.com/thiagomassensini/primos/commit/537028681ae6a775c083a1e2fb6e67db24697b82).

## Build and audit

```bash
lake exe cache get
lake build --wfail GenuineZeroUniformAtlasEnergy
lake build --wfail GenuineZeroUniformAtlasEnergy.Audit
./scripts/audit.sh
```

The audit rejects local `sorry`, `admit`, `axiom`, and `unsafe` declarations,
cross-checks every theorem and claim, validates GitHub Markdown and publication
metadata, locks the separately labelled float64 evidence record, and accepts
only `propext`, `Classical.choice`, and `Quot.sound` in the kernel dependency
reports.

## Repository layout

- `NativeGeometry.lean`: native parameter, quadratic energy, finite-chart
  identity, and exact zero identity;
- `Budget.lean`: full cutoff-atlas energy and unique optimal budget;
- `TiltedCenter.lean`: exact boundary-center factorization, tilt detection,
  common-zero telescoping, and off-equilibrium channel separation;
- `TransverseCoercivity.lean`, `TransverseSpectrum.lean`, and
  `TransverseCapstone.lean`: abstract Hessian, spectrum, Schur-envelope, and
  global supplied-coercivity interface;
- `NativeTransverseBridge.lean`: concrete finite characteristic and exact
  radial/angular tangent geometry;
- `NativeTransverseHessian.lean`: concrete raw-energy Hessian and exact-zero
  isotropy;
- `NativeCutoffTail.lean`: exact primitive-camera resonant tail and explicit
  critical decay;
- `EmpiricalCameraGeometry.lean` and `EmpiricalCameraOperator.lean`: faithful
  C2--C7 radii, exact stack/tail identities, and collective critical decay;
- `EmpiricalFullEvenContinuation.lean`: explicit restoration of the C4/C6
  antipodal channels and their common Genuine continuation;
- `NativeCutoffAsymptotic.lean`: local Taylor remainder, leading model,
  logarithmic phase, and exact collective geometry;
- `NativeCutoffGlobalRemainder.lean`: summation of the local Taylor remainder
  with an explicit critical `M^(-5/2)` bound;
- `AsymptoticCoercivity.lean` and `EmpiricalStackProjection.lean`: phase floor,
  strict projected positivity under simplicity, and the conditional
  coefficient-four implication;
- `UniformCoercivityOn.lean`: region-restricted implication and limit-passage
  interfaces, applicable in particular to a compact region;
- `Capstone.lean`: common-zero corollaries and consolidation theorem;
- `Audit.lean`: ordered kernel dependency reports;
- `audit/`: theorem registry, claim ledger, and locked empirical provenance;
- `docs/`: mathematical scope, theorem map, provenance, and conceptual audit.

## License and citation

The local consolidation is released under the MIT License. Citation and planned
Zenodo metadata are provided in [`CITATION.cff`](CITATION.cff) and
[`.zenodo.json`](.zenodo.json).

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
\mathrm{X}_{p,M}(s)
=
\mathrm{FiniteChart}_{p,M}(n\mapsto n^{-s}).
```

The displayed `X` is the GitHub-renderable symbol for the characteristic called
`Chi` in the surrounding formal development.

At `s = sigma + i*time`, this is literally the complex packaging of the
primitive real camera. Its two real tangent directions obey

```math
\partial_t\mathrm{X}_{p,M}
=
i\,\partial_\sigma\mathrm{X}_{p,M}.
```

Multiplication by `i` is the real quarter-turn `J(x,y)=(-y,x)`. Therefore the
radial and angular tangents have equal Euclidean norm and zero pairing.

The associated raw visibility is

```math
E_{p,M}(\sigma,t)
=
\lVert\mathrm{X}_{p,M}(\sigma+i t)\rVert_{\mathbb R^2}^2.
```

It is exactly the primitive camera's Euclidean resultant energy. No division
by cutoff, coordinate count, state norm, or bracket-coordinate energy is used.
Writing

```math
\kappa=\lVert\mathrm{X}'\rVert^2,
\qquad
a=\langle\mathrm{X},\mathrm{X}''\rangle,
\qquad
b=\langle\mathrm{X},J\mathrm{X}''\rangle,
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

## Sharp scalar tail asymptotic and projected floor model

For period `b` and retained radius `h`, the scalar tail has the exact leading
coefficient

```math
A^{\mathrm{tail}}_{b,h}(s)=sS_2(h)b^{-s-2}.
```

Lean proves an explicit local remainder of order `(k+1)^(-7/2)` and the exact
phase of the leading cutoff monomial

```math
M^{-s-1}=M^{-3/2}\exp(-it\log M).
```

The corresponding leading vector for the finite resonant residue is opposite:
`A_res = -A_tail`. Lean proves this coordinatewise and proves that its
collective squared norm is

```math
\lVert A^{\mathrm{res}}(t)\rVert^2
=
\left\lVert\frac12+it\right\rVert^2
\frac{132244271}{1778112000}.
```

The post-`0.6.0` development proves that the complete named global remainder
is bounded by an explicit `K(b,h,t) M^(-5/2)`. Equivalently, after the natural
critical scaling, the cutoff tail differs from this exact leading coefficient
by at most `K(b,h,t)/M`. The exact scaled tail and its first two complex
derivatives additionally obey explicit critical `O(1/M)` Cauchy bounds.

In the complex Euclidean six-camera space, the proposed finite-residue vector
and limiting complex-derivative model direction are provably non-collinear
when `Re(s)=1/2` and the Genuine derivative is nonzero. Strict Cauchy--Schwarz
gives a positive symbolic projected remainder and phase floor. This symbolic
floor is not yet a concrete finite cutoff-uniform coercivity certificate.

## Concrete pointwise limit and confinement bridge

The faithful finite C2--C7 energy now has a concrete infinite counterpart

```math
E_\infty(\sigma,t)
=\sum_{b=2}^{7}\left|\mathrm{X}_b(\sigma+i t)\right|^2.
```

Lean proves directly from absolute summability that

```math
E_M(\sigma,t)\longrightarrow E_\infty(\sigma,t)
```

for every `sigma > -1`. On the Genuine critical strip, a Genuine zero makes
every faithful limiting camera vanish and hence gives `E_infinity = 0`.
Consequently, if a positive finite transverse coercivity certificate holds
eventually on a region, the limiting energy inherits it and every Genuine zero
inside that region satisfies

```math
\boxed{\mathrm{Re}(s)=\frac12.}
```

This closes the concrete pointwise-limit and zero-to-limit-energy parts of the
pipeline. It does **not** prove the eventual finite coercivity certificate;
the moving minimizer and compact-complement lower bound remain the final
quantitative frontier.

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

The confinement capstones remain conditional on an eventual positive finite
empirical coercivity certificate; they do not silently promote the float64
campaign to a theorem.

## Confinement frontier audit

The `FinalConfinementProbe.lean` and `ArithmeticReadoutBridge.lean` modules are
audited comparison surfaces. They record equivalences among several later
Green/readout formulations and verify that those formulations do not provide a
free substitute for the native carry-geometric confinement step. They are not
used to replace the Genuine-first/native-first construction.

See [the formalization scope](docs/FORMALIZATION_SCOPE.md), [the theorem
map](docs/THEOREM_MAP.md), [the lower-bound status](docs/LOWER_BOUND_STATUS.md),
[the conceptual audit](docs/CONCEPTUAL_AUDIT.md), [the exact source
lock](docs/SOURCE_PROVENANCE.md), and [the v0.12.0 release
notes](docs/RELEASE_0.12.0.md).

## Reproducible dependency lock

The project pins:

- Lean `v4.32.0`;
- Mathlib `v4.32.0`, resolved to the exact commit in `lake-manifest.json`;
- [`thiagomassensini/primos`](https://github.com/thiagomassensini/primos)
  (`CPFormal`) at the exact commit recorded in `lakefile.toml` and
  `lake-manifest.json`;
- [`thiagomassensini/native-carry-c3-crosswalk`](https://github.com/thiagomassensini/native-carry-c3-crosswalk)
  at the exact commit recorded in `lakefile.toml` and `lake-manifest.json`.

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
- `NativeCutoffExactScaledTailCauchy.lean`: exact scaled value and first/second
  complex-derivative bounds from a uniform critical Cauchy circle;
- `AsymptoticCoercivity.lean` and `EmpiricalStackProjection.lean`: phase floor,
  strict projected positivity under simplicity, and conditional floor
  transport;
- `UniformCoercivityOn.lean`: region-restricted implication and abstract
  limit-passage interfaces;
- `EmpiricalLimitConfinement.lean`: concrete pointwise C2--C7 energy limit,
  Genuine-zero limit-energy identity, and conditional regional/global
  confinement capstones;
- `FinalConfinementProbe.lean`: logical frontier audit for final confinement
  formulations;
- `ArithmeticReadoutBridge.lean`: lateral comparison with the canonical
  arithmetic readout surface;
- `Capstone.lean`: common-zero corollaries and consolidation theorem;
- `Audit.lean`: ordered kernel dependency reports;
- `audit/`: theorem registry, claim ledger, and locked empirical provenance;
- `docs/`: mathematical scope, theorem map, provenance, and conceptual audit.

## License and citation

The local consolidation is released under the MIT License. Citation and planned
Zenodo metadata are provided in [`CITATION.cff`](CITATION.cff) and
[`.zenodo.json`](.zenodo.json).

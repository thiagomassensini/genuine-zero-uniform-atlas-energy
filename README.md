# Genuine Zero Uniform Atlas Energy

Lean 4 formalization of one positional carry geometry, one native/Genuine zero,
and one optimal energy budget over the complete tower of finite prime atlases.

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
map](docs/THEOREM_MAP.md), [the conceptual audit](docs/CONCEPTUAL_AUDIT.md),
[the exact source lock](docs/SOURCE_PROVENANCE.md), and [the v0.4.0 release
notes](docs/RELEASE_0.4.0.md).

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
metadata, and accepts only `propext`, `Classical.choice`, and `Quot.sound` in
the kernel dependency reports.

## Repository layout

- `NativeGeometry.lean`: native parameter, quadratic energy, finite-chart
  identity, and exact zero identity;
- `Budget.lean`: full cutoff-atlas energy and unique optimal budget;
- `TiltedCenter.lean`: exact boundary-center factorization, tilt detection,
  common-zero telescoping, and off-equilibrium channel separation;
- `Capstone.lean`: common-zero corollaries and consolidation theorem;
- `Audit.lean`: ordered kernel dependency reports;
- `audit/`: theorem registry and claim ledger;
- `docs/`: mathematical scope, theorem map, provenance, and conceptual audit.

## License and citation

The local consolidation is released under the MIT License. Citation and planned
Zenodo metadata are provided in [`CITATION.cff`](CITATION.cff) and
[`.zenodo.json`](.zenodo.json).

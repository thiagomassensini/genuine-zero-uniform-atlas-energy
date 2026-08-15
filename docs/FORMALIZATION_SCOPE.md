# Formalization Scope

## Object of departure

The library begins with the native positional wave

```math
u_t(n)=n^{-1/2}
\bigl(\cos(-t\log n),\sin(-t\log n)\bigr).
```

It has one real phase coordinate `t`. Its squared Euclidean norm is the inverse
carry mass:

```math
\lVert u_t(n)\rVert^2=n^{-1}.
```

The exponent is therefore not selected by a zero, spectral symmetry, or
additional domain predicate. It is already the quadratic amplitude of the
positional mass.

## Real and complex notation

The map

```math
(x,y)\longmapsto x+iy
```

is used only to store two real coordinates. The upstream crosswalk proves that
it preserves the native samples and commutes with every finite saturated
camera. At camera `3` this is the exact finite Genuine Dirichlet chart.

The limit predicates therefore satisfy

```math
\mathrm{NativeBoundaryCloses}_3(t)
\iff
\mathrm{Genuine}\left(\frac12+it\right)=0.
```

The repository uses this biconditional as the zero theorem. It introduces no
second zero predicate.

## Atlas budget

For every natural cutoff `M` and finite set of prime cameras `S`, the energy is

```math
E_{M,S}(t)
=
\sum_{p\in S}
\frac{\mathcal O_{p,M}(\frac12+it)^2}{p-1}.
```

The observable factors through the radial difference at

```math
\delta
=
\mathrm{Re}\left(\frac12+it\right)-\frac12
=0.
```

Hence `E_{M,S}(t) = 0` pointwise. This gives one bound simultaneously over
every positive cutoff and every finite prime atlas.

An optimal budget is defined order-theoretically as a uniform budget below
every other uniform budget. The empty atlas proves every budget is
nonnegative; exact pointwise vanishing proves zero is a budget. Therefore zero
is the unique optimum.

## Boundary telescoping and the surviving center

The coupled signed boundary and total coupled Green flux are already defined
upstream. This repository defines their finite difference

```math
\mathcal C_{p,M}(s)=\mathcal F_{p,M}(s)-\mathcal B_M(s)
```

and proves, rather than assumes, that it is the radial bulk:

```math
\mathcal C_{p,M}(s)
=
D_p\!\left(\mathrm{Re}(s)-\frac12\right)P_M(s).
```

For positive cutoff and `s` in the open strip, the reflected pairing
`P_M(s)` is strictly positive. Under the upstream odd-prime camera and
admissible-center hypotheses, this gives the exact zero-locus crosswalk

```math
\mathcal C_{p,M}(s)=0
\iff
\mathrm{Re}(s)=\frac12
\iff
\mathrm{Tilt}_{p}(\mathrm{Re}\,s)=0
\iff
\mathrm{BranchDefect}_{p}(\mathrm{Re}\,s)=0.
```

Thus subtracting the boundary cannot conceal radial imbalance. At a common
native/Genuine zero the boundary tends to zero, so closure of the total flux
is equivalent to balance of this same tilt. At the native parameter that
balance is already forced by the quadratic carry amplitude.

Conversely, if a Genuine zero in the strip is presented away from equilibrium,
the same boundary still tends to zero, every positive-cutoff center is nonzero,
and the total coupled Green flux cannot tend to zero. This is a separation of
channels, not a second zero definition and not an existence theorem for an
off-equilibrium zero.

## Abstract transverse Hessian and coercivity

The numerical audit motivates three finite real jet coefficients:

```math
\kappa=\lVert\partial_\sigma\Chi\rVert^2,
\qquad
a=\langle\Chi,\partial_{\sigma\sigma}\Chi\rangle,
\qquad
b=\langle\Chi,J\partial_{\sigma\sigma}\Chi\rangle.
```

The new Lean layer begins from these scalars as an abstract structure and
formalizes the Hessian

```math
D^2E
=
2\begin{pmatrix}
\kappa+a & b\\
b & \kappa-a
\end{pmatrix}.
```

With

```math
D=\kappa^2-a^2-b^2,
```

Lean proves the exact trace and determinant identities, the algebraic
eigenvalue pair, the completed-square positive-definiteness criterion, the
implicit minimizing-clock slope, the Schur-envelope curvature, and the local
coercivity threshold. At an exact residual-free zero, the correction vanishes
and the Hessian becomes `2*kappa` times the identity.

For an arbitrary raw energy `E`, Lean also defines

```math
F_c(\sigma,t)
=
E(\sigma,t)-c\left(\sigma-\frac12\right)^2
```

and proves

```math
F_c\ge0\text{ everywhere}
\iff
E(\sigma,t)\ge c\left(\sigma-\frac12\right)^2\text{ everywhere}.
```

If `c > 0`, this inequality forces every zero of the certified energy onto
`sigma = 1/2`.

This layer is intentionally conditional. It does not yet prove that the
Python finite operator realizes the abstract jet identities, that its energy
is the Lean function being certified, or that a positive constant is uniform
in the cutoff. Those are the remaining operator-bridge and limit gates.

## Logical order

The dependency order is:

```math
\text{inverse carry mass}
\Longrightarrow
\text{quadratic native amplitude}
\Longrightarrow
\text{native parameter}
\Longrightarrow
\text{finite real/Genuine chart identity}
\Longrightarrow
\text{one zero identity}.
```

Independently, the native parameter annihilates the transverse radial defect,
which supplies the unique atlas budget. The Green decomposition then exposes
that same defect as the center left after boundary subtraction. The zero
hypothesis is used only to telescope the boundary; it does not choose the
native exponent or create the tilt balance.

The abstract Hessian layer begins after a finite characteristic jet has been
identified. It packages the algebra needed to turn such a jet and a global
coercivity estimate into an off-critical zero exclusion, without pretending
that the estimate itself has already been proved.

## Exact boundary of the result

The atlas quantifier ranges over all finite prime-camera sets and all positive
cutoffs. The theorem controls the full tower of finite approximations. It does
not introduce a completed infinite-atlas vector because no such object is
needed for this uniform-budget statement.

The center detector uses the hypotheses of the imported Green/tilt interface:
an odd prime camera, positive cutoff, an admissible tilt center, and a
parameter in the open strip. Primality is a camera hypothesis here; it is not
a hypothesis of the foundational all-base quadratic rigidity theorem.

The transverse-coercivity theorems are exact finite real algebra. Their global
zero-exclusion consequence applies only after a positive coercivity inequality
has been supplied for the energy under study.

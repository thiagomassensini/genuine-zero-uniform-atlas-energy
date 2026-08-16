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

A finite transverse jet is encoded by three real coefficients:

```math
\kappa=\lVert\partial_\sigma\Chi\rVert^2,
\qquad
a=\langle\Chi,\partial_{\sigma\sigma}\Chi\rangle,
\qquad
b=\langle\Chi,J\partial_{\sigma\sigma}\Chi\rangle.
```

The abstract Lean layer formalizes the Hessian

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

## Concrete finite primitive-camera bridge

The abstract jet is connected to the finite primitive carry camera itself. For
an odd prime camera `p` and cutoff `M`, define

```math
\Chi_{p,M}(s)
=
\mathrm{FiniteChart}_{p,M}(n\mapsto n^{-s}).
```

The function is entire. At `s = sigma + i*time`, Lean proves that it is
literally the complex packaging of
`nativeCarryRealPlaneFiniteChartAt p M sigma time`. Therefore the radial and
angular derivatives satisfy

```math
\partial_t\Chi_{p,M}
=
i\,\partial_\sigma\Chi_{p,M}.
```

In real coordinates, multiplication by `i` is the fixed quarter-turn

```math
J(x,y)=(-y,x).
```

Hence the two tangent directions have equal Euclidean norm and zero pairing.
No zero hypothesis or score normalization is used.

The concrete raw energy is

```math
E_{p,M}(\sigma,t)
=
\lVert\Chi_{p,M}(\sigma+i t)\rVert_{\mathbb R^2}^2.
```

Lean proves that this is exactly the Euclidean energy of the primitive real
camera, not the scanner score obtained after division by coordinate count or
coordinate energy. With

```math
u=\Chi_{p,M},\qquad
v=\Chi_{p,M}',\qquad
w=\Chi_{p,M}'',
```

the concrete jet is

```math
\kappa=\langle v,v\rangle,
\qquad
a=\langle u,w\rangle,
\qquad
b=\langle u,Jw\rangle,
```

and the three Hessian entries are proved to be exactly

```math
E_{\sigma\sigma}=2(\kappa+a),
\qquad
E_{\sigma t}=2b,
\qquad
E_{tt}=2(\kappa-a).
```

At an exact finite primitive-camera zero, `u = 0`, so `a = b = 0`. The
concrete Hessian is isotropic, the first-order minimizing-clock slope is zero,
the Schur-envelope curvature is `2*kappa`, and both algebraic eigenvalues are
`2*kappa`.

This closes the finite componentwise operator-to-jet bridge for every odd
prime camera, including camera `3`. It does not import floating-point values
or numerical minima as proof objects.

## Exact finite-cutoff tail and critical decay

At a real spectral resonance, the complete infinite chart vanishes. The
finite primitive-camera residue is therefore not an unexplained approximation:
it is exactly the negative unresolved tail,

```math
\Chi_{p,M}\left(\frac12+i t\right)
=
-\sum_{k\ge M}\operatorname{Bracket}_{p,k}
 \left(\frac12+i t\right).
```

The upstream centered-second-difference estimate gives a critical-line
majorant proportional to `(k+1)^(-5/2)`. Lean now sums the shifted majorant by
the improper-integral comparison

```math
\sum_{k\ge0}(k+M+1)^{-5/2}
\le
\int_M^\infty x^{-5/2}\,dx
=
\frac23 M^{-3/2}.
```

Consequently, for the explicit camera majorant `C_{p,t}`,

```math
\left\lVert\Chi_{p,M}\left(\frac12+i t\right)\right\rVert
\le
\frac23 C_{p,t}M^{-3/2},
```

and the raw energy is at most the square of this expression. This is a general
analytic estimate for every positive cutoff under the odd-prime primitive
camera hypotheses. It does not encode the dyadic cutoff table as separate
facts.

The current theorem is an upper bound. It does not identify the sharp first
asymptotic coefficient, the logarithmic phase `exp(-it log M)`, the projected
coercivity oscillation, or a cutoff-uniform lower bound.

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

For the transverse and cutoff mechanisms, the order is:

```math
\text{finite primitive camera}
\Longrightarrow
\text{entire finite characteristic}
\Longrightarrow
\partial_t\Chi=i\partial_\sigma\Chi
\Longrightarrow
\text{concrete jet }(\kappa,a,b)
\Longrightarrow
\text{raw-energy Hessian}
```

and independently

```math
\text{resonance of the complete chart}
\Longrightarrow
\text{finite residue}=-\text{unresolved tail}
\Longrightarrow
\lVert\text{residue}\rVert=O(M^{-3/2})
\Longrightarrow
E_M=O(M^{-3}).
```

The abstract coercivity layer converts a positive discriminant into local
rigidity, and a separately supplied positive global coercivity estimate into
off-critical zero exclusion.

## Exact boundary of the result

The atlas quantifier ranges over all finite prime-camera sets and all positive
cutoffs. The theorem controls the full tower of finite approximations. It does
not introduce a completed infinite-atlas vector because no such object is
needed for the uniform-budget statement.

The center detector uses the hypotheses of the imported Green/tilt interface:
an odd prime camera, positive cutoff, an admissible tilt center, and a
parameter in the open strip. Primality is a camera hypothesis here; it is not
a hypothesis of the foundational all-base quadratic rigidity theorem.

The transverse camera bridge and cutoff-tail identity are exact and finite,
but currently componentwise. The remaining gates are:

- package the empirical finite family `2,3,4,5,6,7` into one product-space
  characteristic, including separate handling of the non-prime/even cameras;
- sharpen the tail upper bound to an explicit asymptotic expansion with a
  certified remainder and logarithmic phase;
- transport that expansion through time reoptimization to obtain a uniform
  positive lower coercivity estimate;
- certify the complement of the critical tubes and prove positivity uniform in
  the cutoff;
- justify the limiting energy and transport the coercivity inequality to that
  limit.

Thus the operator-to-jet bridge and the universal resonant upper-tail rate are
closed. The sharp collective asymptotic, global compact coercivity certificate,
and cutoff-uniform limit are not.

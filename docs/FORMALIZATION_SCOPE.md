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
-\sum_{k\ge M}\mathrm{Bracket}_{p,k}
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

The primitive-camera theorem is an upper bound. The new explicit-radius layer
also isolates the proposed leading block and tail coefficients. Lean proves an
explicit cubic-radius local Taylor remainder of order `(k+1)^(-7/2)`, the exact
phase `M^(-3/2) exp(-it log M)` of the proposed tail monomial, and the exact
collective six-camera squared model coefficient. It does not yet bound the
named global tail remainder or prove scaled-tail convergence, so the
coefficient is not presented as a completed sharp tail asymptotic.

## Faithful empirical stack C2--C7

The empirical operator uses labels, periods, and retained radii

```text
label    2  3  4  5  6  7
period   4  3  4  5  6  7
radii    1  1 12 12 123 123
```

Here `12` means radii one and two, and `123` means radii one, two, and three.
Thus C4 and C6 include their antipodal middle channels. They are not the same
objects as the natural even cameras, whose stored half-range omits that
channel.

Lean defines all six seeds, bracket blocks, finite and infinite
characteristics, cutoff tails, stack vectors, and collective raw energies
directly. Every component is absolutely summable on `re(s) > -1`. At a common
zero, the finite stack is exactly the negative tail stack and the collective
finite energy is exactly the collective tail energy. For each fixed critical
time, the six amplitudes have displayed time-dependent `M^(-3/2)` majorants and
their energy has the corresponding `M^(-3)` upper bound.

The full-even continuation restores the C4/C6 antipodal channel through the
paired odd--even channel instead of reusing the wrong natural-even factor. On
the critical strip, each empirical infinite characteristic is its faithful
factor times the same `genuineContinuation`. Therefore a Genuine zero supplies
the common-zero hypothesis required by the all-six cutoff theorem.

## Projected phase floor and limit interfaces

The proposed tail coefficient is `+A_tail`; the proposed finite resonant
residue vector is `A_res = -A_tail`. Lean proves that coordinate identity and
the common rational squared norm. The finite-residue vector and the limiting
complex-derivative model direction are then placed in the complex Euclidean
six-camera space. At `Re(s)=1/2` with a nonzero Genuine derivative, C2 and C4
force these vectors to be non-collinear: their residue-model coordinates have
ratio five, whereas their faithful limiting factors provably do not. The
formalization does not identify this complex-derivative model direction with
the real time derivative of the empirical stack.

Lean consequently proves strict Cauchy--Schwarz and

```math
\rho
=
\lVert A^{\mathrm{res}}\rVert^2
-
\frac{|\langle A^{\mathrm{res}},V\rangle|^2}{\lVert V\rVert^2}
>0.
```

The algebraic phase-projection model has the symbolic phase-independent floor

```math
c_{\mathrm{floor}}
=
\frac{\kappa\rho}{\lVert A^{\mathrm{res}}\rVert^2}
>0.
```

Two implication theorems keep the quantitative frontier explicit. If a
supplied coefficient sequence approximates the algebraic model with uniform
`C/M` error and `c_floor > 4`, that sequence is eventually at least four. No
theorem identifies it with the concrete reoptimized finite operator. An
eventual cutoff-uniform energy inequality passes to a supplied pointwise
limiting energy, either globally or on a fixed region. This repository does
not prove those quantitative hypotheses for the concrete operator.

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

For the collective empirical stack the additional order is

```math
\text{faithful C2--C7 radii}
\Longrightarrow
\text{full-even continuation}
\Longrightarrow
\text{common Genuine zero}
\Longrightarrow
\text{exact six-camera tail identity}
\Longrightarrow
\text{leading phase model and positive projected floor}.
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

The empirical product-space packaging and the even-camera semantic gap are now
closed. The proposed monomial's logarithmic phase and the local Taylor
remainder are kernel-checked, but the named global cutoff-tail remainder still
lacks a proved bound or scaled-tail convergence theorem. The
remaining concrete gates are:

- finish the global tail remainder and the corresponding derivative and
  Hessian expansions;
- certify a Genuine zero, its simplicity, and a quantitative derivative lower
  bound with exact enclosures;
- use those enclosures to prove `c_floor > 4` and the concrete `C/M`
  reoptimization error;
- certify the complement of the critical tubes and obtain a cutoff-uniform
  compact lower bound;
- supply convergence of the concrete collective energy so the already-proved
  limit interface applies.

Thus the faithful all-camera operator, resonant upper-tail rate, exact phase of
the proposed monomial, connected residue-model geometry, positive symbolic
projection floor, and conditional global/region-restricted limit interfaces
are closed. The unconditional numerical coefficient four and its concrete
infinite-limit lower bound are not.

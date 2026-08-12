# Formalization Scope

## Object of departure

The library begins with the native positional wave

$$
u_t(n)=n^{-1/2}
\bigl(\cos(-t\log n),\sin(-t\log n)\bigr).
$$

It has one real phase coordinate `t`. Its squared Euclidean norm is the inverse
carry mass:

$$
\lVert u_t(n)\rVert^2=n^{-1}.
$$

The exponent is therefore not selected by a zero, spectral symmetry, or
additional domain predicate. It is already the quadratic amplitude of the
positional mass.

## Real and complex notation

The map

$$
(x,y)\longmapsto x+iy
$$

is used only to store two real coordinates. The upstream crosswalk proves that
it preserves the native samples and commutes with every finite saturated
camera. At camera `3` this is the exact finite Genuine Dirichlet chart.

The limit predicates therefore satisfy

$$
\operatorname{NativeBoundaryCloses}_3(t)
\iff
\operatorname{Genuine}\left(\frac12+it\right)=0.
$$

The repository uses this biconditional as the zero theorem. It introduces no
second zero predicate.

## Atlas budget

For every natural cutoff `M` and finite set of prime cameras `S`, the energy is

$$
E_{M,S}(t)
=
\sum_{p\in S}
\frac{\mathcal O_{p,M}(\frac12+it)^2}{p-1}.
$$

The observable factors through the radial difference at

$$
\delta
=
\operatorname{Re}\left(\frac12+it\right)-\frac12
=0.
$$

Hence `E_{M,S}(t) = 0` pointwise. This gives one bound simultaneously over
every positive cutoff and every finite prime atlas.

An optimal budget is defined order-theoretically as a uniform budget below
every other uniform budget. The empty atlas proves every budget is
nonnegative; exact pointwise vanishing proves zero is a budget. Therefore zero
is the unique optimum.

## Logical order

The dependency order is:

$$
\text{inverse carry mass}
\Longrightarrow
\text{quadratic native amplitude}
\Longrightarrow
\text{native parameter}
\Longrightarrow
\text{finite real/Genuine chart identity}
\Longrightarrow
\text{one zero identity}.
$$

Independently, the native parameter annihilates the transverse radial defect,
which supplies the unique atlas budget. Thus the budget is structural and the
zero hypothesis is used only to state the requested corollary.

## Exact boundary of the result

The atlas quantifier ranges over all finite prime-camera sets and all positive
cutoffs. The theorem controls the full tower of finite approximations. It does
not introduce a completed infinite-atlas vector because no such object is
needed for this uniform-budget statement.

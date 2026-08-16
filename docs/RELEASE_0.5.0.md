# Genuine Zero Uniform Atlas Energy v0.5.0

## Concrete finite transverse operator bridge

This release connects the abstract transverse-coercivity algebra to the actual
finite primitive carry camera.

For every odd prime camera `p` and finite cutoff `M`, Lean defines the entire
characteristic

```math
\Chi_{p,M}(s)
=
\mathrm{FiniteChart}_{p,M}(n\mapsto n^{-s}).
```

At `s = sigma + i*time`, Lean proves that this characteristic is literally the
complex packaging of `nativeCarryRealPlaneFiniteChartAt`. No score denominator,
zero predicate, numerical fit, or cutoff limit enters the identification.

## Exact transverse tangent geometry

The finite characteristic is entire, and its real slices satisfy

```math
\partial_t\Chi_{p,M}
=
i\,\partial_\sigma\Chi_{p,M}.
```

After unpacking complex multiplication as the real quarter-turn
`J(x,y)=(-y,x)`, Lean proves that the angular tangent is `J` applied to the
radial tangent. Consequently the two tangents have equal Euclidean norm and
zero pairing.

## Raw-energy Hessian

The release defines the unnormalized finite energy

```math
E_{p,M}(\sigma,t)
=
\lVert\Chi_{p,M}(\sigma+i t)\rVert_{\mathbb R^2}^2
```

and proves that it is exactly the Euclidean energy of the primitive real-camera
resultant.

Writing

```math
\kappa=\langle\Chi',\Chi'\rangle,
\qquad
a=\langle\Chi,\Chi''\rangle,
\qquad
b=\langle\Chi,J\Chi''\rangle,
```

Lean derives the concrete Hessian entries

```math
E_{\sigma\sigma}=2(\kappa+a),
\qquad
E_{\sigma t}=2b,
\qquad
E_{tt}=2(\kappa-a).
```

Thus

```math
D^2E
=
2\begin{pmatrix}
\kappa+a & b\\
b & \kappa-a
\end{pmatrix}.
```

The previously abstract discriminant

```math
D=\kappa^2-a^2-b^2
```

now belongs directly to the concrete finite operator. It controls the Hessian
determinant, positive definiteness, algebraic eigenvalue pair, minimizing-clock
slope, Schur-envelope curvature, and local coercivity threshold.

## Exact-zero isotropy

At an exact finite primitive-camera zero, the characteristic value vanishes, so
`a=b=0`. Lean proves

```math
D^2E=2\kappa I,
\qquad
t_M'=0,
\qquad
L_M''=2\kappa,
\qquad
\lambda_-=\lambda_+=2\kappa.
```

Therefore the finite exact zero has no first-order escape direction obtained by
retuning the angular clock.

## Public audit surface

Release `0.5.0` contains:

- 35 public theorem dependency reports;
- 7 claims marked `KERNEL_CHECKED`;
- 7 abstract transverse-coercivity capstones;
- 3 concrete primitive-camera bridge capstones;
- exact CPFormal and Mathlib dependency locks;
- no local `sorry`, `admit`, `axiom`, or `unsafe` declaration;
- a foundational dependency allowlist restricted to `propext`,
  `Classical.choice`, and `Quot.sound`.

The three concrete public capstones are:

- `finiteNativeCamera_transverse_tangent_geometry`;
- `finiteNativeCamera_rawEnergy_hessian_eq_transverseJet`;
- `finiteNativeCamera_exactZero_has_isotropic_transverseHessian`.

## Exact scope boundary

This release closes the finite componentwise operator-to-jet bridge for odd
prime primitive cameras, including camera `3`.

It does not yet claim:

- a single product-space theorem for the empirical camera family
  `2,3,4,5,6,7`;
- a machine-checked import of the floating-point branch-and-bound certificate;
- a rigorous positive compact-domain coercivity constant for the concrete raw
  energy;
- positivity uniform in the cutoff;
- passage of that coercivity inequality to an infinite limiting energy.

Those remain the collective packaging, certified compact-bound, and
uniform-limit gates.

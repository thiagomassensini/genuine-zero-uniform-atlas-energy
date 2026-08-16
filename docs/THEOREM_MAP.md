# Theorem Map

## Native geometry and zero identity

| Lean declaration | Mathematical content |
| --- | --- |
| `quadraticCarryShell_energy_eq_mass_iff` | In every base and positive depth, for every real angle, quadratic shell energy equals carry mass exactly at `sigma = 1/2`. |
| `nativeParameter_re` | The native radial coordinate is `1/2`. |
| `nativeParameter_im` | The native phase coordinate is the real time. |
| `nativeParameter_mem_genuineCriticalStrip` | Every native parameter lies in the open strip. |
| `nativeAmplitude_energy_eq_inverseCarryMass` | The native quadratic energy is inverse carry mass, independently of time. |
| `packagedNativeFiniteChart_eq_genuineFiniteChart` | Every finite real native chart is literally the packaged Genuine chart. |
| `nativeZero_iff_genuineZero` | Native closure and Genuine vanishing are the same zero predicate. |

## Uniform energy budget

| Lean declaration | Mathematical content |
| --- | --- |
| `nativeAtlasEnergy_eq_zero` | Every native finite radial-defect atlas energy is zero. |
| `uniformAtlasEnergyBudget_nonneg` | Every full-tower budget is nonnegative. |
| `isUniformAtlasEnergyBudget_iff_nonneg` | Uniform budgets are exactly the nonnegative reals. |
| `zero_isOptimalAtlasEnergyBudget` | Zero is the least full-tower budget. |
| `optimalAtlasEnergyBudget_unique` | Any two optimal budgets coincide. |
| `isOptimalAtlasEnergyBudget_iff_eq_zero` | Optimality characterizes zero exactly. |
| `existsUnique_optimalAtlasEnergyBudget` | Every native time has a unique optimal budget. |

## Tilted center after boundary telescoping

| Lean declaration | Mathematical content |
| --- | --- |
| `finiteTiltedCenter_eq_radialDifference_mul_pairing` | Total coupled flux minus its signed boundary is exactly the radial carry difference times the reflected pairing. |
| `finiteTiltedCenter_eq_zero_iff_re_eq_half` | The surviving center vanishes exactly on the critical half-abscissa. |
| `finiteTiltedCenter_eq_zero_iff_carryTilt_eq_zero` | At positive cutoff in the strip, the surviving center vanishes exactly when the carry tilt vanishes. |
| `finiteTiltedCenter_eq_zero_iff_quadraticBranchDefect_eq_zero` | The tilted-center and quadratic branch-defect zero loci coincide. |
| `finiteTiltedCenter_ne_zero_of_carryTilt_ne_zero` | A nonzero tilt is detected by a nonzero center at every nonempty cutoff. |
| `totalFlux_closes_iff_carryTilt_balanced_at_commonZero` | Once the common-zero boundary telescopes, total flux closure is equivalent to tilt balance. |
| `nativeGenuineZero_telescopes_boundary_and_balances_tiltedCenter` | At the native/Genuine zero, boundary, center, tilt, quadratic defect, and total coupled flux close together. |
| `genuineZero_offEquilibrium_telescopes_boundary_and_exposes_tiltedCenter` | At a presented Genuine zero away from equilibrium, the boundary still telescopes, every positive-cutoff center is nonzero, and total coupled Green flux cannot close. |

## Common-zero capstone

| Lean declaration | Mathematical content |
| --- | --- |
| `genuineZero_hasUniqueUniformAtlasEnergyBudget` | A zero written in Genuine notation inherits the structural budget. |
| `nativeZero_hasUniqueUniformAtlasEnergyBudget` | The identical zero written as native closure inherits the same budget. |
| `zeroIdentity_with_uniqueUniformAtlasEnergyBudget` | One statement records the exact zero identity and unique full-atlas budget. |

## Abstract transverse-coercivity certificate

Let the finite transverse jet be encoded by `kappa`, `a`, and `b`, with

```math
D=\kappa^2-a^2-b^2.
```

The formalized Hessian is

```math
2\begin{pmatrix}
\kappa+a & b\\
b & \kappa-a
\end{pmatrix}.
```

| Lean declaration | Mathematical content |
| --- | --- |
| `transverseHessian_trace_det_and_positiveDefinite` | If `kappa > 0` and `D > 0`, then the Hessian has trace `4*kappa`, determinant `4*D`, and a strictly positive quadratic form away from the origin. |
| `transverseHessian_eigenvalue_pair` | The explicit values `2*(kappa ± sqrt(a^2+b^2))` are roots of the characteristic polynomial and recover trace and determinant by sum and product. |
| `transverseEnvelope_slope_and_curvature` | The minimizing-clock slope is `-b/(kappa-a)` and the Schur-envelope curvature is twice the local coefficient `D/(kappa-a)`, hence positive when the discriminant is positive. |
| `transverseLocalCoercivity_certificate` | Every constant below the local Schur coefficient leaves a strictly positive shifted quadratic form after the time direction is allowed to move. |
| `exactZero_transverse_geometry` | At the residual-free exact-zero jet, the Hessian is isotropic, the clock slope is zero, the envelope curvature is `2*kappa`, and both eigenvalues equal `2*kappa`. |
| `transverseCertificateResidual_nonneg_iff` | Global coercivity is equivalent to nonnegativity of the smooth residual `E-c*(sigma-1/2)^2`. |
| `transverseCoercivity_excludes_offCritical_zero` | A supplied positive global coercivity constant forces every zero of the certified raw energy onto `sigma = 1/2`. |

## Concrete finite primitive-camera bridge

For an odd prime camera `p` and cutoff `M`, Lean defines the entire finite
characteristic

```math
\Chi_{p,M}(s)=\mathrm{FiniteChart}_{p,M}(n\mapsto n^{-s}).
```

At `s = sigma + i*time`, this is literally the packaged primitive real-plane
camera. Its raw visibility is

```math
E_{p,M}(\sigma,t)=\lVert\Chi_{p,M}(\sigma+i t)\rVert_{\mathbb R^2}^2,
```

without the scanner score denominator.

| Lean declaration | Mathematical content |
| --- | --- |
| `finiteNativeCamera_transverse_tangent_geometry` | The finite complex characteristic is exactly the packaged primitive real camera; its time tangent is `i` times, equivalently the real quarter-turn of, its sigma tangent; the two tangents have equal norm and zero real pairing. |
| `finiteNativeCamera_rawEnergy_hessian_eq_transverseJet` | The concrete raw energy equals the primitive real-camera Euclidean energy, and its first and second radial/angular derivatives are exactly the entries `2*(kappa+a)`, `2*b`, and `2*(kappa-a)` of the concrete jet built from `Chi`, `Chi'`, and `Chi''`. |
| `finiteNativeCamera_exactZero_has_isotropic_transverseHessian` | At an exact finite primitive-camera zero, the residual coefficients vanish: the Hessian is isotropic, the first-order minimizing-clock slope is zero, the Schur-envelope curvature is `2*kappa`, and both algebraic eigenvalues equal `2*kappa`. |

The concrete bridge is componentwise and finite. It does not yet package the
whole six-camera stack into one product-space theorem, import a numerical
branch-and-bound result as a proof object, establish a cutoff-uniform positive
coercivity constant, or pass that constant to the infinite limit.

The authoritative machine-readable order is
[`audit/theorem-registry.json`](../audit/theorem-registry.json).

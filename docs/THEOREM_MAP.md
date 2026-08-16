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
| `transverseLocalCoercivity_certificate` | Every constant below the local Schur coefficient leaves a strictly positive shifted quadratic bound after the time direction is allowed to move. |
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

## Exact resonant cutoff tail and critical decay

At a real spectral resonance, the infinite chart vanishes. The finite chart is
therefore exactly the negative of the unresolved bracket tail:

```math
\Chi_{p,M}\left(\frac12+i t\right)
=
-\sum_{k\ge M}\mathrm{Bracket}_{p,k}
 \left(\frac12+i t\right).
```

The centered-second-difference majorant and the integral test give

```math
\sum_{k\ge0}(k+M+1)^{-5/2}
\le
\frac23 M^{-3/2}.
```

| Lean declaration | Mathematical content |
| --- | --- |
| `finiteNativeCamera_resonant_cutoffTail_and_rate` | For every positive cutoff of an odd prime primitive camera and every real spectral resonance, the finite characteristic equals the negative unresolved tail; its norm is at most `(2/3) * C_{p,t} * M^(-3/2)`, and its raw quadratic energy is at most the square of that bound. |

This theorem is an explicit upper decay estimate for one odd-prime primitive
camera. The following release layers aggregate the empirical family without
changing that upper-bound interpretation.

## Empirical C2--C7 geometry and operator

| Lean declaration | Mathematical content |
| --- | --- |
| `EmpiricalCamera.period_table` | The operator periods are exactly `4,3,4,5,6,7`. |
| `EmpiricalCamera.radii_table` | The stored radii include the C4 radius two and C6 radius three antipodal channels. |
| `EmpiricalCamera.hasAntipodalRadius_iff` | Exactly C4 and C6 have an antipodal radius; aligned C2 does not. |
| `EmpiricalCamera.secondRadiusMoment_table` | The second moments are exactly `1,1,5,5,14,14`. |
| `EmpiricalCamera.sum_leadingTailGeometryWeight` | The squared leading geometry weights sum to `132244271/1778112000`. |
| `summable_norm_empiricalCameraBlock` | Every stored all-camera block series is absolutely summable on `re(s)>-1`. |
| `empiricalCameraCharacteristic_eq_finite_add_cutoffTail` | Every infinite empirical characteristic is exactly finite prefix plus unresolved tail. |
| `finiteEmpiricalCameraStack_eq_neg_cutoffTailStack_of_zero` | At a common zero, the complete finite stack is the negative tail stack. |
| `finiteEmpiricalCollectiveRawEnergy_eq_cutoffTailEnergy_of_zero` | At a common zero, collective finite raw energy is exactly collective tail energy. |
| `norm_empiricalCameraCutoffTail_critical_le` | At each fixed time, every empirical critical-line tail has the displayed time-dependent `M^(-3/2)` amplitude bound. |
| `empiricalSixCamera_critical_cutoffTail_and_rate` | A common critical zero at a fixed time gives the exact six-camera tail package and displayed `M^(-3)` collective energy upper bound. |

The registry also records the finite label bijection, uniform radius membership
and period inequalities, per-camera moment reductions, complex summability,
and the componentwise finite tail/rate theorem.

## Local remainder and leading cutoff model

| Lean declaration | Mathematical content |
| --- | --- |
| `hasDerivAt_realDirichletPowerDeriv2` | The displayed third Dirichlet-power derivative differentiates the second derivative on the positive axis. |
| `norm_centeredSecondDifference_sub_secondDerivative_le` | A third-derivative bound controls centered difference minus `r^2 f''` by `2 C r^3`. |
| `norm_realCpPairBracket_sub_secondDerivative_critical_le` | The generic estimate specializes to one critical native radius pair. |
| `nativeExplicitRadiusBracketLeading_eq_sum_secondDerivative` | The local leading block is exactly the sum of its quadratic Taylor terms. |
| `norm_nativeExplicitRadiusBracketRemainder_critical_le` | The local named remainder is explicitly `O((k+1)^(-7/2))`, with period margin and third radius moment exposed. |
| `nativeExplicitRadiusCutoffTail_eq_leading_add_remainder` | The global tail is exactly its proposed leading-model term plus the named difference remainder. This identity alone does not bound that remainder. |
| `criticalCutoffPower_eq_amplitude_mul_logPhase` | The critical cutoff monomial is exactly `M^(-3/2) exp(-it log M)`. |
| `empiricalCameraCutoffTailStack_eq_nativeExplicitRadiusCutoffTail` | The explicit-radius tail model uses exactly the empirical stack's periods and retained radii. |
| `norm_empiricalNativeTailCoefficient_critical` | Each candidate tail-model coefficient has the exact second-moment and period norm. |
| `empiricalNativeTailCoefficientNormSq_eq` | The squared six-camera model coefficient has exact rational geometry weight `132244271/1778112000`. |

There is no theorem bounding `nativeExplicitRadiusTailRemainder` or proving
scaled-tail convergence. The global sharp asymptotic remains open.

## Full-even continuation and one six-camera resonance

| Lean declaration | Mathematical content |
| --- | --- |
| `finiteAntipodalEvenCameraChannel_eq_pairedAlt_prefix` | The finite antipodal channel telescopes to a paired odd--even prefix plus one endpoint. |
| `antipodalEvenCameraChannel_eq_pairedAltChannel_of_summable` | After the endpoint vanishes, the infinite channel is `2 h^(-s)` times the paired channel. |
| `empiricalCameraCharacteristic_c4_eq_fullEvenCameraFactor_mul_genuineContinuation` | C4 uses its restored full-even factor times the canonical continuation. |
| `empiricalCameraCharacteristic_c6_eq_fullEvenCameraFactor_mul_genuineContinuation` | C6 uses its restored full-even factor times the canonical continuation. |
| `empiricalCameraCharacteristic_eq_limitingFactor_mul_genuineContinuation` | One faithful factor table covers every empirical camera C2--C7. |
| `empiricalSixCamera_zero_of_realSpectralResonance` | A presented real spectral resonance is a simultaneous zero of all six empirical characteristics. |
| `empiricalSixCamera_resonant_cutoffTail_and_rate` | One resonance supplies the exact six-camera tail and collective critical energy upper-bound capstone. |

## Symbolic projected lower bound

| Lean declaration | Mathematical content |
| --- | --- |
| `empiricalFullEvenCameraFactor_four_sub_five_alignedC2_ne_zero` | On the critical line, the full C4 factor cannot equal five aligned C2 factors. |
| `empiricalLeadingCutoffVector_apply_eq_neg_tailCoefficient` | Each proposed finite-residue model coordinate is the negative of the candidate tail-model coefficient. |
| `empiricalStackAmplitudeSq_critical_eq` | The residue model has the exact collective rational squared norm used by the projection algebra. |
| `empiricalLeadingCutoffVector_not_collinear_clockTangent` | A nonzero Genuine derivative makes the finite-residue model and limiting complex-derivative model direction non-collinear. No real-time derivative identification is asserted. |
| `empiricalStack_strict_cauchy_schwarz` | The corresponding Hermitian Cauchy--Schwarz inequality is strict. |
| `empiricalStackRho_pos` | The transverse Gram remainder is strictly positive. |
| `empiricalStackPhaseProjectionData_isAdmissible` | The empirical Gram scalars satisfy the phase-projection admissibility identity and positivity hypotheses. |
| `empiricalStackPhaseFloor_pos` | The symbolic phase-independent floor is strictly positive. |
| `empiricalStack_phaseCoercivity_uniform_lower_bound` | That floor bounds the projected limiting law for every logarithmic phase. |
| `empiricalStack_projectionRho_pos_of_critical_simple_zero` | A presented critical simple Genuine zero has positive empirical projection remainder. |
| `PhaseProjectionData.eventually_microscopicCoercivity_ge_four_of_inv_error` | `phaseFloor > 4` plus a supplied coefficient sequence with uniform `C/M` approximation to the algebraic model implies that the supplied sequence is eventually at least four. |

The last implication neither proves its quantitative premises nor identifies
the supplied sequence with the concrete reoptimized finite operator.

## Global and regional limit passage

| Lean declaration | Mathematical content |
| --- | --- |
| `transverseCoercivity_passes_to_pointwise_limit` | A cutoff-uniform global coercivity inequality survives supplied pointwise energy convergence. |
| `transverseCoercivity_passes_to_pointwise_limit_eventually` | Eventual cutoff-uniform global coercivity is sufficient. |
| `isTransverselyCoerciveOn_iff_certificateResidual_nonneg` | Regional coercivity is equivalent to nonnegative certificate residual on the region. |
| `zero_in_region_forces_re_eq_half_of_transverse_coercivityOn` | A positive regional certificate excludes off-critical zeros inside the region. |
| `transverseCoercivityOn_passes_to_pointwise_limit_eventually` | Eventual regional coercivity survives supplied pointwise convergence on that region. |
| `IsTransverselyCoercive.isTransverselyCoerciveOn` | Every global certificate restricts to every region. |

These are conditional passage theorems; they do not manufacture the finite
lower bound or the convergence hypothesis.

The authoritative machine-readable order is
[`audit/theorem-registry.json`](../audit/theorem-registry.json).

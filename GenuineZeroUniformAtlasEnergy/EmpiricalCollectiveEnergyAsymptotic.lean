import GenuineZeroUniformAtlasEnergy.NativeCutoffGlobalRemainder

/-!
# Explicit collective critical-energy asymptotic

The sharp camerawise tail estimate is converted here into a quadratic-energy
estimate for the faithful empirical stack C2--C7.

For `s_t = 1/2 + i t`, let `A(t)` be the six-camera leading tail vector and
let `K_camera(t)` be the explicit camerawise remainder constant proved in
`NativeCutoffGlobalRemainder`.  The scaled tail vector differs componentwise
from `A(t)` by at most `K_camera(t) / M`.  Squaring the norm and summing gives
an explicit bound for

```math
M^3 E_M(t) - ||A(t)||^2.
```

Dividing by the exact positive scale gives

```math
|E_M(t) - ||A(t)||^2 M^{-3}|
  <= B_M(t) M^{-3},
```

where `B_M(t)` is a displayed finite sum of terms of order `M^{-1}` and
`M^{-2}`.  Thus the raw collective energy has an explicit `O_t(M^{-4})`
remainder.  At a common six-camera resonance, the same statement applies to
the finite empirical characteristic because its finite residue is exactly the
negative unresolved tail.
-/

open scoped BigOperators

namespace GenuineZeroUniformAtlasEnergy

open CPFormal.Analytic.Cp

noncomputable section

/-- Camerawise constant in the sharp critical tail remainder. -/
def empiricalNativeCriticalTailRemainderConstant
    (camera : EmpiricalCamera) (time : ℝ) : ℝ :=
  nativeExplicitRadiusCriticalTailRemainderConstant
    camera.period (camera.label / 2) time

/-- Naturally scaled unresolved tail of one empirical camera. -/
def empiricalScaledCameraCutoffTail
    (camera : EmpiricalCamera) (M : ℕ) (time : ℝ) : ℂ :=
  (M : ℂ) ^ (criticalLineParameter time + 1) *
    empiricalCameraCutoffTail camera M (criticalLineParameter time)

/-- Squared norm of the naturally scaled six-camera cutoff-tail stack. -/
def empiricalScaledCollectiveCutoffTailEnergy
    (M : ℕ) (time : ℝ) : ℝ :=
  ∑ camera : EmpiricalCamera,
    ‖empiricalScaledCameraCutoffTail camera M time‖ ^ 2

/-- Explicit scaled-energy error supplied by the six camerawise `K/M`
bounds. -/
def empiricalCollectiveCriticalScaledEnergyErrorBound
    (M : ℕ) (time : ℝ) : ℝ :=
  ∑ camera : EmpiricalCamera,
    (2 *
        ‖empiricalNativeTailCoefficient camera
          (criticalLineParameter time)‖ *
        (empiricalNativeCriticalTailRemainderConstant camera time /
          (M : ℝ)) +
      (empiricalNativeCriticalTailRemainderConstant camera time /
        (M : ℝ)) ^ 2)

/-- The corresponding raw-energy error after division by the exact critical
scale `M^3`. -/
def empiricalCollectiveCriticalRawEnergyErrorBound
    (M : ℕ) (time : ℝ) : ℝ :=
  empiricalCollectiveCriticalScaledEnergyErrorBound M time /
    (M : ℝ) ^ (3 : ℝ)

/-- The retained empirical radius cutoff fits the period margin required by
the sharp explicit-radius estimate. -/
lemma empiricalCamera_halfLabel_le_period_sub_one
    (camera : EmpiricalCamera) :
    camera.label / 2 ≤ camera.period - 1 := by
  cases camera <;> norm_num

lemma empiricalNativeCriticalTailRemainderConstant_nonneg
    (camera : EmpiricalCamera) (time : ℝ) :
    0 ≤ empiricalNativeCriticalTailRemainderConstant camera time := by
  unfold empiricalNativeCriticalTailRemainderConstant
    nativeExplicitRadiusCriticalTailRemainderConstant
    nativeRadiusSecondMoment nativeRadiusThirdMoment
  positivity

/-- Camerawise scaled tail convergence with the exact empirical geometry
substituted into the sharp explicit-radius theorem. -/
lemma norm_empiricalScaledCameraCutoffTail_sub_coefficient_critical_le
    (camera : EmpiricalCamera) (M : ℕ) (hM : 1 ≤ M) (time : ℝ) :
    ‖empiricalScaledCameraCutoffTail camera M time -
        empiricalNativeTailCoefficient camera
          (criticalLineParameter time)‖ ≤
      empiricalNativeCriticalTailRemainderConstant camera time /
        (M : ℝ) := by
  have hb : 1 ≤ camera.period := by
    exact empiricalCamera_period_pos camera
  have hh : camera.label / 2 ≤ camera.period - 1 :=
    empiricalCamera_halfLabel_le_period_sub_one camera
  unfold empiricalScaledCameraCutoffTail
    empiricalNativeCriticalTailRemainderConstant
    empiricalNativeTailCoefficient
  rw [empiricalCameraCutoffTail_eq_nativeExplicitRadiusCutoffTail]
  exact
    norm_scaled_nativeExplicitRadiusCutoffTail_sub_coefficient_critical_le
      camera.period (camera.label / 2) M hb hh hM time

/-- Squaring a norm approximation costs at most `2 ||a|| epsilon + epsilon^2`.
This elementary lemma is kept explicit because the same estimate will be
reused for derivative and Hessian expansions. -/
lemma abs_sq_norm_sub_sq_norm_le_of_norm_sub_le
    (x a : ℂ) {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (h : ‖x - a‖ ≤ epsilon) :
    |‖x‖ ^ 2 - ‖a‖ ^ 2| ≤
      2 * ‖a‖ * epsilon + epsilon ^ 2 := by
  have hx0 : 0 ≤ ‖x‖ := norm_nonneg x
  have ha0 : 0 ≤ ‖a‖ := norm_nonneg a
  have hxle : ‖x‖ ≤ ‖a‖ + epsilon := by
    calc
      ‖x‖ = ‖(x - a) + a‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - a‖ + ‖a‖ := norm_add_le _ _
      _ ≤ epsilon + ‖a‖ := add_le_add h (le_refl _)
      _ = ‖a‖ + epsilon := by ring
  have hale : ‖a‖ ≤ ‖x‖ + epsilon := by
    calc
      ‖a‖ = ‖(a - x) + x‖ := by rw [sub_add_cancel]
      _ ≤ ‖a - x‖ + ‖x‖ := norm_add_le _ _
      _ = ‖x - a‖ + ‖x‖ := by rw [norm_sub_rev]
      _ ≤ epsilon + ‖x‖ := add_le_add h (le_refl _)
      _ = ‖x‖ + epsilon := by ring
  by_cases hax : ‖a‖ ≤ ‖x‖
  · have hdiff : 0 ≤ ‖x‖ ^ 2 - ‖a‖ ^ 2 := by
      have hproduct := mul_nonneg
        (sub_nonneg.mpr hax) (add_nonneg hx0 ha0)
      nlinarith
    rw [abs_of_nonneg hdiff]
    have hproduct := mul_nonneg
      (sub_nonneg.mpr hxle)
      (add_nonneg (add_nonneg ha0 hepsilon) hx0)
    nlinarith
  · have hxa : ‖x‖ ≤ ‖a‖ :=
      le_of_lt (lt_of_not_ge hax)
    have hdiff : ‖x‖ ^ 2 - ‖a‖ ^ 2 ≤ 0 := by
      have hproduct := mul_nonneg
        (sub_nonneg.mpr hxa) (add_nonneg ha0 hx0)
      nlinarith
    rw [abs_of_nonpos hdiff]
    have hproduct := mul_nonneg
      (sub_nonneg.mpr hale)
      (add_nonneg (add_nonneg hx0 hepsilon) ha0)
    have hweighted := mul_nonneg (sub_nonneg.mpr hxa) hepsilon
    nlinarith

/-- Exact norm of the critical scaling factor, squared. -/
lemma norm_criticalCutoffScale_sq
    (M : ℕ) (hM : 1 ≤ M) (time : ℝ) :
    ‖(M : ℂ) ^ (criticalLineParameter time + 1)‖ ^ 2 =
      (M : ℝ) ^ (3 : ℝ) := by
  have hMpos : 0 < (M : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)
  have hre :
      (criticalLineParameter time + 1).re = (3 / 2 : ℝ) := by
    norm_num [criticalLineParameter_re]
  have hnorm :=
    Complex.norm_cpow_eq_rpow_re_of_pos hMpos
      (criticalLineParameter time + 1)
  rw [hre] at hnorm
  have hcast : (M : ℂ) = ((M : ℝ) : ℂ) := by norm_cast
  rw [hcast, hnorm]
  calc
    ((M : ℝ) ^ (3 / 2 : ℝ)) ^ 2 =
        (M : ℝ) ^ ((3 / 2 : ℝ) * (2 : ℝ)) := by
      exact (Real.rpow_mul_natCast hMpos.le (3 / 2 : ℝ) 2).symm
    _ = (M : ℝ) ^ (3 : ℝ) := by norm_num

/-- The scaled collective energy is exactly `M^3` times the unscaled tail
energy. -/
theorem empiricalScaledCollectiveCutoffTailEnergy_eq
    (M : ℕ) (hM : 1 ≤ M) (time : ℝ) :
    empiricalScaledCollectiveCutoffTailEnergy M time =
      (M : ℝ) ^ (3 : ℝ) *
        empiricalCollectiveCutoffTailEnergy M
          (criticalLineParameter time) := by
  classical
  unfold empiricalScaledCollectiveCutoffTailEnergy
    empiricalScaledCameraCutoffTail
    empiricalCollectiveCutoffTailEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro camera _hcamera
  rw [norm_mul, mul_pow,
    norm_criticalCutoffScale_sq M hM time]
  simp [Complex.sq_norm]

/-- Explicit six-camera estimate for the scaled collective energy. -/
lemma abs_empiricalScaledCollectiveCutoffTailEnergy_sub_coefficientNormSq_le
    (M : ℕ) (hM : 1 ≤ M) (time : ℝ) :
    |empiricalScaledCollectiveCutoffTailEnergy M time -
        empiricalNativeTailCoefficientNormSq time| ≤
      empiricalCollectiveCriticalScaledEnergyErrorBound M time := by
  classical
  unfold empiricalScaledCollectiveCutoffTailEnergy
    empiricalNativeTailCoefficientNormSq
    empiricalCollectiveCriticalScaledEnergyErrorBound
  have hsum :
      (∑ camera : EmpiricalCamera,
        (‖empiricalScaledCameraCutoffTail camera M time‖ ^ 2 -
          ‖empiricalNativeTailCoefficient camera
            (criticalLineParameter time)‖ ^ 2)) =
      (∑ camera : EmpiricalCamera,
        ‖empiricalScaledCameraCutoffTail camera M time‖ ^ 2) -
      ∑ camera : EmpiricalCamera,
        ‖empiricalNativeTailCoefficient camera
          (criticalLineParameter time)‖ ^ 2 := by
    rw [Finset.sum_sub_distrib]
  rw [← hsum]
  calc
    |∑ camera : EmpiricalCamera,
        (‖empiricalScaledCameraCutoffTail camera M time‖ ^ 2 -
          ‖empiricalNativeTailCoefficient camera
            (criticalLineParameter time)‖ ^ 2)| ≤
      ∑ camera : EmpiricalCamera,
        |‖empiricalScaledCameraCutoffTail camera M time‖ ^ 2 -
          ‖empiricalNativeTailCoefficient camera
            (criticalLineParameter time)‖ ^ 2| := by
      simpa [Real.norm_eq_abs] using
        (norm_sum_le (Finset.univ : Finset EmpiricalCamera)
          (fun camera =>
            ‖empiricalScaledCameraCutoffTail camera M time‖ ^ 2 -
              ‖empiricalNativeTailCoefficient camera
                (criticalLineParameter time)‖ ^ 2))
    _ ≤ ∑ camera : EmpiricalCamera,
        (2 *
            ‖empiricalNativeTailCoefficient camera
              (criticalLineParameter time)‖ *
            (empiricalNativeCriticalTailRemainderConstant camera time /
              (M : ℝ)) +
          (empiricalNativeCriticalTailRemainderConstant camera time /
            (M : ℝ)) ^ 2) := by
      apply Finset.sum_le_sum
      intro camera _hcamera
      apply abs_sq_norm_sub_sq_norm_le_of_norm_sub_le
      · exact div_nonneg
          (empiricalNativeCriticalTailRemainderConstant_nonneg camera time)
          (by positivity)
      · exact
          norm_empiricalScaledCameraCutoffTail_sub_coefficient_critical_le
            camera M hM time

/-- Explicit raw-energy expansion of the unresolved six-camera tail.  The
right-hand side is the scaled `O(1/M)` error divided by the exact factor
`M^3`, hence is `O(M^(-4))`. -/
theorem abs_empiricalCollectiveCutoffTailEnergy_sub_leading_div_cube_le
    (M : ℕ) (hM : 1 ≤ M) (time : ℝ) :
    |empiricalCollectiveCutoffTailEnergy M
          (criticalLineParameter time) -
        empiricalNativeTailCoefficientNormSq time /
          (M : ℝ) ^ (3 : ℝ)| ≤
      empiricalCollectiveCriticalRawEnergyErrorBound M time := by
  have hMpos : 0 < (M : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)
  have hdenpos : 0 < (M : ℝ) ^ (3 : ℝ) :=
    Real.rpow_pos_of_pos hMpos _
  have hscaled :=
    abs_empiricalScaledCollectiveCutoffTailEnergy_sub_coefficientNormSq_le
      M hM time
  rw [empiricalScaledCollectiveCutoffTailEnergy_eq M hM time] at hscaled
  have hrewrite :
      empiricalCollectiveCutoffTailEnergy M
          (criticalLineParameter time) -
        empiricalNativeTailCoefficientNormSq time /
          (M : ℝ) ^ (3 : ℝ) =
      ((M : ℝ) ^ (3 : ℝ) *
          empiricalCollectiveCutoffTailEnergy M
            (criticalLineParameter time) -
        empiricalNativeTailCoefficientNormSq time) /
          (M : ℝ) ^ (3 : ℝ) := by
    field_simp [ne_of_gt hdenpos]
  rw [hrewrite, abs_div, abs_of_pos hdenpos]
  exact div_le_div_of_nonneg_right hscaled hdenpos.le

/-- At a common six-camera resonance, the actual finite raw energy has the
explicit leading coefficient and `O(M^(-4))` remainder. -/
theorem empiricalSixCameraCriticalRawEnergy_explicit_remainder
    (M : ℕ) (hM : 1 ≤ M) (time : ℝ)
    (hzero : ∀ camera, empiricalCameraCharacteristic camera
      (criticalLineParameter time) = 0) :
    |finiteEmpiricalCollectiveRawEnergy M
          (criticalLineParameter time) -
        (‖criticalLineParameter time‖ ^ 2 *
          ((132244271 : ℝ) / 1778112000)) /
          (M : ℝ) ^ (3 : ℝ)| ≤
      empiricalCollectiveCriticalRawEnergyErrorBound M time := by
  have hstrip : -1 < (criticalLineParameter time).re := by
    norm_num [criticalLineParameter_re]
  rw [finiteEmpiricalCollectiveRawEnergy_eq_cutoffTailEnergy_of_zero
    M hstrip hzero]
  rw [← empiricalNativeTailCoefficientNormSq_eq time]
  exact
    abs_empiricalCollectiveCutoffTailEnergy_sub_leading_div_cube_le
      M hM time

end

end GenuineZeroUniformAtlasEnergy

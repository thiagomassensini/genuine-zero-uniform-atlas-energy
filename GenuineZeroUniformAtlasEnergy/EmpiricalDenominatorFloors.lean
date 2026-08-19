import GenuineZeroUniformAtlasEnergy.EmpiricalSecondJetDownstreamClosure
import GenuineZeroUniformAtlasEnergy.EmpiricalFiniteFirstJetBound

/-!
# Concrete empirical denominator floors

The exact cutoff identities already control both versions of the finite first
jet:

* the logarithmically corrected jet used by the reoptimized residual energy;
* the raw jet used by the transverse Hessian and its Schur complement.

This module absorbs every remaining critical cutoff factor into fixed
inverse-cutoff constants and proves eventual positive floors for

* the corrected finite clock Gram;
* the raw finite clock Gram;
* the temporal Schur denominator `|kappa_M-a_M|`.

No numerical height, finite-cutoff witness, or floating-point certificate is
used.  The only spectral hypotheses are a presented critical Genuine zero and
nonvanishing of its first derivative, exactly as required by the quadratic
multiplicity-one sector.
-/

open Filter
open scoped BigOperators

namespace GenuineZeroUniformAtlasEnergy

open CPFormal.Analytic.Cp

noncomputable section

/-- On the critical line the exact cutoff scale has norm `M^(-3/2)`. -/
theorem norm_nativeCutoffScale_critical_eq
    (M : ℕ) (hM : 1 ≤ M) (time : ℝ) :
    ‖nativeCutoffScale M (criticalLineParameter time)‖ =
      (M : ℝ) ^ (-(3 : ℝ) / 2) := by
  unfold nativeCutoffScale
  rw [Complex.norm_natCast_cpow_of_pos (by omega)]
  have hexponent :
      (-criticalLineParameter time - 1).re = -(3 : ℝ) / 2 := by
    simp only [Complex.sub_re, Complex.neg_re, criticalLineParameter_re,
      Complex.one_re]
    norm_num
  rw [hexponent]

/-- The critical cutoff scale is bounded by the simpler inverse-cutoff rate. -/
theorem norm_nativeCutoffScale_critical_le_inv
    (M : ℕ) (hM : 1 ≤ M) (time : ℝ) :
    ‖nativeCutoffScale M (criticalLineParameter time)‖ ≤
      1 / (M : ℝ) := by
  rw [norm_nativeCutoffScale_critical_eq M hM time]
  have hMreal : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hpower :
      (M : ℝ) ^ (-(3 : ℝ) / 2) ≤ (M : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hMreal (by norm_num)
  simpa [Real.rpow_neg_one, one_div] using hpower

/-- The complex cutoff logarithm is the nonnegative real logarithm of the
positive natural cutoff. -/
theorem norm_nativeCutoffLog_eq_realLog
    (M : ℕ) (hM : 1 ≤ M) :
    ‖nativeCutoffLog M‖ = Real.log (M : ℝ) := by
  have hMreal : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  simp [nativeCutoffLog, Real.norm_eq_abs,
    abs_of_nonneg (Real.log_nonneg hMreal)]

/-- The logarithm carried by the raw first jet is absorbed by the stronger
critical `M^(-3/2)` value decay. -/
theorem norm_nativeCutoffLog_mul_rpow_neg_three_halves_le_two_div
    (M : ℕ) (hM : 1 ≤ M) :
    ‖nativeCutoffLog M‖ * (M : ℝ) ^ (-(3 : ℝ) / 2) ≤
      2 / (M : ℝ) := by
  have hMreal : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hMnonneg : (0 : ℝ) ≤ (M : ℝ) := zero_le_one.trans hMreal
  have hMpos : (0 : ℝ) < (M : ℝ) := zero_lt_one.trans_le hMreal
  have hlog :=
    Real.log_natCast_le_rpow_div M (by norm_num : (0 : ℝ) < 1 / 2)
  have hlogBound :
      Real.log (M : ℝ) ≤ 2 * (M : ℝ) ^ (1 / 2 : ℝ) := by
    calc
      Real.log (M : ℝ) ≤
          (M : ℝ) ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) := by
        simpa using hlog
      _ = 2 * (M : ℝ) ^ (1 / 2 : ℝ) := by ring
  rw [norm_nativeCutoffLog_eq_realLog M hM]
  calc
    Real.log (M : ℝ) * (M : ℝ) ^ (-(3 : ℝ) / 2) ≤
        (2 * (M : ℝ) ^ (1 / 2 : ℝ)) *
          (M : ℝ) ^ (-(3 : ℝ) / 2) :=
      mul_le_mul_of_nonneg_right hlogBound
        (Real.rpow_nonneg hMnonneg _)
    _ = 2 *
        ((M : ℝ) ^ (1 / 2 : ℝ) *
          (M : ℝ) ^ (-(3 : ℝ) / 2)) := by ring
    _ = 2 * (M : ℝ) ^ (-1 : ℝ) := by
      rw [← Real.rpow_add hMpos]
      norm_num
    _ = 2 / (M : ℝ) := by
      rw [Real.rpow_neg_one]
      ring

/-! ## Corrected first jet and corrected clock Gram -/

/-- Fixed camerawise inverse-cutoff constant for the corrected first jet. -/
def empiricalCameraCorrectedFirstJetInverseCutoffConstant
    (camera : EmpiricalCamera) (time : ℝ) : ℝ :=
  ‖deriv (empiricalNativeTailCoefficient camera)
      (criticalLineParameter time)‖ +
    empiricalScaledCameraTailCauchyConstant camera time /
      nativeExplicitRadiusCriticalCauchyRadius

lemma empiricalCameraCorrectedFirstJetInverseCutoffConstant_nonneg
    (camera : EmpiricalCamera) (time : ℝ) :
    0 ≤ empiricalCameraCorrectedFirstJetInverseCutoffConstant camera time := by
  unfold empiricalCameraCorrectedFirstJetInverseCutoffConstant
  have hconstant := empiricalScaledCameraTailCauchyConstant_nonneg camera time
  have hradius : 0 ≤ nativeExplicitRadiusCriticalCauchyRadius := by
    norm_num [nativeExplicitRadiusCriticalCauchyRadius]
  exact add_nonneg (norm_nonneg _) (div_nonneg hconstant hradius)

/-- Each corrected first-jet error is bounded by one fixed `C_b(t)/M`. -/
theorem empiricalFiniteCorrectedCameraFirstJetErrorBound_le_inverseCutoff
    (camera : EmpiricalCamera) (M : ℕ) (hM : 1 ≤ M) (time : ℝ) :
    empiricalFiniteCorrectedCameraFirstJetErrorBound camera M time ≤
      empiricalCameraCorrectedFirstJetInverseCutoffConstant camera time /
        (M : ℝ) := by
  have hMreal : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hscale := norm_nativeCutoffScale_critical_le_inv M hM time
  have hconstant := empiricalScaledCameraTailCauchyConstant_nonneg camera time
  have hradiusPos : 0 < nativeExplicitRadiusCriticalCauchyRadius := by
    norm_num [nativeExplicitRadiusCriticalCauchyRadius]
  have hscaledConstant :
      (empiricalScaledCameraTailCauchyConstant camera time / (M : ℝ)) /
          nativeExplicitRadiusCriticalCauchyRadius ≤
        empiricalScaledCameraTailCauchyConstant camera time /
          nativeExplicitRadiusCriticalCauchyRadius := by
    apply div_le_div_of_nonneg_right _ hradiusPos.le
    exact div_le_self hconstant hMreal
  have hinside :
      ‖deriv (empiricalNativeTailCoefficient camera)
          (criticalLineParameter time)‖ +
          (empiricalScaledCameraTailCauchyConstant camera time / (M : ℝ)) /
            nativeExplicitRadiusCriticalCauchyRadius ≤
        empiricalCameraCorrectedFirstJetInverseCutoffConstant camera time := by
    unfold empiricalCameraCorrectedFirstJetInverseCutoffConstant
    exact add_le_add le_rfl hscaledConstant
  have hinsideNonneg :
      0 ≤ ‖deriv (empiricalNativeTailCoefficient camera)
          (criticalLineParameter time)‖ +
          (empiricalScaledCameraTailCauchyConstant camera time / (M : ℝ)) /
            nativeExplicitRadiusCriticalCauchyRadius := by
    have hMnonneg : 0 ≤ (M : ℝ) := by positivity
    exact add_nonneg (norm_nonneg _)
      (div_nonneg (div_nonneg hconstant hMnonneg) hradiusPos.le)
  unfold empiricalFiniteCorrectedCameraFirstJetErrorBound
  calc
    ‖nativeCutoffScale M (criticalLineParameter time)‖ *
        (‖deriv (empiricalNativeTailCoefficient camera)
            (criticalLineParameter time)‖ +
          (empiricalScaledCameraTailCauchyConstant camera time / (M : ℝ)) /
            nativeExplicitRadiusCriticalCauchyRadius) ≤
      (1 / (M : ℝ)) *
        empiricalCameraCorrectedFirstJetInverseCutoffConstant camera time :=
      mul_le_mul hscale hinside hinsideNonneg (by positivity)
    _ = empiricalCameraCorrectedFirstJetInverseCutoffConstant camera time /
        (M : ℝ) := by ring

/-- Fixed six-camera corrected first-jet constant.  The `l1` aggregation keeps
all cutoff dependence outside the constant. -/
def empiricalCorrectedFirstJetInverseCutoffConstant (time : ℝ) : ℝ :=
  ∑ camera : EmpiricalCamera,
    empiricalCameraCorrectedFirstJetInverseCutoffConstant camera time

lemma empiricalCorrectedFirstJetInverseCutoffConstant_nonneg
    (time : ℝ) :
    0 ≤ empiricalCorrectedFirstJetInverseCutoffConstant time := by
  unfold empiricalCorrectedFirstJetInverseCutoffConstant
  exact Finset.sum_nonneg fun camera _ =>
    empiricalCameraCorrectedFirstJetInverseCutoffConstant_nonneg camera time

private theorem empiricalFiniteCorrectedCameraFirstJetErrorBound_nonneg
    (camera : EmpiricalCamera) (M : ℕ) (time : ℝ) :
    0 ≤ empiricalFiniteCorrectedCameraFirstJetErrorBound camera M time := by
  unfold empiricalFiniteCorrectedCameraFirstJetErrorBound
  have hconstant := empiricalScaledCameraTailCauchyConstant_nonneg camera time
  have hMnonneg : 0 ≤ (M : ℝ) := by positivity
  have hradius : 0 ≤ nativeExplicitRadiusCriticalCauchyRadius := by
    norm_num [nativeExplicitRadiusCriticalCauchyRadius]
  exact mul_nonneg (norm_nonneg _)
    (add_nonneg (norm_nonneg _)
      (div_nonneg (div_nonneg hconstant hMnonneg) hradius))

/-- The complete corrected first-jet stack has a fixed `C_V(t)/M` error. -/
theorem empiricalFiniteCorrectedFirstJetStackErrorBound_le_inverseCutoff
    (M : ℕ) (hM : 1 ≤ M) (time : ℝ) :
    empiricalFiniteCorrectedFirstJetStackErrorBound M time ≤
      empiricalCorrectedFirstJetInverseCutoffConstant time / (M : ℝ) := by
  have hnonneg :
      ∀ camera ∈ (Finset.univ : Finset EmpiricalCamera),
        0 ≤ empiricalFiniteCorrectedCameraFirstJetErrorBound camera M time := by
    intro camera _
    exact empiricalFiniteCorrectedCameraFirstJetErrorBound_nonneg camera M time
  have hsquares :=
    Finset.sum_sq_le_sq_sum_of_nonneg
      (s := (Finset.univ : Finset EmpiricalCamera))
      (f := fun camera =>
        empiricalFiniteCorrectedCameraFirstJetErrorBound camera M time)
      hnonneg
  have hsumNonneg :
      0 ≤ ∑ camera : EmpiricalCamera,
        empiricalFiniteCorrectedCameraFirstJetErrorBound camera M time :=
    Finset.sum_nonneg fun camera _ =>
      empiricalFiniteCorrectedCameraFirstJetErrorBound_nonneg camera M time
  have hsqrtL1 :
      Real.sqrt
          (∑ camera : EmpiricalCamera,
            empiricalFiniteCorrectedCameraFirstJetErrorBound camera M time ^ 2) ≤
        ∑ camera : EmpiricalCamera,
          empiricalFiniteCorrectedCameraFirstJetErrorBound camera M time := by
    rw [Real.sqrt_le_iff]
    exact ⟨hsumNonneg, hsquares⟩
  calc
    empiricalFiniteCorrectedFirstJetStackErrorBound M time =
        Real.sqrt
          (∑ camera : EmpiricalCamera,
            empiricalFiniteCorrectedCameraFirstJetErrorBound camera M time ^ 2) := rfl
    _ ≤ ∑ camera : EmpiricalCamera,
        empiricalFiniteCorrectedCameraFirstJetErrorBound camera M time := hsqrtL1
    _ ≤ ∑ camera : EmpiricalCamera,
        empiricalCameraCorrectedFirstJetInverseCutoffConstant camera time /
          (M : ℝ) := by
      exact Finset.sum_le_sum fun camera _ =>
        empiricalFiniteCorrectedCameraFirstJetErrorBound_le_inverseCutoff
          camera M hM time
    _ = empiricalCorrectedFirstJetInverseCutoffConstant time / (M : ℝ) := by
      simp [empiricalCorrectedFirstJetInverseCutoffConstant, Finset.sum_div]

/-- Fixed inverse-cutoff constant for the corrected finite clock Gram. -/
def empiricalCorrectedKappaInverseCutoffConstant (time : ℝ) : ℝ :=
  empiricalCorrectedFirstJetInverseCutoffConstant time *
    (empiricalCorrectedFirstJetInverseCutoffConstant time +
      2 * ‖empiricalClockTangentVector (criticalLineParameter time)‖)

lemma empiricalCorrectedKappaInverseCutoffConstant_nonneg
    (time : ℝ) :
    0 ≤ empiricalCorrectedKappaInverseCutoffConstant time := by
  have hfixed := empiricalCorrectedFirstJetInverseCutoffConstant_nonneg time
  exact mul_nonneg hfixed
    (add_nonneg hfixed
      (mul_nonneg (by norm_num)
        (norm_nonneg
          (empiricalClockTangentVector (criticalLineParameter time)))))

/-- The corrected finite clock Gram differs from its limiting value by one
fixed inverse-cutoff constant. -/
theorem abs_finiteEmpiricalCorrectedKappa_sub_model_le_inverseCutoff
    (M : ℕ) (hM : 1 ≤ M) (time : ℝ)
    (hzero : genuineContinuation (criticalLineParameter time) = 0) :
    |empiricalQuadraticClockKappa
          (finiteEmpiricalCameraCorrectedDerivativeStack M
            (criticalLineParameter time)) -
        empiricalStackKappa (criticalLineParameter time)| ≤
      empiricalCorrectedKappaInverseCutoffConstant time / (M : ℝ) := by
  let error := empiricalFiniteCorrectedFirstJetStackErrorBound M time
  let fixed := empiricalCorrectedFirstJetInverseCutoffConstant time
  let tangent := empiricalClockTangentVector (criticalLineParameter time)
  have hfirst :=
    norm_finiteEmpiricalCameraCorrectedDerivativeStack_sub_clockTangent_le
      M hM time hzero
  have hraw :=
    abs_empiricalQuadraticClockKappa_sub_le_of_norm_sub_le
      (finiteEmpiricalCameraCorrectedDerivativeStack M
        (criticalLineParameter time)) tangent error hfirst
  have herror :=
    empiricalFiniteCorrectedFirstJetStackErrorBound_le_inverseCutoff M hM time
  have hMreal : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hfixedNonneg : 0 ≤ fixed := by
    exact empiricalCorrectedFirstJetInverseCutoffConstant_nonneg time
  have herrorNonneg : 0 ≤ error := by
    dsimp [error]
    exact Real.sqrt_nonneg _
  have hdivNonneg : 0 ≤ fixed / (M : ℝ) :=
    div_nonneg hfixedNonneg (by positivity)
  have herrorFixed : error ≤ fixed :=
    herror.trans (div_le_self hfixedNonneg hMreal)
  have hsum : error + 2 * ‖tangent‖ ≤ fixed + 2 * ‖tangent‖ :=
    add_le_add herrorFixed le_rfl
  have hproduct :
      error * (error + 2 * ‖tangent‖) ≤
        (fixed / (M : ℝ)) * (fixed + 2 * ‖tangent‖) :=
    mul_le_mul herror hsum (by positivity) hdivNonneg
  calc
    |empiricalQuadraticClockKappa
          (finiteEmpiricalCameraCorrectedDerivativeStack M
            (criticalLineParameter time)) -
        empiricalStackKappa (criticalLineParameter time)| ≤
      error * (error + 2 * ‖tangent‖) := by
        simpa [tangent, empiricalQuadraticClockKappa, empiricalStackKappa]
          using hraw
    _ ≤ (fixed / (M : ℝ)) * (fixed + 2 * ‖tangent‖) := hproduct
    _ = empiricalCorrectedKappaInverseCutoffConstant time / (M : ℝ) := by
      unfold empiricalCorrectedKappaInverseCutoffConstant
      dsimp [fixed, tangent]
      ring

/-- Eventually the corrected finite clock Gram is at least half of the exact
positive limiting Gram scalar. -/
theorem eventually_finiteEmpiricalCorrectedKappa_ge_half
    (time : ℝ)
    (hzero : genuineContinuation (criticalLineParameter time) = 0)
    (hsimple : deriv genuineContinuation (criticalLineParameter time) ≠ 0) :
    ∀ᶠ M : ℕ in atTop,
      empiricalStackKappa (criticalLineParameter time) / 2 ≤
        empiricalQuadraticClockKappa
          (finiteEmpiricalCameraCorrectedDerivativeStack M
            (criticalLineParameter time)) := by
  let kappa := empiricalStackKappa (criticalLineParameter time)
  let C := empiricalCorrectedKappaInverseCutoffConstant time
  have hkappa : 0 < kappa := by
    dsimp [kappa]
    exact empiricalStackKappa_pos (by norm_num [criticalLineParameter_re]) hsimple
  have hratio : Tendsto (fun M : ℕ => C / (M : ℝ)) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat C
  have hsmall : ∀ᶠ M : ℕ in atTop, C / (M : ℝ) < kappa / 2 :=
    hratio.eventually (Iio_mem_nhds (by linarith : 0 < kappa / 2))
  filter_upwards [hsmall, eventually_ge_atTop 1] with M hMsmall hM
  have hdiff :=
    abs_finiteEmpiricalCorrectedKappa_sub_model_le_inverseCutoff
      M hM time hzero
  have hlower := (abs_le.mp hdiff).1
  dsimp [C, kappa] at hMsmall hlower ⊢
  linarith

/-! ## Raw first jet and the transverse Schur denominator -/

/-- The coefficient of the raw `M^(-3/2)` residual bound. -/
def empiricalCameraRawResidualThreeHalvesConstant
    (camera : EmpiricalCamera) (time : ℝ) : ℝ :=
  (2 / 3 : ℝ) *
    empiricalCameraBracketMajorantConstant camera
      (criticalLineParameter time)

lemma empiricalCameraRawResidualThreeHalvesConstant_nonneg
    (camera : EmpiricalCamera) (time : ℝ) :
    0 ≤ empiricalCameraRawResidualThreeHalvesConstant camera time := by
  unfold empiricalCameraRawResidualThreeHalvesConstant
    empiricalCameraBracketMajorantConstant
  positivity

/-- Fixed camerawise inverse-cutoff constant for the raw first jet. -/
def empiricalCameraRawFirstJetInverseCutoffConstant
    (camera : EmpiricalCamera) (time : ℝ) : ℝ :=
  empiricalCameraCorrectedFirstJetInverseCutoffConstant camera time +
    2 * empiricalCameraRawResidualThreeHalvesConstant camera time

lemma empiricalCameraRawFirstJetInverseCutoffConstant_nonneg
    (camera : EmpiricalCamera) (time : ℝ) :
    0 ≤ empiricalCameraRawFirstJetInverseCutoffConstant camera time := by
  unfold empiricalCameraRawFirstJetInverseCutoffConstant
  exact add_nonneg
    (empiricalCameraCorrectedFirstJetInverseCutoffConstant_nonneg camera time)
    (mul_nonneg (by norm_num)
      (empiricalCameraRawResidualThreeHalvesConstant_nonneg camera time))

/-- The raw camerawise first-jet error has a fixed `C_b(t)/M` bound. -/
theorem empiricalFiniteCameraFirstJetErrorBound_le_inverseCutoff
    (camera : EmpiricalCamera) (M : ℕ) (hM : 1 ≤ M) (time : ℝ) :
    empiricalFiniteCameraFirstJetErrorBound camera M time ≤
      empiricalCameraRawFirstJetInverseCutoffConstant camera time / (M : ℝ) := by
  have hcorrected :=
    empiricalFiniteCorrectedCameraFirstJetErrorBound_le_inverseCutoff
      camera M hM time
  have hlogPower :=
    norm_nativeCutoffLog_mul_rpow_neg_three_halves_le_two_div M hM
  have hresNonneg :=
    empiricalCameraRawResidualThreeHalvesConstant_nonneg camera time
  have hlogTail :
      ‖nativeCutoffLog M‖ * empiricalCameraCriticalTailBound camera M time ≤
        (2 * empiricalCameraRawResidualThreeHalvesConstant camera time) /
          (M : ℝ) := by
    unfold empiricalCameraCriticalTailBound
    calc
      ‖nativeCutoffLog M‖ *
          ((2 / 3 : ℝ) *
            empiricalCameraBracketMajorantConstant camera
              (criticalLineParameter time) *
            (M : ℝ) ^ (-(3 / 2 : ℝ))) =
        empiricalCameraRawResidualThreeHalvesConstant camera time *
          (‖nativeCutoffLog M‖ *
            (M : ℝ) ^ (-(3 : ℝ) / 2)) := by
          unfold empiricalCameraRawResidualThreeHalvesConstant
          ring
      _ ≤ empiricalCameraRawResidualThreeHalvesConstant camera time *
          (2 / (M : ℝ)) :=
        mul_le_mul_of_nonneg_left hlogPower hresNonneg
      _ = (2 * empiricalCameraRawResidualThreeHalvesConstant camera time) /
          (M : ℝ) := by ring
  unfold empiricalFiniteCameraFirstJetErrorBound
  change
    empiricalFiniteCorrectedCameraFirstJetErrorBound camera M time +
        ‖nativeCutoffLog M‖ * empiricalCameraCriticalTailBound camera M time ≤
      empiricalCameraRawFirstJetInverseCutoffConstant camera time / (M : ℝ)
  calc
    empiricalFiniteCorrectedCameraFirstJetErrorBound camera M time +
        ‖nativeCutoffLog M‖ * empiricalCameraCriticalTailBound camera M time ≤
      empiricalCameraCorrectedFirstJetInverseCutoffConstant camera time /
          (M : ℝ) +
        (2 * empiricalCameraRawResidualThreeHalvesConstant camera time) /
          (M : ℝ) := add_le_add hcorrected hlogTail
    _ = empiricalCameraRawFirstJetInverseCutoffConstant camera time /
        (M : ℝ) := by
      unfold empiricalCameraRawFirstJetInverseCutoffConstant
      ring

/-- Fixed six-camera inverse-cutoff constant for the raw first jet. -/
def empiricalRawFirstJetInverseCutoffConstant (time : ℝ) : ℝ :=
  ∑ camera : EmpiricalCamera,
    empiricalCameraRawFirstJetInverseCutoffConstant camera time

lemma empiricalRawFirstJetInverseCutoffConstant_nonneg (time : ℝ) :
    0 ≤ empiricalRawFirstJetInverseCutoffConstant time := by
  unfold empiricalRawFirstJetInverseCutoffConstant
  exact Finset.sum_nonneg fun camera _ =>
    empiricalCameraRawFirstJetInverseCutoffConstant_nonneg camera time

private theorem empiricalFiniteCameraFirstJetErrorBound_nonneg
    (camera : EmpiricalCamera) (M : ℕ) (time : ℝ) :
    0 ≤ empiricalFiniteCameraFirstJetErrorBound camera M time := by
  unfold empiricalFiniteCameraFirstJetErrorBound
  have hcorrected :=
    empiricalFiniteCorrectedCameraFirstJetErrorBound_nonneg camera M time
  have htail : 0 ≤ empiricalCameraCriticalTailBound camera M time := by
    unfold empiricalCameraCriticalTailBound
      empiricalCameraBracketMajorantConstant
    positivity
  exact add_nonneg hcorrected (mul_nonneg (norm_nonneg _) htail)

/-- The complete raw derivative stack differs from the limiting tangent by one
fixed inverse-cutoff constant. -/
theorem empiricalFiniteFirstJetStackErrorBound_le_inverseCutoff
    (M : ℕ) (hM : 1 ≤ M) (time : ℝ) :
    empiricalFiniteFirstJetStackErrorBound M time ≤
      empiricalRawFirstJetInverseCutoffConstant time / (M : ℝ) := by
  have hnonneg :
      ∀ camera ∈ (Finset.univ : Finset EmpiricalCamera),
        0 ≤ empiricalFiniteCameraFirstJetErrorBound camera M time := by
    intro camera _
    exact empiricalFiniteCameraFirstJetErrorBound_nonneg camera M time
  have hsquares :=
    Finset.sum_sq_le_sq_sum_of_nonneg
      (s := (Finset.univ : Finset EmpiricalCamera))
      (f := fun camera => empiricalFiniteCameraFirstJetErrorBound camera M time)
      hnonneg
  have hsumNonneg :
      0 ≤ ∑ camera : EmpiricalCamera,
        empiricalFiniteCameraFirstJetErrorBound camera M time :=
    Finset.sum_nonneg fun camera _ =>
      empiricalFiniteCameraFirstJetErrorBound_nonneg camera M time
  have hsqrtL1 :
      Real.sqrt
          (∑ camera : EmpiricalCamera,
            empiricalFiniteCameraFirstJetErrorBound camera M time ^ 2) ≤
        ∑ camera : EmpiricalCamera,
          empiricalFiniteCameraFirstJetErrorBound camera M time := by
    rw [Real.sqrt_le_iff]
    exact ⟨hsumNonneg, hsquares⟩
  calc
    empiricalFiniteFirstJetStackErrorBound M time =
        Real.sqrt
          (∑ camera : EmpiricalCamera,
            empiricalFiniteCameraFirstJetErrorBound camera M time ^ 2) := rfl
    _ ≤ ∑ camera : EmpiricalCamera,
        empiricalFiniteCameraFirstJetErrorBound camera M time := hsqrtL1
    _ ≤ ∑ camera : EmpiricalCamera,
        empiricalCameraRawFirstJetInverseCutoffConstant camera time /
          (M : ℝ) := by
      exact Finset.sum_le_sum fun camera _ =>
        empiricalFiniteCameraFirstJetErrorBound_le_inverseCutoff
          camera M hM time
    _ = empiricalRawFirstJetInverseCutoffConstant time / (M : ℝ) := by
      simp [empiricalRawFirstJetInverseCutoffConstant, Finset.sum_div]

/-- Fixed inverse-cutoff constant for the raw finite clock Gram. -/
def empiricalRawKappaInverseCutoffConstant (time : ℝ) : ℝ :=
  empiricalRawFirstJetInverseCutoffConstant time *
    (empiricalRawFirstJetInverseCutoffConstant time +
      2 * ‖empiricalClockTangentVector (criticalLineParameter time)‖)

lemma empiricalRawKappaInverseCutoffConstant_nonneg (time : ℝ) :
    0 ≤ empiricalRawKappaInverseCutoffConstant time := by
  have hfixed := empiricalRawFirstJetInverseCutoffConstant_nonneg time
  exact mul_nonneg hfixed
    (add_nonneg hfixed
      (mul_nonneg (by norm_num)
        (norm_nonneg
          (empiricalClockTangentVector (criticalLineParameter time)))))

/-- The raw finite clock Gram differs from the limiting clock Gram by one fixed
inverse-cutoff constant. -/
theorem abs_finiteEmpiricalTransverseJet_kappa_sub_model_le_inverseCutoff
    (M : ℕ) (hM : 1 ≤ M) (time : ℝ)
    (hzero : genuineContinuation (criticalLineParameter time) = 0) :
    |(finiteEmpiricalTransverseJet M time).kappa -
        empiricalStackKappa (criticalLineParameter time)| ≤
      empiricalRawKappaInverseCutoffConstant time / (M : ℝ) := by
  have hraw :=
    abs_finiteEmpiricalTransverseJet_kappa_sub_model_le M hM time hzero
  let error := empiricalFiniteFirstJetStackErrorBound M time
  let fixed := empiricalRawFirstJetInverseCutoffConstant time
  let tangent := empiricalClockTangentVector (criticalLineParameter time)
  have herror :=
    empiricalFiniteFirstJetStackErrorBound_le_inverseCutoff M hM time
  have hMreal : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hfixedNonneg : 0 ≤ fixed :=
    empiricalRawFirstJetInverseCutoffConstant_nonneg time
  have herrorNonneg : 0 ≤ error := by
    dsimp [error]
    exact Real.sqrt_nonneg _
  have hdivNonneg : 0 ≤ fixed / (M : ℝ) :=
    div_nonneg hfixedNonneg (by positivity)
  have herrorFixed : error ≤ fixed :=
    herror.trans (div_le_self hfixedNonneg hMreal)
  have hsum : error + 2 * ‖tangent‖ ≤ fixed + 2 * ‖tangent‖ :=
    add_le_add herrorFixed le_rfl
  have hproduct :
      error * (error + 2 * ‖tangent‖) ≤
        (fixed / (M : ℝ)) * (fixed + 2 * ‖tangent‖) :=
    mul_le_mul herror hsum (by positivity) hdivNonneg
  calc
    |(finiteEmpiricalTransverseJet M time).kappa -
        empiricalStackKappa (criticalLineParameter time)| ≤
      error * (error + 2 * ‖tangent‖) := by
        simpa [error, tangent, empiricalFiniteRawKappaErrorBound] using hraw
    _ ≤ (fixed / (M : ℝ)) * (fixed + 2 * ‖tangent‖) := hproduct
    _ = empiricalRawKappaInverseCutoffConstant time / (M : ℝ) := by
      unfold empiricalRawKappaInverseCutoffConstant
      dsimp [fixed, tangent]
      ring

/-- Eventually the raw finite clock Gram used by the Hessian is at least half
of its exact positive limiting value. -/
theorem eventually_finiteEmpiricalRawKappa_ge_half
    (time : ℝ)
    (hzero : genuineContinuation (criticalLineParameter time) = 0)
    (hsimple : deriv genuineContinuation (criticalLineParameter time) ≠ 0) :
    ∀ᶠ M : ℕ in atTop,
      empiricalStackKappa (criticalLineParameter time) / 2 ≤
        (finiteEmpiricalTransverseJet M time).kappa := by
  let kappa := empiricalStackKappa (criticalLineParameter time)
  let C := empiricalRawKappaInverseCutoffConstant time
  have hkappa : 0 < kappa := by
    dsimp [kappa]
    exact empiricalStackKappa_pos (by norm_num [criticalLineParameter_re]) hsimple
  have hratio : Tendsto (fun M : ℕ => C / (M : ℝ)) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat C
  have hsmall : ∀ᶠ M : ℕ in atTop, C / (M : ℝ) < kappa / 2 :=
    hratio.eventually (Iio_mem_nhds (by linarith : 0 < kappa / 2))
  filter_upwards [hsmall, eventually_ge_atTop 1] with M hMsmall hM
  have hdiff :=
    abs_finiteEmpiricalTransverseJet_kappa_sub_model_le_inverseCutoff
      M hM time hzero
  have hlower := (abs_le.mp hdiff).1
  dsimp [C, kappa] at hMsmall hlower ⊢
  linarith

/-- Eventually the concrete temporal Schur denominator is separated from zero
by one quarter of the limiting clock Gram. -/
theorem eventually_finiteEmpiricalTemporalDenominator_ge_quarter
    (time : ℝ)
    (hzero : genuineContinuation (criticalLineParameter time) = 0)
    (hsimple : deriv genuineContinuation (criticalLineParameter time) ≠ 0) :
    ∀ᶠ M : ℕ in atTop,
      empiricalStackKappa (criticalLineParameter time) / 4 ≤
        |(finiteEmpiricalTransverseJet M time).kappa -
          (finiteEmpiricalTransverseJet M time).a| := by
  let kappa := empiricalStackKappa (criticalLineParameter time)
  let C := empiricalSecondJetCurvatureInverseCutoffConstant time
  have hkappa : 0 < kappa := by
    dsimp [kappa]
    exact empiricalStackKappa_pos (by norm_num [criticalLineParameter_re]) hsimple
  have hratio : Tendsto (fun M : ℕ => C / (M : ℝ)) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat C
  have hsmall : ∀ᶠ M : ℕ in atTop, C / (M : ℝ) < kappa / 4 :=
    hratio.eventually (Iio_mem_nhds (by linarith : 0 < kappa / 4))
  obtain ⟨threshold, hthreshold⟩ := exists_nat_ge (Real.exp 2)
  filter_upwards [eventually_finiteEmpiricalRawKappa_ge_half
      time hzero hsimple, hsmall, eventually_ge_atTop 1,
      eventually_ge_atTop threshold] with M hkappaM hMsmall hM hMthreshold
  have hMexp : Real.exp 2 ≤ (M : ℝ) :=
    hthreshold.trans (by exact_mod_cast hMthreshold)
  have ha :=
    abs_finiteEmpiricalTransverseJet_a_le_inverseCutoff
      M hMexp time hzero
  have hkappaMNonneg : 0 ≤ (finiteEmpiricalTransverseJet M time).kappa := by
    unfold finiteEmpiricalTransverseJet empiricalQuadraticTransverseJet
    positivity
  have hreverse :=
    abs_sub_abs_le_abs_sub
      (finiteEmpiricalTransverseJet M time).kappa
      (finiteEmpiricalTransverseJet M time).a
  rw [abs_of_nonneg hkappaMNonneg] at hreverse
  dsimp [C, kappa] at hMsmall hkappaM ha ⊢
  linarith

end

end GenuineZeroUniformAtlasEnergy

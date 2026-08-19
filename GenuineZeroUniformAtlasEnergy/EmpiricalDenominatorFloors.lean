import GenuineZeroUniformAtlasEnergy.EmpiricalSecondJetDownstreamClosure

/-!
# Concrete empirical denominator floors

The corrected first jet already differs from the infinite clock tangent by an
explicit camerawise Cauchy bound.  This module absorbs the remaining critical
cutoff scale into a fixed inverse-cutoff constant, aggregates the six cameras,
and turns the resulting convergence into eventual positive floors for

* the finite corrected clock Gram;
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
    exact add_nonneg (norm_nonneg _)
      (div_nonneg (div_nonneg hconstant (by positivity)) hradiusPos.le)
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
  positivity

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
  unfold empiricalCorrectedKappaInverseCutoffConstant
  positivity

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
  have herrorFixed : error ≤ fixed := by
    exact herror.trans (div_le_self hfixedNonneg hMreal)
  have hsum : error + 2 * ‖tangent‖ ≤ fixed + 2 * ‖tangent‖ :=
    add_le_add herrorFixed le_rfl
  have hproduct :
      error * (error + 2 * ‖tangent‖) ≤
        (fixed / (M : ℝ)) * (fixed + 2 * ‖tangent‖) :=
    mul_le_mul herror hsum (by positivity) herrorNonneg
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
  have hlower :
      -C / (M : ℝ) ≤
        empiricalQuadraticClockKappa
            (finiteEmpiricalCameraCorrectedDerivativeStack M
              (criticalLineParameter time)) - kappa :=
    (abs_le.mp hdiff).1
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
  filter_upwards [eventually_finiteEmpiricalCorrectedKappa_ge_half
      time hzero hsimple, hsmall, eventually_ge_atTop 1,
      eventually_ge_atTop 8] with M hkappaM hMsmall hM hMeight
  have hMexp : Real.exp 2 ≤ (M : ℝ) := by
    have hexp : Real.exp 2 < 8 := by
      rw [Real.exp_lt_iff_log]
      norm_num
    exact hexp.le.trans (by exact_mod_cast hMeight)
  have ha :=
    abs_finiteEmpiricalTransverseJet_a_le_inverseCutoff
      M hMexp time hzero
  let kappaM :=
    empiricalQuadraticClockKappa
      (finiteEmpiricalCameraCorrectedDerivativeStack M
        (criticalLineParameter time))
  have hkappaMNonneg : 0 ≤ kappaM := by
    unfold kappaM empiricalQuadraticClockKappa
    positivity
  have hreverse :=
    abs_sub_abs_le_abs_sub kappaM (finiteEmpiricalTransverseJet M time).a
  have hlower :
      kappaM - |(finiteEmpiricalTransverseJet M time).a| ≤
        |kappaM - (finiteEmpiricalTransverseJet M time).a| := by
    have hself :
        kappaM - |(finiteEmpiricalTransverseJet M time).a| ≤
          |kappaM - |(finiteEmpiricalTransverseJet M time).a|| :=
      le_abs_self _
    rw [abs_of_nonneg hkappaMNonneg] at hreverse
    exact hself.trans hreverse
  have hkappaIdentification :
      kappaM = (finiteEmpiricalTransverseJet M time).kappa := by
    rfl
  rw [hkappaIdentification] at hlower
  dsimp [C, kappa] at hMsmall hkappaM ha hlower ⊢
  linarith

end

end GenuineZeroUniformAtlasEnergy

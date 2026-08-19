import GenuineZeroUniformAtlasEnergy.EmpiricalFiniteCorrectedData

/-!
# Corrected finite phase-pairing bound

The finite radial gradient is twice the real part of the pairing between the
phase-normalized residual and the corrected first jet.  Both vectors already
have explicit stack-level error bounds.  Bilinearity of the Hermitian pairing
therefore reduces the gradient channel to two Cauchy--Schwarz estimates.
-/

namespace GenuineZeroUniformAtlasEnergy

open CPFormal.Analytic.Cp

noncomputable section

/-- Generic perturbation bound for a Hermitian pairing. -/
theorem norm_empiricalQuadraticClockPairing_sub_le_of_norm_sub_bounds
    (residual modelResidual firstJet modelFirstJet : EmpiricalCameraStack)
    (residualError firstJetError : ℝ)
    (hresidual : ‖residual - modelResidual‖ ≤ residualError)
    (hfirstJet : ‖firstJet - modelFirstJet‖ ≤ firstJetError) :
    ‖empiricalQuadraticClockPairing residual firstJet -
        empiricalQuadraticClockPairing modelResidual modelFirstJet‖ ≤
      residualError * (firstJetError + ‖modelFirstJet‖) +
        ‖modelResidual‖ * firstJetError := by
  have hfirstNorm :
      ‖firstJet‖ ≤ firstJetError + ‖modelFirstJet‖ := by
    calc
      ‖firstJet‖ = ‖(firstJet - modelFirstJet) + modelFirstJet‖ := by
        rw [sub_add_cancel]
      _ ≤ ‖firstJet - modelFirstJet‖ + ‖modelFirstJet‖ := norm_add_le _ _
      _ ≤ firstJetError + ‖modelFirstJet‖ :=
        add_le_add hfirstJet le_rfl
  have hrewrite :
      empiricalQuadraticClockPairing residual firstJet -
          empiricalQuadraticClockPairing modelResidual modelFirstJet =
        inner ℂ (residual - modelResidual) firstJet +
          inner ℂ modelResidual (firstJet - modelFirstJet) := by
    unfold empiricalQuadraticClockPairing
    rw [inner_sub_left, inner_sub_right]
    ring
  rw [hrewrite]
  calc
    ‖inner ℂ (residual - modelResidual) firstJet +
        inner ℂ modelResidual (firstJet - modelFirstJet)‖ ≤
      ‖inner ℂ (residual - modelResidual) firstJet‖ +
        ‖inner ℂ modelResidual (firstJet - modelFirstJet)‖ := norm_add_le _ _
    _ ≤ ‖residual - modelResidual‖ * ‖firstJet‖ +
        ‖modelResidual‖ * ‖firstJet - modelFirstJet‖ :=
      add_le_add
        (norm_inner_le_norm (residual - modelResidual) firstJet)
        (norm_inner_le_norm modelResidual (firstJet - modelFirstJet))
    _ ≤ residualError * (firstJetError + ‖modelFirstJet‖) +
        ‖modelResidual‖ * firstJetError := by
      exact add_le_add
        (mul_le_mul hresidual hfirstNorm (norm_nonneg _) (by
          exact le_trans (norm_nonneg _) hresidual))
        (mul_le_mul_of_nonneg_left hfirstJet (norm_nonneg _))

/-- Finite corrected phase pairing. -/
def finiteEmpiricalCorrectedPhasePairing
    (M : ℕ) (time : ℝ) : ℂ :=
  empiricalQuadraticClockPairing
    (empiricalPhaseNormalizedFiniteResidualStack M time)
    (finiteEmpiricalCameraCorrectedDerivativeStack M
      (criticalLineParameter time))

/-- Leading phase-rotated pairing. -/
def empiricalLeadingPhasePairing
    (M : ℕ) (time : ℝ) : ℂ :=
  Complex.exp
      ((empiricalCutoffPhase time M : ℂ) * Complex.I) *
    empiricalStackPairing (criticalLineParameter time)

/-- The Hermitian pairing of the phase-normalized leading residual with the
infinite clock tangent is exactly the leading phase pairing. -/
theorem empiricalQuadraticClockPairing_phaseNormalizedLeading_eq
    (M : ℕ) (time : ℝ) :
    empiricalQuadraticClockPairing
        (empiricalPhaseNormalizedLeadingResidualStack M time)
        (empiricalClockTangentVector (criticalLineParameter time)) =
      empiricalLeadingPhasePairing M time := by
  unfold empiricalQuadraticClockPairing
    empiricalPhaseNormalizedLeadingResidualStack
    empiricalCutoffBackPhase empiricalLeadingPhasePairing
    empiricalStackPairing
  have hphase :
      (starRingEnd ℂ)
          (Complex.exp
            (-((empiricalCutoffPhase time M : ℂ) * Complex.I))) =
        Complex.exp
          ((empiricalCutoffPhase time M : ℂ) * Complex.I) := by
    rw [← Complex.exp_conj]
    simp
  rw [inner_smul_left, hphase]

/-- Explicit stack-level pairing error assembled from the residual and
corrected first-jet errors. -/
def empiricalFiniteCorrectedPairingErrorBound
    (M : ℕ) (time : ℝ) : ℝ :=
  empiricalScaledFiniteResidualStackErrorBound M time *
      (empiricalFiniteCorrectedFirstJetStackErrorBound M time +
        ‖empiricalClockTangentVector (criticalLineParameter time)‖) +
    ‖empiricalLeadingCutoffVector (criticalLineParameter time)‖ *
      empiricalFiniteCorrectedFirstJetStackErrorBound M time

/-- Concrete corrected finite pairing estimate. -/
theorem norm_finiteEmpiricalCorrectedPhasePairing_sub_leading_le
    (M : ℕ) (hM : 1 ≤ M) (time : ℝ)
    (hzero : genuineContinuation (criticalLineParameter time) = 0) :
    ‖finiteEmpiricalCorrectedPhasePairing M time -
        empiricalLeadingPhasePairing M time‖ ≤
      empiricalFiniteCorrectedPairingErrorBound M time := by
  rw [← empiricalQuadraticClockPairing_phaseNormalizedLeading_eq M time]
  have hpair :=
    norm_empiricalQuadraticClockPairing_sub_le_of_norm_sub_bounds
      (empiricalPhaseNormalizedFiniteResidualStack M time)
      (empiricalPhaseNormalizedLeadingResidualStack M time)
      (finiteEmpiricalCameraCorrectedDerivativeStack M
        (criticalLineParameter time))
      (empiricalClockTangentVector (criticalLineParameter time))
      (empiricalScaledFiniteResidualStackErrorBound M time)
      (empiricalFiniteCorrectedFirstJetStackErrorBound M time)
      (norm_empiricalPhaseNormalizedFiniteResidualStack_sub_leading_le
        M hM time hzero)
      (norm_finiteEmpiricalCameraCorrectedDerivativeStack_sub_clockTangent_le
        M hM time hzero)
  simpa [finiteEmpiricalCorrectedPhasePairing,
    empiricalFiniteCorrectedPairingErrorBound] using hpair

/-- The finite corrected radial gradient differs from `2 X_M` by twice the
pairing error. -/
theorem abs_finiteEmpiricalCorrectedRadialGradient_sub_model_le
    (M : ℕ) (hM : 1 ≤ M) (time : ℝ)
    (hzero : genuineContinuation (criticalLineParameter time) = 0) :
    |finiteEmpiricalCorrectedRadialGradient M time -
        2 * finiteEmpiricalPhaseProjection time M| ≤
      2 * empiricalFiniteCorrectedPairingErrorBound M time := by
  have hpair :=
    norm_finiteEmpiricalCorrectedPhasePairing_sub_leading_le
      M hM time hzero
  have hre := Complex.abs_re_le_norm
    (finiteEmpiricalCorrectedPhasePairing M time -
      empiricalLeadingPhasePairing M time)
  have hreal :
      |(finiteEmpiricalCorrectedPhasePairing M time -
          empiricalLeadingPhasePairing M time).re| ≤
        empiricalFiniteCorrectedPairingErrorBound M time :=
    le_trans hre hpair
  have hleadingRe :
      (empiricalLeadingPhasePairing M time).re =
        finiteEmpiricalPhaseProjection time M := by
    rfl
  have hrewrite :
      finiteEmpiricalCorrectedRadialGradient M time -
          2 * finiteEmpiricalPhaseProjection time M =
        2 * (finiteEmpiricalCorrectedPhasePairing M time -
          empiricalLeadingPhasePairing M time).re := by
    change
      2 * (finiteEmpiricalCorrectedPhasePairing M time).re -
          2 * finiteEmpiricalPhaseProjection time M =
        2 * (finiteEmpiricalCorrectedPhasePairing M time -
          empiricalLeadingPhasePairing M time).re
    rw [← hleadingRe]
    simp
    ring
  rw [hrewrite]
  calc
    |2 * (finiteEmpiricalCorrectedPhasePairing M time -
        empiricalLeadingPhasePairing M time).re| =
      2 * |(finiteEmpiricalCorrectedPhasePairing M time -
        empiricalLeadingPhasePairing M time).re| := by
        rw [abs_mul]
        norm_num
    _ ≤ 2 * empiricalFiniteCorrectedPairingErrorBound M time :=
      mul_le_mul_of_nonneg_left hreal (by norm_num)

end

end GenuineZeroUniformAtlasEnergy

import GenuineZeroUniformAtlasEnergy.EmpiricalFiniteFirstJetBound

/-!
# Concrete scaled finite-residual bound

The camerawise scaled-tail theorem already controls

```math
M^(s+1) chi_{b,M}(s) - A_b(s)
```

by an explicit `C_b(t) / M` bound at a Genuine critical zero.  This module
assembles those six coordinates in the empirical Euclidean stack and then
transports the estimate through the unit logarithmic cutoff phase used by the
physical `M^(3/2)` normalization.
-/

open scoped BigOperators

namespace GenuineZeroUniformAtlasEnergy

open CPFormal.Analytic.Cp

noncomputable section

/-- Euclidean aggregation of the six explicit scaled-residual bounds. -/
def empiricalScaledFiniteResidualStackErrorBound
    (M : ℕ) (time : ℝ) : ℝ :=
  Real.sqrt
    (∑ camera : EmpiricalCamera,
      (empiricalScaledCameraTailCauchyConstant camera time / (M : ℝ)) ^ 2)

/-- At a Genuine critical zero, the naturally scaled finite residual stack is
within the displayed Euclidean `C/M` bound of the leading cutoff vector. -/
theorem norm_empiricalScaledFiniteResidualStack_sub_leading_critical_le
    (M : ℕ) (hM : 1 ≤ M) (time : ℝ)
    (hzero : genuineContinuation (criticalLineParameter time) = 0) :
    ‖empiricalScaledFiniteResidualStack M (criticalLineParameter time) -
        empiricalLeadingCutoffVector (criticalLineParameter time)‖ ≤
      empiricalScaledFiniteResidualStackErrorBound M time := by
  rw [EuclideanSpace.norm_eq]
  unfold empiricalScaledFiniteResidualStackErrorBound
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro camera _hcamera
  have hcomponent :=
    empiricalSixCamera_scaledFiniteResidual_value_bound_of_genuine_zero
      M hM time hzero camera
  have hboundNonneg :
      0 ≤ empiricalScaledCameraTailCauchyConstant camera time / (M : ℝ) :=
    le_trans (norm_nonneg _) hcomponent
  have hmul :=
    mul_le_mul hcomponent hcomponent
      (norm_nonneg
        (empiricalScaledFiniteCameraResidual camera M
          (criticalLineParameter time) -
        empiricalLeadingCutoffVector (criticalLineParameter time) camera))
      hboundNonneg
  simpa [pow_two] using hmul

/-- The cutoff back-phase is a unit complex scalar. -/
@[simp] theorem norm_empiricalCutoffBackPhase
    (time : ℝ) (M : ℕ) :
    ‖empiricalCutoffBackPhase time M‖ = 1 := by
  unfold empiricalCutoffBackPhase
  have harg :
      -((empiricalCutoffPhase time M : ℂ) * Complex.I) =
        ((-empiricalCutoffPhase time M : ℝ) : ℂ) * Complex.I := by
    simp
  rw [harg]
  exact Complex.norm_exp_ofReal_mul_I (-empiricalCutoffPhase time M)

/-- Phase-rotated leading residual used by the finite clock model. -/
def empiricalPhaseNormalizedLeadingResidualStack
    (M : ℕ) (time : ℝ) : EmpiricalCameraStack :=
  empiricalCutoffBackPhase time M •
    empiricalLeadingCutoffVector (criticalLineParameter time)

/-- Removing the logarithmic cutoff phase preserves the scaled-residual error
bound exactly. -/
theorem norm_empiricalPhaseNormalizedFiniteResidualStack_sub_leading_le
    (M : ℕ) (hM : 1 ≤ M) (time : ℝ)
    (hzero : genuineContinuation (criticalLineParameter time) = 0) :
    ‖empiricalPhaseNormalizedFiniteResidualStack M time -
        empiricalPhaseNormalizedLeadingResidualStack M time‖ ≤
      empiricalScaledFiniteResidualStackErrorBound M time := by
  unfold empiricalPhaseNormalizedFiniteResidualStack
    empiricalPhaseNormalizedLeadingResidualStack
  rw [← smul_sub, norm_smul, norm_empiricalCutoffBackPhase, one_mul]
  exact
    norm_empiricalScaledFiniteResidualStack_sub_leading_critical_le
      M hM time hzero

/-- The phase-rotated leading residual has the same norm as the fixed leading
cutoff vector. -/
@[simp] theorem norm_empiricalPhaseNormalizedLeadingResidualStack
    (M : ℕ) (time : ℝ) :
    ‖empiricalPhaseNormalizedLeadingResidualStack M time‖ =
      ‖empiricalLeadingCutoffVector (criticalLineParameter time)‖ := by
  unfold empiricalPhaseNormalizedLeadingResidualStack
  rw [norm_smul, norm_empiricalCutoffBackPhase, one_mul]

end

end GenuineZeroUniformAtlasEnergy

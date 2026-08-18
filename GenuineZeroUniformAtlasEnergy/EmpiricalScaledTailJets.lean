import GenuineZeroUniformAtlasEnergy.EmpiricalStackDifferential
import GenuineZeroUniformAtlasEnergy.NativeCutoffExactScaledTailCauchy

/-!
# Scaled cutoff-tail jets for the empirical six-camera stack

The explicit-radius Cauchy bounds already control the value, first derivative,
and second derivative of the naturally scaled cutoff-tail error.  This module
specializes those bounds to the faithful empirical cameras `C2` through `C7`.

At a Genuine zero the finite empirical characteristic is exactly the negative
unresolved tail.  Consequently its naturally scaled residual differs from the
existing leading cutoff vector by the negative scaled-tail error.  The value
channel is therefore controlled componentwise by an explicit `C_camera(t)/M`
bound.

The derivative bounds recorded here concern the scaled tail as a holomorphic
function of the spectral parameter.  Converting them into bounds for the
finite reoptimized gradient and local curvature remains a separate algebraic
step; no such identification is inserted into the definitions below.
-/

namespace GenuineZeroUniformAtlasEnergy

open CPFormal.Analytic.Cp

noncomputable section

/-- Naturally scaled empirical tail after subtracting its leading coefficient. -/
def empiricalScaledCameraTailError
    (camera : EmpiricalCamera) (M : ℕ) (s : ℂ) : ℂ :=
  (M : ℂ) ^ (s + 1) * empiricalCameraCutoffTail camera M s -
    empiricalNativeTailCoefficient camera s

/-- Camera-specialized Cauchy constant for the scaled tail jets. -/
def empiricalScaledCameraTailCauchyConstant
    (camera : EmpiricalCamera) (time : ℝ) : ℝ :=
  nativeExplicitRadiusScaledTailCriticalCauchyConstant
    (camera.label / 2) time

/-- Every empirical retained radius satisfies the margin required by the
explicit-radius cutoff estimates. -/
lemma empiricalCamera_retainedRadius_le_period_sub_one
    (camera : EmpiricalCamera) :
    camera.label / 2 ≤ camera.period - 1 := by
  cases camera <;> norm_num

/-- Pointwise identification with the generic explicit-radius scaled error. -/
theorem empiricalScaledCameraTailError_eq_nativeExplicitRadiusScaledTailError
    (camera : EmpiricalCamera) (M : ℕ) (s : ℂ) :
    empiricalScaledCameraTailError camera M s =
      nativeExplicitRadiusScaledTailError
        camera.period (camera.label / 2) M s := by
  unfold empiricalScaledCameraTailError empiricalNativeTailCoefficient
    nativeExplicitRadiusScaledTailError nativeExplicitRadiusScaledCutoffTail
  rw [empiricalCameraCutoffTail_eq_nativeExplicitRadiusCutoffTail]

/-- Function-level form used to transport complex derivatives. -/
theorem empiricalScaledCameraTailError_fun_eq_native
    (camera : EmpiricalCamera) (M : ℕ) :
    empiricalScaledCameraTailError camera M =
      nativeExplicitRadiusScaledTailError
        camera.period (camera.label / 2) M := by
  funext s
  exact
    empiricalScaledCameraTailError_eq_nativeExplicitRadiusScaledTailError
      camera M s

lemma empiricalScaledCameraTailCauchyConstant_nonneg
    (camera : EmpiricalCamera) (time : ℝ) :
    0 ≤ empiricalScaledCameraTailCauchyConstant camera time := by
  exact nativeExplicitRadiusScaledTailCriticalCauchyConstant_nonneg
    (camera.label / 2) time

/-- Zeroth scaled-tail bound for one empirical camera. -/
theorem norm_empiricalScaledCameraTailError_critical_value_le
    (camera : EmpiricalCamera) (M : ℕ) (hM : 1 ≤ M) (time : ℝ) :
    ‖empiricalScaledCameraTailError camera M
        (criticalLineParameter time)‖ ≤
      empiricalScaledCameraTailCauchyConstant camera time / (M : ℝ) := by
  rw [empiricalScaledCameraTailError_eq_nativeExplicitRadiusScaledTailError]
  exact norm_nativeExplicitRadiusScaledTailError_critical_value_le
    camera.period (camera.label / 2) M
    (by omega)
    (empiricalCamera_retainedRadius_le_period_sub_one camera)
    hM time

/-- First complex derivative bound for one empirical scaled tail. -/
theorem norm_iteratedDeriv_one_empiricalScaledCameraTailError_critical_le
    (camera : EmpiricalCamera) (M : ℕ) (hM : 1 ≤ M) (time : ℝ) :
    ‖iteratedDeriv 1 (empiricalScaledCameraTailError camera M)
        (criticalLineParameter time)‖ ≤
      (empiricalScaledCameraTailCauchyConstant camera time / (M : ℝ)) /
        nativeExplicitRadiusCriticalCauchyRadius := by
  rw [empiricalScaledCameraTailError_fun_eq_native]
  exact norm_nativeExplicitRadiusScaledTailError_critical_first_le
    camera.period (camera.label / 2) M
    (by omega)
    (empiricalCamera_retainedRadius_le_period_sub_one camera)
    hM time

/-- Second complex derivative bound for one empirical scaled tail. -/
theorem norm_iteratedDeriv_two_empiricalScaledCameraTailError_critical_le
    (camera : EmpiricalCamera) (M : ℕ) (hM : 1 ≤ M) (time : ℝ) :
    ‖iteratedDeriv 2 (empiricalScaledCameraTailError camera M)
        (criticalLineParameter time)‖ ≤
      2 * (empiricalScaledCameraTailCauchyConstant camera time / (M : ℝ)) /
        nativeExplicitRadiusCriticalCauchyRadius ^ 2 := by
  rw [empiricalScaledCameraTailError_fun_eq_native]
  exact norm_nativeExplicitRadiusScaledTailError_critical_second_le
    camera.period (camera.label / 2) M
    (by omega)
    (empiricalCamera_retainedRadius_le_period_sub_one camera)
    hM time

/-- The three empirical scaled-tail jet bounds in one package. -/
theorem empiricalScaledCameraTailError_critical_three_bounds
    (camera : EmpiricalCamera) (M : ℕ) (hM : 1 ≤ M) (time : ℝ) :
    ‖empiricalScaledCameraTailError camera M
        (criticalLineParameter time)‖ ≤
        empiricalScaledCameraTailCauchyConstant camera time / (M : ℝ) ∧
      ‖iteratedDeriv 1 (empiricalScaledCameraTailError camera M)
          (criticalLineParameter time)‖ ≤
        (empiricalScaledCameraTailCauchyConstant camera time / (M : ℝ)) /
          nativeExplicitRadiusCriticalCauchyRadius ∧
      ‖iteratedDeriv 2 (empiricalScaledCameraTailError camera M)
          (criticalLineParameter time)‖ ≤
        2 * (empiricalScaledCameraTailCauchyConstant camera time / (M : ℝ)) /
          nativeExplicitRadiusCriticalCauchyRadius ^ 2 := by
  exact ⟨
    norm_empiricalScaledCameraTailError_critical_value_le
      camera M hM time,
    norm_iteratedDeriv_one_empiricalScaledCameraTailError_critical_le
      camera M hM time,
    norm_iteratedDeriv_two_empiricalScaledCameraTailError_critical_le
      camera M hM time⟩

/-- Naturally scaled finite empirical residual. -/
def empiricalScaledFiniteCameraResidual
    (camera : EmpiricalCamera) (M : ℕ) (s : ℂ) : ℂ :=
  (M : ℂ) ^ (s + 1) *
    finiteEmpiricalCameraCharacteristic camera M s

/-- At a zero of one infinite camera, the scaled finite residue differs from
the existing leading cutoff vector by exactly the negative scaled-tail error. -/
theorem empiricalScaledFiniteCameraResidual_sub_leading_eq_neg_tailError
    (camera : EmpiricalCamera) (M : ℕ) {s : ℂ}
    (hs : -1 < s.re)
    (hzero : empiricalCameraCharacteristic camera s = 0) :
    empiricalScaledFiniteCameraResidual camera M s -
        empiricalLeadingCutoffVector s camera =
      -empiricalScaledCameraTailError camera M s := by
  rw [finiteEmpiricalCameraCharacteristic_eq_neg_cutoffTail_of_zero
    camera M hs hzero]
  rw [empiricalLeadingCutoffVector_apply_eq_neg_tailCoefficient]
  unfold empiricalScaledFiniteCameraResidual empiricalScaledCameraTailError
  ring

/-- Explicit value-channel approximation of the scaled finite residual at a
critical common zero. -/
theorem norm_empiricalScaledFiniteCameraResidual_sub_leading_critical_le
    (camera : EmpiricalCamera) (M : ℕ) (hM : 1 ≤ M) (time : ℝ)
    (hzero : empiricalCameraCharacteristic camera
      (criticalLineParameter time) = 0) :
    ‖empiricalScaledFiniteCameraResidual camera M
          (criticalLineParameter time) -
        empiricalLeadingCutoffVector (criticalLineParameter time) camera‖ ≤
      empiricalScaledCameraTailCauchyConstant camera time / (M : ℝ) := by
  have hstrip : -1 < (criticalLineParameter time).re := by
    norm_num [criticalLineParameter_re]
  rw [empiricalScaledFiniteCameraResidual_sub_leading_eq_neg_tailError
    camera M hstrip hzero, norm_neg]
  exact norm_empiricalScaledCameraTailError_critical_value_le
    camera M hM time

/-- A Genuine zero supplies the common-zero premise and therefore the explicit
scaled finite-residual value bound in all six empirical cameras. -/
theorem empiricalSixCamera_scaledFiniteResidual_value_bound_of_genuine_zero
    (M : ℕ) (hM : 1 ≤ M) (time : ℝ)
    (hzero : genuineContinuation (criticalLineParameter time) = 0) :
    ∀ camera : EmpiricalCamera,
      ‖empiricalScaledFiniteCameraResidual camera M
            (criticalLineParameter time) -
          empiricalLeadingCutoffVector
            (criticalLineParameter time) camera‖ ≤
        empiricalScaledCameraTailCauchyConstant camera time / (M : ℝ) := by
  intro camera
  exact norm_empiricalScaledFiniteCameraResidual_sub_leading_critical_le
    camera M hM time
    (empiricalCameraCharacteristic_zero_of_genuineContinuation_zero
      camera (criticalLineParameter_mem_genuineCriticalStrip time) hzero)

end

end GenuineZeroUniformAtlasEnergy

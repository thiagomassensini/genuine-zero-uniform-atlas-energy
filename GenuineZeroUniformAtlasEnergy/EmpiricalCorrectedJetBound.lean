import GenuineZeroUniformAtlasEnergy.EmpiricalFiniteJetCrosswalk

/-!
# Explicit bound for the phase-corrected finite empirical derivative

The first finite-jet crosswalk identifies

```math
\chi'_{b,M}(s)+\log(M)\chi_{b,M}(s)
```

with the infinite clock tangent minus the corresponding logarithmically
corrected cutoff-tail jet.  The scaled-tail Cauchy bound now controls that
remaining tail term explicitly.

Writing

```math
B_{b,M}(s)=A_b(s)+R_{b,M}(s)=M^{s+1}T_{b,M}(s),
```

we have

```math
T'_{b,M}(s)+\log(M)T_{b,M}(s)
  =M^{-s-1}B'_{b,M}(s).
```

Thus the phase-corrected finite derivative approaches the concrete infinite
clock tangent with an explicit camerawise error.  No moving-minimizer or
finite-Hessian identification is claimed in this module.
-/

open scoped Topology

namespace GenuineZeroUniformAtlasEnergy

open CPFormal.Analytic.Cp
open Metric

noncomputable section

/-- Full scaled cutoff-tail amplitude: leading coefficient plus exact scaled
error. -/
def empiricalScaledCameraTailAmplitude
    (camera : EmpiricalCamera) (M : ℕ) (s : ℂ) : ℂ :=
  empiricalNativeTailCoefficient camera s +
    empiricalScaledCameraTailError camera M s

/-- First complex derivative of the full scaled amplitude. -/
def empiricalScaledCameraTailAmplitudeFirst
    (camera : EmpiricalCamera) (M : ℕ) (s : ℂ) : ℂ :=
  deriv (empiricalNativeTailCoefficient camera) s +
    deriv (empiricalScaledCameraTailError camera M) s

/-- The empirical tail-model coefficient is entire. -/
theorem differentiable_empiricalNativeTailCoefficient
    (camera : EmpiricalCamera) :
    Differentiable ℂ (empiricalNativeTailCoefficient camera) := by
  unfold empiricalNativeTailCoefficient
  exact differentiable_nativeExplicitRadiusTailCoefficient
    camera.period (camera.label / 2)
    (Nat.succ_le_iff.mpr (empiricalCamera_period_pos camera))

/-- The exact empirical scaled-tail error is differentiable at every critical
point for a positive cutoff. -/
theorem differentiableAt_empiricalScaledCameraTailError_critical
    (camera : EmpiricalCamera) (M : ℕ) (hM : 1 ≤ M) (time : ℝ) :
    DifferentiableAt ℂ (empiricalScaledCameraTailError camera M)
      (criticalLineParameter time) := by
  rw [empiricalScaledCameraTailError_fun_eq_native]
  have hmem :
      criticalLineParameter time ∈
        ball (criticalLineParameter time)
          nativeExplicitRadiusCriticalOuterRadius :=
    mem_ball_self (by
      unfold nativeExplicitRadiusCriticalOuterRadius
      norm_num)
  exact
    (differentiableOn_nativeExplicitRadiusScaledTailError_criticalOuterBall
      camera.period (camera.label / 2) M
      (Nat.succ_le_iff.mpr (empiricalCamera_period_pos camera))
      (empiricalCamera_retainedRadius_le_period_sub_one camera)
      hM time).differentiableAt (isOpen_ball.mem_nhds hmem)

/-- Derivative of the full scaled empirical amplitude at a critical point. -/
theorem hasDerivAt_empiricalScaledCameraTailAmplitude_critical
    (camera : EmpiricalCamera) (M : ℕ) (hM : 1 ≤ M) (time : ℝ) :
    HasDerivAt (empiricalScaledCameraTailAmplitude camera M)
      (empiricalScaledCameraTailAmplitudeFirst camera M
        (criticalLineParameter time))
      (criticalLineParameter time) := by
  unfold empiricalScaledCameraTailAmplitude
    empiricalScaledCameraTailAmplitudeFirst
  exact
    ((differentiable_empiricalNativeTailCoefficient camera)
      (criticalLineParameter time)).hasDerivAt.add
        (differentiableAt_empiricalScaledCameraTailError_critical
          camera M hM time).hasDerivAt

/-- Exact reconstruction of the unresolved empirical tail from its full scaled
amplitude. -/
theorem empiricalCameraCutoffTail_eq_nativeCutoffModel_scaledAmplitude
    (camera : EmpiricalCamera) (M : ℕ) (hM : 0 < M) :
    empiricalCameraCutoffTail camera M =
      nativeCutoffModel M (empiricalScaledCameraTailAmplitude camera M) := by
  funext s
  have hMC : (M : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hM)
  have hcancel :
      (M : ℂ) ^ (-s - 1) * (M : ℂ) ^ (s + 1) = 1 := by
    rw [← Complex.cpow_add _ _ hMC]
    have hexponent : -s - 1 + (s + 1) = 0 := by ring
    rw [hexponent, Complex.cpow_zero]
  unfold nativeCutoffModel nativeCutoffScale
    empiricalScaledCameraTailAmplitude empiricalScaledCameraTailError
  calc
    empiricalCameraCutoffTail camera M s =
        ((M : ℂ) ^ (-s - 1) * (M : ℂ) ^ (s + 1)) *
          empiricalCameraCutoffTail camera M s := by
      rw [hcancel, one_mul]
    _ = (M : ℂ) ^ (-s - 1) *
        (empiricalNativeTailCoefficient camera s +
          ((M : ℂ) ^ (s + 1) *
              empiricalCameraCutoffTail camera M s -
            empiricalNativeTailCoefficient camera s)) := by
      ring

/-- Exact corrected derivative of the unresolved empirical tail.  The
`log(M)` term cancels the derivative of the cutoff phase and leaves the
unscaled first derivative of the full scaled amplitude. -/
theorem empiricalCameraCutoffTail_logCorrectedDerivative_eq_scaledAmplitudeFirst
    (camera : EmpiricalCamera) (M : ℕ) (hM : 1 ≤ M) (time : ℝ) :
    deriv (empiricalCameraCutoffTail camera M)
          (criticalLineParameter time) +
        nativeCutoffLog M *
          empiricalCameraCutoffTail camera M
            (criticalLineParameter time) =
      nativeCutoffScale M (criticalLineParameter time) *
        empiricalScaledCameraTailAmplitudeFirst camera M
          (criticalLineParameter time) := by
  have hfun :=
    empiricalCameraCutoffTail_eq_nativeCutoffModel_scaledAmplitude
      camera M (by omega)
  have hjet :=
    hasDerivAt_nativeCutoffModel M (by omega)
      (hasDerivAt_empiricalScaledCameraTailAmplitude_critical
        camera M hM time)
  rw [hfun, hjet.deriv]
  unfold nativeCutoffModelFirstJet nativeCutoffModel
  ring

/-- Explicit camerawise bound for the corrected unresolved-tail derivative. -/
theorem norm_empiricalCameraCutoffTail_logCorrectedDerivative_critical_le
    (camera : EmpiricalCamera) (M : ℕ) (hM : 1 ≤ M) (time : ℝ) :
    ‖deriv (empiricalCameraCutoffTail camera M)
          (criticalLineParameter time) +
        nativeCutoffLog M *
          empiricalCameraCutoffTail camera M
            (criticalLineParameter time)‖ ≤
      ‖nativeCutoffScale M (criticalLineParameter time)‖ *
        (‖deriv (empiricalNativeTailCoefficient camera)
            (criticalLineParameter time)‖ +
          (empiricalScaledCameraTailCauchyConstant camera time / (M : ℝ)) /
            nativeExplicitRadiusCriticalCauchyRadius) := by
  rw [empiricalCameraCutoffTail_logCorrectedDerivative_eq_scaledAmplitudeFirst
    camera M hM time, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  unfold empiricalScaledCameraTailAmplitudeFirst
  have herror :
      ‖deriv (empiricalScaledCameraTailError camera M)
          (criticalLineParameter time)‖ ≤
        (empiricalScaledCameraTailCauchyConstant camera time / (M : ℝ)) /
          nativeExplicitRadiusCriticalCauchyRadius := by
    change
      ‖iteratedDeriv 1 (empiricalScaledCameraTailError camera M)
          (criticalLineParameter time)‖ ≤
        (empiricalScaledCameraTailCauchyConstant camera time / (M : ℝ)) /
          nativeExplicitRadiusCriticalCauchyRadius
    exact
      norm_iteratedDeriv_one_empiricalScaledCameraTailError_critical_le
        camera M hM time
  calc
    ‖deriv (empiricalNativeTailCoefficient camera)
          (criticalLineParameter time) +
        deriv (empiricalScaledCameraTailError camera M)
          (criticalLineParameter time)‖ ≤
      ‖deriv (empiricalNativeTailCoefficient camera)
          (criticalLineParameter time)‖ +
        ‖deriv (empiricalScaledCameraTailError camera M)
          (criticalLineParameter time)‖ := norm_add_le _ _
    _ ≤ ‖deriv (empiricalNativeTailCoefficient camera)
          (criticalLineParameter time)‖ +
        (empiricalScaledCameraTailCauchyConstant camera time / (M : ℝ)) /
          nativeExplicitRadiusCriticalCauchyRadius :=
      add_le_add_left herror _

/-- Main first-jet estimate: at a Genuine zero, the phase-corrected finite
camera derivative differs from the concrete infinite clock tangent by the
explicit corrected-tail bound above. -/
theorem norm_finiteEmpiricalCamera_logCorrectedDerivative_sub_clockTangent_critical_le
    (camera : EmpiricalCamera) (M : ℕ) (hM : 1 ≤ M) (time : ℝ)
    (hzero : genuineContinuation (criticalLineParameter time) = 0) :
    ‖(deriv (finiteEmpiricalCameraCharacteristic camera M)
          (criticalLineParameter time) +
        nativeCutoffLog M *
          finiteEmpiricalCameraCharacteristic camera M
            (criticalLineParameter time)) -
      empiricalClockTangentVector (criticalLineParameter time) camera‖ ≤
      ‖nativeCutoffScale M (criticalLineParameter time)‖ *
        (‖deriv (empiricalNativeTailCoefficient camera)
            (criticalLineParameter time)‖ +
          (empiricalScaledCameraTailCauchyConstant camera time / (M : ℝ)) /
            nativeExplicitRadiusCriticalCauchyRadius) := by
  rw [finiteEmpiricalCamera_logCorrectedDerivative_eq_clockTangent_sub_tailLogJet
    camera M time hzero]
  have hrewrite :
      (empiricalClockTangentVector (criticalLineParameter time) camera -
          (deriv (empiricalCameraCutoffTail camera M)
              (criticalLineParameter time) +
            nativeCutoffLog M *
              empiricalCameraCutoffTail camera M
                (criticalLineParameter time))) -
        empiricalClockTangentVector (criticalLineParameter time) camera =
      -(deriv (empiricalCameraCutoffTail camera M)
          (criticalLineParameter time) +
        nativeCutoffLog M *
          empiricalCameraCutoffTail camera M
            (criticalLineParameter time)) := by
    ring
  rw [hrewrite, norm_neg]
  exact norm_empiricalCameraCutoffTail_logCorrectedDerivative_critical_le
    camera M hM time

end

end GenuineZeroUniformAtlasEnergy

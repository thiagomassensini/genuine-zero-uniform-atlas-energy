import GenuineZeroUniformAtlasEnergy.EmpiricalFiniteTransverseData

/-!
# Concrete finite first-jet error bound

The phase-corrected first-jet theorem controls

```math
(chi'_M + log(M) chi_M) - W.
```

The actual finite transverse data uses the raw derivative `chi'_M`.  This file
removes the logarithmic correction explicitly.  At a Genuine zero,

```math
chi'_M - W
  = ((chi'_M + log(M) chi_M) - W) - log(M) chi_M,
```

so the existing corrected-jet estimate and the existing critical residual
bound give a completely explicit camerawise bound.  The six component bounds
are then assembled into the Euclidean stack norm.
-/

open scoped BigOperators

namespace GenuineZeroUniformAtlasEnergy

open CPFormal.Analytic.Cp

noncomputable section

/-- Explicit raw first-jet error bound for one empirical camera. -/
def empiricalFiniteCameraFirstJetErrorBound
    (camera : EmpiricalCamera) (M : ℕ) (time : ℝ) : ℝ :=
  ‖nativeCutoffScale M (criticalLineParameter time)‖ *
      (‖deriv (empiricalNativeTailCoefficient camera)
          (criticalLineParameter time)‖ +
        (empiricalScaledCameraTailCauchyConstant camera time / (M : ℝ)) /
          nativeExplicitRadiusCriticalCauchyRadius) +
    ‖nativeCutoffLog M‖ * empiricalCameraCriticalTailBound camera M time

/-- At a Genuine critical zero, the raw finite camera derivative differs from
the concrete infinite clock tangent by the displayed corrected-tail plus
logarithmic-residual bound. -/
theorem norm_finiteEmpiricalCameraDerivative_sub_clockTangent_critical_le
    (camera : EmpiricalCamera) (M : ℕ) (hM : 1 ≤ M) (time : ℝ)
    (hzero : genuineContinuation (criticalLineParameter time) = 0) :
    ‖deriv (finiteEmpiricalCameraCharacteristic camera M)
          (criticalLineParameter time) -
        empiricalClockTangentVector (criticalLineParameter time) camera‖ ≤
      empiricalFiniteCameraFirstJetErrorBound camera M time := by
  have hcorrected :=
    norm_finiteEmpiricalCamera_logCorrectedDerivative_sub_clockTangent_critical_le
      camera M hM time hzero
  have hcameraZero :
      empiricalCameraCharacteristic camera (criticalLineParameter time) = 0 :=
    empiricalCameraCharacteristic_zero_of_genuineContinuation_zero
      camera (criticalLineParameter_mem_genuineCriticalStrip time) hzero
  have hvalue :
      ‖finiteEmpiricalCameraCharacteristic camera M
          (criticalLineParameter time)‖ ≤
        empiricalCameraCriticalTailBound camera M time :=
    (finiteEmpiricalCamera_critical_cutoffTail_and_rate
      camera M hM time hcameraZero).2.1
  have hlogValue :
      ‖nativeCutoffLog M *
          finiteEmpiricalCameraCharacteristic camera M
            (criticalLineParameter time)‖ ≤
        ‖nativeCutoffLog M‖ *
          empiricalCameraCriticalTailBound camera M time := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hvalue (norm_nonneg _)
  have hrewrite :
      deriv (finiteEmpiricalCameraCharacteristic camera M)
          (criticalLineParameter time) -
        empiricalClockTangentVector (criticalLineParameter time) camera =
      ((deriv (finiteEmpiricalCameraCharacteristic camera M)
            (criticalLineParameter time) +
          nativeCutoffLog M *
            finiteEmpiricalCameraCharacteristic camera M
              (criticalLineParameter time)) -
        empiricalClockTangentVector (criticalLineParameter time) camera) -
      nativeCutoffLog M *
        finiteEmpiricalCameraCharacteristic camera M
          (criticalLineParameter time) := by
    ring
  rw [hrewrite]
  calc
    ‖((deriv (finiteEmpiricalCameraCharacteristic camera M)
            (criticalLineParameter time) +
          nativeCutoffLog M *
            finiteEmpiricalCameraCharacteristic camera M
              (criticalLineParameter time)) -
        empiricalClockTangentVector (criticalLineParameter time) camera) -
      nativeCutoffLog M *
        finiteEmpiricalCameraCharacteristic camera M
          (criticalLineParameter time)‖ ≤
      ‖(deriv (finiteEmpiricalCameraCharacteristic camera M)
            (criticalLineParameter time) +
          nativeCutoffLog M *
            finiteEmpiricalCameraCharacteristic camera M
              (criticalLineParameter time)) -
        empiricalClockTangentVector (criticalLineParameter time) camera‖ +
      ‖nativeCutoffLog M *
        finiteEmpiricalCameraCharacteristic camera M
          (criticalLineParameter time)‖ := norm_sub_le _ _
    _ ≤ ‖nativeCutoffScale M (criticalLineParameter time)‖ *
        (‖deriv (empiricalNativeTailCoefficient camera)
            (criticalLineParameter time)‖ +
          (empiricalScaledCameraTailCauchyConstant camera time / (M : ℝ)) /
            nativeExplicitRadiusCriticalCauchyRadius) +
        ‖nativeCutoffLog M‖ *
          empiricalCameraCriticalTailBound camera M time :=
      add_le_add hcorrected hlogValue
    _ = empiricalFiniteCameraFirstJetErrorBound camera M time := rfl

/-- Euclidean aggregation of the six explicit camerawise first-jet bounds. -/
def empiricalFiniteFirstJetStackErrorBound
    (M : ℕ) (time : ℝ) : ℝ :=
  Real.sqrt
    (∑ camera : EmpiricalCamera,
      empiricalFiniteCameraFirstJetErrorBound camera M time ^ 2)

/-- The raw finite derivative stack differs from the infinite clock tangent by
the Euclidean aggregation of the six explicit component bounds. -/
theorem norm_finiteEmpiricalCameraDerivativeStack_sub_clockTangent_critical_le
    (M : ℕ) (hM : 1 ≤ M) (time : ℝ)
    (hzero : genuineContinuation (criticalLineParameter time) = 0) :
    ‖finiteEmpiricalCameraDerivativeStack M (criticalLineParameter time) -
        empiricalClockTangentVector (criticalLineParameter time)‖ ≤
      empiricalFiniteFirstJetStackErrorBound M time := by
  rw [EuclideanSpace.norm_eq]
  unfold empiricalFiniteFirstJetStackErrorBound
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro camera _hcamera
  have hcomponent :=
    norm_finiteEmpiricalCameraDerivative_sub_clockTangent_critical_le
      camera M hM time hzero
  have hboundNonneg :
      0 ≤ empiricalFiniteCameraFirstJetErrorBound camera M time :=
    le_trans (norm_nonneg _) hcomponent
  have hmul :=
    mul_le_mul hcomponent hcomponent
      (norm_nonneg
        (deriv (finiteEmpiricalCameraCharacteristic camera M)
          (criticalLineParameter time) -
        empiricalClockTangentVector (criticalLineParameter time) camera))
      hboundNonneg
  simpa [pow_two] using hmul

end

end GenuineZeroUniformAtlasEnergy

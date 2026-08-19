import GenuineZeroUniformAtlasEnergy.EmpiricalFiniteResidualBound

/-!
# Corrected finite empirical first-jet data

The transverse phase model is expressed in the coordinates that remove the
logarithmic cutoff phase.  Its finite first jet is therefore

```math
chi'_{b,M}(s) + log(M) chi_{b,M}(s),
```

not the raw derivative alone.  The existing camerawise theorem already shows
that this corrected jet approaches the infinite clock tangent.  This module
packages the six coordinates, aggregates the explicit error bounds, and uses
the corrected stack in the finite reoptimized energy and radial gradient.
-/

open scoped BigOperators

namespace GenuineZeroUniformAtlasEnergy

open CPFormal.Analytic.Cp

noncomputable section

/-- Logarithmically corrected finite derivative stack. -/
def finiteEmpiricalCameraCorrectedDerivativeStack
    (M : ℕ) (s : ℂ) : EmpiricalCameraStack :=
  WithLp.toLp 2 fun camera =>
    deriv (finiteEmpiricalCameraCharacteristic camera M) s +
      nativeCutoffLog M * finiteEmpiricalCameraCharacteristic camera M s

@[simp] theorem finiteEmpiricalCameraCorrectedDerivativeStack_apply
    (M : ℕ) (s : ℂ) (camera : EmpiricalCamera) :
    finiteEmpiricalCameraCorrectedDerivativeStack M s camera =
      deriv (finiteEmpiricalCameraCharacteristic camera M) s +
        nativeCutoffLog M * finiteEmpiricalCameraCharacteristic camera M s := by
  rfl

/-- Explicit camerawise corrected first-jet error. -/
def empiricalFiniteCorrectedCameraFirstJetErrorBound
    (camera : EmpiricalCamera) (M : ℕ) (time : ℝ) : ℝ :=
  ‖nativeCutoffScale M (criticalLineParameter time)‖ *
    (‖deriv (empiricalNativeTailCoefficient camera)
        (criticalLineParameter time)‖ +
      (empiricalScaledCameraTailCauchyConstant camera time / (M : ℝ)) /
        nativeExplicitRadiusCriticalCauchyRadius)

/-- The corrected finite derivative of one camera differs from the infinite
clock tangent by the existing explicit Cauchy bound. -/
theorem norm_finiteEmpiricalCameraCorrectedDerivative_sub_clockTangent_le
    (camera : EmpiricalCamera) (M : ℕ) (hM : 1 ≤ M) (time : ℝ)
    (hzero : genuineContinuation (criticalLineParameter time) = 0) :
    ‖finiteEmpiricalCameraCorrectedDerivativeStack M
          (criticalLineParameter time) camera -
        empiricalClockTangentVector (criticalLineParameter time) camera‖ ≤
      empiricalFiniteCorrectedCameraFirstJetErrorBound camera M time := by
  exact
    norm_finiteEmpiricalCamera_logCorrectedDerivative_sub_clockTangent_critical_le
      camera M hM time hzero

/-- Euclidean aggregation of the six corrected first-jet errors. -/
def empiricalFiniteCorrectedFirstJetStackErrorBound
    (M : ℕ) (time : ℝ) : ℝ :=
  Real.sqrt
    (∑ camera : EmpiricalCamera,
      empiricalFiniteCorrectedCameraFirstJetErrorBound camera M time ^ 2)

/-- Stack-level corrected first-jet approximation. -/
theorem norm_finiteEmpiricalCameraCorrectedDerivativeStack_sub_clockTangent_le
    (M : ℕ) (hM : 1 ≤ M) (time : ℝ)
    (hzero : genuineContinuation (criticalLineParameter time) = 0) :
    ‖finiteEmpiricalCameraCorrectedDerivativeStack M
          (criticalLineParameter time) -
        empiricalClockTangentVector (criticalLineParameter time)‖ ≤
      empiricalFiniteCorrectedFirstJetStackErrorBound M time := by
  rw [EuclideanSpace.norm_eq]
  unfold empiricalFiniteCorrectedFirstJetStackErrorBound
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro camera _hcamera
  have hcomponent :=
    norm_finiteEmpiricalCameraCorrectedDerivative_sub_clockTangent_le
      camera M hM time hzero
  have hboundNonneg :
      0 ≤ empiricalFiniteCorrectedCameraFirstJetErrorBound camera M time :=
    le_trans (norm_nonneg _) hcomponent
  have hmul :=
    mul_le_mul hcomponent hcomponent
      (norm_nonneg
        (finiteEmpiricalCameraCorrectedDerivativeStack M
          (criticalLineParameter time) camera -
        empiricalClockTangentVector (criticalLineParameter time) camera))
      hboundNonneg
  simpa [pow_two] using hmul

/-- Corrected finite clock-reoptimized energy. -/
def finiteEmpiricalCorrectedReoptimizedEnergy
    (M : ℕ) (time : ℝ) : ℝ :=
  empiricalQuadraticReoptimizedEnergy
    (empiricalPhaseNormalizedFiniteResidualStack M time)
    (finiteEmpiricalCameraCorrectedDerivativeStack M
      (criticalLineParameter time))

/-- Corrected finite radial gradient. -/
def finiteEmpiricalCorrectedRadialGradient
    (M : ℕ) (time : ℝ) : ℝ :=
  empiricalQuadraticRadialGradient
    (empiricalPhaseNormalizedFiniteResidualStack M time)
    (finiteEmpiricalCameraCorrectedDerivativeStack M
      (criticalLineParameter time))

/-- Corrected finite microscopic coefficient, retaining the concrete finite
Schur coefficient from the raw transverse Hessian. -/
def finiteEmpiricalCorrectedMicroscopicCoercivity
    (M : ℕ) (time : ℝ) : ℝ :=
  quadraticMicroscopicCoercivity
    (finiteEmpiricalCorrectedReoptimizedEnergy M time)
    (finiteEmpiricalCorrectedRadialGradient M time)
    (finiteEmpiricalLocalCoercivity M time)

end

end GenuineZeroUniformAtlasEnergy

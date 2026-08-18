import GenuineZeroUniformAtlasEnergy.EmpiricalScaledTailJets

/-!
# Finite empirical derivative and cutoff-tail crosswalk

The exact prefix--tail identity is an identity of holomorphic functions on the
half-plane `re(s) > -1`, not merely an equality at one zero.  Differentiating
it at a Genuine zero gives the first concrete finite-jet crosswalk

```math
\chi'_{b,M}(s)=W_b(s)-T'_{b,M}(s),
```

where `W_b(s)` is the already identified infinite-stack clock tangent and
`T_{b,M}` is the unresolved empirical cutoff tail.

This distinction matters: the value identity at a zero is
`chi_{b,M}(s) = -T_{b,M}(s)`, but its derivative contains the nonzero infinite
clock tangent.  Treating the value identity as a neighbourhood identity would
silently delete precisely the direction that is reoptimized in the transverse
coercivity calculation.
-/

open scoped Topology

namespace GenuineZeroUniformAtlasEnergy

open CPFormal.Analytic.Cp
open Set Filter Metric

noncomputable section

/-- The bracket half-plane is a neighbourhood of each of its points. -/
lemma empiricalBracketHalfPlane_mem_nhds {s : ℂ}
    (hs : -1 < s.re) :
    {z : ℂ | -1 < z.re} ∈ 𝓝 s := by
  exact
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs

/-- Local functional form of the exact empirical prefix--tail decomposition. -/
lemma empiricalCameraCharacteristic_eventuallyEq_finite_add_cutoffTail
    (camera : EmpiricalCamera) (M : ℕ) {s : ℂ}
    (hs : -1 < s.re) :
    (fun z : ℂ => empiricalCameraCharacteristic camera z) =ᶠ[𝓝 s]
      (fun z : ℂ =>
        finiteEmpiricalCameraCharacteristic camera M z +
          empiricalCameraCutoffTail camera M z) := by
  filter_upwards [empiricalBracketHalfPlane_mem_nhds hs] with z hz
  exact empiricalCameraCharacteristic_eq_finite_add_cutoffTail
    camera M hz

/-- Every faithful empirical infinite camera is complex differentiable at
every point of the open Genuine strip. -/
theorem differentiableAt_empiricalCameraCharacteristic
    (camera : EmpiricalCamera) {s : ℂ}
    (hs : s ∈ genuineCriticalStrip) :
    DifferentiableAt ℂ (empiricalCameraCharacteristic camera) s := by
  have heq :=
    empiricalCameraCharacteristic_eventuallyEq_limitingFactor_mul_genuine
      camera hs
  have hfactor : DifferentiableAt ℂ (empiricalLimitingFactor camera) s :=
    (differentiable_empiricalLimitingFactor camera) s
  have hgenuine : DifferentiableAt ℂ genuineContinuation s :=
    (analyticOnNhd_genuineContinuation_genuineCriticalStrip s hs).differentiableAt
  have hproduct :
      DifferentiableAt ℂ
        (fun z : ℂ =>
          empiricalLimitingFactor camera z * genuineContinuation z) s :=
    hfactor.mul hgenuine
  exact hproduct.congr_of_eventuallyEq heq

/-- Every empirical cutoff tail is complex differentiable at a critical-line
point.  This is the camera specialization of the explicit-radius holomorphy
ball. -/
theorem differentiableAt_empiricalCameraCutoffTail_critical
    (camera : EmpiricalCamera) (M : ℕ) (time : ℝ) :
    DifferentiableAt ℂ (empiricalCameraCutoffTail camera M)
      (criticalLineParameter time) := by
  have hb : 1 ≤ camera.period :=
    Nat.succ_le_iff.mpr (empiricalCamera_period_pos camera)
  have hh : camera.label / 2 ≤ camera.period - 1 :=
    empiricalCamera_retainedRadius_le_period_sub_one camera
  have hmem :
      criticalLineParameter time ∈
        ball (criticalLineParameter time)
          nativeExplicitRadiusCriticalOuterRadius :=
    mem_ball_self (by
      unfold nativeExplicitRadiusCriticalOuterRadius
      norm_num)
  have hnative :
      DifferentiableAt ℂ
        (nativeExplicitRadiusCutoffTail
          camera.period (camera.label / 2) M)
        (criticalLineParameter time) := by
    exact
      (differentiableOn_nativeExplicitRadiusCutoffTail_criticalOuterBall
        camera.period (camera.label / 2) M hb hh time).differentiableAt
          (isOpen_ball.mem_nhds hmem)
  rw [show empiricalCameraCutoffTail camera M =
      nativeExplicitRadiusCutoffTail
        camera.period (camera.label / 2) M by
    funext z
    exact empiricalCameraCutoffTail_eq_nativeExplicitRadiusCutoffTail
      camera M z]
  exact hnative

/-- Exact first finite-jet crosswalk at a Genuine critical zero.  The finite
camera derivative is the concrete infinite clock tangent minus the unresolved
tail derivative. -/
theorem deriv_finiteEmpiricalCameraCharacteristic_eq_clockTangent_sub_cutoffTail
    (camera : EmpiricalCamera) (M : ℕ) (time : ℝ)
    (hzero : genuineContinuation (criticalLineParameter time) = 0) :
    deriv (finiteEmpiricalCameraCharacteristic camera M)
        (criticalLineParameter time) =
      empiricalClockTangentVector (criticalLineParameter time) camera -
        deriv (empiricalCameraCutoffTail camera M)
          (criticalLineParameter time) := by
  let s : ℂ := criticalLineParameter time
  have hsStrip : s ∈ genuineCriticalStrip := by
    dsimp [s]
    exact criticalLineParameter_mem_genuineCriticalStrip time
  have hsHalf : -1 < s.re := by
    dsimp [s]
    norm_num [criticalLineParameter_re]
  have hsplit :=
    empiricalCameraCharacteristic_eventuallyEq_finite_add_cutoffTail
      camera M hsHalf
  have hfiniteEq :
      (fun z : ℂ => finiteEmpiricalCameraCharacteristic camera M z) =ᶠ[𝓝 s]
        (fun z : ℂ =>
          empiricalCameraCharacteristic camera z -
            empiricalCameraCutoffTail camera M z) := by
    filter_upwards [hsplit] with z hz
    rw [hz]
    ring
  have hcharacteristic :
      DifferentiableAt ℂ (empiricalCameraCharacteristic camera) s :=
    differentiableAt_empiricalCameraCharacteristic camera hsStrip
  have htail :
      DifferentiableAt ℂ (empiricalCameraCutoffTail camera M) s := by
    simpa [s] using
      differentiableAt_empiricalCameraCutoffTail_critical camera M time
  calc
    deriv (finiteEmpiricalCameraCharacteristic camera M) s =
        deriv
          (fun z : ℂ =>
            empiricalCameraCharacteristic camera z -
              empiricalCameraCutoffTail camera M z) s :=
      hfiniteEq.deriv_eq
    _ = deriv (empiricalCameraCharacteristic camera) s -
          deriv (empiricalCameraCutoffTail camera M) s :=
      (hcharacteristic.hasDerivAt.sub htail.hasDerivAt).deriv
    _ = empiricalClockTangentVector s camera -
          deriv (empiricalCameraCutoffTail camera M) s := by
      rw [deriv_empiricalCameraCharacteristic_eq_clockTangent
        camera hsStrip (by simpa [s] using hzero)]

/-- Exact logarithmically corrected first-jet identity.  Adding
`log(M) * chi_{b,M}` cancels the derivative of the critical cutoff phase on
the value channel and leaves the clock tangent minus the correspondingly
corrected unresolved-tail jet. -/
theorem finiteEmpiricalCamera_logCorrectedDerivative_eq_clockTangent_sub_tailLogJet
    (camera : EmpiricalCamera) (M : ℕ) (time : ℝ)
    (hzero : genuineContinuation (criticalLineParameter time) = 0) :
    deriv (finiteEmpiricalCameraCharacteristic camera M)
          (criticalLineParameter time) +
        nativeCutoffLog M *
          finiteEmpiricalCameraCharacteristic camera M
            (criticalLineParameter time) =
      empiricalClockTangentVector (criticalLineParameter time) camera -
        (deriv (empiricalCameraCutoffTail camera M)
            (criticalLineParameter time) +
          nativeCutoffLog M *
            empiricalCameraCutoffTail camera M
              (criticalLineParameter time)) := by
  have hsHalf : -1 < (criticalLineParameter time).re := by
    norm_num [criticalLineParameter_re]
  have hcameraZero :
      empiricalCameraCharacteristic camera
        (criticalLineParameter time) = 0 :=
    empiricalCameraCharacteristic_zero_of_genuineContinuation_zero
      camera (criticalLineParameter_mem_genuineCriticalStrip time) hzero
  have hvalue :=
    finiteEmpiricalCameraCharacteristic_eq_neg_cutoffTail_of_zero
      camera M hsHalf hcameraZero
  rw [deriv_finiteEmpiricalCameraCharacteristic_eq_clockTangent_sub_cutoffTail
    camera M time hzero, hvalue]
  ring

/-- Finite derivative stack of the faithful six empirical cameras. -/
def finiteEmpiricalCameraDerivativeStack
    (M : ℕ) (s : ℂ) : EmpiricalCameraStack :=
  WithLp.toLp 2 fun camera =>
    deriv (finiteEmpiricalCameraCharacteristic camera M) s

/-- Derivative stack of the six unresolved empirical cutoff tails. -/
def empiricalCameraCutoffTailDerivativeStack
    (M : ℕ) (s : ℂ) : EmpiricalCameraStack :=
  WithLp.toLp 2 fun camera =>
    deriv (empiricalCameraCutoffTail camera M) s

@[simp] theorem finiteEmpiricalCameraDerivativeStack_apply
    (M : ℕ) (s : ℂ) (camera : EmpiricalCamera) :
    finiteEmpiricalCameraDerivativeStack M s camera =
      deriv (finiteEmpiricalCameraCharacteristic camera M) s := by
  rfl

@[simp] theorem empiricalCameraCutoffTailDerivativeStack_apply
    (M : ℕ) (s : ℂ) (camera : EmpiricalCamera) :
    empiricalCameraCutoffTailDerivativeStack M s camera =
      deriv (empiricalCameraCutoffTail camera M) s := by
  rfl

/-- Stack form of the first finite-jet crosswalk. -/
theorem finiteEmpiricalCameraDerivativeStack_eq_clockTangent_sub_cutoffTail
    (M : ℕ) (time : ℝ)
    (hzero : genuineContinuation (criticalLineParameter time) = 0) :
    finiteEmpiricalCameraDerivativeStack M (criticalLineParameter time) =
      empiricalClockTangentVector (criticalLineParameter time) -
        empiricalCameraCutoffTailDerivativeStack M
          (criticalLineParameter time) := by
  ext camera
  change
    deriv (finiteEmpiricalCameraCharacteristic camera M)
        (criticalLineParameter time) =
      empiricalClockTangentVector (criticalLineParameter time) camera -
        deriv (empiricalCameraCutoffTail camera M)
          (criticalLineParameter time)
  exact
    deriv_finiteEmpiricalCameraCharacteristic_eq_clockTangent_sub_cutoffTail
      camera M time hzero

end

end GenuineZeroUniformAtlasEnergy

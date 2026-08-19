import GenuineZeroUniformAtlasEnergy.EmpiricalFiniteTransverseData
import GenuineZeroUniformAtlasEnergy.GenuineZeroMultiplicity
import GenuineZeroUniformAtlasEnergy.EmpiricalCameraHigherDerivativeCrosswalk

/-!
# Exact finite empirical second-jet crosswalk

The finite empirical characteristic is an exact prefix of the infinite camera
characteristic.  On the bracket half-plane,

```math
\chi_b=\chi_{b,M}+T_{b,M}.
```

Differentiating twice gives the exact identity

```math
\chi_{b,M}''=\chi_b''-T_{b,M}''.
```

This identity is valid for every positive cutoff and does not use a numerical
height or a simplicity hypothesis.  At a critical Genuine zero, simplicity is
needed later only to make the order-one clock direction nonzero.  The cutoff
`M` and the zero multiplicity `m` are distinct parameters.

The spectral-Weyl camera library already proves an all-order Cauchy tail bound.
After the exact camera crosswalk, the order-two specialization gives

```math
\|\chi_b''-\chi_{b,M}''\|
\le 2 C_b(t) M^{-3/2}\log(M)^2.
```

Thus the finite second jet is a fixed infinite second jet plus a decaying tail,
and is uniformly bounded eventually.
-/

open scoped BigOperators Topology

namespace GenuineZeroUniformAtlasEnergy

open CPFormal.Analytic.Cp
open Set Metric

noncomputable section

/-- The faithful infinite empirical characteristic is analytic at every point
of the open Genuine strip. -/
theorem analyticAt_empiricalCameraCharacteristic
    (camera : EmpiricalCamera) {s : ℂ}
    (hs : s ∈ genuineCriticalStrip) :
    AnalyticAt ℂ (empiricalCameraCharacteristic camera) s := by
  have heq :=
    empiricalCameraCharacteristic_eventuallyEq_limitingFactor_mul_genuine
      camera hs
  have hfactor : AnalyticAt ℂ (empiricalLimitingFactor camera) s :=
    (differentiable_empiricalLimitingFactor camera).analyticAt s
  have hgenuine : AnalyticAt ℂ genuineContinuation s :=
    analyticOnNhd_genuineContinuation_genuineCriticalStrip s hs
  rw [← analyticWithinAt_univ] at hfactor hgenuine ⊢
  exact
    (hfactor.mul hgenuine).congr_of_eventuallyEq_insert
      (by simpa using heq)

/-- The unresolved empirical cutoff tail is analytic at every critical-line
point.  The proof uses the already established holomorphy ball. -/
theorem analyticAt_empiricalCameraCutoffTail_critical
    (camera : EmpiricalCamera) (M : ℕ) (time : ℝ) :
    AnalyticAt ℂ (empiricalCameraCutoffTail camera M)
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
  have hdiff :=
    differentiableOn_nativeExplicitRadiusCutoffTail_criticalOuterBall
      camera.period (camera.label / 2) M hb hh time
  have hanalytic :
      AnalyticAt ℂ
        (nativeExplicitRadiusCutoffTail
          camera.period (camera.label / 2) M)
        (criticalLineParameter time) :=
    hdiff.analyticAt (isOpen_ball.mem_nhds hmem)
  rw [show empiricalCameraCutoffTail camera M =
      nativeExplicitRadiusCutoffTail
        camera.period (camera.label / 2) M by
    funext z
    exact empiricalCameraCutoffTail_eq_nativeExplicitRadiusCutoffTail
      camera M z]
  exact hanalytic

/-- Exact camerawise second-jet identity.  Unlike the value identity at a zero,
this retains the second derivative of the infinite camera characteristic. -/
theorem iteratedDeriv_two_finiteEmpiricalCameraCharacteristic_eq_infinite_sub_cutoffTail
    (camera : EmpiricalCamera) (M : ℕ) (time : ℝ) :
    iteratedDeriv 2 (finiteEmpiricalCameraCharacteristic camera M)
        (criticalLineParameter time) =
      iteratedDeriv 2 (empiricalCameraCharacteristic camera)
          (criticalLineParameter time) -
        iteratedDeriv 2 (empiricalCameraCutoffTail camera M)
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
  have hinfinite :
      ContDiffAt ℂ 2 (empiricalCameraCharacteristic camera) s :=
    (analyticAt_empiricalCameraCharacteristic camera hsStrip).contDiffAt
  have htail :
      ContDiffAt ℂ 2 (empiricalCameraCutoffTail camera M) s := by
    simpa [s] using
      (analyticAt_empiricalCameraCutoffTail_critical camera M time).contDiffAt
  calc
    iteratedDeriv 2 (finiteEmpiricalCameraCharacteristic camera M) s =
        iteratedDeriv 2
          (fun z : ℂ =>
            empiricalCameraCharacteristic camera z -
              empiricalCameraCutoffTail camera M z) s := by
      exact (hfiniteEq.iteratedDeriv 2).eq_of_nhds
    _ = iteratedDeriv 2 (empiricalCameraCharacteristic camera) s -
          iteratedDeriv 2 (empiricalCameraCutoffTail camera M) s :=
      iteratedDeriv_fun_sub hinfinite htail

/-- Second derivative stack of the unresolved empirical tails. -/
def empiricalCameraCutoffTailSecondDerivativeStack
    (M : ℕ) (s : ℂ) : EmpiricalCameraStack :=
  WithLp.toLp 2 fun camera =>
    iteratedDeriv 2 (empiricalCameraCutoffTail camera M) s

@[simp] theorem empiricalCameraCutoffTailSecondDerivativeStack_apply
    (M : ℕ) (s : ℂ) (camera : EmpiricalCamera) :
    empiricalCameraCutoffTailSecondDerivativeStack M s camera =
      iteratedDeriv 2 (empiricalCameraCutoffTail camera M) s := by
  rfl

/-- Stack form of the exact second-jet crosswalk. -/
theorem finiteEmpiricalCameraSecondDerivativeStack_eq_infinite_sub_cutoffTail
    (M : ℕ) (time : ℝ) :
    finiteEmpiricalCameraSecondDerivativeStack M
        (criticalLineParameter time) =
      empiricalCameraIteratedDerivativeStack 2
          (criticalLineParameter time) -
        empiricalCameraCutoffTailSecondDerivativeStack M
          (criticalLineParameter time) := by
  ext camera
  exact
    iteratedDeriv_two_finiteEmpiricalCameraCharacteristic_eq_infinite_sub_cutoffTail
      camera M time

/-- Immediate camerawise norm ledger.  The finite second jet is controlled by
the fixed infinite second jet plus the decaying unresolved-tail second jet. -/
theorem norm_iteratedDeriv_two_finiteEmpiricalCameraCharacteristic_le
    (camera : EmpiricalCamera) (M : ℕ) (time : ℝ) :
    ‖iteratedDeriv 2 (finiteEmpiricalCameraCharacteristic camera M)
        (criticalLineParameter time)‖ ≤
      ‖iteratedDeriv 2 (empiricalCameraCharacteristic camera)
          (criticalLineParameter time)‖ +
        ‖iteratedDeriv 2 (empiricalCameraCutoffTail camera M)
          (criticalLineParameter time)‖ := by
  rw [iteratedDeriv_two_finiteEmpiricalCameraCharacteristic_eq_infinite_sub_cutoffTail]
  exact norm_sub_le _ _

/-- Explicit order-two Cauchy tail rate for one empirical camera. -/
def empiricalCameraSecondJetTailRateBound
    (camera : EmpiricalCamera) (M : ℕ) (time : ℝ) : ℝ :=
  (2 *
      NativeCarrySpectralWeyl.Camera.higherDerivativeCircleConstant
        camera.label time) *
    (M : ℝ) ^ (-(3 : ℝ) / 2) *
      (Real.log (M : ℝ)) ^ 2

/-- The second derivative tail itself obeys the inherited all-order Cauchy
estimate. -/
theorem norm_iteratedDeriv_two_empiricalCameraCutoffTail_le
    (camera : EmpiricalCamera) (M : ℕ)
    (hM : Real.exp 2 ≤ (M : ℝ)) (time : ℝ) :
    ‖iteratedDeriv 2 (empiricalCameraCutoffTail camera M)
        (criticalLineParameter time)‖ ≤
      empiricalCameraSecondJetTailRateBound camera M time := by
  have htail :=
    norm_iteratedDeriv_empiricalCameraCharacteristic_sub_finite_le
      camera M 2 hM time
  have hidentity :=
    iteratedDeriv_two_finiteEmpiricalCameraCharacteristic_eq_infinite_sub_cutoffTail
      camera M time
  have hrearrange :
      iteratedDeriv 2 (empiricalCameraCharacteristic camera)
          (criticalLineParameter time) -
        iteratedDeriv 2 (finiteEmpiricalCameraCharacteristic camera M)
          (criticalLineParameter time) =
      iteratedDeriv 2 (empiricalCameraCutoffTail camera M)
        (criticalLineParameter time) := by
    rw [hidentity]
    ring
  rw [hrearrange] at htail
  simpa [empiricalCameraSecondJetTailRateBound] using htail

/-- Explicit finite second-jet bound for one camera. -/
theorem norm_iteratedDeriv_two_finiteEmpiricalCameraCharacteristic_le_explicit
    (camera : EmpiricalCamera) (M : ℕ)
    (hM : Real.exp 2 ≤ (M : ℝ)) (time : ℝ) :
    ‖iteratedDeriv 2 (finiteEmpiricalCameraCharacteristic camera M)
        (criticalLineParameter time)‖ ≤
      ‖iteratedDeriv 2 (empiricalCameraCharacteristic camera)
          (criticalLineParameter time)‖ +
        empiricalCameraSecondJetTailRateBound camera M time := by
  exact
    (norm_iteratedDeriv_two_finiteEmpiricalCameraCharacteristic_le
      camera M time).trans
        (add_le_add_right
          (norm_iteratedDeriv_two_empiricalCameraCutoffTail_le
            camera M hM time) _)

/-- Euclidean aggregation of the six explicit finite second-jet bounds. -/
def empiricalFiniteSecondJetStackBound
    (M : ℕ) (time : ℝ) : ℝ :=
  Real.sqrt
    (∑ camera : EmpiricalCamera,
      (‖iteratedDeriv 2 (empiricalCameraCharacteristic camera)
          (criticalLineParameter time)‖ +
        empiricalCameraSecondJetTailRateBound camera M time) ^ 2)

/-- The complete finite six-camera second-derivative stack obeys the explicit
Euclidean aggregation of the camerawise bounds. -/
theorem norm_finiteEmpiricalCameraSecondDerivativeStack_le
    (M : ℕ) (hM : Real.exp 2 ≤ (M : ℝ)) (time : ℝ) :
    ‖finiteEmpiricalCameraSecondDerivativeStack M
        (criticalLineParameter time)‖ ≤
      empiricalFiniteSecondJetStackBound M time := by
  rw [EuclideanSpace.norm_eq]
  unfold empiricalFiniteSecondJetStackBound
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro camera _hcamera
  have hcomponent :=
    norm_iteratedDeriv_two_finiteEmpiricalCameraCharacteristic_le_explicit
      camera M hM time
  have hboundNonneg :
      0 ≤ ‖iteratedDeriv 2 (empiricalCameraCharacteristic camera)
          (criticalLineParameter time)‖ +
        empiricalCameraSecondJetTailRateBound camera M time :=
    le_trans (norm_nonneg _) hcomponent
  have hmul :=
    mul_le_mul hcomponent hcomponent
      (norm_nonneg
        (iteratedDeriv 2 (finiteEmpiricalCameraCharacteristic camera M)
          (criticalLineParameter time)))
      hboundNonneg
  simpa [finiteEmpiricalCameraSecondDerivativeStack, pow_two] using hmul

end

end GenuineZeroUniformAtlasEnergy

import GenuineZeroUniformAtlasEnergy.EmpiricalScaledTailJets
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Real critical-line jets of the collective cutoff-tail energy

The value estimates in `EmpiricalCollectiveEnergyAsymptotic` are estimates for
the unresolved tail.  This file adds the real parameter jets of that same
tail, keeping the scale

`Z_M(t) = M^(s_t+1) T_M(s_t)`

outside the differentiation of the energy.  Since `Re (s_t+1) = 3/2`, the
identity `|Z_M(t)|^2 = M^3 |T_M(s_t)|^2` is exact.  Thus no logarithm is paid
when differentiating the energy.  The logarithms in the unscaled complex
jets remain exposed by `NativeCutoffLogJet` and are not silently discarded.

The finite raw characteristic is intentionally not identified with this
real-time function in a neighbourhood of a zero: its differentiated
crosswalk contains the order-one clock tangent.  The quantitative theorems
below therefore concern the faithful cutoff-tail energy, which is the object
for which the phase cancellation is an identity.
-/

open scoped BigOperators Topology

namespace GenuineZeroUniformAtlasEnergy

open CPFormal.Analytic.Cp
open Set Filter

noncomputable section

attribute [local instance 10000] NormedSpace.complexToReal

/-! ## Real critical-line parameter and generic analytic jets -/

/-- The critical-line parameter has real derivative `I`. -/
lemma hasDerivAt_criticalLineParameter (time : ℝ) :
    HasDerivAt criticalLineParameter Complex.I time := by
  have hlinear : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 time := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one] using
      (Complex.ofRealCLM.hasDerivAt (x := time))
  have hrot : HasDerivAt (fun u : ℝ => (u : ℂ) * Complex.I)
      (1 * Complex.I) time := hlinear.mul_const Complex.I
  have hsum :=
    (hasDerivAt_const time ((1 / 2 : ℝ) : ℂ)).add hrot
  simpa [criticalLineParameter] using hsum

/-- First real jet of a complex analytic function along the critical line. -/
def criticalLineFirstJet (F : ℂ → ℂ) (time : ℝ) : ℂ :=
  Complex.I * iteratedDeriv 1 F (criticalLineParameter time)

/-- Second real jet of a complex analytic function along the critical line. -/
def criticalLineSecondJet (F : ℂ → ℂ) (time : ℝ) : ℂ :=
  -iteratedDeriv 2 F (criticalLineParameter time)

lemma hasDerivAt_criticalLine_comp
    (F : ℂ → ℂ) {F' : ℂ} (time : ℝ)
    (hF : HasDerivAt F F' (criticalLineParameter time)) :
    HasDerivAt (fun u : ℝ => F (criticalLineParameter u))
      (Complex.I * F') time := by
  have hcomp := hF.scomp (x := time)
    (hasDerivAt_criticalLineParameter time)
  simpa [Function.comp_def, smul_eq_mul] using hcomp

lemma hasDerivAt_criticalLine_firstJet_comp
    (F : ℂ → ℂ) (time : ℝ)
    (hF : HasDerivAt F (iteratedDeriv 1 F (criticalLineParameter time))
      (criticalLineParameter time))
    (hF' : HasDerivAt (iteratedDeriv 1 F)
      (iteratedDeriv 2 F (criticalLineParameter time))
      (criticalLineParameter time)) :
    HasDerivAt
      (fun u : ℝ => criticalLineFirstJet F u)
      (criticalLineSecondJet F time) time := by
  have hcomp := hasDerivAt_criticalLine_comp
    (iteratedDeriv 1 F) time hF'
  have hmul := (hasDerivAt_const time Complex.I).mul hcomp
  convert hmul using 1 <;>
    simp [criticalLineFirstJet, criticalLineSecondJet, Function.comp_def,
      smul_eq_mul, Complex.I_mul_I, mul_assoc]

/-- Analyticity supplies both complex derivatives needed by the real first jet. -/
lemma hasDerivAt_criticalLine_of_analytic
    (F : ℂ → ℂ) (time : ℝ)
    (hF : AnalyticAt ℂ F (criticalLineParameter time)) :
    HasDerivAt (fun u : ℝ => F (criticalLineParameter u))
      (criticalLineFirstJet F time) time := by
  have hcont : ContDiffAt ℂ 1 F (criticalLineParameter time) :=
    hF.contDiffAt
  have hderiv :=
    (hcont.differentiableAt (by norm_num)).hasDerivAt
  simpa [criticalLineFirstJet, iteratedDeriv_one] using
    hasDerivAt_criticalLine_comp F time hderiv

/-- Analyticity supplies the real second jet without any logarithmic factor. -/
lemma hasDerivAt_criticalLine_firstJet_of_analytic
    (F : ℂ → ℂ) (time : ℝ)
    (hF : AnalyticAt ℂ F (criticalLineParameter time)) :
    HasDerivAt (fun u : ℝ => criticalLineFirstJet F u)
      (criticalLineSecondJet F time) time := by
  have hcont : ContDiffAt ℂ 3 F (criticalLineParameter time) :=
    hF.contDiffAt
  have hderivCont : ContDiffAt ℂ 2 (deriv F)
      (criticalLineParameter time) :=
    hcont.derivWithin (m := 2) (by norm_num)
  have hderiv :=
    (hderivCont.differentiableAt (by norm_num)).hasDerivAt
  have hderiv' : HasDerivAt (iteratedDeriv 1 F)
      (iteratedDeriv 2 F (criticalLineParameter time))
      (criticalLineParameter time) := by
    simpa [iteratedDeriv_one, iteratedDeriv_succ] using hderiv
  have hF' : HasDerivAt F
      (iteratedDeriv 1 F (criticalLineParameter time))
      (criticalLineParameter time) := by
    have h :=
      ((hF.contDiffAt : ContDiffAt ℂ 1 F
        (criticalLineParameter time)).differentiableAt (by norm_num)).hasDerivAt
    simpa [iteratedDeriv_one] using h
  exact hasDerivAt_criticalLine_firstJet_comp F time hF' hderiv'

/-! ## Concrete camera paths and their controlled error jets -/

/-- First real jet of the naturally scaled empirical tail. -/
def empiricalScaledCameraCutoffTailCriticalFirst
    (camera : EmpiricalCamera) (M : ℕ) (time : ℝ) : ℂ :=
  criticalLineFirstJet
    (fun s : ℂ ↦ (M : ℂ) ^ (s + 1) *
      empiricalCameraCutoffTail camera M s) time

/-- Second real jet of the naturally scaled empirical tail. -/
def empiricalScaledCameraCutoffTailCriticalSecond
    (camera : EmpiricalCamera) (M : ℕ) (time : ℝ) : ℂ :=
  criticalLineSecondJet
    (fun s : ℂ ↦ (M : ℂ) ^ (s + 1) *
      empiricalCameraCutoffTail camera M s) time

/-- The leading coefficient restricted to the real critical line. -/
def empiricalNativeTailCoefficientCritical
    (camera : EmpiricalCamera) (time : ℝ) : ℂ :=
  empiricalNativeTailCoefficient camera (criticalLineParameter time)

/-- First real jet of a leading camera coefficient. -/
def empiricalNativeTailCoefficientCriticalFirst
    (camera : EmpiricalCamera) (time : ℝ) : ℂ :=
  criticalLineFirstJet (empiricalNativeTailCoefficient camera) time

/-- Second real jet of a leading camera coefficient. -/
def empiricalNativeTailCoefficientCriticalSecond
    (camera : EmpiricalCamera) (time : ℝ) : ℂ :=
  criticalLineSecondJet (empiricalNativeTailCoefficient camera) time

/-- Scaled-tail error restricted to the critical line. -/
def empiricalScaledCameraTailErrorCritical
    (camera : EmpiricalCamera) (M : ℕ) (time : ℝ) : ℂ :=
  empiricalScaledCameraTailError camera M (criticalLineParameter time)

/-- First real jet of the scaled-tail error. -/
def empiricalScaledCameraTailErrorCriticalFirst
    (camera : EmpiricalCamera) (M : ℕ) (time : ℝ) : ℂ :=
  criticalLineFirstJet (empiricalScaledCameraTailError camera M) time

/-- Second real jet of the scaled-tail error. -/
def empiricalScaledCameraTailErrorCriticalSecond
    (camera : EmpiricalCamera) (M : ℕ) (time : ℝ) : ℂ :=
  criticalLineSecondJet (empiricalScaledCameraTailError camera M) time

lemma analyticAt_empiricalScaledCameraTailError_critical
    (camera : EmpiricalCamera) (M : ℕ) (hM : 1 ≤ M) (time : ℝ) :
    AnalyticAt ℂ (empiricalScaledCameraTailError camera M)
      (criticalLineParameter time) := by
  have hb : 1 ≤ camera.period :=
    Nat.succ_le_iff.mpr (empiricalCamera_period_pos camera)
  have hh : camera.label / 2 ≤ camera.period - 1 :=
    empiricalCamera_retainedRadius_le_period_sub_one camera
  have hmem : criticalLineParameter time ∈
      ball (criticalLineParameter time)
        nativeExplicitRadiusCriticalOuterRadius :=
    mem_ball_self (by
      unfold nativeExplicitRadiusCriticalOuterRadius
      norm_num)
  have hnative :=
    differentiableOn_nativeExplicitRadiusScaledTailError_criticalOuterBall
      camera.period (camera.label / 2) M hb hh hM time
  have hanalytic : AnalyticAt ℂ
      (nativeExplicitRadiusScaledTailError
        camera.period (camera.label / 2) M)
      (criticalLineParameter time) :=
    hnative.analyticAt (isOpen_ball.mem_nhds hmem)
  rw [empiricalScaledCameraTailError_fun_eq_native camera M]
  exact hanalytic

lemma analyticAt_empiricalNativeTailCoefficient_critical
    (camera : EmpiricalCamera) (time : ℝ) :
    AnalyticAt ℂ (empiricalNativeTailCoefficient camera)
      (criticalLineParameter time) := by
  have hb : 1 ≤ camera.period :=
    Nat.succ_le_iff.mpr (empiricalCamera_period_pos camera)
  simpa [empiricalNativeTailCoefficient] using
    (differentiable_nativeExplicitRadiusTailCoefficient
      camera.period (camera.label / 2) hb).analyticAt
      (criticalLineParameter time)

lemma hasDerivAt_empiricalScaledCameraCutoffTail_critical
    (camera : EmpiricalCamera) (M : ℕ) (hM : 1 ≤ M) (time : ℝ) :
    HasDerivAt (fun u : ℝ =>
      empiricalScaledCameraCutoffTail camera M u)
      (empiricalScaledCameraCutoffTailCriticalFirst camera M time) time := by
  have herror := hasDerivAt_criticalLine_of_analytic
    (empiricalScaledCameraTailError camera M) time
    (analyticAt_empiricalScaledCameraTailError_critical camera M hM time)
  have hcoef := hasDerivAt_criticalLine_of_analytic
    (empiricalNativeTailCoefficient camera) time
    (analyticAt_empiricalNativeTailCoefficient_critical camera time)
  have hsum := hcoef.add herror
  have heq : ∀ u : ℝ,
      empiricalScaledCameraCutoffTail camera M u =
        empiricalNativeTailCoefficientCritical camera u +
          empiricalScaledCameraTailErrorCritical camera M u := by
    intro u
    unfold empiricalScaledCameraCutoffTail
      empiricalNativeTailCoefficientCritical
      empiricalScaledCameraTailErrorCritical
      empiricalScaledCameraTailError
    ring
  have heq' : (fun u : ℝ => empiricalScaledCameraCutoffTail camera M u) =ᶠ[𝓝 time]
      (fun u : ℝ => empiricalNativeTailCoefficientCritical camera u +
        empiricalScaledCameraTailErrorCritical camera M u) :=
    Filter.Eventually.of_forall heq
  have hresult := hsum.congr_of_eventuallyEq heq'.symm
  simpa [empiricalScaledCameraCutoffTailCriticalFirst,
    empiricalNativeTailCoefficientCriticalFirst,
    empiricalScaledCameraTailErrorCriticalFirst,
    criticalLineFirstJet] using hresult

lemma hasDerivAt_empiricalScaledCameraCutoffTail_critical_firstJet
    (camera : EmpiricalCamera) (M : ℕ) (hM : 1 ≤ M) (time : ℝ) :
    HasDerivAt (fun u : ℝ =>
      empiricalScaledCameraCutoffTailCriticalFirst camera M u)
      (empiricalScaledCameraCutoffTailCriticalSecond camera M time) time := by
  have herror := hasDerivAt_criticalLine_firstJet_of_analytic
    (empiricalScaledCameraTailError camera M) time
    (analyticAt_empiricalScaledCameraTailError_critical camera M hM time)
  have hcoef := hasDerivAt_criticalLine_firstJet_of_analytic
    (empiricalNativeTailCoefficient camera) time
    (analyticAt_empiricalNativeTailCoefficient_critical camera time)
  have hsum := hcoef.add herror
  simpa [empiricalScaledCameraCutoffTailCriticalFirst,
    empiricalScaledCameraCutoffTailCriticalSecond,
    empiricalNativeTailCoefficientCriticalFirst,
    empiricalScaledCameraTailErrorCriticalFirst,
    empiricalNativeTailCoefficientCriticalSecond,
    empiricalScaledCameraTailErrorCriticalSecond,
    criticalLineFirstJet, criticalLineSecondJet] using hsum

lemma norm_empiricalScaledCameraTailErrorCriticalFirst_le
    (camera : EmpiricalCamera) (M : ℕ) (hM : 1 ≤ M) (time : ℝ) :
    ‖empiricalScaledCameraTailErrorCriticalFirst camera M time‖ ≤
      (empiricalScaledCameraTailCauchyConstant camera time / (M : ℝ)) /
        nativeExplicitRadiusCriticalCauchyRadius := by
  unfold empiricalScaledCameraTailErrorCriticalFirst criticalLineFirstJet
  rw [norm_mul]
  simp only [norm_I, one_mul]
  simpa [iteratedDeriv_one] using
    norm_iteratedDeriv_one_empiricalScaledCameraTailError_critical
      camera M hM time

lemma norm_empiricalScaledCameraTailErrorCriticalSecond_le
    (camera : EmpiricalCamera) (M : ℕ) (hM : 1 ≤ M) (time : ℝ) :
    ‖empiricalScaledCameraTailErrorCriticalSecond camera M time‖ ≤
      2 * (empiricalScaledCameraTailCauchyConstant camera time / (M : ℝ)) /
        nativeExplicitRadiusCriticalCauchyRadius ^ 2 := by
  unfold empiricalScaledCameraTailErrorCriticalSecond criticalLineSecondJet
  rw [norm_neg]
  simpa using
    norm_iteratedDeriv_two_empiricalScaledCameraTailError_critical
      camera M hM time

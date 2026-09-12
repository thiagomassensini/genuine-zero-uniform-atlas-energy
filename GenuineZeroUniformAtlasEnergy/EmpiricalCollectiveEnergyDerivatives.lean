import GenuineZeroUniformAtlasEnergy.EmpiricalScaledTailJets
import GenuineZeroUniformAtlasEnergy.EmpiricalCollectiveEnergyAsymptotic
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

open scoped BigOperators Topology ComplexConjugate InnerProductSpace

namespace GenuineZeroUniformAtlasEnergy

open CPFormal.Analytic.Cp
open Set Filter Metric

noncomputable section

/-! ## Real critical-line parameter and generic analytic jets -/

/-- The critical-line parameter has real derivative `I`. -/
lemma hasDerivAt_criticalLineParameter (time : ℝ) :
    HasDerivAt criticalLineParameter Complex.I time := by
  have hlinear : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 time := by
    simpa using (HasDerivAt.ofReal_comp (hasDerivAt_id time))
  have hrot : HasDerivAt (fun u : ℝ => (u : ℂ) * Complex.I)
      (1 * Complex.I) time := hlinear.mul_const Complex.I
  have hsum :=
    (hasDerivAt_const time ((1 / 2 : ℝ) : ℂ)).add hrot
  convert hsum using 1
  · funext u
    simp [criticalLineParameter]
  · simp

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
  convert hmul using 1
  · simp [criticalLineFirstJet, Function.comp_def]
  · simp [criticalLineSecondJet, Complex.I_mul_I]

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

lemma analyticAt_empiricalScaledCameraCutoffTail_critical
    (camera : EmpiricalCamera) (M : ℕ) (hM : 1 ≤ M) (time : ℝ) :
    AnalyticAt ℂ
      (fun s : ℂ => (M : ℂ) ^ (s + 1) *
        empiricalCameraCutoffTail camera M s)
      (criticalLineParameter time) := by
  have herror := analyticAt_empiricalScaledCameraTailError_critical
    camera M hM time
  have hcoef := analyticAt_empiricalNativeTailCoefficient_critical camera time
  have hsum := hcoef.add herror
  have heq : (fun s : ℂ => (M : ℂ) ^ (s + 1) *
      empiricalCameraCutoffTail camera M s) =
      (empiricalNativeTailCoefficient camera +
        empiricalScaledCameraTailError camera M) := by
    funext s
    unfold empiricalScaledCameraTailError
    ring
  rw [heq]
  exact hsum

lemma hasDerivAt_empiricalScaledCameraCutoffTail_critical
    (camera : EmpiricalCamera) (M : ℕ) (hM : 1 ≤ M) (time : ℝ) :
    HasDerivAt (fun u : ℝ =>
      empiricalScaledCameraCutoffTail camera M u)
      (empiricalScaledCameraCutoffTailCriticalFirst camera M time) time := by
  exact hasDerivAt_criticalLine_of_analytic
    (fun s : ℂ => (M : ℂ) ^ (s + 1) *
      empiricalCameraCutoffTail camera M s) time
    (analyticAt_empiricalScaledCameraCutoffTail_critical camera M hM time)

lemma hasDerivAt_empiricalScaledCameraCutoffTail_critical_firstJet
    (camera : EmpiricalCamera) (M : ℕ) (hM : 1 ≤ M) (time : ℝ) :
    HasDerivAt (fun u : ℝ =>
      empiricalScaledCameraCutoffTailCriticalFirst camera M u)
      (empiricalScaledCameraCutoffTailCriticalSecond camera M time) time := by
  exact hasDerivAt_criticalLine_firstJet_of_analytic
    (fun s : ℂ => (M : ℂ) ^ (s + 1) *
      empiricalCameraCutoffTail camera M s) time
    (analyticAt_empiricalScaledCameraCutoffTail_critical camera M hM time)

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

/-! ## Real quadratic jet algebra

The following two pairings are deliberately written with the Hermitian inner
product.  This makes the estimates use the ordinary Cauchy--Schwarz bound,
while keeping the real part visible in the phase-cancellation lemmas below.
-/

/-- Twice the real Hermitian pairing of two complex amplitudes. -/
def complexEnergyPair (z w : ℂ) : ℝ :=
  2 * (inner ℂ z w).re

/-- The second derivative pairing of a complex path. -/
def complexEnergyHessianPair (z z' z'' : ℂ) : ℝ :=
  complexEnergyPair z z'' + complexEnergyPair z' z'

lemma complexEnergyPair_self (z : ℂ) :
    complexEnergyPair z z = 2 * ‖z‖ ^ 2 := by
  unfold complexEnergyPair
  rw [RCLike.inner_apply']
  simp [Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.sq_norm]
  ring

lemma abs_complexEnergyPair_le (z w : ℂ) :
    |complexEnergyPair z w| ≤ 2 * ‖z‖ * ‖w‖ := by
  unfold complexEnergyPair
  rw [abs_mul]
  have hre := Complex.abs_re_le_norm (inner ℂ z w)
  calc
    |(2 : ℝ)| * |(inner ℂ z w).re| ≤
        2 * ‖inner ℂ z w‖ := by
      norm_num
      exact mul_le_mul_of_nonneg_left hre (by norm_num)
    _ ≤ 2 * (‖z‖ * ‖w‖) := by
      exact mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _)
        (by norm_num)

lemma complexEnergyPair_sub_expansion (z w a b : ℂ) :
    complexEnergyPair z w - complexEnergyPair a b =
      complexEnergyPair (z - a) b +
        complexEnergyPair a (w - b) +
        complexEnergyPair (z - a) (w - b) := by
  unfold complexEnergyPair
  simp only [inner_sub_left, inner_sub_right, map_sub, map_add,
    mul_add, add_mul]
  ring

/-- Bilinear perturbation estimate for the first real energy jet. -/
lemma abs_complexEnergyPair_sub_le_of_norm_sub_le
    (z w a b : ℂ) (e₀ e₁ : ℝ)
    (he₀ : 0 ≤ e₀) (he₁ : 0 ≤ e₁)
    (hz : ‖z - a‖ ≤ e₀) (hw : ‖w - b‖ ≤ e₁) :
    |complexEnergyPair z w - complexEnergyPair a b| ≤
      2 * (‖a‖ * e₁ + ‖b‖ * e₀ + e₀ * e₁) := by
  rw [complexEnergyPair_sub_expansion]
  calc
    |complexEnergyPair (z - a) b +
        complexEnergyPair a (w - b) +
        complexEnergyPair (z - a) (w - b)| ≤
        |complexEnergyPair (z - a) b| +
          |complexEnergyPair a (w - b)| +
          |complexEnergyPair (z - a) (w - b)| := by
      calc
        |complexEnergyPair (z - a) b +
            complexEnergyPair a (w - b) +
            complexEnergyPair (z - a) (w - b)| ≤
            |complexEnergyPair (z - a) b +
              complexEnergyPair a (w - b)| +
              |complexEnergyPair (z - a) (w - b)| :=
          abs_add_le _ _
        _ ≤ |complexEnergyPair (z - a) b| +
              |complexEnergyPair a (w - b)| +
              |complexEnergyPair (z - a) (w - b)| := by
          exact add_le_add_right (abs_add_le _ _) _
    _ ≤ 2 * ‖z - a‖ * ‖b‖ +
          2 * ‖a‖ * ‖w - b‖ +
          2 * ‖z - a‖ * ‖w - b‖ := by
      gcongr
      · exact abs_complexEnergyPair_le _ _
      · exact abs_complexEnergyPair_le _ _
      · exact abs_complexEnergyPair_le _ _
    _ ≤ 2 * (‖a‖ * e₁ + ‖b‖ * e₀ + e₀ * e₁) := by
      have hzb : 0 ≤ ‖b‖ := norm_nonneg _
      have hza : 0 ≤ ‖a‖ := norm_nonneg _
      have h₁ := mul_le_mul_of_nonneg_right hz hzb
      have h₂ := mul_le_mul_of_nonneg_left hw hza
      have h₃ := mul_le_mul hz hw (norm_nonneg _) he₁
      nlinarith

/-- Hessian perturbation estimate obtained by applying the same bilinear
estimate to the `z z''` channel and to the self-pairing of `z'`. -/
lemma abs_complexEnergyHessianPair_sub_le_of_norm_sub_le
    (z z' z'' a a' a'' : ℂ) (e₀ e₁ e₂ : ℝ)
    (he₀ : 0 ≤ e₀) (he₁ : 0 ≤ e₁) (he₂ : 0 ≤ e₂)
    (hz : ‖z - a‖ ≤ e₀) (hz' : ‖z' - a'‖ ≤ e₁)
    (hz'' : ‖z'' - a''‖ ≤ e₂) :
    |complexEnergyHessianPair z z' z'' -
        complexEnergyHessianPair a a' a''| ≤
      2 * (‖a‖ * e₂ + ‖a''‖ * e₀ + e₀ * e₂ +
        2 * ‖a'‖ * e₁ + e₁ ^ 2) := by
  unfold complexEnergyHessianPair
  have hmain := abs_complexEnergyPair_sub_le_of_norm_sub_le
    z z'' a a'' e₀ e₂ he₀ he₂ hz hz''
  have hself := abs_complexEnergyPair_sub_le_of_norm_sub_le
    z' z' a' a' e₁ e₁ he₁ he₁ hz' hz'
  calc
    |complexEnergyPair z z'' + complexEnergyPair z' z' -
        (complexEnergyPair a a'' + complexEnergyPair a' a')| ≤
        |complexEnergyPair z z'' - complexEnergyPair a a''| +
          |complexEnergyPair z' z' - complexEnergyPair a' a'| := by
      have hrewrite :
          complexEnergyPair z z'' + complexEnergyPair z' z' -
              (complexEnergyPair a a'' + complexEnergyPair a' a') =
            (complexEnergyPair z z'' - complexEnergyPair a a'') +
              (complexEnergyPair z' z' - complexEnergyPair a' a') := by
        ring
      rw [hrewrite]
      exact abs_add_le _ _
    _ ≤ 2 * (‖a‖ * e₂ + ‖a''‖ * e₀ + e₀ * e₂) +
          2 * (‖a'‖ * e₁ + ‖a'‖ * e₁ + e₁ * e₁) :=
      add_le_add hmain hself
    _ = 2 * (‖a‖ * e₂ + ‖a''‖ * e₀ + e₀ * e₂ +
        2 * ‖a'‖ * e₁ + e₁ ^ 2) := by ring

/-! ## Differentiating the complex norm square -/

lemma hasDerivAt_complexNormSq
    {F : ℝ → ℂ} {F' : ℂ} (time : ℝ)
    (hF : HasDerivAt F F' time) :
    HasDerivAt (fun u : ℝ => Complex.normSq (F u))
      (complexEnergyPair (F time) F') time := by
  have hre :=
    (Complex.reCLM.hasFDerivAt.comp_hasDerivAt time hF).hasDerivAt
  have him :=
    (Complex.imCLM.hasFDerivAt.comp_hasDerivAt time hF).hasDerivAt
  have hsum := (hre.mul hre).add (him.mul him)
  simpa [Complex.normSq_apply, complexEnergyPair,
    RCLike.inner_apply', Complex.mul_re, Complex.conj_re,
    Complex.conj_im] using hsum

lemma hasDerivAt_complexEnergyPair
    {F G : ℝ → ℂ} {F' G' : ℂ} (time : ℝ)
    (hF : HasDerivAt F F' time) (hG : HasDerivAt G G' time) :
    HasDerivAt (fun u : ℝ => complexEnergyPair (F u) (G u))
      (complexEnergyPair F' (G time) +
        complexEnergyPair (F time) G') time := by
  have hFRe :=
    (Complex.reCLM.hasFDerivAt.comp_hasDerivAt time hF).hasDerivAt
  have hFIm :=
    (Complex.imCLM.hasFDerivAt.comp_hasDerivAt time hF).hasDerivAt
  have hGRe :=
    (Complex.reCLM.hasFDerivAt.comp_hasDerivAt time hG).hasDerivAt
  have hGIm :=
    (Complex.imCLM.hasFDerivAt.comp_hasDerivAt time hG).hasDerivAt
  have hsum := (hFRe.mul hGRe).add (hFIm.mul hGIm)
  simpa [complexEnergyPair, RCLike.inner_apply', Complex.mul_re,
    Complex.conj_re, Complex.conj_im] using hsum

lemma hasDerivAt_complexEnergyHessian
    {F F' : ℝ → ℂ} {F'' : ℂ} (time : ℝ)
    (hF : HasDerivAt F (F' time) time)
    (hF' : HasDerivAt F' F'' time) :
    HasDerivAt (fun u : ℝ => complexEnergyPair (F u) (F' u))
      (complexEnergyHessianPair (F time) (F' time) F'') time := by
  have hpair := hasDerivAt_complexEnergyPair time hF hF'
  simpa [complexEnergyHessianPair, complexEnergyPair_self, add_comm,
    add_left_comm, add_assoc] using hpair

/-! ## Exact phase cancellation

These are the two identities which prevent the factor `log M` from entering
the normalized energy remainder.  The cancellation is proved at the level of
the real pairing, rather than inferred from a complex asymptotic. -/

lemma complexEnergyPair_phase_cancel (a : ℂ) (L : ℝ) :
    complexEnergyPair a (-((L : ℂ) * Complex.I) * a) = 0 := by
  unfold complexEnergyPair
  rw [RCLike.inner_apply']
  simp [Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im]
  ring

lemma complexEnergyHessianPair_phase_cancel (a : ℂ) (L : ℝ) :
    complexEnergyHessianPair a
        (-((L : ℂ) * Complex.I) * a)
        (-((L : ℂ) ^ 2) * a) = 0 := by
  unfold complexEnergyHessianPair complexEnergyPair
  rw [RCLike.inner_apply']
  simp [Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im, Complex.sq_norm]
  ring

/-! ## Concrete leading coefficient and tail paths -/

/-- The leading collective energy coefficient, also denoted `‖A(t)‖²`. -/
def empiricalLeadingCollectiveCoefficientEnergy (time : ℝ) : ℝ :=
  empiricalNativeTailCoefficientNormSq time

/-- First derivative channel of the scaled collective tail energy. -/
def empiricalScaledCollectiveCutoffTailEnergyFirst
    (M : ℕ) (time : ℝ) : ℝ :=
  ∑ camera : EmpiricalCamera,
    complexEnergyPair
      (empiricalScaledCameraCutoffTail camera M time)
      (empiricalScaledCameraCutoffTailCriticalFirst camera M time)

/-- Second derivative channel of the scaled collective tail energy. -/
def empiricalScaledCollectiveCutoffTailEnergySecond
    (M : ℕ) (time : ℝ) : ℝ :=
  ∑ camera : EmpiricalCamera,
    complexEnergyHessianPair
      (empiricalScaledCameraCutoffTail camera M time)
      (empiricalScaledCameraCutoffTailCriticalFirst camera M time)
      (empiricalScaledCameraCutoffTailCriticalSecond camera M time)

/-- First derivative channel of the leading coefficient energy. -/
def empiricalLeadingCollectiveCoefficientEnergyFirst (time : ℝ) : ℝ :=
  ∑ camera : EmpiricalCamera,
    complexEnergyPair
      (empiricalNativeTailCoefficientCritical camera time)
      (empiricalNativeTailCoefficientCriticalFirst camera time)

/-- Second derivative channel of the leading coefficient energy. -/
def empiricalLeadingCollectiveCoefficientEnergySecond (time : ℝ) : ℝ :=
  ∑ camera : EmpiricalCamera,
    complexEnergyHessianPair
      (empiricalNativeTailCoefficientCritical camera time)
      (empiricalNativeTailCoefficientCriticalFirst camera time)
      (empiricalNativeTailCoefficientCriticalSecond camera time)

lemma hasDerivAt_empiricalLeadingCollectiveCoefficientEnergy
    (time : ℝ) :
    HasDerivAt empiricalLeadingCollectiveCoefficientEnergy
      (empiricalLeadingCollectiveCoefficientEnergyFirst time) time := by
  classical
  unfold empiricalLeadingCollectiveCoefficientEnergy
    empiricalLeadingCollectiveCoefficientEnergyFirst
  apply HasDerivAt.fun_sum
  intro camera _hcamera
  have hC := hasDerivAt_criticalLine_of_analytic
    (empiricalNativeTailCoefficient camera) time
    (analyticAt_empiricalNativeTailCoefficient_critical camera time)
  have hC' := hasDerivAt_criticalLine_firstJet_of_analytic
    (empiricalNativeTailCoefficient camera) time
    (analyticAt_empiricalNativeTailCoefficient_critical camera time)
  simpa [empiricalNativeTailCoefficientCritical,
    empiricalNativeTailCoefficientCriticalFirst] using
    hasDerivAt_complexNormSq time hC

lemma hasDerivAt_empiricalLeadingCollectiveCoefficientEnergyFirst
    (time : ℝ) :
    HasDerivAt empiricalLeadingCollectiveCoefficientEnergyFirst
      (empiricalLeadingCollectiveCoefficientEnergySecond time) time := by
  classical
  unfold empiricalLeadingCollectiveCoefficientEnergyFirst
    empiricalLeadingCollectiveCoefficientEnergySecond
  apply HasDerivAt.fun_sum
  intro camera _hcamera
  have hC := hasDerivAt_criticalLine_of_analytic
    (empiricalNativeTailCoefficient camera) time
    (analyticAt_empiricalNativeTailCoefficient_critical camera time)
  have hC' := hasDerivAt_criticalLine_firstJet_of_analytic
    (empiricalNativeTailCoefficient camera) time
    (analyticAt_empiricalNativeTailCoefficient_critical camera time)
  simpa [empiricalNativeTailCoefficientCritical,
    empiricalNativeTailCoefficientCriticalFirst,
    empiricalNativeTailCoefficientCriticalSecond] using
    hasDerivAt_complexEnergyHessian time hC hC'

lemma empiricalLeadingCollectiveCoefficientEnergy_eq_quadratic (time : ℝ) :
    empiricalLeadingCollectiveCoefficientEnergy time =
      (1 / 4 + time ^ 2) * ((132244271 : ℝ) / 1778112000) := by
  unfold empiricalLeadingCollectiveCoefficientEnergy
  rw [empiricalNativeTailCoefficientNormSq_eq]
  norm_num [criticalLineParameter, Complex.sq_norm,
    Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im]
  ring

lemma empiricalLeadingCollectiveCoefficientEnergyFirst_eq (time : ℝ) :
    empiricalLeadingCollectiveCoefficientEnergyFirst time =
      2 * time * ((132244271 : ℝ) / 1778112000) := by
  have hsum := hasDerivAt_empiricalLeadingCollectiveCoefficientEnergy time
  have hquad : HasDerivAt
      (fun u : ℝ =>
        (1 / 4 + u ^ 2) * ((132244271 : ℝ) / 1778112000))
      (2 * time * ((132244271 : ℝ) / 1778112000)) time := by
    have hid := hasDerivAt_id time
    have hsq := hid.mul hid
    have hconst := hasDerivAt_const time (1 / 4 : ℝ)
    have hsum' := hconst.add hsq
    have hscaled := hsum'.mul_const
      ((132244271 : ℝ) / 1778112000)
    simpa [pow_two] using hscaled
  have hEq : empiricalLeadingCollectiveCoefficientEnergy =
      (fun u : ℝ =>
        (1 / 4 + u ^ 2) * ((132244271 : ℝ) / 1778112000)) := by
    funext u
    exact empiricalLeadingCollectiveCoefficientEnergy_eq_quadratic u
  have hlead := hquad.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun u => congrFun hEq u).symm)
  exact hsum.deriv.symm.trans hlead.deriv

lemma empiricalLeadingCollectiveCoefficientEnergySecond_eq (time : ℝ) :
    empiricalLeadingCollectiveCoefficientEnergySecond time =
      2 * ((132244271 : ℝ) / 1778112000) := by
  have hsum := hasDerivAt_empiricalLeadingCollectiveCoefficientEnergyFirst time
  have hquad : HasDerivAt
      (fun u : ℝ =>
        2 * u * ((132244271 : ℝ) / 1778112000))
      (2 * ((132244271 : ℝ) / 1778112000)) time := by
    have hid := hasDerivAt_id time
    have hscaled := hid.mul_const
      (2 * ((132244271 : ℝ) / 1778112000))
    simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled
  have hEq : empiricalLeadingCollectiveCoefficientEnergyFirst =
      (fun u : ℝ =>
        2 * u * ((132244271 : ℝ) / 1778112000)) := by
    funext u
    exact empiricalLeadingCollectiveCoefficientEnergyFirst_eq u
  have hlead := hquad.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun u => congrFun hEq u).symm)
  exact hsum.deriv.symm.trans hlead.deriv

/-! ## Camera-wise and collective real jets -/

lemma hasDerivAt_empiricalScaledCameraCutoffTailEnergy
    (camera : EmpiricalCamera) (M : ℕ) (hM : 1 ≤ M) (time : ℝ) :
    HasDerivAt
      (fun u : ℝ =>
        Complex.normSq (empiricalScaledCameraCutoffTail camera M u))
      (complexEnergyPair
        (empiricalScaledCameraCutoffTail camera M time)
        (empiricalScaledCameraCutoffTailCriticalFirst camera M time)) time := by
  exact hasDerivAt_complexNormSq time
    (hasDerivAt_empiricalScaledCameraCutoffTail_critical camera M hM time)

lemma hasDerivAt_empiricalScaledCameraCutoffTailEnergyFirst
    (camera : EmpiricalCamera) (M : ℕ) (hM : 1 ≤ M) (time : ℝ) :
    HasDerivAt
      (fun u : ℝ =>
        complexEnergyPair
          (empiricalScaledCameraCutoffTail camera M u)
          (empiricalScaledCameraCutoffTailCriticalFirst camera M u))
      (complexEnergyHessianPair
        (empiricalScaledCameraCutoffTail camera M time)
        (empiricalScaledCameraCutoffTailCriticalFirst camera M time)
        (empiricalScaledCameraCutoffTailCriticalSecond camera M time)) time := by
  exact hasDerivAt_complexEnergyHessian time
    (hasDerivAt_empiricalScaledCameraCutoffTail_critical camera M hM time)
    (hasDerivAt_empiricalScaledCameraCutoffTail_critical_firstJet
      camera M hM time)

lemma hasDerivAt_empiricalScaledCollectiveCutoffTailEnergy
    (M : ℕ) (hM : 1 ≤ M) (time : ℝ) :
    HasDerivAt (fun u : ℝ => empiricalScaledCollectiveCutoffTailEnergy M u)
      (empiricalScaledCollectiveCutoffTailEnergyFirst M time) time := by
  classical
  unfold empiricalScaledCollectiveCutoffTailEnergy
    empiricalScaledCollectiveCutoffTailEnergyFirst
  apply HasDerivAt.fun_sum
  intro camera _hcamera
  simpa [Complex.sq_norm] using
    hasDerivAt_empiricalScaledCameraCutoffTailEnergy camera M hM time

lemma hasDerivAt_empiricalScaledCollectiveCutoffTailEnergyFirst
    (M : ℕ) (hM : 1 ≤ M) (time : ℝ) :
    HasDerivAt (fun u : ℝ => empiricalScaledCollectiveCutoffTailEnergyFirst M u)
      (empiricalScaledCollectiveCutoffTailEnergySecond M time) time := by
  classical
  unfold empiricalScaledCollectiveCutoffTailEnergyFirst
    empiricalScaledCollectiveCutoffTailEnergySecond
  apply HasDerivAt.fun_sum
  intro camera _hcamera
  exact hasDerivAt_empiricalScaledCameraCutoffTailEnergyFirst camera M hM time

/-! ## Explicit `1/M` remainder ledger

The Cauchy estimates are now used only through three constants.  They are
independent of the cutoff; the named radius remains in the definitions so the
source of the numerical factors is auditable.  The displayed bounds retain
the harmless quadratic `M⁻²` term instead of silently absorbing it. -/

/-- Value-jet constant for one camera (the coefficient of `1/M`). -/
def empiricalScaledCameraTailValueJetConstant
    (camera : EmpiricalCamera) (time : ℝ) : ℝ :=
  empiricalScaledCameraTailCauchyConstant camera time

/-- First-jet constant for one camera (the coefficient of `1/M`). -/
def empiricalScaledCameraTailFirstJetConstant
    (camera : EmpiricalCamera) (time : ℝ) : ℝ :=
  empiricalScaledCameraTailCauchyConstant camera time /
    nativeExplicitRadiusCriticalCauchyRadius

/-- Second-jet constant for one camera (the coefficient of `1/M`). -/
def empiricalScaledCameraTailSecondJetConstant
    (camera : EmpiricalCamera) (time : ℝ) : ℝ :=
  2 * empiricalScaledCameraTailCauchyConstant camera time /
    nativeExplicitRadiusCriticalCauchyRadius ^ 2

lemma empiricalScaledCameraTailValueJetConstant_nonneg
    (camera : EmpiricalCamera) (time : ℝ) :
    0 ≤ empiricalScaledCameraTailValueJetConstant camera time := by
  exact empiricalScaledCameraTailCauchyConstant_nonneg camera time

lemma empiricalScaledCameraTailFirstJetConstant_nonneg
    (camera : EmpiricalCamera) (time : ℝ) :
    0 ≤ empiricalScaledCameraTailFirstJetConstant camera time := by
  unfold empiricalScaledCameraTailFirstJetConstant
  exact div_nonneg
    (empiricalScaledCameraTailCauchyConstant_nonneg camera time)
    (by positivity)

lemma empiricalScaledCameraTailSecondJetConstant_nonneg
    (camera : EmpiricalCamera) (time : ℝ) :
    0 ≤ empiricalScaledCameraTailSecondJetConstant camera time := by
  unfold empiricalScaledCameraTailSecondJetConstant
  exact div_nonneg
    (mul_nonneg (by norm_num)
      (empiricalScaledCameraTailCauchyConstant_nonneg camera time))
    (by positivity)

/-- Linear part of the first derivative remainder. -/
def empiricalCollectiveEnergyFirstDerivativeLinearConstant
    (time : ℝ) : ℝ :=
  ∑ camera : EmpiricalCamera,
    2 * (‖empiricalNativeTailCoefficientCritical camera time‖ *
          empiricalScaledCameraTailFirstJetConstant camera time +
        ‖empiricalNativeTailCoefficientCriticalFirst camera time‖ *
          empiricalScaledCameraTailValueJetConstant camera time)

/-- Quadratic part of the first derivative remainder. -/
def empiricalCollectiveEnergyFirstDerivativeQuadraticConstant
    (time : ℝ) : ℝ :=
  ∑ camera : EmpiricalCamera,
    2 * (empiricalScaledCameraTailValueJetConstant camera time *
      empiricalScaledCameraTailFirstJetConstant camera time)

/-- Total first derivative constant, with the `M⁻²` term absorbed using
`M ≥ 1` when desired. -/
def empiricalCollectiveEnergyFirstDerivativeConstant (time : ℝ) : ℝ :=
  empiricalCollectiveEnergyFirstDerivativeLinearConstant time +
    empiricalCollectiveEnergyFirstDerivativeQuadraticConstant time

/-- Linear part of the second derivative remainder. -/
def empiricalCollectiveEnergySecondDerivativeLinearConstant
    (time : ℝ) : ℝ :=
  ∑ camera : EmpiricalCamera,
    2 * (‖empiricalNativeTailCoefficientCritical camera time‖ *
          empiricalScaledCameraTailSecondJetConstant camera time +
        ‖empiricalNativeTailCoefficientCriticalSecond camera time‖ *
          empiricalScaledCameraTailValueJetConstant camera time +
        2 * ‖empiricalNativeTailCoefficientCriticalFirst camera time‖ *
          empiricalScaledCameraTailFirstJetConstant camera time)

/-- Quadratic part of the second derivative remainder. -/
def empiricalCollectiveEnergySecondDerivativeQuadraticConstant
    (time : ℝ) : ℝ :=
  ∑ camera : EmpiricalCamera,
    2 * (empiricalScaledCameraTailValueJetConstant camera time *
          empiricalScaledCameraTailSecondJetConstant camera time +
        empiricalScaledCameraTailFirstJetConstant camera time ^ 2)

/-- Total second derivative constant, with the `M⁻²` term absorbed using
`M ≥ 1` when desired. -/
def empiricalCollectiveEnergySecondDerivativeConstant (time : ℝ) : ℝ :=
  empiricalCollectiveEnergySecondDerivativeLinearConstant time +
    empiricalCollectiveEnergySecondDerivativeQuadraticConstant time

lemma norm_empiricalScaledCameraTailErrorCritical_value_le_constant_div
    (camera : EmpiricalCamera) (M : ℕ) (hM : 1 ≤ M) (time : ℝ) :
    ‖empiricalScaledCameraTailErrorCritical camera M time‖ ≤
      empiricalScaledCameraTailValueJetConstant camera time / (M : ℝ) := by
  simpa [empiricalScaledCameraTailValueJetConstant] using
    norm_empiricalScaledCameraTailError_critical_value_le camera M hM time

lemma norm_empiricalScaledCameraTailErrorCritical_first_le_constant_div
    (camera : EmpiricalCamera) (M : ℕ) (hM : 1 ≤ M) (time : ℝ) :
    ‖empiricalScaledCameraTailErrorCriticalFirst camera M time‖ ≤
      empiricalScaledCameraTailFirstJetConstant camera time / (M : ℝ) := by
  simpa [empiricalScaledCameraTailFirstJetConstant] using
    norm_empiricalScaledCameraTailErrorCriticalFirst_le camera M hM time

lemma norm_empiricalScaledCameraTailErrorCritical_second_le_constant_div
    (camera : EmpiricalCamera) (M : ℕ) (hM : 1 ≤ M) (time : ℝ) :
    ‖empiricalScaledCameraTailErrorCriticalSecond camera M time‖ ≤
      empiricalScaledCameraTailSecondJetConstant camera time / (M : ℝ) := by
  simpa [empiricalScaledCameraTailSecondJetConstant] using
    norm_empiricalScaledCameraTailErrorCriticalSecond_le camera M hM time

lemma empiricalScaledCameraTailEnergyFirst_remainder_le
    (camera : EmpiricalCamera) (M : ℕ) (hM : 1 ≤ M) (time : ℝ) :
    |complexEnergyPair
        (empiricalScaledCameraCutoffTail camera M time)
        (empiricalScaledCameraCutoffTailCriticalFirst camera M time) -
      complexEnergyPair
        (empiricalNativeTailCoefficientCritical camera time)
        (empiricalNativeTailCoefficientCriticalFirst camera time)| ≤
      2 * (‖empiricalNativeTailCoefficientCritical camera time‖ *
          (empiricalScaledCameraTailFirstJetConstant camera time / (M : ℝ)) +
        ‖empiricalNativeTailCoefficientCriticalFirst camera time‖ *
          (empiricalScaledCameraTailValueJetConstant camera time / (M : ℝ)) +
        (empiricalScaledCameraTailValueJetConstant camera time / (M : ℝ)) *
          (empiricalScaledCameraTailFirstJetConstant camera time / (M : ℝ))) := by
  have h0 : ‖empiricalScaledCameraCutoffTail camera M time -
      empiricalNativeTailCoefficientCritical camera time‖ ≤
      empiricalScaledCameraTailValueJetConstant camera time / (M : ℝ) := by
    change ‖empiricalScaledCameraTailErrorCritical camera M time‖ ≤ _
    exact norm_empiricalScaledCameraTailErrorCritical_value_le_constant_div
      camera M hM time
  have h1 : ‖empiricalScaledCameraCutoffTailCritical camera M time -
      empiricalNativeTailCoefficientCriticalFirst camera time‖ ≤
      empiricalScaledCameraTailFirstJetConstant camera time / (M : ℝ) := by
    change ‖empiricalScaledCameraTailErrorCriticalFirst camera M time‖ ≤ _
    exact norm_empiricalScaledCameraTailErrorCritical_first_le_constant_div
      camera M hM time
  have he0 : 0 ≤ empiricalScaledCameraTailValueJetConstant camera time /
      (M : ℝ) := by positivity
  have he1 : 0 ≤ empiricalScaledCameraTailFirstJetConstant camera time /
      (M : ℝ) := by positivity
  exact abs_complexEnergyPair_sub_le_of_norm_sub_le
    (empiricalScaledCameraCutoffTail camera M time)
    (empiricalScaledCameraCutoffTailCriticalFirst camera M time)
    (empiricalNativeTailCoefficientCritical camera time)
    (empiricalNativeTailCoefficientCriticalFirst camera time)
    (empiricalScaledCameraTailValueJetConstant camera time / (M : ℝ))
    (empiricalScaledCameraTailFirstJetConstant camera time / (M : ℝ))
    he0 he1 h0 h1

lemma empiricalScaledCameraTailEnergySecond_remainder_le
    (camera : EmpiricalCamera) (M : ℕ) (hM : 1 ≤ M) (time : ℝ) :
    |complexEnergyHessianPair
        (empiricalScaledCameraCutoffTail camera M time)
        (empiricalScaledCameraCutoffTailCriticalFirst camera M time)
        (empiricalScaledCameraCutoffTailCriticalSecond camera M time) -
      complexEnergyHessianPair
        (empiricalNativeTailCoefficientCritical camera time)
        (empiricalNativeTailCoefficientCriticalFirst camera time)
        (empiricalNativeTailCoefficientCriticalSecond camera time)| ≤
      2 * (‖empiricalNativeTailCoefficientCritical camera time‖ *
          (empiricalScaledCameraTailSecondJetConstant camera time / (M : ℝ)) +
        ‖empiricalNativeTailCoefficientCriticalSecond camera time‖ *
          (empiricalScaledCameraTailValueJetConstant camera time / (M : ℝ)) +
        (empiricalScaledCameraTailValueJetConstant camera time / (M : ℝ)) *
          (empiricalScaledCameraTailSecondJetConstant camera time / (M : ℝ)) +
        2 * ‖empiricalNativeTailCoefficientCriticalFirst camera time‖ *
          (empiricalScaledCameraTailFirstJetConstant camera time / (M : ℝ)) +
        (empiricalScaledCameraTailFirstJetConstant camera time / (M : ℝ)) ^ 2) := by
  have h0 : ‖empiricalScaledCameraCutoffTail camera M time -
      empiricalNativeTailCoefficientCritical camera time‖ ≤
      empiricalScaledCameraTailValueJetConstant camera time / (M : ℝ) := by
    change ‖empiricalScaledCameraTailErrorCritical camera M time‖ ≤ _
    exact norm_empiricalScaledCameraTailErrorCritical_value_le_constant_div
      camera M hM time
  have h1 : ‖empiricalScaledCameraCutoffTailCritical camera M time -
      empiricalNativeTailCoefficientCriticalFirst camera time‖ ≤
      empiricalScaledCameraTailFirstJetConstant camera time / (M : ℝ) := by
    change ‖empiricalScaledCameraTailErrorCriticalFirst camera M time‖ ≤ _
    exact norm_empiricalScaledCameraTailErrorCritical_first_le_constant_div
      camera M hM time
  have h2 : ‖empiricalScaledCameraCutoffTailCriticalSecond camera M time -
      empiricalNativeTailCoefficientCriticalSecond camera time‖ ≤
      empiricalScaledCameraTailSecondJetConstant camera time / (M : ℝ) := by
    change ‖empiricalScaledCameraTailErrorCriticalSecond camera M time‖ ≤ _
    exact norm_empiricalScaledCameraTailErrorCritical_second_le_constant_div
      camera M hM time
  have he0 : 0 ≤ empiricalScaledCameraTailValueJetConstant camera time /
      (M : ℝ) := by positivity
  have he1 : 0 ≤ empiricalScaledCameraTailFirstJetConstant camera time /
      (M : ℝ) := by positivity
  have he2 : 0 ≤ empiricalScaledCameraTailSecondJetConstant camera time /
      (M : ℝ) := by positivity
  exact abs_complexEnergyHessianPair_sub_le_of_norm_sub_le
    (empiricalScaledCameraCutoffTail camera M time)
    (empiricalScaledCameraCutoffTailCriticalFirst camera M time)
    (empiricalScaledCameraCutoffTailCriticalSecond camera M time)
    (empiricalNativeTailCoefficientCritical camera time)
    (empiricalNativeTailCoefficientCriticalFirst camera time)
    (empiricalNativeTailCoefficientCriticalSecond camera time)
    (empiricalScaledCameraTailValueJetConstant camera time / (M : ℝ))
    (empiricalScaledCameraTailFirstJetConstant camera time / (M : ℝ))
    (empiricalScaledCameraTailSecondJetConstant camera time / (M : ℝ))
    he0 he1 he2 h0 h1 h2

theorem deriv_empiricalScaledCollectiveCutoffTailEnergy_eq
    (M : ℕ) (hM : 1 ≤ M) (time : ℝ) :
    deriv (fun u : ℝ => empiricalScaledCollectiveCutoffTailEnergy M u) time =
      empiricalScaledCollectiveCutoffTailEnergyFirst M time := by
  exact (hasDerivAt_empiricalScaledCollectiveCutoffTailEnergy M hM time).deriv

theorem deriv_empiricalScaledCollectiveCutoffTailEnergyFirst_eq
    (M : ℕ) (hM : 1 ≤ M) (time : ℝ) :
    deriv (fun u : ℝ => empiricalScaledCollectiveCutoffTailEnergyFirst M u) time =
      empiricalScaledCollectiveCutoffTailEnergySecond M time := by
  exact
    (hasDerivAt_empiricalScaledCollectiveCutoffTailEnergyFirst M hM time).deriv

theorem abs_empiricalScaledCollectiveCutoffTailEnergyFirst_sub_le
    (M : ℕ) (hM : 1 ≤ M) (time : ℝ) :
    |empiricalScaledCollectiveCutoffTailEnergyFirst M time -
        empiricalLeadingCollectiveCoefficientEnergyFirst time| ≤
      empiricalCollectiveEnergyFirstDerivativeLinearConstant time /
          (M : ℝ) +
        empiricalCollectiveEnergyFirstDerivativeQuadraticConstant time /
          (M : ℝ) ^ 2 := by
  classical
  unfold empiricalScaledCollectiveCutoffTailEnergyFirst
    empiricalLeadingCollectiveCoefficientEnergyFirst
  have hcomponent : ∀ camera : EmpiricalCamera,
      |complexEnergyPair
          (empiricalScaledCameraCutoffTail camera M time)
          (empiricalScaledCameraCutoffTailCriticalFirst camera M time) -
        complexEnergyPair
          (empiricalNativeTailCoefficientCritical camera time)
          (empiricalNativeTailCoefficientCriticalFirst camera time)| ≤
        2 * (‖empiricalNativeTailCoefficientCritical camera time‖ *
            (empiricalScaledCameraTailFirstJetConstant camera time / (M : ℝ)) +
          ‖empiricalNativeTailCoefficientCriticalFirst camera time‖ *
            (empiricalScaledCameraTailValueJetConstant camera time / (M : ℝ)) +
          (empiricalScaledCameraTailValueJetConstant camera time / (M : ℝ)) *
            (empiricalScaledCameraTailFirstJetConstant camera time / (M : ℝ)) := by
    intro camera
    exact empiricalScaledCameraTailEnergyFirst_remainder_le camera M hM time
  calc
    |(∑ camera : EmpiricalCamera,
        complexEnergyPair
          (empiricalScaledCameraCutoffTail camera M time)
          (empiricalScaledCameraCutoffTailCriticalFirst camera M time)) -
        ∑ camera : EmpiricalCamera,
          complexEnergyPair
            (empiricalNativeTailCoefficientCritical camera time)
            (empiricalNativeTailCoefficientCriticalFirst camera time)| =
      |∑ camera : EmpiricalCamera,
        (complexEnergyPair
            (empiricalScaledCameraCutoffTail camera M time)
            (empiricalScaledCameraCutoffTailCriticalFirst camera M time) -
          complexEnergyPair
            (empiricalNativeTailCoefficientCritical camera time)
            (empiricalNativeTailCoefficientCriticalFirst camera time))| := by
        rw [Finset.sum_sub_distrib]
    _ ≤ ∑ camera : EmpiricalCamera,
        |complexEnergyPair
            (empiricalScaledCameraCutoffTail camera M time)
            (empiricalScaledCameraCutoffTailCriticalFirst camera M time) -
          complexEnergyPair
            (empiricalNativeTailCoefficientCritical camera time)
            (empiricalNativeTailCoefficientCriticalFirst camera time)| := by
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ camera : EmpiricalCamera,
        2 * (‖empiricalNativeTailCoefficientCritical camera time‖ *
            (empiricalScaledCameraTailFirstJetConstant camera time / (M : ℝ)) +
          ‖empiricalNativeTailCoefficientCriticalFirst camera time‖ *
            (empiricalScaledCameraTailValueJetConstant camera time / (M : ℝ)) +
          (empiricalScaledCameraTailValueJetConstant camera time / (M : ℝ)) *
            (empiricalScaledCameraTailFirstJetConstant camera time / (M : ℝ))) := by
        exact Finset.sum_le_sum (fun camera _hcamera => hcomponent camera)
    _ = empiricalCollectiveEnergyFirstDerivativeLinearConstant time /
          (M : ℝ) +
        empiricalCollectiveEnergyFirstDerivativeQuadraticConstant time /
          (M : ℝ) ^ 2 := by
        simp only [empiricalCollectiveEnergyFirstDerivativeLinearConstant,
          empiricalCollectiveEnergyFirstDerivativeQuadraticConstant,
          Finset.sum_add_distrib, div_eq_mul_inv]
        ring

theorem abs_empiricalScaledCollectiveCutoffTailEnergySecond_sub_le
    (M : ℕ) (hM : 1 ≤ M) (time : ℝ) :
    |empiricalScaledCollectiveCutoffTailEnergySecond M time -
        empiricalLeadingCollectiveCoefficientEnergySecond time| ≤
      empiricalCollectiveEnergySecondDerivativeLinearConstant time /
          (M : ℝ) +
        empiricalCollectiveEnergySecondDerivativeQuadraticConstant time /
          (M : ℝ) ^ 2 := by
  classical
  unfold empiricalScaledCollectiveCutoffTailEnergySecond
    empiricalLeadingCollectiveCoefficientEnergySecond
  have hcomponent : ∀ camera : EmpiricalCamera,
      |complexEnergyHessianPair
          (empiricalScaledCameraCutoffTail camera M time)
          (empiricalScaledCameraCutoffTailCriticalFirst camera M time)
          (empiricalScaledCameraCutoffTailCriticalSecond camera M time) -
        complexEnergyHessianPair
          (empiricalNativeTailCoefficientCritical camera time)
          (empiricalNativeTailCoefficientCriticalFirst camera time)
          (empiricalNativeTailCoefficientCriticalSecond camera time)| ≤
        2 * (‖empiricalNativeTailCoefficientCritical camera time‖ *
            (empiricalScaledCameraTailSecondJetConstant camera time / (M : ℝ)) +
          ‖empiricalNativeTailCoefficientCriticalSecond camera time‖ *
            (empiricalScaledCameraTailValueJetConstant camera time / (M : ℝ)) +
          (empiricalScaledCameraTailValueJetConstant camera time / (M : ℝ)) *
            (empiricalScaledCameraTailSecondJetConstant camera time / (M : ℝ)) +
          2 * ‖empiricalNativeTailCoefficientCriticalFirst camera time‖ *
            (empiricalScaledCameraTailFirstJetConstant camera time / (M : ℝ)) +
          (empiricalScaledCameraTailFirstJetConstant camera time / (M : ℝ)) ^ 2) := by
    intro camera
    exact empiricalScaledCameraTailEnergySecond_remainder_le camera M hM time
  calc
    |(∑ camera : EmpiricalCamera,
        complexEnergyHessianPair
          (empiricalScaledCameraCutoffTail camera M time)
          (empiricalScaledCameraCutoffTailCriticalFirst camera M time)
          (empiricalScaledCameraCutoffTailCriticalSecond camera M time)) -
        ∑ camera : EmpiricalCamera,
          complexEnergyHessianPair
            (empiricalNativeTailCoefficientCritical camera time)
            (empiricalNativeTailCoefficientCriticalFirst camera time)
            (empiricalNativeTailCoefficientCriticalSecond camera time)| =
      |∑ camera : EmpiricalCamera,
        (complexEnergyHessianPair
            (empiricalScaledCameraCutoffTail camera M time)
            (empiricalScaledCameraCutoffTailCriticalFirst camera M time)
            (empiricalScaledCameraCutoffTailCriticalSecond camera M time) -
          complexEnergyHessianPair
            (empiricalNativeTailCoefficientCritical camera time)
            (empiricalNativeTailCoefficientCriticalFirst camera time)
            (empiricalNativeTailCoefficientCriticalSecond camera time))| := by
        rw [Finset.sum_sub_distrib]
    _ ≤ ∑ camera : EmpiricalCamera,
        |complexEnergyHessianPair
            (empiricalScaledCameraCutoffTail camera M time)
            (empiricalScaledCameraCutoffTailCriticalFirst camera M time)
            (empiricalScaledCameraCutoffTailCriticalSecond camera M time) -
          complexEnergyHessianPair
            (empiricalNativeTailCoefficientCritical camera time)
            (empiricalNativeTailCoefficientCriticalFirst camera time)
            (empiricalNativeTailCoefficientCriticalSecond camera time)| := by
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ camera : EmpiricalCamera,
        2 * (‖empiricalNativeTailCoefficientCritical camera time‖ *
            (empiricalScaledCameraTailSecondJetConstant camera time / (M : ℝ)) +
          ‖empiricalNativeTailCoefficientCriticalSecond camera time‖ *
            (empiricalScaledCameraTailValueJetConstant camera time / (M : ℝ)) +
          (empiricalScaledCameraTailValueJetConstant camera time / (M : ℝ)) *
            (empiricalScaledCameraTailSecondJetConstant camera time / (M : ℝ)) +
          2 * ‖empiricalNativeTailCoefficientCriticalFirst camera time‖ *
            (empiricalScaledCameraTailFirstJetConstant camera time / (M : ℝ)) +
          (empiricalScaledCameraTailFirstJetConstant camera time / (M : ℝ)) ^ 2) := by
        exact Finset.sum_le_sum (fun camera _hcamera => hcomponent camera)
    _ = empiricalCollectiveEnergySecondDerivativeLinearConstant time /
          (M : ℝ) +
        empiricalCollectiveEnergySecondDerivativeQuadraticConstant time /
          (M : ℝ) ^ 2 := by
        simp only [empiricalCollectiveEnergySecondDerivativeLinearConstant,
          empiricalCollectiveEnergySecondDerivativeQuadraticConstant,
          Finset.sum_add_distrib, div_eq_mul_inv]
        ring

lemma empiricalCollectiveEnergyFirstDerivativeQuadraticConstant_nonneg
    (time : ℝ) :
    0 ≤ empiricalCollectiveEnergyFirstDerivativeQuadraticConstant time := by
  unfold empiricalCollectiveEnergyFirstDerivativeQuadraticConstant
  apply Finset.sum_nonneg
  intro camera _hcamera
  have h0 := empiricalScaledCameraTailValueJetConstant_nonneg camera time
  have h1 := empiricalScaledCameraTailFirstJetConstant_nonneg camera time
  positivity

lemma empiricalCollectiveEnergySecondDerivativeQuadraticConstant_nonneg
    (time : ℝ) :
    0 ≤ empiricalCollectiveEnergySecondDerivativeQuadraticConstant time := by
  unfold empiricalCollectiveEnergySecondDerivativeQuadraticConstant
  apply Finset.sum_nonneg
  intro camera _hcamera
  have h0 := empiricalScaledCameraTailValueJetConstant_nonneg camera time
  have h1 := empiricalScaledCameraTailFirstJetConstant_nonneg camera time
  have h2 := empiricalScaledCameraTailSecondJetConstant_nonneg camera time
  positivity

lemma abs_empiricalScaledCollectiveCutoffTailEnergyFirst_sub_le_div
    (M : ℕ) (hM : 1 ≤ M) (time : ℝ) :
    |empiricalScaledCollectiveCutoffTailEnergyFirst M time -
        empiricalLeadingCollectiveCoefficientEnergyFirst time| ≤
      empiricalCollectiveEnergyFirstDerivativeConstant time / (M : ℝ) := by
  have htwo := abs_empiricalScaledCollectiveCutoffTailEnergyFirst_sub_le
    M hM time
  have hMone : 1 ≤ (M : ℝ) := by exact_mod_cast hM
  have hMpos : 0 < (M : ℝ) := by linarith
  have hMleSq : (M : ℝ) ≤ (M : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((M : ℝ) - 1)]
  have hquad := empiricalCollectiveEnergyFirstDerivativeQuadraticConstant_nonneg time
  have hdiv :
      empiricalCollectiveEnergyFirstDerivativeQuadraticConstant time /
          (M : ℝ) ^ 2 ≤
        empiricalCollectiveEnergyFirstDerivativeQuadraticConstant time /
          (M : ℝ) := by
    exact div_le_div_of_nonneg_left hquad hMpos hMleSq
  calc
    |empiricalScaledCollectiveCutoffTailEnergyFirst M time -
        empiricalLeadingCollectiveCoefficientEnergyFirst time| ≤
        empiricalCollectiveEnergyFirstDerivativeLinearConstant time /
            (M : ℝ) +
          empiricalCollectiveEnergyFirstDerivativeQuadraticConstant time /
            (M : ℝ) ^ 2 := htwo
    _ ≤ empiricalCollectiveEnergyFirstDerivativeLinearConstant time /
          (M : ℝ) +
        empiricalCollectiveEnergyFirstDerivativeQuadraticConstant time /
          (M : ℝ) := add_le_add_left hdiv _
    _ = empiricalCollectiveEnergyFirstDerivativeConstant time /
          (M : ℝ) := by
      unfold empiricalCollectiveEnergyFirstDerivativeConstant
      ring

lemma abs_empiricalScaledCollectiveCutoffTailEnergySecond_sub_le_div
    (M : ℕ) (hM : 1 ≤ M) (time : ℝ) :
    |empiricalScaledCollectiveCutoffTailEnergySecond M time -
        empiricalLeadingCollectiveCoefficientEnergySecond time| ≤
      empiricalCollectiveEnergySecondDerivativeConstant time / (M : ℝ) := by
  have htwo := abs_empiricalScaledCollectiveCutoffTailEnergySecond_sub_le
    M hM time
  have hMone : 1 ≤ (M : ℝ) := by exact_mod_cast hM
  have hMpos : 0 < (M : ℝ) := by linarith
  have hMleSq : (M : ℝ) ≤ (M : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((M : ℝ) - 1)]
  have hquad := empiricalCollectiveEnergySecondDerivativeQuadraticConstant_nonneg time
  have hdiv :
      empiricalCollectiveEnergySecondDerivativeQuadraticConstant time /
          (M : ℝ) ^ 2 ≤
        empiricalCollectiveEnergySecondDerivativeQuadraticConstant time /
          (M : ℝ) := by
    exact div_le_div_of_nonneg_left hquad hMpos hMleSq
  calc
    |empiricalScaledCollectiveCutoffTailEnergySecond M time -
        empiricalLeadingCollectiveCoefficientEnergySecond time| ≤
        empiricalCollectiveEnergySecondDerivativeLinearConstant time /
            (M : ℝ) +
          empiricalCollectiveEnergySecondDerivativeQuadraticConstant time /
            (M : ℝ) ^ 2 := htwo
    _ ≤ empiricalCollectiveEnergySecondDerivativeLinearConstant time /
          (M : ℝ) +
        empiricalCollectiveEnergySecondDerivativeQuadraticConstant time /
          (M : ℝ) := add_le_add_left hdiv _
    _ = empiricalCollectiveEnergySecondDerivativeConstant time /
          (M : ℝ) := by
      unfold empiricalCollectiveEnergySecondDerivativeConstant
      ring

/-- First-derivative capstone for the normalized (scaled) tail energy. -/
theorem empiricalSixCameraCriticalRawEnergy_firstDerivative_explicit_remainder
    (M : ℕ) (hM : 1 ≤ M) (time : ℝ) :
    |empiricalScaledCollectiveCutoffTailEnergyFirst M time -
        2 * time * ((132244271 : ℝ) / 1778112000)| ≤
      empiricalCollectiveEnergyFirstDerivativeConstant time / (M : ℝ) := by
  rw [← empiricalLeadingCollectiveCoefficientEnergyFirst_eq time]
  exact abs_empiricalScaledCollectiveCutoffTailEnergyFirst_sub_le_div M hM time

/-- Hessian capstone for the normalized (scaled) tail energy. -/
theorem empiricalSixCameraCriticalRawEnergy_secondDerivative_explicit_remainder
    (M : ℕ) (hM : 1 ≤ M) (time : ℝ) :
    |empiricalScaledCollectiveCutoffTailEnergySecond M time -
        2 * ((132244271 : ℝ) / 1778112000)| ≤
      empiricalCollectiveEnergySecondDerivativeConstant time / (M : ℝ) := by
  rw [← empiricalLeadingCollectiveCoefficientEnergySecond_eq time]
  exact abs_empiricalScaledCollectiveCutoffTailEnergySecond_sub_le_div M hM time

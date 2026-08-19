import GenuineZeroUniformAtlasEnergy.EmpiricalFullEvenContinuation

/-!
# Differential crosswalk for the empirical six-camera stack

`EmpiricalStackProjection` introduces the model clock direction

```math
W_b(s)=\kappa_b(s)\,G'(s).
```

The faithful continuation table already proves on the open critical strip

```math
\chi_b(s)=\kappa_b(s)\,G(s).
```

This file differentiates that identity locally.  At a Genuine zero the term
`kappa_b'(s) G(s)` vanishes, so the concrete complex derivative of every
infinite empirical camera is exactly the corresponding coordinate of the
existing `empiricalClockTangentVector`.

This is an infinite-stack differential identification only.  No finite-cutoff
or moving-minimizer derivative is asserted here.
-/

open scoped Topology

namespace GenuineZeroUniformAtlasEnergy

open CPFormal.Analytic.Cp
open Set Filter

noncomputable section

/-- The six empirical limiting factors are entire functions of the spectral
parameter. -/
theorem differentiable_empiricalLimitingFactor
    (camera : EmpiricalCamera) :
    Differentiable ℂ (empiricalLimitingFactor camera) := by
  cases camera with
  | c2 =>
      change Differentiable ℂ (naturalEvenCameraFactor 4)
      unfold naturalEvenCameraFactor
      fun_prop (disch := norm_num)
  | c3 =>
      change Differentiable ℂ (naturalOddCameraFactor 3)
      exact differentiable_cpChartFactor 3 (by norm_num)
  | c4 =>
      change Differentiable ℂ (empiricalFullEvenCameraFactor 4)
      unfold empiricalFullEvenCameraFactor
      fun_prop (disch := norm_num)
  | c5 =>
      change Differentiable ℂ (naturalOddCameraFactor 5)
      exact differentiable_cpChartFactor 5 (by norm_num)
  | c6 =>
      change Differentiable ℂ (empiricalFullEvenCameraFactor 6)
      unfold empiricalFullEvenCameraFactor
      fun_prop (disch := norm_num)
  | c7 =>
      change Differentiable ℂ (naturalOddCameraFactor 7)
      exact differentiable_cpChartFactor 7 (by norm_num)

/-- The open Genuine strip is a neighbourhood of each of its points. -/
lemma genuineCriticalStrip_mem_nhds {s : ℂ}
    (hs : s ∈ genuineCriticalStrip) :
    genuineCriticalStrip ∈ 𝓝 s := by
  have hopen : IsOpen genuineCriticalStrip := by
    rw [show genuineCriticalStrip =
      {z : ℂ | 0 < z.re} ∩ {z : ℂ | z.re < 1} by rfl]
    exact
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
  exact hopen.mem_nhds hs

/-- Local eventual form of the faithful continuation table, suitable for
passing to complex derivatives. -/
lemma empiricalCameraCharacteristic_eventuallyEq_limitingFactor_mul_genuine
    (camera : EmpiricalCamera) {s : ℂ}
    (hs : s ∈ genuineCriticalStrip) :
    (fun z : ℂ => empiricalCameraCharacteristic camera z) =ᶠ[𝓝 s]
      (fun z : ℂ => empiricalLimitingFactor camera z * genuineContinuation z) := by
  filter_upwards [genuineCriticalStrip_mem_nhds hs] with z hz
  exact empiricalCameraCharacteristic_eq_limitingFactor_mul_genuineContinuation
    camera hz

/-- At a Genuine zero, differentiating the faithful continuation identity
kills the derivative-of-factor term and leaves exactly the model clock
coordinate. -/
theorem deriv_empiricalCameraCharacteristic_eq_clockTangent
    (camera : EmpiricalCamera) {s : ℂ}
    (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    deriv (empiricalCameraCharacteristic camera) s =
      empiricalClockTangentVector s camera := by
  have heq :=
    empiricalCameraCharacteristic_eventuallyEq_limitingFactor_mul_genuine
      camera hs
  have hfactor : DifferentiableAt ℂ (empiricalLimitingFactor camera) s :=
    (differentiable_empiricalLimitingFactor camera) s
  have hgenuine : DifferentiableAt ℂ genuineContinuation s :=
    (analyticOnNhd_genuineContinuation_genuineCriticalStrip s hs).differentiableAt
  have hproduct := hfactor.hasDerivAt.mul hgenuine.hasDerivAt
  calc
    deriv (empiricalCameraCharacteristic camera) s =
        deriv
          (fun z : ℂ =>
            empiricalLimitingFactor camera z * genuineContinuation z) s :=
      heq.deriv_eq
    _ = deriv (empiricalLimitingFactor camera) s * genuineContinuation s +
          empiricalLimitingFactor camera s * deriv genuineContinuation s :=
      hproduct.deriv
    _ = empiricalClockTangentVector s camera := by
      rw [hzero, mul_zero, zero_add]
      rfl

/-- Concrete derivative stack of the six infinite empirical characteristics. -/
def empiricalCameraDerivativeStack (s : ℂ) : EmpiricalCameraStack :=
  WithLp.toLp 2 fun camera =>
    deriv (empiricalCameraCharacteristic camera) s

@[simp] theorem empiricalCameraDerivativeStack_apply
    (s : ℂ) (camera : EmpiricalCamera) :
    empiricalCameraDerivativeStack s camera =
      deriv (empiricalCameraCharacteristic camera) s := by
  rfl

/-- Stack form of the differential crosswalk: at a Genuine zero, the existing
clock tangent is not merely a model direction; it is exactly the complex
spectral derivative of the faithful infinite six-camera stack. -/
theorem empiricalCameraDerivativeStack_eq_clockTangent_of_genuine_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    empiricalCameraDerivativeStack s = empiricalClockTangentVector s := by
  ext camera
  exact deriv_empiricalCameraCharacteristic_eq_clockTangent camera hs hzero

/-- Consequently the `kappa` stored by the empirical phase data is exactly the
squared norm of the concrete infinite-stack complex derivative at a Genuine
zero. -/
theorem empiricalStackKappa_eq_derivativeStack_normSq_of_genuine_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    empiricalStackKappa s = ‖empiricalCameraDerivativeStack s‖ ^ 2 := by
  rw [empiricalCameraDerivativeStack_eq_clockTangent_of_genuine_zero hs hzero]
  rfl

end

end GenuineZeroUniformAtlasEnergy

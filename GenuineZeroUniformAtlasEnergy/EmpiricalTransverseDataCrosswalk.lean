import GenuineZeroUniformAtlasEnergy.MicroscopicPrimitiveJetBounds
import GenuineZeroUniformAtlasEnergy.EmpiricalStackProjection

/-!
# Empirical transverse data crosswalk

The phase model contains two real coordinates of the cutoff/tangent pairing.
The radial coordinate is already named `empiricalStackPhaseProjection`; the
orthogonal coordinate is the displacement removed by the moving clock.

This module makes that reoptimization exact.  The phase-rotated pairing has
fixed squared modulus `alphaSq`; completing the clock square removes its
imaginary coordinate and leaves exactly

```math
rho + x^2 / kappa.
```

Thus the denominator and model gradient consumed by the microscopic
perturbation ledger are not independent ansatzes.  They are the exact value
and radial gradient of the leading clock-reoptimized quadratic envelope.
-/

open scoped ComplexConjugate InnerProductSpace

namespace GenuineZeroUniformAtlasEnergy

open CPFormal.Analytic.Cp

noncomputable section

/-- Imaginary coordinate of the same phase-rotated pairing whose real
coordinate is `empiricalStackPhaseProjection`. -/
def empiricalStackPhaseImagProjection (s : ℂ) (theta : ℝ) : ℝ :=
  (Complex.exp ((theta : ℂ) * Complex.I) *
    empiricalStackPairing s).im

/-- The real and imaginary phase projections retain exactly the squared
modulus of the cutoff/tangent pairing. -/
theorem empiricalStackPhaseProjection_sq_add_imag_sq
    (s : ℂ) (theta : ℝ) :
    empiricalStackPhaseProjection s theta ^ 2 +
        empiricalStackPhaseImagProjection s theta ^ 2 =
      empiricalStackAlphaSq s := by
  let z : ℂ := Complex.exp ((theta : ℂ) * Complex.I) *
    empiricalStackPairing s
  have hnorm : ‖z‖ = ‖empiricalStackPairing s‖ := by
    dsimp [z]
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  change z.re ^ 2 + z.im ^ 2 = ‖empiricalStackPairing s‖ ^ 2
  rw [← hnorm, Complex.sq_norm, Complex.normSq_apply]
  ring

namespace PhaseProjectionData

/-- Quadratic clock envelope before the temporal direction is reoptimized. -/
def clockEnvelope
    (d : PhaseProjectionData) (x y tau : ℝ) : ℝ :=
  d.amplitudeSq - 2 * y * tau + d.kappa * tau ^ 2

/-- Exact minimizing temporal displacement of the quadratic clock envelope. -/
def clockMinimizer (d : PhaseProjectionData) (y : ℝ) : ℝ :=
  y / d.kappa

/-- Completed-square crosswalk from the two phase coordinates to the radial
model denominator. -/
theorem clockEnvelope_eq_phaseDenominator_add_square
    (d : PhaseProjectionData) (h : d.IsAdmissible)
    (x y tau : ℝ)
    (hphase : x ^ 2 + y ^ 2 = d.alphaSq) :
    d.clockEnvelope x y tau =
      (d.rho + x ^ 2 / d.kappa) +
        d.kappa * (tau - d.clockMinimizer y) ^ 2 := by
  have hkappa : d.kappa ≠ 0 := ne_of_gt h.1
  unfold clockEnvelope clockMinimizer
  rw [← h.2.2.2.2, ← hphase]
  field_simp [hkappa]
  ring

/-- At the moving clock minimizer, the quadratic envelope is exactly the
phase denominator used by `phaseCoercivity`. -/
theorem clockEnvelope_at_minimizer_eq_phaseDenominator
    (d : PhaseProjectionData) (h : d.IsAdmissible)
    (x y : ℝ)
    (hphase : x ^ 2 + y ^ 2 = d.alphaSq) :
    d.clockEnvelope x y (d.clockMinimizer y) =
      d.rho + x ^ 2 / d.kappa := by
  rw [d.clockEnvelope_eq_phaseDenominator_add_square h x y
    (d.clockMinimizer y) hphase]
  simp

/-- The phase denominator is a global lower bound for the full quadratic
clock envelope. -/
theorem phaseDenominator_le_clockEnvelope
    (d : PhaseProjectionData) (h : d.IsAdmissible)
    (x y tau : ℝ)
    (hphase : x ^ 2 + y ^ 2 = d.alphaSq) :
    d.rho + x ^ 2 / d.kappa ≤ d.clockEnvelope x y tau := by
  rw [d.clockEnvelope_eq_phaseDenominator_add_square h x y tau hphase]
  exact le_add_of_nonneg_right
    (mul_nonneg (le_of_lt h.1) (sq_nonneg _))

/-- The positive transverse mass `rho` is a fixed absolute floor for every
phase denominator. -/
theorem rho_le_abs_phaseDenominator
    (d : PhaseProjectionData) (h : d.IsAdmissible) (x : ℝ) :
    d.rho ≤ |d.rho + x ^ 2 / d.kappa| := by
  rw [abs_of_pos (d.phaseDenominator_pos h x)]
  exact le_add_of_nonneg_right
    (div_nonneg (sq_nonneg _) (le_of_lt h.1))

end PhaseProjectionData

/-- Exact logarithmic cutoff phase appearing in the critical cutoff monomial. -/
def empiricalCutoffPhase (time : ℝ) (M : ℕ) : ℝ :=
  time * Real.log (M : ℝ)

/-- The empirical leading clock envelope, evaluated at its moving minimizer,
is exactly the phase-dependent model energy. -/
theorem empiricalStack_clockEnvelope_at_phaseMinimizer_eq
    {s : ℂ} (hs : s.re = (1 : ℝ) / 2)
    (hsimple : deriv genuineContinuation s ≠ 0)
    (theta : ℝ) :
    let d := empiricalStackPhaseProjectionData s
    let x := empiricalStackPhaseProjection s theta
    let y := empiricalStackPhaseImagProjection s theta
    d.clockEnvelope x y (d.clockMinimizer y) =
      d.rho + x ^ 2 / d.kappa := by
  dsimp
  exact
    (empiricalStackPhaseProjectionData s).clockEnvelope_at_minimizer_eq_phaseDenominator
      (empiricalStackPhaseProjectionData_isAdmissible hs hsimple)
      (empiricalStackPhaseProjection s theta)
      (empiricalStackPhaseImagProjection s theta)
      (empiricalStackPhaseProjection_sq_add_imag_sq s theta)

/-- The model radial gradient `2x` is uniformly bounded by twice the norm of
the fixed cutoff/tangent pairing. -/
theorem abs_two_empiricalStackPhaseProjection_le
    (s : ℂ) (theta : ℝ) :
    |2 * empiricalStackPhaseProjection s theta| ≤
      2 * ‖empiricalStackPairing s‖ := by
  let z : ℂ := Complex.exp ((theta : ℂ) * Complex.I) *
    empiricalStackPairing s
  have hnorm : ‖z‖ = ‖empiricalStackPairing s‖ := by
    dsimp [z]
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hre :
      |empiricalStackPhaseProjection s theta| ≤
        ‖empiricalStackPairing s‖ := by
    calc
      |empiricalStackPhaseProjection s theta| = |z.re| := by rfl
      _ ≤ ‖z‖ := Complex.abs_re_le_norm z
      _ = ‖empiricalStackPairing s‖ := hnorm
  calc
    |2 * empiricalStackPhaseProjection s theta| =
        2 * |empiricalStackPhaseProjection s theta| := by
      rw [abs_mul]
      norm_num
    _ ≤ 2 * ‖empiricalStackPairing s‖ :=
      mul_le_mul_of_nonneg_left hre (by norm_num)

/-- The empirical transverse mass is a fixed denominator floor for every
logarithmic cutoff phase. -/
theorem empiricalStackRho_le_abs_phaseDenominator
    {s : ℂ} (hs : s.re = (1 : ℝ) / 2)
    (hsimple : deriv genuineContinuation s ≠ 0)
    (theta : ℝ) :
    empiricalStackRho s ≤
      |empiricalStackRho s +
        empiricalStackPhaseProjection s theta ^ 2 /
          empiricalStackKappa s| := by
  exact
    (empiricalStackPhaseProjectionData s).rho_le_abs_phaseDenominator
      (empiricalStackPhaseProjectionData_isAdmissible hs hsimple)
      (empiricalStackPhaseProjection s theta)

end

end GenuineZeroUniformAtlasEnergy

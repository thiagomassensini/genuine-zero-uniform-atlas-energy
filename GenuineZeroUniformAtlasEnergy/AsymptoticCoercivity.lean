import GenuineZeroUniformAtlasEnergy.TransverseCoercivity

/-!
# Phase-uniform algebraic coercivity model and limit passage

The proposed collective cutoff model has one scalar phase variable after the
clock direction is formally reoptimized.  This file isolates the exact algebra
needed to turn that phase-dependent model into a phase-independent lower bound.

No numerical value of a zeta zero, derivative, cutoff, or fitted coercivity
constant is assumed here.  The analytic bridge must separately provide the
four projection scalars and an explicit approximation error.
-/

open Filter

namespace GenuineZeroUniformAtlasEnergy

noncomputable section

/-- Scalar Gram data for a leading cutoff vector and the limiting clock
tangent.  `amplitudeSq` is the squared norm of the leading vector, `kappa` is
the squared norm of the tangent, `alphaSq` is the squared modulus of their
pairing, and `rho` is the squared transverse component. -/
structure PhaseProjectionData where
  kappa : ℝ
  rho : ℝ
  amplitudeSq : ℝ
  alphaSq : ℝ

namespace PhaseProjectionData

/-- Exact projection identity together with the strict positivity needed for
division. -/
def IsAdmissible (d : PhaseProjectionData) : Prop :=
  0 < d.kappa ∧
    0 < d.rho ∧
      0 < d.amplitudeSq ∧
        0 ≤ d.alphaSq ∧
          d.rho + d.alphaSq / d.kappa = d.amplitudeSq

/-- Algebraic phase-dependent coercivity model.  The real scalar `x` is the
model projection `Re (exp(i theta) alpha)`. -/
def phaseCoercivity (d : PhaseProjectionData) (x : ℝ) : ℝ :=
  d.kappa * d.rho / (d.rho + x ^ 2 / d.kappa)

/-- Phase-independent floor obtained by replacing the phase denominator by
the full leading amplitude. -/
def phaseFloor (d : PhaseProjectionData) : ℝ :=
  d.kappa * d.rho / d.amplitudeSq

lemma phaseDenominator_pos
    (d : PhaseProjectionData) (h : d.IsAdmissible) (x : ℝ) :
    0 < d.rho + x ^ 2 / d.kappa := by
  have hx : 0 ≤ x ^ 2 / d.kappa := div_nonneg (sq_nonneg x) (le_of_lt h.1)
  linarith [h.2.1]

lemma phaseDenominator_le_amplitudeSq
    (d : PhaseProjectionData) (h : d.IsAdmissible) (x : ℝ)
    (hx : x ^ 2 ≤ d.alphaSq) :
    d.rho + x ^ 2 / d.kappa ≤ d.amplitudeSq := by
  have hxdiv : x ^ 2 / d.kappa ≤ d.alphaSq / d.kappa :=
    (div_le_div_iff_of_pos_right h.1).2 hx
  rw [← h.2.2.2.2]
  linarith

lemma phaseFloor_pos
    (d : PhaseProjectionData) (h : d.IsAdmissible) :
    0 < d.phaseFloor := by
  exact div_pos (mul_pos h.1 h.2.1) h.2.2.1

/-- The projected limiting coercivity is bounded below independently of the
logarithmic phase. -/
theorem phaseCoercivity_uniform_lower_bound
    (d : PhaseProjectionData) (h : d.IsAdmissible) (x : ℝ)
    (hx : x ^ 2 ≤ d.alphaSq) :
    d.phaseFloor ≤ d.phaseCoercivity x := by
  have hdenPos := d.phaseDenominator_pos h x
  have hdenLe := d.phaseDenominator_le_amplitudeSq h x hx
  unfold phaseFloor phaseCoercivity
  rw [div_le_div_iff₀ h.2.2.1 hdenPos]
  exact mul_le_mul_of_nonneg_left hdenLe (le_of_lt (mul_pos h.1 h.2.1))

/-- Any explicit error smaller than the gap below the phase floor transfers
the model lower bound to a supplied microscopic-coefficient value. -/
theorem microscopicCoercivity_lower_bound_of_error
    (d : PhaseProjectionData) (h : d.IsAdmissible)
    (x cMicro c error : ℝ)
    (hx : x ^ 2 ≤ d.alphaSq)
    (happrox : |cMicro - d.phaseCoercivity x| ≤ error)
    (hgap : error ≤ d.phaseFloor - c) :
    c ≤ cMicro := by
  have hphase := d.phaseCoercivity_uniform_lower_bound h x hx
  have hlower : -error ≤ cMicro - d.phaseCoercivity x :=
    (abs_le.mp happrox).1
  linarith

/-- A supplied sequence with an explicit `C/M` approximation to the algebraic
phase model is eventually bounded below by every constant strictly below the
phase floor.  This is the precise Archimedean step used to choose a cutoff
threshold `M0`; no numerical value of that threshold is hidden in the
statement. -/
theorem eventually_microscopicCoercivity_lower_bound_of_inv_error
    (d : PhaseProjectionData) (h : d.IsAdmissible)
    (phaseProjection cMicro : ℕ → ℝ) (C c : ℝ)
    (hx : ∀ M : ℕ, (phaseProjection M) ^ 2 ≤ d.alphaSq)
    (happrox : ∀ M : ℕ, 1 ≤ M →
      |cMicro M - d.phaseCoercivity (phaseProjection M)| ≤ C / (M : ℝ))
    (hc : c < d.phaseFloor) :
    ∀ᶠ M : ℕ in atTop, c ≤ cMicro M := by
  have hgap : 0 < d.phaseFloor - c := sub_pos.mpr hc
  have hratio : Tendsto (fun M : ℕ => C / (M : ℝ)) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat C
  have hsmall : ∀ᶠ M : ℕ in atTop,
      C / (M : ℝ) < d.phaseFloor - c :=
    hratio.eventually (Iio_mem_nhds hgap)
  filter_upwards [hsmall, eventually_ge_atTop 1] with M hMsmall hM
  exact d.microscopicCoercivity_lower_bound_of_error h
    (phaseProjection M) (cMicro M) c (C / (M : ℝ))
    (hx M) (happrox M hM) (le_of_lt hMsmall)

/-- The target `4` follows conditionally as soon as a separate exact argument
places the phase floor strictly above `4` and a supplied sequence is
approximated by the model with error `C/M`. -/
theorem eventually_microscopicCoercivity_ge_four_of_inv_error
    (d : PhaseProjectionData) (h : d.IsAdmissible)
    (phaseProjection cMicro : ℕ → ℝ) (C : ℝ)
    (hx : ∀ M : ℕ, (phaseProjection M) ^ 2 ≤ d.alphaSq)
    (happrox : ∀ M : ℕ, 1 ≤ M →
      |cMicro M - d.phaseCoercivity (phaseProjection M)| ≤ C / (M : ℝ))
    (hfour : (4 : ℝ) < d.phaseFloor) :
    ∀ᶠ M : ℕ in atTop, (4 : ℝ) ≤ cMicro M := by
  exact d.eventually_microscopicCoercivity_lower_bound_of_inv_error h
    phaseProjection cMicro C 4 hx happrox hfour

end PhaseProjectionData

/-- A fixed transverse coercivity constant survives pointwise convergence of
the finite energies.  This is the global limit passage once a uniform finite
lower bound and the operator-energy convergence have been supplied. -/
theorem transverseCoercivity_passes_to_pointwise_limit
    (energy : ℕ → ℝ → ℝ → ℝ)
    (limitEnergy : ℝ → ℝ → ℝ) (c : ℝ)
    (hcoercive : ∀ M : ℕ, IsTransverselyCoercive (energy M) c)
    (hlimit : ∀ sigma time : ℝ,
      Tendsto (fun M : ℕ => energy M sigma time) atTop
        (nhds (limitEnergy sigma time))) :
    IsTransverselyCoercive limitEnergy c := by
  intro sigma time
  exact ge_of_tendsto (hlimit sigma time)
    (Eventually.of_forall fun M => hcoercive M sigma time)

/-- It is enough that the uniform finite coercivity estimate hold eventually
in the cutoff. -/
theorem transverseCoercivity_passes_to_pointwise_limit_eventually
    (energy : ℕ → ℝ → ℝ → ℝ)
    (limitEnergy : ℝ → ℝ → ℝ) (c : ℝ)
    (hcoercive : ∀ᶠ M : ℕ in atTop,
      IsTransverselyCoercive (energy M) c)
    (hlimit : ∀ sigma time : ℝ,
      Tendsto (fun M : ℕ => energy M sigma time) atTop
        (nhds (limitEnergy sigma time))) :
    IsTransverselyCoercive limitEnergy c := by
  intro sigma time
  apply ge_of_tendsto (hlimit sigma time)
  filter_upwards [hcoercive] with M hM
  exact hM sigma time

end

end GenuineZeroUniformAtlasEnergy

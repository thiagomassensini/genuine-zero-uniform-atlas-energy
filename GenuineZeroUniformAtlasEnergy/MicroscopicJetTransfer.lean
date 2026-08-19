import GenuineZeroUniformAtlasEnergy.MicroscopicCoercivityFrontier

/-!
# Microscopic jet transfer

The quadratic microscopic coefficient is already reduced to the exact
perturbation ledger

```math
(c_M-c_0)
- \frac{g_M^2-g_0^2}{4E_M}
- \frac{g_0^2(E_0-E_M)}{4E_ME_0}.
```

This module packages the remaining quantitative step.  Three independently
proved `C_i / M` bounds for the curvature, squared-gradient, and residual
energy channels give one `C / M` approximation to the phase model.  The
existing phase-floor theorem then supplies an eventual strictly positive
microscopic coefficient.

No cutoff estimate is assumed implicitly: the three component bounds remain
visible hypotheses, ready to be discharged by the value, first-derivative,
and second-derivative tail estimates.
-/

open Filter

namespace GenuineZeroUniformAtlasEnergy

noncomputable section

/-- Three inverse-cutoff perturbation bounds combine into the exact
`C / M` approximation required by the phase-floor argument. -/
theorem PhaseProjectionData.abs_quadraticMicroscopicCoercivity_sub_phaseCoercivity_le_inv_of_perturbation_bounds
    (d : PhaseProjectionData) (h : d.IsAdmissible)
    (M : ℕ) (energy gradient localCoercivity x
      curvatureConstant gradientConstant energyConstant : ℝ)
    (henergy : energy ≠ 0)
    (hcurvature :
      |localCoercivity - d.kappa| ≤ curvatureConstant / (M : ℝ))
    (hgradient :
      |(gradient ^ 2 - (2 * x) ^ 2) / (4 * energy)| ≤
        gradientConstant / (M : ℝ))
    (henergyError :
      |(2 * x) ^ 2 *
          ((d.rho + x ^ 2 / d.kappa) - energy) /
            (4 * energy * (d.rho + x ^ 2 / d.kappa))| ≤
        energyConstant / (M : ℝ)) :
    |quadraticMicroscopicCoercivity energy gradient localCoercivity -
        d.phaseCoercivity x| ≤
      (curvatureConstant + gradientConstant + energyConstant) / (M : ℝ) := by
  have henergy₀ : d.rho + x ^ 2 / d.kappa ≠ 0 :=
    ne_of_gt (d.phaseDenominator_pos h x)
  rw [d.phaseCoercivity_eq_quadraticMicroscopicCoercivity h x]
  have hbound :=
    abs_quadraticMicroscopicCoercivity_sub_le_of_perturbation_bounds
      energy (d.rho + x ^ 2 / d.kappa)
      gradient (2 * x) localCoercivity d.kappa
      (curvatureConstant / (M : ℝ))
      (gradientConstant / (M : ℝ))
      (energyConstant / (M : ℝ))
      henergy henergy₀ hcurvature hgradient henergyError
  calc
    |quadraticMicroscopicCoercivity energy gradient localCoercivity -
        quadraticMicroscopicCoercivity
          (d.rho + x ^ 2 / d.kappa) (2 * x) d.kappa| ≤
      curvatureConstant / (M : ℝ) +
        gradientConstant / (M : ℝ) +
          energyConstant / (M : ℝ) := hbound
    _ = (curvatureConstant + gradientConstant + energyConstant) /
        (M : ℝ) := by ring

/-- Sequence form of the transfer.  Once the three displayed ledger channels
are `O(1/M)`, the reoptimized microscopic coefficient is eventually bounded
below by one fixed positive constant.  Thus the local analytic bridge no
longer has to manipulate the quotient `c - g^2/(4E)` directly. -/
theorem PhaseProjectionData.eventually_positive_quadraticMicroscopicCoercivity_of_inv_perturbation_bounds
    (d : PhaseProjectionData) (h : d.IsAdmissible)
    (energy gradient localCoercivity phaseProjection : ℕ → ℝ)
    (curvatureConstant gradientConstant energyConstant : ℝ)
    (hx : ∀ M : ℕ, (phaseProjection M) ^ 2 ≤ d.alphaSq)
    (henergy : ∀ M : ℕ, 1 ≤ M → energy M ≠ 0)
    (hcurvature : ∀ M : ℕ, 1 ≤ M →
      |localCoercivity M - d.kappa| ≤
        curvatureConstant / (M : ℝ))
    (hgradient : ∀ M : ℕ, 1 ≤ M →
      |((gradient M) ^ 2 - (2 * phaseProjection M) ^ 2) /
          (4 * energy M)| ≤
        gradientConstant / (M : ℝ))
    (henergyError : ∀ M : ℕ, 1 ≤ M →
      |(2 * phaseProjection M) ^ 2 *
          ((d.rho + (phaseProjection M) ^ 2 / d.kappa) - energy M) /
            (4 * energy M *
              (d.rho + (phaseProjection M) ^ 2 / d.kappa))| ≤
        energyConstant / (M : ℝ)) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ M : ℕ in atTop,
        c ≤ quadraticMicroscopicCoercivity
          (energy M) (gradient M) (localCoercivity M) := by
  let C : ℝ := curvatureConstant + gradientConstant + energyConstant
  let c : ℝ := d.phaseFloor / 2
  have hfloor : 0 < d.phaseFloor := d.phaseFloor_pos h
  have hcpos : 0 < c := by
    dsimp [c]
    linarith
  have hclt : c < d.phaseFloor := by
    dsimp [c]
    linarith
  refine ⟨c, hcpos, ?_⟩
  apply d.eventually_microscopicCoercivity_lower_bound_of_inv_error h
    phaseProjection
    (fun M : ℕ =>
      quadraticMicroscopicCoercivity
        (energy M) (gradient M) (localCoercivity M))
    C c hx
  · intro M hM
    have hbound :=
      d.abs_quadraticMicroscopicCoercivity_sub_phaseCoercivity_le_inv_of_perturbation_bounds
        h M (energy M) (gradient M) (localCoercivity M)
        (phaseProjection M)
        curvatureConstant gradientConstant energyConstant
        (henergy M hM) (hcurvature M hM)
        (hgradient M hM) (henergyError M hM)
    simpa [C] using hbound
  · exact hclt

end

end GenuineZeroUniformAtlasEnergy

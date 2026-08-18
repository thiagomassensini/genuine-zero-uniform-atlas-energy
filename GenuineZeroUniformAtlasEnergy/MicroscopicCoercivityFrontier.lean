import GenuineZeroUniformAtlasEnergy.AsymptoticCoercivity

/-!
# Quadratic microscopic coercivity frontier

The finite transverse audit isolates, after reoptimizing the clock, a local
quadratic envelope

```math
E_0 + g\,\delta + c_{\rm local}\,\delta^2.
```

Its sharp coefficient against `delta^2` is

```math
c_{\rm micro}=c_{\rm local}-\frac{g^2}{4E_0}.
```

This file records that algebra exactly and identifies the leading empirical
phase model with this same microscopic coefficient when

```math
E_0=\rho+x^2/\kappa,\qquad g=2x,\qquad c_{\rm local}=\kappa.
```

No zero height, fitted decimal, cutoff witness, or numerical positivity input
appears in these statements.
-/

namespace GenuineZeroUniformAtlasEnergy

noncomputable section

/-- Quadratic envelope obtained after the clock direction has been
reoptimized to first order. -/
def quadraticMicroscopicEnvelope
    (energy gradient localCoercivity delta : ℝ) : ℝ :=
  energy + gradient * delta + localCoercivity * delta ^ 2

/-- Sharp transverse coefficient of the quadratic microscopic envelope when
the residual energy is positive. -/
def quadraticMicroscopicCoercivity
    (energy gradient localCoercivity : ℝ) : ℝ :=
  localCoercivity - gradient ^ 2 / (4 * energy)

/-- Completed-square identity behind the microscopic quotient. -/
theorem quadraticMicroscopicEnvelope_sub_coercivity_mul_sq
    (energy gradient localCoercivity delta : ℝ)
    (henergy : energy ≠ 0) :
    quadraticMicroscopicEnvelope energy gradient localCoercivity delta -
        quadraticMicroscopicCoercivity energy gradient localCoercivity *
          delta ^ 2 =
      (2 * energy + gradient * delta) ^ 2 / (4 * energy) := by
  unfold quadraticMicroscopicEnvelope quadraticMicroscopicCoercivity
  field_simp [henergy]
  ring

/-- Positive residual energy makes the microscopic coefficient a genuine
lower bound for the entire quadratic envelope. -/
theorem quadraticMicroscopicCoercivity_mul_sq_le_envelope
    (energy gradient localCoercivity delta : ℝ)
    (henergy : 0 < energy) :
    quadraticMicroscopicCoercivity energy gradient localCoercivity *
        delta ^ 2 ≤
      quadraticMicroscopicEnvelope energy gradient localCoercivity delta := by
  have hden : 0 < 4 * energy := by positivity
  have hnonneg :
      0 ≤ (2 * energy + gradient * delta) ^ 2 / (4 * energy) :=
    div_nonneg (sq_nonneg _) (le_of_lt hden)
  rw [← quadraticMicroscopicEnvelope_sub_coercivity_mul_sq
    energy gradient localCoercivity delta (ne_of_gt henergy)] at hnonneg
  linarith

/-- The empirical phase formula is not a separate ansatz: it is exactly the
quadratic microscopic coefficient with leading residual energy
`rho + x^2/kappa`, leading radial gradient `2x`, and limiting local curvature
`kappa`. -/
theorem PhaseProjectionData.phaseCoercivity_eq_quadraticMicroscopicCoercivity
    (d : PhaseProjectionData) (h : d.IsAdmissible) (x : ℝ) :
    d.phaseCoercivity x =
      quadraticMicroscopicCoercivity
        (d.rho + x ^ 2 / d.kappa) (2 * x) d.kappa := by
  have hkappa : d.kappa ≠ 0 := ne_of_gt h.1
  have hdenPos : 0 < d.rho + x ^ 2 / d.kappa :=
    d.phaseDenominator_pos h x
  have hden : d.rho + x ^ 2 / d.kappa ≠ 0 := ne_of_gt hdenPos
  have hscaledDenPos : 0 < d.kappa * d.rho + x ^ 2 :=
    add_pos_of_pos_of_nonneg (mul_pos h.1 h.2.1) (sq_nonneg x)
  have hscaledDen : d.kappa * d.rho + x ^ 2 ≠ 0 :=
    ne_of_gt hscaledDenPos
  unfold PhaseProjectionData.phaseCoercivity quadraticMicroscopicCoercivity
  field_simp [hkappa, hden, hscaledDen]
  ring

/-- Consequently the phase coercivity is an exact quadratic lower bound,
uniformly in the transverse displacement, before any cutoff approximation is
introduced. -/
theorem PhaseProjectionData.phaseCoercivity_mul_sq_le_quadraticEnvelope
    (d : PhaseProjectionData) (h : d.IsAdmissible)
    (x delta : ℝ) :
    d.phaseCoercivity x * delta ^ 2 ≤
      quadraticMicroscopicEnvelope
        (d.rho + x ^ 2 / d.kappa) (2 * x) d.kappa delta := by
  rw [d.phaseCoercivity_eq_quadraticMicroscopicCoercivity h x]
  exact quadraticMicroscopicCoercivity_mul_sq_le_envelope
    (d.rho + x ^ 2 / d.kappa) (2 * x) d.kappa delta
    (d.phaseDenominator_pos h x)

end

end GenuineZeroUniformAtlasEnergy

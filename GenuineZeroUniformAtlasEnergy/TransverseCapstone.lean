import GenuineZeroUniformAtlasEnergy.TransverseSpectrum

/-!
# Transverse coercivity capstones

These public theorems package the exact algebra needed by a future bridge from
the finite native operator to a cutoff-uniform coercivity certificate.  The
bridge itself is intentionally not assumed here: this module does not identify
a Python computation with a Lean function, assert differentiability of a
specific finite characteristic, or claim a cutoff-independent numerical lower
bound.
-/

namespace GenuineZeroUniformAtlasEnergy

noncomputable section

/-- Positive `κ` and positive discriminant give the exact trace and determinant
formulas together with positive definiteness of the transverse Hessian. -/
theorem transverseHessian_trace_det_and_positiveDefinite
    (j : TransverseJet) (hkappa : 0 < j.kappa)
    (hdisc : 0 < j.discriminant) :
    j.hessianTrace = 4 * j.kappa ∧
      j.hessianDet = 4 * j.discriminant ∧
      j.IsPositiveDefinite := by
  exact ⟨
    TransverseJet.hessianTrace_eq_four_mul_kappa j,
    TransverseJet.hessianDet_eq_four_mul_discriminant j,
    TransverseJet.isPositiveDefinite_of_discriminant_pos j hkappa hdisc⟩

/-- The two explicit algebraic eigenvalues are roots of the Hessian
characteristic polynomial, and their sum and product recover trace and
determinant. -/
theorem transverseHessian_eigenvalue_pair (j : TransverseJet) :
    j.characteristicValue j.eigenvalueMinus = 0 ∧
      j.characteristicValue j.eigenvaluePlus = 0 ∧
      j.eigenvalueMinus + j.eigenvaluePlus = j.hessianTrace ∧
      j.eigenvalueMinus * j.eigenvaluePlus = j.hessianDet := by
  exact ⟨
    TransverseJet.characteristicValue_eigenvalueMinus j,
    TransverseJet.characteristicValue_eigenvaluePlus j,
    TransverseJet.eigenvalueMinus_add_eigenvaluePlus j,
    TransverseJet.eigenvalueMinus_mul_eigenvaluePlus j⟩

/-- The minimizing-clock slope and the envelope curvature are controlled by
the same discriminant.  Positive discriminant leaves strictly positive
curvature after the clock is reoptimized. -/
theorem transverseEnvelope_slope_and_curvature
    (j : TransverseJet) (hkappa : 0 < j.kappa)
    (hdisc : 0 < j.discriminant) :
    j.implicitTimeSlope = -j.b / (j.kappa - j.a) ∧
      j.schurEnvelopeCurvature = 2 * j.localCoercivity ∧
      0 < j.schurEnvelopeCurvature := by
  have hdenPos : 0 < j.kappa - j.a :=
    TransverseJet.kappa_sub_a_pos j hkappa hdisc
  have hden : j.kappa - j.a ≠ 0 := ne_of_gt hdenPos
  exact ⟨
    TransverseJet.implicitTimeSlope_eq j hden,
    TransverseJet.schurEnvelopeCurvature_eq_two_mul_localCoercivity j hden,
    TransverseJet.schurEnvelopeCurvature_pos j hkappa hdisc⟩

/-- Every constant strictly below the Schur coefficient gives a strict local
quadratic coercivity certificate, even after allowing the time direction to
move. -/
theorem transverseLocalCoercivity_certificate
    (j : TransverseJet) (hkappa : 0 < j.kappa)
    (hdisc : 0 < j.discriminant)
    (c : ℝ) (hc : c < j.localCoercivity)
    (x y : ℝ) (hxy : x ≠ 0 ∨ y ≠ 0) :
    0 < j.shiftedHalfHessianQuadratic c x y := by
  exact
    TransverseJet.shiftedHalfHessianQuadratic_pos_of_lt_localCoercivity
      j hkappa hdisc c hc x y hxy

/-- At an exact critical zero the residual correction vanishes: the Hessian is
isotropic, the minimizing clock has zero first-order slope, the envelope
curvature is `2κ`, and both eigenvalues equal `2κ`. -/
theorem exactZero_transverse_geometry (kappa x y : ℝ) :
    (TransverseJet.exactZero kappa).hessianQuadratic x y =
        2 * kappa * (x ^ 2 + y ^ 2) ∧
      (TransverseJet.exactZero kappa).implicitTimeSlope = 0 ∧
      (TransverseJet.exactZero kappa).schurEnvelopeCurvature = 2 * kappa ∧
      (TransverseJet.exactZero kappa).eigenvalueMinus = 2 * kappa ∧
      (TransverseJet.exactZero kappa).eigenvaluePlus = 2 * kappa := by
  exact ⟨
    TransverseJet.exactZero_hessianQuadratic kappa x y,
    TransverseJet.exactZero_implicitTimeSlope kappa,
    TransverseJet.exactZero_schurEnvelopeCurvature kappa,
    TransverseJet.exactZero_eigenvalueMinus kappa,
    TransverseJet.exactZero_eigenvaluePlus kappa⟩

/-- Certifying nonnegativity of the smooth residual
`E-c(σ-1/2)^2` is exactly the global transverse coercivity inequality. -/
theorem transverseCertificateResidual_nonneg_iff
    (energy : ℝ → ℝ → ℝ) (c : ℝ) :
    IsTransverselyCoercive energy c ↔
      ∀ sigma time : ℝ,
        0 ≤ transverseCertificateResidual energy c sigma time := by
  exact isTransverselyCoercive_iff_certificateResidual_nonneg energy c

/-- A positive global coercivity certificate excludes every off-critical zero
of the certified raw energy. -/
theorem transverseCoercivity_excludes_offCritical_zero
    {energy : ℝ → ℝ → ℝ} {c sigma time : ℝ}
    (hc : 0 < c)
    (hcoercive : IsTransverselyCoercive energy c)
    (hzero : energy sigma time = 0) :
    sigma = (1 : ℝ) / 2 := by
  exact zero_forces_re_eq_half_of_transverse_coercivity
    hc hcoercive hzero

end

end GenuineZeroUniformAtlasEnergy

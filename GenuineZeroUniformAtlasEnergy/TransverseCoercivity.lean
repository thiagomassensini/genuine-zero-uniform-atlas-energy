import Mathlib

/-!
# Finite transverse-coercivity certificate

This module formalizes the exact algebra behind the finite-cutoff Hessian
calculation discussed in the numerical audit.  It deliberately starts from the
three scalar jet coefficients

* `kappa = ‖∂σ χ‖²`,
* `a = ⟪χ, ∂σσ χ⟫`,
* `b = ⟪χ, J ∂σσ χ⟫`,

and does not claim that a particular numerical operator has already supplied
those identities in Lean.  Once the jet identities are available, the
Hessian, determinant, Schur complement, optimal time slope, and local
coercivity threshold are algebraic consequences.

The Hessian is represented by

```math
2\begin{pmatrix}
\kappa+a & b\\
b & \kappa-a
\end{pmatrix}.
```

Its discriminant is `κ²-a²-b²`.  The same scalar controls the determinant, the
positive-definiteness certificate, and the curvature left after minimizing in
the time direction.
-/

namespace GenuineZeroUniformAtlasEnergy

noncomputable section

/-- The three real scalar coefficients of the transverse finite-cutoff jet. -/
structure TransverseJet where
  kappa : ℝ
  a : ℝ
  b : ℝ

namespace TransverseJet

/-- The common discriminant controlling determinant and envelope curvature. -/
def discriminant (j : TransverseJet) : ℝ :=
  j.kappa ^ 2 - j.a ^ 2 - j.b ^ 2

/-- Upper-left Hessian entry. -/
def hessian00 (j : TransverseJet) : ℝ := 2 * (j.kappa + j.a)

/-- Mixed Hessian entry. -/
def hessian01 (j : TransverseJet) : ℝ := 2 * j.b

/-- Lower-right, temporal Hessian entry. -/
def hessian11 (j : TransverseJet) : ℝ := 2 * (j.kappa - j.a)

/-- Trace of the two-dimensional Hessian. -/
def hessianTrace (j : TransverseJet) : ℝ :=
  j.hessian00 + j.hessian11

/-- Determinant of the two-dimensional Hessian. -/
def hessianDet (j : TransverseJet) : ℝ :=
  j.hessian00 * j.hessian11 - j.hessian01 ^ 2

/-- Half of the Hessian quadratic form. -/
def halfHessianQuadratic (j : TransverseJet) (x y : ℝ) : ℝ :=
  (j.kappa + j.a) * x ^ 2 + 2 * j.b * x * y +
    (j.kappa - j.a) * y ^ 2

/-- The full Hessian quadratic form. -/
def hessianQuadratic (j : TransverseJet) (x y : ℝ) : ℝ :=
  2 * j.halfHessianQuadratic x y

/-- Positive definiteness expressed directly through the quadratic form. -/
def IsPositiveDefinite (j : TransverseJet) : Prop :=
  ∀ x y : ℝ, x ≠ 0 ∨ y ≠ 0 → 0 < j.hessianQuadratic x y

/-- The implicit-function slope `-E_{σt}/E_{tt}` of the minimizing clock. -/
def implicitTimeSlope (j : TransverseJet) : ℝ :=
  -j.hessian01 / j.hessian11

/-- Curvature after minimizing in the time direction, written as a Schur
complement. -/
def schurEnvelopeCurvature (j : TransverseJet) : ℝ :=
  j.hessian00 - j.hessian01 ^ 2 / j.hessian11

/-- Half of the envelope curvature: the local transverse coercivity constant. -/
def localCoercivity (j : TransverseJet) : ℝ :=
  j.discriminant / (j.kappa - j.a)

/-- Half-Hessian after subtracting a proposed coercivity constant `c` in the
sigma direction. -/
def shiftedHalfHessianQuadratic
    (j : TransverseJet) (c x y : ℝ) : ℝ :=
  j.halfHessianQuadratic x y - c * x ^ 2

@[simp] lemma hessianTrace_eq_four_mul_kappa (j : TransverseJet) :
    j.hessianTrace = 4 * j.kappa := by
  unfold hessianTrace hessian00 hessian11
  ring

@[simp] lemma hessianDet_eq_four_mul_discriminant (j : TransverseJet) :
    j.hessianDet = 4 * j.discriminant := by
  unfold hessianDet hessian00 hessian01 hessian11 discriminant
  ring

/-- Positivity of the discriminant and of `κ` forces positive temporal
curvature. -/
lemma kappa_sub_a_pos
    (j : TransverseJet) (hkappa : 0 < j.kappa)
    (hdisc : 0 < j.discriminant) :
    0 < j.kappa - j.a := by
  by_contra hnot
  have hka : j.kappa ≤ j.a := by linarith
  have hsum : 0 ≤ j.a + j.kappa := by linarith
  have hprod : 0 ≤ (j.a - j.kappa) * (j.a + j.kappa) :=
    mul_nonneg (sub_nonneg.mpr hka) hsum
  unfold discriminant at hdisc
  nlinarith [sq_nonneg j.b]

/-- Exact completed-square/Schur identity for the Hessian. -/
lemma halfHessianQuadratic_eq_schur
    (j : TransverseJet) (x y : ℝ)
    (hden : j.kappa - j.a ≠ 0) :
    j.halfHessianQuadratic x y =
      (j.kappa - j.a) *
          (y + j.b / (j.kappa - j.a) * x) ^ 2 +
        j.discriminant / (j.kappa - j.a) * x ^ 2 := by
  unfold halfHessianQuadratic discriminant
  field_simp [hden]
  ring

/-- Positive discriminant gives strict positivity of the half-Hessian away
from the origin. -/
lemma halfHessianQuadratic_pos_of_discriminant_pos
    (j : TransverseJet) (hkappa : 0 < j.kappa)
    (hdisc : 0 < j.discriminant)
    (x y : ℝ) (hxy : x ≠ 0 ∨ y ≠ 0) :
    0 < j.halfHessianQuadratic x y := by
  have hdenPos : 0 < j.kappa - j.a := j.kappa_sub_a_pos hkappa hdisc
  have hden : j.kappa - j.a ≠ 0 := ne_of_gt hdenPos
  rw [j.halfHessianQuadratic_eq_schur x y hden]
  by_cases hx : x = 0
  · have hy : y ≠ 0 := by
      rcases hxy with hx' | hy'
      · exact (hx hx').elim
      · exact hy'
    subst x
    simpa using mul_pos hdenPos (show 0 < y ^ 2 by positivity)
  · have hx2 : 0 < x ^ 2 := by positivity
    have hmain :
        0 < j.discriminant / (j.kappa - j.a) * x ^ 2 :=
      mul_pos (div_pos hdisc hdenPos) hx2
    have hrest :
        0 ≤ (j.kappa - j.a) *
          (y + j.b / (j.kappa - j.a) * x) ^ 2 :=
      mul_nonneg (le_of_lt hdenPos) (sq_nonneg _)
    linarith

/-- Positive discriminant is a sufficient finite Hessian
positive-definiteness certificate. -/
lemma isPositiveDefinite_of_discriminant_pos
    (j : TransverseJet) (hkappa : 0 < j.kappa)
    (hdisc : 0 < j.discriminant) :
    j.IsPositiveDefinite := by
  intro x y hxy
  unfold hessianQuadratic
  have hhalf :=
    j.halfHessianQuadratic_pos_of_discriminant_pos hkappa hdisc x y hxy
  linarith

/-- The scalar certificate simultaneously makes trace and determinant positive
and makes the Hessian positive definite. -/
lemma hessian_certificate
    (j : TransverseJet) (hkappa : 0 < j.kappa)
    (hdisc : 0 < j.discriminant) :
    0 < j.hessianTrace ∧ 0 < j.hessianDet ∧ j.IsPositiveDefinite := by
  refine ⟨?_, ?_, j.isPositiveDefinite_of_discriminant_pos hkappa hdisc⟩
  · rw [hessianTrace_eq_four_mul_kappa]
    positivity
  · rw [hessianDet_eq_four_mul_discriminant]
    positivity

/-- The implicit minimizing-clock slope is exactly `-b/(κ-a)`. -/
lemma implicitTimeSlope_eq
    (j : TransverseJet) (hden : j.kappa - j.a ≠ 0) :
    j.implicitTimeSlope = -j.b / (j.kappa - j.a) := by
  unfold implicitTimeSlope hessian01 hessian11
  field_simp [hden]
  ring

/-- The Schur complement is exactly twice the local coercivity constant. -/
lemma schurEnvelopeCurvature_eq_two_mul_localCoercivity
    (j : TransverseJet) (hden : j.kappa - j.a ≠ 0) :
    j.schurEnvelopeCurvature = 2 * j.localCoercivity := by
  unfold schurEnvelopeCurvature hessian00 hessian01 hessian11 localCoercivity
    discriminant
  field_simp [hden]
  ring

/-- Positive discriminant makes the reoptimized envelope curvature positive. -/
lemma schurEnvelopeCurvature_pos
    (j : TransverseJet) (hkappa : 0 < j.kappa)
    (hdisc : 0 < j.discriminant) :
    0 < j.schurEnvelopeCurvature := by
  have hdenPos : 0 < j.kappa - j.a := j.kappa_sub_a_pos hkappa hdisc
  rw [j.schurEnvelopeCurvature_eq_two_mul_localCoercivity
    (ne_of_gt hdenPos)]
  unfold localCoercivity
  positivity

/-- Subtracting `c x²` leaves a completed square plus the gap between the
actual local coercivity and the proposed constant. -/
lemma shiftedHalfHessianQuadratic_eq_schur
    (j : TransverseJet) (c x y : ℝ)
    (hden : j.kappa - j.a ≠ 0) :
    j.shiftedHalfHessianQuadratic c x y =
      (j.kappa - j.a) *
          (y + j.b / (j.kappa - j.a) * x) ^ 2 +
        (j.localCoercivity - c) * x ^ 2 := by
  unfold shiftedHalfHessianQuadratic localCoercivity
  rw [j.halfHessianQuadratic_eq_schur x y hden]
  ring

/-- Every constant strictly below the local Schur coefficient is a strict
quadratic coercivity certificate. -/
lemma shiftedHalfHessianQuadratic_pos_of_lt_localCoercivity
    (j : TransverseJet) (hkappa : 0 < j.kappa)
    (hdisc : 0 < j.discriminant)
    (c : ℝ) (hc : c < j.localCoercivity)
    (x y : ℝ) (hxy : x ≠ 0 ∨ y ≠ 0) :
    0 < j.shiftedHalfHessianQuadratic c x y := by
  have hdenPos : 0 < j.kappa - j.a := j.kappa_sub_a_pos hkappa hdisc
  have hden : j.kappa - j.a ≠ 0 := ne_of_gt hdenPos
  rw [j.shiftedHalfHessianQuadratic_eq_schur c x y hden]
  by_cases hx : x = 0
  · have hy : y ≠ 0 := by
      rcases hxy with hx' | hy'
      · exact (hx hx').elim
      · exact hy'
    subst x
    simpa using mul_pos hdenPos (show 0 < y ^ 2 by positivity)
  · have hx2 : 0 < x ^ 2 := by positivity
    have hmain : 0 < (j.localCoercivity - c) * x ^ 2 :=
      mul_pos (sub_pos.mpr hc) hx2
    have hrest :
        0 ≤ (j.kappa - j.a) *
          (y + j.b / (j.kappa - j.a) * x) ^ 2 :=
      mul_nonneg (le_of_lt hdenPos) (sq_nonneg _)
    linarith

/-- The residual-free jet occurring at an exact critical zero. -/
def exactZero (kappa : ℝ) : TransverseJet :=
  ⟨kappa, 0, 0⟩

@[simp] lemma exactZero_discriminant (kappa : ℝ) :
    (exactZero kappa).discriminant = kappa ^ 2 := by
  simp [exactZero, discriminant]

@[simp] lemma exactZero_hessianQuadratic
    (kappa x y : ℝ) :
    (exactZero kappa).hessianQuadratic x y =
      2 * kappa * (x ^ 2 + y ^ 2) := by
  unfold exactZero hessianQuadratic halfHessianQuadratic
  ring

@[simp] lemma exactZero_implicitTimeSlope (kappa : ℝ) :
    (exactZero kappa).implicitTimeSlope = 0 := by
  simp [exactZero, implicitTimeSlope, hessian01, hessian11]

@[simp] lemma exactZero_schurEnvelopeCurvature (kappa : ℝ) :
    (exactZero kappa).schurEnvelopeCurvature = 2 * kappa := by
  simp [exactZero, schurEnvelopeCurvature, hessian00, hessian01, hessian11]

end TransverseJet

/-- The smooth certificate function used by a branch-and-bound proof. -/
def transverseCertificateResidual
    (energy : ℝ → ℝ → ℝ) (c sigma time : ℝ) : ℝ :=
  energy sigma time - c * (sigma - (1 : ℝ) / 2) ^ 2

/-- A raw energy has coercivity constant `c` when it dominates the squared
distance from the critical line at every time. -/
def IsTransverselyCoercive
    (energy : ℝ → ℝ → ℝ) (c : ℝ) : Prop :=
  ∀ sigma time : ℝ,
    c * (sigma - (1 : ℝ) / 2) ^ 2 ≤ energy sigma time

/-- Certifying nonnegativity of the smooth residual is exactly the same as
certifying the transverse coercivity inequality. -/
lemma isTransverselyCoercive_iff_certificateResidual_nonneg
    (energy : ℝ → ℝ → ℝ) (c : ℝ) :
    IsTransverselyCoercive energy c ↔
      ∀ sigma time : ℝ,
        0 ≤ transverseCertificateResidual energy c sigma time := by
  constructor
  · intro h sigma time
    unfold transverseCertificateResidual
    linarith [h sigma time]
  · intro h sigma time
    unfold transverseCertificateResidual at h
    linarith [h sigma time]

/-- A positive coercivity certificate excludes every off-critical zero. -/
lemma zero_forces_re_eq_half_of_transverse_coercivity
    {energy : ℝ → ℝ → ℝ} {c sigma time : ℝ}
    (hc : 0 < c)
    (hcoercive : IsTransverselyCoercive energy c)
    (hzero : energy sigma time = 0) :
    sigma = (1 : ℝ) / 2 := by
  by_contra hne
  have hdiff : sigma - (1 : ℝ) / 2 ≠ 0 := sub_ne_zero.mpr hne
  have hsquare : 0 < (sigma - (1 : ℝ) / 2) ^ 2 := by positivity
  have hpositive :
      0 < c * (sigma - (1 : ℝ) / 2) ^ 2 :=
    mul_pos hc hsquare
  have hbound := hcoercive sigma time
  rw [hzero] at hbound
  linarith

end

end GenuineZeroUniformAtlasEnergy

import GenuineZeroUniformAtlasEnergy.GenuineZeroMultiplicity

/-!
# Exact scope of the quadratic empirical sector

The empirical phase floor is built from the first complex derivative of the
common Genuine scalar.  It is therefore the correct local model precisely for
a zero of multiplicity one.

This file makes that scope kernel-visible.  At every higher-multiplicity zero
the first derivative vanishes, hence the empirical clock tangent and its Gram
scalar `kappa` vanish.  The current `PhaseProjectionData` cannot then be
admissible.  Conversely, multiplicity one recovers the already proved strict
Gram positivity and phase-floor package.

No assertion that all zeros are simple is made.  The theorem only separates
the order-one quadratic route from the higher-order `2m` route.
-/

namespace GenuineZeroUniformAtlasEnergy

open CPFormal.Analytic.Cp

noncomputable section

namespace IsGenuineZeroOfMultiplicity

/-- Every zero of multiplicity strictly greater than one has zero first
complex derivative. -/
theorem deriv_eq_zero_of_one_lt
    {order : ℕ} {s : ℂ}
    (hroot : IsGenuineZeroOfMultiplicity order s)
    (horder : 1 < order) :
    deriv genuineContinuation s = 0 := by
  have hzero := hroot.lower_iteratedDeriv_eq_zero 1 horder
  simpa [iteratedDeriv_one] using hzero

end IsGenuineZeroOfMultiplicity

/-- The order-`m` root-jet Gram scalar.  It replaces the first-derivative
`empiricalStackKappa` when the Genuine zero has arbitrary finite order. -/
def empiricalRootJetKappa (order : ℕ) (s : ℂ) : ℝ :=
  ‖empiricalRootJetVector order s‖ ^ 2

/-- The generalized Gram scalar is strictly positive at every finite
multiplicity datum on the critical line. -/
theorem empiricalRootJetKappa_pos_of_multiplicity
    {order : ℕ} {s : ℂ}
    (hroot : IsGenuineZeroOfMultiplicity order s)
    (hs : s.re = (1 : ℝ) / 2) :
    0 < empiricalRootJetKappa order s := by
  unfold empiricalRootJetKappa
  exact sq_pos_of_pos
    (norm_pos_iff.mpr
      (empiricalRootJetVector_ne_zero_of_multiplicity hroot hs))

/-- In order one the generalized Gram scalar is literally the existing
quadratic `kappa`. -/
@[simp] theorem empiricalRootJetKappa_one (s : ℂ) :
    empiricalRootJetKappa 1 s = empiricalStackKappa s := by
  simp [empiricalRootJetKappa, empiricalStackKappa]

/-- Higher multiplicity kills the first-derivative empirical clock tangent. -/
theorem empiricalClockTangentVector_eq_zero_of_multiplicity_gt_one
    {order : ℕ} {s : ℂ}
    (hroot : IsGenuineZeroOfMultiplicity order s)
    (horder : 1 < order) :
    empiricalClockTangentVector s = 0 := by
  have hderiv := hroot.deriv_eq_zero_of_one_lt horder
  ext camera
  simp [empiricalClockTangentVector_apply, hderiv]

/-- Consequently the quadratic Gram scalar vanishes at every
higher-multiplicity zero. -/
theorem empiricalStackKappa_eq_zero_of_multiplicity_gt_one
    {order : ℕ} {s : ℂ}
    (hroot : IsGenuineZeroOfMultiplicity order s)
    (horder : 1 < order) :
    empiricalStackKappa s = 0 := by
  unfold empiricalStackKappa
  rw [empiricalClockTangentVector_eq_zero_of_multiplicity_gt_one
    hroot horder]
  simp

/-- The current first-derivative phase data is not admissible at a zero of
multiplicity greater than one. -/
theorem empiricalStackPhaseProjectionData_not_admissible_of_multiplicity_gt_one
    {order : ℕ} {s : ℂ}
    (hroot : IsGenuineZeroOfMultiplicity order s)
    (horder : 1 < order) :
    ¬ (empiricalStackPhaseProjectionData s).IsAdmissible := by
  intro hadmissible
  have hkappa :=
    empiricalStackKappa_eq_zero_of_multiplicity_gt_one hroot horder
  have hkappaPos := hadmissible.1
  change 0 < empiricalStackKappa s at hkappaPos
  rw [hkappa] at hkappaPos
  linarith

/-- Exact scope theorem: for a finite-order Genuine zero on the critical line,
the existing quadratic phase data is admissible if and only if the zero has
multiplicity one. -/
theorem empiricalStackPhaseProjectionData_isAdmissible_iff_multiplicity_one
    {order : ℕ} {s : ℂ}
    (hroot : IsGenuineZeroOfMultiplicity order s)
    (hs : s.re = (1 : ℝ) / 2) :
    (empiricalStackPhaseProjectionData s).IsAdmissible ↔ order = 1 := by
  constructor
  · intro hadmissible
    by_contra hne
    have horderPos : 0 < order := hroot.order_pos
    have horder : 1 < order := by omega
    exact
      (empiricalStackPhaseProjectionData_not_admissible_of_multiplicity_gt_one
        hroot horder) hadmissible
  · intro horder
    subst order
    have hsimple : deriv genuineContinuation s ≠ 0 := by
      simpa [iteratedDeriv_one] using
        hroot.leading_iteratedDeriv_ne_zero
    exact empiricalStackPhaseProjectionData_isAdmissible hs hsimple

/-- Equivalent positivity statement for the first-derivative Gram scalar. -/
theorem empiricalStackKappa_pos_iff_multiplicity_one
    {order : ℕ} {s : ℂ}
    (hroot : IsGenuineZeroOfMultiplicity order s)
    (hs : s.re = (1 : ℝ) / 2) :
    0 < empiricalStackKappa s ↔ order = 1 := by
  constructor
  · intro hkappa
    by_contra hne
    have horderPos : 0 < order := hroot.order_pos
    have horder : 1 < order := by omega
    rw [empiricalStackKappa_eq_zero_of_multiplicity_gt_one
      hroot horder] at hkappa
    linarith
  · intro horder
    subst order
    have hsimple : deriv genuineContinuation s ≠ 0 := by
      simpa [iteratedDeriv_one] using
        hroot.leading_iteratedDeriv_ne_zero
    exact empiricalStackKappa_pos hs hsimple

end

end GenuineZeroUniformAtlasEnergy

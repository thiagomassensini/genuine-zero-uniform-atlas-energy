import GenuineZeroUniformAtlasEnergy.NativeCutoffLogJet

/-!
# Differentiated cutoff-remainder transport

This module closes the algebraic stitching between a supplied twice
controlled scaled remainder and the exact logarithmic cutoff jets.

Suppose two scaled amplitudes `actual` and `model` have value,
first-derivative, and second-derivative discrepancies bounded by one common
rate `K * r`.  After multiplication by the exact cutoff factor `M^(-s-1)`,
their first jets differ by at most

```math
\|M^{-s-1}\|\,(1+\|\log M\|) K r,
```

and their second jets differ by at most

```math
\|M^{-s-1}\|\,(1+\|\log M\|)^2 K r.
```

The theorem is deliberately an interface theorem: it does not manufacture the
three analytic remainder estimates for the exact cutoff tail.  It proves that
once those estimates are supplied, no further differentiation or product-rule
gap remains before the phase-floor limit theorem.
-/

namespace GenuineZeroUniformAtlasEnergy

noncomputable section

/-- Pointwise first- and second-jet error bounds after exact transport through
`M^(-s-1)`.  The three inputs `errorZero`, `errorFirst`, and `errorSecond`
bound the scaled amplitude discrepancy and its first two derivatives. -/
theorem cutoffModel_first_second_jet_error_bounds
    (M : ℕ)
    (actual actualFirst actualSecond model modelFirst modelSecond : ℂ → ℂ)
    (s : ℂ) (errorZero errorFirst errorSecond : ℝ)
    (hzero : ‖actual s - model s‖ ≤ errorZero)
    (hfirst : ‖actualFirst s - modelFirst s‖ ≤ errorFirst)
    (hsecond : ‖actualSecond s - modelSecond s‖ ≤ errorSecond) :
    ‖nativeCutoffModelFirstJet M actual actualFirst s -
        nativeCutoffModelFirstJet M model modelFirst s‖ ≤
        ‖nativeCutoffScale M s‖ *
          (errorFirst + ‖nativeCutoffLog M‖ * errorZero) ∧
      ‖nativeCutoffModelSecondJet M actual actualFirst actualSecond s -
        nativeCutoffModelSecondJet M model modelFirst modelSecond s‖ ≤
        ‖nativeCutoffScale M s‖ *
          (errorSecond +
            2 * ‖nativeCutoffLog M‖ * errorFirst +
            ‖nativeCutoffLog M‖ ^ 2 * errorZero) := by
  have hfirstRewrite :
      nativeCutoffModelFirstJet M actual actualFirst s -
          nativeCutoffModelFirstJet M model modelFirst s =
        nativeCutoffScale M s *
          ((actualFirst s - modelFirst s) -
            nativeCutoffLog M * (actual s - model s)) := by
    unfold nativeCutoffModelFirstJet
    ring
  have hfirstCore :
      ‖(actualFirst s - modelFirst s) -
          nativeCutoffLog M * (actual s - model s)‖ ≤
        errorFirst + ‖nativeCutoffLog M‖ * errorZero := by
    calc
      ‖(actualFirst s - modelFirst s) -
          nativeCutoffLog M * (actual s - model s)‖ ≤
        ‖actualFirst s - modelFirst s‖ +
          ‖nativeCutoffLog M * (actual s - model s)‖ :=
        norm_sub_le _ _
      _ = ‖actualFirst s - modelFirst s‖ +
          ‖nativeCutoffLog M‖ * ‖actual s - model s‖ := by
        rw [norm_mul]
      _ ≤ errorFirst + ‖nativeCutoffLog M‖ * errorZero := by
        exact add_le_add hfirst
          (mul_le_mul_of_nonneg_left hzero
            (norm_nonneg (nativeCutoffLog M)))
  have hsecondRewrite :
      nativeCutoffModelSecondJet M actual actualFirst actualSecond s -
          nativeCutoffModelSecondJet M model modelFirst modelSecond s =
        nativeCutoffScale M s *
          ((actualSecond s - modelSecond s) -
            2 * nativeCutoffLog M * (actualFirst s - modelFirst s) +
            nativeCutoffLog M ^ 2 * (actual s - model s)) := by
    unfold nativeCutoffModelSecondJet
    ring
  have hmiddle :
      ‖(2 : ℂ) * nativeCutoffLog M *
          (actualFirst s - modelFirst s)‖ ≤
        2 * ‖nativeCutoffLog M‖ * errorFirst := by
    calc
      ‖(2 : ℂ) * nativeCutoffLog M *
          (actualFirst s - modelFirst s)‖ =
        2 * ‖nativeCutoffLog M‖ *
          ‖actualFirst s - modelFirst s‖ := by
        simp only [norm_mul]
        norm_num
      _ ≤ 2 * ‖nativeCutoffLog M‖ * errorFirst := by
        exact mul_le_mul_of_nonneg_left hfirst (by positivity)
  have hlast :
      ‖nativeCutoffLog M ^ 2 * (actual s - model s)‖ ≤
        ‖nativeCutoffLog M‖ ^ 2 * errorZero := by
    calc
      ‖nativeCutoffLog M ^ 2 * (actual s - model s)‖ =
        ‖nativeCutoffLog M‖ ^ 2 * ‖actual s - model s‖ := by
        rw [norm_mul, norm_pow]
      _ ≤ ‖nativeCutoffLog M‖ ^ 2 * errorZero := by
        exact mul_le_mul_of_nonneg_left hzero (sq_nonneg _)
  have hsecondCore :
      ‖(actualSecond s - modelSecond s) -
          2 * nativeCutoffLog M * (actualFirst s - modelFirst s) +
          nativeCutoffLog M ^ 2 * (actual s - model s)‖ ≤
        errorSecond +
          2 * ‖nativeCutoffLog M‖ * errorFirst +
          ‖nativeCutoffLog M‖ ^ 2 * errorZero := by
    calc
      ‖(actualSecond s - modelSecond s) -
          2 * nativeCutoffLog M * (actualFirst s - modelFirst s) +
          nativeCutoffLog M ^ 2 * (actual s - model s)‖ ≤
        ‖(actualSecond s - modelSecond s) -
          2 * nativeCutoffLog M * (actualFirst s - modelFirst s)‖ +
          ‖nativeCutoffLog M ^ 2 * (actual s - model s)‖ :=
        norm_add_le _ _
      _ ≤
        (‖actualSecond s - modelSecond s‖ +
          ‖(2 : ℂ) * nativeCutoffLog M *
            (actualFirst s - modelFirst s)‖) +
          ‖nativeCutoffLog M ^ 2 * (actual s - model s)‖ := by
        exact add_le_add_right
          (norm_sub_le
            (actualSecond s - modelSecond s)
            ((2 : ℂ) * nativeCutoffLog M *
              (actualFirst s - modelFirst s)))
          ‖nativeCutoffLog M ^ 2 * (actual s - model s)‖
      _ ≤ (errorSecond +
          2 * ‖nativeCutoffLog M‖ * errorFirst) +
          ‖nativeCutoffLog M‖ ^ 2 * errorZero := by
        exact add_le_add (add_le_add hsecond hmiddle) hlast
      _ = errorSecond +
          2 * ‖nativeCutoffLog M‖ * errorFirst +
          ‖nativeCutoffLog M‖ ^ 2 * errorZero := by ring
  constructor
  · rw [hfirstRewrite, norm_mul]
    exact mul_le_mul_of_nonneg_left hfirstCore
      (norm_nonneg (nativeCutoffScale M s))
  · rw [hsecondRewrite, norm_mul]
    exact mul_le_mul_of_nonneg_left hsecondCore
      (norm_nonneg (nativeCutoffScale M s))

/-- If the scaled value and both scaled derivatives share one bound `K * r`,
the first transported jet acquires one logarithm and the second transported
jet acquires exactly the square `(1 + ‖log M‖)^2`. -/
theorem cutoffModel_first_second_jet_error_bounds_of_common_rate
    (M : ℕ)
    (actual actualFirst actualSecond model modelFirst modelSecond : ℂ → ℂ)
    (s : ℂ) (K rate : ℝ)
    (hzero : ‖actual s - model s‖ ≤ K * rate)
    (hfirst : ‖actualFirst s - modelFirst s‖ ≤ K * rate)
    (hsecond : ‖actualSecond s - modelSecond s‖ ≤ K * rate) :
    ‖nativeCutoffModelFirstJet M actual actualFirst s -
        nativeCutoffModelFirstJet M model modelFirst s‖ ≤
        ‖nativeCutoffScale M s‖ *
          ((1 + ‖nativeCutoffLog M‖) * (K * rate)) ∧
      ‖nativeCutoffModelSecondJet M actual actualFirst actualSecond s -
        nativeCutoffModelSecondJet M model modelFirst modelSecond s‖ ≤
        ‖nativeCutoffScale M s‖ *
          ((1 + ‖nativeCutoffLog M‖) ^ 2 * (K * rate)) := by
  have hbounds :=
    cutoffModel_first_second_jet_error_bounds
      M actual actualFirst actualSecond model modelFirst modelSecond s
      (K * rate) (K * rate) (K * rate)
      hzero hfirst hsecond
  constructor
  · calc
      ‖nativeCutoffModelFirstJet M actual actualFirst s -
          nativeCutoffModelFirstJet M model modelFirst s‖ ≤
        ‖nativeCutoffScale M s‖ *
          (K * rate + ‖nativeCutoffLog M‖ * (K * rate)) := hbounds.1
      _ = ‖nativeCutoffScale M s‖ *
          ((1 + ‖nativeCutoffLog M‖) * (K * rate)) := by ring
  · calc
      ‖nativeCutoffModelSecondJet M actual actualFirst actualSecond s -
          nativeCutoffModelSecondJet M model modelFirst modelSecond s‖ ≤
        ‖nativeCutoffScale M s‖ *
          (K * rate +
            2 * ‖nativeCutoffLog M‖ * (K * rate) +
            ‖nativeCutoffLog M‖ ^ 2 * (K * rate)) := hbounds.2
      _ = ‖nativeCutoffScale M s‖ *
          ((1 + ‖nativeCutoffLog M‖) ^ 2 * (K * rate)) := by ring

/-- Capstone for the differentiated-remainder gate.  It combines the exact
first/second product-rule jets for both amplitudes with the common-rate
logarithmic error bounds.  The only remaining analytic input is the supplied
value/first/second remainder estimate itself. -/
theorem cutoffModel_differentiated_remainder_gate
    (M : ℕ) (hM : 0 < M)
    {actual actualFirst actualSecond model modelFirst modelSecond : ℂ → ℂ}
    {s : ℂ} {K rate : ℝ}
    (hActual : HasDerivAt actual (actualFirst s) s)
    (hActualFirst : HasDerivAt actualFirst (actualSecond s) s)
    (hModel : HasDerivAt model (modelFirst s) s)
    (hModelFirst : HasDerivAt modelFirst (modelSecond s) s)
    (hzero : ‖actual s - model s‖ ≤ K * rate)
    (hfirst : ‖actualFirst s - modelFirst s‖ ≤ K * rate)
    (hsecond : ‖actualSecond s - modelSecond s‖ ≤ K * rate) :
    HasDerivAt (nativeCutoffModel M actual)
        (nativeCutoffModelFirstJet M actual actualFirst s) s ∧
      HasDerivAt (nativeCutoffModelFirstJet M actual actualFirst)
        (nativeCutoffModelSecondJet M actual actualFirst actualSecond s) s ∧
      HasDerivAt (nativeCutoffModel M model)
        (nativeCutoffModelFirstJet M model modelFirst s) s ∧
      HasDerivAt (nativeCutoffModelFirstJet M model modelFirst)
        (nativeCutoffModelSecondJet M model modelFirst modelSecond s) s ∧
      (‖nativeCutoffModelFirstJet M actual actualFirst s -
          nativeCutoffModelFirstJet M model modelFirst s‖ ≤
          ‖nativeCutoffScale M s‖ *
            ((1 + ‖nativeCutoffLog M‖) * (K * rate)) ∧
        ‖nativeCutoffModelSecondJet M actual actualFirst actualSecond s -
          nativeCutoffModelSecondJet M model modelFirst modelSecond s‖ ≤
          ‖nativeCutoffScale M s‖ *
            ((1 + ‖nativeCutoffLog M‖) ^ 2 * (K * rate))) := by
  have hActualJets :=
    cutoffModel_first_second_logarithmic_jets
      M hM hActual hActualFirst
  have hModelJets :=
    cutoffModel_first_second_logarithmic_jets
      M hM hModel hModelFirst
  have hbounds :=
    cutoffModel_first_second_jet_error_bounds_of_common_rate
      M actual actualFirst actualSecond model modelFirst modelSecond s K rate
      hzero hfirst hsecond
  exact ⟨
    hActualJets.1,
    hActualJets.2,
    hModelJets.1,
    hModelJets.2,
    hbounds⟩

end

end GenuineZeroUniformAtlasEnergy

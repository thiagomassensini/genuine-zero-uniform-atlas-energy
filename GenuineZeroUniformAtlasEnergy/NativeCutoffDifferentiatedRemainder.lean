import GenuineZeroUniformAtlasEnergy.NativeCutoffLogJet

/-!
# Differentiated cutoff-remainder transport

This module closes the algebraic stitching between a supplied twice
controlled scaled remainder and the exact logarithmic cutoff jets.

Suppose two scaled amplitudes `exact` and `model` have value, first-derivative,
and second-derivative discrepancies bounded by one common rate `K * r`.  After
multiplication by the exact cutoff factor `M^(-s-1)`, their first jets differ by
at most

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
    (exact exactFirst exactSecond model modelFirst modelSecond : ℂ → ℂ)
    (s : ℂ) (errorZero errorFirst errorSecond : ℝ)
    (hzero : ‖exact s - model s‖ ≤ errorZero)
    (hfirst : ‖exactFirst s - modelFirst s‖ ≤ errorFirst)
    (hsecond : ‖exactSecond s - modelSecond s‖ ≤ errorSecond) :
    ‖nativeCutoffModelFirstJet M exact exactFirst s -
        nativeCutoffModelFirstJet M model modelFirst s‖ ≤
        ‖nativeCutoffScale M s‖ *
          (errorFirst + ‖nativeCutoffLog M‖ * errorZero) ∧
      ‖nativeCutoffModelSecondJet M exact exactFirst exactSecond s -
        nativeCutoffModelSecondJet M model modelFirst modelSecond s‖ ≤
        ‖nativeCutoffScale M s‖ *
          (errorSecond +
            2 * ‖nativeCutoffLog M‖ * errorFirst +
            ‖nativeCutoffLog M‖ ^ 2 * errorZero) := by
  have hfirstRewrite :
      nativeCutoffModelFirstJet M exact exactFirst s -
          nativeCutoffModelFirstJet M model modelFirst s =
        nativeCutoffScale M s *
          ((exactFirst s - modelFirst s) -
            nativeCutoffLog M * (exact s - model s)) := by
    unfold nativeCutoffModelFirstJet
    ring
  have hfirstCore :
      ‖(exactFirst s - modelFirst s) -
          nativeCutoffLog M * (exact s - model s)‖ ≤
        errorFirst + ‖nativeCutoffLog M‖ * errorZero := by
    calc
      ‖(exactFirst s - modelFirst s) -
          nativeCutoffLog M * (exact s - model s)‖ ≤
        ‖exactFirst s - modelFirst s‖ +
          ‖nativeCutoffLog M * (exact s - model s)‖ :=
        norm_sub_le _ _
      _ = ‖exactFirst s - modelFirst s‖ +
          ‖nativeCutoffLog M‖ * ‖exact s - model s‖ := by
        rw [norm_mul]
      _ ≤ errorFirst + ‖nativeCutoffLog M‖ * errorZero := by
        exact add_le_add hfirst
          (mul_le_mul_of_nonneg_left hzero
            (norm_nonneg (nativeCutoffLog M)))
  have hsecondRewrite :
      nativeCutoffModelSecondJet M exact exactFirst exactSecond s -
          nativeCutoffModelSecondJet M model modelFirst modelSecond s =
        nativeCutoffScale M s *
          ((exactSecond s - modelSecond s) -
            2 * nativeCutoffLog M * (exactFirst s - modelFirst s) +
            nativeCutoffLog M ^ 2 * (exact s - model s)) := by
    unfold nativeCutoffModelSecondJet
    ring
  have hmiddle :
      ‖(2 : ℂ) * nativeCutoffLog M *
          (exactFirst s - modelFirst s)‖ ≤
        2 * ‖nativeCutoffLog M‖ * errorFirst := by
    calc
      ‖(2 : ℂ) * nativeCutoffLog M *
          (exactFirst s - modelFirst s)‖ =
        2 * ‖nativeCutoffLog M‖ *
          ‖exactFirst s - modelFirst s‖ := by
        simp only [norm_mul]
        norm_num
      _ ≤ 2 * ‖nativeCutoffLog M‖ * errorFirst := by
        exact mul_le_mul_of_nonneg_left hfirst (by positivity)
  have hlast :
      ‖nativeCutoffLog M ^ 2 * (exact s - model s)‖ ≤
        ‖nativeCutoffLog M‖ ^ 2 * errorZero := by
    calc
      ‖nativeCutoffLog M ^ 2 * (exact s - model s)‖ =
        ‖nativeCutoffLog M‖ ^ 2 * ‖exact s - model s‖ := by
        rw [norm_mul, norm_pow]
      _ ≤ ‖nativeCutoffLog M‖ ^ 2 * errorZero := by
        exact mul_le_mul_of_nonneg_left hzero (sq_nonneg _)
  have hsecondCore :
      ‖(exactSecond s - modelSecond s) -
          2 * nativeCutoffLog M * (exactFirst s - modelFirst s) +
          nativeCutoffLog M ^ 2 * (exact s - model s)‖ ≤
        errorSecond +
          2 * ‖nativeCutoffLog M‖ * errorFirst +
          ‖nativeCutoffLog M‖ ^ 2 * errorZero := by
    calc
      ‖(exactSecond s - modelSecond s) -
          2 * nativeCutoffLog M * (exactFirst s - modelFirst s) +
          nativeCutoffLog M ^ 2 * (exact s - model s)‖ ≤
        ‖(exactSecond s - modelSecond s) -
          2 * nativeCutoffLog M * (exactFirst s - modelFirst s)‖ +
          ‖nativeCutoffLog M ^ 2 * (exact s - model s)‖ :=
        norm_add_le _ _
      _ ≤
        (‖exactSecond s - modelSecond s‖ +
          ‖(2 : ℂ) * nativeCutoffLog M *
            (exactFirst s - modelFirst s)‖) +
          ‖nativeCutoffLog M ^ 2 * (exact s - model s)‖ := by
        exact add_le_add_right (norm_sub_le _ _) _
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
    (exact exactFirst exactSecond model modelFirst modelSecond : ℂ → ℂ)
    (s : ℂ) (K rate : ℝ)
    (hzero : ‖exact s - model s‖ ≤ K * rate)
    (hfirst : ‖exactFirst s - modelFirst s‖ ≤ K * rate)
    (hsecond : ‖exactSecond s - modelSecond s‖ ≤ K * rate) :
    ‖nativeCutoffModelFirstJet M exact exactFirst s -
        nativeCutoffModelFirstJet M model modelFirst s‖ ≤
        ‖nativeCutoffScale M s‖ *
          ((1 + ‖nativeCutoffLog M‖) * (K * rate)) ∧
      ‖nativeCutoffModelSecondJet M exact exactFirst exactSecond s -
        nativeCutoffModelSecondJet M model modelFirst modelSecond s‖ ≤
        ‖nativeCutoffScale M s‖ *
          ((1 + ‖nativeCutoffLog M‖) ^ 2 * (K * rate)) := by
  have hbounds :=
    cutoffModel_first_second_jet_error_bounds
      M exact exactFirst exactSecond model modelFirst modelSecond s
      (K * rate) (K * rate) (K * rate)
      hzero hfirst hsecond
  constructor
  · calc
      ‖nativeCutoffModelFirstJet M exact exactFirst s -
          nativeCutoffModelFirstJet M model modelFirst s‖ ≤
        ‖nativeCutoffScale M s‖ *
          (K * rate + ‖nativeCutoffLog M‖ * (K * rate)) := hbounds.1
      _ = ‖nativeCutoffScale M s‖ *
          ((1 + ‖nativeCutoffLog M‖) * (K * rate)) := by ring
  · calc
      ‖nativeCutoffModelSecondJet M exact exactFirst exactSecond s -
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
    {exact exactFirst exactSecond model modelFirst modelSecond : ℂ → ℂ}
    {s : ℂ} {K rate : ℝ}
    (hExact : HasDerivAt exact (exactFirst s) s)
    (hExactFirst : HasDerivAt exactFirst (exactSecond s) s)
    (hModel : HasDerivAt model (modelFirst s) s)
    (hModelFirst : HasDerivAt modelFirst (modelSecond s) s)
    (hzero : ‖exact s - model s‖ ≤ K * rate)
    (hfirst : ‖exactFirst s - modelFirst s‖ ≤ K * rate)
    (hsecond : ‖exactSecond s - modelSecond s‖ ≤ K * rate) :
    HasDerivAt (nativeCutoffModel M exact)
        (nativeCutoffModelFirstJet M exact exactFirst s) s ∧
      HasDerivAt (nativeCutoffModelFirstJet M exact exactFirst)
        (nativeCutoffModelSecondJet M exact exactFirst exactSecond s) s ∧
      HasDerivAt (nativeCutoffModel M model)
        (nativeCutoffModelFirstJet M model modelFirst s) s ∧
      HasDerivAt (nativeCutoffModelFirstJet M model modelFirst)
        (nativeCutoffModelSecondJet M model modelFirst modelSecond s) s ∧
      (‖nativeCutoffModelFirstJet M exact exactFirst s -
          nativeCutoffModelFirstJet M model modelFirst s‖ ≤
          ‖nativeCutoffScale M s‖ *
            ((1 + ‖nativeCutoffLog M‖) * (K * rate)) ∧
        ‖nativeCutoffModelSecondJet M exact exactFirst exactSecond s -
          nativeCutoffModelSecondJet M model modelFirst modelSecond s‖ ≤
          ‖nativeCutoffScale M s‖ *
            ((1 + ‖nativeCutoffLog M‖) ^ 2 * (K * rate))) := by
  have hExactJets :=
    cutoffModel_first_second_logarithmic_jets
      M hM hExact hExactFirst
  have hModelJets :=
    cutoffModel_first_second_logarithmic_jets
      M hM hModel hModelFirst
  have hbounds :=
    cutoffModel_first_second_jet_error_bounds_of_common_rate
      M exact exactFirst exactSecond model modelFirst modelSecond s K rate
      hzero hfirst hsecond
  exact ⟨
    hExactJets.1,
    hExactJets.2,
    hModelJets.1,
    hModelJets.2,
    hbounds⟩

end

end GenuineZeroUniformAtlasEnergy

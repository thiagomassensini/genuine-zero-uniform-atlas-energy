import GenuineZeroUniformAtlasEnergy.NativeCutoffExactScaledTailLocal

/-!
# Exact scaled cutoff tail: accumulated complex remainder

Summation of the generic local Taylor remainder on `Re(s)>0`.
-/

open scoped BigOperators Function Topology

namespace GenuineZeroUniformAtlasEnergy

open CPFormal.Analytic.Cp
open Set MeasureTheory Metric

noncomputable section

attribute [local instance 10000] NormedSpace.complexToReal
lemma summable_shifted_rpow_neg_re_sub_three
    (M : ℕ) {s : ℂ} (hs : 0 < s.re) :
    Summable (fun k : ℕ ↦
      ((k : ℝ) + (M : ℝ) + 1) ^ (-s.re - 3)) := by
  have hraw : Summable (fun n : ℕ ↦ (n : ℝ) ^ (-s.re - 3)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hbase : Summable (fun k : ℕ ↦
      ((k : ℝ) + 1) ^ (-s.re - 3)) := by
    have hshift := hraw.comp_injective
      (show Function.Injective (fun n : ℕ ↦ n + 1) by
        intro a b hab
        exact Nat.add_right_cancel hab)
    simpa [Function.comp_def, Nat.cast_add] using hshift
  refine Summable.of_nonneg_of_le
    (fun k ↦ Real.rpow_nonneg (by positivity) _) ?_ hbase
  intro k
  have hleft : 0 < (k : ℝ) + 1 := by positivity
  have hMnonneg : 0 ≤ (M : ℝ) := by positivity
  have hle : (k : ℝ) + 1 ≤ (k : ℝ) + (M : ℝ) + 1 := by linarith
  exact Real.rpow_le_rpow_of_nonpos hleft hle (by linarith)

lemma shifted_rpow_neg_re_sub_three_tsum_le
    (M : ℕ) (hM : 1 ≤ M) {s : ℂ} (hs : 0 < s.re) :
    (∑' k : ℕ,
      ((k : ℝ) + (M : ℝ) + 1) ^ (-s.re - 3)) ≤
      (M : ℝ) ^ (-(s.re + 2)) / (s.re + 2) := by
  have hMpos : 0 < (M : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)
  let f : ℝ → ℝ := fun x ↦ x ^ (-s.re - 3)
  have hanti : AntitoneOn f (Ici (M : ℝ)) := by
    intro x hx y _hy hxy
    dsimp [f]
    exact Real.rpow_le_rpow_of_nonpos
      (lt_of_lt_of_le hMpos (mem_Ici.mp hx)) hxy (by linarith)
  have hintegrable : IntegrableOn f (Ioi (M : ℝ)) := by
    dsimp [f]
    exact integrableOn_Ioi_rpow_of_lt (by linarith) hMpos
  have hnonneg : ∀ x ∈ Ioi (M : ℝ), 0 ≤ f x := by
    intro x hx
    dsimp [f]
    exact Real.rpow_nonneg (le_of_lt (hMpos.trans (mem_Ioi.mp hx))) _
  calc
    (∑' k : ℕ,
      ((k : ℝ) + (M : ℝ) + 1) ^ (-s.re - 3)) ≤
        ∫ x in Ioi (M : ℝ), x ^ (-s.re - 3) := by
      simpa [f, Nat.cast_add] using
        hanti.tsum_comp_add_le_integral M hintegrable hnonneg
    _ = -(M : ℝ) ^ ((-s.re - 3) + 1) /
          ((-s.re - 3) + 1) :=
      integral_Ioi_rpow_of_lt (by linarith) hMpos
    _ = (M : ℝ) ^ (-(s.re + 2)) / (s.re + 2) := by
      have hexp : (-s.re - 3) + 1 = -(s.re + 2) := by ring
      rw [hexp, neg_div_neg_eq]

lemma summable_nativeExplicitRadiusBracketRemainder_of_re_pos
    (b h M : ℕ) (hb : 1 ≤ b) (hh : h ≤ b - 1)
    {s : ℂ} (hs : 0 < s.re) :
    Summable (fun k : ℕ ↦
      nativeExplicitRadiusBracketRemainder b h (k + M) s) := by
  let C : ℝ :=
    2 * ‖s * (s + 1) * (s + 2)‖ *
      ((b - h : ℕ) : ℝ) ^ (-s.re - 3) *
      nativeRadiusThirdMoment h
  have hpower := summable_shifted_rpow_neg_re_sub_three M hs
  have hmajorant : Summable (fun k : ℕ ↦
      C * ((k : ℝ) + (M : ℝ) + 1) ^ (-s.re - 3)) :=
    hpower.mul_left C
  exact hmajorant.of_norm_bounded (fun k ↦ by
    have hlocal :=
      norm_nativeExplicitRadiusBracketRemainder_of_re_pos_le
        b h (k + M) hb hh hs
    calc
      ‖nativeExplicitRadiusBracketRemainder b h (k + M) s‖ ≤
        2 * ‖s * (s + 1) * (s + 2)‖ *
          ((b - h : ℕ) : ℝ) ^ (-s.re - 3) *
          (((k + M + 1 : ℕ) : ℝ)) ^ (-s.re - 3) *
          nativeRadiusThirdMoment h := hlocal
      _ = C * ((k : ℝ) + (M : ℝ) + 1) ^ (-s.re - 3) := by
        simp [C, Nat.cast_add]
        ring)

/-- Generic accumulated local Taylor bound. -/
theorem norm_nativeExplicitRadiusAccumulatedBracketRemainder_of_re_pos_le
    (b h M : ℕ) (hb : 1 ≤ b) (hh : h ≤ b - 1)
    (hM : 1 ≤ M) {s : ℂ} (hs : 0 < s.re) :
    ‖nativeExplicitRadiusAccumulatedBracketRemainder b h M s‖ ≤
      (2 * ‖s * (s + 1) * (s + 2)‖ *
        ((b - h : ℕ) : ℝ) ^ (-s.re - 3) *
        nativeRadiusThirdMoment h / (s.re + 2)) *
      (M : ℝ) ^ (-(s.re + 2)) := by
  let C : ℝ :=
    2 * ‖s * (s + 1) * (s + 2)‖ *
      ((b - h : ℕ) : ℝ) ^ (-s.re - 3) *
      nativeRadiusThirdMoment h
  have hpower := summable_shifted_rpow_neg_re_sub_three M hs
  have hmajorantHasSum :
      HasSum (fun k : ℕ ↦
          C * ((k : ℝ) + (M : ℝ) + 1) ^ (-s.re - 3))
        (C * ∑' k : ℕ,
          ((k : ℝ) + (M : ℝ) + 1) ^ (-s.re - 3)) :=
    hpower.hasSum.mul_left C
  have hpointwise : ∀ k : ℕ,
      ‖nativeExplicitRadiusBracketRemainder b h (k + M) s‖ ≤
        C * ((k : ℝ) + (M : ℝ) + 1) ^ (-s.re - 3) := by
    intro k
    have hlocal :=
      norm_nativeExplicitRadiusBracketRemainder_of_re_pos_le
        b h (k + M) hb hh hs
    calc
      ‖nativeExplicitRadiusBracketRemainder b h (k + M) s‖ ≤
        2 * ‖s * (s + 1) * (s + 2)‖ *
          ((b - h : ℕ) : ℝ) ^ (-s.re - 3) *
          (((k + M + 1 : ℕ) : ℝ)) ^ (-s.re - 3) *
          nativeRadiusThirdMoment h := hlocal
      _ = C * ((k : ℝ) + (M : ℝ) + 1) ^ (-s.re - 3) := by
        simp [C, Nat.cast_add]
        ring
  have hnorm :
      ‖∑' k : ℕ,
          nativeExplicitRadiusBracketRemainder b h (k + M) s‖ ≤
        C * ∑' k : ℕ,
          ((k : ℝ) + (M : ℝ) + 1) ^ (-s.re - 3) :=
    tsum_of_norm_bounded hmajorantHasSum hpointwise
  have hC : 0 ≤ C := by
    have hmoment : 0 ≤ nativeRadiusThirdMoment h :=
      nativeRadiusThirdMoment_nonneg h
    dsimp [C]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (norm_nonneg _))
        (Real.rpow_nonneg (by positivity) _))
      hmoment
  have hden : 0 < s.re + 2 := by linarith
  calc
    ‖nativeExplicitRadiusAccumulatedBracketRemainder b h M s‖ =
        ‖∑' k : ℕ,
          nativeExplicitRadiusBracketRemainder b h (k + M) s‖ := by rfl
    _ ≤ C * ∑' k : ℕ,
        ((k : ℝ) + (M : ℝ) + 1) ^ (-s.re - 3) := hnorm
    _ ≤ C * ((M : ℝ) ^ (-(s.re + 2)) / (s.re + 2)) :=
      mul_le_mul_of_nonneg_left
        (shifted_rpow_neg_re_sub_three_tsum_le M hM hs) hC
    _ = (C / (s.re + 2)) *
        (M : ℝ) ^ (-(s.re + 2)) := by
      field_simp
    _ = (2 * ‖s * (s + 1) * (s + 2)‖ *
        ((b - h : ℕ) : ℝ) ^ (-s.re - 3) *
        nativeRadiusThirdMoment h / (s.re + 2)) *
      (M : ℝ) ^ (-(s.re + 2)) := by rfl


end

end GenuineZeroUniformAtlasEnergy

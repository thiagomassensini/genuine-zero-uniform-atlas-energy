import GenuineZeroUniformAtlasEnergy.NativeCutoffGlobalRemainder
import GenuineZeroUniformAtlasEnergy.NativeCutoffDifferentiatedRemainder
import CPFormal.Analytic.CpBracketHolomorphic
import Mathlib.Analysis.Complex.Liouville

/-!
# Exact scaled cutoff tail: local complex remainder

Generic local Taylor estimates on `Re(s)>0`, before global summation.
-/

open scoped BigOperators Function Topology

namespace GenuineZeroUniformAtlasEnergy

open CPFormal.Analytic.Cp
open Set MeasureTheory Metric

noncomputable section

attribute [local instance 10000] NormedSpace.complexToReal
def nativeExplicitRadiusScaledCutoffTail
    (b h M : ℕ) (s : ℂ) : ℂ :=
  (M : ℂ) ^ (s + 1) * nativeExplicitRadiusCutoffTail b h M s

/-- Error of the exact scaled cutoff tail from its leading coefficient. -/
def nativeExplicitRadiusScaledTailError
    (b h M : ℕ) (s : ℂ) : ℂ :=
  nativeExplicitRadiusScaledCutoffTail b h M s -
    nativeExplicitRadiusTailCoefficient b h s

/-- Generic local Taylor remainder for one centered radius pair. -/
theorem norm_realCpPairBracket_sub_secondDerivative_of_re_pos_le
    (b radius k : ℕ) (hb : 1 ≤ b) (hradius : radius ≤ b - 1)
    {s : ℂ} (hs : 0 < s.re) :
    ‖realCpPairBracket b radius k s -
        ((radius : ℝ) ^ 2) •
          realDirichletPowerDeriv2 s
            ((b : ℝ) * ((k + 1 : ℕ) : ℝ))‖ ≤
      2 * ‖s * (s + 1) * (s + 2)‖ *
        ((b : ℝ) * ((k + 1 : ℕ) : ℝ) - (radius : ℝ)) ^
          (-s.re - 3) *
        (radius : ℝ) ^ 3 := by
  let center : ℝ := (b : ℝ) * ((k + 1 : ℕ) : ℝ)
  let r : ℝ := radius
  have hs0 : s ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp at hre
    linarith
  have hs1 : -1 < s.re := by linarith
  have hs2 : -2 < s.re := by linarith
  have hj : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  have hbrNat : radius + 1 ≤ b := by omega
  have hbr : (radius : ℝ) + 1 ≤ (b : ℝ) := by
    exact_mod_cast hbrNat
  have hbnonneg : 0 ≤ (b : ℝ) := by positivity
  have hbCenter : (b : ℝ) ≤ center := by
    dsimp [center]
    nlinarith [mul_nonneg hbnonneg (sub_nonneg.mpr hj)]
  have hleft : 0 < center - r := by
    dsimp [r]
    linarith
  have hthirdBound :
      ∀ x ∈ Set.Icc (center - r) (center + r),
        ‖realDirichletPowerDeriv3 s x‖ ≤
          ‖s * (s + 1) * (s + 2)‖ *
            (center - r) ^ (-s.re - 3) := by
    intro x hx
    have hxpos : 0 < x := hleft.trans_le hx.1
    rw [norm_realDirichletPowerDeriv3 s hxpos]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hleft hx.1 (by linarith))
      (norm_nonneg _)
  have hraw :=
    norm_centeredSecondDifference_sub_secondDerivative_le
      (f := realDirichletPower s)
      (f' := realDirichletPowerDeriv s)
      (f'' := realDirichletPowerDeriv2 s)
      (f''' := realDirichletPowerDeriv3 s)
      (center := center) (radius := r)
      (C := ‖s * (s + 1) * (s + 2)‖ *
        (center - r) ^ (-s.re - 3))
      (by positivity)
      (fun x hx ↦ hasDerivAt_realDirichletPower hs0
        (hleft.trans_le hx.1))
      (fun x hx ↦ hasDerivAt_realDirichletPowerDeriv hs1
        (hleft.trans_le hx.1))
      (fun x hx ↦ hasDerivAt_realDirichletPowerDeriv2 hs2
        (hleft.trans_le hx.1))
      hthirdBound
  simpa [realCpPairBracket, center, r, mul_assoc] using hraw

/-- Generic local explicit-radius remainder bound. -/
theorem norm_nativeExplicitRadiusBracketRemainder_of_re_pos_le
    (b h k : ℕ) (hb : 1 ≤ b) (hh : h ≤ b - 1)
    {s : ℂ} (hs : 0 < s.re) :
    ‖nativeExplicitRadiusBracketRemainder b h k s‖ ≤
      2 * ‖s * (s + 1) * (s + 2)‖ *
        ((b - h : ℕ) : ℝ) ^ (-s.re - 3) *
        ((k + 1 : ℕ) : ℝ) ^ (-s.re - 3) *
        nativeRadiusThirdMoment h := by
  classical
  have hhB : h ≤ b := by omega
  have hgapNat : 1 ≤ b - h := by omega
  have hgapPos : 0 < ((b - h : ℕ) : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hgapNat)
  have hj : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  have hjPos : 0 < ((k + 1 : ℕ) : ℝ) := lt_of_lt_of_le zero_lt_one hj
  unfold nativeExplicitRadiusBracketRemainder
  rw [nativeExplicitRadiusBracketLeading_eq_sum_secondDerivative]
  unfold nativeExplicitRadiusBracket
  calc
    ‖(∑ radius ∈ Finset.Icc 1 h, realCpPairBracket b radius k s) -
        ∑ radius ∈ Finset.Icc 1 h,
          ((radius : ℝ) ^ 2) •
            realDirichletPowerDeriv2 s
              ((b : ℝ) * ((k + 1 : ℕ) : ℝ))‖ =
      ‖∑ radius ∈ Finset.Icc 1 h,
        (realCpPairBracket b radius k s -
          ((radius : ℝ) ^ 2) •
            realDirichletPowerDeriv2 s
              ((b : ℝ) * ((k + 1 : ℕ) : ℝ)))‖ := by
        congr 1
        rw [Finset.sum_sub_distrib]
    _ ≤ ∑ radius ∈ Finset.Icc 1 h,
        ‖realCpPairBracket b radius k s -
          ((radius : ℝ) ^ 2) •
            realDirichletPowerDeriv2 s
              ((b : ℝ) * ((k + 1 : ℕ) : ℝ))‖ := norm_sum_le _ _
    _ ≤ ∑ radius ∈ Finset.Icc 1 h,
        2 * ‖s * (s + 1) * (s + 2)‖ *
          ((b : ℝ) * ((k + 1 : ℕ) : ℝ) - (radius : ℝ)) ^
            (-s.re - 3) *
          (radius : ℝ) ^ 3 := by
      exact Finset.sum_le_sum fun radius hradius ↦
        norm_realCpPairBracket_sub_secondDerivative_of_re_pos_le
          b radius k hb
          (le_trans (Finset.mem_Icc.mp hradius).2 hh) hs
    _ ≤ ∑ radius ∈ Finset.Icc 1 h,
        (2 * ‖s * (s + 1) * (s + 2)‖ *
          ((b - h : ℕ) : ℝ) ^ (-s.re - 3) *
          ((k + 1 : ℕ) : ℝ) ^ (-s.re - 3)) *
          (radius : ℝ) ^ 3 := by
      apply Finset.sum_le_sum
      intro radius hradius
      have hrh : radius ≤ h := (Finset.mem_Icc.mp hradius).2
      have hrhReal : (radius : ℝ) ≤ (h : ℝ) := by exact_mod_cast hrh
      have hhNonneg : 0 ≤ (h : ℝ) := by positivity
      have hleftLower :
          ((b - h : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) ≤
            (b : ℝ) * ((k + 1 : ℕ) : ℝ) - (radius : ℝ) := by
        rw [Nat.cast_sub hhB]
        nlinarith [mul_nonneg hhNonneg (sub_nonneg.mpr hj)]
      have hlowerPos :
          0 < ((b - h : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) :=
        mul_pos hgapPos hjPos
      have hpower :
          ((b : ℝ) * ((k + 1 : ℕ) : ℝ) - (radius : ℝ)) ^
              (-s.re - 3) ≤
            (((b - h : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ)) ^
              (-s.re - 3) :=
        Real.rpow_le_rpow_of_nonpos hlowerPos hleftLower (by linarith)
      calc
        2 * ‖s * (s + 1) * (s + 2)‖ *
            ((b : ℝ) * ((k + 1 : ℕ) : ℝ) - (radius : ℝ)) ^
              (-s.re - 3) *
            (radius : ℝ) ^ 3 ≤
          2 * ‖s * (s + 1) * (s + 2)‖ *
            ((((b - h : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ)) ^
              (-s.re - 3)) *
            (radius : ℝ) ^ 3 := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpower (by positivity)) (by positivity)
        _ = (2 * ‖s * (s + 1) * (s + 2)‖ *
            ((b - h : ℕ) : ℝ) ^ (-s.re - 3) *
            ((k + 1 : ℕ) : ℝ) ^ (-s.re - 3)) *
            (radius : ℝ) ^ 3 := by
          rw [Real.mul_rpow hgapPos.le hjPos.le]
          ring
    _ = 2 * ‖s * (s + 1) * (s + 2)‖ *
        ((b - h : ℕ) : ℝ) ^ (-s.re - 3) *
        ((k + 1 : ℕ) : ℝ) ^ (-s.re - 3) *
        nativeRadiusThirdMoment h := by
      unfold nativeRadiusThirdMoment
      rw [Finset.mul_sum]


end

end GenuineZeroUniformAtlasEnergy

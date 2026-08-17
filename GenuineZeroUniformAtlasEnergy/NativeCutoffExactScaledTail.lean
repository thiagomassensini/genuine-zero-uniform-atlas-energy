import GenuineZeroUniformAtlasEnergy.NativeCutoffExactScaledTailScalar

/-!
# Exact scaled cutoff tail: pointwise analytic bound

Combines the scalar and Taylor defects and proves the exact pointwise `K(s)/M`
bound for the scaled tail.  Disk-uniform and Cauchy derivative bounds are added
in the next layer.
-/

open scoped BigOperators Function Topology

namespace GenuineZeroUniformAtlasEnergy

open CPFormal.Analytic.Cp
open Set MeasureTheory Metric

noncomputable section

attribute [local instance 10000] NormedSpace.complexToReal

lemma nativeExplicitRadiusTailRemainder_of_re_pos_eq
    (b h M : ℕ) (hb : 1 ≤ b) (hh : h ≤ b - 1)
    {s : ℂ} (hs : 0 < s.re) :
    nativeExplicitRadiusTailRemainder b h M s =
      nativeExplicitRadiusBlockCoefficient b h s *
        nativeExplicitRadiusScalarTailDefect M s +
      nativeExplicitRadiusAccumulatedBracketRemainder b h M s := by
  have hs1 : s + 1 ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp at hre
    linarith
  have hscalar := summable_nativeExplicitRadiusLeadingPower_of_re_pos M hs
  have hleading : Summable (fun k : ℕ ↦
      nativeExplicitRadiusBracketLeading b h (k + M) s) := by
    simpa [nativeExplicitRadiusBracketLeading, Nat.add_assoc] using
      hscalar.mul_left (nativeExplicitRadiusBlockCoefficient b h s)
  have hlocal :=
    summable_nativeExplicitRadiusBracketRemainder_of_re_pos
      b h M hb hh hs
  have hsplit :
      (∑' k : ℕ, nativeExplicitRadiusBracket b h (k + M) s) =
        (∑' k : ℕ, nativeExplicitRadiusBracketLeading b h (k + M) s) +
          ∑' k : ℕ,
            nativeExplicitRadiusBracketRemainder b h (k + M) s := by
    rw [← hleading.tsum_add hlocal]
    exact tsum_congr (fun k ↦
      nativeExplicitRadiusBracket_eq_leading_add_remainder
        b h (k + M) s)
  have hleadingTsum :
      (∑' k : ℕ, nativeExplicitRadiusBracketLeading b h (k + M) s) =
        nativeExplicitRadiusBlockCoefficient b h s *
          ∑' k : ℕ, (((k + M + 1 : ℕ) : ℂ) ^ (-s - 2)) := by
    simp only [nativeExplicitRadiusBracketLeading, Nat.add_assoc]
    rw [tsum_mul_left]
  unfold nativeExplicitRadiusTailRemainder nativeExplicitRadiusCutoffTail
    nativeExplicitRadiusScalarTailDefect
    nativeExplicitRadiusAccumulatedBracketRemainder
  rw [hsplit, hleadingTsum,
    ← nativeExplicitRadiusBlockCoefficient_div b h hs1]
  ring

lemma norm_nativeExplicitRadiusBlockCoefficient_of_re_pos
    (b h : ℕ) (hb : 1 ≤ b) (s : ℂ) :
    ‖nativeExplicitRadiusBlockCoefficient b h s‖ =
      ‖s * (s + 1)‖ * nativeRadiusSecondMoment h *
        (b : ℝ) ^ (-s.re - 2) := by
  have hbNat : 0 < b := lt_of_lt_of_le Nat.zero_lt_one hb
  have hbReal : 0 < (b : ℝ) := by exact_mod_cast hbNat
  have hbCast : (b : ℂ) = ((b : ℝ) : ℂ) := by norm_cast
  have hmoment : 0 ≤ nativeRadiusSecondMoment h := by
    unfold nativeRadiusSecondMoment
    positivity
  unfold nativeExplicitRadiusBlockCoefficient
  rw [norm_mul, norm_mul, hbCast,
    Complex.norm_cpow_eq_rpow_re_of_pos hbReal]
  have hexponent : (-s - 2).re = -s.re - 2 := by simp
  rw [hexponent, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hmoment]

/-- Pointwise `O(1/M)` bound for the exact scaled cutoff tail. -/
def nativeExplicitRadiusScaledTailPointConstant
    (b h : ℕ) (s : ℂ) : ℝ :=
  ‖s * (s + 1) * (s + 2)‖ *
    (nativeRadiusSecondMoment h * (b : ℝ) ^ (-s.re - 2) +
      2 * nativeRadiusThirdMoment h *
        ((b - h : ℕ) : ℝ) ^ (-s.re - 3)) / (s.re + 2)

/-- Generic unscaled tail remainder bound. -/
theorem norm_nativeExplicitRadiusTailRemainder_of_re_pos_le
    (b h M : ℕ) (hb : 1 ≤ b) (hh : h ≤ b - 1)
    (hM : 1 ≤ M) {s : ℂ} (hs : 0 < s.re) :
    ‖nativeExplicitRadiusTailRemainder b h M s‖ ≤
      nativeExplicitRadiusScaledTailPointConstant b h s *
        (M : ℝ) ^ (-(s.re + 2)) := by
  let q : ℝ := (M : ℝ) ^ (-(s.re + 2))
  have hsplit :=
    nativeExplicitRadiusTailRemainder_of_re_pos_eq
      b h M hb hh hs
  have hscalar :=
    norm_nativeExplicitRadiusScalarTailDefect_of_re_pos_le M hM hs
  have hacc :=
    norm_nativeExplicitRadiusAccumulatedBracketRemainder_of_re_pos_le
      b h M hb hh hM hs
  have hblock :=
    norm_nativeExplicitRadiusBlockCoefficient_of_re_pos b h hb s
  have hden : s.re + 2 ≠ 0 := by linarith
  rw [hsplit]
  calc
    ‖nativeExplicitRadiusBlockCoefficient b h s *
          nativeExplicitRadiusScalarTailDefect M s +
        nativeExplicitRadiusAccumulatedBracketRemainder b h M s‖ ≤
      ‖nativeExplicitRadiusBlockCoefficient b h s‖ *
          ‖nativeExplicitRadiusScalarTailDefect M s‖ +
        ‖nativeExplicitRadiusAccumulatedBracketRemainder b h M s‖ := by
      simpa only [norm_mul] using
        norm_add_le
          (nativeExplicitRadiusBlockCoefficient b h s *
            nativeExplicitRadiusScalarTailDefect M s)
          (nativeExplicitRadiusAccumulatedBracketRemainder b h M s)
    _ ≤ ‖nativeExplicitRadiusBlockCoefficient b h s‖ *
          ((‖s + 2‖ / (s.re + 2)) * q) +
        (2 * ‖s * (s + 1) * (s + 2)‖ *
          ((b - h : ℕ) : ℝ) ^ (-s.re - 3) *
          nativeRadiusThirdMoment h / (s.re + 2)) * q := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hscalar
          (norm_nonneg (nativeExplicitRadiusBlockCoefficient b h s)))
        (by simpa [q] using hacc)
    _ = nativeExplicitRadiusScaledTailPointConstant b h s * q := by
      rw [hblock]
      unfold nativeExplicitRadiusScaledTailPointConstant
      simp only [norm_mul]
      field_simp [hden]
      ring
    _ = nativeExplicitRadiusScaledTailPointConstant b h s *
        (M : ℝ) ^ (-(s.re + 2)) := by rfl

lemma nativeExplicitRadiusScaledTailError_eq_scaled_remainder
    (b h M : ℕ) (hM : 0 < M) (s : ℂ) :
    nativeExplicitRadiusScaledTailError b h M s =
      (M : ℂ) ^ (s + 1) *
        nativeExplicitRadiusTailRemainder b h M s := by
  have hMC : (M : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hM)
  have hcancel :
      (M : ℂ) ^ (s + 1) * (M : ℂ) ^ (-s - 1) = 1 := by
    rw [← Complex.cpow_add _ _ hMC]
    have hexponent : s + 1 + (-s - 1) = 0 := by ring
    rw [hexponent, Complex.cpow_zero]
  unfold nativeExplicitRadiusScaledTailError
    nativeExplicitRadiusScaledCutoffTail
    nativeExplicitRadiusTailRemainder
  calc
    (M : ℂ) ^ (s + 1) * nativeExplicitRadiusCutoffTail b h M s -
        nativeExplicitRadiusTailCoefficient b h s =
      (M : ℂ) ^ (s + 1) * nativeExplicitRadiusCutoffTail b h M s -
        nativeExplicitRadiusTailCoefficient b h s *
          ((M : ℂ) ^ (s + 1) * (M : ℂ) ^ (-s - 1)) := by
        rw [hcancel, mul_one]
    _ = (M : ℂ) ^ (s + 1) *
        (nativeExplicitRadiusCutoffTail b h M s -
          nativeExplicitRadiusTailCoefficient b h s *
            (M : ℂ) ^ (-s - 1)) := by ring

/-- Exact pointwise scaled value bound. -/
theorem norm_nativeExplicitRadiusScaledTailError_of_re_pos_le
    (b h M : ℕ) (hb : 1 ≤ b) (hh : h ≤ b - 1)
    (hM : 1 ≤ M) {s : ℂ} (hs : 0 < s.re) :
    ‖nativeExplicitRadiusScaledTailError b h M s‖ ≤
      nativeExplicitRadiusScaledTailPointConstant b h s / (M : ℝ) := by
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hrem :=
    norm_nativeExplicitRadiusTailRemainder_of_re_pos_le
      b h M hb hh hM hs
  have hscale :
      ‖(M : ℂ) ^ (s + 1)‖ = (M : ℝ) ^ (s.re + 1) := by
    have hnorm :=
      Complex.norm_cpow_eq_rpow_re_of_pos hMpos (s + 1)
    have hre : (s + 1).re = s.re + 1 := by simp
    simpa [hre] using hnorm
  have hpow :
      (M : ℝ) ^ (s.re + 1) *
          (M : ℝ) ^ (-(s.re + 2)) =
        (M : ℝ)⁻¹ := by
    rw [← Real.rpow_add hMpos]
    have hexp : s.re + 1 + -(s.re + 2) = (-1 : ℝ) := by ring
    rw [hexp, Real.rpow_neg_one]
  rw [nativeExplicitRadiusScaledTailError_eq_scaled_remainder
    b h M (by omega) s, norm_mul, hscale]
  calc
    (M : ℝ) ^ (s.re + 1) *
        ‖nativeExplicitRadiusTailRemainder b h M s‖ ≤
      (M : ℝ) ^ (s.re + 1) *
        (nativeExplicitRadiusScaledTailPointConstant b h s *
          (M : ℝ) ^ (-(s.re + 2))) :=
      mul_le_mul_of_nonneg_left hrem (Real.rpow_nonneg hMpos.le _)
    _ = nativeExplicitRadiusScaledTailPointConstant b h s *
        ((M : ℝ) ^ (s.re + 1) *
          (M : ℝ) ^ (-(s.re + 2))) := by ring
    _ = nativeExplicitRadiusScaledTailPointConstant b h s *
        (M : ℝ)⁻¹ := by rw [hpow]
    _ = nativeExplicitRadiusScaledTailPointConstant b h s / (M : ℝ) := by
      rw [div_eq_mul_inv]

end

end GenuineZeroUniformAtlasEnergy

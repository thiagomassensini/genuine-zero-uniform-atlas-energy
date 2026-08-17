import GenuineZeroUniformAtlasEnergy.NativeCutoffExactScaledTail
import Mathlib.Analysis.Complex.Liouville

/-!
# Exact scaled cutoff tail: holomorphy core

The exact explicit-radius block series is holomorphic on the radius-`1/2`
ball around every critical-line point.  The block family is dominated there
by a quadratic p-series, uniformly in the spectral parameter.
-/

open scoped BigOperators Function Topology

namespace GenuineZeroUniformAtlasEnergy

open CPFormal.Analytic.Cp
open Set MeasureTheory Metric

noncomputable section

attribute [local instance 10000] NormedSpace.complexToReal

/-- Outer holomorphy radius around a critical-line point. -/
def nativeExplicitRadiusCriticalOuterRadius : ℝ := 1 / 2

/-- Inner radius used by Cauchy's estimates. -/
def nativeExplicitRadiusCriticalCauchyRadius : ℝ := 1 / 4

lemma nativeRadiusSecondMoment_nonneg (h : ℕ) :
    0 ≤ nativeRadiusSecondMoment h := by
  unfold nativeRadiusSecondMoment
  positivity

lemma explicitRadius_natCast_add_one_le_center_sub_radius
    (b radius k : ℕ) (hb : 1 ≤ b) (hradius : radius ≤ b - 1) :
    ((k + 1 : ℕ) : ℝ) ≤
      (b : ℝ) * ((k + 1 : ℕ) : ℝ) - (radius : ℝ) := by
  have hbrNat : radius + 1 ≤ b := by omega
  have hbr : (radius : ℝ) + 1 ≤ (b : ℝ) := by
    exact_mod_cast hbrNat
  have hk : 1 ≤ ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  have hbOne : 1 ≤ (b : ℝ) := by exact_mod_cast hb
  nlinarith [mul_nonneg (sub_nonneg.mpr hbOne) (sub_nonneg.mpr hk)]

lemma differentiable_realCpPairBracket_explicit
    (b radius k : ℕ) (hb : 1 ≤ b) (hradius : radius ≤ b - 1) :
    Differentiable ℂ (realCpPairBracket b radius k) := by
  have hleftLower :=
    explicitRadius_natCast_add_one_le_center_sub_radius
      b radius k hb hradius
  have hkpos : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
  have hleft :
      0 < (b : ℝ) * ((k + 1 : ℕ) : ℝ) - (radius : ℝ) :=
    lt_of_lt_of_le hkpos hleftLower
  have hcenter : 0 < (b : ℝ) * ((k + 1 : ℕ) : ℝ) := by
    exact mul_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hb))
      (by positivity)
  have hright :
      0 < (b : ℝ) * ((k + 1 : ℕ) : ℝ) + (radius : ℝ) :=
    add_pos_of_pos_of_nonneg hcenter (by positivity)
  have hleftDiff :=
    differentiable_realDirichletPower_in_parameter (ne_of_gt hleft)
  have hcenterDiff :=
    differentiable_realDirichletPower_in_parameter (ne_of_gt hcenter)
  have hrightDiff :=
    differentiable_realDirichletPower_in_parameter (ne_of_gt hright)
  rw [show realCpPairBracket b radius k =
      ((fun s : ℂ ↦ realDirichletPower s
          ((b : ℝ) * ((k + 1 : ℕ) : ℝ) - (radius : ℝ))) -
        ((fun s : ℂ ↦ realDirichletPower s
            ((b : ℝ) * ((k + 1 : ℕ) : ℝ))) +
          (fun s : ℂ ↦ realDirichletPower s
            ((b : ℝ) * ((k + 1 : ℕ) : ℝ))))) +
        (fun s : ℂ ↦ realDirichletPower s
          ((b : ℝ) * ((k + 1 : ℕ) : ℝ) + (radius : ℝ))) by
    funext s
    simp [realCpPairBracket, two_smul]]
  exact (hleftDiff.sub (hcenterDiff.add hcenterDiff)).add hrightDiff

lemma differentiable_nativeExplicitRadiusBracket
    (b h k : ℕ) (hb : 1 ≤ b) (hh : h ≤ b - 1) :
    Differentiable ℂ (nativeExplicitRadiusBracket b h k) := by
  classical
  unfold nativeExplicitRadiusBracket
  exact Differentiable.fun_sum fun radius hradius ↦
    differentiable_realCpPairBracket_explicit b radius k hb
      (le_trans (Finset.mem_Icc.mp hradius).2 hh)

lemma norm_realCpPairBracket_explicit_le
    (b radius k : ℕ) (hb : 1 ≤ b) (hradius : radius ≤ b - 1)
    {s : ℂ} (hs : -1 < s.re) :
    ‖realCpPairBracket b radius k s‖ ≤
      (2 * ‖s * (s + 1)‖ * (radius : ℝ) ^ 2) *
        ((k + 1 : ℕ) : ℝ) ^ (-s.re - 2) := by
  have hleftLower :=
    explicitRadius_natCast_add_one_le_center_sub_radius
      b radius k hb hradius
  have hkpos : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
  have hleft :
      0 < (b : ℝ) * ((k + 1 : ℕ) : ℝ) - (radius : ℝ) :=
    lt_of_lt_of_le hkpos hleftLower
  have hraw := norm_realDirichletPower_centeredSecondDifference_le
    hs (show 0 ≤ (radius : ℝ) by positivity) hleft
  have hpower :
      ((b : ℝ) * ((k + 1 : ℕ) : ℝ) - (radius : ℝ)) ^
          (-s.re - 2) ≤
        ((k + 1 : ℕ) : ℝ) ^ (-s.re - 2) :=
    Real.rpow_le_rpow_of_nonpos hkpos hleftLower (by linarith [hs])
  calc
    ‖realCpPairBracket b radius k s‖ ≤
        2 *
          (‖s * (s + 1)‖ *
            ((b : ℝ) * ((k + 1 : ℕ) : ℝ) - (radius : ℝ)) ^
              (-s.re - 2)) *
          (radius : ℝ) ^ 2 := by
      simpa [realCpPairBracket] using hraw
    _ = (2 * ‖s * (s + 1)‖ * (radius : ℝ) ^ 2) *
          (((b : ℝ) * ((k + 1 : ℕ) : ℝ) - (radius : ℝ)) ^
            (-s.re - 2)) := by ring
    _ ≤ (2 * ‖s * (s + 1)‖ * (radius : ℝ) ^ 2) *
          ((k + 1 : ℕ) : ℝ) ^ (-s.re - 2) :=
      mul_le_mul_of_nonneg_left hpower (by positivity)

lemma norm_nativeExplicitRadiusBracket_of_re_gt_neg_one_le
    (b h k : ℕ) (hb : 1 ≤ b) (hh : h ≤ b - 1)
    {s : ℂ} (hs : -1 < s.re) :
    ‖nativeExplicitRadiusBracket b h k s‖ ≤
      (2 * ‖s * (s + 1)‖ * nativeRadiusSecondMoment h) *
        ((k + 1 : ℕ) : ℝ) ^ (-s.re - 2) := by
  classical
  unfold nativeExplicitRadiusBracket
  calc
    ‖∑ radius ∈ Finset.Icc 1 h, realCpPairBracket b radius k s‖ ≤
        ∑ radius ∈ Finset.Icc 1 h,
          ‖realCpPairBracket b radius k s‖ := norm_sum_le _ _
    _ ≤ ∑ radius ∈ Finset.Icc 1 h,
          (2 * ‖s * (s + 1)‖ * (radius : ℝ) ^ 2) *
            ((k + 1 : ℕ) : ℝ) ^ (-s.re - 2) := by
      exact Finset.sum_le_sum fun radius hradius ↦
        norm_realCpPairBracket_explicit_le b radius k hb
          (le_trans (Finset.mem_Icc.mp hradius).2 hh) hs
    _ = (∑ radius ∈ Finset.Icc 1 h,
          2 * ‖s * (s + 1)‖ * (radius : ℝ) ^ 2) *
            ((k + 1 : ℕ) : ℝ) ^ (-s.re - 2) := by
      rw [Finset.sum_mul]
    _ = (2 * ‖s * (s + 1)‖ * nativeRadiusSecondMoment h) *
          ((k + 1 : ℕ) : ℝ) ^ (-s.re - 2) := by
      unfold nativeRadiusSecondMoment
      rw [Finset.mul_sum]

lemma re_pos_of_mem_nativeExplicitRadiusCriticalOuterBall
    {time : ℝ} {s : ℂ}
    (hs : s ∈ ball (criticalLineParameter time)
      nativeExplicitRadiusCriticalOuterRadius) :
    0 < s.re := by
  have hdist :
      ‖s - criticalLineParameter time‖ <
        nativeExplicitRadiusCriticalOuterRadius := by
    simpa [dist_eq_norm] using hs
  have hreNorm :
      |s.re - (criticalLineParameter time).re| ≤
        ‖s - criticalLineParameter time‖ := by
    simpa using Complex.abs_re_le_norm (s - criticalLineParameter time)
  have hnegative :
      -‖s - criticalLineParameter time‖ ≤
        s.re - (criticalLineParameter time).re := by
    calc
      -‖s - criticalLineParameter time‖ ≤
          -|s.re - (criticalLineParameter time).re| := neg_le_neg hreNorm
      _ ≤ s.re - (criticalLineParameter time).re := neg_abs_le _
  have hcenter :
      (criticalLineParameter time).re = (1 : ℝ) / 2 := by
    simp [criticalLineParameter_re]
  change ‖s - criticalLineParameter time‖ < (1 : ℝ) / 2 at hdist
  linarith

def nativeExplicitRadiusCriticalOuterBlockConstant
    (h : ℕ) (time : ℝ) : ℝ :=
  2 * localQuadraticNormBound (criticalLineParameter time)
      nativeExplicitRadiusCriticalOuterRadius *
    nativeRadiusSecondMoment h

lemma nativeExplicitRadiusCriticalOuterBlockConstant_nonneg
    (h : ℕ) (time : ℝ) :
    0 ≤ nativeExplicitRadiusCriticalOuterBlockConstant h time := by
  have hmoment := nativeRadiusSecondMoment_nonneg h
  have hlocal :
      0 ≤ localQuadraticNormBound (criticalLineParameter time)
        nativeExplicitRadiusCriticalOuterRadius := by
    unfold localQuadraticNormBound nativeExplicitRadiusCriticalOuterRadius
    positivity
  unfold nativeExplicitRadiusCriticalOuterBlockConstant
  positivity

lemma summable_nativeExplicitRadiusCriticalOuterMajorant
    (h : ℕ) (time : ℝ) :
    Summable (fun k : ℕ ↦
      nativeExplicitRadiusCriticalOuterBlockConstant h time *
        ((k + 1 : ℕ) : ℝ) ^ (-2 : ℝ)) := by
  have hpower :=
    summable_nat_add_one_rpow_neg_sub_two (a := (0 : ℝ)) (by norm_num)
  simpa using hpower.mul_left
    (nativeExplicitRadiusCriticalOuterBlockConstant h time)

lemma norm_nativeExplicitRadiusBracket_shift_criticalOuter_le
    (b h M k : ℕ) (hb : 1 ≤ b) (hh : h ≤ b - 1)
    {time : ℝ} {s : ℂ}
    (hs : s ∈ ball (criticalLineParameter time)
      nativeExplicitRadiusCriticalOuterRadius) :
    ‖nativeExplicitRadiusBracket b h (k + M) s‖ ≤
      nativeExplicitRadiusCriticalOuterBlockConstant h time *
        ((k + 1 : ℕ) : ℝ) ^ (-2 : ℝ) := by
  have hsre : 0 < s.re :=
    re_pos_of_mem_nativeExplicitRadiusCriticalOuterBall hs
  have hpoint :=
    norm_nativeExplicitRadiusBracket_of_re_gt_neg_one_le
      b h (k + M) hb hh (by linarith)
  have hquad :=
    norm_mul_add_one_le_localQuadraticNormBound
      (z := criticalLineParameter time) (w := s)
      (R := nativeExplicitRadiusCriticalOuterRadius)
      (by unfold nativeExplicitRadiusCriticalOuterRadius; norm_num) hs
  have hmoment : 0 ≤ nativeRadiusSecondMoment h :=
    nativeRadiusSecondMoment_nonneg h
  have hC :
      0 ≤ nativeExplicitRadiusCriticalOuterBlockConstant h time :=
    nativeExplicitRadiusCriticalOuterBlockConstant_nonneg h time
  have hkpos : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
  have hkone : 1 ≤ ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  have hshift :
      ((k + 1 : ℕ) : ℝ) ≤ (((k + M) + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show k + 1 ≤ (k + M) + 1 by omega)
  have hpowerShift :
      (((k + M) + 1 : ℕ) : ℝ) ^ (-s.re - 2) ≤
        ((k + 1 : ℕ) : ℝ) ^ (-s.re - 2) :=
    Real.rpow_le_rpow_of_nonpos hkpos hshift (by linarith)
  have hpowerExponent :
      ((k + 1 : ℕ) : ℝ) ^ (-s.re - 2) ≤
        ((k + 1 : ℕ) : ℝ) ^ (-2 : ℝ) :=
    Real.monotone_rpow_of_base_ge_one hkone (by linarith)
  calc
    ‖nativeExplicitRadiusBracket b h (k + M) s‖ ≤
        (2 * ‖s * (s + 1)‖ * nativeRadiusSecondMoment h) *
          (((k + M) + 1 : ℕ) : ℝ) ^ (-s.re - 2) := hpoint
    _ ≤ (2 * localQuadraticNormBound (criticalLineParameter time)
          nativeExplicitRadiusCriticalOuterRadius *
          nativeRadiusSecondMoment h) *
        (((k + M) + 1 : ℕ) : ℝ) ^ (-s.re - 2) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hquad (by norm_num)) hmoment)
        (Real.rpow_nonneg (by positivity) _)
    _ ≤ nativeExplicitRadiusCriticalOuterBlockConstant h time *
        ((k + 1 : ℕ) : ℝ) ^ (-s.re - 2) := by
      exact mul_le_mul_of_nonneg_left hpowerShift hC
    _ ≤ nativeExplicitRadiusCriticalOuterBlockConstant h time *
        ((k + 1 : ℕ) : ℝ) ^ (-2 : ℝ) :=
      mul_le_mul_of_nonneg_left hpowerExponent hC

lemma differentiableOn_nativeExplicitRadiusCutoffTail_criticalOuterBall
    (b h M : ℕ) (hb : 1 ≤ b) (hh : h ≤ b - 1) (time : ℝ) :
    DifferentiableOn ℂ (nativeExplicitRadiusCutoffTail b h M)
      (ball (criticalLineParameter time)
        nativeExplicitRadiusCriticalOuterRadius) := by
  let u : ℕ → ℝ := fun k ↦
    nativeExplicitRadiusCriticalOuterBlockConstant h time *
      ((k + 1 : ℕ) : ℝ) ^ (-2 : ℝ)
  have hu : Summable u := by
    simpa [u] using
      summable_nativeExplicitRadiusCriticalOuterMajorant h time
  unfold nativeExplicitRadiusCutoffTail
  apply Complex.differentiableOn_tsum_of_summable_norm hu
  · intro k
    exact (differentiable_nativeExplicitRadiusBracket
      b h (k + M) hb hh).differentiableOn
  · exact isOpen_ball
  · intro k s hs
    simpa [u] using
      norm_nativeExplicitRadiusBracket_shift_criticalOuter_le
        b h M k hb hh hs

end

end GenuineZeroUniformAtlasEnergy

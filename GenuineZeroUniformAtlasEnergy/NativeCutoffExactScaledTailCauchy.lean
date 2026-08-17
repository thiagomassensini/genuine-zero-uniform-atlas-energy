import GenuineZeroUniformAtlasEnergy.NativeCutoffExactScaledTail
import Mathlib.Analysis.Complex.Liouville

/-!
# Exact scaled cutoff tail: value and derivative bounds

The pointwise `O(1/M)` estimate is made uniform on the critical Cauchy circle
of radius `1/4` around `1/2 + it`.  Holomorphy is proved on the larger ball of
radius `1/2`, where every point still has positive real part and the block
series is dominated by a quadratic p-series.  Cauchy's estimate then gives
explicit bounds for the value and the first two complex derivatives.
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

lemma differentiable_nativeExplicitRadiusScaledFactor
    (M : ℕ) (hM : 1 ≤ M) :
    Differentiable ℂ (fun s : ℂ ↦ (M : ℂ) ^ (s + 1)) := by
  have hM0 : M ≠ 0 := by omega
  intro s
  have hinner :
      HasDerivAt (fun z : ℂ ↦ z + 1) 1 s := by
    simpa using (hasDerivAt_id' s).const_add 1
  exact (hinner.const_cpow
    (Or.inl (Nat.cast_ne_zero.mpr hM0))).differentiableAt

lemma differentiable_nativeExplicitRadiusTailCoefficient
    (b h : ℕ) (hb : 1 ≤ b) :
    Differentiable ℂ (nativeExplicitRadiusTailCoefficient b h) := by
  have hb0 : b ≠ 0 := by omega
  intro s
  have hinner :
      HasDerivAt (fun z : ℂ ↦ -z - 2) (-1) s := by
    simpa using (hasDerivAt_neg' s).sub_const 2
  have hpower := hinner.const_cpow
    (Or.inl (Nat.cast_ne_zero.mpr hb0))
  have hlinear :
      HasDerivAt
        (fun z : ℂ ↦ z * (nativeRadiusSecondMoment h : ℂ))
        (nativeRadiusSecondMoment h : ℂ) s := by
    simpa using
      (hasDerivAt_id' s).mul_const (nativeRadiusSecondMoment h : ℂ)
  simpa [nativeExplicitRadiusTailCoefficient] using
    (hlinear.mul hpower).differentiableAt

lemma differentiableOn_nativeExplicitRadiusScaledTailError_criticalOuterBall
    (b h M : ℕ) (hb : 1 ≤ b) (hh : h ≤ b - 1)
    (hM : 1 ≤ M) (time : ℝ) :
    DifferentiableOn ℂ (nativeExplicitRadiusScaledTailError b h M)
      (ball (criticalLineParameter time)
        nativeExplicitRadiusCriticalOuterRadius) := by
  have hscale :=
    (differentiable_nativeExplicitRadiusScaledFactor M hM).differentiableOn
  have htail :=
    differentiableOn_nativeExplicitRadiusCutoffTail_criticalOuterBall
      b h M hb hh time
  have hcoefficient :=
    (differentiable_nativeExplicitRadiusTailCoefficient b h hb).differentiableOn
  simpa [nativeExplicitRadiusScaledTailError,
    nativeExplicitRadiusScaledCutoffTail] using
      (hscale.mul htail).sub hcoefficient

/-- Uniform norm bound used on the critical Cauchy circle. -/
def nativeExplicitRadiusCriticalCauchyNormBound (time : ℝ) : ℝ :=
  ‖criticalLineParameter time‖ + nativeExplicitRadiusCriticalCauchyRadius

/-- Explicit circle constant.  The base powers are bounded by one on
`Re(s)>0`; the geometric moments remain visible. -/
def nativeExplicitRadiusScaledTailCriticalCauchyConstant
    (h : ℕ) (time : ℝ) : ℝ :=
  nativeExplicitRadiusCriticalCauchyNormBound time *
    (nativeExplicitRadiusCriticalCauchyNormBound time + 1) *
    (nativeExplicitRadiusCriticalCauchyNormBound time + 2) *
    (nativeRadiusSecondMoment h + 2 * nativeRadiusThirdMoment h)

lemma nativeExplicitRadiusScaledTailCriticalCauchyConstant_nonneg
    (h : ℕ) (time : ℝ) :
    0 ≤ nativeExplicitRadiusScaledTailCriticalCauchyConstant h time := by
  have hsecond := nativeRadiusSecondMoment_nonneg h
  have hthird := nativeRadiusThirdMoment_nonneg h
  unfold nativeExplicitRadiusScaledTailCriticalCauchyConstant
    nativeExplicitRadiusCriticalCauchyNormBound
    nativeExplicitRadiusCriticalCauchyRadius
  positivity

lemma nativeExplicitRadiusCriticalCauchyClosedBall_subset_outerBall
    (time : ℝ) :
    closedBall (criticalLineParameter time)
        nativeExplicitRadiusCriticalCauchyRadius ⊆
      ball (criticalLineParameter time)
        nativeExplicitRadiusCriticalOuterRadius := by
  intro s hs
  have hdist :
      dist s (criticalLineParameter time) ≤
        nativeExplicitRadiusCriticalCauchyRadius := by
    simpa using hs
  change dist s (criticalLineParameter time) < (1 : ℝ) / 2
  change dist s (criticalLineParameter time) ≤ (1 : ℝ) / 4 at hdist
  linarith

lemma one_quarter_le_re_of_mem_nativeExplicitRadiusCriticalCauchyClosedBall
    {time : ℝ} {s : ℂ}
    (hs : s ∈ closedBall (criticalLineParameter time)
      nativeExplicitRadiusCriticalCauchyRadius) :
    (1 : ℝ) / 4 ≤ s.re := by
  have hdist :
      ‖s - criticalLineParameter time‖ ≤
        nativeExplicitRadiusCriticalCauchyRadius := by
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
  change ‖s - criticalLineParameter time‖ ≤ (1 : ℝ) / 4 at hdist
  linarith

lemma norm_le_nativeExplicitRadiusCriticalCauchyNormBound
    {time : ℝ} {s : ℂ}
    (hs : s ∈ closedBall (criticalLineParameter time)
      nativeExplicitRadiusCriticalCauchyRadius) :
    ‖s‖ ≤ nativeExplicitRadiusCriticalCauchyNormBound time := by
  have hdist :
      ‖s - criticalLineParameter time‖ ≤
        nativeExplicitRadiusCriticalCauchyRadius := by
    simpa [dist_eq_norm] using hs
  calc
    ‖s‖ = ‖(s - criticalLineParameter time) +
        criticalLineParameter time‖ := by ring_nf
    _ ≤ ‖s - criticalLineParameter time‖ +
        ‖criticalLineParameter time‖ := norm_add_le _ _
    _ ≤ nativeExplicitRadiusCriticalCauchyRadius +
        ‖criticalLineParameter time‖ :=
      add_le_add_right hdist _
    _ = nativeExplicitRadiusCriticalCauchyNormBound time := by
      unfold nativeExplicitRadiusCriticalCauchyNormBound
      ring

lemma norm_add_one_le_nativeExplicitRadiusCriticalCauchyNormBound
    {time : ℝ} {s : ℂ}
    (hs : s ∈ closedBall (criticalLineParameter time)
      nativeExplicitRadiusCriticalCauchyRadius) :
    ‖s + 1‖ ≤ nativeExplicitRadiusCriticalCauchyNormBound time + 1 := by
  calc
    ‖s + 1‖ ≤ ‖s‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    _ ≤ nativeExplicitRadiusCriticalCauchyNormBound time + 1 := by
      norm_num
      exact add_le_add_right
        (norm_le_nativeExplicitRadiusCriticalCauchyNormBound hs) 1

lemma norm_add_two_le_nativeExplicitRadiusCriticalCauchyNormBound
    {time : ℝ} {s : ℂ}
    (hs : s ∈ closedBall (criticalLineParameter time)
      nativeExplicitRadiusCriticalCauchyRadius) :
    ‖s + 2‖ ≤ nativeExplicitRadiusCriticalCauchyNormBound time + 2 := by
  calc
    ‖s + 2‖ ≤ ‖s‖ + ‖(2 : ℂ)‖ := norm_add_le _ _
    _ ≤ nativeExplicitRadiusCriticalCauchyNormBound time + 2 := by
      norm_num
      exact add_le_add_right
        (norm_le_nativeExplicitRadiusCriticalCauchyNormBound hs) 2

lemma nativeExplicitRadiusScaledTailPointConstant_le_criticalCauchyConstant
    (b h : ℕ) (hb : 1 ≤ b) (hh : h ≤ b - 1)
    {time : ℝ} {s : ℂ}
    (hs : s ∈ closedBall (criticalLineParameter time)
      nativeExplicitRadiusCriticalCauchyRadius) :
    nativeExplicitRadiusScaledTailPointConstant b h s ≤
      nativeExplicitRadiusScaledTailCriticalCauchyConstant h time := by
  have hsreLower :=
    one_quarter_le_re_of_mem_nativeExplicitRadiusCriticalCauchyClosedBall hs
  have hsre : 0 < s.re := by linarith
  have hnorm := norm_le_nativeExplicitRadiusCriticalCauchyNormBound hs
  have hnormOne :=
    norm_add_one_le_nativeExplicitRadiusCriticalCauchyNormBound hs
  have hnormTwo :=
    norm_add_two_le_nativeExplicitRadiusCriticalCauchyNormBound hs
  let A : ℝ := nativeExplicitRadiusCriticalCauchyNormBound time
  have hA : 0 ≤ A := by
    dsimp [A, nativeExplicitRadiusCriticalCauchyNormBound,
      nativeExplicitRadiusCriticalCauchyRadius]
    positivity
  have hAOne : 0 ≤ A + 1 := by linarith
  have hAProduct : 0 ≤ A * (A + 1) := mul_nonneg hA hAOne
  have hpair : ‖s‖ * ‖s + 1‖ ≤ A * (A + 1) := by
    calc
      ‖s‖ * ‖s + 1‖ ≤ A * ‖s + 1‖ :=
        mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
      _ ≤ A * (A + 1) :=
        mul_le_mul_of_nonneg_left hnormOne hA
  have htriple :
      ‖s * (s + 1) * (s + 2)‖ ≤ A * (A + 1) * (A + 2) := by
    simp only [norm_mul]
    calc
      ‖s‖ * ‖s + 1‖ * ‖s + 2‖ ≤
          (A * (A + 1)) * ‖s + 2‖ :=
        mul_le_mul_of_nonneg_right hpair (norm_nonneg _)
      _ ≤ (A * (A + 1)) * (A + 2) :=
        mul_le_mul_of_nonneg_left hnormTwo hAProduct
  have hbOne : 1 ≤ (b : ℝ) := by exact_mod_cast hb
  have hbPower :
      (b : ℝ) ^ (-s.re - 2) ≤ 1 := by
    have h := Real.monotone_rpow_of_base_ge_one hbOne
      (show -s.re - 2 ≤ (0 : ℝ) by linarith)
    simpa using h
  have hgapNat : 1 ≤ b - h := by omega
  have hgapOne : 1 ≤ ((b - h : ℕ) : ℝ) := by exact_mod_cast hgapNat
  have hgapPower :
      ((b - h : ℕ) : ℝ) ^ (-s.re - 3) ≤ 1 := by
    have h := Real.monotone_rpow_of_base_ge_one hgapOne
      (show -s.re - 3 ≤ (0 : ℝ) by linarith)
    simpa using h
  have hsecond : 0 ≤ nativeRadiusSecondMoment h :=
    nativeRadiusSecondMoment_nonneg h
  have hthird : 0 ≤ nativeRadiusThirdMoment h :=
    nativeRadiusThirdMoment_nonneg h
  have hmoment :
      nativeRadiusSecondMoment h * (b : ℝ) ^ (-s.re - 2) +
          2 * nativeRadiusThirdMoment h *
            ((b - h : ℕ) : ℝ) ^ (-s.re - 3) ≤
        nativeRadiusSecondMoment h + 2 * nativeRadiusThirdMoment h := by
    calc
      nativeRadiusSecondMoment h * (b : ℝ) ^ (-s.re - 2) +
          2 * nativeRadiusThirdMoment h *
            ((b - h : ℕ) : ℝ) ^ (-s.re - 3) ≤
        nativeRadiusSecondMoment h * 1 +
          (2 * nativeRadiusThirdMoment h) * 1 :=
        add_le_add
          (mul_le_mul_of_nonneg_left hbPower hsecond)
          (mul_le_mul_of_nonneg_left hgapPower
            (mul_nonneg (by norm_num) hthird))
      _ = nativeRadiusSecondMoment h +
          2 * nativeRadiusThirdMoment h := by ring
  have hmomentNonneg :
      0 ≤ nativeRadiusSecondMoment h * (b : ℝ) ^ (-s.re - 2) +
          2 * nativeRadiusThirdMoment h *
            ((b - h : ℕ) : ℝ) ^ (-s.re - 3) := by positivity
  have hproduct :
      ‖s * (s + 1) * (s + 2)‖ *
          (nativeRadiusSecondMoment h * (b : ℝ) ^ (-s.re - 2) +
            2 * nativeRadiusThirdMoment h *
              ((b - h : ℕ) : ℝ) ^ (-s.re - 3)) ≤
        (A * (A + 1) * (A + 2)) *
          (nativeRadiusSecondMoment h + 2 * nativeRadiusThirdMoment h) := by
    calc
      ‖s * (s + 1) * (s + 2)‖ *
          (nativeRadiusSecondMoment h * (b : ℝ) ^ (-s.re - 2) +
            2 * nativeRadiusThirdMoment h *
              ((b - h : ℕ) : ℝ) ^ (-s.re - 3)) ≤
        (A * (A + 1) * (A + 2)) *
          (nativeRadiusSecondMoment h * (b : ℝ) ^ (-s.re - 2) +
            2 * nativeRadiusThirdMoment h *
              ((b - h : ℕ) : ℝ) ^ (-s.re - 3)) :=
        mul_le_mul_of_nonneg_right htriple hmomentNonneg
      _ ≤ (A * (A + 1) * (A + 2)) *
          (nativeRadiusSecondMoment h + 2 * nativeRadiusThirdMoment h) :=
        mul_le_mul_of_nonneg_left hmoment
          (mul_nonneg hAProduct (by linarith))
  have hproductNonneg :
      0 ≤ ‖s * (s + 1) * (s + 2)‖ *
          (nativeRadiusSecondMoment h * (b : ℝ) ^ (-s.re - 2) +
            2 * nativeRadiusThirdMoment h *
              ((b - h : ℕ) : ℝ) ^ (-s.re - 3)) := by positivity
  have hdenOne : 1 ≤ s.re + 2 := by linarith
  have hdenPos : 0 < s.re + 2 := by linarith
  unfold nativeExplicitRadiusScaledTailPointConstant
  calc
    ‖s * (s + 1) * (s + 2)‖ *
        (nativeRadiusSecondMoment h * (b : ℝ) ^ (-s.re - 2) +
          2 * nativeRadiusThirdMoment h *
            ((b - h : ℕ) : ℝ) ^ (-s.re - 3)) / (s.re + 2) ≤
      ‖s * (s + 1) * (s + 2)‖ *
        (nativeRadiusSecondMoment h * (b : ℝ) ^ (-s.re - 2) +
          2 * nativeRadiusThirdMoment h *
            ((b - h : ℕ) : ℝ) ^ (-s.re - 3)) := by
      apply (div_le_iff₀ hdenPos).2
      nlinarith [mul_nonneg hproductNonneg (sub_nonneg.mpr hdenOne)]
    _ ≤ (A * (A + 1) * (A + 2)) *
        (nativeRadiusSecondMoment h + 2 * nativeRadiusThirdMoment h) := hproduct
    _ = nativeExplicitRadiusScaledTailCriticalCauchyConstant h time := by
      unfold nativeExplicitRadiusScaledTailCriticalCauchyConstant
      dsimp [A]

lemma norm_nativeExplicitRadiusScaledTailError_criticalSphere_le
    (b h M : ℕ) (hb : 1 ≤ b) (hh : h ≤ b - 1)
    (hM : 1 ≤ M) (time : ℝ)
    (s : ℂ)
    (hs : s ∈ sphere (criticalLineParameter time)
      nativeExplicitRadiusCriticalCauchyRadius) :
    ‖nativeExplicitRadiusScaledTailError b h M s‖ ≤
      nativeExplicitRadiusScaledTailCriticalCauchyConstant h time / (M : ℝ) := by
  have hclosed :
      s ∈ closedBall (criticalLineParameter time)
        nativeExplicitRadiusCriticalCauchyRadius :=
    sphere_subset_closedBall hs
  have hsreLower :=
    one_quarter_le_re_of_mem_nativeExplicitRadiusCriticalCauchyClosedBall hclosed
  have hpoint :=
    norm_nativeExplicitRadiusScaledTailError_of_re_pos_le
      b h M hb hh hM (by linarith)
  have hconstant :=
    nativeExplicitRadiusScaledTailPointConstant_le_criticalCauchyConstant
      b h hb hh hclosed
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  exact hpoint.trans ((div_le_div_iff_of_pos_right hMpos).2 hconstant)

lemma norm_iteratedDeriv_nativeExplicitRadiusScaledTailError_critical_le
    (n b h M : ℕ) (hb : 1 ≤ b) (hh : h ≤ b - 1)
    (hM : 1 ≤ M) (time : ℝ) :
    ‖iteratedDeriv n (nativeExplicitRadiusScaledTailError b h M)
        (criticalLineParameter time)‖ ≤
      n.factorial *
          (nativeExplicitRadiusScaledTailCriticalCauchyConstant h time /
            (M : ℝ)) /
        nativeExplicitRadiusCriticalCauchyRadius ^ n := by
  have hdiffOuter :=
    differentiableOn_nativeExplicitRadiusScaledTailError_criticalOuterBall
      b h M hb hh hM time
  have hsubset :=
    nativeExplicitRadiusCriticalCauchyClosedBall_subset_outerBall time
  have hdiff :
      DiffContOnCl ℂ (nativeExplicitRadiusScaledTailError b h M)
        (ball (criticalLineParameter time)
          nativeExplicitRadiusCriticalCauchyRadius) :=
    hdiffOuter.diffContOnCl_ball hsubset
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    n (by unfold nativeExplicitRadiusCriticalCauchyRadius; norm_num)
    hdiff (fun s hs ↦
      norm_nativeExplicitRadiusScaledTailError_criticalSphere_le
        b h M hb hh hM time s hs)

/-- Zeroth analytic bound for the exact scaled cutoff tail. -/
theorem norm_nativeExplicitRadiusScaledTailError_critical_value_le
    (b h M : ℕ) (hb : 1 ≤ b) (hh : h ≤ b - 1)
    (hM : 1 ≤ M) (time : ℝ) :
    ‖nativeExplicitRadiusScaledTailError b h M
        (criticalLineParameter time)‖ ≤
      nativeExplicitRadiusScaledTailCriticalCauchyConstant h time / (M : ℝ) := by
  simpa using
    (norm_iteratedDeriv_nativeExplicitRadiusScaledTailError_critical_le
      0 b h M hb hh hM time)

/-- First analytic derivative bound.  The denominator is the Cauchy radius
`1/4`, hence this is exactly four times the value-circle majorant. -/
theorem norm_nativeExplicitRadiusScaledTailError_critical_first_le
    (b h M : ℕ) (hb : 1 ≤ b) (hh : h ≤ b - 1)
    (hM : 1 ≤ M) (time : ℝ) :
    ‖iteratedDeriv 1 (nativeExplicitRadiusScaledTailError b h M)
        (criticalLineParameter time)‖ ≤
      (nativeExplicitRadiusScaledTailCriticalCauchyConstant h time /
        (M : ℝ)) /
      nativeExplicitRadiusCriticalCauchyRadius := by
  simpa using
    (norm_iteratedDeriv_nativeExplicitRadiusScaledTailError_critical_le
      1 b h M hb hh hM time)

/-- Second analytic derivative bound.  Cauchy contributes the exact factorial
`2` and the square of the radius. -/
theorem norm_nativeExplicitRadiusScaledTailError_critical_second_le
    (b h M : ℕ) (hb : 1 ≤ b) (hh : h ≤ b - 1)
    (hM : 1 ≤ M) (time : ℝ) :
    ‖iteratedDeriv 2 (nativeExplicitRadiusScaledTailError b h M)
        (criticalLineParameter time)‖ ≤
      2 * (nativeExplicitRadiusScaledTailCriticalCauchyConstant h time /
        (M : ℝ)) /
      nativeExplicitRadiusCriticalCauchyRadius ^ 2 := by
  simpa using
    (norm_iteratedDeriv_nativeExplicitRadiusScaledTailError_critical_le
      2 b h M hb hh hM time)

/-- The three requested analytic bounds in one kernel-checked package. -/
theorem nativeExplicitRadiusScaledTailError_critical_three_bounds
    (b h M : ℕ) (hb : 1 ≤ b) (hh : h ≤ b - 1)
    (hM : 1 ≤ M) (time : ℝ) :
    ‖nativeExplicitRadiusScaledTailError b h M
        (criticalLineParameter time)‖ ≤
        nativeExplicitRadiusScaledTailCriticalCauchyConstant h time / (M : ℝ) ∧
      ‖iteratedDeriv 1 (nativeExplicitRadiusScaledTailError b h M)
          (criticalLineParameter time)‖ ≤
        (nativeExplicitRadiusScaledTailCriticalCauchyConstant h time /
          (M : ℝ)) /
        nativeExplicitRadiusCriticalCauchyRadius ∧
      ‖iteratedDeriv 2 (nativeExplicitRadiusScaledTailError b h M)
          (criticalLineParameter time)‖ ≤
        2 * (nativeExplicitRadiusScaledTailCriticalCauchyConstant h time /
          (M : ℝ)) /
        nativeExplicitRadiusCriticalCauchyRadius ^ 2 := by
  exact ⟨
    norm_nativeExplicitRadiusScaledTailError_critical_value_le
      b h M hb hh hM time,
    norm_nativeExplicitRadiusScaledTailError_critical_first_le
      b h M hb hh hM time,
    norm_nativeExplicitRadiusScaledTailError_critical_second_le
      b h M hb hh hM time⟩

end

end GenuineZeroUniformAtlasEnergy

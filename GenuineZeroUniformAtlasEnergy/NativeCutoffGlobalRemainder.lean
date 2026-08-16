import GenuineZeroUniformAtlasEnergy.NativeCutoffAsymptotic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Global accumulation of the critical local cutoff remainder

`NativeCutoffAsymptotic` proves that one explicit-radius block differs from
its quadratic leading term by `O((k+1)^(-7/2))` on the critical line.  This
module performs the missing infinite summation of that already-audited local
remainder.

For every positive cutoff `M`, the accumulated Taylor part is bounded by an
explicit multiple of

```math
M^{-5/2}.
```

After multiplying a resonant finite residue by the natural critical scale
`M^(3/2)`, this contribution is therefore `O(1/M)`.  The separate scalar
sum-versus-primitive defect of the leading complex p-series is not hidden in
this theorem and remains the next term required for the complete named tail
remainder.
-/

open scoped BigOperators Function

namespace GenuineZeroUniformAtlasEnergy

open CPFormal.Analytic.Cp
open Set MeasureTheory

noncomputable section

/-- Infinite accumulation of the local Taylor remainders after cutoff `M`. -/
def nativeExplicitRadiusAccumulatedBracketRemainder
    (b h M : ℕ) (s : ℂ) : ℂ :=
  ∑' k : ℕ, nativeExplicitRadiusBracketRemainder b h (k + M) s

/-- Explicit critical-line bound for the accumulated local Taylor remainder. -/
def nativeExplicitRadiusAccumulatedBracketRemainderBound
    (b h M : ℕ) (time : ℝ) : ℝ :=
  (4 / 5 : ℝ) *
    ‖criticalLineParameter time * (criticalLineParameter time + 1) *
      (criticalLineParameter time + 2)‖ *
    ((b - h : ℕ) : ℝ) ^ (-(7 / 2 : ℝ)) *
    nativeRadiusThirdMoment h *
    (M : ℝ) ^ (-(5 / 2 : ℝ))

lemma nativeRadiusThirdMoment_nonneg (h : ℕ) :
    0 ≤ nativeRadiusThirdMoment h := by
  unfold nativeRadiusThirdMoment
  positivity

/-- Integral-test bound for the shifted `7/2`-power tail. -/
lemma criticalSevenHalves_tsum_le
    (M : ℕ) (hM : 1 ≤ M) :
    (∑' k : ℕ,
      ((k : ℝ) + (M : ℝ) + 1) ^ (-(7 / 2 : ℝ))) ≤
      (2 / 5 : ℝ) * (M : ℝ) ^ (-(5 / 2 : ℝ)) := by
  have hMpos : 0 < (M : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)
  let f : ℝ → ℝ := fun x => x ^ (-(7 / 2 : ℝ))
  have hanti : AntitoneOn f (Ici (M : ℝ)) := by
    intro x hx y _hy hxy
    dsimp [f]
    exact Real.rpow_le_rpow_of_nonpos
      (lt_of_lt_of_le hMpos (mem_Ici.mp hx)) hxy (by norm_num)
  have hintegrable : IntegrableOn f (Ioi (M : ℝ)) := by
    dsimp [f]
    exact integrableOn_Ioi_rpow_of_lt (by norm_num) hMpos
  have hnonneg : ∀ x ∈ Ioi (M : ℝ), 0 ≤ f x := by
    intro x hx
    dsimp [f]
    exact Real.rpow_nonneg (le_of_lt (hMpos.trans (mem_Ioi.mp hx))) _
  calc
    (∑' k : ℕ,
      ((k : ℝ) + (M : ℝ) + 1) ^ (-(7 / 2 : ℝ))) ≤
        ∫ x in Ioi (M : ℝ), x ^ (-(7 / 2 : ℝ)) := by
      simpa [f, Nat.cast_add] using
        hanti.tsum_comp_add_le_integral M hintegrable hnonneg
    _ = -(M : ℝ) ^ (-(7 / 2 : ℝ) + 1) /
          (-(7 / 2 : ℝ) + 1) :=
      integral_Ioi_rpow_of_lt (by norm_num) hMpos
    _ = (2 / 5 : ℝ) * (M : ℝ) ^ (-(5 / 2 : ℝ)) := by
      norm_num
      ring

lemma summable_criticalSevenHalves_shifted (M : ℕ) :
    Summable (fun k : ℕ =>
      ((k : ℝ) + (M : ℝ) + 1) ^ (-(7 / 2 : ℝ))) := by
  have hraw : Summable (fun n : ℕ =>
      (n : ℝ) ^ (-(7 / 2 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hbase : Summable (fun k : ℕ =>
      ((k : ℝ) + 1) ^ (-(7 / 2 : ℝ))) := by
    have hshift := hraw.comp_injective
      (show Function.Injective (fun n : ℕ => n + 1) by
        intro a b hab
        exact Nat.add_right_cancel hab)
    simpa [Function.comp_def, Nat.cast_add] using hshift
  refine Summable.of_nonneg_of_le
    (fun k => Real.rpow_nonneg (by positivity) _) ?_ hbase
  intro k
  have hleft : 0 < (k : ℝ) + 1 := by positivity
  have hMnonneg : 0 ≤ (M : ℝ) := by positivity
  have hle : (k : ℝ) + 1 ≤ (k : ℝ) + (M : ℝ) + 1 := by
    linarith
  exact Real.rpow_le_rpow_of_nonpos hleft hle (by norm_num)

lemma summable_nativeExplicitRadiusBracketRemainder_critical
    (b h M : ℕ) (hb : 1 ≤ b) (hh : h ≤ b - 1) (time : ℝ) :
    Summable (fun k : ℕ =>
      nativeExplicitRadiusBracketRemainder b h (k + M)
        (criticalLineParameter time)) := by
  let C : ℝ :=
    2 *
      ‖criticalLineParameter time * (criticalLineParameter time + 1) *
        (criticalLineParameter time + 2)‖ *
      ((b - h : ℕ) : ℝ) ^ (-(7 / 2 : ℝ)) *
      nativeRadiusThirdMoment h
  have hpower := summable_criticalSevenHalves_shifted M
  have hmajorant : Summable (fun k : ℕ =>
      C * ((k : ℝ) + (M : ℝ) + 1) ^ (-(7 / 2 : ℝ))) :=
    hpower.mul_left C
  exact hmajorant.of_norm_bounded (fun k => by
    have hlocal :=
      norm_nativeExplicitRadiusBracketRemainder_critical_le
        b h (k + M) hb hh time
    calc
      ‖nativeExplicitRadiusBracketRemainder b h (k + M)
          (criticalLineParameter time)‖ ≤
        2 *
          ‖criticalLineParameter time * (criticalLineParameter time + 1) *
            (criticalLineParameter time + 2)‖ *
          ((b - h : ℕ) : ℝ) ^ (-(7 / 2 : ℝ)) *
          (((k + M + 1 : ℕ) : ℝ)) ^ (-(7 / 2 : ℝ)) *
          nativeRadiusThirdMoment h := hlocal
      _ = C *
          ((k : ℝ) + (M : ℝ) + 1) ^ (-(7 / 2 : ℝ)) := by
        simp [C, Nat.cast_add]
        ring)

/-- The local cubic Taylor errors sum to an explicit global
`O(M^(-5/2))` remainder on the critical line. -/
theorem norm_nativeExplicitRadiusAccumulatedBracketRemainder_critical_le
    (b h M : ℕ) (hb : 1 ≤ b) (hh : h ≤ b - 1)
    (hM : 1 ≤ M) (time : ℝ) :
    ‖nativeExplicitRadiusAccumulatedBracketRemainder b h M
        (criticalLineParameter time)‖ ≤
      nativeExplicitRadiusAccumulatedBracketRemainderBound b h M time := by
  let C : ℝ :=
    2 *
      ‖criticalLineParameter time * (criticalLineParameter time + 1) *
        (criticalLineParameter time + 2)‖ *
      ((b - h : ℕ) : ℝ) ^ (-(7 / 2 : ℝ)) *
      nativeRadiusThirdMoment h
  have hpower := summable_criticalSevenHalves_shifted M
  have hmajorantHasSum :
      HasSum
        (fun k : ℕ =>
          C * ((k : ℝ) + (M : ℝ) + 1) ^ (-(7 / 2 : ℝ)))
        (C * ∑' k : ℕ,
          ((k : ℝ) + (M : ℝ) + 1) ^ (-(7 / 2 : ℝ))) :=
    hpower.hasSum.mul_left C
  have hpointwise : ∀ k : ℕ,
      ‖nativeExplicitRadiusBracketRemainder b h (k + M)
          (criticalLineParameter time)‖ ≤
        C * ((k : ℝ) + (M : ℝ) + 1) ^ (-(7 / 2 : ℝ)) := by
    intro k
    have hlocal :=
      norm_nativeExplicitRadiusBracketRemainder_critical_le
        b h (k + M) hb hh time
    calc
      ‖nativeExplicitRadiusBracketRemainder b h (k + M)
          (criticalLineParameter time)‖ ≤
        2 *
          ‖criticalLineParameter time * (criticalLineParameter time + 1) *
            (criticalLineParameter time + 2)‖ *
          ((b - h : ℕ) : ℝ) ^ (-(7 / 2 : ℝ)) *
          (((k + M + 1 : ℕ) : ℝ)) ^ (-(7 / 2 : ℝ)) *
          nativeRadiusThirdMoment h := hlocal
      _ = C *
          ((k : ℝ) + (M : ℝ) + 1) ^ (-(7 / 2 : ℝ)) := by
        simp [C, Nat.cast_add]
        ring
  have hnorm :
      ‖∑' k : ℕ,
          nativeExplicitRadiusBracketRemainder b h (k + M)
            (criticalLineParameter time)‖ ≤
        C * ∑' k : ℕ,
          ((k : ℝ) + (M : ℝ) + 1) ^ (-(7 / 2 : ℝ)) :=
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
  calc
    ‖nativeExplicitRadiusAccumulatedBracketRemainder b h M
        (criticalLineParameter time)‖ =
        ‖∑' k : ℕ,
          nativeExplicitRadiusBracketRemainder b h (k + M)
            (criticalLineParameter time)‖ := by rfl
    _ ≤ C * ∑' k : ℕ,
        ((k : ℝ) + (M : ℝ) + 1) ^ (-(7 / 2 : ℝ)) := hnorm
    _ ≤ C * ((2 / 5 : ℝ) * (M : ℝ) ^ (-(5 / 2 : ℝ))) :=
      mul_le_mul_of_nonneg_left (criticalSevenHalves_tsum_le M hM) hC
    _ = nativeExplicitRadiusAccumulatedBracketRemainderBound b h M time := by
      unfold nativeExplicitRadiusAccumulatedBracketRemainderBound
      dsimp [C]
      ring

/-- Scalar sum-versus-primitive defect of the critical leading block model. -/
def nativeExplicitRadiusScalarTailDefect
    (M : ℕ) (s : ℂ) : ℂ :=
  (∑' k : ℕ, (((k + M + 1 : ℕ) : ℂ) ^ (-s - 2))) -
    (M : ℂ) ^ (-s - 1) / (s + 1)

lemma summable_criticalFiveHalves_shifted (M : ℕ) :
    Summable (fun k : ℕ =>
      ((k : ℝ) + (M : ℝ) + 1) ^ (-(5 / 2 : ℝ))) := by
  have hraw : Summable (fun n : ℕ =>
      (n : ℝ) ^ (-(5 / 2 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hbase : Summable (fun k : ℕ =>
      ((k : ℝ) + 1) ^ (-(5 / 2 : ℝ))) := by
    have hshift := hraw.comp_injective
      (show Function.Injective (fun n : ℕ => n + 1) by
        intro a b hab
        exact Nat.add_right_cancel hab)
    simpa [Function.comp_def, Nat.cast_add] using hshift
  refine Summable.of_nonneg_of_le
    (fun k => Real.rpow_nonneg (by positivity) _) ?_ hbase
  intro k
  have hleft : 0 < (k : ℝ) + 1 := by positivity
  have hMnonneg : 0 ≤ (M : ℝ) := by positivity
  have hle : (k : ℝ) + 1 ≤ (k : ℝ) + (M : ℝ) + 1 := by
    linarith
  exact Real.rpow_le_rpow_of_nonpos hleft hle (by norm_num)

lemma summable_nativeExplicitRadiusLeadingPower_critical
    (M : ℕ) (time : ℝ) :
    Summable (fun k : ℕ =>
      (((k + M + 1 : ℕ) : ℂ) ^
        (-criticalLineParameter time - 2))) := by
  have hpower := summable_criticalFiveHalves_shifted M
  exact hpower.of_norm_bounded (fun k => by
    rw [Complex.norm_natCast_cpow_of_pos (by omega)]
    have hexponent :
        (-criticalLineParameter time - 2).re = -(5 / 2 : ℝ) := by
      simp only [Complex.sub_re, Complex.neg_re, criticalLineParameter_re]
      norm_num
    rw [hexponent]
    norm_num [Nat.cast_add])

lemma norm_nativeExplicitRadiusScalarTailDefect_critical_le
    (M : ℕ) (hM : 1 ≤ M) (time : ℝ) :
    ‖nativeExplicitRadiusScalarTailDefect M
        (criticalLineParameter time)‖ ≤
      (2 / 5 : ℝ) * ‖criticalLineParameter time + 2‖ *
        (M : ℝ) ^ (-(5 / 2 : ℝ)) := by
  let s : ℂ := criticalLineParameter time
  let q : ℂ := -s - 2
  let F : ℝ → ℂ := fun x => (x : ℂ) ^ q
  let F' : ℝ → ℂ := fun x => q * (x : ℂ) ^ (q - 1)
  let left : ℕ → ℝ := fun k => (M : ℝ) + (k : ℝ)
  let cell : ℕ → Set ℝ :=
    fun k => Ioc (left k) (left (Nat.succ k))
  let seq : ℕ → ℂ := fun k => F (left (Nat.succ k))
  let weighted : ℕ → ℝ → ℂ :=
    fun k x => ((x - left k : ℝ) : ℂ) * F' x
  let err : ℕ → ℂ :=
    fun k => ∫ x in cell k, weighted k x
  let g : ℝ → ℝ :=
    fun x => ‖s + 2‖ * x ^ (-(7 / 2 : ℝ))
  have hs_re : s.re = (1 : ℝ) / 2 := by
    simp [s, criticalLineParameter_re]
  have hq_re : q.re = -(5 / 2 : ℝ) := by
    dsimp [q]
    simp only [hs_re]
    norm_num
  have hq_sub_one_re : (q - 1).re = -(7 / 2 : ℝ) := by
    rw [Complex.sub_re, hq_re]
    norm_num
  have hq_lt : q.re < -1 := by
    rw [hq_re]
    norm_num
  have hq_ne : q ≠ 0 := by
    intro hqzero
    have hre := congrArg Complex.re hqzero
    rw [hq_re] at hre
    norm_num at hre
  have hq_norm : ‖q‖ = ‖s + 2‖ := by
    have hq : q = -(s + 2) := by
      dsimp [q]
      ring
    rw [hq, norm_neg]
  have hMpos : 0 < (M : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)
  have hleft_mono : Monotone left := by
    intro i j hij
    dsimp [left]
    have hijReal : (i : ℝ) ≤ (j : ℝ) := by
      exact_mod_cast hij
    exact add_le_add_left hijReal (M : ℝ)
  have hleft_succ (k : ℕ) :
      left (Nat.succ k) = left k + 1 := by
    dsimp [left]
    push_cast
    ring
  have hleft_pos (k : ℕ) : 0 < left k := by
    dsimp [left]
    exact add_pos_of_pos_of_nonneg hMpos (Nat.cast_nonneg k)
  have hleft_le_succ (k : ℕ) :
      left k ≤ left (Nat.succ k) :=
    hleft_mono (Nat.le_succ k)
  have hleft_unbounded : ¬ BddAbove (Set.range left) := by
    rw [not_bddAbove_iff]
    intro x
    obtain ⟨k, hk⟩ := exists_nat_gt (x - (M : ℝ))
    refine ⟨left k, ⟨k, rfl⟩, ?_⟩
    dsimp [left]
    linarith
  have hcells_union :
      (⋃ k : ℕ, cell k) = Ioi (M : ℝ) := by
    have hcover :=
      iUnion_Ioc_map_succ_eq_Ioi
        (f := left)
        (fun k => hleft_mono (Nat.zero_le k))
        hleft_unbounded
    simpa [cell, left] using hcover
  have hcells_disjoint :
      Pairwise (Disjoint on cell) := by
    simpa [cell] using
      hleft_mono.pairwise_disjoint_on_Ioc_succ
  have hF_integrable :
      IntegrableOn F (Ioi (M : ℝ)) := by
    simpa [F] using
      integrableOn_Ioi_cpow_of_lt
        (a := q) hq_lt hMpos
  have hg_integrable :
      IntegrableOn g (Ioi (M : ℝ)) := by
    change Integrable
      (fun x : ℝ => ‖s + 2‖ * x ^ (-(7 / 2 : ℝ)))
      (volume.restrict (Ioi (M : ℝ)))
    exact (integrableOn_Ioi_rpow_of_lt
      (a := -(7 / 2 : ℝ)) (by norm_num) hMpos).const_mul
        ‖s + 2‖
  have hF_union :
      IntegrableOn F (⋃ k : ℕ, cell k) := by
    rw [hcells_union]
    exact hF_integrable
  have hg_union :
      IntegrableOn g (⋃ k : ℕ, cell k) := by
    rw [hcells_union]
    exact hg_integrable
  have hF_cells :
      HasSum
        (fun k : ℕ => ∫ x in cell k, F x)
        (∫ x in Ioi (M : ℝ), F x) := by
    have h :=
      MeasureTheory.hasSum_integral_iUnion
        (f := F) (μ := volume) (s := cell)
        (fun _ => measurableSet_Ioc)
        hcells_disjoint hF_union
    simpa only [hcells_union] using h
  have hg_cells :
      HasSum
        (fun k : ℕ => ∫ x in cell k, g x)
        (∫ x in Ioi (M : ℝ), g x) := by
    have h :=
      MeasureTheory.hasSum_integral_iUnion
        (f := g) (μ := volume) (s := cell)
        (fun _ => measurableSet_Ioc)
        hcells_disjoint hg_union
    simpa only [hcells_union] using h
  have hF_deriv (x : ℝ) (hx : 0 < x) :
      HasDerivAt F (F' x) x := by
    dsimp [F, F']
    exact hasDerivAt_ofReal_cpow_const hx.ne' hq_ne
  have hFprime_intervalIntegrable (k : ℕ) :
      IntervalIntegrable F' volume
        (left k) (left (Nat.succ k)) := by
    apply ContinuousOn.intervalIntegrable_of_Icc
      (hleft_le_succ k)
    intro x hx
    have hxpos : 0 < x :=
      (hleft_pos k).trans_le hx.1
    have hp :
        ContinuousAt
          (fun y : ℝ => (y : ℂ) ^ (q - 1)) x :=
      Complex.continuousAt_ofReal_cpow_const
        x (q - 1) (Or.inr hxpos.ne')
    have hc :
        ContinuousAt (fun _ : ℝ => q) x :=
      continuousAt_const
    dsimp [F']
    exact (hc.mul hp).continuousWithinAt
  have herr_eq (k : ℕ) :
      err k =
        seq k - ∫ x in cell k, F x := by
    have hparts :=
      intervalIntegral.integral_mul_deriv_eq_deriv_mul
        (a := left k) (b := left (Nat.succ k))
        (u := fun x : ℝ => ((x - left k : ℝ) : ℂ))
        (v := F)
        (u' := fun _ : ℝ => (1 : ℂ))
        (v' := F')
        (fun x _hx => by
          simpa using
            ((hasDerivAt_id x).sub_const (left k)).ofReal_comp)
        (fun x hx => by
          have hxIcc :
              x ∈ Icc (left k) (left (Nat.succ k)) := by
            simpa only [uIcc_of_le (hleft_le_succ k)] using hx
          exact hF_deriv x
            ((hleft_pos k).trans_le hxIcc.1))
        (intervalIntegrable_const :
          IntervalIntegrable
            (fun _ : ℝ => (1 : ℂ)) volume
            (left k) (left (Nat.succ k)))
        (hFprime_intervalIntegrable k)
    rw [intervalIntegral.integral_of_le (hleft_le_succ k),
      intervalIntegral.integral_of_le (hleft_le_succ k)] at hparts
    simpa [err, weighted, seq, cell, hleft_succ k] using hparts
  have hnorm_Fprime (x : ℝ) (hx : 0 < x) :
      ‖F' x‖ =
        ‖s + 2‖ * x ^ (-(7 / 2 : ℝ)) := by
    dsimp [F']
    rw [norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hx,
      hq_norm, hq_sub_one_re]
  have hweighted_le
      (k : ℕ) (x : ℝ) (hx : x ∈ cell k) :
      ‖weighted k x‖ ≤ g x := by
    have hxpos : 0 < x :=
      (hleft_pos k).trans hx.1
    have hnonneg : 0 ≤ x - left k :=
      sub_nonneg.mpr hx.1.le
    have hleone : x - left k ≤ 1 := by
      have hxright := hx.2
      rw [hleft_succ k] at hxright
      linarith
    dsimp [weighted]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hnonneg, hnorm_Fprime x hxpos]
    dsimp [g]
    calc
      (x - left k) *
          (‖s + 2‖ * x ^ (-(7 / 2 : ℝ))) ≤
        1 * (‖s + 2‖ * x ^ (-(7 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_right hleone (by positivity)
      _ = ‖s + 2‖ * x ^ (-(7 / 2 : ℝ)) := one_mul _
  have hM_le_left (k : ℕ) :
      (M : ℝ) ≤ left k := by
    dsimp [left]
    exact le_add_of_nonneg_right (Nat.cast_nonneg k)
  have hcell_subset (k : ℕ) :
      cell k ⊆ Ioi (M : ℝ) := by
    intro x hx
    exact (hM_le_left k).trans_lt hx.1
  have herr_bound (k : ℕ) :
      ‖err k‖ ≤ ∫ x in cell k, g x := by
    dsimp [err]
    exact MeasureTheory.norm_integral_le_of_norm_le
      (hg_integrable.mono_set (hcell_subset k))
      (ae_restrict_of_forall_mem measurableSet_Ioc
        (fun x hx => hweighted_le k x hx))
  have herr_norm_summable :
      Summable (fun k : ℕ => ‖err k‖) :=
    Summable.of_nonneg_of_le
      (fun _ => norm_nonneg _)
      herr_bound
      hg_cells.summable
  have herr_summable : Summable err :=
    herr_norm_summable.of_norm
  have hseq_hasSum :
      HasSum seq
        ((∑' k : ℕ, err k) +
          ∫ x in Ioi (M : ℝ), F x) := by
    refine (herr_summable.hasSum.add hF_cells).congr_fun ?_
    intro k
    rw [herr_eq k]
    ring
  have hdiff :
      (∑' k : ℕ, seq k) -
          (∫ x in Ioi (M : ℝ), F x) =
        ∑' k : ℕ, err k := by
    rw [hseq_hasSum.tsum_eq]
    ring
  have hF_eval :
      (∫ x in Ioi (M : ℝ), F x) =
        (M : ℂ) ^ (-s - 1) / (s + 1) := by
    calc
      (∫ x in Ioi (M : ℝ), F x) =
          -(M : ℂ) ^ (q + 1) / (q + 1) := by
        simpa [F] using
          integral_Ioi_cpow_of_lt
            (a := q) hq_lt hMpos
      _ = (M : ℂ) ^ (-s - 1) / (s + 1) := by
        have hq1 : q + 1 = -s - 1 := by
          dsimp [q]
          ring
        have hs1 : -s - 1 = -(s + 1) := by ring
        rw [hq1, hs1, neg_div_neg_eq]
  have hseq_apply (k : ℕ) :
      seq k =
        (((k + M + 1 : ℕ) : ℂ) ^
          (-criticalLineParameter time - 2)) := by
    dsimp [seq, F, left, q, s]
    congr 1
    push_cast
    ring
  have hseq_tsum :
      (∑' k : ℕ, seq k) =
        ∑' k : ℕ,
          (((k + M + 1 : ℕ) : ℂ) ^
            (-criticalLineParameter time - 2)) := by
    apply tsum_congr
    exact hseq_apply
  have htarget := hdiff
  rw [hF_eval, hseq_tsum] at htarget
  have htarget' :
      (∑' k : ℕ,
          (((k + M + 1 : ℕ) : ℂ) ^
            (-criticalLineParameter time - 2))) -
        (M : ℂ) ^ (-criticalLineParameter time - 1) /
          (criticalLineParameter time + 1) =
        ∑' k : ℕ, err k := by
    simpa [s] using htarget
  have hg_eval :
      (∫ x in Ioi (M : ℝ), g x) =
        (2 / 5 : ℝ) * ‖s + 2‖ *
          (M : ℝ) ^ (-(5 / 2 : ℝ)) := by
    dsimp [g]
    rw [MeasureTheory.integral_const_mul,
      integral_Ioi_rpow_of_lt
        (a := -(7 / 2 : ℝ)) (by norm_num) hMpos]
    norm_num
    ring
  unfold nativeExplicitRadiusScalarTailDefect
  rw [htarget']
  calc
    ‖∑' k : ℕ, err k‖ ≤
        ∫ x in Ioi (M : ℝ), g x :=
      tsum_of_norm_bounded hg_cells herr_bound
    _ = (2 / 5 : ℝ) *
          ‖criticalLineParameter time + 2‖ *
          (M : ℝ) ^ (-(5 / 2 : ℝ)) := by
      simpa [s] using hg_eval

/-- On the critical line, the complete named tail remainder is exactly the
sum of the scalar leading-series defect and the accumulated local Taylor
remainder. -/
lemma nativeExplicitRadiusTailRemainder_critical_eq
    (b h M : ℕ) (hb : 1 ≤ b) (hh : h ≤ b - 1) (time : ℝ) :
    nativeExplicitRadiusTailRemainder b h M
        (criticalLineParameter time) =
      nativeExplicitRadiusBlockCoefficient b h
          (criticalLineParameter time) *
        nativeExplicitRadiusScalarTailDefect M
          (criticalLineParameter time) +
      nativeExplicitRadiusAccumulatedBracketRemainder b h M
        (criticalLineParameter time) := by
  let s : ℂ := criticalLineParameter time
  have hs1 : s + 1 ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    norm_num [s, criticalLineParameter_re] at hre
  have hscalar : Summable (fun k : ℕ =>
      (((k + M + 1 : ℕ) : ℂ) ^ (-s - 2))) := by
    simpa [s] using
      summable_nativeExplicitRadiusLeadingPower_critical M time
  have hleading : Summable (fun k : ℕ =>
      nativeExplicitRadiusBracketLeading b h (k + M) s) := by
    simpa [nativeExplicitRadiusBracketLeading, Nat.add_assoc] using
      hscalar.mul_left (nativeExplicitRadiusBlockCoefficient b h s)
  have hlocal : Summable (fun k : ℕ =>
      nativeExplicitRadiusBracketRemainder b h (k + M) s) := by
    simpa [s] using
      summable_nativeExplicitRadiusBracketRemainder_critical
        b h M hb hh time
  have hsplit :
      (∑' k : ℕ, nativeExplicitRadiusBracket b h (k + M) s) =
        (∑' k : ℕ, nativeExplicitRadiusBracketLeading b h (k + M) s) +
          ∑' k : ℕ,
            nativeExplicitRadiusBracketRemainder b h (k + M) s := by
    rw [← hleading.tsum_add hlocal]
    exact tsum_congr (fun k =>
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
  change
    (∑' k : ℕ, nativeExplicitRadiusBracket b h (k + M) s) -
        nativeExplicitRadiusTailCoefficient b h s *
          (M : ℂ) ^ (-s - 1) = _
  rw [hsplit, hleadingTsum,
    ← nativeExplicitRadiusBlockCoefficient_div b h hs1]
  ring

end

end GenuineZeroUniformAtlasEnergy

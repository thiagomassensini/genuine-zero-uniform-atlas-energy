import GenuineZeroUniformAtlasEnergy.NativeCutoffExactScaledTailSummation

/-!
# Exact scaled cutoff tail: scalar complex defect

The generic sum-versus-primitive defect on `Re(s)>0`.
-/

open scoped BigOperators Function Topology

namespace GenuineZeroUniformAtlasEnergy

open CPFormal.Analytic.Cp
open Set MeasureTheory Metric

noncomputable section

attribute [local instance 10000] NormedSpace.complexToReal
lemma summable_nativeExplicitRadiusLeadingPower_of_re_pos
    (M : ℕ) {s : ℂ} (hs : 0 < s.re) :
    Summable (fun k : ℕ ↦
      (((k + M + 1 : ℕ) : ℂ) ^ (-s - 2))) := by
  have hpower : Summable (fun k : ℕ ↦
      ((k : ℝ) + (M : ℝ) + 1) ^ (-s.re - 2)) := by
    have hraw : Summable (fun n : ℕ ↦ (n : ℝ) ^ (-s.re - 2)) :=
      Real.summable_nat_rpow.mpr (by linarith)
    have hbase : Summable (fun k : ℕ ↦
        ((k : ℝ) + 1) ^ (-s.re - 2)) := by
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
    have hle : (k : ℝ) + 1 ≤ (k : ℝ) + (M : ℝ) + 1 := by
      linarith
    exact Real.rpow_le_rpow_of_nonpos hleft hle (by linarith)
  exact hpower.of_norm_bounded (fun k ↦ by
    rw [Complex.norm_natCast_cpow_of_pos (by omega)]
    have hexponent : (-s - 2).re = -s.re - 2 := by simp
    rw [hexponent]
    norm_num [Nat.cast_add])

/-- Generic scalar sum-versus-primitive estimate. -/
theorem norm_nativeExplicitRadiusScalarTailDefect_of_re_pos_le
    (M : ℕ) (hM : 1 ≤ M) {s : ℂ} (hs : 0 < s.re) :
    ‖nativeExplicitRadiusScalarTailDefect M s‖ ≤
      (‖s + 2‖ / (s.re + 2)) *
        (M : ℝ) ^ (-(s.re + 2)) := by
  let q : ℂ := -s - 2
  let F : ℝ → ℂ := fun x ↦ (x : ℂ) ^ q
  let F' : ℝ → ℂ := fun x ↦ q * (x : ℂ) ^ (q - 1)
  let left : ℕ → ℝ := fun k ↦ (M : ℝ) + (k : ℝ)
  let cell : ℕ → Set ℝ := fun k ↦ Ioc (left k) (left (Nat.succ k))
  let seq : ℕ → ℂ := fun k ↦ F (left (Nat.succ k))
  let weighted : ℕ → ℝ → ℂ :=
    fun k x ↦ ((x - left k : ℝ) : ℂ) * F' x
  let err : ℕ → ℂ := fun k ↦ ∫ x in cell k, weighted k x
  let g : ℝ → ℝ := fun x ↦ ‖s + 2‖ * x ^ (-s.re - 3)
  have hq_re : q.re = -s.re - 2 := by
    simp [q]
  have hq_sub_one_re : (q - 1).re = -s.re - 3 := by
    rw [Complex.sub_re, hq_re, Complex.one_re]
    ring
  have hq_lt : q.re < -1 := by rw [hq_re]; linarith
  have hq_ne : q ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    rw [hq_re] at hre
    simp at hre
    linarith
  have hq_norm : ‖q‖ = ‖s + 2‖ := by
    have hq : q = -(s + 2) := by dsimp [q]; ring
    rw [hq, norm_neg]
  have hMpos : 0 < (M : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)
  have hleft_mono : Monotone left := by
    intro i j hij
    have hijReal : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    dsimp [left]
    exact add_le_add_left hijReal (M : ℝ)
  have hleft_succ (k : ℕ) : left (Nat.succ k) = left k + 1 := by
    dsimp [left]
    push_cast
    ring
  have hleft_pos (k : ℕ) : 0 < left k := by
    dsimp [left]
    exact add_pos_of_pos_of_nonneg hMpos (Nat.cast_nonneg k)
  have hleft_le_succ (k : ℕ) : left k ≤ left (Nat.succ k) :=
    hleft_mono (Nat.le_succ k)
  have hleft_unbounded : ¬ BddAbove (Set.range left) := by
    rw [not_bddAbove_iff]
    intro x
    obtain ⟨k, hk⟩ := exists_nat_gt (x - (M : ℝ))
    refine ⟨left k, ⟨k, rfl⟩, ?_⟩
    dsimp [left]
    linarith
  have hcells_union : (⋃ k : ℕ, cell k) = Ioi (M : ℝ) := by
    have hcover :=
      iUnion_Ioc_map_succ_eq_Ioi
        (f := left)
        (fun k ↦ hleft_mono (Nat.zero_le k))
        hleft_unbounded
    simpa [cell, left] using hcover
  have hcells_disjoint : Pairwise (Disjoint on cell) := by
    simpa [cell] using hleft_mono.pairwise_disjoint_on_Ioc_succ
  have hF_integrable : IntegrableOn F (Ioi (M : ℝ)) := by
    simpa [F] using integrableOn_Ioi_cpow_of_lt
      (a := q) hq_lt hMpos
  have hg_integrable : IntegrableOn g (Ioi (M : ℝ)) := by
    change Integrable
      (fun x : ℝ ↦ ‖s + 2‖ * x ^ (-s.re - 3))
      (volume.restrict (Ioi (M : ℝ)))
    exact (integrableOn_Ioi_rpow_of_lt
      (a := -s.re - 3) (by linarith) hMpos).const_mul ‖s + 2‖
  have hF_union : IntegrableOn F (⋃ k : ℕ, cell k) := by
    rw [hcells_union]
    exact hF_integrable
  have hg_union : IntegrableOn g (⋃ k : ℕ, cell k) := by
    rw [hcells_union]
    exact hg_integrable
  have hF_cells :
      HasSum (fun k : ℕ ↦ ∫ x in cell k, F x)
        (∫ x in Ioi (M : ℝ), F x) := by
    have h := MeasureTheory.hasSum_integral_iUnion
      (f := F) (μ := volume) (s := cell)
      (fun _ ↦ measurableSet_Ioc) hcells_disjoint hF_union
    simpa only [hcells_union] using h
  have hg_cells :
      HasSum (fun k : ℕ ↦ ∫ x in cell k, g x)
        (∫ x in Ioi (M : ℝ), g x) := by
    have h := MeasureTheory.hasSum_integral_iUnion
      (f := g) (μ := volume) (s := cell)
      (fun _ ↦ measurableSet_Ioc) hcells_disjoint hg_union
    simpa only [hcells_union] using h
  have hF_deriv (x : ℝ) (hx : 0 < x) : HasDerivAt F (F' x) x := by
    dsimp [F, F']
    exact hasDerivAt_ofReal_cpow_const hx.ne' hq_ne
  have hFprime_intervalIntegrable (k : ℕ) :
      IntervalIntegrable F' volume (left k) (left (Nat.succ k)) := by
    apply ContinuousOn.intervalIntegrable_of_Icc (hleft_le_succ k)
    intro x hx
    have hxpos : 0 < x := (hleft_pos k).trans_le hx.1
    have hp : ContinuousAt (fun y : ℝ ↦ (y : ℂ) ^ (q - 1)) x :=
      Complex.continuousAt_ofReal_cpow_const
        x (q - 1) (Or.inr hxpos.ne')
    have hc : ContinuousAt (fun _ : ℝ ↦ q) x := continuousAt_const
    dsimp [F']
    exact (hc.mul hp).continuousWithinAt
  have herr_eq (k : ℕ) :
      err k = seq k - ∫ x in cell k, F x := by
    have hparts :=
      intervalIntegral.integral_mul_deriv_eq_deriv_mul
        (a := left k) (b := left (Nat.succ k))
        (u := fun x : ℝ ↦ ((x - left k : ℝ) : ℂ))
        (v := F)
        (u' := fun _ : ℝ ↦ (1 : ℂ))
        (v' := F')
        (fun x _hx ↦ by
          simpa using ((hasDerivAt_id x).sub_const (left k)).ofReal_comp)
        (fun x hx ↦ by
          have hxIcc : x ∈ Icc (left k) (left (Nat.succ k)) := by
            simpa only [uIcc_of_le (hleft_le_succ k)] using hx
          exact hF_deriv x ((hleft_pos k).trans_le hxIcc.1))
        (intervalIntegrable_const :
          IntervalIntegrable (fun _ : ℝ ↦ (1 : ℂ)) volume
            (left k) (left (Nat.succ k)))
        (hFprime_intervalIntegrable k)
    rw [intervalIntegral.integral_of_le (hleft_le_succ k),
      intervalIntegral.integral_of_le (hleft_le_succ k)] at hparts
    simpa [err, weighted, seq, cell, hleft_succ k] using hparts
  have hnorm_Fprime (x : ℝ) (hx : 0 < x) :
      ‖F' x‖ = ‖s + 2‖ * x ^ (-s.re - 3) := by
    dsimp [F']
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx,
      hq_norm, hq_sub_one_re]
  have hweighted_le (k : ℕ) (x : ℝ) (hx : x ∈ cell k) :
      ‖weighted k x‖ ≤ g x := by
    have hxpos : 0 < x := (hleft_pos k).trans hx.1
    have hnonneg : 0 ≤ x - left k := sub_nonneg.mpr hx.1.le
    have hleone : x - left k ≤ 1 := by
      have hxright := hx.2
      rw [hleft_succ k] at hxright
      linarith
    dsimp [weighted]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hnonneg, hnorm_Fprime x hxpos]
    dsimp [g]
    calc
      (x - left k) * (‖s + 2‖ * x ^ (-s.re - 3)) ≤
          1 * (‖s + 2‖ * x ^ (-s.re - 3)) :=
        mul_le_mul_of_nonneg_right hleone (by positivity)
      _ = ‖s + 2‖ * x ^ (-s.re - 3) := one_mul _
  have hM_le_left (k : ℕ) : (M : ℝ) ≤ left k := by
    dsimp [left]
    exact le_add_of_nonneg_right (Nat.cast_nonneg k)
  have hcell_subset (k : ℕ) : cell k ⊆ Ioi (M : ℝ) := by
    intro x hx
    exact (hM_le_left k).trans_lt hx.1
  have herr_bound (k : ℕ) : ‖err k‖ ≤ ∫ x in cell k, g x := by
    dsimp [err]
    exact MeasureTheory.norm_integral_le_of_norm_le
      (hg_integrable.mono_set (hcell_subset k))
      (ae_restrict_of_forall_mem measurableSet_Ioc
        (fun x hx ↦ hweighted_le k x hx))
  have herr_norm_summable : Summable (fun k : ℕ ↦ ‖err k‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) herr_bound
      hg_cells.summable
  have herr_summable : Summable err := herr_norm_summable.of_norm
  have hseq_hasSum :
      HasSum seq ((∑' k : ℕ, err k) + ∫ x in Ioi (M : ℝ), F x) := by
    refine (herr_summable.hasSum.add hF_cells).congr_fun ?_
    intro k
    rw [herr_eq k]
    ring
  have hdiff :
      (∑' k : ℕ, seq k) - (∫ x in Ioi (M : ℝ), F x) =
        ∑' k : ℕ, err k := by
    rw [hseq_hasSum.tsum_eq]
    ring
  have hF_eval :
      (∫ x in Ioi (M : ℝ), F x) =
        (M : ℂ) ^ (-s - 1) / (s + 1) := by
    calc
      (∫ x in Ioi (M : ℝ), F x) =
          -(M : ℂ) ^ (q + 1) / (q + 1) := by
        simpa [F] using integral_Ioi_cpow_of_lt
          (a := q) hq_lt hMpos
      _ = (M : ℂ) ^ (-s - 1) / (s + 1) := by
        have hq1 : q + 1 = -s - 1 := by dsimp [q]; ring
        have hs1 : -s - 1 = -(s + 1) := by ring
        rw [hq1, hs1, neg_div_neg_eq]
  have hseq_apply (k : ℕ) :
      seq k = (((k + M + 1 : ℕ) : ℂ) ^ (-s - 2)) := by
    dsimp [seq, F, left, q]
    congr 1
    push_cast
    ring
  have hseq_tsum :
      (∑' k : ℕ, seq k) =
        ∑' k : ℕ, (((k + M + 1 : ℕ) : ℂ) ^ (-s - 2)) := by
    apply tsum_congr
    exact hseq_apply
  have htarget := hdiff
  rw [hF_eval, hseq_tsum] at htarget
  have hg_eval :
      (∫ x in Ioi (M : ℝ), g x) =
        (‖s + 2‖ / (s.re + 2)) *
          (M : ℝ) ^ (-(s.re + 2)) := by
    dsimp [g]
    rw [MeasureTheory.integral_const_mul,
      integral_Ioi_rpow_of_lt
        (a := -s.re - 3) (by linarith) hMpos]
    have hexp : -s.re - 3 + 1 = -(s.re + 2) := by ring
    rw [hexp, neg_div_neg_eq]
    field_simp
  unfold nativeExplicitRadiusScalarTailDefect
  rw [htarget]
  calc
    ‖∑' k : ℕ, err k‖ ≤ ∫ x in Ioi (M : ℝ), g x :=
      tsum_of_norm_bounded hg_cells herr_bound
    _ = (‖s + 2‖ / (s.re + 2)) *
        (M : ℝ) ^ (-(s.re + 2)) := hg_eval

end

end GenuineZeroUniformAtlasEnergy

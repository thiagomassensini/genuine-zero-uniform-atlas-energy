import GenuineZeroUniformAtlasEnergy.NativeCutoffAsymptotic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SumIntegralComparisons

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

open scoped BigOperators

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

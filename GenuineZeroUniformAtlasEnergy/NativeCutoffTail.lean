import GenuineZeroUniformAtlasEnergy.NativeTransverseHessian
import CPFormal.Analytic.CpGenuineFirstCutoffTail
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SumIntegralComparisons

/-!
# Exact native cutoff tail and critical-line decay

The finite primitive camera does not carry an unexplained numerical residue.
At a real spectral resonance its value is exactly the negative of the
bracketed tail not yet included by the cutoff.

This module adds a quantitative estimate. The existing centered-second-
difference majorant is summed by the integral test on the critical line:

```math
\sum_{k\ge 0}(k+M+1)^{-5/2}
\le \int_M^\infty x^{-5/2}\,dx
=\frac23 M^{-3/2}.
```

Consequently the raw finite-camera amplitude is `O(M^(-3/2))` and its raw
quadratic energy is `O(M^(-3))`. The theorem uses no numerical cutoff table,
fitted constant, score normalization, or infinite-limit zero claim.
-/

open scoped BigOperators

namespace GenuineZeroUniformAtlasEnergy

open CPFormal.Analytic.Cp
open Set MeasureTheory

noncomputable section

/-- Raw critical-line energy of one finite primitive camera. -/
def finiteNativeCriticalRawEnergy
    (p M : ℕ) (time : ℝ) : ℝ :=
  ‖finiteNativeCharacteristic p M (criticalLineParameter time)‖ ^ 2

/-- Explicit critical-line cutoff majorant obtained from the integral test. -/
def finiteNativeCriticalTailBound
    (p M : ℕ) (time : ℝ) : ℝ :=
  (2 / 3 : ℝ) *
    cpBracketMajorantConstant p (criticalLineParameter time) *
      (M : ℝ) ^ (-(3 / 2 : ℝ))

/-- The shifted critical `p`-series tail is bounded by its improper integral. -/
lemma criticalTailPower_tsum_le
    (M : ℕ) (hM : 1 ≤ M) :
    (∑' k : ℕ,
      (((k + M + 1 : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ) - 2)) ≤
      (2 / 3 : ℝ) * (M : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hMpos : 0 < (M : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)
  let f : ℝ → ℝ := fun x => x ^ (-(1 / 2 : ℝ) - 2)
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
      (((k + M + 1 : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ) - 2)) ≤
        ∫ x in Ioi (M : ℝ), x ^ (-(1 / 2 : ℝ) - 2) := by
      simpa [f] using
        hanti.tsum_comp_add_le_integral M hintegrable hnonneg
    _ = -(M : ℝ) ^ (-(1 / 2 : ℝ) - 2 + 1) /
          (-(1 / 2 : ℝ) - 2 + 1) :=
      integral_Ioi_rpow_of_lt (by norm_num) hMpos
    _ = (2 / 3 : ℝ) * (M : ℝ) ^ (-(3 / 2 : ℝ)) := by
      norm_num
      ring

/-- The unresolved critical-line bracket tail has amplitude `O(M^(-3/2))`. -/
lemma norm_realCpBracketCutoffTail_critical_le
    (p M : ℕ) (hp : Nat.Prime p) (hM : 1 ≤ M) (time : ℝ) :
    ‖realCpBracketCutoffTail p M (criticalLineParameter time)‖ ≤
      finiteNativeCriticalTailBound p M time := by
  let s : ℂ := criticalLineParameter time
  let C : ℝ := cpBracketMajorantConstant p s
  have hs : -1 < s.re := by
    dsimp [s]
    norm_num [criticalLineParameter_re]
  have hpowerSummable :
      Summable (fun k : ℕ =>
        (((k + M + 1 : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ) - 2)) := by
    have hbase :=
      summable_nat_add_one_rpow_neg_re_sub_two (s := s) hs
    have hinjective : Function.Injective (fun k : ℕ => k + M) := by
      intro a b hab
      exact Nat.add_right_cancel hab
    have hshift := hbase.comp_injective hinjective
    simpa [Function.comp_apply, s, criticalLineParameter_re] using hshift
  have hmajorantHasSum :
      HasSum
        (fun k : ℕ =>
          C * (((k + M + 1 : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ) - 2))
        (C * ∑' k : ℕ,
          (((k + M + 1 : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ) - 2)) :=
    hpowerSummable.hasSum.mul_left C
  have hpointwise : ∀ k : ℕ,
      ‖realCpSaturatedBracket p (k + M) s‖ ≤
        C * (((k + M + 1 : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ) - 2) := by
    intro k
    simpa [C, s, criticalLineParameter_re] using
      (norm_realCpSaturatedBracket_le
        (p := p) (k := k + M) hp (s := s) hs)
  have hnorm :
      ‖∑' k : ℕ, realCpSaturatedBracket p (k + M) s‖ ≤
        C * ∑' k : ℕ,
          (((k + M + 1 : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ) - 2) :=
    tsum_of_norm_bounded hmajorantHasSum hpointwise
  have hC : 0 ≤ C := by
    dsimp [C]
    unfold cpBracketMajorantConstant
    positivity
  calc
    ‖realCpBracketCutoffTail p M (criticalLineParameter time)‖ =
        ‖∑' k : ℕ, realCpSaturatedBracket p (k + M) s‖ := by
      rfl
    _ ≤ C * ∑' k : ℕ,
        (((k + M + 1 : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ) - 2) := hnorm
    _ ≤ C * ((2 / 3 : ℝ) * (M : ℝ) ^ (-(3 / 2 : ℝ))) :=
      mul_le_mul_of_nonneg_left (criticalTailPower_tsum_le M hM) hC
    _ = finiteNativeCriticalTailBound p M time := by
      simp [finiteNativeCriticalTailBound, C, s]
      ring

/--
Concrete cutoff capstone. At a real spectral resonance, the finite primitive
camera is exactly the negative unresolved tail; its amplitude is bounded by
`(2/3) C_{p,t} M^(-3/2)`, and its raw energy by the square of that expression.
-/
theorem finiteNativeCamera_resonant_cutoffTail_and_rate
    (p M : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (hM : 1 ≤ M) (time : ℝ)
    (hres : IsRealSpectralResonance time) :
    finiteNativeCharacteristic p M (criticalLineParameter time) =
        -realCpBracketCutoffTail p M (criticalLineParameter time) ∧
      ‖finiteNativeCharacteristic p M (criticalLineParameter time)‖ ≤
        finiteNativeCriticalTailBound p M time ∧
      finiteNativeCriticalRawEnergy p M time ≤
        (finiteNativeCriticalTailBound p M time) ^ 2 := by
  have htail :
      finiteNativeCharacteristic p M (criticalLineParameter time) =
        -realCpBracketCutoffTail p M (criticalLineParameter time) := by
    simpa [finiteNativeCharacteristic, finiteRealSpectralChart] using
      (finiteRealSpectralChart_eq_neg_cutoffTail_of_resonance
        p M hp hpodd time hres)
  have hnormTail :=
    norm_realCpBracketCutoffTail_critical_le p M hp hM time
  have hnorm :
      ‖finiteNativeCharacteristic p M (criticalLineParameter time)‖ ≤
        finiteNativeCriticalTailBound p M time := by
    rw [htail, norm_neg]
    exact hnormTail
  have hboundNonneg : 0 ≤ finiteNativeCriticalTailBound p M time := by
    unfold finiteNativeCriticalTailBound cpBracketMajorantConstant
    positivity
  have hsquare :
      ‖finiteNativeCharacteristic p M (criticalLineParameter time)‖ ^ 2 ≤
        (finiteNativeCriticalTailBound p M time) ^ 2 := by
    have hproduct := mul_nonneg
      (sub_nonneg.mpr hnorm)
      (add_nonneg hboundNonneg
        (norm_nonneg
          (finiteNativeCharacteristic p M (criticalLineParameter time))))
    nlinarith
  exact ⟨htail, hnorm, by
    simpa [finiteNativeCriticalRawEnergy] using hsquare⟩

end

end GenuineZeroUniformAtlasEnergy

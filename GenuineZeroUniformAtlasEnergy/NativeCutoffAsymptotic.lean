import GenuineZeroUniformAtlasEnergy.NativeCutoffTail
import GenuineZeroUniformAtlasEnergy.EmpiricalCameraOperator
import Mathlib.Analysis.Calculus.Taylor

/-!
# Explicit-radius cutoff leading model and local remainder

This module keeps the period and the retained radius independent.  For a
period `b` and radius cutoff `h`, the local block is the sum of the centered
Dirichlet second differences of radii `1, ..., h` at the centre `b(k+1)`.
This includes the empirical even cameras with the antipodal radius
`h = b / 2`; it does not silently replace them by the natural-camera
half-range `(b-1)/2`.

The leading local coefficient is the second radius moment

`s(s+1) * (sum r^2) * b^(-s-2)`.

Replacing the leading block series by its continuous primitive suggests

`s * (sum r^2) * b^(-s-2) * M^(-s-1)`.

The definitions below make the indexing and this coefficient explicit.  The
module proves a local block remainder, the exact logarithmic phase, and the
collective coefficient geometry.  It does not bound the global tail remainder
and therefore does not claim a completed sharp cutoff-tail asymptotic.
-/

open scoped BigOperators

namespace GenuineZeroUniformAtlasEnergy

open CPFormal.Analytic.Cp

noncomputable section

attribute [local instance 10000] NormedSpace.complexToReal

/-- Second radius moment of the retained radii `1, ..., h`. -/
def nativeRadiusSecondMoment (h : ℕ) : ℝ :=
  ∑ radius ∈ Finset.Icc 1 h, (radius : ℝ) ^ 2

/-- Third radius moment used by the explicit Taylor remainder. -/
def nativeRadiusThirdMoment (h : ℕ) : ℝ :=
  ∑ radius ∈ Finset.Icc 1 h, (radius : ℝ) ^ 3

/-- Third real derivative of the Dirichlet monomial. -/
def realDirichletPowerDeriv3 (s : ℂ) (x : ℝ) : ℂ :=
  -(s * (s + 1) * (s + 2)) * (x : ℂ) ^ (-s - 3)

/-- The displayed third derivative is the derivative of the already audited
second derivative on the positive real axis. -/
theorem hasDerivAt_realDirichletPowerDeriv2
    {s : ℂ} (hs : -2 < s.re) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (realDirichletPowerDeriv2 s)
      (realDirichletPowerDeriv3 s x) x := by
  have hexponent : -s - 2 ≠ 0 := by
    intro hzero
    have hre : -s.re - 2 = 0 := by
      simpa using congrArg Complex.re hzero
    linarith
  have hpow :=
    hasDerivAt_ofReal_cpow_const (ne_of_gt hx) hexponent
  have hscaled :
      HasDerivAt
        (fun y : ℝ ↦ (s * (s + 1)) • (y : ℂ) ^ (-s - 2))
        ((s * (s + 1)) •
          ((-s - 2) * (x : ℂ) ^ ((-s - 2) - 1))) x := by
    apply HasDerivAt.fun_const_smul
    exact hpow
  change HasDerivAt
    (fun y : ℝ ↦ s * (s + 1) * (y : ℂ) ^ (-s - 2))
    (-(s * (s + 1) * (s + 2)) * (x : ℂ) ^ (-s - 3)) x
  convert hscaled using 1
  simp only [smul_eq_mul]
  ring_nf

/-- Exact norm of the third derivative on the positive real axis. -/
theorem norm_realDirichletPowerDeriv3
    (s : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖realDirichletPowerDeriv3 s x‖ =
      ‖s * (s + 1) * (s + 2)‖ * x ^ (-s.re - 3) := by
  rw [realDirichletPowerDeriv3, norm_mul, norm_neg,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  congr 1

/-- A third-derivative bound controls the error made by replacing a centered
second difference by `radius^2 * f''(center)`.  The constant `2` is chosen for
a short mean-value proof; the integral Taylor formula improves it to `1/3`.
-/
theorem norm_centeredSecondDifference_sub_secondDerivative_le
    {f f' f'' f''' : ℝ → ℂ}
    {center radius C : ℝ}
    (hradius : 0 ≤ radius)
    (hf : ∀ x ∈ Set.Icc (center - radius) (center + radius),
      HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Set.Icc (center - radius) (center + radius),
      HasDerivAt f' (f'' x) x)
    (hf'' : ∀ x ∈ Set.Icc (center - radius) (center + radius),
      HasDerivAt f'' (f''' x) x)
    (hbound : ∀ x ∈ Set.Icc (center - radius) (center + radius),
      ‖f''' x‖ ≤ C) :
    ‖f (center - radius) - (2 • f center) + f (center + radius) -
        (radius ^ 2) • f'' center‖ ≤
      2 * C * radius ^ 3 := by
  let segment : Set ℝ := Set.Icc (center - radius) (center + radius)
  have hcenter : center ∈ segment := by
    dsimp [segment]
    constructor <;> linarith
  have hC : 0 ≤ C :=
    le_trans (norm_nonneg (f''' center)) (hbound center hcenter)
  have hsecondDifference : ∀ y ∈ segment,
      ‖f'' y - f'' center‖ ≤ C * radius := by
    intro y hy
    have hlip :=
      (convex_Icc (center - radius) (center + radius)).norm_image_sub_le_of_norm_hasDerivWithin_le
          (fun z hz ↦ (hf'' z hz).hasDerivWithinAt)
          hbound hcenter hy
    have habs : ‖y - center‖ ≤ radius := by
      rw [Real.norm_eq_abs, abs_le]
      dsimp [segment] at hy
      constructor <;> linarith [hy.1, hy.2]
    exact hlip.trans
      (mul_le_mul_of_nonneg_left habs hC)
  let u : ℝ → ℂ := fun y ↦
    f' y - (y - center) • f'' center
  have hu : ∀ y ∈ segment,
      HasDerivAt u (f'' y - f'' center) y := by
    intro y hy
    have hlinear :
        HasDerivAt (fun z : ℝ ↦ (z - center) • f'' center)
          (f'' center) y := by
      simpa using
        ((hasDerivAt_id y).sub_const center).smul_const (f'' center)
    exact (hf' y hy).sub hlinear
  have huLip : ∀ {x y : ℝ}, x ∈ segment → y ∈ segment →
      ‖u y - u x‖ ≤ (C * radius) * ‖y - x‖ := by
    intro x y hx hy
    exact
      (convex_Icc (center - radius) (center + radius)).norm_image_sub_le_of_norm_hasDerivWithin_le
          (fun z hz ↦ (hu z hz).hasDerivWithinAt)
          hsecondDifference hx hy
  let g : ℝ → ℂ := fun t ↦
    f (center - t) + f (center + t) - (2 • f center) -
      (t ^ 2) • f'' center
  let g' : ℝ → ℂ := fun t ↦
    f' (center + t) - f' (center - t) -
      (2 * t) • f'' center
  have hg : ∀ t ∈ Set.Icc (0 : ℝ) radius,
      HasDerivWithinAt g (g' t) (Set.Icc (0 : ℝ) radius) t := by
    intro t ht
    have hminusMem : center - t ∈ segment := by
      dsimp [segment]
      constructor <;> linarith [ht.1, ht.2]
    have hplusMem : center + t ∈ segment := by
      dsimp [segment]
      constructor <;> linarith [ht.1, ht.2]
    have hminusInner :
        HasDerivAt (fun z : ℝ ↦ center - z) (-1 : ℝ) t := by
      exact (hasDerivAt_id' t).const_sub center
    have hplusInner :
        HasDerivAt (fun z : ℝ ↦ center + z) (1 : ℝ) t := by
      exact (hasDerivAt_id' t).const_add center
    have hminus :
        HasDerivAt (fun z : ℝ ↦ f (center - z))
          (-f' (center - t)) t := by
      simpa [Function.comp_def] using
        (hf (center - t) hminusMem).scomp t hminusInner
    have hplus :
        HasDerivAt (fun z : ℝ ↦ f (center + z))
          (f' (center + t)) t := by
      simpa [Function.comp_def] using
        (hf (center + t) hplusMem).scomp t hplusInner
    have hpair :
        HasDerivAt
          (fun z : ℝ ↦
            f (center - z) + f (center + z) - (2 • f center))
          (f' (center + t) - f' (center - t)) t := by
      simpa only [sub_eq_add_neg, neg_add_rev, add_comm] using
        (hminus.fun_add hplus).sub_const (2 • f center)
    have hsquare :
        HasDerivAt (fun z : ℝ ↦ (z ^ 2) • f'' center)
          ((2 * t) • f'' center) t := by
      simpa [pow_two, two_mul] using
        ((hasDerivAt_id t).pow 2).smul_const (f'' center)
    exact (hpair.sub hsquare).hasDerivWithinAt
  have hgBound : ∀ t ∈ Set.Ico (0 : ℝ) radius,
      ‖g' t‖ ≤ 2 * C * radius ^ 2 := by
    intro t ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) radius := ⟨ht.1, ht.2.le⟩
    have hminusMem : center - t ∈ segment := by
      dsimp [segment]
      constructor <;> linarith [ht.1, ht.2]
    have hplusMem : center + t ∈ segment := by
      dsimp [segment]
      constructor <;> linarith [ht.1, ht.2]
    have hplus := huLip hcenter hplusMem
    have hminus := huLip hminusMem hcenter
    have hplusDist : ‖(center + t) - center‖ ≤ radius := by
      rw [show (center + t) - center = t by ring, Real.norm_eq_abs,
        abs_of_nonneg ht.1]
      exact ht.2.le
    have hminusDist : ‖center - (center - t)‖ ≤ radius := by
      rw [show center - (center - t) = t by ring, Real.norm_eq_abs,
        abs_of_nonneg ht.1]
      exact ht.2.le
    have hplusBound : ‖u (center + t) - u center‖ ≤ C * radius ^ 2 := by
      exact hplus.trans (by
        calc
          (C * radius) * ‖(center + t) - center‖ ≤
              (C * radius) * radius :=
            mul_le_mul_of_nonneg_left hplusDist
              (mul_nonneg hC hradius)
          _ = C * radius ^ 2 := by ring)
    have hminusBound : ‖u center - u (center - t)‖ ≤ C * radius ^ 2 := by
      exact hminus.trans (by
        calc
          (C * radius) * ‖center - (center - t)‖ ≤
              (C * radius) * radius :=
            mul_le_mul_of_nonneg_left hminusDist
              (mul_nonneg hC hradius)
          _ = C * radius ^ 2 := by ring)
    have hrewrite :
        g' t =
          (u (center + t) - u center) +
            (u center - u (center - t)) := by
      dsimp [g', u]
      push_cast
      ring
    rw [hrewrite]
    calc
      ‖(u (center + t) - u center) +
          (u center - u (center - t))‖ ≤
          ‖u (center + t) - u center‖ +
            ‖u center - u (center - t)‖ := norm_add_le _ _
      _ ≤ C * radius ^ 2 + C * radius ^ 2 :=
        add_le_add hplusBound hminusBound
      _ = 2 * C * radius ^ 2 := by ring
  have hgMvt :=
    norm_image_sub_le_of_norm_deriv_le_segment'
      hg hgBound radius (Set.right_mem_Icc.mpr hradius)
  have hgzero : g 0 = 0 := by
    dsimp [g]
    simp [two_smul]
  rw [hgzero, sub_zero] at hgMvt
  change
    ‖f (center - radius) - (2 • f center) + f (center + radius) -
        (radius ^ 2) • f'' center‖ ≤
      2 * C * radius ^ 3
  calc
    ‖f (center - radius) - (2 • f center) + f (center + radius) -
        (radius ^ 2) • f'' center‖ = ‖g radius‖ := by
      dsimp [g]
      congr 1
      abel
    _ ≤ (2 * C * radius ^ 2) * radius := by
      simpa using hgMvt
    _ = 2 * C * radius ^ 3 := by ring

/-- On the critical line, one radius pair differs from its quadratic Taylor
term by an explicit cubic-radius remainder.  The power `-7/2` is evaluated at
the left endpoint of the centered interval, where the third derivative is
largest. -/
theorem norm_realCpPairBracket_sub_secondDerivative_critical_le
    (b radius k : ℕ) (hb : 1 ≤ b) (hradius : radius ≤ b - 1)
    (time : ℝ) :
    ‖realCpPairBracket b radius k (criticalLineParameter time) -
        ((radius : ℝ) ^ 2) •
          realDirichletPowerDeriv2 (criticalLineParameter time)
            ((b : ℝ) * ((k + 1 : ℕ) : ℝ))‖ ≤
      2 *
        ‖criticalLineParameter time * (criticalLineParameter time + 1) *
          (criticalLineParameter time + 2)‖ *
        ((b : ℝ) * ((k + 1 : ℕ) : ℝ) - (radius : ℝ)) ^
          (-(7 / 2 : ℝ)) *
        (radius : ℝ) ^ 3 := by
  let s : ℂ := criticalLineParameter time
  let center : ℝ := (b : ℝ) * ((k + 1 : ℕ) : ℝ)
  let r : ℝ := radius
  have hs0 : s ≠ 0 := by
    intro hs
    have hre := congrArg Complex.re hs
    simp [s, criticalLineParameter_re] at hre
  have hs1 : -1 < s.re := by
    simp [s, criticalLineParameter_re]
    norm_num
  have hs2 : -2 < s.re := by
    simp [s, criticalLineParameter_re]
    norm_num
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
            (center - r) ^ (-(7 / 2 : ℝ)) := by
    intro x hx
    have hxpos : 0 < x := hleft.trans_le hx.1
    rw [norm_realDirichletPowerDeriv3 s hxpos]
    have hexponent : -s.re - 3 = -(7 / 2 : ℝ) := by
      simp [s, criticalLineParameter_re]
      norm_num
    rw [hexponent]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hleft hx.1 (by norm_num))
      (norm_nonneg _)
  have hraw :=
    norm_centeredSecondDifference_sub_secondDerivative_le
      (f := realDirichletPower s)
      (f' := realDirichletPowerDeriv s)
      (f'' := realDirichletPowerDeriv2 s)
      (f''' := realDirichletPowerDeriv3 s)
      (center := center) (radius := r)
      (C := ‖s * (s + 1) * (s + 2)‖ *
        (center - r) ^ (-(7 / 2 : ℝ)))
      (by positivity)
      (fun x hx ↦ hasDerivAt_realDirichletPower hs0
        (hleft.trans_le hx.1))
      (fun x hx ↦ hasDerivAt_realDirichletPowerDeriv hs1
        (hleft.trans_le hx.1))
      (fun x hx ↦ hasDerivAt_realDirichletPowerDeriv2 hs2
        (hleft.trans_le hx.1))
      hthirdBound
  simpa [realCpPairBracket, s, center, r, mul_assoc] using hraw

/-- Explicit-radius block at the aligned centre `b(k+1)`. -/
def nativeExplicitRadiusBracket
    (b h k : ℕ) (s : ℂ) : ℂ :=
  ∑ radius ∈ Finset.Icc 1 h, realCpPairBracket b radius k s

/-- Unresolved explicit-radius tail after `M` complete blocks. -/
def nativeExplicitRadiusCutoffTail
    (b h M : ℕ) (s : ℂ) : ℂ :=
  ∑' k : ℕ, nativeExplicitRadiusBracket b h (k + M) s

/-- Coefficient of `(k+1)^(-s-2)` in one explicit-radius block. -/
def nativeExplicitRadiusBlockCoefficient
    (b h : ℕ) (s : ℂ) : ℂ :=
  s * (s + 1) * (nativeRadiusSecondMoment h : ℂ) *
    (b : ℂ) ^ (-s - 2)

/-- Leading model for one explicit-radius block. -/
def nativeExplicitRadiusBracketLeading
    (b h k : ℕ) (s : ℂ) : ℂ :=
  nativeExplicitRadiusBlockCoefficient b h s *
    ((k + 1 : ℕ) : ℂ) ^ (-s - 2)

/-- Exact local error after removing the quadratic Taylor term. -/
def nativeExplicitRadiusBracketRemainder
    (b h k : ℕ) (s : ℂ) : ℂ :=
  nativeExplicitRadiusBracket b h k s -
    nativeExplicitRadiusBracketLeading b h k s

/-- The displayed leading block is exactly the finite sum of the quadratic
Taylor terms of its radius pairs. -/
theorem nativeExplicitRadiusBracketLeading_eq_sum_secondDerivative
    (b h k : ℕ) (s : ℂ) :
    nativeExplicitRadiusBracketLeading b h k s =
      ∑ radius ∈ Finset.Icc 1 h,
        ((radius : ℝ) ^ 2) •
          realDirichletPowerDeriv2 s
            ((b : ℝ) * ((k + 1 : ℕ) : ℝ)) := by
  classical
  rw [← Finset.sum_smul]
  unfold nativeExplicitRadiusBracketLeading
    nativeExplicitRadiusBlockCoefficient nativeRadiusSecondMoment
    realDirichletPowerDeriv2
  push_cast
  have hkCast : (k : ℂ) + 1 = ((k + 1 : ℕ) : ℂ) := by
    norm_num
  rw [hkCast, Complex.natCast_mul_natCast_cpow]
  rw [Complex.real_smul]
  push_cast
  ring

/-- Kernel-checked local remainder bound obtained by summing the explicit
third-derivative estimate over all retained radii. -/
theorem norm_nativeExplicitRadiusBracketRemainder_critical_le_sum
    (b h k : ℕ) (hb : 1 ≤ b) (hh : h ≤ b - 1) (time : ℝ) :
    ‖nativeExplicitRadiusBracketRemainder b h k
        (criticalLineParameter time)‖ ≤
      ∑ radius ∈ Finset.Icc 1 h,
        2 *
          ‖criticalLineParameter time * (criticalLineParameter time + 1) *
            (criticalLineParameter time + 2)‖ *
          ((b : ℝ) * ((k + 1 : ℕ) : ℝ) - (radius : ℝ)) ^
            (-(7 / 2 : ℝ)) *
          (radius : ℝ) ^ 3 := by
  classical
  unfold nativeExplicitRadiusBracketRemainder
  rw [nativeExplicitRadiusBracketLeading_eq_sum_secondDerivative]
  unfold nativeExplicitRadiusBracket
  calc
    ‖(∑ radius ∈ Finset.Icc 1 h,
          realCpPairBracket b radius k (criticalLineParameter time)) -
        ∑ radius ∈ Finset.Icc 1 h,
          ((radius : ℝ) ^ 2) •
            realDirichletPowerDeriv2 (criticalLineParameter time)
              ((b : ℝ) * ((k + 1 : ℕ) : ℝ))‖ =
        ‖∑ radius ∈ Finset.Icc 1 h,
          (realCpPairBracket b radius k (criticalLineParameter time) -
            ((radius : ℝ) ^ 2) •
              realDirichletPowerDeriv2 (criticalLineParameter time)
                ((b : ℝ) * ((k + 1 : ℕ) : ℝ)))‖ := by
      congr 1
      rw [Finset.sum_sub_distrib]
    _ ≤ ∑ radius ∈ Finset.Icc 1 h,
          ‖realCpPairBracket b radius k (criticalLineParameter time) -
            ((radius : ℝ) ^ 2) •
              realDirichletPowerDeriv2 (criticalLineParameter time)
                ((b : ℝ) * ((k + 1 : ℕ) : ℝ))‖ := norm_sum_le _ _
    _ ≤ ∑ radius ∈ Finset.Icc 1 h,
        2 *
          ‖criticalLineParameter time * (criticalLineParameter time + 1) *
            (criticalLineParameter time + 2)‖ *
          ((b : ℝ) * ((k + 1 : ℕ) : ℝ) - (radius : ℝ)) ^
            (-(7 / 2 : ℝ)) *
          (radius : ℝ) ^ 3 := by
      exact Finset.sum_le_sum fun radius hradius ↦
        norm_realCpPairBracket_sub_secondDerivative_critical_le
          b radius k hb
          (le_trans (Finset.mem_Icc.mp hradius).2 hh) time

/-- Uniform local rate.  The geometric margin `b-h` and the block index
separate, giving the genuine bracket remainder order `(k+1)^(-7/2)` after the
quadratic leading term is removed. -/
theorem norm_nativeExplicitRadiusBracketRemainder_critical_le
    (b h k : ℕ) (hb : 1 ≤ b) (hh : h ≤ b - 1) (time : ℝ) :
    ‖nativeExplicitRadiusBracketRemainder b h k
        (criticalLineParameter time)‖ ≤
      2 *
        ‖criticalLineParameter time * (criticalLineParameter time + 1) *
          (criticalLineParameter time + 2)‖ *
        ((b - h : ℕ) : ℝ) ^ (-(7 / 2 : ℝ)) *
        ((k + 1 : ℕ) : ℝ) ^ (-(7 / 2 : ℝ)) *
        nativeRadiusThirdMoment h := by
  classical
  have hbase :=
    norm_nativeExplicitRadiusBracketRemainder_critical_le_sum
      b h k hb hh time
  have hhB : h ≤ b := by omega
  have hgapNat : 1 ≤ b - h := by omega
  have hgapPos : 0 < ((b - h : ℕ) : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hgapNat)
  have hj : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  have hjPos : 0 < ((k + 1 : ℕ) : ℝ) := lt_of_lt_of_le zero_lt_one hj
  calc
    ‖nativeExplicitRadiusBracketRemainder b h k
        (criticalLineParameter time)‖ ≤
      ∑ radius ∈ Finset.Icc 1 h,
        2 *
          ‖criticalLineParameter time * (criticalLineParameter time + 1) *
            (criticalLineParameter time + 2)‖ *
          ((b : ℝ) * ((k + 1 : ℕ) : ℝ) - (radius : ℝ)) ^
            (-(7 / 2 : ℝ)) *
          (radius : ℝ) ^ 3 := hbase
    _ ≤ ∑ radius ∈ Finset.Icc 1 h,
        (2 *
          ‖criticalLineParameter time * (criticalLineParameter time + 1) *
            (criticalLineParameter time + 2)‖ *
          ((b - h : ℕ) : ℝ) ^ (-(7 / 2 : ℝ)) *
          ((k + 1 : ℕ) : ℝ) ^ (-(7 / 2 : ℝ))) *
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
              (-(7 / 2 : ℝ)) ≤
            (((b - h : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ)) ^
              (-(7 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hlowerPos hleftLower (by norm_num)
      calc
        2 *
            ‖criticalLineParameter time * (criticalLineParameter time + 1) *
              (criticalLineParameter time + 2)‖ *
            ((b : ℝ) * ((k + 1 : ℕ) : ℝ) - (radius : ℝ)) ^
              (-(7 / 2 : ℝ)) *
            (radius : ℝ) ^ 3 ≤
          2 *
            ‖criticalLineParameter time * (criticalLineParameter time + 1) *
              (criticalLineParameter time + 2)‖ *
            ((((b - h : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ)) ^
              (-(7 / 2 : ℝ))) *
            (radius : ℝ) ^ 3 := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpower (by positivity)) (by positivity)
        _ = (2 *
            ‖criticalLineParameter time * (criticalLineParameter time + 1) *
              (criticalLineParameter time + 2)‖ *
            ((b - h : ℕ) : ℝ) ^ (-(7 / 2 : ℝ)) *
            ((k + 1 : ℕ) : ℝ) ^ (-(7 / 2 : ℝ))) *
            (radius : ℝ) ^ 3 := by
          rw [Real.mul_rpow hgapPos.le hjPos.le]
          ring
    _ = 2 *
        ‖criticalLineParameter time * (criticalLineParameter time + 1) *
          (criticalLineParameter time + 2)‖ *
        ((b - h : ℕ) : ℝ) ^ (-(7 / 2 : ℝ)) *
        ((k + 1 : ℕ) : ℝ) ^ (-(7 / 2 : ℝ)) *
        nativeRadiusThirdMoment h := by
      unfold nativeRadiusThirdMoment
      rw [Finset.mul_sum]

/-- Candidate coefficient of `M^(-s-1)` suggested by the continuous primitive
of the leading block model. -/
def nativeExplicitRadiusTailCoefficient
    (b h : ℕ) (s : ℂ) : ℂ :=
  s * (nativeRadiusSecondMoment h : ℂ) *
    (b : ℂ) ^ (-s - 2)

/-- Exact global error after removing the predicted leading cutoff tail. -/
def nativeExplicitRadiusTailRemainder
    (b h M : ℕ) (s : ℂ) : ℂ :=
  nativeExplicitRadiusCutoffTail b h M s -
    nativeExplicitRadiusTailCoefficient b h s *
      (M : ℂ) ^ (-s - 1)

/-- The local block splits exactly into its leading model and its remainder. -/
theorem nativeExplicitRadiusBracket_eq_leading_add_remainder
    (b h k : ℕ) (s : ℂ) :
    nativeExplicitRadiusBracket b h k s =
      nativeExplicitRadiusBracketLeading b h k s +
        nativeExplicitRadiusBracketRemainder b h k s := by
  unfold nativeExplicitRadiusBracketRemainder
  ring

/-- The cutoff tail splits exactly into its proposed leading model and the
explicitly named global difference remainder.  No smallness estimate for that
global remainder is asserted here. -/
theorem nativeExplicitRadiusCutoffTail_eq_leading_add_remainder
    (b h M : ℕ) (s : ℂ) :
    nativeExplicitRadiusCutoffTail b h M s =
      nativeExplicitRadiusTailCoefficient b h s *
          (M : ℂ) ^ (-s - 1) +
        nativeExplicitRadiusTailRemainder b h M s := by
  unfold nativeExplicitRadiusTailRemainder
  ring

/-- The factor `s+1` in the local second derivative cancels against the
primitive of `(k+1)^(-s-2)`. -/
theorem nativeExplicitRadiusBlockCoefficient_div
    (b h : ℕ) {s : ℂ} (hs : s + 1 ≠ 0) :
    nativeExplicitRadiusBlockCoefficient b h s / (s + 1) =
      nativeExplicitRadiusTailCoefficient b h s := by
  unfold nativeExplicitRadiusBlockCoefficient
    nativeExplicitRadiusTailCoefficient
  field_simp

/-- On the critical line the candidate tail-model coefficient has the exact
expected norm.  This records both the second radius moment and the full period
factor `b^(-5/2)`. -/
theorem norm_nativeExplicitRadiusTailCoefficient_critical
    (b h : ℕ) (hb : 0 < b) (time : ℝ) :
    ‖nativeExplicitRadiusTailCoefficient b h
        (criticalLineParameter time)‖ =
      ‖criticalLineParameter time‖ *
        nativeRadiusSecondMoment h *
          (b : ℝ) ^ (-(5 / 2 : ℝ)) := by
  have hbReal : 0 < (b : ℝ) := by exact_mod_cast hb
  have hbCast : (b : ℂ) = ((b : ℝ) : ℂ) := by norm_cast
  have hexponent :
      (-criticalLineParameter time - 2).re = -(5 / 2 : ℝ) := by
    simp only [Complex.sub_re, Complex.neg_re, criticalLineParameter_re]
    norm_num
  unfold nativeExplicitRadiusTailCoefficient
  rw [norm_mul, norm_mul, hbCast,
    Complex.norm_cpow_eq_rpow_re_of_pos hbReal]
  rw [hexponent]
  have hmoment : 0 ≤ nativeRadiusSecondMoment h := by
    unfold nativeRadiusSecondMoment
    positivity
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hmoment]

/-- Exact logarithmic phase of the cutoff monomial.  The amplitude is
`M^(-3/2)` and the phase is `exp (-i t log M)`; no asymptotic notation is
used in this identity. -/
theorem criticalCutoffPower_eq_amplitude_mul_logPhase
    (M : ℕ) (hM : 0 < M) (time : ℝ) :
    (M : ℂ) ^ (-criticalLineParameter time - 1) =
      (((M : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
        Complex.exp
          (-(((time * Real.log (M : ℝ) : ℝ) : ℂ) * Complex.I)) := by
  let x : ℝ := (M : ℝ)
  have hx : 0 < x := by
    dsimp [x]
    exact_mod_cast hM
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hbase : (M : ℂ) = (x : ℂ) := by
    dsimp [x]
  have hexponent :
      -criticalLineParameter time - 1 =
        ((-(3 / 2 : ℝ) : ℝ) : ℂ) +
          (-((time : ℂ) * Complex.I)) := by
    unfold criticalLineParameter
    push_cast
    ring
  rw [hbase, hexponent,
    Complex.cpow_add (x := (x : ℂ)) _ _ hxC]
  rw [← Complex.ofReal_cpow hx.le]
  congr 1
  rw [Complex.cpow_def_of_ne_zero hxC]
  rw [← Complex.ofReal_log hx.le]
  congr 1
  dsimp [x]
  rw [Complex.ofReal_log (show 0 ≤ (M : ℝ) by positivity)]
  rw [Complex.ofReal_mul]
  rw [Complex.ofReal_log (show 0 ≤ (M : ℝ) by positivity)]
  ring

/-! ## The six empirical geometries -/

/-- The explicit-radius tail is not a surrogate for the empirical operator:
after substituting the audited radius table, it is definitionally the same
summable tail camera by camera. -/
theorem empiricalCameraCutoffTail_eq_nativeExplicitRadiusCutoffTail
    (camera : EmpiricalCamera) (M : ℕ) (s : ℂ) :
    empiricalCameraCutoffTail camera M s =
      nativeExplicitRadiusCutoffTail
        camera.period (camera.label / 2) M s := by
  unfold empiricalCameraCutoffTail empiricalCameraBlock
    nativeExplicitRadiusCutoffTail nativeExplicitRadiusBracket
  apply tsum_congr
  intro k
  rw [camera.radii_eq_Icc]

/-- Pointwise identification of the full six-camera cutoff-tail stack with
the explicit-radius construction used in this module. -/
theorem empiricalCameraCutoffTailStack_eq_nativeExplicitRadiusCutoffTail
    (M : ℕ) (s : ℂ) :
    empiricalCameraCutoffTailStack M s =
      fun camera ↦ nativeExplicitRadiusCutoffTail
        camera.period (camera.label / 2) M s := by
  funext camera
  exact empiricalCameraCutoffTail_eq_nativeExplicitRadiusCutoffTail
    camera M s

/-- Candidate tail-model coefficient attached to one of the six empirical
cameras.  The period and the retained radius are read from different table
columns. -/
def empiricalNativeTailCoefficient
    (camera : EmpiricalCamera) (s : ℂ) : ℂ :=
  nativeExplicitRadiusTailCoefficient
    camera.period (camera.label / 2) s

/-- Squared norm of the six-camera leading vector. -/
def empiricalNativeTailCoefficientNormSq (time : ℝ) : ℝ :=
  ∑ camera : EmpiricalCamera,
    ‖empiricalNativeTailCoefficient camera
      (criticalLineParameter time)‖ ^ 2

/-- Real version of the exact rational geometry weight stored with each
empirical camera. -/
def empiricalNativeLeadingGeometryWeight
    (camera : EmpiricalCamera) : ℝ :=
  ((camera.secondRadiusMoment : ℝ) ^ 2) /
    ((camera.period : ℝ) ^ 5)

@[simp] theorem nativeRadiusSecondMoment_empirical
    (camera : EmpiricalCamera) :
    nativeRadiusSecondMoment (camera.label / 2) =
      (camera.secondRadiusMoment : ℝ) := by
  unfold nativeRadiusSecondMoment EmpiricalCamera.secondRadiusMoment
  rw [← camera.radii_eq_Icc]
  norm_cast

theorem empiricalCamera_period_pos (camera : EmpiricalCamera) :
    0 < camera.period := by
  cases camera <;> norm_num

/-- Squaring the critical amplitude `x^(-5/2)` gives exactly `x^(-5)`. -/
theorem sq_rpow_neg_five_halves (x : ℝ) (hx : 0 ≤ x) :
    (x ^ (-(5 / 2 : ℝ))) ^ 2 = x ^ (-5 : ℝ) := by
  calc
    (x ^ (-(5 / 2 : ℝ))) ^ 2 =
        x ^ ((-(5 / 2 : ℝ)) * (2 : ℝ)) := by
      exact (Real.rpow_mul_natCast hx (-(5 / 2 : ℝ)) 2).symm
    _ = x ^ (-5 : ℝ) := by norm_num

/-- Exact critical norm of every empirical candidate tail-model coefficient. -/
theorem norm_empiricalNativeTailCoefficient_critical
    (camera : EmpiricalCamera) (time : ℝ) :
    ‖empiricalNativeTailCoefficient camera
        (criticalLineParameter time)‖ =
      ‖criticalLineParameter time‖ *
        (camera.secondRadiusMoment : ℝ) *
          (camera.period : ℝ) ^ (-(5 / 2 : ℝ)) := by
  unfold empiricalNativeTailCoefficient
  rw [norm_nativeExplicitRadiusTailCoefficient_critical
    camera.period (camera.label / 2)
      (empiricalCamera_period_pos camera) time]
  rw [nativeRadiusSecondMoment_empirical]

/-- The squared leading norm of one empirical camera is its stored rational
geometry weight times the common spectral norm. -/
theorem norm_empiricalNativeTailCoefficient_critical_sq
    (camera : EmpiricalCamera) (time : ℝ) :
    ‖empiricalNativeTailCoefficient camera
        (criticalLineParameter time)‖ ^ 2 =
      ‖criticalLineParameter time‖ ^ 2 *
        empiricalNativeLeadingGeometryWeight camera := by
  rw [norm_empiricalNativeTailCoefficient_critical]
  have hperiod : 0 ≤ (camera.period : ℝ) := by positivity
  rw [mul_pow, mul_pow,
    sq_rpow_neg_five_halves (camera.period : ℝ) hperiod]
  unfold empiricalNativeLeadingGeometryWeight
  have hperiodPos : 0 < (camera.period : ℝ) := by
    exact_mod_cast empiricalCamera_period_pos camera
  have hperiodne : (camera.period : ℝ) ≠ 0 := ne_of_gt hperiodPos
  have hnegFive :
      (camera.period : ℝ) ^ (-5 : ℝ) =
        ((camera.period : ℝ) ^ 5)⁻¹ := by
    rw [show (-5 : ℝ) = -(5 : ℕ) by norm_num,
      Real.rpow_neg_natCast]
    simp
    norm_cast
  rw [hnegFive]
  field_simp

/-- The real geometry weights are the scalar extension of the exact rational
weights already audited in `EmpiricalCameraGeometry`. -/
theorem empiricalNativeLeadingGeometryWeight_eq_ratCast
    (camera : EmpiricalCamera) :
    empiricalNativeLeadingGeometryWeight camera =
      (camera.leadingTailGeometryWeight : ℝ) := by
  cases camera <;>
    norm_num [empiricalNativeLeadingGeometryWeight,
      EmpiricalCamera.leadingTailGeometryWeight]

/-- Exact collective squared leading norm for the empirical stack. -/
theorem empiricalNativeTailCoefficientNormSq_eq
    (time : ℝ) :
    empiricalNativeTailCoefficientNormSq time =
      ‖criticalLineParameter time‖ ^ 2 *
        ((132244271 : ℝ) / 1778112000) := by
  unfold empiricalNativeTailCoefficientNormSq
  simp_rw [norm_empiricalNativeTailCoefficient_critical_sq]
  rw [← Finset.mul_sum]
  congr 1
  calc
    (∑ camera : EmpiricalCamera,
        empiricalNativeLeadingGeometryWeight camera) =
        ∑ camera : EmpiricalCamera,
          (camera.leadingTailGeometryWeight : ℝ) := by
      apply Finset.sum_congr rfl
      intro camera hcamera
      exact empiricalNativeLeadingGeometryWeight_eq_ratCast camera
    _ = ((∑ camera : EmpiricalCamera,
          camera.leadingTailGeometryWeight : ℚ) : ℝ) := by
      norm_cast
    _ = ((((132244271 : ℚ) / (1778112000 : ℚ)) : ℚ) : ℝ) := by
      rw [EmpiricalCamera.sum_leadingTailGeometryWeight]
    _ = (132244271 : ℝ) / 1778112000 := by
      rw [Rat.cast_div]
      norm_num

end

end GenuineZeroUniformAtlasEnergy

import GenuineZeroUniformAtlasEnergy.EmpiricalCameraOperator
import GenuineZeroUniformAtlasEnergy.EmpiricalStackProjection
import CPFormal.Analytic.CpNaturalCameraAnalyticContinuation
import CPFormal.Analytic.CpPairedGenuineBridgeIdentity

/-!
# Analytic continuation of the empirical full-even cameras

The natural even-camera API omits the middle residue class.  The empirical
cameras labelled four and six retain that antipodal channel.  This module
keeps the two geometries separate and proves the correction explicitly.

For width `b = 2h`, the extra seed plus antipodal brackets is

`2 * h^(-s) * pairedAltChannel s`.

On the open critical strip this turns the truncated natural-even factor into

`1 + h^(-s) - (b+2)b^(-s)`.
-/

open scoped BigOperators Topology

namespace GenuineZeroUniformAtlasEnergy

open CPFormal.Analytic.Cp
open Filter

noncomputable section

/-- The seed and all centered brackets in the antipodal radius `h` of a
width-`2h` camera. -/
def antipodalEvenCameraChannel (h : ℕ) (s : ℂ) : ℂ :=
  realDirichletPower s (h : ℝ) +
    ∑' k : ℕ, realCpPairBracket (2 * h) h k s

/-- Finite prefix of the extra antipodal channel. -/
def finiteAntipodalEvenCameraChannel (h M : ℕ) (s : ℂ) : ℂ :=
  realDirichletPower s (h : ℝ) +
    ∑ k ∈ Finset.range M, realCpPairBracket (2 * h) h k s

/-- A width-`2h`, radius-`h` bracket is a scaled second difference on the
odd--even lattice. -/
lemma realCpPairBracket_two_mul_half_eq
    (h k : ℕ) (s : ℂ) :
    realCpPairBracket (2 * h) h k s =
      (h : ℂ) ^ (-s) *
        (((2 * k + 1 : ℕ) : ℂ) ^ (-s) -
          2 * ((2 * k + 2 : ℕ) : ℂ) ^ (-s) +
            ((2 * k + 3 : ℕ) : ℂ) ^ (-s)) := by
  unfold realCpPairBracket realDirichletPower
  simp only [nsmul_eq_mul]
  have hleftReal :
      ((2 * h : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) - (h : ℝ) =
        (h : ℝ) * ((2 * k + 1 : ℕ) : ℝ) := by
    push_cast
    ring
  have hcenterReal :
      ((2 * h : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) =
        (h : ℝ) * ((2 * k + 2 : ℕ) : ℝ) := by
    push_cast
    ring
  have hrightReal :
      ((2 * h : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) + (h : ℝ) =
        (h : ℝ) * ((2 * k + 3 : ℕ) : ℝ) := by
    push_cast
    ring
  rw [hleftReal, hrightReal, hcenterReal]
  rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_mul]
  rw [Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity),
    Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity),
    Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity)]
  norm_cast
  ring

/-- Exact finite telescoping identity for the antipodal channel.  The final
odd monomial is retained explicitly; it is the only endpoint term. -/
theorem finiteAntipodalEvenCameraChannel_eq_pairedAlt_prefix
    (h M : ℕ) (s : ℂ) :
    finiteAntipodalEvenCameraChannel h M s =
      2 * (h : ℂ) ^ (-s) *
          (∑ k ∈ Finset.range M, pairedAltTerm s k) +
        (h : ℂ) ^ (-s) * ((2 * M + 1 : ℕ) : ℂ) ^ (-s) := by
  induction M with
  | zero =>
      simp [finiteAntipodalEvenCameraChannel, realDirichletPower]
  | succ M ih =>
      calc
        finiteAntipodalEvenCameraChannel h (M + 1) s =
            finiteAntipodalEvenCameraChannel h M s +
              realCpPairBracket (2 * h) h M s := by
          simp only [finiteAntipodalEvenCameraChannel,
            Finset.sum_range_succ]
          ring
        _ =
            (2 * (h : ℂ) ^ (-s) *
                (∑ k ∈ Finset.range M, pairedAltTerm s k) +
              (h : ℂ) ^ (-s) * ((2 * M + 1 : ℕ) : ℂ) ^ (-s)) +
                realCpPairBracket (2 * h) h M s := by
          rw [ih]
        _ =
            2 * (h : ℂ) ^ (-s) *
                (∑ k ∈ Finset.range (M + 1), pairedAltTerm s k) +
              (h : ℂ) ^ (-s) *
                ((2 * (M + 1) + 1 : ℕ) : ℂ) ^ (-s) := by
          rw [realCpPairBracket_two_mul_half_eq]
          simp only [Finset.sum_range_succ, pairedAltTerm]
          push_cast
          ring_nf

/-- Absolute summability of the paired odd--even terms on the open right
half-plane, extracted from the CPFormal envelope estimate. -/
lemma summable_pairedAltTerm_of_pos_re
    {s : ℂ} (hs : 0 < s.re) :
    Summable (fun k : ℕ ↦ pairedAltTerm s k) := by
  have hs0 : s ≠ 0 := by
    intro hzero
    rw [hzero] at hs
    simp at hs
  have hmajorant :=
    (summable_pairedAltEnvelope hs).mul_left ‖s‖
  exact hmajorant.of_norm_bounded fun k ↦
    norm_pairedAltTerm_le hs0 hs k

/-- The endpoint left by finite antipodal telescoping vanishes whenever
`re(s) > 0`. -/
lemma tendsto_antipodalEvenCamera_endpoint_zero
    (h : ℕ) {s : ℂ} (hs : 0 < s.re) :
    Tendsto
      (fun M : ℕ ↦
        (h : ℂ) ^ (-s) * ((2 * M + 1 : ℕ) : ℂ) ^ (-s))
      atTop (𝓝 0) := by
  have hindexNat :
      Tendsto (fun M : ℕ ↦ 2 * M + 1) atTop atTop :=
    naturalCameraCutoff_tendsto_atTop 2 1 (by norm_num)
  have hindexReal :
      Tendsto (fun M : ℕ ↦ ((2 * M + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hindexNat
  have hrpow :
      Tendsto (fun x : ℝ ↦ x ^ (-s.re)) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop hs
  have hnorm :
      Tendsto
        (fun M : ℕ ↦ ‖((2 * M + 1 : ℕ) : ℂ) ^ (-s)‖)
        atTop (𝓝 0) := by
    have hcomp := hrpow.comp hindexReal
    apply hcomp.congr'
    filter_upwards with M
    have hformula := Complex.norm_cpow_eq_rpow_re_of_pos
      (x := ((2 * M + 1 : ℕ) : ℝ)) (by positivity) (-s)
    simpa [Function.comp_def] using hformula.symm
  have hterm :
      Tendsto (fun M : ℕ ↦ ((2 * M + 1 : ℕ) : ℂ) ^ (-s))
        atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  simpa using Filter.Tendsto.const_mul ((h : ℂ) ^ (-s)) hterm

/-! ## Separating the natural and antipodal blocks at widths four and six -/

lemma empiricalCameraBlock_c4_eq_natural_add_antipodal
    (k : ℕ) (s : ℂ) :
    empiricalCameraBlock EmpiricalCamera.c4 k s =
      realCpSaturatedBracket 4 k s + realCpPairBracket 4 2 k s := by
  simp [empiricalCameraBlock, realCpSaturatedBracket,
    CPFormal.Genuine.Cp.halfRange]

lemma empiricalCameraBlock_c6_eq_natural_add_antipodal
    (k : ℕ) (s : ℂ) :
    empiricalCameraBlock EmpiricalCamera.c6 k s =
      realCpSaturatedBracket 6 k s + realCpPairBracket 6 3 k s := by
  have hsat :
      realCpSaturatedBracket 6 k s =
        realCpPairBracket 6 1 k s + realCpPairBracket 6 2 k s := by
    unfold realCpSaturatedBracket
    rw [show Finset.Icc 1 (CPFormal.Genuine.Cp.halfRange 6) = {1, 2} by
      decide]
    simp
  rw [hsat]
  simp [empiricalCameraBlock]
  ring

lemma summable_c4_antipodalBracket
    {s : ℂ} (hs : 0 < s.re) :
    Summable (fun k : ℕ ↦ realCpPairBracket 4 2 k s) := by
  have hemp := summable_empiricalCameraBlock EmpiricalCamera.c4
    (s := s) (by linarith)
  have hnatural := summable_realCpSaturatedBracket_of_two_le
    4 (by norm_num) (s := s) (by linarith)
  have hdifference := hemp.sub hnatural
  refine hdifference.congr fun k ↦ ?_
  rw [empiricalCameraBlock_c4_eq_natural_add_antipodal]
  ring

lemma summable_c6_antipodalBracket
    {s : ℂ} (hs : 0 < s.re) :
    Summable (fun k : ℕ ↦ realCpPairBracket 6 3 k s) := by
  have hemp := summable_empiricalCameraBlock EmpiricalCamera.c6
    (s := s) (by linarith)
  have hnatural := summable_realCpSaturatedBracket_of_two_le
    6 (by norm_num) (s := s) (by linarith)
  have hdifference := hemp.sub hnatural
  refine hdifference.congr fun k ↦ ?_
  rw [empiricalCameraBlock_c6_eq_natural_add_antipodal]
  ring

/-! ## The extra channel is a scaled paired Genuine channel -/

/-- Abstract antipodal-channel identity once summability of the width-specific
bracket series has been supplied. -/
theorem antipodalEvenCameraChannel_eq_pairedAltChannel_of_summable
    (h : ℕ) {s : ℂ} (hs : 0 < s.re)
    (hbracket :
      Summable (fun k : ℕ ↦ realCpPairBracket (2 * h) h k s)) :
    antipodalEvenCameraChannel h s =
      2 * (h : ℂ) ^ (-s) * pairedAltChannel s := by
  have hleft :
      Tendsto (fun M : ℕ ↦ finiteAntipodalEvenCameraChannel h M s)
        atTop (𝓝 (antipodalEvenCameraChannel h s)) := by
    simpa [finiteAntipodalEvenCameraChannel,
      antipodalEvenCameraChannel] using
        tendsto_const_nhds.add hbracket.tendsto_sum_tsum_nat
  have hpaired :=
    (summable_pairedAltTerm_of_pos_re hs).tendsto_sum_tsum_nat
  have hscaled :
      Tendsto
        (fun M : ℕ ↦
          2 * (h : ℂ) ^ (-s) *
            (∑ k ∈ Finset.range M, pairedAltTerm s k))
        atTop
        (𝓝 (2 * (h : ℂ) ^ (-s) * pairedAltChannel s)) := by
    simpa [pairedAltChannel] using
      Filter.Tendsto.const_mul (2 * (h : ℂ) ^ (-s)) hpaired
  have hright :
      Tendsto
        (fun M : ℕ ↦
          2 * (h : ℂ) ^ (-s) *
              (∑ k ∈ Finset.range M, pairedAltTerm s k) +
            (h : ℂ) ^ (-s) * ((2 * M + 1 : ℕ) : ℂ) ^ (-s))
        atTop
        (𝓝 (2 * (h : ℂ) ^ (-s) * pairedAltChannel s)) := by
    simpa using hscaled.add
      (tendsto_antipodalEvenCamera_endpoint_zero h hs)
  have hfinite :
      Tendsto (fun M : ℕ ↦ finiteAntipodalEvenCameraChannel h M s)
        atTop
        (𝓝 (2 * (h : ℂ) ^ (-s) * pairedAltChannel s)) := by
    exact hright.congr'
      (Filter.Eventually.of_forall fun M ↦
        (finiteAntipodalEvenCameraChannel_eq_pairedAlt_prefix h M s).symm)
  exact tendsto_nhds_unique hleft hfinite

/-- Exact antipodal correction for the empirical width-four camera. -/
theorem antipodalEvenCameraChannel_two_eq_pairedAltChannel
    {s : ℂ} (hs : 0 < s.re) :
    antipodalEvenCameraChannel 2 s =
      2 * (2 : ℂ) ^ (-s) * pairedAltChannel s := by
  exact antipodalEvenCameraChannel_eq_pairedAltChannel_of_summable
    2 hs (by simpa using summable_c4_antipodalBracket hs)

/-- Exact antipodal correction for the empirical width-six camera. -/
theorem antipodalEvenCameraChannel_three_eq_pairedAltChannel
    {s : ℂ} (hs : 0 < s.re) :
    antipodalEvenCameraChannel 3 s =
      2 * (3 : ℂ) ^ (-s) * pairedAltChannel s := by
  exact antipodalEvenCameraChannel_eq_pairedAltChannel_of_summable
    3 hs (by simpa using summable_c6_antipodalBracket hs)

/-! ## Exact split of the empirical full-even characteristics -/

lemma empiricalCameraSeed_c4_eq_natural_add_antipodalSeed
    (s : ℂ) :
    empiricalCameraSeed EmpiricalCamera.c4 s =
      CPFormal.Genuine.Cp.seedSum 4 (dirichletTerm s) +
        realDirichletPower s 2 := by
  simp [empiricalCameraSeed, CPFormal.Genuine.Cp.seedSum,
    CPFormal.Genuine.Cp.halfRange, dirichletTerm,
    realDirichletPower]

lemma empiricalCameraSeed_c6_eq_natural_add_antipodalSeed
    (s : ℂ) :
    empiricalCameraSeed EmpiricalCamera.c6 s =
      CPFormal.Genuine.Cp.seedSum 6 (dirichletTerm s) +
        realDirichletPower s 3 := by
  have hseed :
      CPFormal.Genuine.Cp.seedSum 6 (dirichletTerm s) =
        dirichletTerm s 1 + dirichletTerm s 2 := by
    unfold CPFormal.Genuine.Cp.seedSum
    rw [show
      Finset.Icc (1 : ℤ) (CPFormal.Genuine.Cp.halfRange 6 : ℤ) = {1, 2} by
        ext n
        simp only [CPFormal.Genuine.Cp.halfRange, Finset.mem_Icc,
          Finset.mem_insert, Finset.mem_singleton]
        norm_num
        omega]
    simp
  rw [hseed]
  simp [empiricalCameraSeed, dirichletTerm, realDirichletPower]
  ring

lemma tsum_empiricalCameraBlock_c4_eq_natural_add_antipodal
    {s : ℂ} (hs : 0 < s.re) :
    (∑' k : ℕ, empiricalCameraBlock EmpiricalCamera.c4 k s) =
      (∑' k : ℕ, realCpSaturatedBracket 4 k s) +
        ∑' k : ℕ, realCpPairBracket 4 2 k s := by
  have hnatural := summable_realCpSaturatedBracket_of_two_le
    4 (by norm_num) (s := s) (by linarith)
  have hantipodal := summable_c4_antipodalBracket hs
  calc
    (∑' k : ℕ, empiricalCameraBlock EmpiricalCamera.c4 k s) =
        ∑' k : ℕ,
          (realCpSaturatedBracket 4 k s + realCpPairBracket 4 2 k s) := by
      exact tsum_congr fun k ↦
        empiricalCameraBlock_c4_eq_natural_add_antipodal k s
    _ = (∑' k : ℕ, realCpSaturatedBracket 4 k s) +
          ∑' k : ℕ, realCpPairBracket 4 2 k s :=
      hnatural.tsum_add hantipodal

lemma tsum_empiricalCameraBlock_c6_eq_natural_add_antipodal
    {s : ℂ} (hs : 0 < s.re) :
    (∑' k : ℕ, empiricalCameraBlock EmpiricalCamera.c6 k s) =
      (∑' k : ℕ, realCpSaturatedBracket 6 k s) +
        ∑' k : ℕ, realCpPairBracket 6 3 k s := by
  have hnatural := summable_realCpSaturatedBracket_of_two_le
    6 (by norm_num) (s := s) (by linarith)
  have hantipodal := summable_c6_antipodalBracket hs
  calc
    (∑' k : ℕ, empiricalCameraBlock EmpiricalCamera.c6 k s) =
        ∑' k : ℕ,
          (realCpSaturatedBracket 6 k s + realCpPairBracket 6 3 k s) := by
      exact tsum_congr fun k ↦
        empiricalCameraBlock_c6_eq_natural_add_antipodal k s
    _ = (∑' k : ℕ, realCpSaturatedBracket 6 k s) +
          ∑' k : ℕ, realCpPairBracket 6 3 k s :=
      hnatural.tsum_add hantipodal

/-- The full empirical width-four characteristic is the truncated natural
width-four chart plus its explicitly restored antipodal channel. -/
theorem empiricalCameraCharacteristic_c4_eq_natural_add_antipodal
    {s : ℂ} (hs : 0 < s.re) :
    empiricalCameraCharacteristic EmpiricalCamera.c4 s =
      bracketedDirichletChart 4 s + antipodalEvenCameraChannel 2 s := by
  rw [show empiricalCameraCharacteristic EmpiricalCamera.c4 s =
      empiricalCameraSeed EmpiricalCamera.c4 s +
        ∑' k : ℕ, empiricalCameraBlock EmpiricalCamera.c4 k s by rfl]
  rw [empiricalCameraSeed_c4_eq_natural_add_antipodalSeed,
    tsum_empiricalCameraBlock_c4_eq_natural_add_antipodal hs]
  unfold bracketedDirichletChart antipodalEvenCameraChannel
  norm_num
  ring

/-- The full empirical width-six characteristic is the truncated natural
width-six chart plus its explicitly restored antipodal channel. -/
theorem empiricalCameraCharacteristic_c6_eq_natural_add_antipodal
    {s : ℂ} (hs : 0 < s.re) :
    empiricalCameraCharacteristic EmpiricalCamera.c6 s =
      bracketedDirichletChart 6 s + antipodalEvenCameraChannel 3 s := by
  rw [show empiricalCameraCharacteristic EmpiricalCamera.c6 s =
      empiricalCameraSeed EmpiricalCamera.c6 s +
        ∑' k : ℕ, empiricalCameraBlock EmpiricalCamera.c6 k s by rfl]
  rw [empiricalCameraSeed_c6_eq_natural_add_antipodalSeed,
    tsum_empiricalCameraBlock_c6_eq_natural_add_antipodal hs]
  unfold bracketedDirichletChart antipodalEvenCameraChannel
  norm_num
  ring

/-! ## Full-even factors and critical-strip continuation -/

/-- Restoring the antipodal channel changes the natural even-camera factor
into the empirical full-even factor. -/
lemma naturalEvenCameraFactor_add_antipodalFactor_eq_fullEven
    (h : ℕ) (hh : 1 ≤ h) (s : ℂ) :
    naturalEvenCameraFactor (2 * h) s +
        2 * (h : ℂ) ^ (-s) * (1 - (2 : ℂ) ^ (1 - s)) =
      empiricalFullEvenCameraFactor (2 * h) s := by
  have htwo : (2 : ℂ) ^ (1 - s) =
      (2 : ℂ) * (2 : ℂ) ^ (-s) := by
    have htwo0 : (2 : ℂ) ≠ 0 := by norm_num
    simpa [sub_eq_add_neg] using
      (Complex.cpow_add (x := (2 : ℂ)) (1 : ℂ) (-s) htwo0)
  have hproduct : ((2 * h : ℕ) : ℂ) ^ (-s) =
      (2 : ℂ) ^ (-s) * (h : ℂ) ^ (-s) := by
    simpa using Complex.natCast_mul_natCast_cpow 2 h (-s)
  have hhalf : (2 * h) / 2 = h := by omega
  have htwoLe : 2 ≤ 2 * h := by omega
  unfold naturalEvenCameraFactor empiricalFullEvenCameraFactor
  rw [hhalf, htwo, hproduct]
  push_cast [Nat.cast_sub htwoLe]
  ring

/-- The empirical camera labelled four has the full-even factor, not the
middle-omitting natural-even factor. -/
theorem empiricalCameraCharacteristic_c4_eq_fullEvenCameraFactor_mul_genuineContinuation
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    empiricalCameraCharacteristic EmpiricalCamera.c4 s =
      empiricalFullEvenCameraFactor 4 s * genuineContinuation s := by
  rw [empiricalCameraCharacteristic_c4_eq_natural_add_antipodal hs.1,
    bracketedDirichletChart_eq_naturalCameraFactor_mul_genuineContinuation
      4 (by norm_num) hs,
    antipodalEvenCameraChannel_two_eq_pairedAltChannel hs.1,
    pairedAltChannel_eq_genuineContinuation hs]
  rw [naturalCameraFactor_eq_even (by decide : Even 4)]
  change
    naturalEvenCameraFactor (2 * 2) s * genuineContinuation s +
        2 * (2 : ℂ) ^ (-s) *
          ((1 - (2 : ℂ) ^ (1 - s)) * genuineContinuation s) =
      empiricalFullEvenCameraFactor (2 * 2) s * genuineContinuation s
  calc
    _ = (naturalEvenCameraFactor (2 * 2) s +
          2 * (2 : ℂ) ^ (-s) * (1 - (2 : ℂ) ^ (1 - s))) *
            genuineContinuation s := by ring
    _ = empiricalFullEvenCameraFactor (2 * 2) s * genuineContinuation s := by
      simpa using congrArg (fun z : ℂ ↦ z * genuineContinuation s)
        (naturalEvenCameraFactor_add_antipodalFactor_eq_fullEven
          2 (by norm_num) s)

/-- The empirical camera labelled six has the full-even factor, not the
middle-omitting natural-even factor. -/
theorem empiricalCameraCharacteristic_c6_eq_fullEvenCameraFactor_mul_genuineContinuation
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    empiricalCameraCharacteristic EmpiricalCamera.c6 s =
      empiricalFullEvenCameraFactor 6 s * genuineContinuation s := by
  rw [empiricalCameraCharacteristic_c6_eq_natural_add_antipodal hs.1,
    bracketedDirichletChart_eq_naturalCameraFactor_mul_genuineContinuation
      6 (by norm_num) hs,
    antipodalEvenCameraChannel_three_eq_pairedAltChannel hs.1,
    pairedAltChannel_eq_genuineContinuation hs]
  rw [naturalCameraFactor_eq_even (by decide : Even 6)]
  change
    naturalEvenCameraFactor (2 * 3) s * genuineContinuation s +
        2 * (3 : ℂ) ^ (-s) *
          ((1 - (2 : ℂ) ^ (1 - s)) * genuineContinuation s) =
      empiricalFullEvenCameraFactor (2 * 3) s * genuineContinuation s
  calc
    _ = (naturalEvenCameraFactor (2 * 3) s +
          2 * (3 : ℂ) ^ (-s) * (1 - (2 : ℂ) ^ (1 - s))) *
            genuineContinuation s := by ring
    _ = empiricalFullEvenCameraFactor (2 * 3) s * genuineContinuation s := by
      simpa using congrArg (fun z : ℂ ↦ z * genuineContinuation s)
        (naturalEvenCameraFactor_add_antipodalFactor_eq_fullEven
          3 (by norm_num) s)

/-! ## Uniform continuation table for all six empirical cameras -/

lemma empiricalCameraCharacteristic_c2_eq_bracketedDirichletChart
    (s : ℂ) :
    empiricalCameraCharacteristic EmpiricalCamera.c2 s =
      bracketedDirichletChart 4 s := by
  simp [empiricalCameraCharacteristic, empiricalCameraSeed,
    empiricalCameraBlock, bracketedDirichletChart,
    realCpSaturatedBracket, CPFormal.Genuine.Cp.seedSum,
    CPFormal.Genuine.Cp.halfRange, dirichletTerm, realDirichletPower]

lemma empiricalCameraCharacteristic_c3_eq_bracketedDirichletChart
    (s : ℂ) :
    empiricalCameraCharacteristic EmpiricalCamera.c3 s =
      bracketedDirichletChart 3 s := by
  simp [empiricalCameraCharacteristic, empiricalCameraSeed,
    empiricalCameraBlock, bracketedDirichletChart,
    realCpSaturatedBracket, CPFormal.Genuine.Cp.seedSum,
    CPFormal.Genuine.Cp.halfRange, dirichletTerm, realDirichletPower]

lemma empiricalCameraCharacteristic_c5_eq_bracketedDirichletChart
    (s : ℂ) :
    empiricalCameraCharacteristic EmpiricalCamera.c5 s =
      bracketedDirichletChart 5 s := by
  have hNat :
      Finset.Icc (1 : ℕ) 2 = {1, 2} := by
    decide
  have hInt :
      Finset.Icc (1 : ℤ) 2 = {1, 2} := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  simp [empiricalCameraCharacteristic, empiricalCameraSeed,
    empiricalCameraBlock, bracketedDirichletChart,
    realCpSaturatedBracket, CPFormal.Genuine.Cp.seedSum,
    CPFormal.Genuine.Cp.halfRange, dirichletTerm, realDirichletPower,
    hNat, hInt]

lemma empiricalCameraCharacteristic_c7_eq_bracketedDirichletChart
    (s : ℂ) :
    empiricalCameraCharacteristic EmpiricalCamera.c7 s =
      bracketedDirichletChart 7 s := by
  have hNat :
      Finset.Icc (1 : ℕ) 3 = {1, 2, 3} := by
    decide
  have hInt :
      Finset.Icc (1 : ℤ) 3 = {1, 2, 3} := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  simp [empiricalCameraCharacteristic, empiricalCameraSeed,
    empiricalCameraBlock, bracketedDirichletChart,
    realCpSaturatedBracket, CPFormal.Genuine.Cp.seedSum,
    CPFormal.Genuine.Cp.halfRange, dirichletTerm, realDirichletPower,
    hNat, hInt]

/-- Faithful continuation table for every member of the empirical six-camera
stack.  The `c4` and `c6` branches use the full-even factor with the antipodal
channel; the other four branches use their existing natural factors. -/
theorem empiricalCameraCharacteristic_eq_limitingFactor_mul_genuineContinuation
    (camera : EmpiricalCamera) {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    empiricalCameraCharacteristic camera s =
      empiricalLimitingFactor camera s * genuineContinuation s := by
  cases camera with
  | c2 =>
      rw [empiricalCameraCharacteristic_c2_eq_bracketedDirichletChart,
        bracketedDirichletChart_eq_naturalCameraFactor_mul_genuineContinuation
          4 (by norm_num) hs,
        naturalCameraFactor_eq_even (by decide : Even 4)]
      rfl
  | c3 =>
      rw [empiricalCameraCharacteristic_c3_eq_bracketedDirichletChart,
        bracketedDirichletChart_eq_naturalCameraFactor_mul_genuineContinuation
          3 (by norm_num) hs,
        naturalCameraFactor_eq_odd (by decide : Odd 3)]
      rfl
  | c4 =>
      simpa [empiricalLimitingFactor] using
        empiricalCameraCharacteristic_c4_eq_fullEvenCameraFactor_mul_genuineContinuation hs
  | c5 =>
      rw [empiricalCameraCharacteristic_c5_eq_bracketedDirichletChart,
        bracketedDirichletChart_eq_naturalCameraFactor_mul_genuineContinuation
          5 (by norm_num) hs,
        naturalCameraFactor_eq_odd (by decide : Odd 5)]
      rfl
  | c6 =>
      simpa [empiricalLimitingFactor] using
        empiricalCameraCharacteristic_c6_eq_fullEvenCameraFactor_mul_genuineContinuation hs
  | c7 =>
      rw [empiricalCameraCharacteristic_c7_eq_bracketedDirichletChart,
        bracketedDirichletChart_eq_naturalCameraFactor_mul_genuineContinuation
          7 (by norm_num) hs,
        naturalCameraFactor_eq_odd (by decide : Odd 7)]
      rfl

/-- A zero of the canonical Genuine continuation is a simultaneous zero of
all six empirical infinite characteristics.  No nonvanishing assertion about
the empirical factors is needed in this direction. -/
theorem empiricalCameraCharacteristic_zero_of_genuineContinuation_zero
    (camera : EmpiricalCamera) {s : ℂ}
    (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    empiricalCameraCharacteristic camera s = 0 := by
  rw [empiricalCameraCharacteristic_eq_limitingFactor_mul_genuineContinuation
    camera hs, hzero, mul_zero]

/-- Simultaneous-zero form of the empirical six-camera continuation table. -/
theorem empiricalSixCamera_zero_of_genuineContinuation_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    ∀ camera, empiricalCameraCharacteristic camera s = 0 := by
  intro camera
  exact empiricalCameraCharacteristic_zero_of_genuineContinuation_zero
    camera hs hzero

/-- Every intrinsic real spectral resonance is recognized by all six
empirical infinite cameras. -/
theorem empiricalSixCamera_zero_of_realSpectralResonance
    (time : ℝ) (hres : IsRealSpectralResonance time) :
    ∀ camera,
      empiricalCameraCharacteristic camera (criticalLineParameter time) = 0 := by
  apply empiricalSixCamera_zero_of_genuineContinuation_zero
    (criticalLineParameter_mem_genuineCriticalStrip time)
  simpa [IsRealSpectralResonance, realSpectralGenuine] using hres

/-- Closed six-camera cutoff capstone: a single canonical real-spectral
resonance supplies the common-zero premise, hence the exact tail-stack identity
and the displayed time-dependent `M^(-3)` collective energy upper bound. -/
theorem empiricalSixCamera_resonant_cutoffTail_and_rate
    (M : ℕ) (hM : 1 ≤ M) (time : ℝ)
    (hres : IsRealSpectralResonance time) :
    finiteEmpiricalCameraStack M (criticalLineParameter time) =
        (fun camera ↦
          -empiricalCameraCutoffTailStack M
            (criticalLineParameter time) camera) ∧
      finiteEmpiricalCollectiveRawEnergy M (criticalLineParameter time) =
        empiricalCollectiveCutoffTailEnergy M (criticalLineParameter time) ∧
      finiteEmpiricalCollectiveRawEnergy M (criticalLineParameter time) ≤
        empiricalCollectiveCriticalTailEnergyBound M time := by
  exact empiricalSixCamera_critical_cutoffTail_and_rate M hM time
    (empiricalSixCamera_zero_of_realSpectralResonance time hres)

end

end GenuineZeroUniformAtlasEnergy

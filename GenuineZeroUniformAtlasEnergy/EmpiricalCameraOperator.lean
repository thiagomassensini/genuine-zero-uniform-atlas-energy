import GenuineZeroUniformAtlasEnergy.EmpiricalCameraGeometry
import GenuineZeroUniformAtlasEnergy.NativeCutoffTail

/-!
# Exact operator for the empirical six-camera stack

The cutoff experiments use the six finite geometries recorded in
`EmpiricalCameraGeometry`.  This file builds their complex operator directly
from the analytic centered-pair primitive `realCpPairBracket`.

For the cameras labelled four and six the stored radius set includes the
antipodal channel.  Consequently these definitions deliberately do not pass
through the natural-even-camera API, whose middle channel is omitted.

Every camera is split exactly into a visible finite prefix and an unresolved
summable tail on `re(s) > -1`.  At a common zero of the six infinite
characteristics, the whole finite stack is therefore the negative tail stack,
and its collective raw energy is exactly the sum of the six tail energies.
-/

open scoped BigOperators

namespace GenuineZeroUniformAtlasEnergy

open CPFormal.Analytic.Cp

noncomputable section

/-! ## Exact finite and infinite cameras -/

/-- Positive seed stored by one empirical camera. -/
def empiricalCameraSeed (camera : EmpiricalCamera) (s : ℂ) : ℂ :=
  ∑ radius ∈ camera.radii,
    realDirichletPower s (radius : ℝ)

/-- One centered bracket block of an empirical camera. -/
def empiricalCameraBlock
    (camera : EmpiricalCamera) (k : ℕ) (s : ℂ) : ℂ :=
  ∑ radius ∈ camera.radii,
    realCpPairBracket camera.period radius k s

/-- Finite empirical characteristic through the first `M` centered blocks. -/
def finiteEmpiricalCameraCharacteristic
    (camera : EmpiricalCamera) (M : ℕ) (s : ℂ) : ℂ :=
  empiricalCameraSeed camera s +
    ∑ k ∈ Finset.range M, empiricalCameraBlock camera k s

/-- Infinite empirical characteristic, defined by the absolutely convergent
bracket series on `re(s) > -1`. -/
def empiricalCameraCharacteristic
    (camera : EmpiricalCamera) (s : ℂ) : ℂ :=
  empiricalCameraSeed camera s +
    ∑' k : ℕ, empiricalCameraBlock camera k s

/-- Bracket information not yet visible after cutoff `M`. -/
def empiricalCameraCutoffTail
    (camera : EmpiricalCamera) (M : ℕ) (s : ℂ) : ℂ :=
  ∑' k : ℕ, empiricalCameraBlock camera (k + M) s

/-- The six finite characteristics as one camera-indexed vector. -/
def finiteEmpiricalCameraStack (M : ℕ) (s : ℂ) : EmpiricalCamera → ℂ :=
  fun camera ↦ finiteEmpiricalCameraCharacteristic camera M s

/-- The six infinite characteristics as one camera-indexed vector. -/
def empiricalCameraStack (s : ℂ) : EmpiricalCamera → ℂ :=
  fun camera ↦ empiricalCameraCharacteristic camera s

/-- The six unresolved cutoff tails as one camera-indexed vector. -/
def empiricalCameraCutoffTailStack
    (M : ℕ) (s : ℂ) : EmpiricalCamera → ℂ :=
  fun camera ↦ empiricalCameraCutoffTail camera M s

/-- Collective unnormalised quadratic energy of the finite six-camera stack. -/
def finiteEmpiricalCollectiveRawEnergy (M : ℕ) (s : ℂ) : ℝ :=
  ∑ camera : EmpiricalCamera,
    Complex.normSq (finiteEmpiricalCameraCharacteristic camera M s)

/-- Collective unnormalised quadratic energy of the unresolved tail stack. -/
def empiricalCollectiveCutoffTailEnergy (M : ℕ) (s : ℂ) : ℝ :=
  ∑ camera : EmpiricalCamera,
    Complex.normSq (empiricalCameraCutoffTail camera M s)

/-! ## Absolute convergence for the stored radii -/

/-- Finite second-difference constant for one empirical camera. -/
def empiricalCameraBracketMajorantConstant
    (camera : EmpiricalCamera) (s : ℂ) : ℝ :=
  ∑ radius ∈ camera.radii,
    2 * ‖s * (s + 1)‖ * (radius : ℝ) ^ 2

/-- Every stored leg leaves the left endpoint of every block beyond `k+1`.
This uses `radius < period`, and therefore also covers the antipodal channels
of the cameras labelled four and six. -/
lemma natCast_add_one_le_empirical_center_sub_radius
    (camera : EmpiricalCamera) {radius k : ℕ}
    (hradius : radius ∈ camera.radii) :
    ((k + 1 : ℕ) : ℝ) ≤
      (camera.period : ℝ) * ((k + 1 : ℕ) : ℝ) - (radius : ℝ) := by
  have hradiusLt : radius < camera.period :=
    camera.radius_lt_period hradius
  have hradiusLe : radius ≤ camera.period - 1 := by
    omega
  have hperiodOne : 1 ≤ camera.period := by
    cases camera <;> norm_num
  have hperiodOneReal : (1 : ℝ) ≤ (camera.period : ℝ) := by
    exact_mod_cast hperiodOne
  have hperiodNonneg : 0 ≤ (camera.period : ℝ) - 1 :=
    sub_nonneg.mpr hperiodOneReal
  have hkNat : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
  have hk : 1 ≤ ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast hkNat
  have hradiusRealNat :
      (radius : ℝ) ≤ ((camera.period - 1 : ℕ) : ℝ) := by
    exact_mod_cast hradiusLe
  have hperiodCast :
      ((camera.period - 1 : ℕ) : ℝ) = (camera.period : ℝ) - 1 := by
    rw [Nat.cast_sub hperiodOne]
    norm_num
  have hradiusReal :
      (radius : ℝ) ≤ (camera.period : ℝ) - 1 := by
    calc
      (radius : ℝ) ≤ ((camera.period - 1 : ℕ) : ℝ) := hradiusRealNat
      _ = (camera.period : ℝ) - 1 := hperiodCast
  nlinarith [mul_nonneg hperiodNonneg (sub_nonneg.mpr hk)]

/-- Pointwise centered-second-difference estimate for every stored leg. -/
lemma norm_empiricalCameraPairBracket_le
    (camera : EmpiricalCamera) {radius k : ℕ}
    {s : ℂ} (hs : -1 < s.re)
    (hradius : radius ∈ camera.radii) :
    ‖realCpPairBracket camera.period radius k s‖ ≤
      (2 * ‖s * (s + 1)‖ * (radius : ℝ) ^ 2) *
        ((k + 1 : ℕ) : ℝ) ^ (-s.re - 2) := by
  have hleftLower :=
    natCast_add_one_le_empirical_center_sub_radius
      camera (k := k) hradius
  have hkpos : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
  have hleft :
      0 < (camera.period : ℝ) * ((k + 1 : ℕ) : ℝ) - (radius : ℝ) :=
    lt_of_lt_of_le hkpos hleftLower
  have hraw := norm_realDirichletPower_centeredSecondDifference_le
    hs (show 0 ≤ (radius : ℝ) by positivity) hleft
  have hpower :
      ((camera.period : ℝ) * ((k + 1 : ℕ) : ℝ) - (radius : ℝ)) ^
          (-s.re - 2) ≤
        ((k + 1 : ℕ) : ℝ) ^ (-s.re - 2) :=
    Real.rpow_le_rpow_of_nonpos hkpos hleftLower (by linarith [hs])
  calc
    ‖realCpPairBracket camera.period radius k s‖ ≤
        2 *
          (‖s * (s + 1)‖ *
            ((camera.period : ℝ) * ((k + 1 : ℕ) : ℝ) - (radius : ℝ)) ^
              (-s.re - 2)) *
          (radius : ℝ) ^ 2 := by
      simpa [realCpPairBracket] using hraw
    _ = (2 * ‖s * (s + 1)‖ * (radius : ℝ) ^ 2) *
          (((camera.period : ℝ) * ((k + 1 : ℕ) : ℝ) - (radius : ℝ)) ^
            (-s.re - 2)) := by ring
    _ ≤ (2 * ‖s * (s + 1)‖ * (radius : ℝ) ^ 2) *
          ((k + 1 : ℕ) : ℝ) ^ (-s.re - 2) :=
      mul_le_mul_of_nonneg_left hpower (by positivity)

/-- One full empirical block is bounded by a single shifted `p`-series. -/
lemma norm_empiricalCameraBlock_le
    (camera : EmpiricalCamera) {k : ℕ}
    {s : ℂ} (hs : -1 < s.re) :
    ‖empiricalCameraBlock camera k s‖ ≤
      empiricalCameraBracketMajorantConstant camera s *
        ((k + 1 : ℕ) : ℝ) ^ (-s.re - 2) := by
  classical
  unfold empiricalCameraBlock empiricalCameraBracketMajorantConstant
  calc
    ‖∑ radius ∈ camera.radii,
        realCpPairBracket camera.period radius k s‖ ≤
        ∑ radius ∈ camera.radii,
          ‖realCpPairBracket camera.period radius k s‖ := norm_sum_le _ _
    _ ≤ ∑ radius ∈ camera.radii,
          (2 * ‖s * (s + 1)‖ * (radius : ℝ) ^ 2) *
            ((k + 1 : ℕ) : ℝ) ^ (-s.re - 2) := by
      exact Finset.sum_le_sum fun radius hradius ↦
        norm_empiricalCameraPairBracket_le camera hs hradius
    _ = (∑ radius ∈ camera.radii,
          2 * ‖s * (s + 1)‖ * (radius : ℝ) ^ 2) *
            ((k + 1 : ℕ) : ℝ) ^ (-s.re - 2) := by
      rw [Finset.sum_mul]

/-- Absolute summability of an empirical block series on `re(s) > -1`. -/
theorem summable_norm_empiricalCameraBlock
    (camera : EmpiricalCamera) {s : ℂ} (hs : -1 < s.re) :
    Summable (fun k : ℕ ↦ ‖empiricalCameraBlock camera k s‖) := by
  have hpower := summable_nat_add_one_rpow_neg_re_sub_two hs
  have hmajorant :=
    hpower.mul_left (empiricalCameraBracketMajorantConstant camera s)
  exact hmajorant.of_norm_bounded
    (fun k ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact norm_empiricalCameraBlock_le camera hs)

/-- Complex summability follows from absolute summability. -/
theorem summable_empiricalCameraBlock
    (camera : EmpiricalCamera) {s : ℂ} (hs : -1 < s.re) :
    Summable (fun k : ℕ ↦ empiricalCameraBlock camera k s) :=
  (summable_norm_empiricalCameraBlock camera hs).of_norm

/-! ## Exact prefix--tail identities -/

/-- Exact decomposition of every infinite empirical characteristic. -/
theorem empiricalCameraCharacteristic_eq_finite_add_cutoffTail
    (camera : EmpiricalCamera) (M : ℕ)
    {s : ℂ} (hs : -1 < s.re) :
    empiricalCameraCharacteristic camera s =
      finiteEmpiricalCameraCharacteristic camera M s +
        empiricalCameraCutoffTail camera M s := by
  unfold empiricalCameraCharacteristic finiteEmpiricalCameraCharacteristic
    empiricalCameraCutoffTail
  have hsplit :=
    (summable_empiricalCameraBlock camera hs).sum_add_tsum_nat_add M
  rw [← hsplit]
  ring

/-- At a zero of one infinite empirical camera, its finite residue is exactly
the negative unresolved tail. -/
theorem finiteEmpiricalCameraCharacteristic_eq_neg_cutoffTail_of_zero
    (camera : EmpiricalCamera) (M : ℕ)
    {s : ℂ} (hs : -1 < s.re)
    (hzero : empiricalCameraCharacteristic camera s = 0) :
    finiteEmpiricalCameraCharacteristic camera M s =
      -empiricalCameraCutoffTail camera M s := by
  have hsplit :=
    empiricalCameraCharacteristic_eq_finite_add_cutoffTail camera M hs
  calc
    finiteEmpiricalCameraCharacteristic camera M s =
        (finiteEmpiricalCameraCharacteristic camera M s +
          empiricalCameraCutoffTail camera M s) -
            empiricalCameraCutoffTail camera M s := by ring
    _ = empiricalCameraCharacteristic camera s -
          empiricalCameraCutoffTail camera M s := by rw [← hsplit]
    _ = -empiricalCameraCutoffTail camera M s := by rw [hzero]; ring

/-- Componentwise exact tail identity for the complete six-camera stack. -/
theorem finiteEmpiricalCameraStack_eq_neg_cutoffTailStack_of_zero
    (M : ℕ) {s : ℂ} (hs : -1 < s.re)
    (hzero : ∀ camera, empiricalCameraCharacteristic camera s = 0) :
    finiteEmpiricalCameraStack M s =
      fun camera ↦ -empiricalCameraCutoffTailStack M s camera := by
  funext camera
  exact finiteEmpiricalCameraCharacteristic_eq_neg_cutoffTail_of_zero
    camera M hs (hzero camera)

/-- Under a common six-camera zero, finite collective energy is literally the
unresolved tail energy, with no discarded error term. -/
theorem finiteEmpiricalCollectiveRawEnergy_eq_cutoffTailEnergy_of_zero
    (M : ℕ) {s : ℂ} (hs : -1 < s.re)
    (hzero : ∀ camera, empiricalCameraCharacteristic camera s = 0) :
    finiteEmpiricalCollectiveRawEnergy M s =
      empiricalCollectiveCutoffTailEnergy M s := by
  classical
  unfold finiteEmpiricalCollectiveRawEnergy empiricalCollectiveCutoffTailEnergy
  apply Finset.sum_congr rfl
  intro camera _hcamera
  rw [finiteEmpiricalCameraCharacteristic_eq_neg_cutoffTail_of_zero
    camera M hs (hzero camera)]
  simp

/-- All-six exact cutoff package: vector residue and collective energy are
simultaneously identified with their unresolved tails. -/
theorem empiricalSixCamera_exact_cutoffTail_and_energy
    (M : ℕ) {s : ℂ} (hs : -1 < s.re)
    (hzero : ∀ camera, empiricalCameraCharacteristic camera s = 0) :
    finiteEmpiricalCameraStack M s =
        (fun camera ↦ -empiricalCameraCutoffTailStack M s camera) ∧
      finiteEmpiricalCollectiveRawEnergy M s =
        empiricalCollectiveCutoffTailEnergy M s := by
  exact ⟨
    finiteEmpiricalCameraStack_eq_neg_cutoffTailStack_of_zero M hs hzero,
    finiteEmpiricalCollectiveRawEnergy_eq_cutoffTailEnergy_of_zero M hs hzero⟩

/-! ## Critical-line cutoff rates -/

/-- Explicit amplitude majorant for one empirical critical-line tail. -/
def empiricalCameraCriticalTailBound
    (camera : EmpiricalCamera) (M : ℕ) (time : ℝ) : ℝ :=
  (2 / 3 : ℝ) *
    empiricalCameraBracketMajorantConstant camera (criticalLineParameter time) *
      (M : ℝ) ^ (-(3 / 2 : ℝ))

/-- Collective squared critical-line majorant for the six empirical tails. -/
def empiricalCollectiveCriticalTailEnergyBound (M : ℕ) (time : ℝ) : ℝ :=
  ∑ camera : EmpiricalCamera,
    (empiricalCameraCriticalTailBound camera M time) ^ 2

/-- For each fixed time, every empirical critical-line tail is bounded by the
displayed time-dependent multiple of `M^(-3/2)`, including the antipodal
channels of the cameras labelled four and six. -/
theorem norm_empiricalCameraCutoffTail_critical_le
    (camera : EmpiricalCamera) (M : ℕ) (hM : 1 ≤ M) (time : ℝ) :
    ‖empiricalCameraCutoffTail camera M (criticalLineParameter time)‖ ≤
      empiricalCameraCriticalTailBound camera M time := by
  let s : ℂ := criticalLineParameter time
  let C : ℝ := empiricalCameraBracketMajorantConstant camera s
  have hs : -1 < s.re := by
    dsimp [s]
    norm_num [criticalLineParameter_re]
  have hbase :
      Summable (fun k : ℕ =>
        ((k : ℝ) + 1) ^ (-(1 / 2 : ℝ) - 2)) := by
    simpa [s, criticalLineParameter_re] using
      (summable_nat_add_one_rpow_neg_re_sub_two (s := s) hs)
  have hpowerSummable :
      Summable (fun k : ℕ =>
        ((k : ℝ) + (M : ℝ) + 1) ^ (-(1 / 2 : ℝ) - 2)) := by
    refine Summable.of_nonneg_of_le ?_ ?_ hbase
    · intro k
      exact Real.rpow_nonneg (by positivity) _
    · intro k
      have hkpos : 0 < (k : ℝ) + 1 := by positivity
      have hshift :
          (k : ℝ) + 1 ≤ (k : ℝ) + (M : ℝ) + 1 := by
        have hMnonneg : 0 ≤ (M : ℝ) := by positivity
        linarith
      exact Real.rpow_le_rpow_of_nonpos hkpos hshift (by norm_num)
  have hmajorantHasSum :
      HasSum
        (fun k : ℕ =>
          C * ((k : ℝ) + (M : ℝ) + 1) ^ (-(1 / 2 : ℝ) - 2))
        (C * ∑' k : ℕ,
          ((k : ℝ) + (M : ℝ) + 1) ^ (-(1 / 2 : ℝ) - 2)) :=
    hpowerSummable.hasSum.mul_left C
  have hpointwise : ∀ k : ℕ,
      ‖empiricalCameraBlock camera (k + M) s‖ ≤
        C * ((k : ℝ) + (M : ℝ) + 1) ^ (-(1 / 2 : ℝ) - 2) := by
    intro k
    simpa [C, s, criticalLineParameter_re, Nat.cast_add] using
      (norm_empiricalCameraBlock_le
        (camera := camera) (k := k + M) (s := s) hs)
  have hnorm :
      ‖∑' k : ℕ, empiricalCameraBlock camera (k + M) s‖ ≤
        C * ∑' k : ℕ,
          ((k : ℝ) + (M : ℝ) + 1) ^ (-(1 / 2 : ℝ) - 2) :=
    tsum_of_norm_bounded hmajorantHasSum hpointwise
  have hC : 0 ≤ C := by
    dsimp [C]
    unfold empiricalCameraBracketMajorantConstant
    positivity
  calc
    ‖empiricalCameraCutoffTail camera M (criticalLineParameter time)‖ =
        ‖∑' k : ℕ, empiricalCameraBlock camera (k + M) s‖ := by
      rfl
    _ ≤ C * ∑' k : ℕ,
        ((k : ℝ) + (M : ℝ) + 1) ^ (-(1 / 2 : ℝ) - 2) := hnorm
    _ ≤ C * ((2 / 3 : ℝ) * (M : ℝ) ^ (-(3 / 2 : ℝ))) :=
      mul_le_mul_of_nonneg_left (criticalTailPower_tsum_le M hM) hC
    _ = empiricalCameraCriticalTailBound camera M time := by
      simp [empiricalCameraCriticalTailBound, C, s]
      ring

/-- At a critical-line zero and each fixed time, one empirical finite residue
has the displayed time-dependent `M^(-3/2)` amplitude and `M^(-3)` raw-energy
upper bounds. -/
theorem finiteEmpiricalCamera_critical_cutoffTail_and_rate
    (camera : EmpiricalCamera) (M : ℕ) (hM : 1 ≤ M) (time : ℝ)
    (hzero : empiricalCameraCharacteristic camera
      (criticalLineParameter time) = 0) :
    finiteEmpiricalCameraCharacteristic camera M
          (criticalLineParameter time) =
        -empiricalCameraCutoffTail camera M (criticalLineParameter time) ∧
      ‖finiteEmpiricalCameraCharacteristic camera M
          (criticalLineParameter time)‖ ≤
        empiricalCameraCriticalTailBound camera M time ∧
      Complex.normSq
          (finiteEmpiricalCameraCharacteristic camera M
            (criticalLineParameter time)) ≤
        (empiricalCameraCriticalTailBound camera M time) ^ 2 := by
  have htail :
      finiteEmpiricalCameraCharacteristic camera M
          (criticalLineParameter time) =
        -empiricalCameraCutoffTail camera M (criticalLineParameter time) :=
    finiteEmpiricalCameraCharacteristic_eq_neg_cutoffTail_of_zero
      camera M (by norm_num [criticalLineParameter_re]) hzero
  have hnormTail :=
    norm_empiricalCameraCutoffTail_critical_le camera M hM time
  have hnorm :
      ‖finiteEmpiricalCameraCharacteristic camera M
          (criticalLineParameter time)‖ ≤
        empiricalCameraCriticalTailBound camera M time := by
    rw [htail, norm_neg]
    exact hnormTail
  have hboundNonneg :
      0 ≤ empiricalCameraCriticalTailBound camera M time := by
    unfold empiricalCameraCriticalTailBound
      empiricalCameraBracketMajorantConstant
    positivity
  have hsquare :
      ‖finiteEmpiricalCameraCharacteristic camera M
          (criticalLineParameter time)‖ ^ 2 ≤
        (empiricalCameraCriticalTailBound camera M time) ^ 2 := by
    have hproduct := mul_nonneg
      (sub_nonneg.mpr hnorm)
      (add_nonneg hboundNonneg
        (norm_nonneg
          (finiteEmpiricalCameraCharacteristic camera M
            (criticalLineParameter time))))
    nlinarith
  exact ⟨htail, hnorm, by
    simpa [Complex.sq_norm] using hsquare⟩

/-- Common critical-line zeros at a fixed time give an exact six-camera
tail-stack identity and the displayed time-dependent `M^(-3)` collective
energy upper bound. -/
theorem empiricalSixCamera_critical_cutoffTail_and_rate
    (M : ℕ) (hM : 1 ≤ M) (time : ℝ)
    (hzero : ∀ camera, empiricalCameraCharacteristic camera
      (criticalLineParameter time) = 0) :
    finiteEmpiricalCameraStack M (criticalLineParameter time) =
        (fun camera ↦
          -empiricalCameraCutoffTailStack M
            (criticalLineParameter time) camera) ∧
      finiteEmpiricalCollectiveRawEnergy M (criticalLineParameter time) =
        empiricalCollectiveCutoffTailEnergy M (criticalLineParameter time) ∧
      finiteEmpiricalCollectiveRawEnergy M (criticalLineParameter time) ≤
        empiricalCollectiveCriticalTailEnergyBound M time := by
  have hstrip : -1 < (criticalLineParameter time).re := by
    norm_num [criticalLineParameter_re]
  refine ⟨
    finiteEmpiricalCameraStack_eq_neg_cutoffTailStack_of_zero
      M hstrip hzero,
    finiteEmpiricalCollectiveRawEnergy_eq_cutoffTailEnergy_of_zero
      M hstrip hzero,
    ?_⟩
  classical
  unfold finiteEmpiricalCollectiveRawEnergy
    empiricalCollectiveCriticalTailEnergyBound
  exact Finset.sum_le_sum fun camera _hcamera ↦
    (finiteEmpiricalCamera_critical_cutoffTail_and_rate
      camera M hM time (hzero camera)).2.2

end

end GenuineZeroUniformAtlasEnergy

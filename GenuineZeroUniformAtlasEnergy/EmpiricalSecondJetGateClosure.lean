import GenuineZeroUniformAtlasEnergy.EmpiricalFiniteSecondJetBound
import GenuineZeroUniformAtlasEnergy.EmpiricalFiniteCurvatureBound

/-!
# Complete quantitative closure of the empirical second-jet gate

`EmpiricalFiniteSecondJetBound` proves the exact camerawise identity

```math
\chi_{b,M}''=\chi_b''-T_{b,M}''
```

and the sharp Cauchy rate

```math
\|T_{b,M}''\|\le 2C_b(t)M^{-3/2}\log(M)^2.
```

This module removes the last downstream placeholder attached to that result.
The elementary estimate

```math
M^{-3/2}\log(M)^2\le 16/M
```

turns the tail into a fixed inverse-cutoff constant.  It then constructs a
cutoff-independent bound for the complete six-camera finite second jet and
feeds it into the concrete curvature channels.  Consequently the finite `a`
and `b` terms are bounded by one fixed `C(t)/M`; later modules no longer need
to accept an external `secondJetBound` hypothesis.

The constants may depend on the fixed time and on the six stored cameras, but
never on the cutoff.  No zero height, numerical certificate, or simplicity
hypothesis enters the analytic estimate.  The zero hypothesis appears only
when the finite residual is identified with the unresolved tail in the
curvature application.
-/

open scoped BigOperators

namespace GenuineZeroUniformAtlasEnergy

open CPFormal.Analytic.Cp

noncomputable section

/-- Elementary logarithmic absorption used by the order-two Cauchy tail.
The deliberately loose constant `16` is sufficient to produce a fixed `1/M`
rate and avoids introducing a cutoff-dependent maximization problem. -/
theorem rpow_neg_three_halves_mul_log_sq_le_sixteen_div
    (M : ℕ) (hM : 1 ≤ M) :
    (M : ℝ) ^ (-(3 : ℝ) / 2) * (Real.log (M : ℝ)) ^ 2 ≤
      16 / (M : ℝ) := by
  have hMreal : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hMnonneg : (0 : ℝ) ≤ (M : ℝ) := zero_le_one.trans hMreal
  have hMpos : (0 : ℝ) < (M : ℝ) := zero_lt_one.trans_le hMreal
  have hlogNonneg : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg hMreal
  have hquarterNonneg : 0 ≤ (M : ℝ) ^ (1 / 4 : ℝ) :=
    Real.rpow_nonneg hMnonneg _
  have hlogQuarter :
      Real.log (M : ℝ) ≤ 4 * (M : ℝ) ^ (1 / 4 : ℝ) := by
    calc
      Real.log (M : ℝ) ≤
          (M : ℝ) ^ (1 / 4 : ℝ) / (1 / 4 : ℝ) :=
        Real.log_natCast_le_rpow_div M (by norm_num)
      _ = 4 * (M : ℝ) ^ (1 / 4 : ℝ) := by ring
  have hrightNonneg : 0 ≤ 4 * (M : ℝ) ^ (1 / 4 : ℝ) := by positivity
  have hlogSq :
      (Real.log (M : ℝ)) ^ 2 ≤
        (4 * (M : ℝ) ^ (1 / 4 : ℝ)) ^ 2 := by
    have hproduct :
        0 ≤
          (4 * (M : ℝ) ^ (1 / 4 : ℝ) - Real.log (M : ℝ)) *
            (4 * (M : ℝ) ^ (1 / 4 : ℝ) + Real.log (M : ℝ)) :=
      mul_nonneg (sub_nonneg.mpr hlogQuarter)
        (add_nonneg hrightNonneg hlogNonneg)
    nlinarith
  have hquarterSq :
      ((M : ℝ) ^ (1 / 4 : ℝ)) ^ 2 =
        (M : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hMnonneg]
    norm_num
  have hlogSqBound :
      (Real.log (M : ℝ)) ^ 2 ≤
        16 * (M : ℝ) ^ (1 / 2 : ℝ) := by
    calc
      (Real.log (M : ℝ)) ^ 2 ≤
          (4 * (M : ℝ) ^ (1 / 4 : ℝ)) ^ 2 := hlogSq
      _ = 16 * (M : ℝ) ^ (1 / 2 : ℝ) := by
        rw [pow_two, hquarterSq]
        ring
  calc
    (M : ℝ) ^ (-(3 : ℝ) / 2) * (Real.log (M : ℝ)) ^ 2 ≤
        (M : ℝ) ^ (-(3 : ℝ) / 2) *
          (16 * (M : ℝ) ^ (1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hlogSqBound
        (Real.rpow_nonneg hMnonneg _)
    _ = 16 *
        ((M : ℝ) ^ (-(3 : ℝ) / 2) *
          (M : ℝ) ^ (1 / 2 : ℝ)) := by ring
    _ = 16 * (M : ℝ) ^ (-1 : ℝ) := by
      rw [← Real.rpow_add hMpos]
      norm_num
    _ = 16 / (M : ℝ) := by
      rw [Real.rpow_neg_one, div_eq_mul_inv]

/-- Fixed camerawise inverse-cutoff constant for the second derivative tail. -/
def empiricalCameraSecondJetInverseCutoffConstant
    (camera : EmpiricalCamera) (time : ℝ) : ℝ :=
  32 *
    NativeCarrySpectralWeyl.Camera.higherDerivativeCircleConstant
      camera.label time

/-- The camerawise second-jet tail rate is bounded by a fixed `C_b(t)/M`. -/
theorem empiricalCameraSecondJetTailRateBound_le_inverseCutoff
    (camera : EmpiricalCamera) (M : ℕ) (hM : 1 ≤ M) (time : ℝ) :
    empiricalCameraSecondJetTailRateBound camera M time ≤
      empiricalCameraSecondJetInverseCutoffConstant camera time / (M : ℝ) := by
  have hbase :=
    rpow_neg_three_halves_mul_log_sq_le_sixteen_div M hM
  have hconstant :
      0 ≤
        2 * NativeCarrySpectralWeyl.Camera.higherDerivativeCircleConstant
          camera.label time := by
    positivity [NativeCarrySpectralWeyl.Camera.higherDerivativeCircleConstant_nonneg]
  unfold empiricalCameraSecondJetTailRateBound
    empiricalCameraSecondJetInverseCutoffConstant
  calc
    (2 * NativeCarrySpectralWeyl.Camera.higherDerivativeCircleConstant
        camera.label time) *
        (M : ℝ) ^ (-(3 : ℝ) / 2) *
          (Real.log (M : ℝ)) ^ 2 =
      (2 * NativeCarrySpectralWeyl.Camera.higherDerivativeCircleConstant
        camera.label time) *
        ((M : ℝ) ^ (-(3 : ℝ) / 2) *
          (Real.log (M : ℝ)) ^ 2) := by ring
    _ ≤
      (2 * NativeCarrySpectralWeyl.Camera.higherDerivativeCircleConstant
        camera.label time) * (16 / (M : ℝ)) :=
      mul_le_mul_of_nonneg_left hbase hconstant
    _ =
      (32 * NativeCarrySpectralWeyl.Camera.higherDerivativeCircleConstant
        camera.label time) / (M : ℝ) := by ring

/-- The actual unresolved second derivative tail has the same fixed `1/M`
majorant. -/
theorem norm_iteratedDeriv_two_empiricalCameraCutoffTail_le_inverseCutoff
    (camera : EmpiricalCamera) (M : ℕ)
    (hM : Real.exp 2 ≤ (M : ℝ)) (time : ℝ) :
    ‖iteratedDeriv 2 (empiricalCameraCutoffTail camera M)
        (criticalLineParameter time)‖ ≤
      empiricalCameraSecondJetInverseCutoffConstant camera time / (M : ℝ) := by
  have hMOne : 1 ≤ M := by
    have hone : (1 : ℝ) < Real.exp 2 :=
      Real.one_lt_exp_iff.mpr (by norm_num)
    exact_mod_cast hone.trans_le hM
  exact
    (norm_iteratedDeriv_two_empiricalCameraCutoffTail_le
      camera M hM time).trans
        (empiricalCameraSecondJetTailRateBound_le_inverseCutoff
          camera M hMOne time)

/-- Fixed camerawise bound for the complete finite second derivative. -/
def empiricalCameraUniformSecondJetBound
    (camera : EmpiricalCamera) (time : ℝ) : ℝ :=
  ‖iteratedDeriv 2 (empiricalCameraCharacteristic camera)
      (criticalLineParameter time)‖ +
    empiricalCameraSecondJetInverseCutoffConstant camera time

/-- After the Cauchy threshold, every finite camerawise second jet is bounded
by a constant independent of the cutoff. -/
theorem norm_iteratedDeriv_two_finiteEmpiricalCameraCharacteristic_le_uniform
    (camera : EmpiricalCamera) (M : ℕ)
    (hM : Real.exp 2 ≤ (M : ℝ)) (time : ℝ) :
    ‖iteratedDeriv 2 (finiteEmpiricalCameraCharacteristic camera M)
        (criticalLineParameter time)‖ ≤
      empiricalCameraUniformSecondJetBound camera time := by
  have hMOne : 1 ≤ M := by
    have hone : (1 : ℝ) < Real.exp 2 :=
      Real.one_lt_exp_iff.mpr (by norm_num)
    exact_mod_cast hone.trans_le hM
  have hMreal : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hMOne
  have hconstantNonneg :
      0 ≤ empiricalCameraSecondJetInverseCutoffConstant camera time := by
    unfold empiricalCameraSecondJetInverseCutoffConstant
    positivity [NativeCarrySpectralWeyl.Camera.higherDerivativeCircleConstant_nonneg]
  calc
    ‖iteratedDeriv 2 (finiteEmpiricalCameraCharacteristic camera M)
        (criticalLineParameter time)‖ ≤
      ‖iteratedDeriv 2 (empiricalCameraCharacteristic camera)
          (criticalLineParameter time)‖ +
        empiricalCameraSecondJetTailRateBound camera M time :=
      norm_iteratedDeriv_two_finiteEmpiricalCameraCharacteristic_le_explicit
        camera M hM time
    _ ≤
      ‖iteratedDeriv 2 (empiricalCameraCharacteristic camera)
          (criticalLineParameter time)‖ +
        empiricalCameraSecondJetInverseCutoffConstant camera time / (M : ℝ) :=
      add_le_add_left
        (empiricalCameraSecondJetTailRateBound_le_inverseCutoff
          camera M hMOne time) _
    _ ≤
      ‖iteratedDeriv 2 (empiricalCameraCharacteristic camera)
          (criticalLineParameter time)‖ +
        empiricalCameraSecondJetInverseCutoffConstant camera time :=
      add_le_add_left
        (div_le_self hconstantNonneg hMreal) _
    _ = empiricalCameraUniformSecondJetBound camera time := rfl

/-- Cutoff-independent Euclidean bound for the complete six-camera second
jet. -/
def empiricalUniformSecondJetStackBound (time : ℝ) : ℝ :=
  Real.sqrt
    (∑ camera : EmpiricalCamera,
      empiricalCameraUniformSecondJetBound camera time ^ 2)

/-- The complete finite six-camera second jet is uniformly bounded, with no
supplied second-jet parameter left in the statement. -/
theorem norm_finiteEmpiricalCameraSecondDerivativeStack_le_uniform
    (M : ℕ) (hM : Real.exp 2 ≤ (M : ℝ)) (time : ℝ) :
    ‖finiteEmpiricalCameraSecondDerivativeStack M
        (criticalLineParameter time)‖ ≤
      empiricalUniformSecondJetStackBound time := by
  rw [EuclideanSpace.norm_eq]
  unfold empiricalUniformSecondJetStackBound
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro camera _hcamera
  have hcomponent :=
    norm_iteratedDeriv_two_finiteEmpiricalCameraCharacteristic_le_uniform
      camera M hM time
  have hboundNonneg :
      0 ≤ empiricalCameraUniformSecondJetBound camera time :=
    le_trans
      (norm_nonneg
        (iteratedDeriv 2 (finiteEmpiricalCameraCharacteristic camera M)
          (criticalLineParameter time))) hcomponent
  have hmul :=
    mul_le_mul hcomponent hcomponent
      (norm_nonneg
        (iteratedDeriv 2 (finiteEmpiricalCameraCharacteristic camera M)
          (criticalLineParameter time)))
      hboundNonneg
  simpa [finiteEmpiricalCameraSecondDerivativeStack, pow_two] using hmul

/-- The coefficient of the already known raw `M^{-3/2}` residual bound. -/
def empiricalCameraRawResidualInverseCutoffConstant
    (camera : EmpiricalCamera) (time : ℝ) : ℝ :=
  (2 / 3 : ℝ) *
    empiricalCameraBracketMajorantConstant camera
      (criticalLineParameter time)

private theorem empiricalCameraRawResidualInverseCutoffConstant_nonneg
    (camera : EmpiricalCamera) (time : ℝ) :
    0 ≤ empiricalCameraRawResidualInverseCutoffConstant camera time := by
  unfold empiricalCameraRawResidualInverseCutoffConstant
    empiricalCameraBracketMajorantConstant
  positivity

/-- The raw critical residual majorant is itself bounded by a fixed `C_b/M`. -/
theorem empiricalCameraCriticalTailBound_le_inverseCutoff
    (camera : EmpiricalCamera) (M : ℕ) (hM : 1 ≤ M) (time : ℝ) :
    empiricalCameraCriticalTailBound camera M time ≤
      empiricalCameraRawResidualInverseCutoffConstant camera time / (M : ℝ) := by
  have hMreal : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hpower :
      (M : ℝ) ^ (-(3 / 2 : ℝ)) ≤ (M : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hMreal (by norm_num)
  unfold empiricalCameraCriticalTailBound
    empiricalCameraRawResidualInverseCutoffConstant
  calc
    (2 / 3 : ℝ) *
        empiricalCameraBracketMajorantConstant camera
          (criticalLineParameter time) *
        (M : ℝ) ^ (-(3 / 2 : ℝ)) ≤
      (2 / 3 : ℝ) *
        empiricalCameraBracketMajorantConstant camera
          (criticalLineParameter time) *
        (M : ℝ) ^ (-1 : ℝ) :=
      mul_le_mul_of_nonneg_left hpower
        (empiricalCameraRawResidualInverseCutoffConstant_nonneg camera time)
    _ =
      ((2 / 3 : ℝ) *
        empiricalCameraBracketMajorantConstant camera
          (criticalLineParameter time)) / (M : ℝ) := by
      rw [Real.rpow_neg_one, div_eq_mul_inv]

/-- A simple fixed all-camera residual constant.  The `l1` aggregation is
chosen deliberately: it avoids hiding another square-root normalization in the
later curvature constants. -/
def empiricalFiniteRawResidualInverseCutoffConstant (time : ℝ) : ℝ :=
  ∑ camera : EmpiricalCamera,
    empiricalCameraRawResidualInverseCutoffConstant camera time

private theorem empiricalCameraCriticalTailBound_nonneg
    (camera : EmpiricalCamera) (M : ℕ) (time : ℝ) :
    0 ≤ empiricalCameraCriticalTailBound camera M time := by
  unfold empiricalCameraCriticalTailBound
    empiricalCameraBracketMajorantConstant
  positivity

/-- The Euclidean residual stack bound is bounded by one fixed `C_res(t)/M`. -/
theorem empiricalFiniteRawResidualStackBound_le_inverseCutoff
    (M : ℕ) (hM : 1 ≤ M) (time : ℝ) :
    empiricalFiniteRawResidualStackBound M time ≤
      empiricalFiniteRawResidualInverseCutoffConstant time / (M : ℝ) := by
  have hnonneg :
      ∀ camera ∈ (Finset.univ : Finset EmpiricalCamera),
        0 ≤ empiricalCameraCriticalTailBound camera M time := by
    intro camera _
    exact empiricalCameraCriticalTailBound_nonneg camera M time
  have hsquares :=
    Finset.sum_sq_le_sq_sum_of_nonneg
      (s := (Finset.univ : Finset EmpiricalCamera))
      (f := fun camera => empiricalCameraCriticalTailBound camera M time)
      hnonneg
  have hsumNonneg :
      0 ≤ ∑ camera : EmpiricalCamera,
        empiricalCameraCriticalTailBound camera M time :=
    Finset.sum_nonneg fun camera _ =>
      empiricalCameraCriticalTailBound_nonneg camera M time
  have hsqrtL1 :
      Real.sqrt
        (∑ camera : EmpiricalCamera,
          empiricalCameraCriticalTailBound camera M time ^ 2) ≤
        ∑ camera : EmpiricalCamera,
          empiricalCameraCriticalTailBound camera M time := by
    rw [Real.sqrt_le_iff]
    exact ⟨hsumNonneg, hsquares⟩
  calc
    empiricalFiniteRawResidualStackBound M time =
        Real.sqrt
          (∑ camera : EmpiricalCamera,
            empiricalCameraCriticalTailBound camera M time ^ 2) := rfl
    _ ≤ ∑ camera : EmpiricalCamera,
        empiricalCameraCriticalTailBound camera M time := hsqrtL1
    _ ≤ ∑ camera : EmpiricalCamera,
        empiricalCameraRawResidualInverseCutoffConstant camera time /
          (M : ℝ) := by
      exact Finset.sum_le_sum fun camera _ =>
        empiricalCameraCriticalTailBound_le_inverseCutoff
          camera M hM time
    _ = empiricalFiniteRawResidualInverseCutoffConstant time / (M : ℝ) := by
      simp [empiricalFiniteRawResidualInverseCutoffConstant, Finset.sum_div]

/-- Fixed inverse-cutoff constant for both second-jet curvature coordinates. -/
def empiricalSecondJetCurvatureInverseCutoffConstant (time : ℝ) : ℝ :=
  empiricalFiniteRawResidualInverseCutoffConstant time *
    empiricalUniformSecondJetStackBound time

/-- The concrete finite `a` channel now has a fixed `C_a(t)/M` estimate with
no supplied second-jet bound. -/
theorem abs_finiteEmpiricalTransverseJet_a_le_inverseCutoff
    (M : ℕ) (hM : Real.exp 2 ≤ (M : ℝ)) (time : ℝ)
    (hzero : genuineContinuation (criticalLineParameter time) = 0) :
    |(finiteEmpiricalTransverseJet M time).a| ≤
      empiricalSecondJetCurvatureInverseCutoffConstant time / (M : ℝ) := by
  have hMOne : 1 ≤ M := by
    have hone : (1 : ℝ) < Real.exp 2 :=
      Real.one_lt_exp_iff.mpr (by norm_num)
    exact_mod_cast hone.trans_le hM
  have hsecond :=
    norm_finiteEmpiricalCameraSecondDerivativeStack_le_uniform M hM time
  have ha :=
    abs_finiteEmpiricalTransverseJet_a_le
      M hMOne time (empiricalUniformSecondJetStackBound time)
      hzero hsecond
  have hraw :=
    empiricalFiniteRawResidualStackBound_le_inverseCutoff M hMOne time
  have hsecondNonneg :
      0 ≤ empiricalUniformSecondJetStackBound time := Real.sqrt_nonneg _
  calc
    |(finiteEmpiricalTransverseJet M time).a| ≤
        empiricalFiniteRawResidualStackBound M time *
          empiricalUniformSecondJetStackBound time := ha
    _ ≤
        (empiricalFiniteRawResidualInverseCutoffConstant time / (M : ℝ)) *
          empiricalUniformSecondJetStackBound time :=
      mul_le_mul_of_nonneg_right hraw hsecondNonneg
    _ =
        empiricalSecondJetCurvatureInverseCutoffConstant time / (M : ℝ) := by
      unfold empiricalSecondJetCurvatureInverseCutoffConstant
      ring

/-- The concrete finite `b` channel obeys the same fixed inverse-cutoff
constant. -/
theorem abs_finiteEmpiricalTransverseJet_b_le_inverseCutoff
    (M : ℕ) (hM : Real.exp 2 ≤ (M : ℝ)) (time : ℝ)
    (hzero : genuineContinuation (criticalLineParameter time) = 0) :
    |(finiteEmpiricalTransverseJet M time).b| ≤
      empiricalSecondJetCurvatureInverseCutoffConstant time / (M : ℝ) := by
  have hMOne : 1 ≤ M := by
    have hone : (1 : ℝ) < Real.exp 2 :=
      Real.one_lt_exp_iff.mpr (by norm_num)
    exact_mod_cast hone.trans_le hM
  have hsecond :=
    norm_finiteEmpiricalCameraSecondDerivativeStack_le_uniform M hM time
  have hb :=
    abs_finiteEmpiricalTransverseJet_b_le
      M hMOne time (empiricalUniformSecondJetStackBound time)
      hzero hsecond
  have hraw :=
    empiricalFiniteRawResidualStackBound_le_inverseCutoff M hMOne time
  have hsecondNonneg :
      0 ≤ empiricalUniformSecondJetStackBound time := Real.sqrt_nonneg _
  calc
    |(finiteEmpiricalTransverseJet M time).b| ≤
        empiricalFiniteRawResidualStackBound M time *
          empiricalUniformSecondJetStackBound time := hb
    _ ≤
        (empiricalFiniteRawResidualInverseCutoffConstant time / (M : ℝ)) *
          empiricalUniformSecondJetStackBound time :=
      mul_le_mul_of_nonneg_right hraw hsecondNonneg
    _ =
        empiricalSecondJetCurvatureInverseCutoffConstant time / (M : ℝ) := by
      unfold empiricalSecondJetCurvatureInverseCutoffConstant
      ring

end

end GenuineZeroUniformAtlasEnergy

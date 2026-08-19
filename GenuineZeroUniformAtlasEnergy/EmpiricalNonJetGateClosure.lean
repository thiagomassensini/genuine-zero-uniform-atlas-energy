import GenuineZeroUniformAtlasEnergy.EmpiricalDenominatorFloors
import GenuineZeroUniformAtlasEnergy.EmpiricalFiniteEnergyBound

/-!
# Fixed inverse-cutoff constants for the non-jet channels

The second-jet contribution and the two clock denominators are already closed.
This module consumes the remaining exact stack-level cutoff estimates and
removes cutoff dependence from the scaled residual, corrected pairing, and
radial-gradient channels.

All constants depend only on the fixed critical time and the six stored
cameras.  No numerical height, finite-cutoff witness, or floating-point
certificate is used.
-/

open Filter
open scoped BigOperators

namespace GenuineZeroUniformAtlasEnergy

open CPFormal.Analytic.Cp

noncomputable section

/-- Fixed `l1` constant for the naturally scaled six-camera residual. -/
def empiricalScaledResidualInverseCutoffConstant (time : ℝ) : ℝ :=
  ∑ camera : EmpiricalCamera,
    empiricalScaledCameraTailCauchyConstant camera time

lemma empiricalScaledResidualInverseCutoffConstant_nonneg (time : ℝ) :
    0 ≤ empiricalScaledResidualInverseCutoffConstant time := by
  unfold empiricalScaledResidualInverseCutoffConstant
  exact Finset.sum_nonneg fun camera _ =>
    empiricalScaledCameraTailCauchyConstant_nonneg camera time

/-- The Euclidean scaled-residual error is bounded by one fixed `C_R(t)/M`. -/
theorem empiricalScaledFiniteResidualStackErrorBound_le_inverseCutoff
    (M : ℕ) (hM : 1 ≤ M) (time : ℝ) :
    empiricalScaledFiniteResidualStackErrorBound M time ≤
      empiricalScaledResidualInverseCutoffConstant time / (M : ℝ) := by
  have hMnonneg : 0 ≤ (M : ℝ) := by positivity
  have hnonneg :
      ∀ camera ∈ (Finset.univ : Finset EmpiricalCamera),
        0 ≤ empiricalScaledCameraTailCauchyConstant camera time / (M : ℝ) := by
    intro camera _
    exact div_nonneg
      (empiricalScaledCameraTailCauchyConstant_nonneg camera time) hMnonneg
  have hsquares :=
    Finset.sum_sq_le_sq_sum_of_nonneg
      (s := (Finset.univ : Finset EmpiricalCamera))
      (f := fun camera =>
        empiricalScaledCameraTailCauchyConstant camera time / (M : ℝ))
      hnonneg
  have hsumNonneg :
      0 ≤ ∑ camera : EmpiricalCamera,
        empiricalScaledCameraTailCauchyConstant camera time / (M : ℝ) :=
    Finset.sum_nonneg hnonneg
  have hsqrtL1 :
      Real.sqrt
          (∑ camera : EmpiricalCamera,
            (empiricalScaledCameraTailCauchyConstant camera time /
              (M : ℝ)) ^ 2) ≤
        ∑ camera : EmpiricalCamera,
          empiricalScaledCameraTailCauchyConstant camera time / (M : ℝ) := by
    rw [Real.sqrt_le_iff]
    exact ⟨hsumNonneg, hsquares⟩
  calc
    empiricalScaledFiniteResidualStackErrorBound M time =
        Real.sqrt
          (∑ camera : EmpiricalCamera,
            (empiricalScaledCameraTailCauchyConstant camera time /
              (M : ℝ)) ^ 2) := rfl
    _ ≤ ∑ camera : EmpiricalCamera,
        empiricalScaledCameraTailCauchyConstant camera time / (M : ℝ) :=
      hsqrtL1
    _ = empiricalScaledResidualInverseCutoffConstant time / (M : ℝ) := by
      simp [empiricalScaledResidualInverseCutoffConstant, Finset.sum_div]

/-- Fixed inverse-cutoff constant for the corrected residual/clock pairing. -/
def empiricalCorrectedPairingInverseCutoffConstant (time : ℝ) : ℝ :=
  empiricalScaledResidualInverseCutoffConstant time *
      (empiricalCorrectedFirstJetInverseCutoffConstant time +
        ‖empiricalClockTangentVector (criticalLineParameter time)‖) +
    ‖empiricalLeadingCutoffVector (criticalLineParameter time)‖ *
      empiricalCorrectedFirstJetInverseCutoffConstant time

lemma empiricalCorrectedPairingInverseCutoffConstant_nonneg (time : ℝ) :
    0 ≤ empiricalCorrectedPairingInverseCutoffConstant time := by
  have hres := empiricalScaledResidualInverseCutoffConstant_nonneg time
  have hjet := empiricalCorrectedFirstJetInverseCutoffConstant_nonneg time
  exact add_nonneg
    (mul_nonneg hres (add_nonneg hjet (norm_nonneg _)))
    (mul_nonneg (norm_nonneg _) hjet)

/-- The complete corrected pairing error is bounded by one fixed `C_P(t)/M`. -/
theorem empiricalFiniteCorrectedPairingErrorBound_le_inverseCutoff
    (M : ℕ) (hM : 1 ≤ M) (time : ℝ) :
    empiricalFiniteCorrectedPairingErrorBound M time ≤
      empiricalCorrectedPairingInverseCutoffConstant time / (M : ℝ) := by
  let residualError := empiricalScaledFiniteResidualStackErrorBound M time
  let firstJetError := empiricalFiniteCorrectedFirstJetStackErrorBound M time
  let residualConstant := empiricalScaledResidualInverseCutoffConstant time
  let firstJetConstant := empiricalCorrectedFirstJetInverseCutoffConstant time
  let tangentNorm :=
    ‖empiricalClockTangentVector (criticalLineParameter time)‖
  let leadingNorm :=
    ‖empiricalLeadingCutoffVector (criticalLineParameter time)‖
  have hMreal : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hres :=
    empiricalScaledFiniteResidualStackErrorBound_le_inverseCutoff M hM time
  have hfirst :=
    empiricalFiniteCorrectedFirstJetStackErrorBound_le_inverseCutoff M hM time
  have hresConstant : 0 ≤ residualConstant := by
    exact empiricalScaledResidualInverseCutoffConstant_nonneg time
  have hfirstConstant : 0 ≤ firstJetConstant := by
    exact empiricalCorrectedFirstJetInverseCutoffConstant_nonneg time
  have hresNonneg : 0 ≤ residualError := by
    dsimp [residualError]
    exact Real.sqrt_nonneg _
  have hfirstNonneg : 0 ≤ firstJetError := by
    dsimp [firstJetError]
    exact Real.sqrt_nonneg _
  have hresDivNonneg : 0 ≤ residualConstant / (M : ℝ) :=
    div_nonneg hresConstant (by positivity)
  have hfirstFixed : firstJetError ≤ firstJetConstant :=
    hfirst.trans (div_le_self hfirstConstant hMreal)
  have hsum :
      firstJetError + tangentNorm ≤ firstJetConstant + tangentNorm :=
    add_le_add hfirstFixed le_rfl
  have hsumNonneg : 0 ≤ firstJetError + tangentNorm :=
    add_nonneg hfirstNonneg (norm_nonneg _)
  have hfirstProduct :
      residualError * (firstJetError + tangentNorm) ≤
        (residualConstant / (M : ℝ)) *
          (firstJetConstant + tangentNorm) :=
    mul_le_mul hres hsum hsumNonneg hresDivNonneg
  have hsecondProduct :
      leadingNorm * firstJetError ≤
        leadingNorm * (firstJetConstant / (M : ℝ)) :=
    mul_le_mul_of_nonneg_left hfirst (norm_nonneg _)
  calc
    empiricalFiniteCorrectedPairingErrorBound M time =
        residualError * (firstJetError + tangentNorm) +
          leadingNorm * firstJetError := rfl
    _ ≤ (residualConstant / (M : ℝ)) *
          (firstJetConstant + tangentNorm) +
        leadingNorm * (firstJetConstant / (M : ℝ)) :=
      add_le_add hfirstProduct hsecondProduct
    _ = empiricalCorrectedPairingInverseCutoffConstant time / (M : ℝ) := by
      unfold empiricalCorrectedPairingInverseCutoffConstant
      dsimp [residualConstant, firstJetConstant, tangentNorm, leadingNorm]
      ring

/-- Fixed inverse-cutoff constant for the corrected radial-gradient channel. -/
def empiricalCorrectedGradientInverseCutoffConstant (time : ℝ) : ℝ :=
  2 * empiricalCorrectedPairingInverseCutoffConstant time

lemma empiricalCorrectedGradientInverseCutoffConstant_nonneg (time : ℝ) :
    0 ≤ empiricalCorrectedGradientInverseCutoffConstant time :=
  mul_nonneg (by norm_num)
    (empiricalCorrectedPairingInverseCutoffConstant_nonneg time)

/-- The corrected finite radial gradient differs from `2 X_M` by `C_g(t)/M`. -/
theorem abs_finiteEmpiricalCorrectedRadialGradient_sub_model_le_inverseCutoff
    (M : ℕ) (hM : 1 ≤ M) (time : ℝ)
    (hzero : genuineContinuation (criticalLineParameter time) = 0) :
    |finiteEmpiricalCorrectedRadialGradient M time -
        2 * finiteEmpiricalPhaseProjection time M| ≤
      empiricalCorrectedGradientInverseCutoffConstant time / (M : ℝ) := by
  have hgradient :=
    abs_finiteEmpiricalCorrectedRadialGradient_sub_model_le
      M hM time hzero
  have hpairing :=
    empiricalFiniteCorrectedPairingErrorBound_le_inverseCutoff M hM time
  calc
    |finiteEmpiricalCorrectedRadialGradient M time -
        2 * finiteEmpiricalPhaseProjection time M| ≤
      2 * empiricalFiniteCorrectedPairingErrorBound M time := hgradient
    _ ≤ 2 *
        (empiricalCorrectedPairingInverseCutoffConstant time / (M : ℝ)) :=
      mul_le_mul_of_nonneg_left hpairing (by norm_num)
    _ = empiricalCorrectedGradientInverseCutoffConstant time / (M : ℝ) := by
      unfold empiricalCorrectedGradientInverseCutoffConstant
      ring

/-- A fixed bound for the sum of the finite and model radial gradients. -/
def empiricalCorrectedGradientSumBound (time : ℝ) : ℝ :=
  empiricalCorrectedGradientInverseCutoffConstant time +
    4 * ‖empiricalStackPairing (criticalLineParameter time)‖

lemma empiricalCorrectedGradientSumBound_nonneg (time : ℝ) :
    0 ≤ empiricalCorrectedGradientSumBound time :=
  add_nonneg
    (empiricalCorrectedGradientInverseCutoffConstant_nonneg time)
    (mul_nonneg (by norm_num) (norm_nonneg _))

/-- The gradient sum is uniformly bounded independently of the cutoff. -/
theorem abs_finiteEmpiricalCorrectedRadialGradient_add_model_le
    (M : ℕ) (hM : 1 ≤ M) (time : ℝ)
    (hzero : genuineContinuation (criticalLineParameter time) = 0) :
    |finiteEmpiricalCorrectedRadialGradient M time +
        2 * finiteEmpiricalPhaseProjection time M| ≤
      empiricalCorrectedGradientSumBound time := by
  let gradient := finiteEmpiricalCorrectedRadialGradient M time
  let model := 2 * finiteEmpiricalPhaseProjection time M
  let C := empiricalCorrectedGradientInverseCutoffConstant time
  have hMreal : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hC : 0 ≤ C := by
    exact empiricalCorrectedGradientInverseCutoffConstant_nonneg time
  have hdiff :=
    abs_finiteEmpiricalCorrectedRadialGradient_sub_model_le_inverseCutoff
      M hM time hzero
  have hdiffFixed : |gradient - model| ≤ C := by
    exact hdiff.trans (div_le_self hC hMreal)
  have hmodel :=
    abs_two_empiricalStackPhaseProjection_le
      (criticalLineParameter time) (empiricalCutoffPhase time M)
  have htriangle :
      |gradient + model| ≤ |gradient - model| + 2 * |model| := by
    calc
      |gradient + model| = |(gradient - model) + 2 * model| := by ring
      _ ≤ |gradient - model| + |2 * model| := abs_add _ _
      _ = |gradient - model| + 2 * |model| := by
        rw [abs_mul]
        norm_num
  calc
    |finiteEmpiricalCorrectedRadialGradient M time +
        2 * finiteEmpiricalPhaseProjection time M| =
      |gradient + model| := rfl
    _ ≤ |gradient - model| + 2 * |model| := htriangle
    _ ≤ C + 2 *
        (2 * ‖empiricalStackPairing (criticalLineParameter time)‖) :=
      add_le_add hdiffFixed (mul_le_mul_of_nonneg_left hmodel (by norm_num))
    _ = empiricalCorrectedGradientSumBound time := by
      unfold empiricalCorrectedGradientSumBound
      dsimp [C]
      ring

end

end GenuineZeroUniformAtlasEnergy

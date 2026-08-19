import GenuineZeroUniformAtlasEnergy.EmpiricalEnergyLocalGateClosure

/-!
# Concrete eventual microscopic positivity

The preceding modules provide every primitive channel of the exact
moving-clock microscopic ledger with a fixed inverse-cutoff constant.  This
module combines those channels at a presented critical simple zero and obtains
one strictly positive eventual lower bound for the concrete corrected finite
microscopic coefficient.

This is a local theorem at a fixed critical simple zero.  It does not promote
that local sector to strip-wide coercivity or assume that every Genuine zero
is simple.
-/

open Filter

namespace GenuineZeroUniformAtlasEnergy

open CPFormal.Analytic.Cp

noncomputable section

/-- Fixed inverse-cutoff constant for the gradient-square perturbation channel. -/
def empiricalGradientSquareChannelInverseCutoffConstant (time : ℝ) : ℝ :=
  empiricalCorrectedGradientInverseCutoffConstant time *
      empiricalCorrectedGradientSumBound time /
    (4 * (empiricalStackRho (criticalLineParameter time) / 2))

lemma empiricalGradientSquareChannelInverseCutoffConstant_nonneg
    (time : ℝ)
    (hsimple : deriv genuineContinuation (criticalLineParameter time) ≠ 0) :
    0 ≤ empiricalGradientSquareChannelInverseCutoffConstant time := by
  have hrho : 0 < empiricalStackRho (criticalLineParameter time) :=
    empiricalStackRho_pos
      (by norm_num [criticalLineParameter_re]) hsimple
  exact div_nonneg
    (mul_nonneg
      (empiricalCorrectedGradientInverseCutoffConstant_nonneg time)
      (empiricalCorrectedGradientSumBound_nonneg time))
    (by positivity)

/-- Fixed inverse-cutoff constant for the model-energy denominator channel. -/
def empiricalEnergyDenominatorChannelInverseCutoffConstant (time : ℝ) : ℝ :=
  let rho := empiricalStackRho (criticalLineParameter time)
  let modelGradientBound :=
    2 * ‖empiricalStackPairing (criticalLineParameter time)‖
  modelGradientBound ^ 2 *
      empiricalCorrectedEnergyInverseCutoffConstant time /
    (4 * (rho / 2) * rho)

lemma empiricalEnergyDenominatorChannelInverseCutoffConstant_nonneg
    (time : ℝ)
    (hsimple : deriv genuineContinuation (criticalLineParameter time) ≠ 0) :
    0 ≤ empiricalEnergyDenominatorChannelInverseCutoffConstant time := by
  have hrho : 0 < empiricalStackRho (criticalLineParameter time) :=
    empiricalStackRho_pos
      (by norm_num [criticalLineParameter_re]) hsimple
  have henergy :=
    empiricalCorrectedEnergyInverseCutoffConstant_nonneg time hsimple
  dsimp [empiricalEnergyDenominatorChannelInverseCutoffConstant]
  exact div_nonneg (mul_nonneg (sq_nonneg _) henergy) (by positivity)

/-- Total fixed inverse-cutoff constant for the microscopic coefficient. -/
def empiricalMicroscopicInverseCutoffConstant (time : ℝ) : ℝ :=
  empiricalLocalCoercivityInverseCutoffConstant time +
    empiricalGradientSquareChannelInverseCutoffConstant time +
    empiricalEnergyDenominatorChannelInverseCutoffConstant time

lemma empiricalMicroscopicInverseCutoffConstant_nonneg
    (time : ℝ)
    (hsimple : deriv genuineContinuation (criticalLineParameter time) ≠ 0) :
    0 ≤ empiricalMicroscopicInverseCutoffConstant time := by
  exact add_nonneg
    (add_nonneg
      (empiricalLocalCoercivityInverseCutoffConstant_nonneg time hsimple)
      (empiricalGradientSquareChannelInverseCutoffConstant_nonneg time hsimple))
    (empiricalEnergyDenominatorChannelInverseCutoffConstant_nonneg time hsimple)

/-- At a presented critical simple zero, the concrete corrected finite
microscopic coefficient is eventually bounded below by half of the exact
phase floor. -/
theorem eventually_finiteEmpiricalCorrectedMicroscopicCoercivity_ge_half_phaseFloor
    (time : ℝ)
    (hzero : genuineContinuation (criticalLineParameter time) = 0)
    (hsimple : deriv genuineContinuation (criticalLineParameter time) ≠ 0) :
    ∀ᶠ M : ℕ in atTop,
      (empiricalStackPhaseProjectionData
          (criticalLineParameter time)).phaseFloor / 2 ≤
        finiteEmpiricalCorrectedMicroscopicCoercivity M time := by
  let s := criticalLineParameter time
  let d := empiricalStackPhaseProjectionData s
  let rho := empiricalStackRho s
  let kappa := empiricalStackKappa s
  let curvatureConstant := empiricalLocalCoercivityInverseCutoffConstant time
  let gradientDifferenceConstant :=
    empiricalCorrectedGradientInverseCutoffConstant time
  let gradientSumBound := empiricalCorrectedGradientSumBound time
  let energyDifferenceConstant :=
    empiricalCorrectedEnergyInverseCutoffConstant time
  let gradientChannelConstant :=
    empiricalGradientSquareChannelInverseCutoffConstant time
  let energyChannelConstant :=
    empiricalEnergyDenominatorChannelInverseCutoffConstant time
  let totalConstant := empiricalMicroscopicInverseCutoffConstant time
  have hs : s.re = (1 : ℝ) / 2 := by
    dsimp [s]
    norm_num [criticalLineParameter_re]
  have hd : d.IsAdmissible := by
    dsimp [d]
    exact empiricalStackPhaseProjectionData_isAdmissible hs hsimple
  have hrho : 0 < rho := by
    dsimp [rho, s]
    exact empiricalStackRho_pos
      (by norm_num [criticalLineParameter_re]) hsimple
  have hkappa : 0 < kappa := by
    dsimp [kappa, s]
    exact empiricalStackKappa_pos
      (by norm_num [criticalLineParameter_re]) hsimple
  have hphaseFloor : 0 < d.phaseFloor := d.phaseFloor_pos hd
  have hratio :
      Tendsto (fun M : ℕ => totalConstant / (M : ℝ)) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat totalConstant
  have hsmall : ∀ᶠ M : ℕ in atTop,
      totalConstant / (M : ℝ) < d.phaseFloor / 2 :=
    hratio.eventually (Iio_mem_nhds (by linarith : 0 < d.phaseFloor / 2))
  filter_upwards [
    eventually_abs_finiteEmpiricalLocalCoercivity_sub_model_le_inverseCutoff
      time hzero hsimple,
    eventually_finiteEmpiricalCorrectedReoptimizedEnergy_ge_half_rho
      time hzero hsimple,
    eventually_abs_finiteEmpiricalCorrectedReoptimizedEnergy_sub_model_le_inverseCutoff
      time hzero hsimple,
    hsmall,
    eventually_ge_atTop 1] with M hcurvature henergyFloor henergyDifference
      hMsmall hM
  let x := finiteEmpiricalPhaseProjection time M
  let energy := finiteEmpiricalCorrectedReoptimizedEnergy M time
  let gradient := finiteEmpiricalCorrectedRadialGradient M time
  let localCoeff := finiteEmpiricalLocalCoercivity M time
  let modelEnergy := rho + x ^ 2 / kappa
  let modelGradientBound := 2 * ‖empiricalStackPairing s‖
  have henergyPos : 0 < energy := by
    have hfloorPos : 0 < rho / 2 := by positivity
    exact lt_of_lt_of_le hfloorPos henergyFloor
  have henergyAbsFloor : rho / 2 ≤ |energy| := by
    rw [abs_of_pos henergyPos]
    exact henergyFloor
  have hmodelEnergyPos : 0 < modelEnergy := by
    dsimp [modelEnergy]
    exact add_pos_of_pos_of_nonneg hrho
      (div_nonneg (sq_nonneg x) (le_of_lt hkappa))
  have hmodelEnergyFloor : rho ≤ |modelEnergy| := by
    rw [abs_of_pos hmodelEnergyPos]
    dsimp [modelEnergy]
    exact le_add_of_nonneg_right
      (div_nonneg (sq_nonneg x) (le_of_lt hkappa))
  have hgradientDifference :=
    abs_finiteEmpiricalCorrectedRadialGradient_sub_model_le_inverseCutoff
      M hM time hzero
  have hgradientSum :=
    abs_finiteEmpiricalCorrectedRadialGradient_add_model_le
      M hM time hzero
  have hmodelGradient : |2 * x| ≤ modelGradientBound := by
    dsimp [x, modelGradientBound, s]
    simpa [finiteEmpiricalPhaseProjection] using
      abs_two_empiricalStackPhaseProjection_le
        (criticalLineParameter time) (empiricalCutoffPhase time M)
  have hgradientChannelRaw :=
    abs_gradientSquareChannel_le_of_primitive_bounds
      energy gradient (2 * x)
      (gradientDifferenceConstant / (M : ℝ))
      gradientSumBound (rho / 2)
      (by positivity) henergyAbsFloor
      (by simpa [gradient, x, gradientDifferenceConstant] using
        hgradientDifference)
      (by simpa [gradient, x, gradientSumBound] using hgradientSum)
  have hgradientChannel :
      |(gradient ^ 2 - (2 * x) ^ 2) / (4 * energy)| ≤
        gradientChannelConstant / (M : ℝ) := by
    calc
      |(gradient ^ 2 - (2 * x) ^ 2) / (4 * energy)| ≤
          (gradientDifferenceConstant / (M : ℝ)) *
            gradientSumBound / (4 * (rho / 2)) := hgradientChannelRaw
      _ = gradientChannelConstant / (M : ℝ) := by
        unfold empiricalGradientSquareChannelInverseCutoffConstant
        dsimp [gradientDifferenceConstant, gradientSumBound,
          gradientChannelConstant, rho, s]
        ring
  have henergyDifference' :
      |modelEnergy - energy| ≤ energyDifferenceConstant / (M : ℝ) := by
    have h := henergyDifference
    dsimp [energy, modelEnergy, rho, kappa, x, s,
      energyDifferenceConstant] at h ⊢
    simpa [abs_sub_comm] using h
  have henergyChannelRaw :=
    abs_energyDenominatorChannel_le_of_primitive_bounds
      energy modelEnergy (2 * x) modelGradientBound
      (energyDifferenceConstant / (M : ℝ))
      (rho / 2) rho
      (by positivity) hrho henergyAbsFloor hmodelEnergyFloor
      hmodelGradient henergyDifference'
  have henergyChannel :
      |(2 * x) ^ 2 * (modelEnergy - energy) /
          (4 * energy * modelEnergy)| ≤
        energyChannelConstant / (M : ℝ) := by
    calc
      |(2 * x) ^ 2 * (modelEnergy - energy) /
          (4 * energy * modelEnergy)| ≤
        modelGradientBound ^ 2 *
          (energyDifferenceConstant / (M : ℝ)) /
            (4 * (rho / 2) * rho) := henergyChannelRaw
      _ = energyChannelConstant / (M : ℝ) := by
        unfold empiricalEnergyDenominatorChannelInverseCutoffConstant
        dsimp [modelGradientBound, energyDifferenceConstant,
          energyChannelConstant, rho, s]
        ring
  have happrox :=
    d.abs_quadraticMicroscopicCoercivity_sub_phaseCoercivity_le_inv_of_perturbation_bounds
      hd M energy gradient localCoeff x
      curvatureConstant gradientChannelConstant energyChannelConstant
      (ne_of_gt henergyPos)
      (by simpa [localCoeff, curvatureConstant, d, s] using hcurvature)
      hgradientChannel henergyChannel
  have hphase : d.phaseFloor ≤ d.phaseCoercivity x := by
    apply d.phaseCoercivity_uniform_lower_bound hd
    dsimp [d, x, s]
    simpa [finiteEmpiricalPhaseProjection] using
      empiricalStackPhaseProjection_sq_le_alphaSq
        (criticalLineParameter time) (empiricalCutoffPhase time M)
  have hlower := (abs_le.mp happrox).1
  have htotal :
      curvatureConstant + gradientChannelConstant + energyChannelConstant =
        totalConstant := by
    rfl
  rw [htotal] at hlower
  change d.phaseFloor / 2 ≤
    quadraticMicroscopicCoercivity energy gradient localCoeff
  linarith

/-- Existential form of the concrete local gate. -/
theorem eventually_positive_finiteEmpiricalCorrectedMicroscopicCoercivity
    (time : ℝ)
    (hzero : genuineContinuation (criticalLineParameter time) = 0)
    (hsimple : deriv genuineContinuation (criticalLineParameter time) ≠ 0) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ M : ℕ in atTop,
        c ≤ finiteEmpiricalCorrectedMicroscopicCoercivity M time := by
  let c :=
    (empiricalStackPhaseProjectionData
      (criticalLineParameter time)).phaseFloor / 2
  have hc : 0 < c := by
    dsimp [c]
    have hfloor := empiricalStackPhaseFloor_pos
      (by norm_num [criticalLineParameter_re]) hsimple
    linarith
  exact ⟨c, hc,
    eventually_finiteEmpiricalCorrectedMicroscopicCoercivity_ge_half_phaseFloor
      time hzero hsimple⟩

end

end GenuineZeroUniformAtlasEnergy

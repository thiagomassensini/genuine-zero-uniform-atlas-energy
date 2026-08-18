import GenuineZeroUniformAtlasEnergy.MicroscopicJetTransfer

/-!
# Primitive bounds for the microscopic perturbation ledger

`MicroscopicJetTransfer` accepts three already-divided `C_i / M` channels.
The analytic cutoff estimates naturally provide more primitive information:

* an `O(1/M)` difference of gradients;
* a uniform bound for their sum;
* an `O(1/M)` difference of residual energies;
* positive lower floors for the two energy denominators.

This module performs the missing denominator algebra once and for all.  It
turns those primitive bounds into the squared-gradient and residual-energy
quotient bounds required by `MicroscopicJetTransfer`, and then exposes a
sequence-level eventual positivity theorem.
-/

open Filter

namespace GenuineZeroUniformAtlasEnergy

noncomputable section

/-- Difference and sum bounds control the difference of two squares. -/
theorem abs_sq_sub_sq_le_of_sub_add_bounds
    (x y differenceBound sumBound : ℝ)
    (hdifference : |x - y| ≤ differenceBound)
    (hsum : |x + y| ≤ sumBound) :
    |x ^ 2 - y ^ 2| ≤ differenceBound * sumBound := by
  have hdifferenceNonneg : 0 ≤ differenceBound :=
    le_trans (abs_nonneg _) hdifference
  calc
    |x ^ 2 - y ^ 2| = |x - y| * |x + y| := by
      rw [show x ^ 2 - y ^ 2 = (x - y) * (x + y) by ring,
        abs_mul]
    _ ≤ differenceBound * sumBound :=
      mul_le_mul hdifference hsum (abs_nonneg _) hdifferenceNonneg

/-- A primitive first-jet difference, a sum bound, and a positive residual
energy floor imply the divided squared-gradient channel. -/
theorem abs_gradientSquareChannel_le_of_primitive_bounds
    (energy gradient modelGradient differenceBound sumBound energyFloor : ℝ)
    (henergyFloorPos : 0 < energyFloor)
    (henergyFloor : energyFloor ≤ |energy|)
    (hgradientDifference : |gradient - modelGradient| ≤ differenceBound)
    (hgradientSum : |gradient + modelGradient| ≤ sumBound) :
    |(gradient ^ 2 - modelGradient ^ 2) / (4 * energy)| ≤
      differenceBound * sumBound / (4 * energyFloor) := by
  have hnum :=
    abs_sq_sub_sq_le_of_sub_add_bounds
      gradient modelGradient differenceBound sumBound
      hgradientDifference hgradientSum
  have hdifferenceNonneg : 0 ≤ differenceBound :=
    le_trans (abs_nonneg _) hgradientDifference
  have hsumNonneg : 0 ≤ sumBound :=
    le_trans (abs_nonneg _) hgradientSum
  have hproductNonneg : 0 ≤ differenceBound * sumBound :=
    mul_nonneg hdifferenceNonneg hsumNonneg
  have henergyAbsPos : 0 < |energy| :=
    lt_of_lt_of_le henergyFloorPos henergyFloor
  have hdenPos : 0 < 4 * |energy| := by positivity
  have hfloorDenPos : 0 < 4 * energyFloor := by positivity
  have hdenComparison : 4 * energyFloor ≤ 4 * |energy| :=
    mul_le_mul_of_nonneg_left henergyFloor (by norm_num)
  have habsDen : |4 * energy| = 4 * |energy| := by
    rw [abs_mul]
    norm_num
  rw [abs_div, habsDen]
  calc
    |gradient ^ 2 - modelGradient ^ 2| / (4 * |energy|) ≤
        (differenceBound * sumBound) / (4 * |energy|) :=
      div_le_div_of_nonneg_right hnum (le_of_lt hdenPos)
    _ ≤ (differenceBound * sumBound) / (4 * energyFloor) :=
      div_le_div_of_nonneg_left hproductNonneg hfloorDenPos hdenComparison

/-- Primitive energy and model-gradient bounds imply the second divided
residual-energy channel. -/
theorem abs_energyDenominatorChannel_le_of_primitive_bounds
    (energy modelEnergy modelGradient gradientBound energyDifferenceBound
      energyFloor modelEnergyFloor : ℝ)
    (henergyFloorPos : 0 < energyFloor)
    (hmodelEnergyFloorPos : 0 < modelEnergyFloor)
    (henergyFloor : energyFloor ≤ |energy|)
    (hmodelEnergyFloor : modelEnergyFloor ≤ |modelEnergy|)
    (hgradient : |modelGradient| ≤ gradientBound)
    (henergyDifference : |modelEnergy - energy| ≤ energyDifferenceBound) :
    |modelGradient ^ 2 * (modelEnergy - energy) /
        (4 * energy * modelEnergy)| ≤
      gradientBound ^ 2 * energyDifferenceBound /
        (4 * energyFloor * modelEnergyFloor) := by
  have hgradientBoundNonneg : 0 ≤ gradientBound :=
    le_trans (abs_nonneg _) hgradient
  have henergyDifferenceBoundNonneg : 0 ≤ energyDifferenceBound :=
    le_trans (abs_nonneg _) henergyDifference
  have hgradientSq : |modelGradient| ^ 2 ≤ gradientBound ^ 2 := by
    nlinarith [sq_nonneg (gradientBound - |modelGradient|)]
  have hgradientSqAbs : |modelGradient ^ 2| ≤ gradientBound ^ 2 := by
    rw [abs_pow]
    exact hgradientSq
  have hnum :
      |modelGradient ^ 2 * (modelEnergy - energy)| ≤
        gradientBound ^ 2 * energyDifferenceBound := by
    rw [abs_mul]
    exact mul_le_mul hgradientSqAbs henergyDifference
      (abs_nonneg _) (sq_nonneg _)
  have hnumNonneg :
      0 ≤ gradientBound ^ 2 * energyDifferenceBound :=
    mul_nonneg (sq_nonneg _) henergyDifferenceBoundNonneg
  have henergyAbsPos : 0 < |energy| :=
    lt_of_lt_of_le henergyFloorPos henergyFloor
  have hmodelEnergyAbsPos : 0 < |modelEnergy| :=
    lt_of_lt_of_le hmodelEnergyFloorPos hmodelEnergyFloor
  have hdenPos : 0 < 4 * |energy| * |modelEnergy| := by positivity
  have hfloorDenPos :
      0 < 4 * energyFloor * modelEnergyFloor := by positivity
  have hfirstFactor : 4 * energyFloor ≤ 4 * |energy| :=
    mul_le_mul_of_nonneg_left henergyFloor (by norm_num)
  have hdenComparison :
      4 * energyFloor * modelEnergyFloor ≤
        4 * |energy| * |modelEnergy| :=
    mul_le_mul hfirstFactor hmodelEnergyFloor
      (le_of_lt hmodelEnergyFloorPos) (by positivity)
  have habsDen :
      |4 * energy * modelEnergy| = 4 * |energy| * |modelEnergy| := by
    rw [abs_mul, abs_mul]
    norm_num
  rw [abs_div, habsDen]
  calc
    |modelGradient ^ 2 * (modelEnergy - energy)| /
        (4 * |energy| * |modelEnergy|) ≤
      (gradientBound ^ 2 * energyDifferenceBound) /
        (4 * |energy| * |modelEnergy|) :=
      div_le_div_of_nonneg_right hnum (le_of_lt hdenPos)
    _ ≤ (gradientBound ^ 2 * energyDifferenceBound) /
        (4 * energyFloor * modelEnergyFloor) :=
      div_le_div_of_nonneg_left hnumNonneg hfloorDenPos hdenComparison

namespace PhaseProjectionData

/-- Primitive `O(1/M)` jet estimates and fixed positive denominator floors
supply all three channels of `MicroscopicJetTransfer`.  Consequently the
finite reoptimized microscopic coefficient is eventually bounded below by one
strictly positive constant. -/
theorem eventually_positive_quadraticMicroscopicCoercivity_of_primitive_bounds
    (d : PhaseProjectionData) (h : d.IsAdmissible)
    (energy gradient localCoercivity phaseProjection : ℕ → ℝ)
    (curvatureConstant gradientDifferenceConstant energyDifferenceConstant
      gradientSumBound modelGradientBound energyFloor modelEnergyFloor : ℝ)
    (henergyFloorPos : 0 < energyFloor)
    (hmodelEnergyFloorPos : 0 < modelEnergyFloor)
    (hx : ∀ M : ℕ, (phaseProjection M) ^ 2 ≤ d.alphaSq)
    (henergyFloor : ∀ M : ℕ, 1 ≤ M → energyFloor ≤ |energy M|)
    (hmodelEnergyFloor : ∀ M : ℕ,
      modelEnergyFloor ≤
        |d.rho + (phaseProjection M) ^ 2 / d.kappa|)
    (hcurvature : ∀ M : ℕ, 1 ≤ M →
      |localCoercivity M - d.kappa| ≤ curvatureConstant / (M : ℝ))
    (hgradientDifference : ∀ M : ℕ, 1 ≤ M →
      |gradient M - 2 * phaseProjection M| ≤
        gradientDifferenceConstant / (M : ℝ))
    (hgradientSum : ∀ M : ℕ, 1 ≤ M →
      |gradient M + 2 * phaseProjection M| ≤ gradientSumBound)
    (hmodelGradient : ∀ M : ℕ,
      |2 * phaseProjection M| ≤ modelGradientBound)
    (henergyDifference : ∀ M : ℕ, 1 ≤ M →
      |(d.rho + (phaseProjection M) ^ 2 / d.kappa) - energy M| ≤
        energyDifferenceConstant / (M : ℝ)) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ M : ℕ in atTop,
        c ≤ quadraticMicroscopicCoercivity
          (energy M) (gradient M) (localCoercivity M) := by
  refine d.eventually_positive_quadraticMicroscopicCoercivity_of_inv_perturbation_bounds
    h energy gradient localCoercivity phaseProjection
    curvatureConstant
    (gradientDifferenceConstant * gradientSumBound / (4 * energyFloor))
    (modelGradientBound ^ 2 * energyDifferenceConstant /
      (4 * energyFloor * modelEnergyFloor))
    hx ?_ hcurvature ?_ ?_
  · intro M hM
    have hpositive : 0 < |energy M| :=
      lt_of_lt_of_le henergyFloorPos (henergyFloor M hM)
    exact (abs_pos.mp hpositive)
  · intro M hM
    have hbound :=
      abs_gradientSquareChannel_le_of_primitive_bounds
        (energy M) (gradient M) (2 * phaseProjection M)
        (gradientDifferenceConstant / (M : ℝ))
        gradientSumBound energyFloor
        henergyFloorPos (henergyFloor M hM)
        (hgradientDifference M hM) (hgradientSum M hM)
    calc
      |gradient M ^ 2 - (2 * phaseProjection M) ^ 2 /
          (4 * energy M)| =
        |(gradient M ^ 2 - (2 * phaseProjection M) ^ 2) /
          (4 * energy M)| := by ring_nf
      _ ≤ (gradientDifferenceConstant / (M : ℝ)) *
          gradientSumBound / (4 * energyFloor) := hbound
      _ = (gradientDifferenceConstant * gradientSumBound /
          (4 * energyFloor)) / (M : ℝ) := by ring
  · intro M hM
    let modelEnergy : ℝ :=
      d.rho + (phaseProjection M) ^ 2 / d.kappa
    have hbound :=
      abs_energyDenominatorChannel_le_of_primitive_bounds
        (energy M) modelEnergy (2 * phaseProjection M)
        modelGradientBound
        (energyDifferenceConstant / (M : ℝ))
        energyFloor modelEnergyFloor
        henergyFloorPos hmodelEnergyFloorPos
        (henergyFloor M hM)
        (by simpa [modelEnergy] using hmodelEnergyFloor M)
        (hmodelGradient M)
        (by simpa [modelEnergy] using henergyDifference M hM)
    simpa [modelEnergy] using
      (hbound.trans_eq (by ring))

end PhaseProjectionData

end

end GenuineZeroUniformAtlasEnergy

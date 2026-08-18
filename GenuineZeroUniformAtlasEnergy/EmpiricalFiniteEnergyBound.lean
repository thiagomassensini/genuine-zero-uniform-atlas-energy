import GenuineZeroUniformAtlasEnergy.EmpiricalFinitePairingBound

/-!
# Corrected finite reoptimized-energy bound

The corrected finite energy is

```math
||R_M||^2 - Im(<R_M,V_M>)^2 / ||V_M||^2.
```

The leading model is the same expression with the phase-rotated cutoff vector
and the infinite clock tangent.  The exact phase geometry identifies it with

```math
rho + X_M^2 / kappa.
```

This module separates the finite error into the residual norm, pairing, and
clock-Gram channels.  A positive finite clock-Gram floor is kept explicit.
-/

namespace GenuineZeroUniformAtlasEnergy

open CPFormal.Analytic.Cp

noncomputable section

/-- Norm perturbations control squared-norm perturbations. -/
theorem abs_norm_sq_sub_norm_sq_le_of_norm_sub_le
    {E : Type*} [NormedAddCommGroup E]
    (x y : E) (error : ℝ)
    (hxy : ‖x - y‖ ≤ error) :
    |‖x‖ ^ 2 - ‖y‖ ^ 2| ≤
      error * (error + 2 * ‖y‖) := by
  have herrorNonneg : 0 ≤ error := le_trans (norm_nonneg _) hxy
  have hdiff : |‖x‖ - ‖y‖| ≤ error :=
    le_trans (abs_norm_sub_norm_le x y) hxy
  have hxNorm : ‖x‖ ≤ error + ‖y‖ := by
    calc
      ‖x‖ = ‖(x - y) + y‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - y‖ + ‖y‖ := norm_add_le _ _
      _ ≤ error + ‖y‖ := add_le_add_right hxy _
  have hsum : |‖x‖ + ‖y‖| ≤ error + 2 * ‖y‖ := by
    rw [abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    linarith
  exact abs_sq_sub_sq_le_of_sub_add_bounds
    ‖x‖ ‖y‖ error (error + 2 * ‖y‖) hdiff hsum

/-- First-jet perturbations control the clock Gram scalar. -/
theorem abs_empiricalQuadraticClockKappa_sub_le_of_norm_sub_le
    (firstJet modelFirstJet : EmpiricalCameraStack) (error : ℝ)
    (hfirst : ‖firstJet - modelFirstJet‖ ≤ error) :
    |empiricalQuadraticClockKappa firstJet -
        empiricalQuadraticClockKappa modelFirstJet| ≤
      error * (error + 2 * ‖modelFirstJet‖) := by
  unfold empiricalQuadraticClockKappa
  exact abs_norm_sq_sub_norm_sq_le_of_norm_sub_le
    firstJet modelFirstJet error hfirst

/-- Scalar quotient perturbation with both denominator floors visible. -/
theorem abs_sq_div_sub_sq_div_le_of_primitive_bounds
    (kappa modelKappa y modelY yDifference ySum modelYBound
      kappaDifference kappaFloor modelKappaFloor : ℝ)
    (hkappaFloorPos : 0 < kappaFloor)
    (hmodelKappaFloorPos : 0 < modelKappaFloor)
    (hkappaFloor : kappaFloor ≤ |kappa|)
    (hmodelKappaFloor : modelKappaFloor ≤ |modelKappa|)
    (hyDifference : |y - modelY| ≤ yDifference)
    (hySum : |y + modelY| ≤ ySum)
    (hmodelY : |modelY| ≤ modelYBound)
    (hkappaDifference : |modelKappa - kappa| ≤ kappaDifference) :
    |y ^ 2 / kappa - modelY ^ 2 / modelKappa| ≤
      yDifference * ySum / kappaFloor +
        modelYBound ^ 2 * kappaDifference /
          (kappaFloor * modelKappaFloor) := by
  have hkappaAbsPos : 0 < |kappa| :=
    lt_of_lt_of_le hkappaFloorPos hkappaFloor
  have hmodelKappaAbsPos : 0 < |modelKappa| :=
    lt_of_lt_of_le hmodelKappaFloorPos hmodelKappaFloor
  have hkappaNe : kappa ≠ 0 := abs_pos.mp hkappaAbsPos
  have hmodelKappaNe : modelKappa ≠ 0 := abs_pos.mp hmodelKappaAbsPos
  have hyDifferenceNonneg : 0 ≤ yDifference :=
    le_trans (abs_nonneg _) hyDifference
  have hySumNonneg : 0 ≤ ySum :=
    le_trans (abs_nonneg _) hySum
  have hfirstNumerator :=
    abs_sq_sub_sq_le_of_sub_add_bounds
      y modelY yDifference ySum hyDifference hySum
  have hfirst :
      |(y ^ 2 - modelY ^ 2) / kappa| ≤
        yDifference * ySum / kappaFloor := by
    rw [abs_div]
    calc
      |y ^ 2 - modelY ^ 2| / |kappa| ≤
          (yDifference * ySum) / |kappa| :=
        div_le_div_of_nonneg_right hfirstNumerator (le_of_lt hkappaAbsPos)
      _ ≤ (yDifference * ySum) / kappaFloor :=
        div_le_div_of_nonneg_left
          (mul_nonneg hyDifferenceNonneg hySumNonneg)
          hkappaFloorPos hkappaFloor
  have hmodelYBoundNonneg : 0 ≤ modelYBound :=
    le_trans (abs_nonneg _) hmodelY
  have hkappaDifferenceNonneg : 0 ≤ kappaDifference :=
    le_trans (abs_nonneg _) hkappaDifference
  have hmodelYSq : |modelY| ^ 2 ≤ modelYBound ^ 2 := by
    have hmul :=
      mul_le_mul hmodelY hmodelY (abs_nonneg _) hmodelYBoundNonneg
    simpa [pow_two] using hmul
  have hmodelYSqAbs : |modelY ^ 2| ≤ modelYBound ^ 2 := by
    rw [abs_pow]
    exact hmodelYSq
  have hsecondNumerator :
      |modelY ^ 2 * (modelKappa - kappa)| ≤
        modelYBound ^ 2 * kappaDifference := by
    rw [abs_mul]
    exact mul_le_mul hmodelYSqAbs hkappaDifference
      (abs_nonneg _) (sq_nonneg _)
  have hdenFloorPos : 0 < kappaFloor * modelKappaFloor :=
    mul_pos hkappaFloorPos hmodelKappaFloorPos
  have hdenComparison :
      kappaFloor * modelKappaFloor ≤ |kappa| * |modelKappa| :=
    mul_le_mul hkappaFloor hmodelKappaFloor
      (le_of_lt hmodelKappaFloorPos) (abs_nonneg _)
  have hsecond :
      |modelY ^ 2 * (modelKappa - kappa) /
          (kappa * modelKappa)| ≤
        modelYBound ^ 2 * kappaDifference /
          (kappaFloor * modelKappaFloor) := by
    rw [abs_div, abs_mul]
    calc
      |modelY ^ 2 * (modelKappa - kappa)| /
          (|kappa| * |modelKappa|) ≤
        (modelYBound ^ 2 * kappaDifference) /
          (|kappa| * |modelKappa|) :=
        div_le_div_of_nonneg_right hsecondNumerator
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ ≤ (modelYBound ^ 2 * kappaDifference) /
          (kappaFloor * modelKappaFloor) :=
        div_le_div_of_nonneg_left
          (mul_nonneg (sq_nonneg _) hkappaDifferenceNonneg)
          hdenFloorPos hdenComparison
  have hrewrite :
      y ^ 2 / kappa - modelY ^ 2 / modelKappa =
        (y ^ 2 - modelY ^ 2) / kappa +
          modelY ^ 2 * (modelKappa - kappa) /
            (kappa * modelKappa) := by
    field_simp [hkappaNe, hmodelKappaNe]
    ring
  rw [hrewrite]
  calc
    |(y ^ 2 - modelY ^ 2) / kappa +
        modelY ^ 2 * (modelKappa - kappa) /
          (kappa * modelKappa)| ≤
      |(y ^ 2 - modelY ^ 2) / kappa| +
        |modelY ^ 2 * (modelKappa - kappa) /
          (kappa * modelKappa)| := abs_add _ _
    _ ≤ yDifference * ySum / kappaFloor +
        modelYBound ^ 2 * kappaDifference /
          (kappaFloor * modelKappaFloor) := add_le_add hfirst hsecond

/-- Leading corrected reoptimized energy. -/
def empiricalLeadingCorrectedReoptimizedEnergy
    (M : ℕ) (time : ℝ) : ℝ :=
  empiricalQuadraticReoptimizedEnergy
    (empiricalPhaseNormalizedLeadingResidualStack M time)
    (empiricalClockTangentVector (criticalLineParameter time))

/-- Exact identification of the leading corrected energy with the phase
model denominator. -/
theorem empiricalLeadingCorrectedReoptimizedEnergy_eq_phaseDenominator
    (M : ℕ) (time : ℝ) :
    empiricalLeadingCorrectedReoptimizedEnergy M time =
      empiricalStackRho (criticalLineParameter time) +
        finiteEmpiricalPhaseProjection time M ^ 2 /
          empiricalStackKappa (criticalLineParameter time) := by
  have hphase :=
    empiricalStackPhaseProjection_sq_add_imag_sq
      (criticalLineParameter time) (empiricalCutoffPhase time M)
  have hphase' :
      (empiricalLeadingPhasePairing M time).re ^ 2 +
          (empiricalLeadingPhasePairing M time).im ^ 2 =
        empiricalStackAlphaSq (criticalLineParameter time) := by
    simpa [empiricalLeadingPhasePairing,
      finiteEmpiricalPhaseProjection] using hphase
  unfold empiricalLeadingCorrectedReoptimizedEnergy
    empiricalQuadraticReoptimizedEnergy empiricalQuadraticClockKappa
  rw [empiricalQuadraticClockPairing_phaseNormalizedLeading_eq,
    norm_empiricalPhaseNormalizedLeadingResidualStack]
  unfold empiricalStackRho empiricalStackAmplitudeSq
    empiricalStackKappa finiteEmpiricalPhaseProjection
  rw [← hphase']
  ring

/-- Explicit first-jet Gram error used by the finite energy ledger. -/
def empiricalFiniteCorrectedKappaErrorBound
    (M : ℕ) (time : ℝ) : ℝ :=
  empiricalFiniteCorrectedFirstJetStackErrorBound M time *
    (empiricalFiniteCorrectedFirstJetStackErrorBound M time +
      2 * ‖empiricalClockTangentVector (criticalLineParameter time)‖)

/-- Explicit corrected finite-energy error once a positive finite clock-Gram
floor is supplied. -/
def empiricalFiniteCorrectedEnergyErrorBound
    (M : ℕ) (time finiteKappaFloor : ℝ) : ℝ :=
  empiricalScaledFiniteResidualStackErrorBound M time *
      (empiricalScaledFiniteResidualStackErrorBound M time +
        2 * ‖empiricalLeadingCutoffVector (criticalLineParameter time)‖) +
    empiricalFiniteCorrectedPairingErrorBound M time *
        (empiricalFiniteCorrectedPairingErrorBound M time +
          2 * ‖empiricalLeadingPhasePairing M time‖) /
      finiteKappaFloor +
    ‖empiricalLeadingPhasePairing M time‖ ^ 2 *
        empiricalFiniteCorrectedKappaErrorBound M time /
      (finiteKappaFloor *
        empiricalStackKappa (criticalLineParameter time))

/-- Concrete corrected finite-energy approximation. -/
theorem abs_finiteEmpiricalCorrectedReoptimizedEnergy_sub_model_le
    (M : ℕ) (hM : 1 ≤ M) (time finiteKappaFloor : ℝ)
    (hzero : genuineContinuation (criticalLineParameter time) = 0)
    (hsimple : deriv genuineContinuation (criticalLineParameter time) ≠ 0)
    (hfiniteKappaFloorPos : 0 < finiteKappaFloor)
    (hfiniteKappaFloor :
      finiteKappaFloor ≤
        |empiricalQuadraticClockKappa
          (finiteEmpiricalCameraCorrectedDerivativeStack M
            (criticalLineParameter time))|) :
    |finiteEmpiricalCorrectedReoptimizedEnergy M time -
        (empiricalStackRho (criticalLineParameter time) +
          finiteEmpiricalPhaseProjection time M ^ 2 /
            empiricalStackKappa (criticalLineParameter time))| ≤
      empiricalFiniteCorrectedEnergyErrorBound M time finiteKappaFloor := by
  let residual := empiricalPhaseNormalizedFiniteResidualStack M time
  let modelResidual := empiricalPhaseNormalizedLeadingResidualStack M time
  let firstJet := finiteEmpiricalCameraCorrectedDerivativeStack M
    (criticalLineParameter time)
  let modelFirstJet := empiricalClockTangentVector (criticalLineParameter time)
  let pairing := finiteEmpiricalCorrectedPhasePairing M time
  let modelPairing := empiricalLeadingPhasePairing M time
  let kappa := empiricalQuadraticClockKappa firstJet
  let modelKappa := empiricalQuadraticClockKappa modelFirstJet
  have hresidual :=
    norm_empiricalPhaseNormalizedFiniteResidualStack_sub_leading_le
      M hM time hzero
  have hfirst :=
    norm_finiteEmpiricalCameraCorrectedDerivativeStack_sub_clockTangent_le
      M hM time hzero
  have hpairing :=
    norm_finiteEmpiricalCorrectedPhasePairing_sub_leading_le
      M hM time hzero
  have hvalue :=
    abs_norm_sq_sub_norm_sq_le_of_norm_sub_le
      residual modelResidual
      (empiricalScaledFiniteResidualStackErrorBound M time) hresidual
  have hkappaDifference :=
    abs_empiricalQuadraticClockKappa_sub_le_of_norm_sub_le
      firstJet modelFirstJet
      (empiricalFiniteCorrectedFirstJetStackErrorBound M time) hfirst
  have hmodelKappaPos : 0 < modelKappa := by
    simpa [modelKappa, modelFirstJet, empiricalQuadraticClockKappa,
      empiricalStackKappa] using
      empiricalStackKappa_pos
        (by norm_num [criticalLineParameter_re]) hsimple
  have hyDifference :
      |pairing.im - modelPairing.im| ≤
        empiricalFiniteCorrectedPairingErrorBound M time := by
    have him := Complex.abs_im_le_norm (pairing - modelPairing)
    have hre : (pairing - modelPairing).im = pairing.im - modelPairing.im := by
      rfl
    rw [hre] at him
    exact le_trans him hpairing
  have hySum :
      |pairing.im + modelPairing.im| ≤
        empiricalFiniteCorrectedPairingErrorBound M time +
          2 * ‖modelPairing‖ := by
    have hrewrite :
        pairing.im + modelPairing.im =
          (pairing.im - modelPairing.im) + 2 * modelPairing.im := by
      ring
    rw [hrewrite]
    calc
      |(pairing.im - modelPairing.im) + 2 * modelPairing.im| ≤
        |pairing.im - modelPairing.im| + |2 * modelPairing.im| := abs_add _ _
      _ ≤ empiricalFiniteCorrectedPairingErrorBound M time +
          2 * ‖modelPairing‖ := by
        apply add_le_add hyDifference
        rw [abs_mul]
        norm_num
        exact mul_le_mul_of_nonneg_left
          (Complex.abs_im_le_norm modelPairing) (by norm_num)
  have hquotient :=
    abs_sq_div_sub_sq_div_le_of_primitive_bounds
      kappa modelKappa pairing.im modelPairing.im
      (empiricalFiniteCorrectedPairingErrorBound M time)
      (empiricalFiniteCorrectedPairingErrorBound M time +
        2 * ‖modelPairing‖)
      ‖modelPairing‖
      (empiricalFiniteCorrectedKappaErrorBound M time)
      finiteKappaFloor modelKappa
      hfiniteKappaFloorPos hmodelKappaPos
      (by simpa [kappa, firstJet] using hfiniteKappaFloor)
      (by rw [abs_of_pos hmodelKappaPos])
      hyDifference hySum (Complex.abs_im_le_norm modelPairing)
      (by simpa [kappa, modelKappa, firstJet, modelFirstJet,
        empiricalFiniteCorrectedKappaErrorBound] using hkappaDifference)
  have hmodelEnergy :=
    empiricalLeadingCorrectedReoptimizedEnergy_eq_phaseDenominator M time
  rw [← hmodelEnergy]
  have hrewrite :
      finiteEmpiricalCorrectedReoptimizedEnergy M time -
          empiricalLeadingCorrectedReoptimizedEnergy M time =
        (‖residual‖ ^ 2 - ‖modelResidual‖ ^ 2) -
          (pairing.im ^ 2 / kappa - modelPairing.im ^ 2 / modelKappa) := by
    rfl
  rw [hrewrite]
  calc
    |(‖residual‖ ^ 2 - ‖modelResidual‖ ^ 2) -
        (pairing.im ^ 2 / kappa - modelPairing.im ^ 2 / modelKappa)| ≤
      |‖residual‖ ^ 2 - ‖modelResidual‖ ^ 2| +
        |pairing.im ^ 2 / kappa - modelPairing.im ^ 2 / modelKappa| :=
      abs_sub _ _
    _ ≤ empiricalScaledFiniteResidualStackErrorBound M time *
        (empiricalScaledFiniteResidualStackErrorBound M time +
          2 * ‖empiricalLeadingCutoffVector (criticalLineParameter time)‖) +
      (empiricalFiniteCorrectedPairingErrorBound M time *
          (empiricalFiniteCorrectedPairingErrorBound M time +
            2 * ‖empiricalLeadingPhasePairing M time‖) /
        finiteKappaFloor +
      ‖empiricalLeadingPhasePairing M time‖ ^ 2 *
          empiricalFiniteCorrectedKappaErrorBound M time /
        (finiteKappaFloor *
          empiricalStackKappa (criticalLineParameter time))) := by
      apply add_le_add
      · simpa [modelResidual,
          norm_empiricalPhaseNormalizedLeadingResidualStack] using hvalue
      · simpa [pairing, modelPairing, kappa, modelKappa, modelFirstJet,
          empiricalQuadraticClockKappa, empiricalStackKappa] using hquotient
    _ = empiricalFiniteCorrectedEnergyErrorBound M time finiteKappaFloor := rfl

end

end GenuineZeroUniformAtlasEnergy

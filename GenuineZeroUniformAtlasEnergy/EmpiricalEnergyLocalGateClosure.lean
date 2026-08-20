import GenuineZeroUniformAtlasEnergy.EmpiricalNonJetGateClosure

/-!
# Finite energy floor and local Schur closure

The exact residual, pairing, first-jet, and second-jet estimates are now fixed
inverse-cutoff bounds.  This module consumes them to prove:

* a fixed `C_E(t)/M` approximation of the corrected reoptimized energy;
* an eventual positive floor `rho(t)/2` for that finite energy;
* a fixed `C_c(t)/M` approximation of the concrete local Schur coefficient.

The proofs use only the exact camera identities and Cauchy-tail bounds already
in the public dependency graph.  No numerical height or finite-cutoff witness
is admitted as a premise.
-/

open Filter

namespace GenuineZeroUniformAtlasEnergy

open CPFormal.Analytic.Cp

noncomputable section

/-- The leading phase pairing has a norm independent of the cutoff phase. -/
@[simp] theorem norm_empiricalLeadingPhasePairing
    (M : ℕ) (time : ℝ) :
    ‖empiricalLeadingPhasePairing M time‖ =
      ‖empiricalStackPairing (criticalLineParameter time)‖ := by
  unfold empiricalLeadingPhasePairing
  rw [norm_mul]
  have hunit :
      ‖Complex.exp
        ((empiricalCutoffPhase time M : ℂ) * Complex.I)‖ = 1 := by
    exact Complex.norm_exp_ofReal_mul_I (empiricalCutoffPhase time M)
  rw [hunit, one_mul]

/-- The explicit corrected clock-Gram error ledger has the same fixed
inverse-cutoff bound as the actual clock-Gram difference. -/
theorem empiricalFiniteCorrectedKappaErrorBound_le_inverseCutoff
    (M : ℕ) (hM : 1 ≤ M) (time : ℝ) :
    empiricalFiniteCorrectedKappaErrorBound M time ≤
      empiricalCorrectedKappaInverseCutoffConstant time / (M : ℝ) := by
  let error := empiricalFiniteCorrectedFirstJetStackErrorBound M time
  let fixed := empiricalCorrectedFirstJetInverseCutoffConstant time
  let tangent := empiricalClockTangentVector (criticalLineParameter time)
  have herror :=
    empiricalFiniteCorrectedFirstJetStackErrorBound_le_inverseCutoff M hM time
  have hMreal : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hfixedNonneg : 0 ≤ fixed :=
    empiricalCorrectedFirstJetInverseCutoffConstant_nonneg time
  have herrorNonneg : 0 ≤ error := by
    dsimp [error]
    exact Real.sqrt_nonneg _
  have hdivNonneg : 0 ≤ fixed / (M : ℝ) :=
    div_nonneg hfixedNonneg (by positivity)
  have herrorFixed : error ≤ fixed :=
    herror.trans (div_le_self hfixedNonneg hMreal)
  have hsum : error + 2 * ‖tangent‖ ≤ fixed + 2 * ‖tangent‖ :=
    add_le_add herrorFixed le_rfl
  have hproduct :
      error * (error + 2 * ‖tangent‖) ≤
        (fixed / (M : ℝ)) * (fixed + 2 * ‖tangent‖) :=
    mul_le_mul herror hsum (by positivity) hdivNonneg
  calc
    empiricalFiniteCorrectedKappaErrorBound M time =
        error * (error + 2 * ‖tangent‖) := rfl
    _ ≤ (fixed / (M : ℝ)) * (fixed + 2 * ‖tangent‖) := hproduct
    _ = empiricalCorrectedKappaInverseCutoffConstant time / (M : ℝ) := by
      unfold empiricalCorrectedKappaInverseCutoffConstant
      dsimp [fixed, tangent]
      ring

/-- The explicit raw clock-Gram ledger has a fixed inverse-cutoff bound. -/
theorem empiricalFiniteRawKappaErrorBound_le_inverseCutoff
    (M : ℕ) (hM : 1 ≤ M) (time : ℝ) :
    empiricalFiniteRawKappaErrorBound M time ≤
      empiricalRawKappaInverseCutoffConstant time / (M : ℝ) := by
  let error := empiricalFiniteFirstJetStackErrorBound M time
  let fixed := empiricalRawFirstJetInverseCutoffConstant time
  let tangent := empiricalClockTangentVector (criticalLineParameter time)
  have herror :=
    empiricalFiniteFirstJetStackErrorBound_le_inverseCutoff M hM time
  have hMreal : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hfixedNonneg : 0 ≤ fixed :=
    empiricalRawFirstJetInverseCutoffConstant_nonneg time
  have herrorNonneg : 0 ≤ error := by
    dsimp [error]
    exact Real.sqrt_nonneg _
  have hdivNonneg : 0 ≤ fixed / (M : ℝ) :=
    div_nonneg hfixedNonneg (by positivity)
  have herrorFixed : error ≤ fixed :=
    herror.trans (div_le_self hfixedNonneg hMreal)
  have hsum : error + 2 * ‖tangent‖ ≤ fixed + 2 * ‖tangent‖ :=
    add_le_add herrorFixed le_rfl
  have hproduct :
      error * (error + 2 * ‖tangent‖) ≤
        (fixed / (M : ℝ)) * (fixed + 2 * ‖tangent‖) :=
    mul_le_mul herror hsum (by positivity) hdivNonneg
  calc
    empiricalFiniteRawKappaErrorBound M time =
        error * (error + 2 * ‖tangent‖) := rfl
    _ ≤ (fixed / (M : ℝ)) * (fixed + 2 * ‖tangent‖) := hproduct
    _ = empiricalRawKappaInverseCutoffConstant time / (M : ℝ) := by
      unfold empiricalRawKappaInverseCutoffConstant
      dsimp [fixed, tangent]
      ring

/-- Fixed constant for the corrected finite-energy error. -/
def empiricalCorrectedEnergyInverseCutoffConstant (time : ℝ) : ℝ :=
  let residualConstant := empiricalScaledResidualInverseCutoffConstant time
  let pairingConstant := empiricalCorrectedPairingInverseCutoffConstant time
  let kappaConstant := empiricalCorrectedKappaInverseCutoffConstant time
  let leadingNorm :=
    ‖empiricalLeadingCutoffVector (criticalLineParameter time)‖
  let pairingNorm :=
    ‖empiricalStackPairing (criticalLineParameter time)‖
  let kappa := empiricalStackKappa (criticalLineParameter time)
  residualConstant * (residualConstant + 2 * leadingNorm) +
    pairingConstant * (pairingConstant + 2 * pairingNorm) / (kappa / 2) +
    pairingNorm ^ 2 * kappaConstant / ((kappa / 2) * kappa)

lemma empiricalCorrectedEnergyInverseCutoffConstant_nonneg
    (time : ℝ)
    (hsimple : deriv genuineContinuation (criticalLineParameter time) ≠ 0) :
    0 ≤ empiricalCorrectedEnergyInverseCutoffConstant time := by
  have hkappa :
      0 < empiricalStackKappa (criticalLineParameter time) :=
    empiricalStackKappa_pos
      (by norm_num [criticalLineParameter_re]) hsimple
  have hres := empiricalScaledResidualInverseCutoffConstant_nonneg time
  have hpair := empiricalCorrectedPairingInverseCutoffConstant_nonneg time
  have hkerr := empiricalCorrectedKappaInverseCutoffConstant_nonneg time
  dsimp [empiricalCorrectedEnergyInverseCutoffConstant]
  exact add_nonneg
    (add_nonneg
      (mul_nonneg hres (add_nonneg hres
        (mul_nonneg (by norm_num) (norm_nonneg _))))
      (div_nonneg
        (mul_nonneg hpair (add_nonneg hpair
          (mul_nonneg (by norm_num) (norm_nonneg _))))
        (by positivity)))
    (div_nonneg (mul_nonneg (sq_nonneg _) hkerr) (by positivity))

/-- The explicit corrected finite-energy error is bounded by one fixed
`C_E(t)/M` once the limiting clock Gram is positive. -/
theorem empiricalFiniteCorrectedEnergyErrorBound_le_inverseCutoff
    (M : ℕ) (hM : 1 ≤ M) (time : ℝ)
    (hsimple : deriv genuineContinuation (criticalLineParameter time) ≠ 0) :
    empiricalFiniteCorrectedEnergyErrorBound M time
        (empiricalStackKappa (criticalLineParameter time) / 2) ≤
      empiricalCorrectedEnergyInverseCutoffConstant time / (M : ℝ) := by
  let residualError := empiricalScaledFiniteResidualStackErrorBound M time
  let pairingError := empiricalFiniteCorrectedPairingErrorBound M time
  let kappaError := empiricalFiniteCorrectedKappaErrorBound M time
  let residualConstant := empiricalScaledResidualInverseCutoffConstant time
  let pairingConstant := empiricalCorrectedPairingInverseCutoffConstant time
  let kappaConstant := empiricalCorrectedKappaInverseCutoffConstant time
  let leadingNorm :=
    ‖empiricalLeadingCutoffVector (criticalLineParameter time)‖
  let pairingNorm :=
    ‖empiricalStackPairing (criticalLineParameter time)‖
  let kappa := empiricalStackKappa (criticalLineParameter time)
  have hkappa : 0 < kappa := by
    dsimp [kappa]
    exact empiricalStackKappa_pos
      (by norm_num [criticalLineParameter_re]) hsimple
  have hMreal : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hres :=
    empiricalScaledFiniteResidualStackErrorBound_le_inverseCutoff M hM time
  have hpair :=
    empiricalFiniteCorrectedPairingErrorBound_le_inverseCutoff M hM time
  have hkerr :=
    empiricalFiniteCorrectedKappaErrorBound_le_inverseCutoff M hM time
  have hresConstant : 0 ≤ residualConstant :=
    empiricalScaledResidualInverseCutoffConstant_nonneg time
  have hpairConstant : 0 ≤ pairingConstant :=
    empiricalCorrectedPairingInverseCutoffConstant_nonneg time
  have hkerrConstant : 0 ≤ kappaConstant :=
    empiricalCorrectedKappaInverseCutoffConstant_nonneg time
  have hresErrorNonneg : 0 ≤ residualError := by
    dsimp [residualError]
    exact Real.sqrt_nonneg _
  have hpairErrorNonneg : 0 ≤ pairingError := by
    dsimp [pairingError]
    unfold empiricalFiniteCorrectedPairingErrorBound
    exact add_nonneg
      (mul_nonneg (Real.sqrt_nonneg _)
        (add_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)))
      (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
  have hresDivNonneg : 0 ≤ residualConstant / (M : ℝ) :=
    div_nonneg hresConstant (by positivity)
  have hpairDivNonneg : 0 ≤ pairingConstant / (M : ℝ) :=
    div_nonneg hpairConstant (by positivity)
  have hresFixed : residualError ≤ residualConstant :=
    hres.trans (div_le_self hresConstant hMreal)
  have hpairFixed : pairingError ≤ pairingConstant :=
    hpair.trans (div_le_self hpairConstant hMreal)
  have hresSumNonneg : 0 ≤ residualError + 2 * leadingNorm :=
    add_nonneg hresErrorNonneg
      (mul_nonneg (by norm_num) (norm_nonneg _))
  have hpairSumNonneg : 0 ≤ pairingError + 2 * pairingNorm :=
    add_nonneg hpairErrorNonneg
      (mul_nonneg (by norm_num) (norm_nonneg _))
  have hresTerm :
      residualError * (residualError + 2 * leadingNorm) ≤
        (residualConstant * (residualConstant + 2 * leadingNorm)) /
          (M : ℝ) := by
    calc
      residualError * (residualError + 2 * leadingNorm) ≤
          (residualConstant / (M : ℝ)) *
            (residualConstant + 2 * leadingNorm) :=
        mul_le_mul hres (add_le_add hresFixed le_rfl)
          hresSumNonneg hresDivNonneg
      _ = (residualConstant *
          (residualConstant + 2 * leadingNorm)) / (M : ℝ) := by ring
  have hpairNumerator :
      pairingError * (pairingError + 2 * pairingNorm) ≤
        (pairingConstant / (M : ℝ)) *
          (pairingConstant + 2 * pairingNorm) :=
    mul_le_mul hpair (add_le_add hpairFixed le_rfl)
      hpairSumNonneg hpairDivNonneg
  have hpairTerm :
      pairingError * (pairingError + 2 * pairingNorm) / (kappa / 2) ≤
        (pairingConstant * (pairingConstant + 2 * pairingNorm) /
          (kappa / 2)) / (M : ℝ) := by
    calc
      pairingError * (pairingError + 2 * pairingNorm) / (kappa / 2) ≤
          ((pairingConstant / (M : ℝ)) *
            (pairingConstant + 2 * pairingNorm)) / (kappa / 2) :=
        div_le_div_of_nonneg_right hpairNumerator (by positivity)
      _ = (pairingConstant * (pairingConstant + 2 * pairingNorm) /
          (kappa / 2)) / (M : ℝ) := by ring
  have hkappaNumerator :
      pairingNorm ^ 2 * kappaError ≤
        pairingNorm ^ 2 * (kappaConstant / (M : ℝ)) :=
    mul_le_mul_of_nonneg_left hkerr (sq_nonneg _)
  have hkappaTerm :
      pairingNorm ^ 2 * kappaError / ((kappa / 2) * kappa) ≤
        (pairingNorm ^ 2 * kappaConstant / ((kappa / 2) * kappa)) /
          (M : ℝ) := by
    calc
      pairingNorm ^ 2 * kappaError / ((kappa / 2) * kappa) ≤
          (pairingNorm ^ 2 * (kappaConstant / (M : ℝ))) /
            ((kappa / 2) * kappa) :=
        div_le_div_of_nonneg_right hkappaNumerator (by positivity)
      _ = (pairingNorm ^ 2 * kappaConstant / ((kappa / 2) * kappa)) /
          (M : ℝ) := by ring
  unfold empiricalFiniteCorrectedEnergyErrorBound
  rw [norm_empiricalLeadingPhasePairing]
  calc
    residualError * (residualError + 2 * leadingNorm) +
          pairingError * (pairingError + 2 * pairingNorm) / (kappa / 2) +
          pairingNorm ^ 2 * kappaError / ((kappa / 2) * kappa) ≤
        (residualConstant * (residualConstant + 2 * leadingNorm)) /
            (M : ℝ) +
          (pairingConstant * (pairingConstant + 2 * pairingNorm) /
            (kappa / 2)) / (M : ℝ) +
          (pairingNorm ^ 2 * kappaConstant / ((kappa / 2) * kappa)) /
            (M : ℝ) :=
      add_le_add (add_le_add hresTerm hpairTerm) hkappaTerm
    _ = empiricalCorrectedEnergyInverseCutoffConstant time / (M : ℝ) := by
      unfold empiricalCorrectedEnergyInverseCutoffConstant
      dsimp [residualConstant, pairingConstant, kappaConstant,
        leadingNorm, pairingNorm, kappa]
      ring

/-- Eventually the corrected finite energy is within `C_E(t)/M` of its exact
phase denominator. -/
theorem eventually_abs_finiteEmpiricalCorrectedReoptimizedEnergy_sub_model_le_inverseCutoff
    (time : ℝ)
    (hzero : genuineContinuation (criticalLineParameter time) = 0)
    (hsimple : deriv genuineContinuation (criticalLineParameter time) ≠ 0) :
    ∀ᶠ M : ℕ in atTop,
      |finiteEmpiricalCorrectedReoptimizedEnergy M time -
        (empiricalStackRho (criticalLineParameter time) +
          finiteEmpiricalPhaseProjection time M ^ 2 /
            empiricalStackKappa (criticalLineParameter time))| ≤
        empiricalCorrectedEnergyInverseCutoffConstant time / (M : ℝ) := by
  let kappa := empiricalStackKappa (criticalLineParameter time)
  have hkappa : 0 < kappa := by
    dsimp [kappa]
    exact empiricalStackKappa_pos
      (by norm_num [criticalLineParameter_re]) hsimple
  filter_upwards [eventually_finiteEmpiricalCorrectedKappa_ge_half
      time hzero hsimple, eventually_ge_atTop 1] with M hkappaFloor hM
  have hfiniteKappaNonneg :
      0 ≤ empiricalQuadraticClockKappa
        (finiteEmpiricalCameraCorrectedDerivativeStack M
          (criticalLineParameter time)) := by
    unfold empiricalQuadraticClockKappa
    positivity
  have hkappaFloorAbs :
      kappa / 2 ≤
        |empiricalQuadraticClockKappa
          (finiteEmpiricalCameraCorrectedDerivativeStack M
            (criticalLineParameter time))| := by
    rw [abs_of_nonneg hfiniteKappaNonneg]
    exact hkappaFloor
  have hbase :=
    abs_finiteEmpiricalCorrectedReoptimizedEnergy_sub_model_le
      M hM time (kappa / 2) hzero hsimple
      (by positivity) hkappaFloorAbs
  exact hbase.trans
    (empiricalFiniteCorrectedEnergyErrorBound_le_inverseCutoff
      M hM time hsimple)

/-- Eventually the corrected finite reoptimized energy is bounded below by
half of the exact positive transverse residual `rho(t)`. -/
theorem eventually_finiteEmpiricalCorrectedReoptimizedEnergy_ge_half_rho
    (time : ℝ)
    (hzero : genuineContinuation (criticalLineParameter time) = 0)
    (hsimple : deriv genuineContinuation (criticalLineParameter time) ≠ 0) :
    ∀ᶠ M : ℕ in atTop,
      empiricalStackRho (criticalLineParameter time) / 2 ≤
        finiteEmpiricalCorrectedReoptimizedEnergy M time := by
  let rho := empiricalStackRho (criticalLineParameter time)
  let kappa := empiricalStackKappa (criticalLineParameter time)
  let C := empiricalCorrectedEnergyInverseCutoffConstant time
  have hrho : 0 < rho := by
    dsimp [rho]
    exact empiricalStackRho_pos
      (by norm_num [criticalLineParameter_re]) hsimple
  have hkappa : 0 < kappa := by
    dsimp [kappa]
    exact empiricalStackKappa_pos
      (by norm_num [criticalLineParameter_re]) hsimple
  have hratio : Tendsto (fun M : ℕ => C / (M : ℝ)) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat C
  have hsmall : ∀ᶠ M : ℕ in atTop, C / (M : ℝ) < rho / 2 :=
    hratio.eventually (Iio_mem_nhds (by linarith : 0 < rho / 2))
  filter_upwards [
    eventually_abs_finiteEmpiricalCorrectedReoptimizedEnergy_sub_model_le_inverseCutoff
      time hzero hsimple,
    hsmall] with M herror hMsmall
  let x := finiteEmpiricalPhaseProjection time M
  have hmodelFloor : rho ≤ rho + x ^ 2 / kappa := by
    exact le_add_of_nonneg_right
      (div_nonneg (sq_nonneg x) (le_of_lt hkappa))
  have hlower := (abs_le.mp herror).1
  dsimp [rho, kappa, C, x] at hMsmall hmodelFloor hlower ⊢
  linarith

/-- Fixed inverse-cutoff constant for the concrete local Schur coefficient. -/
def empiricalLocalCoercivityInverseCutoffConstant (time : ℝ) : ℝ :=
  let kappa := empiricalStackKappa (criticalLineParameter time)
  let kappaConstant := empiricalRawKappaInverseCutoffConstant time
  let curvatureConstant := empiricalSecondJetCurvatureInverseCutoffConstant time
  kappaConstant + curvatureConstant +
    curvatureConstant ^ 2 / (kappa / 4)

lemma empiricalFiniteRawResidualInverseCutoffConstant_nonneg_public
    (time : ℝ) :
    0 ≤ empiricalFiniteRawResidualInverseCutoffConstant time := by
  unfold empiricalFiniteRawResidualInverseCutoffConstant
  exact Finset.sum_nonneg fun camera _ => by
    unfold empiricalCameraRawResidualInverseCutoffConstant
      empiricalCameraBracketMajorantConstant
    positivity

lemma empiricalSecondJetCurvatureInverseCutoffConstant_nonneg
    (time : ℝ) :
    0 ≤ empiricalSecondJetCurvatureInverseCutoffConstant time := by
  unfold empiricalSecondJetCurvatureInverseCutoffConstant
  exact mul_nonneg
    (empiricalFiniteRawResidualInverseCutoffConstant_nonneg_public time)
    (Real.sqrt_nonneg _)

lemma empiricalLocalCoercivityInverseCutoffConstant_nonneg
    (time : ℝ)
    (hsimple : deriv genuineContinuation (criticalLineParameter time) ≠ 0) :
    0 ≤ empiricalLocalCoercivityInverseCutoffConstant time := by
  have hkappa :
      0 < empiricalStackKappa (criticalLineParameter time) :=
    empiricalStackKappa_pos
      (by norm_num [criticalLineParameter_re]) hsimple
  have hkerr := empiricalRawKappaInverseCutoffConstant_nonneg time
  have hcurv := empiricalSecondJetCurvatureInverseCutoffConstant_nonneg time
  dsimp [empiricalLocalCoercivityInverseCutoffConstant]
  exact add_nonneg (add_nonneg hkerr hcurv)
    (div_nonneg (sq_nonneg _) (by positivity))

/-- At every sufficiently large cutoff, the concrete local Schur coefficient
is within `C_c(t)/M` of the limiting clock Gram. -/
theorem eventually_abs_finiteEmpiricalLocalCoercivity_sub_model_le_inverseCutoff
    (time : ℝ)
    (hzero : genuineContinuation (criticalLineParameter time) = 0)
    (hsimple : deriv genuineContinuation (criticalLineParameter time) ≠ 0) :
    ∀ᶠ M : ℕ in atTop,
      |finiteEmpiricalLocalCoercivity M time -
        empiricalStackKappa (criticalLineParameter time)| ≤
      empiricalLocalCoercivityInverseCutoffConstant time / (M : ℝ) := by
  let kappa := empiricalStackKappa (criticalLineParameter time)
  let kappaConstant := empiricalRawKappaInverseCutoffConstant time
  let curvatureConstant := empiricalSecondJetCurvatureInverseCutoffConstant time
  have hkappa : 0 < kappa := by
    dsimp [kappa]
    exact empiricalStackKappa_pos
      (by norm_num [criticalLineParameter_re]) hsimple
  have hcurvNonneg : 0 ≤ curvatureConstant := by
    exact empiricalSecondJetCurvatureInverseCutoffConstant_nonneg time
  obtain ⟨threshold, hthreshold⟩ := exists_nat_ge (Real.exp 2)
  filter_upwards [
    eventually_finiteEmpiricalTemporalDenominator_ge_quarter
      time hzero hsimple,
    eventually_ge_atTop 1,
    eventually_ge_atTop threshold] with M hden hM hMthreshold
  have hMexp : Real.exp 2 ≤ (M : ℝ) :=
    hthreshold.trans (by exact_mod_cast hMthreshold)
  have hkappaError :=
    abs_finiteEmpiricalTransverseJet_kappa_sub_model_le_inverseCutoff
      M hM time hzero
  have ha :=
    abs_finiteEmpiricalTransverseJet_a_le_inverseCutoff
      M hMexp time hzero
  have hb :=
    abs_finiteEmpiricalTransverseJet_b_le_inverseCutoff
      M hMexp time hzero
  have hprimitive :=
    abs_transverseLocalCoercivity_sub_le_of_primitive_bounds
      (finiteEmpiricalTransverseJet M time) kappa
      (kappaConstant / (M : ℝ))
      (curvatureConstant / (M : ℝ))
      (curvatureConstant / (M : ℝ))
      (kappa / 4)
      (by positivity) hden hkappaError ha hb
  have hMreal : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hcurvDivNonneg : 0 ≤ curvatureConstant / (M : ℝ) :=
    div_nonneg hcurvNonneg (by positivity)
  have hcurvDivLe : curvatureConstant / (M : ℝ) ≤ curvatureConstant :=
    div_le_self hcurvNonneg hMreal
  have hsquare :
      (curvatureConstant / (M : ℝ)) ^ 2 ≤
        (curvatureConstant / (M : ℝ)) * curvatureConstant := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left hcurvDivLe hcurvDivNonneg
  have hthird :
      (curvatureConstant / (M : ℝ)) ^ 2 / (kappa / 4) ≤
        (curvatureConstant ^ 2 / (kappa / 4)) / (M : ℝ) := by
    calc
      (curvatureConstant / (M : ℝ)) ^ 2 / (kappa / 4) ≤
          ((curvatureConstant / (M : ℝ)) * curvatureConstant) /
            (kappa / 4) :=
        div_le_div_of_nonneg_right hsquare (by positivity)
      _ = (curvatureConstant ^ 2 / (kappa / 4)) / (M : ℝ) := by ring
  calc
    |finiteEmpiricalLocalCoercivity M time - kappa| ≤
        kappaConstant / (M : ℝ) + curvatureConstant / (M : ℝ) +
          (curvatureConstant / (M : ℝ)) ^ 2 / (kappa / 4) := hprimitive
    _ ≤ kappaConstant / (M : ℝ) + curvatureConstant / (M : ℝ) +
          (curvatureConstant ^ 2 / (kappa / 4)) / (M : ℝ) :=
      add_le_add le_rfl hthird
    _ = empiricalLocalCoercivityInverseCutoffConstant time / (M : ℝ) := by
      unfold empiricalLocalCoercivityInverseCutoffConstant
      dsimp [kappaConstant, curvatureConstant, kappa]
      ring

end

end GenuineZeroUniformAtlasEnergy

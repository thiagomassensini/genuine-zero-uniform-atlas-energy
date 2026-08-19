import GenuineZeroUniformAtlasEnergy.EmpiricalFiniteEnergyBound
import GenuineZeroUniformAtlasEnergy.EmpiricalFiniteFirstJetBound

/-!
# Finite Schur-coefficient bound from primitive jets

For the concrete finite transverse jet,

```math
kappa_M = ||chi'_M||^2,
 a_M = Re <chi_M, chi''_M>,
 b_M = -Im <chi_M, chi''_M>.
```

The first channel is controlled by the raw first-jet approximation.  The last
two channels are bounded by the product of the finite residual norm and a
supplied second-jet norm bound.  Feeding these estimates into the generic Schur
ledger reduces the finite local-coercivity obligation to one second-jet bound
and one positive temporal denominator floor.
-/

open scoped BigOperators

namespace GenuineZeroUniformAtlasEnergy

open CPFormal.Analytic.Cp

noncomputable section

/-- Euclidean bound for the unscaled six-camera finite residual. -/
def empiricalFiniteRawResidualStackBound
    (M : ℕ) (time : ℝ) : ℝ :=
  Real.sqrt
    (∑ camera : EmpiricalCamera,
      empiricalCameraCriticalTailBound camera M time ^ 2)

/-- At a Genuine critical zero, the raw finite residual stack has the expected
`M^(-3/2)` Euclidean bound. -/
theorem norm_finiteEmpiricalCameraEuclideanStack_critical_le
    (M : ℕ) (hM : 1 ≤ M) (time : ℝ)
    (hzero : genuineContinuation (criticalLineParameter time) = 0) :
    ‖finiteEmpiricalCameraEuclideanStack M (criticalLineParameter time)‖ ≤
      empiricalFiniteRawResidualStackBound M time := by
  rw [EuclideanSpace.norm_eq]
  unfold empiricalFiniteRawResidualStackBound
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro camera _hcamera
  have hcameraZero :
      empiricalCameraCharacteristic camera (criticalLineParameter time) = 0 :=
    empiricalCameraCharacteristic_zero_of_genuineContinuation_zero
      camera (criticalLineParameter_mem_genuineCriticalStrip time) hzero
  have hcomponent :=
    (finiteEmpiricalCamera_critical_cutoffTail_and_rate
      camera M hM time hcameraZero).2.1
  have hboundNonneg :
      0 ≤ empiricalCameraCriticalTailBound camera M time :=
    le_trans (norm_nonneg _) hcomponent
  have hmul :=
    mul_le_mul hcomponent hcomponent
      (norm_nonneg
        (finiteEmpiricalCameraCharacteristic camera M
          (criticalLineParameter time))) hboundNonneg
  simpa [pow_two] using hmul

/-- Raw first-jet Gram error. -/
def empiricalFiniteRawKappaErrorBound
    (M : ℕ) (time : ℝ) : ℝ :=
  empiricalFiniteFirstJetStackErrorBound M time *
    (empiricalFiniteFirstJetStackErrorBound M time +
      2 * ‖empiricalClockTangentVector (criticalLineParameter time)‖)

/-- The concrete finite transverse `kappa` differs from the infinite clock
Gram scalar by the raw first-jet error ledger. -/
theorem abs_finiteEmpiricalTransverseJet_kappa_sub_model_le
    (M : ℕ) (hM : 1 ≤ M) (time : ℝ)
    (hzero : genuineContinuation (criticalLineParameter time) = 0) :
    |(finiteEmpiricalTransverseJet M time).kappa -
        empiricalStackKappa (criticalLineParameter time)| ≤
      empiricalFiniteRawKappaErrorBound M time := by
  have hfirst :=
    norm_finiteEmpiricalCameraDerivativeStack_sub_clockTangent_critical_le
      M hM time hzero
  have hsq :=
    abs_norm_sq_sub_norm_sq_le_of_norm_sub_le
      (finiteEmpiricalCameraDerivativeStack M (criticalLineParameter time))
      (empiricalClockTangentVector (criticalLineParameter time))
      (empiricalFiniteFirstJetStackErrorBound M time) hfirst
  simpa [finiteEmpiricalTransverseJet, empiricalQuadraticTransverseJet,
    empiricalStackKappa, empiricalFiniteRawKappaErrorBound] using hsq

/-- The finite `a` channel is bounded by the raw residual norm times the
second-jet norm. -/
theorem abs_finiteEmpiricalTransverseJet_a_le
    (M : ℕ) (hM : 1 ≤ M) (time secondJetBound : ℝ)
    (hzero : genuineContinuation (criticalLineParameter time) = 0)
    (hsecond :
      ‖finiteEmpiricalCameraSecondDerivativeStack M
        (criticalLineParameter time)‖ ≤ secondJetBound) :
    |(finiteEmpiricalTransverseJet M time).a| ≤
      empiricalFiniteRawResidualStackBound M time * secondJetBound := by
  have hraw :=
    norm_finiteEmpiricalCameraEuclideanStack_critical_le M hM time hzero
  have hsecondNonneg : 0 ≤ secondJetBound :=
    le_trans (norm_nonneg _) hsecond
  change
    |(inner ℂ
      (finiteEmpiricalCameraEuclideanStack M (criticalLineParameter time))
      (finiteEmpiricalCameraSecondDerivativeStack M
        (criticalLineParameter time))).re| ≤
      empiricalFiniteRawResidualStackBound M time * secondJetBound
  calc
    |(inner ℂ
      (finiteEmpiricalCameraEuclideanStack M (criticalLineParameter time))
      (finiteEmpiricalCameraSecondDerivativeStack M
        (criticalLineParameter time))).re| ≤
      ‖inner ℂ
        (finiteEmpiricalCameraEuclideanStack M (criticalLineParameter time))
        (finiteEmpiricalCameraSecondDerivativeStack M
          (criticalLineParameter time))‖ :=
      Complex.abs_re_le_norm _
    _ ≤ ‖finiteEmpiricalCameraEuclideanStack M
          (criticalLineParameter time)‖ *
        ‖finiteEmpiricalCameraSecondDerivativeStack M
          (criticalLineParameter time)‖ :=
      norm_inner_le_norm _ _
    _ ≤ empiricalFiniteRawResidualStackBound M time * secondJetBound :=
      mul_le_mul hraw hsecond (norm_nonneg _) (by
        exact le_trans (norm_nonneg _) hraw)

/-- The finite `b` channel obeys the same primitive product bound. -/
theorem abs_finiteEmpiricalTransverseJet_b_le
    (M : ℕ) (hM : 1 ≤ M) (time secondJetBound : ℝ)
    (hzero : genuineContinuation (criticalLineParameter time) = 0)
    (hsecond :
      ‖finiteEmpiricalCameraSecondDerivativeStack M
        (criticalLineParameter time)‖ ≤ secondJetBound) :
    |(finiteEmpiricalTransverseJet M time).b| ≤
      empiricalFiniteRawResidualStackBound M time * secondJetBound := by
  have hraw :=
    norm_finiteEmpiricalCameraEuclideanStack_critical_le M hM time hzero
  have hsecondNonneg : 0 ≤ secondJetBound :=
    le_trans (norm_nonneg _) hsecond
  change
    |-((inner ℂ
      (finiteEmpiricalCameraEuclideanStack M (criticalLineParameter time))
      (finiteEmpiricalCameraSecondDerivativeStack M
        (criticalLineParameter time))).im)| ≤
      empiricalFiniteRawResidualStackBound M time * secondJetBound
  rw [abs_neg]
  calc
    |(inner ℂ
      (finiteEmpiricalCameraEuclideanStack M (criticalLineParameter time))
      (finiteEmpiricalCameraSecondDerivativeStack M
        (criticalLineParameter time))).im| ≤
      ‖inner ℂ
        (finiteEmpiricalCameraEuclideanStack M (criticalLineParameter time))
        (finiteEmpiricalCameraSecondDerivativeStack M
          (criticalLineParameter time))‖ :=
      Complex.abs_im_le_norm _
    _ ≤ ‖finiteEmpiricalCameraEuclideanStack M
          (criticalLineParameter time)‖ *
        ‖finiteEmpiricalCameraSecondDerivativeStack M
          (criticalLineParameter time)‖ :=
      norm_inner_le_norm _ _
    _ ≤ empiricalFiniteRawResidualStackBound M time * secondJetBound :=
      mul_le_mul hraw hsecond (norm_nonneg _) (by
        exact le_trans (norm_nonneg _) hraw)

/-- Explicit finite Schur-coefficient error from a supplied second-jet bound
and temporal denominator floor. -/
def empiricalFiniteLocalCoercivityErrorBound
    (M : ℕ) (time secondJetBound denominatorFloor : ℝ) : ℝ :=
  empiricalFiniteRawKappaErrorBound M time +
    empiricalFiniteRawResidualStackBound M time * secondJetBound +
    (empiricalFiniteRawResidualStackBound M time * secondJetBound) ^ 2 /
      denominatorFloor

/-- Concrete reduction of the finite local-coercivity obligation. -/
theorem abs_finiteEmpiricalLocalCoercivity_sub_model_le
    (M : ℕ) (hM : 1 ≤ M)
    (time secondJetBound denominatorFloor : ℝ)
    (hzero : genuineContinuation (criticalLineParameter time) = 0)
    (hsecond :
      ‖finiteEmpiricalCameraSecondDerivativeStack M
        (criticalLineParameter time)‖ ≤ secondJetBound)
    (hdenominatorFloorPos : 0 < denominatorFloor)
    (hdenominatorFloor :
      denominatorFloor ≤
        |(finiteEmpiricalTransverseJet M time).kappa -
          (finiteEmpiricalTransverseJet M time).a|) :
    |finiteEmpiricalLocalCoercivity M time -
        empiricalStackKappa (criticalLineParameter time)| ≤
      empiricalFiniteLocalCoercivityErrorBound
        M time secondJetBound denominatorFloor := by
  have hkappa :=
    abs_finiteEmpiricalTransverseJet_kappa_sub_model_le
      M hM time hzero
  have ha :=
    abs_finiteEmpiricalTransverseJet_a_le
      M hM time secondJetBound hzero hsecond
  have hb :=
    abs_finiteEmpiricalTransverseJet_b_le
      M hM time secondJetBound hzero hsecond
  exact
    abs_transverseLocalCoercivity_sub_le_of_primitive_bounds
      (finiteEmpiricalTransverseJet M time)
      (empiricalStackKappa (criticalLineParameter time))
      (empiricalFiniteRawKappaErrorBound M time)
      (empiricalFiniteRawResidualStackBound M time * secondJetBound)
      (empiricalFiniteRawResidualStackBound M time * secondJetBound)
      denominatorFloor
      hdenominatorFloorPos hdenominatorFloor hkappa ha hb

end

end GenuineZeroUniformAtlasEnergy

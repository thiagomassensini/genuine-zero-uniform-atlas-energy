import GenuineZeroUniformAtlasEnergy.EmpiricalCorrectedJetBound
import GenuineZeroUniformAtlasEnergy.EmpiricalTransverseDataCrosswalk

/-!
# Concrete finite empirical transverse data

The microscopic transfer theorems are stated for three scalar sequences
`(E_M, g_M, c_M)`.  This module identifies those sequences with concrete
objects built from the finite six-camera characteristic:

* the resonant residual, normalized by the critical `M^(3/2)` amplitude and
  with the logarithmic cutoff phase removed;
* the finite first complex-derivative stack;
* the finite second complex-derivative stack;
* the raw finite transverse Hessian jet;
* the clock-reoptimized residual energy, radial gradient, Schur coefficient,
  and final microscopic coefficient.

No asymptotic estimate is hidden in the definitions.  The final theorem in
this file specializes the primitive perturbation capstone to these concrete
sequences and displays exactly which quantitative bounds remain to be fed by
the cutoff-tail jet estimates.
-/

open Filter
open scoped BigOperators ComplexConjugate InnerProductSpace

namespace GenuineZeroUniformAtlasEnergy

open CPFormal.Analytic.Cp

noncomputable section

/-- The finite six-camera characteristic in its Euclidean `L²` packaging. -/
def finiteEmpiricalCameraEuclideanStack
    (M : ℕ) (s : ℂ) : EmpiricalCameraStack :=
  WithLp.toLp 2 fun camera =>
    finiteEmpiricalCameraCharacteristic camera M s

@[simp] theorem finiteEmpiricalCameraEuclideanStack_apply
    (M : ℕ) (s : ℂ) (camera : EmpiricalCamera) :
    finiteEmpiricalCameraEuclideanStack M s camera =
      finiteEmpiricalCameraCharacteristic camera M s := by
  rfl

/-- The naturally scaled finite residual stack `M^(s+1) chi_M(s)`. -/
def empiricalScaledFiniteResidualStack
    (M : ℕ) (s : ℂ) : EmpiricalCameraStack :=
  WithLp.toLp 2 fun camera =>
    empiricalScaledFiniteCameraResidual camera M s

@[simp] theorem empiricalScaledFiniteResidualStack_apply
    (M : ℕ) (s : ℂ) (camera : EmpiricalCamera) :
    empiricalScaledFiniteResidualStack M s camera =
      empiricalScaledFiniteCameraResidual camera M s := by
  rfl

/-- Unit scalar removing the logarithmic cutoff phase on the critical line. -/
def empiricalCutoffBackPhase (time : ℝ) (M : ℕ) : ℂ :=
  Complex.exp (-((empiricalCutoffPhase time M : ℂ) * Complex.I))

/-- Physical critical normalization of the finite residual.  Since
`M^(s+1)=M^(3/2) exp(i t log M)` at `s=1/2+it`, this is the real-amplitude
normalization `M^(3/2) chi_M` written using the already exact analytic scale. -/
def empiricalPhaseNormalizedFiniteResidualStack
    (M : ℕ) (time : ℝ) : EmpiricalCameraStack :=
  empiricalCutoffBackPhase time M •
    empiricalScaledFiniteResidualStack M (criticalLineParameter time)

/-- Second complex derivative stack of the finite six-camera characteristic. -/
def finiteEmpiricalCameraSecondDerivativeStack
    (M : ℕ) (s : ℂ) : EmpiricalCameraStack :=
  WithLp.toLp 2 fun camera =>
    iteratedDeriv 2 (finiteEmpiricalCameraCharacteristic camera M) s

@[simp] theorem finiteEmpiricalCameraSecondDerivativeStack_apply
    (M : ℕ) (s : ℂ) (camera : EmpiricalCamera) :
    finiteEmpiricalCameraSecondDerivativeStack M s camera =
      iteratedDeriv 2 (finiteEmpiricalCameraCharacteristic camera M) s := by
  rfl

/-- Clock Gram scalar of a supplied first-jet stack. -/
def empiricalQuadraticClockKappa
    (firstJet : EmpiricalCameraStack) : ℝ :=
  ‖firstJet‖ ^ 2

/-- Complex pairing between a normalized residual and its first jet. -/
def empiricalQuadraticClockPairing
    (residual firstJet : EmpiricalCameraStack) : ℂ :=
  inner ℂ residual firstJet

/-- Residual energy after minimizing the first-order clock displacement. -/
def empiricalQuadraticReoptimizedEnergy
    (residual firstJet : EmpiricalCameraStack) : ℝ :=
  ‖residual‖ ^ 2 -
    (empiricalQuadraticClockPairing residual firstJet).im ^ 2 /
      empiricalQuadraticClockKappa firstJet

/-- Radial gradient left after the orthogonal clock displacement is removed. -/
def empiricalQuadraticRadialGradient
    (residual firstJet : EmpiricalCameraStack) : ℝ :=
  2 * (empiricalQuadraticClockPairing residual firstJet).re

/-- Concrete aggregate transverse jet of a finite empirical stack.  The sign
in `b` is the complex-coordinate form of pairing with the real quarter-turn:
`Re <u, i w> = -Im <u,w>`. -/
def empiricalQuadraticTransverseJet
    (rawResidual firstJet secondJet : EmpiricalCameraStack) : TransverseJet where
  kappa := ‖firstJet‖ ^ 2
  a := (inner ℂ rawResidual secondJet).re
  b := -(inner ℂ rawResidual secondJet).im

/-- Concrete finite clock-reoptimized energy `E_M`. -/
def finiteEmpiricalReoptimizedEnergy (M : ℕ) (time : ℝ) : ℝ :=
  empiricalQuadraticReoptimizedEnergy
    (empiricalPhaseNormalizedFiniteResidualStack M time)
    (finiteEmpiricalCameraDerivativeStack M (criticalLineParameter time))

/-- Concrete finite radial gradient `g_M`. -/
def finiteEmpiricalRadialGradient (M : ℕ) (time : ℝ) : ℝ :=
  empiricalQuadraticRadialGradient
    (empiricalPhaseNormalizedFiniteResidualStack M time)
    (finiteEmpiricalCameraDerivativeStack M (criticalLineParameter time))

/-- Concrete raw finite transverse Hessian jet. -/
def finiteEmpiricalTransverseJet (M : ℕ) (time : ℝ) : TransverseJet :=
  empiricalQuadraticTransverseJet
    (finiteEmpiricalCameraEuclideanStack M (criticalLineParameter time))
    (finiteEmpiricalCameraDerivativeStack M (criticalLineParameter time))
    (finiteEmpiricalCameraSecondDerivativeStack M
      (criticalLineParameter time))

/-- Concrete finite Schur coefficient `c_M`. -/
def finiteEmpiricalLocalCoercivity (M : ℕ) (time : ℝ) : ℝ :=
  (finiteEmpiricalTransverseJet M time).localCoercivity

/-- Final finite microscopic coefficient after both the clock direction and
the nonzero residual value have been reoptimized. -/
def finiteEmpiricalMicroscopicCoercivity (M : ℕ) (time : ℝ) : ℝ :=
  quadraticMicroscopicCoercivity
    (finiteEmpiricalReoptimizedEnergy M time)
    (finiteEmpiricalRadialGradient M time)
    (finiteEmpiricalLocalCoercivity M time)

/-- Exact logarithmic phase sequence used by the finite cutoff data. -/
def finiteEmpiricalPhaseProjection (time : ℝ) (M : ℕ) : ℝ :=
  empiricalStackPhaseProjection (criticalLineParameter time)
    (empiricalCutoffPhase time M)

/-- Concrete specialization of the primitive microscopic capstone.  The model
projection bound, model-gradient bound, and model-energy denominator floor are
already discharged by the phase geometry.  What remains visible is precisely:

* a positive floor for the finite reoptimized energy;
* `O(1/M)` approximation of the finite Schur coefficient;
* `O(1/M)` approximation of the finite radial gradient;
* one uniform bound for the corresponding gradient sum;
* `O(1/M)` approximation of the finite reoptimized energy.
-/
theorem eventually_positive_finiteEmpiricalMicroscopicCoercivity_of_primitive_bounds
    (time : ℝ)
    (hsimple :
      deriv genuineContinuation (criticalLineParameter time) ≠ 0)
    (curvatureConstant gradientDifferenceConstant energyDifferenceConstant
      gradientSumBound energyFloor : ℝ)
    (henergyFloorPos : 0 < energyFloor)
    (henergyFloor : ∀ M : ℕ, 1 ≤ M →
      energyFloor ≤ |finiteEmpiricalReoptimizedEnergy M time|)
    (hcurvature : ∀ M : ℕ, 1 ≤ M →
      |finiteEmpiricalLocalCoercivity M time -
          empiricalStackKappa (criticalLineParameter time)| ≤
        curvatureConstant / (M : ℝ))
    (hgradientDifference : ∀ M : ℕ, 1 ≤ M →
      |finiteEmpiricalRadialGradient M time -
          2 * finiteEmpiricalPhaseProjection time M| ≤
        gradientDifferenceConstant / (M : ℝ))
    (hgradientSum : ∀ M : ℕ, 1 ≤ M →
      |finiteEmpiricalRadialGradient M time +
          2 * finiteEmpiricalPhaseProjection time M| ≤
        gradientSumBound)
    (henergyDifference : ∀ M : ℕ, 1 ≤ M →
      |(empiricalStackRho (criticalLineParameter time) +
          finiteEmpiricalPhaseProjection time M ^ 2 /
            empiricalStackKappa (criticalLineParameter time)) -
        finiteEmpiricalReoptimizedEnergy M time| ≤
          energyDifferenceConstant / (M : ℝ)) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ M : ℕ in atTop,
        c ≤ finiteEmpiricalMicroscopicCoercivity M time := by
  have hs :
      (criticalLineParameter time).re = (1 : ℝ) / 2 := by
    norm_num [criticalLineParameter_re]
  have hadmissible :
      (empiricalStackPhaseProjectionData
        (criticalLineParameter time)).IsAdmissible :=
    empiricalStackPhaseProjectionData_isAdmissible hs hsimple
  have hrho :
      0 < empiricalStackRho (criticalLineParameter time) :=
    empiricalStackRho_pos hs hsimple
  have hmain :=
    PhaseProjectionData.eventually_positive_quadraticMicroscopicCoercivity_of_primitive_bounds
      (empiricalStackPhaseProjectionData (criticalLineParameter time))
      hadmissible
      (fun M => finiteEmpiricalReoptimizedEnergy M time)
      (fun M => finiteEmpiricalRadialGradient M time)
      (fun M => finiteEmpiricalLocalCoercivity M time)
      (finiteEmpiricalPhaseProjection time)
      curvatureConstant gradientDifferenceConstant energyDifferenceConstant
      gradientSumBound
      (2 * ‖empiricalStackPairing (criticalLineParameter time)‖)
      energyFloor
      (empiricalStackRho (criticalLineParameter time))
      henergyFloorPos hrho
      (fun M =>
        empiricalStackPhaseProjection_sq_le_alphaSq
          (criticalLineParameter time) (empiricalCutoffPhase time M))
      henergyFloor
      (fun M => by
        simpa [finiteEmpiricalPhaseProjection,
          empiricalStackPhaseProjectionData] using
          empiricalStackRho_le_abs_phaseDenominator
            hs hsimple (empiricalCutoffPhase time M))
      hcurvature hgradientDifference hgradientSum
      (fun M => by
        simpa [finiteEmpiricalPhaseProjection] using
          abs_two_empiricalStackPhaseProjection_le
            (criticalLineParameter time) (empiricalCutoffPhase time M))
      henergyDifference
  simpa [finiteEmpiricalMicroscopicCoercivity] using hmain

end

end GenuineZeroUniformAtlasEnergy

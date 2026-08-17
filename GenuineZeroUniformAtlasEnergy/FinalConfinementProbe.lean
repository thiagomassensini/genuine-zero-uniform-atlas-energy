import GenuineZeroUniformAtlasEnergy.EmpiricalLimitConfinement
import CPFormal.Analytic.CpGenuineGreenKernelInclusion
import CPFormal.Analytic.CpGenuinePrimeCarryDefectUniformBound
import CPFormal.Analytic.CpGenuineGprePrimeVerticalTraceWeightedBessel

/-!
# Final Genuine-confinement frontier audit

This module records the exact logical frontier exposed by the unconditional
confinement probe. It adds no numerical premise, local trust escape, or zero
predicate containing the desired conclusion.

The scalar confinement statement is compared with three independently built
CPFormal formulations: Green-kernel inclusion, existence of one global
centered-carry readout state, and the prime half-amplitude smoothing property.
The existing v0.11 empirical-energy bridge is also recorded as a sufficient
route: an eventual positive strip coercivity certificate implies the scalar
confinement statement.
-/

open Filter Set

namespace GenuineZeroUniformAtlasEnergy

open CPFormal.Analytic.Cp

noncomputable section

/-- The scalar endpoint of the research line: every raw Genuine zero in the
open strip lies on the carry half-abscissa. -/
def FinalGenuineZeroConfinement : Prop :=
  ∀ {s : ℂ}, s ∈ genuineCriticalStrip →
    genuineContinuation s = 0 →
      s.re = (1 : ℝ) / 2

/-- Scalar confinement is exactly the strong off-critical nonvanishing
formulation already isolated in CPFormal. -/
theorem finalGenuineZeroConfinement_iff_strongNonvanishing :
    FinalGenuineZeroConfinement ↔ GenuineStrongNonvanishingInStrip := by
  constructor
  · intro hconf s hs hoff hzero
    exact hoff (hconf hs hzero)
  · intro hstrong s hs hzero
    by_contra hoff
    exact (hstrong hs hoff) hzero

/-- The Green-kernel route has exactly the strength of scalar confinement. -/
theorem finalGenuineZeroConfinement_iff_greenKernelInclusion :
    FinalGenuineZeroConfinement ↔
      GenuineKernelIncludedInGreenLimitKernel 3 5 := by
  exact finalGenuineZeroConfinement_iff_strongNonvanishing.trans
    (genuineKernelIncludedInGreenLimitKernel_iff_strongNonvanishing
      3 5 (by norm_num) (by norm_num)).symm

/-- The global centered-carry realization route has exactly the same final
logical strength. -/
theorem finalGenuineZeroConfinement_iff_globalCenteredCarryReadoutState :
    FinalGenuineZeroConfinement ↔
      GenuineZerosAdmitGlobalCenteredCarryReadoutState := by
  exact finalGenuineZeroConfinement_iff_strongNonvanishing.trans
    genuineZerosAdmitGlobalCenteredCarryReadoutState_iff_strongNonvanishing.symm

/-- The missing prime half-amplitude smoothing gain is likewise exactly the
scalar confinement statement, not a weaker lemma that can be imported for
free. -/
theorem finalGenuineZeroConfinement_iff_primeHalfAmplitudeSmoothing :
    FinalGenuineZeroConfinement ↔
      GenuineZeroProvidesPrimeHalfAmplitudeSmoothing := by
  exact finalGenuineZeroConfinement_iff_strongNonvanishing.trans
    genuineZeroProvidesPrimeHalfAmplitudeSmoothing_iff_strongNonvanishing.symm

/-- The single certificate shape consumed by the v0.11 concrete empirical
limit bridge. -/
def HasEventualPositiveEmpiricalStripCoercivity : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ᶠ M : ℕ in atTop,
      IsTransverselyCoerciveOn empiricalCriticalStripPlane
        (finiteEmpiricalCollectiveRawEnergyPlane M) c

/-- The already-proved v0.11 limit bridge turns the eventual positive finite
certificate into unconditional scalar confinement. -/
theorem finalGenuineZeroConfinement_of_eventualPositiveEmpiricalStripCoercivity
    (hcert : HasEventualPositiveEmpiricalStripCoercivity) :
    FinalGenuineZeroConfinement := by
  rcases hcert with ⟨c, hc, hcoercive⟩
  intro s hs hzero
  exact genuineZero_forces_re_eq_half_of_eventual_empiricalStripCoercivity
    (c := c) (sigma := s.re) (time := s.im) hc hcoercive
    (by simpa [empiricalPlaneParameter] using hs)
    (by simpa [empiricalPlaneParameter] using hzero)

/-- Consequently the empirical positive-certificate route is a sufficient
construction of the strong nonvanishing property. No converse is asserted:
the uniform quadratic certificate is intentionally kept stronger than the
bare zero-location statement. -/
theorem strongNonvanishing_of_eventualPositiveEmpiricalStripCoercivity
    (hcert : HasEventualPositiveEmpiricalStripCoercivity) :
    GenuineStrongNonvanishingInStrip :=
  finalGenuineZeroConfinement_iff_strongNonvanishing.mp
    (finalGenuineZeroConfinement_of_eventualPositiveEmpiricalStripCoercivity
      hcert)

end

end GenuineZeroUniformAtlasEnergy

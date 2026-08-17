import GenuineZeroUniformAtlasEnergy.EmpiricalLimitConfinement
import CPFormal.Analytic.CpGenuineGreenKernelInclusion
import CPFormal.Analytic.CpGenuinePrimeCarryDefectUniformBound
import CPFormal.Analytic.CpGenuineGprePrimeVerticalTraceWeightedBessel
import CPFormal.Analytic.CpFiniteGenuineOneSidedGreenBudget

/-!
# Final Genuine-confinement frontier audit

This module records the exact logical frontier exposed by the unconditional
confinement probe. It adds no numerical premise, local trust escape, or zero
predicate containing the desired conclusion.

The scalar confinement statement is compared with independently built
CPFormal formulations: Green-kernel inclusion, existence of one global
centered-carry readout state, prime half-amplitude smoothing, and the minimal
one-sided angular Green bridge. The existing v0.11 empirical-energy bridge is
also recorded as a sufficient route.
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

/-- At a Genuine zero, the full nonradial angular correction has an explicit
limit: it tends to the negative infinite reflected Green pairing.  Thus scalar
port decay does not make this provenance-sensitive term disappear. -/
theorem angularGreenCorrection_tendsto_neg_infinitePairing_of_genuine_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    Tendsto
      (fun M : ℕ => finiteCanonicalAngularGreenCorrection M s)
      atTop (nhds (-infiniteReflectedGradientPairing s)) := by
  have hbudget :=
    finiteCanonicalAngularGreenBudget_tendsto_zero_of_genuine_zero hs hzero
  have hthree : Tendsto (fun M : ℕ => 3 * M) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with M hM
    omega
  have hgreen :=
    (finiteReflectedGradientPairing_tendsto_infinite hs).comp hthree
  have hsub := hbudget.sub hgreen
  have hfun :
      (fun M : ℕ => finiteCanonicalAngularGreenCorrection M s) =
        (fun M : ℕ =>
          (finiteReflectedGradientPairing (3 * M) s +
              finiteCanonicalAngularGreenCorrection M s) -
            finiteReflectedGradientPairing (3 * M) s) := by
    funext M
    ring
  rw [hfun]
  simpa using hsub

/-- Pointwise exact frontier: after a Genuine zero has killed the scalar port,
the radially weighted nonradial correction closes exactly on the half-line. -/
theorem scaledAngularGreenCorrection_closes_iff_re_eq_half
    {p : ℕ} (hp : Nat.Prime p)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    Tendsto
        (fun M : ℕ =>
          ((cpRadialDifference p (criticalDisplacement s.re) : ℝ) : ℂ) *
            finiteCanonicalAngularGreenCorrection M s)
        atTop (nhds 0) ↔
      s.re = (1 : ℝ) / 2 := by
  constructor
  · intro hclose
    have hcritical :=
      criticalDisplacement_eq_zero_of_genuine_zero_of_scaled_correction
        hp hzero hs hclose
    unfold criticalDisplacement at hcritical
    linarith
  · intro hre
    have hradial :
        cpRadialDifference p (criticalDisplacement s.re) = 0 := by
      simp [criticalDisplacement, hre, cpRadialDifference]
    simp [hradial]

/-- The minimal one-sided Green bridge is not a weaker hidden gate: globally
it is exactly scalar Genuine confinement. -/
theorem finalGenuineZeroConfinement_iff_oneSidedAngularGreenBridge_three :
    FinalGenuineZeroConfinement ↔ GenuineOneSidedAngularGreenBridge 3 := by
  constructor
  · intro hconf
    refine ⟨?_⟩
    intro s hzero hs
    have hre : s.re = (1 : ℝ) / 2 := hconf hs hzero
    have hradial :
        cpRadialDifference 3 (criticalDisplacement s.re) = 0 := by
      simp [criticalDisplacement, hre, cpRadialDifference]
    simp [hradial]
  · intro bridge s hs hzero
    have hcritical :=
      bridge.criticalDisplacement_eq_zero (by norm_num) hzero hs
    unfold criticalDisplacement at hcritical
    linarith

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

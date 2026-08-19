import GenuineZeroUniformAtlasEnergy.EmpiricalLimitConfinement
import GenuineZeroUniformAtlasEnergy.EmpiricalStackProjection
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

/-- A strictly positive phase floor is already enough for the final frontier:
there is no need to certify the historical target `4`.  Once the microscopic
coefficient is within `C/M` of the phase model, half of the phase floor is an
eventual positive lower bound. -/
theorem eventually_positive_microscopicCoercivity_of_inv_error
    (d : PhaseProjectionData) (h : d.IsAdmissible)
    (phaseProjection cMicro : ℕ → ℝ) (C : ℝ)
    (hx : ∀ M : ℕ, (phaseProjection M) ^ 2 ≤ d.alphaSq)
    (happrox : ∀ M : ℕ, 1 ≤ M →
      |cMicro M - d.phaseCoercivity (phaseProjection M)| ≤ C / (M : ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ M : ℕ in atTop, c ≤ cMicro M := by
  have hfloor : 0 < d.phaseFloor := d.phaseFloor_pos h
  refine ⟨d.phaseFloor / 2, by linarith, ?_⟩
  exact d.eventually_microscopicCoercivity_lower_bound_of_inv_error h
    phaseProjection cMicro C (d.phaseFloor / 2) hx happrox (by linarith)

/-- Concrete empirical specialization of the previous theorem.  At a critical
simple point the symbolic six-camera phase floor is strictly positive, so an
explicit `C/M` approximation of the reoptimized microscopic coefficient gives
some eventual positive coefficient without importing a numerical zero height
or the exploratory `> 4` threshold. -/
theorem eventually_positive_empiricalStack_microscopicCoercivity_of_inv_error
    {s : ℂ} (hs : s.re = (1 : ℝ) / 2)
    (hsimple : deriv genuineContinuation s ≠ 0)
    (theta cMicro : ℕ → ℝ) (C : ℝ)
    (happrox : ∀ M : ℕ, 1 ≤ M →
      |cMicro M -
          (empiricalStackPhaseProjectionData s).phaseCoercivity
            (empiricalStackPhaseProjection s (theta M))| ≤ C / (M : ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ M : ℕ in atTop, c ≤ cMicro M := by
  apply eventually_positive_microscopicCoercivity_of_inv_error
    (d := empiricalStackPhaseProjectionData s)
    (h := empiricalStackPhaseProjectionData_isAdmissible hs hsimple)
    (phaseProjection := fun M => empiricalStackPhaseProjection s (theta M))
    (cMicro := cMicro) (C := C)
  · intro M
    exact empiricalStackPhaseProjection_sq_le_alphaSq s (theta M)
  · exact happrox

/-- Exact regional stitching lemma.  If a microscopic region and its
complementary region cover the critical strip and each has an eventual
positive quadratic coercivity constant, their minimum is a single eventual
positive strip-wide constant. -/
theorem hasEventualPositiveEmpiricalStripCoercivity_of_cover
    {microscopicRegion complementRegion : Set (ℝ × ℝ)}
    {cMicroscopic cComplement : ℝ}
    (hcMicroscopic : 0 < cMicroscopic)
    (hcComplement : 0 < cComplement)
    (hcover : empiricalCriticalStripPlane ⊆
      microscopicRegion ∪ complementRegion)
    (hmicroscopic : ∀ᶠ M : ℕ in atTop,
      IsTransverselyCoerciveOn microscopicRegion
        (finiteEmpiricalCollectiveRawEnergyPlane M) cMicroscopic)
    (hcomplement : ∀ᶠ M : ℕ in atTop,
      IsTransverselyCoerciveOn complementRegion
        (finiteEmpiricalCollectiveRawEnergyPlane M) cComplement) :
    HasEventualPositiveEmpiricalStripCoercivity := by
  refine ⟨min cMicroscopic cComplement,
    lt_min hcMicroscopic hcComplement, ?_⟩
  filter_upwards [hmicroscopic, hcomplement] with M hMicro hComp
  intro point hpoint
  rcases hcover hpoint with hpointMicro | hpointComp
  · have hbound := hMicro point hpointMicro
    have hsq : 0 ≤ (point.1 - (1 : ℝ) / 2) ^ 2 := sq_nonneg _
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _) hsq).trans hbound
  · have hbound := hComp point hpointComp
    have hsq : 0 ≤ (point.1 - (1 : ℝ) / 2) ^ 2 := sq_nonneg _
    exact (mul_le_mul_of_nonneg_right (min_le_right _ _) hsq).trans hbound

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

/-- Final two-region stitching capstone.  The microscopic lower bound and the
compact-complement lower bound are the only quantitative inputs; once their
regions cover the empirical critical strip, the existing limit bridge gives
scalar Genuine confinement. -/
theorem finalGenuineZeroConfinement_of_empiricalCoercivity_cover
    {microscopicRegion complementRegion : Set (ℝ × ℝ)}
    {cMicroscopic cComplement : ℝ}
    (hcMicroscopic : 0 < cMicroscopic)
    (hcComplement : 0 < cComplement)
    (hcover : empiricalCriticalStripPlane ⊆
      microscopicRegion ∪ complementRegion)
    (hmicroscopic : ∀ᶠ M : ℕ in atTop,
      IsTransverselyCoerciveOn microscopicRegion
        (finiteEmpiricalCollectiveRawEnergyPlane M) cMicroscopic)
    (hcomplement : ∀ᶠ M : ℕ in atTop,
      IsTransverselyCoerciveOn complementRegion
        (finiteEmpiricalCollectiveRawEnergyPlane M) cComplement) :
    FinalGenuineZeroConfinement := by
  apply finalGenuineZeroConfinement_of_eventualPositiveEmpiricalStripCoercivity
  exact hasEventualPositiveEmpiricalStripCoercivity_of_cover
    hcMicroscopic hcComplement hcover hmicroscopic hcomplement

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

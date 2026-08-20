import GenuineZeroUniformAtlasEnergy.GenuineZeroMultiplicity
import Mathlib.Analysis.Complex.Norm

/-!
# Arbitrary-multiplicity near-axis certificate

The quadratic transverse sector is necessarily restricted to simple Genuine
zeros.  This module records the complementary qualitative fact that survives
at every finite multiplicity: analyticity and a nonzero leading jet isolate the
zero, hence give a punctured horizontal window on which the Genuine
continuation does not vanish.

The construction is analytic, not a finite-height verification.  It packages
one radius around every critical-line Genuine zero carrying finite
multiplicity data.  No numerical zero list, zero height, or simplicity
assumption is imported.
-/

open Filter Set
open scoped Topology

namespace GenuineZeroUniformAtlasEnergy

open CPFormal.Analytic.Cp

noncomputable section

/-- A critical-line Genuine zero equipped with some positive finite analytic
multiplicity. -/
def IsCriticalGenuineZeroOfFiniteMultiplicity (rho : ℂ) : Prop :=
  ∃ order : ℕ,
    IsGenuineZeroOfMultiplicity order rho ∧
      rho.re = (1 : ℝ) / 2

theorem IsCriticalGenuineZeroOfFiniteMultiplicity.re_eq_half
    {rho : ℂ} (h : IsCriticalGenuineZeroOfFiniteMultiplicity rho) :
    rho.re = (1 : ℝ) / 2 := by
  rcases h with ⟨_order, _hroot, hrho⟩
  exact hrho

/-- Punctured horizontal window at the fixed height of a critical-line
center. -/
def genuineTransversalWindow (rho : ℂ) (radius : ℝ) : Set ℂ :=
  {s : ℂ |
    s.im = rho.im ∧
      0 < |s.re - rho.re| ∧
        |s.re - rho.re| < radius}

/-- Union of the punctured horizontal windows selected around all
critical-line finite-multiplicity Genuine zeros. -/
def genuineNearAxisRegion (radius : ℂ → ℝ) : Set ℂ :=
  {s : ℂ |
    ∃ rho : ℂ,
      IsCriticalGenuineZeroOfFiniteMultiplicity rho ∧
        s ∈ genuineTransversalWindow rho (radius rho)}

/-- Analytic near-axis certificate valid uniformly in the logical sense over
all finite multiplicities.  The radii may depend on the center; no unjustified
global quantitative lower radius is asserted. -/
structure GenuineNearAxisMultiplicityCertificate where
  radius : ℂ → ℝ
  radius_pos :
    ∀ rho, IsCriticalGenuineZeroOfFiniteMultiplicity rho → 0 < radius rho
  radius_le_half :
    ∀ rho, IsCriticalGenuineZeroOfFiniteMultiplicity rho →
      radius rho ≤ (1 : ℝ) / 2
  nonvanishing :
    ∀ {rho s : ℂ},
      IsCriticalGenuineZeroOfFiniteMultiplicity rho →
        s ∈ genuineTransversalWindow rho (radius rho) →
          genuineContinuation s ≠ 0

/-- A nonzero leading analytic jet prevents the Genuine continuation from
vanishing identically on a neighborhood. -/
theorem IsGenuineZeroOfMultiplicity.not_eventually_zero
    {order : ℕ} {rho : ℂ}
    (hroot : IsGenuineZeroOfMultiplicity order rho) :
    ¬ ∀ᶠ z in 𝓝 rho, genuineContinuation z = 0 := by
  intro hzero
  have heq :
      genuineContinuation =ᶠ[𝓝 rho] fun _ : ℂ => (0 : ℂ) := by
    simpa [Filter.EventuallyEq] using hzero
  have hderiv :
      iteratedDeriv order genuineContinuation rho =
        iteratedDeriv order (fun _ : ℂ => (0 : ℂ)) rho := by
    simpa using heq.iteratedDeriv_eq order
  exact hroot.leading_iteratedDeriv_ne_zero (by simpa using hderiv)

/-- Every finite-multiplicity Genuine zero is isolated in a punctured
neighborhood. -/
theorem IsGenuineZeroOfMultiplicity.eventually_ne_zero
    {order : ℕ} {rho : ℂ}
    (hroot : IsGenuineZeroOfMultiplicity order rho) :
    ∀ᶠ z in 𝓝[≠] rho, genuineContinuation z ≠ 0 := by
  exact
    (hroot.analyticAt.eventually_eq_zero_or_eventually_ne_zero).resolve_left
      hroot.not_eventually_zero

/-- A punctured-neighborhood nonvanishing statement contains a horizontal
window with radius at most one half. -/
theorem exists_genuineTransversalRadius_of_eventually_ne_zero
    {F : ℂ → ℂ} {rho : ℂ}
    (hEventually : ∀ᶠ z in 𝓝[≠] rho, F z ≠ 0) :
    ∃ r : ℝ,
      0 < r ∧
      r ≤ (1 : ℝ) / 2 ∧
      ∀ ⦃s : ℂ⦄,
        s ∈ genuineTransversalWindow rho r → F s ≠ 0 := by
  let t : Set ℂ := {z : ℂ | F z ≠ 0}
  rcases (mem_nhdsWithin.mp hEventually) with ⟨u, huOpen, hrhoU, huSub⟩
  rcases Metric.mem_nhds_iff.mp (huOpen.mem_nhds hrhoU) with
    ⟨epsilon, hepsilonPos, hepsilonBall⟩
  refine
    ⟨min epsilon ((1 : ℝ) / 2),
      lt_min hepsilonPos (by norm_num),
      min_le_right _ _, ?_⟩
  intro s hs
  rcases hs with ⟨hsIm, hsPos, hsLt⟩
  have hsNe : s ≠ rho := by
    intro hsEq
    have : |s.re - rho.re| = 0 := by simp [hsEq]
    linarith
  have hsDist : dist s rho = |s.re - rho.re| := by
    rw [Complex.dist_eq, Complex.norm_def, Complex.normSq_apply]
    simp [hsIm]
    simpa [pow_two] using (Real.sqrt_sq_eq_abs (s.re - rho.re))
  have hsBall : s ∈ Metric.ball rho epsilon := by
    change dist s rho < epsilon
    rw [hsDist]
    exact lt_of_lt_of_le hsLt (min_le_left _ _)
  have hsU : s ∈ u := hepsilonBall hsBall
  have hsComp : s ∈ ({rho}ᶜ : Set ℂ) := by
    simpa using hsNe
  exact huSub ⟨hsU, hsComp⟩

/-- Multiplicity data supplies a positive zero-free horizontal radius without
any simplicity assumption. -/
theorem IsGenuineZeroOfMultiplicity.exists_genuineTransversalRadius
    {order : ℕ} {rho : ℂ}
    (hroot : IsGenuineZeroOfMultiplicity order rho) :
    ∃ r : ℝ,
      0 < r ∧
      r ≤ (1 : ℝ) / 2 ∧
      ∀ ⦃s : ℂ⦄,
        s ∈ genuineTransversalWindow rho r →
          genuineContinuation s ≠ 0 := by
  exact
    exists_genuineTransversalRadius_of_eventually_ne_zero
      hroot.eventually_ne_zero

/-- Canonical choice of a near-axis certificate over every critical-line
finite-multiplicity Genuine zero.  This closes the local near-axis gate at
arbitrary finite multiplicity; the remaining global work lies outside the
resulting union of windows. -/
noncomputable def
    GenuineNearAxisMultiplicityCertificate.of_finiteMultiplicity :
    GenuineNearAxisMultiplicityCertificate := by
  classical
  have hex :
      ∀ rho, IsCriticalGenuineZeroOfFiniteMultiplicity rho →
        ∃ r : ℝ,
          0 < r ∧
          r ≤ (1 : ℝ) / 2 ∧
          ∀ ⦃s : ℂ⦄,
            s ∈ genuineTransversalWindow rho r →
              genuineContinuation s ≠ 0 := by
    intro rho hrho
    rcases hrho with ⟨order, hroot, _hrho⟩
    exact hroot.exists_genuineTransversalRadius
  let radius : ℂ → ℝ := fun rho =>
    if hrho : IsCriticalGenuineZeroOfFiniteMultiplicity rho then
      Classical.choose (hex rho hrho)
    else
      (1 : ℝ) / 2
  refine
    { radius := radius
      radius_pos := ?_
      radius_le_half := ?_
      nonvanishing := ?_ }
  · intro rho hrho
    simpa [radius, hrho] using
      (Classical.choose_spec (hex rho hrho)).1
  · intro rho hrho
    simpa [radius, hrho] using
      (Classical.choose_spec (hex rho hrho)).2.1
  · intro rho s hrho hs
    have hnonzero := (Classical.choose_spec (hex rho hrho)).2.2
    exact hnonzero (by simpa [radius, hrho] using hs)

/-- Membership in the induced near-axis region is enough for Genuine
nonvanishing. -/
theorem GenuineNearAxisMultiplicityCertificate.nonvanishing_of_mem
    (cert : GenuineNearAxisMultiplicityCertificate) {s : ℂ}
    (hs : s ∈ genuineNearAxisRegion cert.radius) :
    genuineContinuation s ≠ 0 := by
  rcases hs with ⟨rho, hrho, hsWindow⟩
  exact cert.nonvanishing hrho hsWindow

end

end GenuineZeroUniformAtlasEnergy

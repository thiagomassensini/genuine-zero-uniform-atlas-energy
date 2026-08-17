import GenuineZeroUniformAtlasEnergy.EmpiricalFullEvenContinuation
import GenuineZeroUniformAtlasEnergy.UniformCoercivityOn

/-!
# Concrete empirical energy limit and confinement bridge

This module connects the faithful finite C2--C7 stack to its infinite
characteristic energy.  It proves the actual pointwise cutoff limit and then
eliminates the abstract limit hypothesis from the confinement step.

The remaining quantitative hypothesis is stated honestly: a positive
cutoff-uniform finite coercivity certificate must still be supplied, globally
or on the chosen region.  No floating-point campaign is promoted to that
certificate here.
-/

open Filter Set
open scoped BigOperators Topology

namespace GenuineZeroUniformAtlasEnergy

open CPFormal.Analytic.Cp

noncomputable section

/-- The infinite unnormalised quadratic energy of the faithful six-camera
stack. -/
def empiricalCollectiveRawEnergy (s : ℂ) : ℝ :=
  ∑ camera : EmpiricalCamera,
    Complex.normSq (empiricalCameraCharacteristic camera s)

/-- The standard real-plane parameter used by the empirical stack. -/
def empiricalPlaneParameter (sigma time : ℝ) : ℂ :=
  (sigma : ℂ) + (time : ℂ) * Complex.I

@[simp] theorem empiricalPlaneParameter_re (sigma time : ℝ) :
    (empiricalPlaneParameter sigma time).re = sigma := by
  simp [empiricalPlaneParameter]

@[simp] theorem empiricalPlaneParameter_im (sigma time : ℝ) :
    (empiricalPlaneParameter sigma time).im = time := by
  simp [empiricalPlaneParameter]

/-- Finite empirical energy written on the real `(sigma,time)` plane. -/
def finiteEmpiricalCollectiveRawEnergyPlane
    (M : ℕ) (sigma time : ℝ) : ℝ :=
  finiteEmpiricalCollectiveRawEnergy M (empiricalPlaneParameter sigma time)

/-- Infinite empirical energy written on the real `(sigma,time)` plane. -/
def empiricalCollectiveRawEnergyPlane (sigma time : ℝ) : ℝ :=
  empiricalCollectiveRawEnergy (empiricalPlaneParameter sigma time)

/-- Real parameter pairs whose associated complex parameter lies in the
Genuine critical strip. -/
def empiricalCriticalStripPlane : Set (ℝ × ℝ) :=
  {point | empiricalPlaneParameter point.1 point.2 ∈ genuineCriticalStrip}

private theorem tendsto_finiteEmpiricalCameraCharacteristic
    (camera : EmpiricalCamera) {s : ℂ} (hs : -1 < s.re) :
    Tendsto
      (fun M : ℕ => finiteEmpiricalCameraCharacteristic camera M s)
      atTop
      (nhds (empiricalCameraCharacteristic camera s)) := by
  unfold finiteEmpiricalCameraCharacteristic empiricalCameraCharacteristic
  have hsum :
      Tendsto
        (fun M : ℕ =>
          ∑ k ∈ Finset.range M, empiricalCameraBlock camera k s)
        atTop
        (nhds (∑' k : ℕ, empiricalCameraBlock camera k s)) :=
    (summable_empiricalCameraBlock camera hs).hasSum.tendsto_sum_nat
  exact tendsto_const_nhds.add hsum

private theorem tendsto_finiteEmpiricalCollectiveRawEnergy
    {s : ℂ} (hs : -1 < s.re) :
    Tendsto
      (fun M : ℕ => finiteEmpiricalCollectiveRawEnergy M s)
      atTop
      (nhds (empiricalCollectiveRawEnergy s)) := by
  classical
  unfold finiteEmpiricalCollectiveRawEnergy empiricalCollectiveRawEnergy
  apply tendsto_finsetSum
  intro camera _hcamera
  exact (Complex.continuous_normSq.tendsto _).comp
    (tendsto_finiteEmpiricalCameraCharacteristic camera hs)

/-- The concrete finite six-camera raw energy converges pointwise to the
concrete infinite six-camera raw energy throughout `sigma > -1`. -/
theorem finiteEmpiricalCollectiveRawEnergyPlane_tendsto
    (sigma time : ℝ) (hsigma : -1 < sigma) :
    Tendsto
      (fun M : ℕ => finiteEmpiricalCollectiveRawEnergyPlane M sigma time)
      atTop
      (nhds (empiricalCollectiveRawEnergyPlane sigma time)) := by
  have hs : -1 < (empiricalPlaneParameter sigma time).re := by
    simpa using hsigma
  simpa [finiteEmpiricalCollectiveRawEnergyPlane,
    empiricalCollectiveRawEnergyPlane] using
    (tendsto_finiteEmpiricalCollectiveRawEnergy
      (s := empiricalPlaneParameter sigma time) hs)

/-- A Genuine zero in the critical strip annihilates the concrete infinite
energy of the faithful empirical stack. -/
theorem empiricalCollectiveRawEnergy_eq_zero_of_genuine_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    empiricalCollectiveRawEnergy s = 0 := by
  classical
  unfold empiricalCollectiveRawEnergy
  apply Finset.sum_eq_zero
  intro camera _hcamera
  rw [empiricalCameraCharacteristic_zero_of_genuineContinuation_zero
    camera hs hzero]
  simp

/-- Real-plane form of the simultaneous-zero energy identity. -/
theorem empiricalCollectiveRawEnergyPlane_eq_zero_of_genuine_zero
    {sigma time : ℝ}
    (hs : empiricalPlaneParameter sigma time ∈ genuineCriticalStrip)
    (hzero : genuineContinuation (empiricalPlaneParameter sigma time) = 0) :
    empiricalCollectiveRawEnergyPlane sigma time = 0 := by
  exact empiricalCollectiveRawEnergy_eq_zero_of_genuine_zero hs hzero

/-- Concrete regional limit-and-confinement capstone.  The pointwise energy
limit is no longer a supplied hypothesis: it follows from the absolutely
summable empirical camera series.  A positive eventual finite coercivity
certificate on the chosen region then excludes every off-critical Genuine
zero in that region. -/
theorem genuineZero_in_region_forces_re_eq_half_of_eventual_empiricalCoercivity
    {region : Set (ℝ × ℝ)} {c sigma time : ℝ}
    (hc : 0 < c)
    (hstrip : ∀ point ∈ region,
      empiricalPlaneParameter point.1 point.2 ∈ genuineCriticalStrip)
    (hcoercive : ∀ᶠ M : ℕ in atTop,
      IsTransverselyCoerciveOn region
        (finiteEmpiricalCollectiveRawEnergyPlane M) c)
    (hmem : (sigma, time) ∈ region)
    (hzero : genuineContinuation (empiricalPlaneParameter sigma time) = 0) :
    sigma = (1 : ℝ) / 2 := by
  have hlimit : ∀ point ∈ region,
      Tendsto
        (fun M : ℕ =>
          finiteEmpiricalCollectiveRawEnergyPlane M point.1 point.2)
        atTop
        (nhds (empiricalCollectiveRawEnergyPlane point.1 point.2)) := by
    intro point hpoint
    have hs := hstrip point hpoint
    have hpos : 0 < point.1 := by
      simpa using hs.1
    exact finiteEmpiricalCollectiveRawEnergyPlane_tendsto
      point.1 point.2 (by linarith)
  have hlimitCoercive :
      IsTransverselyCoerciveOn region empiricalCollectiveRawEnergyPlane c :=
    transverseCoercivityOn_passes_to_pointwise_limit_eventually
      region finiteEmpiricalCollectiveRawEnergyPlane
      empiricalCollectiveRawEnergyPlane c hcoercive hlimit
  have henergy : empiricalCollectiveRawEnergyPlane sigma time = 0 :=
    empiricalCollectiveRawEnergyPlane_eq_zero_of_genuine_zero
      (hstrip (sigma, time) hmem) hzero
  exact zero_in_region_forces_re_eq_half_of_transverse_coercivityOn
    hc hlimitCoercive hmem henergy

/-- Strip-wide concrete confinement theorem.  It removes the separate
pointwise-limit premise from the abstract interface; only the eventual finite
coercivity certificate remains quantitative input. -/
theorem genuineZero_forces_re_eq_half_of_eventual_empiricalStripCoercivity
    {c sigma time : ℝ}
    (hc : 0 < c)
    (hcoercive : ∀ᶠ M : ℕ in atTop,
      IsTransverselyCoerciveOn empiricalCriticalStripPlane
        (finiteEmpiricalCollectiveRawEnergyPlane M) c)
    (hs : empiricalPlaneParameter sigma time ∈ genuineCriticalStrip)
    (hzero : genuineContinuation (empiricalPlaneParameter sigma time) = 0) :
    sigma = (1 : ℝ) / 2 := by
  apply genuineZero_in_region_forces_re_eq_half_of_eventual_empiricalCoercivity
    (region := empiricalCriticalStripPlane) hc
  · intro point hpoint
    simpa [empiricalCriticalStripPlane] using hpoint
  · exact hcoercive
  · simpa [empiricalCriticalStripPlane] using hs
  · exact hzero

/-- A supplied eventual global finite coercivity certificate implies the
strip-wide hypothesis above and therefore confines every Genuine zero in the
strip. -/
theorem genuineZero_forces_re_eq_half_of_eventual_globalEmpiricalCoercivity
    {c sigma time : ℝ}
    (hc : 0 < c)
    (hcoercive : ∀ᶠ M : ℕ in atTop,
      IsTransverselyCoercive
        (finiteEmpiricalCollectiveRawEnergyPlane M) c)
    (hs : empiricalPlaneParameter sigma time ∈ genuineCriticalStrip)
    (hzero : genuineContinuation (empiricalPlaneParameter sigma time) = 0) :
    sigma = (1 : ℝ) / 2 := by
  have hregional : ∀ᶠ M : ℕ in atTop,
      IsTransverselyCoerciveOn empiricalCriticalStripPlane
        (finiteEmpiricalCollectiveRawEnergyPlane M) c := by
    filter_upwards [hcoercive] with M hM
    exact hM.isTransverselyCoerciveOn empiricalCriticalStripPlane
  exact genuineZero_forces_re_eq_half_of_eventual_empiricalStripCoercivity
    hc hregional hs hzero

end

end GenuineZeroUniformAtlasEnergy

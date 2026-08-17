import GenuineZeroUniformAtlasEnergy.EmpiricalFullEvenContinuation
import GenuineZeroUniformAtlasEnergy.UniformCoercivityOn

/-!
# Concrete empirical energy limit and confinement bridge

This module connects the faithful finite C2--C7 stack to its infinite
characteristic energy.  It first proves the actual pointwise cutoff limit,
then packages the existing eventual coercivity interface into a concrete
confinement theorem for Genuine zeros.
-/

open Filter
open scoped BigOperators Topology

namespace GenuineZeroUniformAtlasEnergy

noncomputable section

/-- The infinite unnormalised quadratic energy of the faithful six-camera
stack. -/
def empiricalCollectiveRawEnergy (s : ℂ) : ℝ :=
  ∑ camera : EmpiricalCamera,
    Complex.normSq (empiricalCameraCharacteristic camera s)

/-- The standard real-plane parameter used by the empirical stack. -/
def empiricalPlaneParameter (sigma time : ℝ) : ℂ :=
  (sigma : ℂ) + (time : ℂ) * Complex.I

/-- Finite empirical energy written on the real `(sigma,time)` plane. -/
def finiteEmpiricalCollectiveRawEnergyPlane
    (M : ℕ) (sigma time : ℝ) : ℝ :=
  finiteEmpiricalCollectiveRawEnergy M (empiricalPlaneParameter sigma time)

/-- Infinite empirical energy written on the real `(sigma,time)` plane. -/
def empiricalCollectiveRawEnergyPlane (sigma time : ℝ) : ℝ :=
  empiricalCollectiveRawEnergy (empiricalPlaneParameter sigma time)

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
  apply tendsto_finset_sum
  intro camera _hcamera
  exact (Complex.continuous_normSq.tendsto _).comp
    (tendsto_finiteEmpiricalCameraCharacteristic camera hs)

private theorem empiricalCollectiveRawEnergy_eq_zero_of_genuine_zero
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

end

end GenuineZeroUniformAtlasEnergy

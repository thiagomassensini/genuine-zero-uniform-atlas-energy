import CPFormal.Analytic.CpGenuineNativeRealBoundaryCrosswalk
import CPFormal.Analytic.CpPositionalCarryQuadraticRigidity

/-!
# One native geometry, one zero

The native parameter has one free real coordinate: phase time.  Its radial
amplitude is the quadratic carry amplitude `n^(-1/2)`, whose squared norm is
the inverse carry mass `n⁻¹`.

The real two-coordinate camera and the scalar Genuine chart are not distinct
number systems or distinct zero notions.  Exact finite-chart equality followed
by the common limit proves literal equality of their zero sets.
-/

namespace GenuineZeroUniformAtlasEnergy

open CPFormal.Analytic.Cp
open CPFormal.Carry.Cp

noncomputable section

/-- Before any camera or zero, quadratic energy reproduces positional carry
mass in every nondegenerate base and positive depth exactly at exponent
`1/2`.  The real rotation angle is arbitrary. -/
theorem quadraticCarryShell_energy_eq_mass_iff
    (b k : ℕ) (hb : 1 < b) (hk : 0 < k)
    (sigma theta : ℝ) :
    positionalPlaneEnergy
        (positionalBranchShell b sigma k (realRotationDirection theta)) =
        criticalMass b k ↔
      sigma = (1 : ℝ) / 2 :=
  positionalPlaneEnergy_rotatedShell_eq_criticalMass_iff
    b k hb hk sigma theta

/-- The unique native spectral parameter at real phase time `time`. -/
def nativeParameter (time : ℝ) : ℂ :=
  nativeCarryRealPlaneParameter ((1 : ℝ) / 2) time

@[simp] theorem nativeParameter_re (time : ℝ) :
    (nativeParameter time).re = (1 : ℝ) / 2 := rfl

@[simp] theorem nativeParameter_im (time : ℝ) :
    (nativeParameter time).im = time := rfl

/-- Every native parameter lies in the open Genuine strip. -/
theorem nativeParameter_mem_genuineCriticalStrip (time : ℝ) :
    nativeParameter time ∈ genuineCriticalStrip := by
  constructor <;> norm_num

/-- The quadratic energy of the native amplitude is exactly inverse carry
mass.  Phase time does not alter it. -/
theorem nativeAmplitude_energy_eq_inverseCarryMass
    (time : ℝ) {n : ℤ} (hn : 0 < n) :
    nativeCarryRealPlaneEnergy (nativeCarryRealPlaneSample time n) =
      ((n : ℝ))⁻¹ :=
  nativeCarryRealPlaneEnergy_sample time hn

/-- At every finite cutoff, the packaged native real resultant is literally
the Genuine finite Dirichlet chart computed from the same positional wave. -/
theorem packagedNativeFiniteChart_eq_genuineFiniteChart
    (M : ℕ) (time : ℝ) :
    nativeCarryRealPlaneComplexPackaging
        (nativeCarryRealPlaneFiniteChart 3 M time) =
      CPFormal.Genuine.Cp.finiteChart 3 M
        (dirichletTerm (nativeParameter time)) := by
  simpa [nativeCarryRealPlaneFiniteChart, nativeParameter] using
    (nativeCarryRealPlaneComplexPackaging_finiteChartAt_eq_dirichlet
      3 M (by norm_num) (by norm_num) ((1 : ℝ) / 2) time)

/-- The native camera and the Genuine continuation have one and the same zero
at each native time. -/
theorem nativeZero_iff_genuineZero (time : ℝ) :
    NativeCarryRealOperatorBoundaryClosesAt
        3 ((1 : ℝ) / 2) time ↔
      genuineContinuation (nativeParameter time) = 0 := by
  simpa [nativeParameter] using
    (nativeCarryRealBoundaryClosure_iff_genuineContinuation_zero
      (nativeParameter_mem_genuineCriticalStrip time))

end

end GenuineZeroUniformAtlasEnergy

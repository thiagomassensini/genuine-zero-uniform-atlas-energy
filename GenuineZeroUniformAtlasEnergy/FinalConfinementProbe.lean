import GenuineZeroUniformAtlasEnergy

/-!
# Final confinement assembly probe

This probe makes every already-closed bridge explicit and asks the compiled
library for only one object: a positive eventual finite coercivity certificate
for the faithful empirical C2--C7 energy.  If that certificate already exists
under a different theorem name, `exact?` should resolve it.  Otherwise the
kernel error is the exact residual interface, with no numerical premise and no
conclusion hidden in a definition.
-/

open Filter Set

namespace GenuineZeroUniformAtlasEnergy

open CPFormal.Analytic.Cp

noncomputable section

/-- The single certificate shape consumed by the v0.11 concrete limit bridge. -/
def HasEventualPositiveEmpiricalStripCoercivity : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ᶠ M : ℕ in atTop,
      IsTransverselyCoerciveOn empiricalCriticalStripPlane
        (finiteEmpiricalCollectiveRawEnergyPlane M) c

/-- Final target.  Everything after `hcert` is already the v0.11 concrete
limit/confinement theorem; the probe asks the theorem inventory to synthesize
only `hcert`. -/
theorem finalGenuineZeroConfinement_probe
    {s : ℂ}
    (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    s.re = (1 : ℝ) / 2 := by
  have hcert : HasEventualPositiveEmpiricalStripCoercivity := by
    exact?
  rcases hcert with ⟨c, hc, hcoercive⟩
  have h := genuineZero_forces_re_eq_half_of_eventual_empiricalStripCoercivity
    (c := c) (sigma := s.re) (time := s.im) hc hcoercive
    (by simpa [empiricalPlaneParameter] using hs)
    (by simpa [empiricalPlaneParameter] using hzero)
  simpa using h

end

end GenuineZeroUniformAtlasEnergy

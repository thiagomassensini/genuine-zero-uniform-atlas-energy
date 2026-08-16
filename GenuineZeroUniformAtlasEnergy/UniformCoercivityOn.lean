import GenuineZeroUniformAtlasEnergy.AsymptoticCoercivity

/-!
# Region-restricted transverse coercivity and limit passage

The branch-and-bound computations concern a compact rectangle, whereas
`IsTransverselyCoercive` quantifies over the whole real plane.  This module
records an interface for an arbitrary region, applicable in particular to a
compact rectangle, and its exact conditional passage to a pointwise energy
limit.  It does not encode or certify any specific rectangle.
-/

open Filter Set

namespace GenuineZeroUniformAtlasEnergy

noncomputable section

/-- The raw energy dominates squared radial distance from the critical line
at every point of a specified region. -/
def IsTransverselyCoerciveOn
    (region : Set (ℝ × ℝ))
    (energy : ℝ → ℝ → ℝ) (c : ℝ) : Prop :=
  ∀ point ∈ region,
    c * (point.1 - (1 : ℝ) / 2) ^ 2 ≤ energy point.1 point.2

/-- Region-restricted coercivity is equivalent to nonnegativity of the same
smooth certificate residual on that region. -/
theorem isTransverselyCoerciveOn_iff_certificateResidual_nonneg
    (region : Set (ℝ × ℝ))
    (energy : ℝ → ℝ → ℝ) (c : ℝ) :
    IsTransverselyCoerciveOn region energy c ↔
      ∀ point ∈ region,
        0 ≤ transverseCertificateResidual
          energy c point.1 point.2 := by
  constructor
  · intro h point hpoint
    unfold transverseCertificateResidual
    linarith [h point hpoint]
  · intro h point hpoint
    unfold transverseCertificateResidual at h
    linarith [h point hpoint]

/-- A positive regional bound excludes off-critical zeros inside the supplied
region. -/
theorem zero_in_region_forces_re_eq_half_of_transverse_coercivityOn
    {region : Set (ℝ × ℝ)}
    {energy : ℝ → ℝ → ℝ} {c sigma time : ℝ}
    (hc : 0 < c)
    (hcoercive : IsTransverselyCoerciveOn region energy c)
    (hmem : (sigma, time) ∈ region)
    (hzero : energy sigma time = 0) :
    sigma = (1 : ℝ) / 2 := by
  by_contra hne
  have hdiff : sigma - (1 : ℝ) / 2 ≠ 0 := sub_ne_zero.mpr hne
  have hsquare : 0 < (sigma - (1 : ℝ) / 2) ^ 2 := by positivity
  have hpositive : 0 < c * (sigma - (1 : ℝ) / 2) ^ 2 :=
    mul_pos hc hsquare
  have hbound := hcoercive (sigma, time) hmem
  simp only at hbound
  rw [hzero] at hbound
  linarith

/-- An eventual uniform lower bound on a fixed region passes to the pointwise
limit energy on that same region. -/
theorem transverseCoercivityOn_passes_to_pointwise_limit_eventually
    (region : Set (ℝ × ℝ))
    (energy : ℕ → ℝ → ℝ → ℝ)
    (limitEnergy : ℝ → ℝ → ℝ) (c : ℝ)
    (hcoercive : ∀ᶠ M : ℕ in atTop,
      IsTransverselyCoerciveOn region (energy M) c)
    (hlimit : ∀ point ∈ region,
      Tendsto (fun M : ℕ => energy M point.1 point.2) atTop
        (nhds (limitEnergy point.1 point.2))) :
    IsTransverselyCoerciveOn region limitEnergy c := by
  intro point hpoint
  apply ge_of_tendsto (hlimit point hpoint)
  filter_upwards [hcoercive] with M hM
  exact hM point hpoint

/-- A global coercivity certificate restricts to every region. -/
theorem IsTransverselyCoercive.isTransverselyCoerciveOn
    {energy : ℝ → ℝ → ℝ} {c : ℝ}
    (h : IsTransverselyCoercive energy c)
    (region : Set (ℝ × ℝ)) :
    IsTransverselyCoerciveOn region energy c := by
  intro point _hpoint
  exact h point.1 point.2

end

end GenuineZeroUniformAtlasEnergy

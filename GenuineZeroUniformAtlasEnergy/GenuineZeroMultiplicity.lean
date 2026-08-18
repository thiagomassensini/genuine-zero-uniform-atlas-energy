import GenuineZeroUniformAtlasEnergy.EmpiricalStackDifferential
import Mathlib.Analysis.Analytic.Order

/-!
# Genuine zero multiplicity and empirical root jets

The existing positive-coercivity route is the nondegenerate order-one sector.
The underlying analytic theory, however, carries arbitrary finite zero order.
This module records that distinction without importing the private
`formalizacao_C2` repository.

A Genuine zero of multiplicity `m` is represented by the usual finite jet:
all iterated derivatives below `m` vanish and the `m`th derivative is nonzero.
Mathlib's `analyticOrderAt` then identifies this jet datum with analytic order
`m`.  The empirical six-camera root jet is obtained by multiplying the common
Genuine jet by the already formalized nonvanishing camera factors.

For `m = 1` the root-jet vector is exactly the existing
`empiricalClockTangentVector`, so the current quadratic PR remains a literal
specialization rather than a competing definition.
-/

open scoped Topology

namespace GenuineZeroUniformAtlasEnergy

open CPFormal.Analytic.Cp

noncomputable section

/-- A finite-order Genuine zero in the open critical strip.  The zero predicate
is not strengthened with a location conclusion: multiplicity is only the
ordinary analytic jet condition. -/
structure IsGenuineZeroOfMultiplicity (order : ℕ) (s : ℂ) : Prop where
  mem_strip : s ∈ genuineCriticalStrip
  order_pos : 0 < order
  lower_iteratedDeriv_eq_zero :
    ∀ k < order, iteratedDeriv k genuineContinuation s = 0
  leading_iteratedDeriv_ne_zero :
    iteratedDeriv order genuineContinuation s ≠ 0

namespace IsGenuineZeroOfMultiplicity

/-- Genuine continuation is analytic at every multiplicity datum. -/
theorem analyticAt {order : ℕ} {s : ℂ}
    (h : IsGenuineZeroOfMultiplicity order s) :
    AnalyticAt ℂ genuineContinuation s :=
  analyticOnNhd_genuineContinuation_genuineCriticalStrip s h.mem_strip

/-- Every positive-order multiplicity datum is, in particular, a raw Genuine
zero. -/
theorem zero {order : ℕ} {s : ℂ}
    (h : IsGenuineZeroOfMultiplicity order s) :
    genuineContinuation s = 0 := by
  have hzero := h.lower_iteratedDeriv_eq_zero 0 h.order_pos
  simpa using hzero

/-- The finite jet definition agrees with Mathlib's analytic order. -/
theorem analyticOrderAt_eq {order : ℕ} {s : ℂ}
    (h : IsGenuineZeroOfMultiplicity order s) :
    analyticOrderAt genuineContinuation s = (order : ℕ∞) := by
  exact
    (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero h.analyticAt).2
      ⟨h.lower_iteratedDeriv_eq_zero, h.leading_iteratedDeriv_ne_zero⟩

/-- Multiplicity one is exactly the familiar zero plus nonzero first
complex derivative, with strip membership kept explicit. -/
theorem one_iff {s : ℂ} :
    IsGenuineZeroOfMultiplicity 1 s ↔
      s ∈ genuineCriticalStrip ∧
        genuineContinuation s = 0 ∧ deriv genuineContinuation s ≠ 0 := by
  constructor
  · intro h
    refine ⟨h.mem_strip, h.zero, ?_⟩
    simpa [iteratedDeriv_one] using h.leading_iteratedDeriv_ne_zero
  · rintro ⟨hs, hzero, hderiv⟩
    refine ⟨hs, by omega, ?_, ?_⟩
    · intro k hk
      have hkzero : k = 0 := by omega
      subst k
      simpa using hzero
    · simpa [iteratedDeriv_one] using hderiv

end IsGenuineZeroOfMultiplicity

/-- Order-`m` empirical root jet in the concrete six-camera Euclidean space. -/
def empiricalRootJetVector (order : ℕ) (s : ℂ) : EmpiricalCameraStack :=
  WithLp.toLp 2 fun camera =>
    empiricalLimitingFactor camera s *
      iteratedDeriv order genuineContinuation s

@[simp] theorem empiricalRootJetVector_apply
    (order : ℕ) (s : ℂ) (camera : EmpiricalCamera) :
    empiricalRootJetVector order s camera =
      empiricalLimitingFactor camera s *
        iteratedDeriv order genuineContinuation s := by
  rfl

/-- The current clock tangent is precisely the order-one empirical root jet. -/
@[simp] theorem empiricalRootJetVector_one (s : ℂ) :
    empiricalRootJetVector 1 s = empiricalClockTangentVector s := by
  ext camera
  simp [empiricalRootJetVector, empiricalClockTangentVector, iteratedDeriv_one]

/-- A nonzero leading Genuine jet gives a nonzero empirical stack jet on the
critical line.  The aligned C2 factor supplies one explicit nonvanishing
coordinate. -/
theorem empiricalRootJetVector_ne_zero
    {order : ℕ} {s : ℂ}
    (hs : s.re = (1 : ℝ) / 2)
    (hleading : iteratedDeriv order genuineContinuation s ≠ 0) :
    empiricalRootJetVector order s ≠ 0 := by
  have hcomponent :
      empiricalRootJetVector order s EmpiricalCamera.c2 ≠ 0 := by
    simp only [empiricalRootJetVector_apply, empiricalLimitingFactor]
    exact mul_ne_zero
      (naturalEvenCameraFactor_four_ne_zero_on_criticalLine hs) hleading
  intro hzero
  apply hcomponent
  have hc2 := congrArg
    (fun w : EmpiricalCameraStack => w EmpiricalCamera.c2) hzero
  simpa using hc2

/-- Multiplicity data on the native line automatically supplies a nonzero
order-`m` empirical jet. -/
theorem empiricalRootJetVector_ne_zero_of_multiplicity
    {order : ℕ} {s : ℂ}
    (hroot : IsGenuineZeroOfMultiplicity order s)
    (hs : s.re = (1 : ℝ) / 2) :
    empiricalRootJetVector order s ≠ 0 :=
  empiricalRootJetVector_ne_zero hs hroot.leading_iteratedDeriv_ne_zero

end

end GenuineZeroUniformAtlasEnergy

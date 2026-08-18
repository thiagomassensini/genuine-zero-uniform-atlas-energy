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
Genuine jet by the already formalized camera factors.

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

/-- At a Genuine zero of order `m`, the `m`th derivative of every faithful
empirical camera is exactly its limiting factor times the common leading
Genuine jet.  This is the public finite-Leibniz replacement for the private
near-axis helper: every term containing a lower Genuine derivative vanishes. -/
theorem iteratedDeriv_empiricalCameraCharacteristic_eq_rootJet
    (camera : EmpiricalCamera) {order : ℕ} {s : ℂ}
    (hroot : IsGenuineZeroOfMultiplicity order s) :
    iteratedDeriv order (empiricalCameraCharacteristic camera) s =
      empiricalRootJetVector order s camera := by
  have heq :=
    empiricalCameraCharacteristic_eventuallyEq_limitingFactor_mul_genuine
      camera hroot.mem_strip
  have hfactor :
      ContDiffAt ℂ order (empiricalLimitingFactor camera) s :=
    ((differentiable_empiricalLimitingFactor camera).analyticAt s).contDiffAt
  have hgenuine : ContDiffAt ℂ order genuineContinuation s :=
    hroot.analyticAt.contDiffAt
  have hleibniz :
      iteratedDeriv order
          (fun z : ℂ =>
            empiricalLimitingFactor camera z * genuineContinuation z) s =
        ∑ j ∈ Finset.range (order + 1),
          (Nat.choose order j : ℂ) *
            iteratedDeriv j (empiricalLimitingFactor camera) s *
              iteratedDeriv (order - j) genuineContinuation s := by
    simpa only [Pi.mul_apply] using
      (iteratedDeriv_mul (n := order) (x := s) hfactor hgenuine)
  have hsum :
      (∑ j ∈ Finset.range (order + 1),
          (Nat.choose order j : ℂ) *
            iteratedDeriv j (empiricalLimitingFactor camera) s *
              iteratedDeriv (order - j) genuineContinuation s) =
        empiricalLimitingFactor camera s *
          iteratedDeriv order genuineContinuation s := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro j hjmem hjne
      have hjlt : j < order + 1 := Finset.mem_range.mp hjmem
      have hjle : j ≤ order := Nat.lt_succ_iff.mp hjlt
      have hjpos : 0 < j := Nat.pos_of_ne_zero hjne
      have hsub : order - j < order :=
        Nat.sub_lt hroot.order_pos hjpos
      have hzero := hroot.lower_iteratedDeriv_eq_zero (order - j) hsub
      simp [hzero]
    · simp
  calc
    iteratedDeriv order (empiricalCameraCharacteristic camera) s =
        iteratedDeriv order
          (fun z : ℂ =>
            empiricalLimitingFactor camera z * genuineContinuation z) s := by
      simpa using heq.iteratedDeriv_eq order
    _ = ∑ j ∈ Finset.range (order + 1),
          (Nat.choose order j : ℂ) *
            iteratedDeriv j (empiricalLimitingFactor camera) s *
              iteratedDeriv (order - j) genuineContinuation s := hleibniz
    _ = empiricalLimitingFactor camera s *
          iteratedDeriv order genuineContinuation s := hsum
    _ = empiricalRootJetVector order s camera := rfl

/-- Concrete order-`m` derivative stack of all six infinite empirical
characteristics. -/
def empiricalCameraIteratedDerivativeStack
    (order : ℕ) (s : ℂ) : EmpiricalCameraStack :=
  WithLp.toLp 2 fun camera =>
    iteratedDeriv order (empiricalCameraCharacteristic camera) s

@[simp] theorem empiricalCameraIteratedDerivativeStack_apply
    (order : ℕ) (s : ℂ) (camera : EmpiricalCamera) :
    empiricalCameraIteratedDerivativeStack order s camera =
      iteratedDeriv order (empiricalCameraCharacteristic camera) s := by
  rfl

/-- The already existing derivative stack is the first member of the general
iterated-derivative stack. -/
@[simp] theorem empiricalCameraIteratedDerivativeStack_one (s : ℂ) :
    empiricalCameraIteratedDerivativeStack 1 s =
      empiricalCameraDerivativeStack s := by
  ext camera
  simp [empiricalCameraIteratedDerivativeStack,
    empiricalCameraDerivativeStack, iteratedDeriv_one]

/-- Stack form of the order-`m` empirical root-jet crosswalk. -/
theorem empiricalCameraIteratedDerivativeStack_eq_rootJet_of_multiplicity
    {order : ℕ} {s : ℂ}
    (hroot : IsGenuineZeroOfMultiplicity order s) :
    empiricalCameraIteratedDerivativeStack order s =
      empiricalRootJetVector order s := by
  ext camera
  exact
    iteratedDeriv_empiricalCameraCharacteristic_eq_rootJet camera hroot

/-- On the critical line, the concrete order-`m` camera derivative stack is
nonzero for every finite Genuine multiplicity datum. -/
theorem empiricalCameraIteratedDerivativeStack_ne_zero_of_multiplicity
    {order : ℕ} {s : ℂ}
    (hroot : IsGenuineZeroOfMultiplicity order s)
    (hs : s.re = (1 : ℝ) / 2) :
    empiricalCameraIteratedDerivativeStack order s ≠ 0 := by
  rw [empiricalCameraIteratedDerivativeStack_eq_rootJet_of_multiplicity hroot]
  exact empiricalRootJetVector_ne_zero_of_multiplicity hroot hs

end

end GenuineZeroUniformAtlasEnergy

import GenuineZeroUniformAtlasEnergy.NativeCutoffAsymptotic
import GenuineZeroUniformAtlasEnergy.AsymptoticCoercivity
import CPFormal.Analytic.CpNaturalCameraFactor
import CPFormal.Analytic.CpGenuineCompatibility
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Projection algebra for the empirical six-camera stack

This module records the limiting factors used by the empirical operator.  The
odd cameras use the already formalized natural odd factors, while the aligned
camera labelled `2` uses the width-four factor already supplied by `CPFormal`.
The cameras labelled `4` and `6` retain their antipodal channels, so their
factor is defined separately here.  No analytic-continuation theorem is
claimed for that new full-even factor.

The leading finite-residue vector and the limiting complex-derivative
direction live in the complex Euclidean space on the six camera labels.  The
former is the negative of the proposed cutoff-tail coefficient at a resonance.
No theorem in this module identifies the complex-derivative model direction
with the real time derivative of the empirical stack, or either model vector
with a finite reoptimized operator.
-/

open scoped BigOperators ComplexConjugate InnerProductSpace

namespace GenuineZeroUniformAtlasEnergy

open CPFormal.Analytic.Cp

noncomputable section

/-- Factor of a full even empirical camera, including its antipodal channel. -/
def empiricalFullEvenCameraFactor (b : ℕ) (s : ℂ) : ℂ :=
  1 + ((b / 2 : ℕ) : ℂ) ^ (-s) -
    ((b + 2 : ℕ) : ℂ) * (b : ℂ) ^ (-s)

/-- Faithful limiting factor table for the six empirical cameras. -/
def empiricalLimitingFactor (camera : EmpiricalCamera) (s : ℂ) : ℂ :=
  match camera with
  | .c2 => naturalEvenCameraFactor 4 s
  | .c3 => naturalOddCameraFactor 3 s
  | .c4 => empiricalFullEvenCameraFactor 4 s
  | .c5 => naturalOddCameraFactor 5 s
  | .c6 => empiricalFullEvenCameraFactor 6 s
  | .c7 => naturalOddCameraFactor 7 s

/-- Exact algebraic separation of the full `C4` factor from five copies of
the aligned `C2` factor. -/
theorem empiricalFullEvenCameraFactor_four_sub_five_alignedC2
    (s : ℂ) :
    empiricalFullEvenCameraFactor 4 s -
        5 * naturalEvenCameraFactor 4 s =
      2 * (2 * (2 : ℂ) ^ (-s) - 1) *
        ((2 : ℂ) ^ (-s) + 2) := by
  have hpow :
      (4 : ℂ) ^ (-s) =
        (2 : ℂ) ^ (-s) * (2 : ℂ) ^ (-s) := by
    convert (Complex.natCast_mul_natCast_cpow 2 2 (-s)) using 1 <;>
      norm_num
  unfold empiricalFullEvenCameraFactor naturalEvenCameraFactor
  norm_num
  rw [hpow]
  ring

/-- On the critical line the full `C4` factor cannot equal five copies of
the aligned `C2` factor.  The proof uses only the modulus of `2^(-s)`. -/
theorem empiricalFullEvenCameraFactor_four_sub_five_alignedC2_ne_zero
    {s : ℂ} (hs : s.re = (1 : ℝ) / 2) :
    empiricalFullEvenCameraFactor 4 s -
        5 * naturalEvenCameraFactor 4 s ≠ 0 := by
  rw [empiricalFullEvenCameraFactor_four_sub_five_alignedC2]
  refine mul_ne_zero (mul_ne_zero (by norm_num) ?_) ?_
  · intro hzero
    have hq : (2 : ℂ) ^ (-s) = (1 : ℂ) / 2 := by
      linear_combination hzero / 2
    have hnorm := norm_nat_cpow_neg 2 (by norm_num) s
    rw [hs] at hnorm
    have hnorm' :
        ‖(2 : ℂ) ^ (-s)‖ = (2 : ℝ) ^ (-(2 : ℝ)⁻¹) := by
      simpa using hnorm
    have hstrict :
        (1 : ℝ) / 2 < (2 : ℝ) ^ (-(2 : ℝ)⁻¹) := by
      have h := Real.rpow_lt_rpow_of_exponent_lt
        (x := (2 : ℝ)) (y := (-1 : ℝ)) (z := (-(2 : ℝ)⁻¹))
        (by norm_num) (by norm_num)
      simpa [Real.rpow_neg_one] using h
    have hqnorm := congrArg norm hq
    norm_num at hqnorm
    rw [hnorm'] at hqnorm
    linarith
  · intro hzero
    have hq : (2 : ℂ) ^ (-s) = -2 := by
      linear_combination hzero
    have hnorm := norm_nat_cpow_neg 2 (by norm_num) s
    rw [hs] at hnorm
    have hnorm' :
        ‖(2 : ℂ) ^ (-s)‖ = (2 : ℝ) ^ (-(2 : ℝ)⁻¹) := by
      simpa using hnorm
    have hstrict :
        (2 : ℝ) ^ (-(2 : ℝ)⁻¹) < 1 := by
      exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
    have hqnorm := congrArg norm hq
    norm_num at hqnorm
    rw [hnorm'] at hqnorm
    linarith

/-- The complex Euclidean space carrying the six empirical camera values. -/
abbrev EmpiricalCameraStack := EuclideanSpace ℂ EmpiricalCamera

/-- Proposed leading coefficient of the finite resonant residue in each
empirical camera.  It is the negative of the corresponding cutoff-tail model
coefficient. -/
def empiricalLeadingCutoffVector (s : ℂ) : EmpiricalCameraStack :=
  WithLp.toLp 2 fun camera =>
    -(s * (EmpiricalCamera.secondRadiusMoment camera : ℂ) *
      ((EmpiricalCamera.period camera : ℕ) : ℂ) ^ (-s - 2))

/-- Complex-derivative model direction of the limiting empirical stack at a
Genuine point.  No real-time derivative identification is asserted here. -/
def empiricalClockTangentVector (s : ℂ) : EmpiricalCameraStack :=
  WithLp.toLp 2 fun camera =>
    empiricalLimitingFactor camera s * deriv genuineContinuation s

@[simp] theorem empiricalLeadingCutoffVector_apply
    (s : ℂ) (camera : EmpiricalCamera) :
    empiricalLeadingCutoffVector s camera =
      -(s * (EmpiricalCamera.secondRadiusMoment camera : ℂ) *
        ((EmpiricalCamera.period camera : ℕ) : ℂ) ^ (-s - 2)) := by
  rfl

/-- The finite-residue model coordinate is exactly the negative of the
corresponding cutoff-tail model coefficient. -/
@[simp] theorem empiricalLeadingCutoffVector_apply_eq_neg_tailCoefficient
    (s : ℂ) (camera : EmpiricalCamera) :
    empiricalLeadingCutoffVector s camera =
      -empiricalNativeTailCoefficient camera s := by
  rw [empiricalLeadingCutoffVector_apply]
  unfold empiricalNativeTailCoefficient
    nativeExplicitRadiusTailCoefficient
  rw [nativeRadiusSecondMoment_empirical]
  norm_cast

@[simp] theorem empiricalClockTangentVector_apply
    (s : ℂ) (camera : EmpiricalCamera) :
    empiricalClockTangentVector s camera =
      empiricalLimitingFactor camera s * deriv genuineContinuation s := by
  rfl

/-- Equal periods and the radius-moment ratio force the exact relation
`A_C4 = 5 A_C2`. -/
theorem empiricalLeadingCutoffVector_c4_eq_five_c2 (s : ℂ) :
    empiricalLeadingCutoffVector s EmpiricalCamera.c4 =
      5 * empiricalLeadingCutoffVector s EmpiricalCamera.c2 := by
  simp [empiricalLeadingCutoffVector]
  ring

/-- At a critical-line point with nonzero Genuine derivative, the `C4` and
`C2` model-direction coordinates separate in exactly the direction that the
leading cutoff coefficients cannot see. -/
theorem empiricalClockTangentVector_c4_ne_five_c2
    {s : ℂ} (hs : s.re = (1 : ℝ) / 2)
    (hsimple : deriv genuineContinuation s ≠ 0) :
    empiricalClockTangentVector s EmpiricalCamera.c4 ≠
      5 * empiricalClockTangentVector s EmpiricalCamera.c2 := by
  intro heq
  have heq' :
      empiricalFullEvenCameraFactor 4 s * deriv genuineContinuation s =
        5 * (naturalEvenCameraFactor 4 s *
          deriv genuineContinuation s) := by
    simpa [empiricalClockTangentVector, empiricalLimitingFactor] using heq
  have hproduct :
      (empiricalFullEvenCameraFactor 4 s -
          5 * naturalEvenCameraFactor 4 s) *
        deriv genuineContinuation s = 0 := by
    linear_combination heq'
  exact (mul_ne_zero
    (empiricalFullEvenCameraFactor_four_sub_five_alignedC2_ne_zero hs)
    hsimple) hproduct

/-- The leading cutoff vector and limiting complex-derivative model direction
are not complex-collinear at a critical-line point with nonzero derivative. -/
theorem empiricalLeadingCutoffVector_not_collinear_clockTangent
    {s : ℂ} (hs : s.re = (1 : ℝ) / 2)
    (hsimple : deriv genuineContinuation s ≠ 0) :
    ¬ ∃ r : ℂ,
      empiricalClockTangentVector s =
        r • empiricalLeadingCutoffVector s := by
  rintro ⟨r, hcollinear⟩
  have hc2 := congrArg
    (fun w : EmpiricalCameraStack => w EmpiricalCamera.c2) hcollinear
  have hc4 := congrArg
    (fun w : EmpiricalCameraStack => w EmpiricalCamera.c4) hcollinear
  have hc2' :
      empiricalClockTangentVector s EmpiricalCamera.c2 =
        r • empiricalLeadingCutoffVector s EmpiricalCamera.c2 := by
    simpa using hc2
  have hc4' :
      empiricalClockTangentVector s EmpiricalCamera.c4 =
        r • empiricalLeadingCutoffVector s EmpiricalCamera.c4 := by
    simpa using hc4
  apply empiricalClockTangentVector_c4_ne_five_c2 hs hsimple
  calc
    empiricalClockTangentVector s EmpiricalCamera.c4 =
        r • empiricalLeadingCutoffVector s EmpiricalCamera.c4 := hc4'
    _ = r • (5 * empiricalLeadingCutoffVector s EmpiricalCamera.c2) := by
      rw [empiricalLeadingCutoffVector_c4_eq_five_c2]
    _ = 5 * (r • empiricalLeadingCutoffVector s EmpiricalCamera.c2) := by
      change r * (5 * empiricalLeadingCutoffVector s EmpiricalCamera.c2) =
        5 * (r * empiricalLeadingCutoffVector s EmpiricalCamera.c2)
      ring
    _ = 5 * empiricalClockTangentVector s EmpiricalCamera.c2 := by
      rw [← hc2']

/-- Squared Euclidean norm of the limiting tangent. -/
def empiricalStackKappa (s : ℂ) : ℝ :=
  ‖empiricalClockTangentVector s‖ ^ 2

/-- Hermitian pairing of the leading finite-residue vector with the limiting
complex-derivative direction. -/
def empiricalStackPairing (s : ℂ) : ℂ :=
  inner ℂ (empiricalLeadingCutoffVector s)
    (empiricalClockTangentVector s)

/-- Squared modulus of the cutoff/tangent pairing. -/
def empiricalStackAlphaSq (s : ℂ) : ℝ :=
  ‖empiricalStackPairing s‖ ^ 2

/-- Squared Euclidean norm of the leading finite-residue model vector. -/
def empiricalStackAmplitudeSq (s : ℂ) : ℝ :=
  ‖empiricalLeadingCutoffVector s‖ ^ 2

/-- Squared component of the leading finite-residue vector transverse to the
complex-derivative direction. -/
def empiricalStackRho (s : ℂ) : ℝ :=
  empiricalStackAmplitudeSq s -
    empiricalStackAlphaSq s / empiricalStackKappa s

/-- Model projection scalars packaged for the phase-uniform coercivity
algebra. -/
def empiricalStackPhaseProjectionData (s : ℂ) : PhaseProjectionData where
  kappa := empiricalStackKappa s
  rho := empiricalStackRho s
  amplitudeSq := empiricalStackAmplitudeSq s
  alphaSq := empiricalStackAlphaSq s

/-- Real projection produced by rotating the cutoff/tangent pairing through a
logarithmic phase. -/
def empiricalStackPhaseProjection (s : ℂ) (theta : ℝ) : ℝ :=
  (Complex.exp ((theta : ℂ) * Complex.I) *
    empiricalStackPairing s).re

/-- Every rotated real projection is bounded by the squared modulus stored in
the empirical Gram data. -/
theorem empiricalStackPhaseProjection_sq_le_alphaSq
    (s : ℂ) (theta : ℝ) :
    empiricalStackPhaseProjection s theta ^ 2 ≤
      empiricalStackAlphaSq s := by
  let z : ℂ := Complex.exp ((theta : ℂ) * Complex.I) *
    empiricalStackPairing s
  have hre : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
  have hsquare : |z.re| ^ 2 ≤ ‖z‖ ^ 2 := by
    nlinarith [abs_nonneg z.re, norm_nonneg z]
  have hnorm : ‖z‖ = ‖empiricalStackPairing s‖ := by
    dsimp [z]
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  simpa [empiricalStackPhaseProjection, empiricalStackAlphaSq,
    z, sq_abs, hnorm] using hsquare

/-- The Euclidean norm used by the projection algebra is exactly the
collective squared norm of the six finite-residue model coefficients.  Its
sign relative to the tail model disappears after taking norms. -/
theorem empiricalStackAmplitudeSq_critical_eq
    (time : ℝ) :
    empiricalStackAmplitudeSq (criticalLineParameter time) =
      ‖criticalLineParameter time‖ ^ 2 *
        ((132244271 : ℝ) / 1778112000) := by
  unfold empiricalStackAmplitudeSq
  rw [EuclideanSpace.norm_sq_eq]
  have hmodel := empiricalNativeTailCoefficientNormSq_eq time
  unfold empiricalNativeTailCoefficientNormSq at hmodel
  simpa only [empiricalLeadingCutoffVector_apply_eq_neg_tailCoefficient,
    norm_neg] using hmodel

/-- The leading vector is nonzero everywhere on the critical line. -/
theorem empiricalLeadingCutoffVector_ne_zero
    {s : ℂ} (hs : s.re = (1 : ℝ) / 2) :
    empiricalLeadingCutoffVector s ≠ 0 := by
  have hsne : s ≠ 0 := by
    intro hszero
    rw [hszero] at hs
    norm_num at hs
  have hpow : (4 : ℂ) ^ (-s - 2) ≠ 0 :=
    (Complex.cpow_ne_zero_iff).2 (Or.inl (by norm_num))
  have hcomponent :
      empiricalLeadingCutoffVector s EmpiricalCamera.c2 ≠ 0 := by
    simp only [empiricalLeadingCutoffVector_apply,
      EmpiricalCamera.secondRadiusMoment_c2, EmpiricalCamera.period]
    exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero hsne (by norm_num)) hpow)
  intro hzero
  apply hcomponent
  have hc2 := congrArg
    (fun w : EmpiricalCameraStack => w EmpiricalCamera.c2) hzero
  simpa using hc2

/-- A critical-line point with nonzero Genuine derivative gives a nonzero
limiting complex-derivative model vector. -/
theorem empiricalClockTangentVector_ne_zero
    {s : ℂ} (hs : s.re = (1 : ℝ) / 2)
    (hsimple : deriv genuineContinuation s ≠ 0) :
    empiricalClockTangentVector s ≠ 0 := by
  have hcomponent :
      empiricalClockTangentVector s EmpiricalCamera.c2 ≠ 0 := by
    simp only [empiricalClockTangentVector_apply, empiricalLimitingFactor]
    exact mul_ne_zero
      (naturalEvenCameraFactor_four_ne_zero_on_criticalLine hs) hsimple
  intro hzero
  apply hcomponent
  have hc2 := congrArg
    (fun w : EmpiricalCameraStack => w EmpiricalCamera.c2) hzero
  simpa using hc2

/-- Strict Cauchy--Schwarz for the empirical leading vector and tangent. -/
theorem empiricalStack_strict_cauchy_schwarz
    {s : ℂ} (hs : s.re = (1 : ℝ) / 2)
    (hsimple : deriv genuineContinuation s ≠ 0) :
    ‖empiricalStackPairing s‖ <
      ‖empiricalLeadingCutoffVector s‖ *
        ‖empiricalClockTangentVector s‖ := by
  have hA := empiricalLeadingCutoffVector_ne_zero hs
  have hV := empiricalClockTangentVector_ne_zero hs hsimple
  have hnocol :=
    empiricalLeadingCutoffVector_not_collinear_clockTangent hs hsimple
  have hne :
      ‖inner ℂ (empiricalLeadingCutoffVector s)
          (empiricalClockTangentVector s)‖ ≠
        ‖empiricalLeadingCutoffVector s‖ *
          ‖empiricalClockTangentVector s‖ := by
    intro heq
    rcases (norm_inner_eq_norm_iff hA hV).1 heq with ⟨r, _hr, hcol⟩
    exact hnocol ⟨r, hcol⟩
  unfold empiricalStackPairing
  exact lt_of_le_of_ne
    (norm_inner_le_norm (empiricalLeadingCutoffVector s)
      (empiricalClockTangentVector s)) hne

/-- The model-direction Gram scalar is strictly positive at a critical-line
point with nonzero Genuine derivative. -/
theorem empiricalStackKappa_pos
    {s : ℂ} (hs : s.re = (1 : ℝ) / 2)
    (hsimple : deriv genuineContinuation s ≠ 0) :
    0 < empiricalStackKappa s := by
  unfold empiricalStackKappa
  exact sq_pos_of_pos
    (norm_pos_iff.mpr (empiricalClockTangentVector_ne_zero hs hsimple))

/-- The leading cutoff amplitude is strictly positive on the critical
line. -/
theorem empiricalStackAmplitudeSq_pos
    {s : ℂ} (hs : s.re = (1 : ℝ) / 2) :
    0 < empiricalStackAmplitudeSq s := by
  unfold empiricalStackAmplitudeSq
  exact sq_pos_of_pos
    (norm_pos_iff.mpr (empiricalLeadingCutoffVector_ne_zero hs))

/-- The empirical stack has a strictly positive transverse projection at a
critical-line point with nonzero Genuine derivative. -/
theorem empiricalStackRho_pos
    {s : ℂ} (hs : s.re = (1 : ℝ) / 2)
    (hsimple : deriv genuineContinuation s ≠ 0) :
    0 < empiricalStackRho s := by
  have hstrict := empiricalStack_strict_cauchy_schwarz hs hsimple
  have hA0 : 0 ≤ ‖empiricalLeadingCutoffVector s‖ := norm_nonneg _
  have hV0 : 0 ≤ ‖empiricalClockTangentVector s‖ := norm_nonneg _
  have hinner0 : 0 ≤ ‖empiricalStackPairing s‖ := norm_nonneg _
  have hsquare :
      ‖empiricalStackPairing s‖ ^ 2 <
        ‖empiricalLeadingCutoffVector s‖ ^ 2 *
          ‖empiricalClockTangentVector s‖ ^ 2 := by
    nlinarith [mul_nonneg hA0 hV0]
  have hkappa := empiricalStackKappa_pos hs hsimple
  have hdiv :
      empiricalStackAlphaSq s / empiricalStackKappa s <
        empiricalStackAmplitudeSq s := by
    apply (div_lt_iff₀ hkappa).2
    simpa [empiricalStackAlphaSq, empiricalStackKappa,
      empiricalStackAmplitudeSq, mul_comm] using hsquare
  unfold empiricalStackRho
  linarith

/-- The exact empirical projection data satisfies every algebraic
admissibility condition needed by the phase-uniform floor theorem. -/
theorem empiricalStackPhaseProjectionData_isAdmissible
    {s : ℂ} (hs : s.re = (1 : ℝ) / 2)
    (hsimple : deriv genuineContinuation s ≠ 0) :
    (empiricalStackPhaseProjectionData s).IsAdmissible := by
  refine ⟨empiricalStackKappa_pos hs hsimple,
    empiricalStackRho_pos hs hsimple,
    empiricalStackAmplitudeSq_pos hs,
    sq_nonneg _, ?_⟩
  simp only [empiricalStackPhaseProjectionData, empiricalStackRho]
  ring

/-- The symbolic phase floor of the empirical stack is strictly positive at a
critical-line point with nonzero Genuine derivative. -/
theorem empiricalStackPhaseFloor_pos
    {s : ℂ} (hs : s.re = (1 : ℝ) / 2)
    (hsimple : deriv genuineContinuation s ≠ 0) :
    0 < (empiricalStackPhaseProjectionData s).phaseFloor := by
  exact PhaseProjectionData.phaseFloor_pos _
    (empiricalStackPhaseProjectionData_isAdmissible hs hsimple)

/-- The algebraic projected phase model has one strictly positive lower bound
for every logarithmic phase. -/
theorem empiricalStack_phaseCoercivity_uniform_lower_bound
    {s : ℂ} (hs : s.re = (1 : ℝ) / 2)
    (hsimple : deriv genuineContinuation s ≠ 0) (theta : ℝ) :
    (empiricalStackPhaseProjectionData s).phaseFloor ≤
      (empiricalStackPhaseProjectionData s).phaseCoercivity
        (empiricalStackPhaseProjection s theta) := by
  exact PhaseProjectionData.phaseCoercivity_uniform_lower_bound _
    (empiricalStackPhaseProjectionData_isAdmissible hs hsimple) _
    (empiricalStackPhaseProjection_sq_le_alphaSq s theta)

/-- Capstone: a critical simple Genuine zero has a strictly positive
phase-independent empirical projection remainder.  The zero hypothesis
records the spectral meaning of the point; positivity uses criticality and
simplicity. -/
theorem empiricalStack_projectionRho_pos_of_critical_simple_zero
    {s : ℂ} (hs : s.re = (1 : ℝ) / 2)
    (_hzero : genuineContinuation s = 0)
    (hsimple : deriv genuineContinuation s ≠ 0) :
    0 < empiricalStackRho s :=
  empiricalStackRho_pos hs hsimple

end

end GenuineZeroUniformAtlasEnergy

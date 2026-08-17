import GenuineZeroUniformAtlasEnergy.EmpiricalCollectiveEnergyAsymptotic
import GenuineZeroUniformAtlasEnergy.AsymptoticCoercivity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Logarithmic cutoff jets and vanishing-error coercivity

The dyadic cutoff experiments were used only to discover and independently
validate the analytic model.  The statements in this file do not depend on a
floating-point table or on a selected finite-cutoff witness.

For a positive cutoff `M`, the exact analytic scale is

```math
M^{-s-1}.
```

Differentiating this factor once and twice produces the unavoidable
`log M` and `(log M)^2` terms.  The main theorem packages the exact product
rule for an arbitrary twice differentiable scaled model.  This is the bridge
needed before transporting a three-term cutoff expansion to the first and
second jets of the native characteristic.

The file also generalizes the phase-floor passage from a special `C/M` error
to any explicitly supplied error sequence tending to zero.  This covers the
validated derivative profile once its logarithmic remainder is proved.
-/

open Filter
open scoped BigOperators

namespace GenuineZeroUniformAtlasEnergy

noncomputable section

/-- Fourth radius moment appearing in the third tested cutoff coefficient. -/
def nativeRadiusFourthMoment (h : ℕ) : ℝ :=
  ∑ radius ∈ Finset.Icc 1 h, (radius : ℝ) ^ 4

/-- Exact analytic cutoff scale. -/
def nativeCutoffScale (M : ℕ) (s : ℂ) : ℂ :=
  (M : ℂ) ^ (-s - 1)

/-- Complex logarithm carried by differentiation of the cutoff scale. -/
def nativeCutoffLog (M : ℕ) : ℂ :=
  Complex.log (M : ℂ)

/-- Second coefficient of the tested scaled cutoff-tail model.  The sign is
for the tail itself; the finite resonant characteristic is its negative. -/
def nativeExplicitRadiusTailSecondCoefficient
    (b h : ℕ) (s : ℂ) : ℂ :=
  -(s * (s + 1) / 2) *
    (nativeRadiusSecondMoment h : ℂ) *
      (b : ℂ) ^ (-s - 2)

/-- Third coefficient of the tested scaled cutoff-tail model. -/
def nativeExplicitRadiusTailThirdCoefficient
    (b h : ℕ) (s : ℂ) : ℂ :=
  (s * (s + 1) * (s + 2) / 12) *
    ((nativeRadiusSecondMoment h : ℂ) *
        (b : ℂ) ^ (-s - 2) +
      (nativeRadiusFourthMoment h : ℂ) *
        (b : ℂ) ^ (-s - 4))

/-- Three-term scaled cutoff model found by the `M -> 2M` validation.  This
definition records the candidate model; it does not by itself assert that the
exact tail has the displayed third-order remainder. -/
def nativeExplicitRadiusThreeTermScaledModel
    (b h M : ℕ) (s : ℂ) : ℂ :=
  nativeExplicitRadiusTailCoefficient b h s +
    nativeExplicitRadiusTailSecondCoefficient b h s / (M : ℂ) +
    nativeExplicitRadiusTailThirdCoefficient b h s / ((M : ℂ) ^ 2)

/-- Unscaled analytic model obtained from a scaled coefficient function. -/
def nativeCutoffModel
    (M : ℕ) (amplitude : ℂ → ℂ) (s : ℂ) : ℂ :=
  nativeCutoffScale M s * amplitude s

/-- First logarithmic jet of the unscaled model. -/
def nativeCutoffModelFirstJet
    (M : ℕ) (amplitude amplitudeFirst : ℂ → ℂ) (s : ℂ) : ℂ :=
  nativeCutoffScale M s *
    (amplitudeFirst s - nativeCutoffLog M * amplitude s)

/-- Second logarithmic jet of the unscaled model. -/
def nativeCutoffModelSecondJet
    (M : ℕ)
    (amplitude amplitudeFirst amplitudeSecond : ℂ → ℂ)
    (s : ℂ) : ℂ :=
  nativeCutoffScale M s *
    (amplitudeSecond s -
      2 * nativeCutoffLog M * amplitudeFirst s +
      nativeCutoffLog M ^ 2 * amplitude s)

lemma hasDerivAt_nativeCutoffScale
    (M : ℕ) (hM : 0 < M) (s : ℂ) :
    HasDerivAt (nativeCutoffScale M)
      (nativeCutoffScale M s * nativeCutoffLog M * (-1)) s := by
  have hinner :
      HasDerivAt (fun z : ℂ => -z - 1) (-1) s := by
    simpa using (hasDerivAt_neg' s).sub_const 1
  simpa [nativeCutoffScale, nativeCutoffLog] using
    hinner.const_cpow
      (Or.inl (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hM)))

lemma hasDerivAt_nativeCutoffModel
    (M : ℕ) (hM : 0 < M)
    {amplitude amplitudeFirst : ℂ → ℂ} {s : ℂ}
    (hAmplitude : HasDerivAt amplitude (amplitudeFirst s) s) :
    HasDerivAt (nativeCutoffModel M amplitude)
      (nativeCutoffModelFirstJet M amplitude amplitudeFirst s) s := by
  have hproduct :=
    (hasDerivAt_nativeCutoffScale M hM s).mul hAmplitude
  simpa [nativeCutoffModel, nativeCutoffModelFirstJet,
    nativeCutoffLog] using hproduct

lemma hasDerivAt_nativeCutoffModelFirstJet
    (M : ℕ) (hM : 0 < M)
    {amplitude amplitudeFirst amplitudeSecond : ℂ → ℂ} {s : ℂ}
    (hAmplitude : HasDerivAt amplitude (amplitudeFirst s) s)
    (hAmplitudeFirst : HasDerivAt amplitudeFirst (amplitudeSecond s) s) :
    HasDerivAt
      (nativeCutoffModelFirstJet M amplitude amplitudeFirst)
      (nativeCutoffModelSecondJet M amplitude amplitudeFirst
        amplitudeSecond s) s := by
  let ell : ℂ := nativeCutoffLog M
  have hinner :
      HasDerivAt
        (fun z : ℂ => amplitudeFirst z - ell * amplitude z)
        (amplitudeSecond s - ell * amplitudeFirst s) s := by
    exact hAmplitudeFirst.sub (HasDerivAt.const_mul ell hAmplitude)
  have hproduct :=
    (hasDerivAt_nativeCutoffScale M hM s).mul hinner
  simpa [nativeCutoffModelFirstJet, nativeCutoffModelSecondJet,
    ell, nativeCutoffLog] using hproduct

/-- Exact first- and second-jet bridge.  In particular, any scaled cutoff
expansion transported through `M^(-s-1)` necessarily acquires one logarithm in
the first jet and two logarithms in the second jet. -/
theorem cutoffModel_first_second_logarithmic_jets
    (M : ℕ) (hM : 0 < M)
    {amplitude amplitudeFirst amplitudeSecond : ℂ → ℂ} {s : ℂ}
    (hAmplitude : HasDerivAt amplitude (amplitudeFirst s) s)
    (hAmplitudeFirst : HasDerivAt amplitudeFirst (amplitudeSecond s) s) :
    HasDerivAt (nativeCutoffModel M amplitude)
        (nativeCutoffModelFirstJet M amplitude amplitudeFirst s) s ∧
      HasDerivAt
        (nativeCutoffModelFirstJet M amplitude amplitudeFirst)
        (nativeCutoffModelSecondJet M amplitude amplitudeFirst
          amplitudeSecond s) s := by
  exact ⟨
    hasDerivAt_nativeCutoffModel M hM hAmplitude,
    hasDerivAt_nativeCutoffModelFirstJet M hM
      hAmplitude hAmplitudeFirst⟩

namespace PhaseProjectionData

/-- A phase-uniform floor survives any explicitly controlled approximation
whose error tends to zero.  The error need not have the special form `C/M`;
this is the interface required by logarithmic derivative remainders. -/
theorem eventually_microscopicCoercivity_lower_bound_of_vanishing_error
    (d : PhaseProjectionData) (h : d.IsAdmissible)
    (phaseProjection cMicro error : ℕ → ℝ) (c : ℝ)
    (hx : ∀ M : ℕ, (phaseProjection M) ^ 2 ≤ d.alphaSq)
    (happrox : ∀ M : ℕ,
      |cMicro M - d.phaseCoercivity (phaseProjection M)| ≤ error M)
    (herror : Tendsto error atTop (nhds 0))
    (hc : c < d.phaseFloor) :
    ∀ᶠ M : ℕ in atTop, c ≤ cMicro M := by
  have hgap : 0 < d.phaseFloor - c := sub_pos.mpr hc
  have hsmall : ∀ᶠ M : ℕ in atTop,
      error M < d.phaseFloor - c :=
    herror.eventually (Iio_mem_nhds hgap)
  filter_upwards [hsmall] with M hM
  exact d.microscopicCoercivity_lower_bound_of_error h
    (phaseProjection M) (cMicro M) c (error M)
    (hx M) (happrox M) (le_of_lt hM)

/-- Conditional target-four theorem for an arbitrary vanishing approximation
error. -/
theorem eventually_microscopicCoercivity_ge_four_of_vanishing_error
    (d : PhaseProjectionData) (h : d.IsAdmissible)
    (phaseProjection cMicro error : ℕ → ℝ)
    (hx : ∀ M : ℕ, (phaseProjection M) ^ 2 ≤ d.alphaSq)
    (happrox : ∀ M : ℕ,
      |cMicro M - d.phaseCoercivity (phaseProjection M)| ≤ error M)
    (herror : Tendsto error atTop (nhds 0))
    (hfour : (4 : ℝ) < d.phaseFloor) :
    ∀ᶠ M : ℕ in atTop, (4 : ℝ) ≤ cMicro M := by
  exact d.eventually_microscopicCoercivity_lower_bound_of_vanishing_error h
    phaseProjection cMicro error 4 hx happrox herror hfour

end PhaseProjectionData

end

end GenuineZeroUniformAtlasEnergy

import GenuineZeroUniformAtlasEnergy.NativeTransverseBridge
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Concrete Hessian of the finite native raw energy

The first transverse bridge proves that the finite primitive camera is an
entire complex characteristic and that the angular tangent is the real
quarter-turn of the radial tangent. This module differentiates once more.

At a point `s = sigma + i time`, write

```math
u=\Chi(s),\qquad v=\Chi'(s),\qquad w=\Chi''(s).
```

The raw, unnormalized visibility is

```math
E(\sigma,t)=\lVert\Chi(\sigma+i t)\rVert_{\mathbb R^2}^2.
```

Its Hessian is proved to be

```math
D^2E=2\begin{pmatrix}
\kappa+a & b\\
b & \kappa-a
\end{pmatrix},
```

with

```math
\kappa=\langle v,v\rangle,\qquad
 a=\langle u,w\rangle,\qquad
 b=\langle u,Jw\rangle.
```

Thus the previously abstract `TransverseJet` is obtained directly from the
concrete finite camera derivatives. No score denominator, zero predicate, or
numerical fit enters these definitions.
-/

namespace GenuineZeroUniformAtlasEnergy

open CPFormal.Analytic.Cp

noncomputable section

/-- Second complex derivative of the finite native characteristic. -/
def finiteNativeSecondJet (p M : ℕ) (s : ℂ) : ℂ :=
  deriv (finiteNativeFirstJet p M) s

/-- The first jet is entire because the original finite characteristic is
entire. -/
lemma finiteNativeFirstJet_differentiable
    (p M : ℕ) (hp : Nat.Prime p) :
    Differentiable ℂ (finiteNativeFirstJet p M) := by
  change Differentiable ℂ (deriv (finiteNativeCharacteristic p M))
  exact (finiteNativeCharacteristic_differentiable p M hp).deriv

/-- Radial derivative of the first jet. -/
lemma finiteNativeFirstJetSlice_hasDerivAt_sigma
    (p M : ℕ) (hp : Nat.Prime p)
    (sigma time : ℝ) :
    HasDerivAt
      (fun x : ℝ =>
        finiteNativeFirstJet p M
          (nativeCarryRealPlaneParameter x time))
      (finiteNativeSecondJet p M
        (nativeCarryRealPlaneParameter sigma time)) sigma := by
  have houter :
      HasDerivAt
        (finiteNativeFirstJet p M)
        (finiteNativeSecondJet p M
          (nativeCarryRealPlaneParameter sigma time))
        (nativeCarryRealPlaneParameter sigma time) :=
    (finiteNativeFirstJet_differentiable p M hp
      (nativeCarryRealPlaneParameter sigma time)).hasDerivAt
  have hreal := houter.complexToReal_fderiv.comp_hasDerivAt sigma
    (nativeParameter_hasDerivAt_sigma sigma time)
  change HasDerivAt
    (finiteNativeFirstJet p M ∘
      fun x : ℝ => nativeCarryRealPlaneParameter x time)
    (finiteNativeSecondJet p M
      (nativeCarryRealPlaneParameter sigma time)) sigma
  simpa using hreal

/-- Angular derivative of the first jet. -/
lemma finiteNativeFirstJetSlice_hasDerivAt_time
    (p M : ℕ) (hp : Nat.Prime p)
    (sigma time : ℝ) :
    HasDerivAt
      (fun y : ℝ =>
        finiteNativeFirstJet p M
          (nativeCarryRealPlaneParameter sigma y))
      (Complex.I * finiteNativeSecondJet p M
        (nativeCarryRealPlaneParameter sigma time)) time := by
  have houter :
      HasDerivAt
        (finiteNativeFirstJet p M)
        (finiteNativeSecondJet p M
          (nativeCarryRealPlaneParameter sigma time))
        (nativeCarryRealPlaneParameter sigma time) :=
    (finiteNativeFirstJet_differentiable p M hp
      (nativeCarryRealPlaneParameter sigma time)).hasDerivAt
  have hreal := houter.complexToReal_fderiv.comp_hasDerivAt time
    (nativeParameter_hasDerivAt_time sigma time)
  change HasDerivAt
    (finiteNativeFirstJet p M ∘
      nativeCarryRealPlaneParameter sigma)
    (Complex.I * finiteNativeSecondJet p M
      (nativeCarryRealPlaneParameter sigma time)) time
  simpa [mul_comm] using hreal

/-- Real coordinates of the finite characteristic value. -/
def finiteNativeValuePlane
    (p M : ℕ) (sigma time : ℝ) : NativeCarryRealPlane :=
  complexToNativePlane (finiteNativeSlice p M sigma time)

/-- Real radial second tangent. -/
def finiteNativeSecondSigmaTangent
    (p M : ℕ) (sigma time : ℝ) : NativeCarryRealPlane :=
  complexToNativePlane
    (finiteNativeSecondJet p M
      (nativeCarryRealPlaneParameter sigma time))

/-- The concrete scalar jet supplied by the finite native characteristic. -/
def finiteNativeTransverseJet
    (p M : ℕ) (sigma time : ℝ) : TransverseJet where
  kappa :=
    nativePlaneInner
      (finiteNativeSigmaTangent p M sigma time)
      (finiteNativeSigmaTangent p M sigma time)
  a :=
    nativePlaneInner
      (finiteNativeValuePlane p M sigma time)
      (finiteNativeSecondSigmaTangent p M sigma time)
  b :=
    nativePlaneInner
      (finiteNativeValuePlane p M sigma time)
      (nativeQuarterTurn
        (finiteNativeSecondSigmaTangent p M sigma time))

/-- Raw, unnormalized finite visibility. -/
def finiteNativeRawEnergy
    (p M : ℕ) (sigma time : ℝ) : ℝ :=
  nativePlaneInner
    (finiteNativeValuePlane p M sigma time)
    (finiteNativeValuePlane p M sigma time)

/-- First radial derivative of the raw visibility. -/
def finiteNativeSigmaEnergyGradient
    (p M : ℕ) (sigma time : ℝ) : ℝ :=
  2 * nativePlaneInner
    (finiteNativeValuePlane p M sigma time)
    (finiteNativeSigmaTangent p M sigma time)

/-- First angular derivative of the raw visibility. -/
def finiteNativeTimeEnergyGradient
    (p M : ℕ) (sigma time : ℝ) : ℝ :=
  2 * nativePlaneInner
    (finiteNativeValuePlane p M sigma time)
    (finiteNativeTimeTangent p M sigma time)

/-- Extract the real-coordinate derivative of a complex-valued real curve. -/
lemma hasDerivAt_complex_re
    {f : ℝ → ℂ} {f' : ℂ} {x : ℝ}
    (hf : HasDerivAt f f' x) :
    HasDerivAt (fun y => (f y).re) f'.re x := by
  change HasDerivAt (Complex.reCLM ∘ f) (Complex.reCLM f') x
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hf

/-- The native real pairing is the real part of the conjugate product. -/
@[simp] lemma nativePlaneInner_complexToNativePlane
    (z w : ℂ) :
    nativePlaneInner
      (complexToNativePlane z)
      (complexToNativePlane w) =
        (star z * w).re := by
  simp [nativePlaneInner, complexToNativePlane]
  ring

/-- Product rule for the Euclidean pairing of two complex curves, written in
native real coordinates. The proof differentiates one complex conjugate
product before taking its real part, avoiding any choice of real module
presentation. -/
lemma hasDerivAt_nativePlaneInner_of_complex
    {f g : ℝ → ℂ} {f' g' : ℂ} {x : ℝ}
    (hf : HasDerivAt f f' x)
    (hg : HasDerivAt g g' x) :
    HasDerivAt
      (fun y =>
        nativePlaneInner
          (complexToNativePlane (f y))
          (complexToNativePlane (g y)))
      (nativePlaneInner
          (complexToNativePlane f')
          (complexToNativePlane (g x)) +
        nativePlaneInner
          (complexToNativePlane (f x))
          (complexToNativePlane g')) x := by
  have hproduct :
      HasDerivAt
        (fun y => star (f y) * g y)
        (star f' * g x + star (f x) * g') x :=
    hf.star.mul hg
  have hreal := hasDerivAt_complex_re hproduct
  simpa using hreal

/-- Derivative of the native squared norm. -/
lemma hasDerivAt_nativePlaneNormSq_of_complex
    {f : ℝ → ℂ} {f' : ℂ} {x : ℝ}
    (hf : HasDerivAt f f' x) :
    HasDerivAt
      (fun y =>
        nativePlaneInner
          (complexToNativePlane (f y))
          (complexToNativePlane (f y)))
      (2 * nativePlaneInner
        (complexToNativePlane (f x))
        (complexToNativePlane f')) x := by
  have h := hasDerivAt_nativePlaneInner_of_complex hf hf
  have hderiv :
      2 * nativePlaneInner
          (complexToNativePlane (f x))
          (complexToNativePlane f') =
        nativePlaneInner
            (complexToNativePlane f')
            (complexToNativePlane (f x)) +
          nativePlaneInner
            (complexToNativePlane (f x))
            (complexToNativePlane f') := by
    simp [nativePlaneInner, complexToNativePlane]
    ring
  rw [hderiv]
  exact h

/-- Derivative of twice the native pairing. -/
lemma hasDerivAt_two_nativePlaneInner_of_complex
    {f g : ℝ → ℂ} {f' g' : ℂ} {x : ℝ}
    (hf : HasDerivAt f f' x)
    (hg : HasDerivAt g g' x) :
    HasDerivAt
      (fun y =>
        2 * nativePlaneInner
          (complexToNativePlane (f y))
          (complexToNativePlane (g y)))
      (2 *
        (nativePlaneInner
            (complexToNativePlane f')
            (complexToNativePlane (g x)) +
          nativePlaneInner
            (complexToNativePlane (f x))
            (complexToNativePlane g'))) x := by
  exact (hasDerivAt_nativePlaneInner_of_complex hf hg).const_mul (2 : ℝ)

@[simp] lemma nativePlaneInner_quarterTurn_left_self
    (u : NativeCarryRealPlane) :
    nativePlaneInner (nativeQuarterTurn u) u = 0 := by
  rcases u with ⟨x, y⟩
  simp [nativePlaneInner, nativeQuarterTurn]
  ring

@[simp] lemma complexToNativePlane_neg (z : ℂ) :
    complexToNativePlane (-z) = -complexToNativePlane z := by
  ext <;> simp [complexToNativePlane]

@[simp] lemma nativePlaneInner_neg_right
    (u v : NativeCarryRealPlane) :
    nativePlaneInner u (-v) = -nativePlaneInner u v := by
  rcases u with ⟨ux, uy⟩
  rcases v with ⟨vx, vy⟩
  simp [nativePlaneInner]
  ring

/-- Multiplying the first jet by `i` and differentiating in time gives the
negative second radial jet. -/
lemma finiteNativeRotatedFirstJetSlice_hasDerivAt_time
    (p M : ℕ) (hp : Nat.Prime p)
    (sigma time : ℝ) :
    HasDerivAt
      (fun y : ℝ =>
        Complex.I * finiteNativeFirstJet p M
          (nativeCarryRealPlaneParameter sigma y))
      (-finiteNativeSecondJet p M
        (nativeCarryRealPlaneParameter sigma time)) time := by
  have h :=
    (finiteNativeFirstJetSlice_hasDerivAt_time
      p M hp sigma time).const_mul Complex.I
  simpa only [← mul_assoc, Complex.I_mul_I, neg_one_mul] using h

/-- The raw visibility is literally the complex squared norm. -/
lemma finiteNativeRawEnergy_eq_normSq
    (p M : ℕ) (sigma time : ℝ) :
    finiteNativeRawEnergy p M sigma time =
      Complex.normSq (finiteNativeSlice p M sigma time) := by
  simp [finiteNativeRawEnergy, finiteNativeValuePlane,
    nativePlaneInner, complexToNativePlane, Complex.normSq]

/-- Hence the raw visibility is exactly the Euclidean energy of the primitive
real camera. -/
lemma finiteNativeRawEnergy_eq_realCameraEnergy
    (p M : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (sigma time : ℝ) :
    finiteNativeRawEnergy p M sigma time =
      nativeCarryRealPlaneEnergy
        (nativeCarryRealPlaneFiniteChartAt p M sigma time) := by
  calc
    finiteNativeRawEnergy p M sigma time =
        Complex.normSq (finiteNativeSlice p M sigma time) :=
      finiteNativeRawEnergy_eq_normSq p M sigma time
    _ = Complex.normSq
        (nativeCarryRealPlaneComplexPackaging
          (nativeCarryRealPlaneFiniteChartAt p M sigma time)) := by
      rw [finiteNativeSlice_eq_packaged_realCamera
        p M hp hpodd sigma time]
    _ = nativeCarryRealPlaneEnergy
        (nativeCarryRealPlaneFiniteChartAt p M sigma time) := by
      exact normSq_nativeCarryRealPlaneComplexPackaging _

/-- First radial derivative of the raw energy. -/
lemma finiteNativeRawEnergy_hasDerivAt_sigma
    (p M : ℕ) (hp : Nat.Prime p)
    (sigma time : ℝ) :
    HasDerivAt
      (fun x : ℝ => finiteNativeRawEnergy p M x time)
      (finiteNativeSigmaEnergyGradient p M sigma time) sigma := by
  simpa [finiteNativeRawEnergy, finiteNativeSigmaEnergyGradient,
    finiteNativeValuePlane, finiteNativeSigmaTangent] using
    (hasDerivAt_nativePlaneNormSq_of_complex
      (finiteNativeSlice_hasDerivAt_sigma p M hp sigma time))

/-- First angular derivative of the raw energy. -/
lemma finiteNativeRawEnergy_hasDerivAt_time
    (p M : ℕ) (hp : Nat.Prime p)
    (sigma time : ℝ) :
    HasDerivAt
      (fun y : ℝ => finiteNativeRawEnergy p M sigma y)
      (finiteNativeTimeEnergyGradient p M sigma time) time := by
  simpa [finiteNativeRawEnergy, finiteNativeTimeEnergyGradient,
    finiteNativeValuePlane, finiteNativeTimeTangent] using
    (hasDerivAt_nativePlaneNormSq_of_complex
      (finiteNativeSlice_hasDerivAt_time p M hp sigma time))

/-- Radial-radial Hessian entry is `2(κ+a)`. -/
lemma finiteNativeSigmaEnergyGradient_hasDerivAt_sigma
    (p M : ℕ) (hp : Nat.Prime p)
    (sigma time : ℝ) :
    HasDerivAt
      (fun x : ℝ => finiteNativeSigmaEnergyGradient p M x time)
      (finiteNativeTransverseJet p M sigma time).hessian00 sigma := by
  have h := hasDerivAt_two_nativePlaneInner_of_complex
    (finiteNativeSlice_hasDerivAt_sigma p M hp sigma time)
    (finiteNativeFirstJetSlice_hasDerivAt_sigma p M hp sigma time)
  simpa [finiteNativeSigmaEnergyGradient, finiteNativeValuePlane,
    finiteNativeSigmaTangent, finiteNativeSecondSigmaTangent,
    finiteNativeTransverseJet, TransverseJet.hessian00] using h

/-- Radial-angular Hessian entry is `2b`. -/
lemma finiteNativeSigmaEnergyGradient_hasDerivAt_time
    (p M : ℕ) (hp : Nat.Prime p)
    (sigma time : ℝ) :
    HasDerivAt
      (fun y : ℝ => finiteNativeSigmaEnergyGradient p M sigma y)
      (finiteNativeTransverseJet p M sigma time).hessian01 time := by
  have h := hasDerivAt_two_nativePlaneInner_of_complex
    (finiteNativeSlice_hasDerivAt_time p M hp sigma time)
    (finiteNativeFirstJetSlice_hasDerivAt_time p M hp sigma time)
  simpa [finiteNativeSigmaEnergyGradient, finiteNativeValuePlane,
    finiteNativeSigmaTangent, finiteNativeSecondSigmaTangent,
    finiteNativeTransverseJet, TransverseJet.hessian01] using h

/-- Angular-angular Hessian entry is `2(κ-a)`. -/
lemma finiteNativeTimeEnergyGradient_hasDerivAt_time
    (p M : ℕ) (hp : Nat.Prime p)
    (sigma time : ℝ) :
    HasDerivAt
      (fun y : ℝ => finiteNativeTimeEnergyGradient p M sigma y)
      (finiteNativeTransverseJet p M sigma time).hessian11 time := by
  have h := hasDerivAt_two_nativePlaneInner_of_complex
    (finiteNativeSlice_hasDerivAt_time p M hp sigma time)
    (finiteNativeRotatedFirstJetSlice_hasDerivAt_time
      p M hp sigma time)
  simpa [finiteNativeTimeEnergyGradient, finiteNativeValuePlane,
    finiteNativeTimeTangent, finiteNativeSigmaTangent,
    finiteNativeSecondSigmaTangent, finiteNativeTransverseJet,
    TransverseJet.hessian11, sub_eq_add_neg] using h

/-- At an exact finite zero the residual coefficients `a` and `b` vanish, so
the concrete jet is the isotropic exact-zero jet. -/
lemma finiteNativeTransverseJet_eq_exactZero_of_slice_eq_zero
    (p M : ℕ) (sigma time : ℝ)
    (hzero : finiteNativeSlice p M sigma time = 0) :
    finiteNativeTransverseJet p M sigma time =
      TransverseJet.exactZero
        (nativePlaneInner
          (finiteNativeSigmaTangent p M sigma time)
          (finiteNativeSigmaTangent p M sigma time)) := by
  simp [finiteNativeTransverseJet, TransverseJet.exactZero,
    finiteNativeValuePlane, hzero, complexToNativePlane,
    nativePlaneInner]

/-- Concrete finite Hessian bridge: the real primitive camera energy is the raw
complex norm, and its first and second derivative statements are exactly the
three entries of the supplied `TransverseJet`. -/
theorem finiteNativeCamera_rawEnergy_hessian_eq_transverseJet
    (p M : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (sigma time : ℝ) :
    finiteNativeRawEnergy p M sigma time =
        nativeCarryRealPlaneEnergy
          (nativeCarryRealPlaneFiniteChartAt p M sigma time) ∧
      HasDerivAt
        (fun x : ℝ => finiteNativeRawEnergy p M x time)
        (finiteNativeSigmaEnergyGradient p M sigma time) sigma ∧
      HasDerivAt
        (fun y : ℝ => finiteNativeRawEnergy p M sigma y)
        (finiteNativeTimeEnergyGradient p M sigma time) time ∧
      HasDerivAt
        (fun x : ℝ => finiteNativeSigmaEnergyGradient p M x time)
        (finiteNativeTransverseJet p M sigma time).hessian00 sigma ∧
      HasDerivAt
        (fun y : ℝ => finiteNativeSigmaEnergyGradient p M sigma y)
        (finiteNativeTransverseJet p M sigma time).hessian01 time ∧
      HasDerivAt
        (fun y : ℝ => finiteNativeTimeEnergyGradient p M sigma y)
        (finiteNativeTransverseJet p M sigma time).hessian11 time := by
  exact ⟨
    finiteNativeRawEnergy_eq_realCameraEnergy
      p M hp hpodd sigma time,
    finiteNativeRawEnergy_hasDerivAt_sigma p M hp sigma time,
    finiteNativeRawEnergy_hasDerivAt_time p M hp sigma time,
    finiteNativeSigmaEnergyGradient_hasDerivAt_sigma
      p M hp sigma time,
    finiteNativeSigmaEnergyGradient_hasDerivAt_time
      p M hp sigma time,
    finiteNativeTimeEnergyGradient_hasDerivAt_time
      p M hp sigma time⟩

/-- A zero of the concrete primitive finite camera has isotropic Hessian,
stationary optimal clock to first order, and a double algebraic Hessian
eigenvalue. -/
theorem finiteNativeCamera_exactZero_has_isotropic_transverseHessian
    (p M : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (sigma time x y : ℝ)
    (hzero :
      nativeCarryRealPlaneFiniteChartAt p M sigma time = 0) :
    let kappa :=
      nativePlaneInner
        (finiteNativeSigmaTangent p M sigma time)
        (finiteNativeSigmaTangent p M sigma time)
    let j := finiteNativeTransverseJet p M sigma time
    j = TransverseJet.exactZero kappa ∧
      j.hessianQuadratic x y =
        2 * kappa * (x ^ 2 + y ^ 2) ∧
      j.implicitTimeSlope = 0 ∧
      j.schurEnvelopeCurvature = 2 * kappa ∧
      j.eigenvalueMinus = 2 * kappa ∧
      j.eigenvaluePlus = 2 * kappa := by
  have hslice : finiteNativeSlice p M sigma time = 0 := by
    rw [finiteNativeSlice_eq_packaged_realCamera
      p M hp hpodd sigma time, hzero]
    apply Complex.ext <;> rfl
  have hjet :=
    finiteNativeTransverseJet_eq_exactZero_of_slice_eq_zero
      p M sigma time hslice
  dsimp
  constructor
  · exact hjet
  · rw [hjet]
    simp

end

end GenuineZeroUniformAtlasEnergy

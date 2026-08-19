import GenuineZeroUniformAtlasEnergy.EmpiricalCameraOperator
import NativeCarrySpectralWeyl.Camera.HigherDerivativeTail

/-!
# Empirical camera crosswalk to the spectral-Weyl derivative tails

The six empirical cameras use exactly the aligned center and radius geometry
of `NativeCarrySpectralWeyl.Camera`: camera two has centers `4(k+1)` and radius
one, while every other label uses centers `b(k+1)` and all radii
`1,...,floor(b/2)`, including the even antipodal radius.

This module proves the equality rather than merely comparing formulas.  The
all-order Cauchy tail theorem from `native-carry-spectral-weyl` can therefore be
reused directly by the empirical stack.
-/

namespace GenuineZeroUniformAtlasEnergy

open CPFormal.Analytic.Cp

noncomputable section

/-- The empirical finite seed is literally the spectral-Weyl camera seed. -/
theorem empiricalCameraSeed_eq_spectralCameraSeed
    (camera : EmpiricalCamera) (s : ℂ) :
    empiricalCameraSeed camera s =
      NativeCarrySpectralWeyl.Camera.seedDirichletTerm camera.label s := by
  cases camera <;>
    simp [empiricalCameraSeed,
      NativeCarrySpectralWeyl.Camera.seedDirichletTerm,
      NativeCarrySpectralWeyl.Camera.dirichletValue,
      realDirichletPower,
      FiniteNativeCarryOperator.Camera.radiusSet,
      FiniteNativeCarryOperator.Camera.halfRange]

/-- Every empirical center block is literally the corresponding aligned
spectral-Weyl center block. -/
theorem empiricalCameraBlock_eq_spectralCameraBlock
    (camera : EmpiricalCamera) (index : ℕ) (s : ℂ) :
    empiricalCameraBlock camera index s =
      NativeCarrySpectralWeyl.Camera.centerBracketTerm
        camera.label s index := by
  cases camera <;>
    simp [empiricalCameraBlock,
      NativeCarrySpectralWeyl.Camera.centerBracketTerm,
      NativeCarrySpectralWeyl.Camera.centeredBracketTerm,
      NativeCarrySpectralWeyl.Camera.dirichletValue,
      realCpPairBracket, realDirichletPower,
      FiniteNativeCarryOperator.Camera.alignedCenter,
      FiniteNativeCarryOperator.Camera.radiusSet,
      FiniteNativeCarryOperator.Camera.halfRange, two_smul]

/-- Function-level equality of the infinite empirical and spectral-Weyl
characteristics. -/
theorem empiricalCameraCharacteristic_eq_spectralCameraCharacteristic
    (camera : EmpiricalCamera) :
    empiricalCameraCharacteristic camera =
      NativeCarrySpectralWeyl.Camera.bracketCharacteristic camera.label := by
  funext s
  unfold empiricalCameraCharacteristic
    NativeCarrySpectralWeyl.Camera.bracketCharacteristic
  rw [empiricalCameraSeed_eq_spectralCameraSeed]
  congr 1
  exact tsum_congr fun index =>
    empiricalCameraBlock_eq_spectralCameraBlock camera index s

/-- Function-level equality of every finite cutoff characteristic. -/
theorem finiteEmpiricalCameraCharacteristic_eq_spectralCameraCharacteristic
    (camera : EmpiricalCamera) (M : ℕ) :
    finiteEmpiricalCameraCharacteristic camera M =
      NativeCarrySpectralWeyl.Camera.finiteBracketCharacteristic
        camera.label M := by
  funext s
  unfold finiteEmpiricalCameraCharacteristic
    NativeCarrySpectralWeyl.Camera.finiteBracketCharacteristic
  rw [empiricalCameraSeed_eq_spectralCameraSeed]
  congr 1
  apply Finset.sum_congr rfl
  intro index _hindex
  exact empiricalCameraBlock_eq_spectralCameraBlock camera index s

/-- The two projects use the same critical-line parameter. -/
theorem criticalLineParameter_eq_spectralCameraNativeLine (time : ℝ) :
    criticalLineParameter time =
      NativeCarrySpectralWeyl.Camera.nativeLine time := by
  apply Complex.ext
  · simp [criticalLineParameter_re,
      NativeCarrySpectralWeyl.Camera.nativeLine_re]
  · simp [criticalLineParameter_im,
      NativeCarrySpectralWeyl.Camera.nativeLine_im]

/-- All-order derivative tail bound for one empirical camera. -/
theorem norm_iteratedDeriv_empiricalCameraCharacteristic_sub_finite_le
    (camera : EmpiricalCamera) (M order : ℕ)
    (hM : Real.exp 2 ≤ (M : ℝ)) (time : ℝ) :
    ‖iteratedDeriv order (empiricalCameraCharacteristic camera)
          (criticalLineParameter time) -
        iteratedDeriv order (finiteEmpiricalCameraCharacteristic camera M)
          (criticalLineParameter time)‖ ≤
      (order.factorial *
          NativeCarrySpectralWeyl.Camera.higherDerivativeCircleConstant
            camera.label time) *
        (M : ℝ) ^ (-(3 : ℝ) / 2) *
          (Real.log (M : ℝ)) ^ order := by
  rw [empiricalCameraCharacteristic_eq_spectralCameraCharacteristic,
    finiteEmpiricalCameraCharacteristic_eq_spectralCameraCharacteristic,
    criticalLineParameter_eq_spectralCameraNativeLine]
  exact
    NativeCarrySpectralWeyl.Camera.iteratedDeriv_bracketCharacteristic_nativeLine_tail_le
      (camera := camera.label) (cutoff := M) (order := order)
      (by cases camera <;> norm_num) hM time

end

end GenuineZeroUniformAtlasEnergy

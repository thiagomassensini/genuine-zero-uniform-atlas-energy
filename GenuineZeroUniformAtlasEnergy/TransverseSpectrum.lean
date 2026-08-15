import GenuineZeroUniformAtlasEnergy.TransverseCoercivity

/-!
# Explicit spectrum of the transverse Hessian

For the Hessian

```math
2\begin{pmatrix}
\kappa+a & b\\
b & \kappa-a
\end{pmatrix},
```

the spectral radius of the traceless correction is
`r = sqrt(a^2+b^2)`.  The two algebraic eigenvalues are therefore
`2(κ-r)` and `2(κ+r)`.  This module verifies their sum, product, and
characteristic equations without introducing any numerical approximation.
-/

namespace GenuineZeroUniformAtlasEnergy

noncomputable section

namespace TransverseJet

/-- Radius of the symmetric traceless Hessian correction. -/
def spectralRadius (j : TransverseJet) : ℝ :=
  Real.sqrt (j.a ^ 2 + j.b ^ 2)

/-- Smaller algebraic eigenvalue of the transverse Hessian. -/
def eigenvalueMinus (j : TransverseJet) : ℝ :=
  2 * (j.kappa - j.spectralRadius)

/-- Larger algebraic eigenvalue of the transverse Hessian. -/
def eigenvaluePlus (j : TransverseJet) : ℝ :=
  2 * (j.kappa + j.spectralRadius)

/-- Characteristic polynomial evaluated at a scalar. -/
def characteristicValue (j : TransverseJet) (lambda : ℝ) : ℝ :=
  lambda ^ 2 - j.hessianTrace * lambda + j.hessianDet

@[simp] lemma spectralRadius_sq (j : TransverseJet) :
    j.spectralRadius ^ 2 = j.a ^ 2 + j.b ^ 2 := by
  unfold spectralRadius
  rw [Real.sq_sqrt]
  positivity

lemma eigenvalueMinus_add_eigenvaluePlus (j : TransverseJet) :
    j.eigenvalueMinus + j.eigenvaluePlus = j.hessianTrace := by
  rw [hessianTrace_eq_four_mul_kappa]
  unfold eigenvalueMinus eigenvaluePlus
  ring

lemma eigenvalueMinus_mul_eigenvaluePlus (j : TransverseJet) :
    j.eigenvalueMinus * j.eigenvaluePlus = j.hessianDet := by
  calc
    j.eigenvalueMinus * j.eigenvaluePlus =
        4 * (j.kappa ^ 2 - j.spectralRadius ^ 2) := by
      unfold eigenvalueMinus eigenvaluePlus
      ring
    _ = 4 * j.discriminant := by
      rw [spectralRadius_sq]
      unfold discriminant
      ring
    _ = j.hessianDet := by
      exact (hessianDet_eq_four_mul_discriminant j).symm

@[simp] lemma characteristicValue_eigenvalueMinus (j : TransverseJet) :
    j.characteristicValue j.eigenvalueMinus = 0 := by
  unfold characteristicValue
  rw [← eigenvalueMinus_add_eigenvaluePlus,
    ← eigenvalueMinus_mul_eigenvaluePlus]
  ring

@[simp] lemma characteristicValue_eigenvaluePlus (j : TransverseJet) :
    j.characteristicValue j.eigenvaluePlus = 0 := by
  unfold characteristicValue
  rw [← eigenvalueMinus_add_eigenvaluePlus,
    ← eigenvalueMinus_mul_eigenvaluePlus]
  ring

@[simp] lemma exactZero_eigenvalueMinus (kappa : ℝ) :
    (exactZero kappa).eigenvalueMinus = 2 * kappa := by
  simp [eigenvalueMinus, spectralRadius, exactZero]

@[simp] lemma exactZero_eigenvaluePlus (kappa : ℝ) :
    (exactZero kappa).eigenvaluePlus = 2 * kappa := by
  simp [eigenvaluePlus, spectralRadius, exactZero]

end TransverseJet

end

end GenuineZeroUniformAtlasEnergy

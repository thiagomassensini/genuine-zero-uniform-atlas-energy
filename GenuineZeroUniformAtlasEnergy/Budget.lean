import GenuineZeroUniformAtlasEnergy.NativeGeometry
import CPFormal.Analytic.CpTfvdSeededFiniteBesselConservation

/-!
# The structural uniform atlas-energy budget

The seeded TFVD Bessel ledger is evaluated on the native parameter.  Since its
radial defect is measured from the quadratic carry amplitude itself, every
finite energy is exactly zero.  Consequently one number controls every
positive cutoff and every finite prime atlas, and its unique least value is
zero.

This budget exists before asking whether the common native/Genuine camera
vanishes.  A zero inherits the budget; it does not select the exponent.
-/

open scoped BigOperators

namespace GenuineZeroUniformAtlasEnergy

open CPFormal.Analytic.Cp

noncomputable section

/-- Seeded TFVD radial-defect energy of the native positional wave. -/
def nativeAtlasEnergy
    (M : ℕ) (time : ℝ) (S : Finset Nat.Primes) : ℝ :=
  finiteSeededTfvdBesselEnergy M (nativeParameter time) S

/-- `C` controls every finite prime atlas at every positive cutoff. -/
def IsUniformAtlasEnergyBudget (time : ℝ) (C : ℝ) : Prop :=
  ∀ M : ℕ, 0 < M → ∀ S : Finset Nat.Primes,
    nativeAtlasEnergy M time S ≤ C

/-- A budget is optimal when it is no larger than any other uniform budget. -/
def IsOptimalAtlasEnergyBudget (time : ℝ) (C : ℝ) : Prop :=
  IsUniformAtlasEnergyBudget time C ∧
    ∀ D : ℝ, IsUniformAtlasEnergyBudget time D → C ≤ D

/-- Every finite native radial-defect energy vanishes exactly. -/
@[simp] theorem nativeAtlasEnergy_eq_zero
    (M : ℕ) (time : ℝ) (S : Finset Nat.Primes) :
    nativeAtlasEnergy M time S = 0 := by
  unfold nativeAtlasEnergy finiteSeededTfvdBesselEnergy
  apply Finset.sum_eq_zero
  intro p hp
  have hobservable :
      finiteCanonicalSeededTfvdGreenRadialClosureObservable
          (p : ℕ) M 1 (fun _ => 1) (nativeParameter time) = 0 := by
    rw [
      finiteCanonicalSeededTfvdGreenRadialClosureObservable_eq_radialDifference_mul_pairing
        (p : ℕ) p.prop M (by norm_num) (fun _ => 1)
          (by intro m; norm_num) (nativeParameter time)]
    simp [criticalDisplacement, cpRadialDifference]
  rw [hobservable]
  simp

/-- Every uniform budget is nonnegative. -/
theorem uniformAtlasEnergyBudget_nonneg
    {time C : ℝ} (hC : IsUniformAtlasEnergyBudget time C) :
    0 ≤ C := by
  simpa using hC 1 (by norm_num) ∅

/-- Uniform budgets are exactly the nonnegative real numbers. -/
theorem isUniformAtlasEnergyBudget_iff_nonneg
    (time C : ℝ) :
    IsUniformAtlasEnergyBudget time C ↔ 0 ≤ C := by
  constructor
  · exact uniformAtlasEnergyBudget_nonneg
  · intro hC M _hM S
    simpa using hC

/-- Zero is the canonical least budget over the complete native atlas tower. -/
theorem zero_isOptimalAtlasEnergyBudget (time : ℝ) :
    IsOptimalAtlasEnergyBudget time 0 := by
  refine ⟨(isUniformAtlasEnergyBudget_iff_nonneg time 0).2 (le_refl 0), ?_⟩
  intro D hD
  exact uniformAtlasEnergyBudget_nonneg hD

/-- Optimal budgets, if presented twice, are equal. -/
theorem optimalAtlasEnergyBudget_unique
    {time C D : ℝ}
    (hC : IsOptimalAtlasEnergyBudget time C)
    (hD : IsOptimalAtlasEnergyBudget time D) :
    C = D := by
  exact le_antisymm (hC.2 D hD.1) (hD.2 C hC.1)

/-- A real number is the optimal native budget exactly when it is zero. -/
theorem isOptimalAtlasEnergyBudget_iff_eq_zero
    (time C : ℝ) :
    IsOptimalAtlasEnergyBudget time C ↔ C = 0 := by
  constructor
  · intro hC
    exact optimalAtlasEnergyBudget_unique hC
      (zero_isOptimalAtlasEnergyBudget time)
  · intro hC
    subst C
    exact zero_isOptimalAtlasEnergyBudget time

/-- Every native time has one and only one optimal full-atlas budget. -/
theorem existsUnique_optimalAtlasEnergyBudget (time : ℝ) :
    ∃! C : ℝ, IsOptimalAtlasEnergyBudget time C := by
  refine ⟨0, zero_isOptimalAtlasEnergyBudget time, ?_⟩
  intro C hC
  exact (isOptimalAtlasEnergyBudget_iff_eq_zero time C).1 hC

end

end GenuineZeroUniformAtlasEnergy

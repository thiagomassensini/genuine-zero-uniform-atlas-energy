import GenuineZeroUniformAtlasEnergy.Budget

/-!
# One-zero uniform-energy capstone

The budget is structural and already exists at every native time.  These
corollaries specialize it to a zero expressed either in real-camera notation
or Genuine notation.  The final theorem records the exact zero identity and
the unique budget in one statement.
-/

namespace GenuineZeroUniformAtlasEnergy

open CPFormal.Analytic.Cp

/-- A zero written in Genuine notation inherits the unique structural budget. -/
theorem genuineZero_hasUniqueUniformAtlasEnergyBudget
    (time : ℝ)
    (_hzero : genuineContinuation (nativeParameter time) = 0) :
    ∃! C : ℝ, IsOptimalAtlasEnergyBudget time C :=
  existsUnique_optimalAtlasEnergyBudget time

/-- The same zero written as closure of the native real camera inherits the
same unique structural budget. -/
theorem nativeZero_hasUniqueUniformAtlasEnergyBudget
    (time : ℝ)
    (_hzero : IsNativeCarryRealOperatorZero
      3 ((1 : ℝ) / 2) time) :
    ∃! C : ℝ, IsOptimalAtlasEnergyBudget time C :=
  existsUnique_optimalAtlasEnergyBudget time

/-- Consolidation theorem: native closure and Genuine vanishing are literally
the same zero, and their common positional geometry has exactly one optimal
budget over every positive cutoff and finite prime atlas. -/
theorem zeroIdentity_with_uniqueUniformAtlasEnergyBudget (time : ℝ) :
    (IsNativeCarryRealOperatorZero
        3 ((1 : ℝ) / 2) time ↔
      genuineContinuation (nativeParameter time) = 0) ∧
    ∃! C : ℝ, IsOptimalAtlasEnergyBudget time C :=
  ⟨nativeZero_iff_genuineZero time,
    existsUnique_optimalAtlasEnergyBudget time⟩

end GenuineZeroUniformAtlasEnergy

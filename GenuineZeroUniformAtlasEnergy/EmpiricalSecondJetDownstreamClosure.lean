import GenuineZeroUniformAtlasEnergy.EmpiricalSecondJetGateClosure

/-!
# Downstream closure of the empirical second-jet gate

The generic Schur ledger in `EmpiricalFiniteCurvatureBound` deliberately
accepts a supplied second-jet bound.  The actual empirical route no longer
needs that parameter: `EmpiricalSecondJetGateClosure` constructs a fixed
cutoff-independent six-camera bound from the exact derivative-tail theorem.

This module specializes the local Schur estimate to that canonical bound.
After this point the only remaining primitive hypothesis in the local
coercivity channel is the positive temporal denominator floor.  In particular,
no later theorem needs to rediscover or assume a finite second-jet estimate.
-/

namespace GenuineZeroUniformAtlasEnergy

open CPFormal.Analytic.Cp

noncomputable section

/-- Concrete local-coercivity error with the second-jet input replaced by the
canonical cutoff-independent empirical bound. -/
def empiricalFiniteLocalCoercivityClosedSecondJetErrorBound
    (M : ℕ) (time denominatorFloor : ℝ) : ℝ :=
  empiricalFiniteLocalCoercivityErrorBound M time
    (empiricalUniformSecondJetStackBound time) denominatorFloor

/-- The actual finite local Schur coefficient requires no external second-jet
hypothesis.  The remaining supplied datum is exactly the denominator floor
scheduled for Gate 2. -/
theorem abs_finiteEmpiricalLocalCoercivity_sub_model_le_closedSecondJet
    (M : ℕ) (hM : Real.exp 2 ≤ (M : ℝ))
    (time denominatorFloor : ℝ)
    (hzero : genuineContinuation (criticalLineParameter time) = 0)
    (hdenominatorFloorPos : 0 < denominatorFloor)
    (hdenominatorFloor :
      denominatorFloor ≤
        |(finiteEmpiricalTransverseJet M time).kappa -
          (finiteEmpiricalTransverseJet M time).a|) :
    |finiteEmpiricalLocalCoercivity M time -
        empiricalStackKappa (criticalLineParameter time)| ≤
      empiricalFiniteLocalCoercivityClosedSecondJetErrorBound
        M time denominatorFloor := by
  have hMOne : 1 ≤ M := by
    have hone : (1 : ℝ) < Real.exp 2 :=
      Real.one_lt_exp_iff.mpr (by norm_num)
    have hMlt : 1 < M := by
      exact_mod_cast hone.trans_le hM
    exact Nat.le_of_lt hMlt
  have hsecond :=
    norm_finiteEmpiricalCameraSecondDerivativeStack_le_uniform M hM time
  exact
    abs_finiteEmpiricalLocalCoercivity_sub_model_le
      M hMOne time (empiricalUniformSecondJetStackBound time)
      denominatorFloor hzero hsecond hdenominatorFloorPos hdenominatorFloor

end

end GenuineZeroUniformAtlasEnergy

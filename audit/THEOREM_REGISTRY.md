# Theorem Registry

The current post-`0.6.0` development surface contains 135 local public
theorems. Their canonical order and qualified Lean names are stored in
[`theorem-registry.json`](theorem-registry.json).

The registry is checked against:

- declarations in `NativeGeometry.lean`, `Budget.lean`, `TiltedCenter.lean`,
  `Capstone.lean`, `TransverseCapstone.lean`, `NativeTransverseBridge.lean`,
  `NativeTransverseHessian.lean`, `NativeCutoffTail.lean`,
  `EmpiricalCameraGeometry.lean`, `EmpiricalCameraOperator.lean`,
  `NativeCutoffAsymptotic.lean`, `AsymptoticCoercivity.lean`,
  `EmpiricalStackProjection.lean`, `EmpiricalFullEvenContinuation.lean`,
  `UniformCoercivityOn.lean`, and `NativeCutoffGlobalRemainder.lean`;
- the ordered `#print axioms` commands in `Audit.lean`;
- complete claim-ledger coverage.

The abstract transverse support modules concentrate seven public algebraic
capstones in `TransverseCapstone.lean`. The concrete bridge contributes three
capstones: finite camera tangent geometry, raw-energy Hessian identification,
and exact-zero isotropy. `NativeCutoffTail.lean` adds the exact resonant
cutoff-tail identity together with the explicit critical-line amplitude and
raw-energy decay bounds. The release adds 96 audited declarations covering the
faithful six-camera geometry and operator, local Taylor remainder, leading
phase model, symbolic projected floor, full-even continuation, and conditional
global and regional limit passage.
`NativeCutoffGlobalRemainder.lean` adds the explicit `M^(-5/2)` bounds for the
accumulated local Taylor remainder and for the complete named tail remainder,
together with the scaled cutoff-tail error bound `K/M`.

CI checks the declaration count and order, the matching `Audit.lean` reports,
and complete claim-ledger coverage.

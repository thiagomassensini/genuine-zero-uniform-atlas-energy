# Theorem Registry

Release `0.5.0` plus the current cutoff-tail draft contains 36 local public
theorems. Their canonical order and qualified Lean names are stored in
[`theorem-registry.json`](theorem-registry.json).

The registry is checked against:

- declarations in `NativeGeometry.lean`, `Budget.lean`, `TiltedCenter.lean`,
  `Capstone.lean`, `TransverseCapstone.lean`, `NativeTransverseBridge.lean`,
  `NativeTransverseHessian.lean`, and `NativeCutoffTail.lean`;
- the ordered `#print axioms` commands in `Audit.lean`;
- complete claim-ledger coverage.

The abstract transverse support modules concentrate seven public algebraic
capstones in `TransverseCapstone.lean`. The concrete bridge contributes three
capstones: finite camera tangent geometry, raw-energy Hessian identification,
and exact-zero isotropy. `NativeCutoffTail.lean` adds the exact resonant
cutoff-tail identity together with the explicit critical-line amplitude and
raw-energy decay bounds.

CI fails if any surface diverges.

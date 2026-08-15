# Theorem Registry

Release candidate `0.4.0` contains 35 local public theorems. Their canonical
order and qualified Lean names are stored in
[`theorem-registry.json`](theorem-registry.json).

The registry is checked against:

- declarations in `NativeGeometry.lean`, `Budget.lean`, `TiltedCenter.lean`,
  `Capstone.lean`, `TransverseCapstone.lean`, `NativeTransverseBridge.lean`,
  and `NativeTransverseHessian.lean`;
- the ordered `#print axioms` commands in `Audit.lean`;
- complete claim-ledger coverage.

The abstract transverse support modules concentrate seven public algebraic
capstones in `TransverseCapstone.lean`. The concrete bridge contributes three
additional capstones: finite camera tangent geometry, raw-energy Hessian
identification, and exact-zero isotropy.

CI fails if any surface diverges.

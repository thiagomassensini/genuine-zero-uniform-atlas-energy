# Theorem Registry

Release `0.7.0` contains 138 local public theorems. The locked `0.6.0` base
surface remains in [`theorem-registry.json`](theorem-registry.json); the three
new declarations are appended, without renumbering history, in
[`theorem-registry-0.7.0.json`](theorem-registry-0.7.0.json).

The combined registry is checked against:

- declarations in `NativeGeometry.lean`, `Budget.lean`, `TiltedCenter.lean`,
  `Capstone.lean`, `TransverseCapstone.lean`, `NativeTransverseBridge.lean`,
  `NativeTransverseHessian.lean`, `NativeCutoffTail.lean`,
  `EmpiricalCameraGeometry.lean`, `EmpiricalCameraOperator.lean`,
  `NativeCutoffAsymptotic.lean`, `AsymptoticCoercivity.lean`,
  `EmpiricalStackProjection.lean`, `EmpiricalFullEvenContinuation.lean`,
  `UniformCoercivityOn.lean`, `NativeCutoffGlobalRemainder.lean`, and
  `EmpiricalCollectiveEnergyAsymptotic.lean`;
- the ordered `#print axioms` commands in `Audit.lean`;
- complete claim-ledger coverage.

The `0.7.0` extension records the exact critical scaling of the collective
tail energy, its explicit `O_t(M^(-4))` raw-energy remainder, and the
common-resonance finite-energy expansion with rational six-camera leading
coefficient `132244271/1778112000`.

CI checks the combined declaration count and order, the matching `Audit.lean`
reports, release metadata, and complete claim-ledger coverage.

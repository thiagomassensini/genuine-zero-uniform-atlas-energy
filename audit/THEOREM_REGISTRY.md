# Theorem Registry

Release candidate `0.4.0` contains 25 local public theorems. Their canonical
order and qualified Lean names are stored in
[`theorem-registry.json`](theorem-registry.json).

The registry is checked against:

- declarations in `NativeGeometry.lean`, `Budget.lean`, `TiltedCenter.lean`,
  and `Capstone.lean`;
- the ordered `#print axioms` commands in `Audit.lean`;
- complete claim-ledger coverage.

CI fails if any surface diverges.

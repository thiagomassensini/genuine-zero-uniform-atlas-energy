# Theorem Registry

Release candidate `0.4.0` contains 32 local public theorems. Their canonical
order and qualified Lean names are stored in
[`theorem-registry.json`](theorem-registry.json).

The registry is checked against:

- declarations in `NativeGeometry.lean`, `Budget.lean`, `TiltedCenter.lean`,
  `Capstone.lean`, and `TransverseCapstone.lean`;
- the ordered `#print axioms` commands in `Audit.lean`;
- complete claim-ledger coverage.

The transverse support modules contain definitions and internal lemmas; their
seven public capstones are deliberately concentrated in
`TransverseCapstone.lean` so the audited claim surface stays explicit.

CI fails if any surface diverges.

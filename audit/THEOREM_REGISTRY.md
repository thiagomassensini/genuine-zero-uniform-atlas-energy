# Theorem Registry

Release `0.12.0` contains 156 ordered public theorem reports. The locked
`0.6.0` base surface remains in
[`theorem-registry.json`](theorem-registry.json). The current cumulative
extension is
[`theorem-registry-0.12.0.json`](theorem-registry-0.12.0.json); the historical
`0.7.0` through `0.11.0` extensions are retained for provenance and are not
renumbered.

The combined registry is checked against declarations in every public module,
including `NativeCutoffExactScaledTailCauchy.lean` and
`EmpiricalLimitConfinement.lean`; against the ordered `#print axioms` commands
in `Audit.lean`; and against complete claim-ledger coverage.

The `0.12.0` cumulative extension preserves the same 21 post-`0.6.0` public
reports already present in `0.11.0`. Version `0.12.0` adds no new theorem IDs:
`FinalConfinementProbe.lean` and `ArithmeticReadoutBridge.lean` are deliberately
lateral audit/comparison surfaces rather than promoted public claims. This
keeps the registry from disguising an equivalent frontier formulation as a new
confinement theorem.

The empirical cutoff campaigns remain discovery and reproducibility
provenance only. The concrete pointwise-limit gap is closed; the remaining
native-first quantitative frontier is the eventual positive finite coercivity
certificate. The `0.12.0` packaging additionally locks the exact dependency
graph used by GitHub Actions and corrects GitHub math rendering in the README.

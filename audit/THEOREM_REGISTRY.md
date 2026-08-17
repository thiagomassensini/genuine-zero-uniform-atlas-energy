# Theorem Registry

Release `0.8.0` contains 141 local public theorems. The locked `0.6.0` base
surface remains in [`theorem-registry.json`](theorem-registry.json). The
current cumulative extension is
[`theorem-registry-0.8.0.json`](theorem-registry-0.8.0.json); the historical
`0.7.0` extension is retained for provenance and is not renumbered.

The combined registry is checked against declarations in all public modules,
including `NativeCutoffGlobalRemainder.lean`,
`EmpiricalCollectiveEnergyAsymptotic.lean`, and
`NativeCutoffLogJet.lean`; the ordered `#print axioms` commands in
`Audit.lean`; and complete claim-ledger coverage.

The `0.8.0` extension retains the three collective-energy capstones from
`0.7.0` and adds the exact first/second logarithmic cutoff-jet bridge plus the
general vanishing-error transport of the symbolic phase floor.

The empirical cutoff-doubling campaign is discovery and reproducibility
provenance only. CI does not use its floating-point results as theorem
premises or as a publication gate.

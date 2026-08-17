# Theorem Registry

Release `0.9.0` contains 144 local public theorems. The locked `0.6.0` base
surface remains in [`theorem-registry.json`](theorem-registry.json). The
current cumulative extension is
[`theorem-registry-0.9.0.json`](theorem-registry-0.9.0.json); the historical
`0.7.0` and `0.8.0` extensions are retained for provenance and are not
renumbered.

The combined registry is checked against declarations in all public modules,
including `NativeCutoffGlobalRemainder.lean`,
`EmpiricalCollectiveEnergyAsymptotic.lean`, `NativeCutoffLogJet.lean`, and
`NativeCutoffDifferentiatedRemainder.lean`; the ordered `#print axioms`
commands in `Audit.lean`; and complete claim-ledger coverage.

The `0.9.0` extension retains the six capstones accumulated through `0.8.0`
and adds three differentiated-remainder transport theorems. They convert
supplied scaled value/first/second derivative bounds into exact first- and
second-cutoff-jet error bounds with factors `1 + ||log M||` and
`(1 + ||log M||)^2`.

The empirical cutoff-doubling campaign is discovery and reproducibility
provenance only. CI does not use its floating-point results as theorem
premises or as a publication gate. The analytic production of the three
remainder bounds for the exact tail remains explicitly outside the current
claim surface.

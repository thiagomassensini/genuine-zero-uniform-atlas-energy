# Release manifest 0.16.0

Version `0.16.0` closes the concrete finite microscopic-positivity gate in the
presented simple-zero sector while retaining the promoted theorem registry and
claim ledger from `0.12.0`.

The release manifest records this distinction mechanically:

- software release: `0.16.0`;
- theorem registry snapshot: `0.12.0`;
- claim ledger snapshot: `0.12.0`;
- promoted theorem count: `156`;
- promoted claim count: `24`.

The new modules are compiled by the full public library and trust audit:

- `EmpiricalDenominatorFloors`;
- `EmpiricalEnergyLocalGateClosure`;
- `EmpiricalNonJetGateClosure`;
- `EmpiricalMicroscopicPositiveGate`.

The release proves fixed inverse-cutoff first-jet and non-jet controls,
eventual positive denominator and corrected-energy floors, and eventual
positivity of the finite corrected microscopic coefficient at every presented
critical simple zero. It does not relabel arbitrary multiplicity,
compact-complement nonvanishing, exact regional coverage, or global strip-wide
stitching as discharged claims.

# Release manifest 0.13.0

Version `0.13.0` adds public-build-checked microscopic coercivity modules while
retaining the promoted theorem registry and claim ledger from `0.12.0`.

The release manifest records this distinction mechanically:

- software release: `0.13.0`;
- theorem registry snapshot: `0.12.0`;
- claim ledger snapshot: `0.12.0`;
- promoted theorem count: `156`;
- promoted claim count: `24`.

The new bridge is not omitted from validation. It is compiled by the canonical
bridge target, the full public library, and the ordered trust audit. It is
merely not mislabeled as a newly discharged unconditional confinement claim.

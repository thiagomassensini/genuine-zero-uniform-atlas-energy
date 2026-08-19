# Theorem registry status

Release `0.13.0` keeps the promoted theorem registry frozen at the audited
`0.12.0` snapshot.

- promoted theorem IDs: `GZUAE-001` through `GZUAE-156`;
- promoted claims: `24`;
- dependency lock: unchanged;
- new `0.13.0` modules: compiled through the public library and trust audit,
  but not promoted as a new unconditional confinement claim.

This separation is intentional. The microscopic coercivity bridge exposes
concrete sufficient obligations and removes a historical abstract threshold,
while the remaining uniform finite-jet bounds, denominator floors, and
compact-region coverage are still visible gates.

The machine-readable mapping is recorded in
`audit/release-manifest-0.13.0.json`. Historical registry files remain
immutable so a release cannot silently rewrite the theorem and claim surface
that earlier Zenodo records cited.

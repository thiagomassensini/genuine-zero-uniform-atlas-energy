# Theorem registry status

Release `0.15.0` keeps the promoted theorem registry frozen at the audited
`0.12.0` snapshot.

- promoted theorem IDs: `GZUAE-001` through `GZUAE-156`;
- promoted claims: `24`;
- dependency lock: unchanged;
- new `0.15.0` modules: compiled through the public library and trust audit,
  but not promoted as a new unconditional confinement claim.

This separation is intentional. Version `0.15.0` completes the quantitative
second-jet gate by producing fixed inverse-cutoff tail and curvature bounds and
removing the external second-jet premise from the concrete Schur route. The
remaining denominator floors, non-jet fixed constants, concrete local
positivity, and compact-region coverage stay visible obligations for
subsequent work.

The machine-readable mapping is recorded in
`audit/release-manifest-0.15.0.json`. Historical registry files remain
immutable so a software release cannot silently rewrite the theorem and claim
surface cited by earlier Zenodo records.

# Release manifest 0.15.0

Version `0.15.0` completes the quantitative second-jet gate while retaining the
promoted theorem registry and claim ledger from `0.12.0`.

The release manifest records this distinction mechanically:

- software release: `0.15.0`;
- theorem registry snapshot: `0.12.0`;
- claim ledger snapshot: `0.12.0`;
- promoted theorem count: `156`;
- promoted claim count: `24`.

The new modules are not omitted from validation. They are compiled by the full
public library and trust audit:

- `EmpiricalSecondJetGateClosure`;
- `EmpiricalSecondJetDownstreamClosure`.

The release proves fixed inverse-cutoff second-jet and curvature bounds and
removes the external second-jet premise from the concrete local Schur route. It
does not relabel the remaining denominator floors, non-jet perturbation
constants, local positivity, or compact-region stitching as discharged claims.

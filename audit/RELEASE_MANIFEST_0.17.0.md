# Release manifest 0.17.0

Version `0.17.0` closes the qualitative local near-axis gate at arbitrary
positive finite analytic multiplicity while retaining the promoted theorem
registry and claim ledger from `0.12.0`.

The release manifest records this distinction mechanically:

- software release: `0.17.0`;
- theorem registry snapshot: `0.12.0`;
- claim ledger snapshot: `0.12.0`;
- promoted theorem count: `156`;
- promoted claim count: `24`.

The public library and trust audit compile the new
`GenuineNearAxisMultiplicity` module and the extended
`FinalConfinementProbe`.

The release proves that every critical Genuine zero carrying arbitrary
positive finite multiplicity is isolated, selects a positive punctured
horizontal nonvanishing radius at every such center, and packages the union of
those windows. It also proves that near-axis nonvanishing together with
nonvanishing on the complementary off-critical strip yields final
confinement.

It does not provide the complement certificate and does not relabel the
conditional stitching theorem as unconditional global confinement.

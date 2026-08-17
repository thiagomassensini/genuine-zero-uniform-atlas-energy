# v0.12.0 — Native-first confinement frontier audit

Version `0.12.0` preserves the Genuine-first/native-first architecture while
consolidating the exact final-confinement frontier already exposed by the
kernel-checked carry, cutoff, Green, and energy development.

## Native-first scope

The foundational route remains independent of later classical identifications:

```math
\text{carry depth}
\longrightarrow b^{-k}
\longrightarrow b^{-k/2}
\longrightarrow \sigma=\frac12.
```

The half-abscissa is the quadratic-amplitude law of the positional carry
geometry and is camera-invariant. Prime-specific or classical analytic
comparisons are not used as foundational premises of this release.

## Frontier audit

The release includes `FinalConfinementProbe.lean`, which records the exact
logical strength of several later confinement formulations. In particular, it
prevents a Green-kernel, global-state, smoothing, or readout-domain condition
from being silently reused as if it were a weaker independent hypothesis when
it is already equivalent to the final strong nonvanishing statement.

The existing empirical-energy bridge remains a valid sufficient route:

```math
\exists c>0,\quad
\forall^{\infty}M,\quad
E_M(\sigma,t)\ge c\left(\sigma-\frac12\right)^2
```

on the certified region implies that every Genuine zero in that region has
`Re(s)=1/2`. The concrete finite-to-limit energy passage and the
zero-to-limit-energy implication remain kernel-checked.

## Canonical readout comparison

`ArithmeticReadoutBridge.lean` imports the already formalized canonical
nonlocal readout and verifies its closedness, self-adjointness, maximal
Green-isotropic graph, and exact logical comparison with scalar confinement.
This module is deliberately a lateral audit surface. It does not replace the
native carry-geometric route and does not promote readout-domain membership to
an unconditional theorem.

## GitHub math rendering

The README characteristic symbol now uses the GitHub-supported display
notation

```math
\mathrm{X}_{p,M}(s)
```

for the characteristic called `Chi` in the formal development. This removes
the unsupported `\Chi` macro that GitHub displayed as raw red text while
leaving the mathematics unchanged.

## Reproducibility

The release is validated only by GitHub Actions. The audit checks the exact
checkout, resolves the pinned dependency graph, compiles the readout/frontier
modules, runs the static Markdown/publication audit, builds the public library
with warnings as errors, builds the ordered kernel audit, and checks the
foundational axiom allowlist.

No floating-point witness is imported into the Lean proof kernel.

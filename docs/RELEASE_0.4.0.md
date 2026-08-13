# Genuine Zero Uniform Atlas Energy v0.4.0

## Corrected foundation

This release pins CPFormal `v0.62.0`, where a native zero is literal camera
closure and quadratic mass compatibility remains a separate, prior fact. The
dependency resolves to commit
`537028681ae6a775c083a1e2fb6e67db24697b82`.

## Off-equilibrium capstone

The new theorem
`genuineZero_offEquilibrium_telescopes_boundary_and_exposes_tiltedCenter`
states that for a prime camera `p` and a presented Genuine zero `s` in the
open strip with `Re(s) ≠ 1/2`:

```math
\mathcal B_M(s)\longrightarrow0,
```

```math
\mathcal C_{p,M}(s)\ne0\qquad\text{for every }M>0,
```

and

```math
\mathcal F_{p,M}(s)\not\longrightarrow0.
```

The theorem does not assert that an off-equilibrium zero exists. It records
the exact consequence if one is presented: the zero remains a zero, its legs
still telescope, and the surviving Green center exposes the tilt.

## Logical content

No new zero predicate, bridge structure, or analytic hypothesis is introduced.
The proof composes three existing kernel-checked results:

- boundary telescoping at every Genuine zero in the strip;
- strict positivity of the pairing, which makes the center nonzero away from
  `Re(s) = 1/2`;
- equivalence between total Green-flux closure and zero critical displacement
  at a Genuine zero.

The native-line theorem remains the balanced specialization: at
`s = 1/2 + i t`, boundary, center, tilt, branch defect, and total flux close.

## Audit

- 25 public theorem dependency reports;
- 5 claims marked `KERNEL_CHECKED`;
- exact CPFormal and Mathlib commit locks;
- no local `sorry`, `admit`, `axiom`, or `unsafe` declaration;
- foundational allowlist restricted to `propext`, `Classical.choice`, and
  `Quot.sound`;
- GitHub-friendly Markdown and synchronized publication metadata.

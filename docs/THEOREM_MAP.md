# Theorem Map

## Native geometry and zero identity

| Lean declaration | Mathematical content |
| --- | --- |
| `quadraticCarryShell_energy_eq_mass_iff` | In every base and positive depth, for every real angle, quadratic shell energy equals carry mass exactly at `sigma = 1/2`. |
| `nativeParameter_re` | The native radial coordinate is `1/2`. |
| `nativeParameter_im` | The native phase coordinate is the real time. |
| `nativeParameter_mem_genuineCriticalStrip` | Every native parameter lies in the open strip. |
| `nativeAmplitude_energy_eq_inverseCarryMass` | The native quadratic energy is inverse carry mass, independently of time. |
| `packagedNativeFiniteChart_eq_genuineFiniteChart` | Every finite real native chart is literally the packaged Genuine chart. |
| `nativeZero_iff_genuineZero` | Native closure and Genuine vanishing are the same zero predicate. |

## Uniform energy budget

| Lean declaration | Mathematical content |
| --- | --- |
| `nativeAtlasEnergy_eq_zero` | Every native finite radial-defect atlas energy is zero. |
| `uniformAtlasEnergyBudget_nonneg` | Every full-tower budget is nonnegative. |
| `isUniformAtlasEnergyBudget_iff_nonneg` | Uniform budgets are exactly the nonnegative reals. |
| `zero_isOptimalAtlasEnergyBudget` | Zero is the least full-tower budget. |
| `optimalAtlasEnergyBudget_unique` | Any two optimal budgets coincide. |
| `isOptimalAtlasEnergyBudget_iff_eq_zero` | Optimality characterizes zero exactly. |
| `existsUnique_optimalAtlasEnergyBudget` | Every native time has a unique optimal budget. |

## Tilted center after boundary telescoping

| Lean declaration | Mathematical content |
| --- | --- |
| `finiteTiltedCenter_eq_radialDifference_mul_pairing` | Total coupled flux minus its signed boundary is exactly the radial carry difference times the reflected pairing. |
| `finiteTiltedCenter_eq_zero_iff_re_eq_half` | The surviving center vanishes exactly on the critical half-abscissa. |
| `finiteTiltedCenter_eq_zero_iff_carryTilt_eq_zero` | At positive cutoff in the strip, the surviving center vanishes exactly when the carry tilt vanishes. |
| `finiteTiltedCenter_eq_zero_iff_quadraticBranchDefect_eq_zero` | The tilted-center and quadratic branch-defect zero loci coincide. |
| `finiteTiltedCenter_ne_zero_of_carryTilt_ne_zero` | A nonzero tilt is detected by a nonzero center at every nonempty cutoff. |
| `totalFlux_closes_iff_carryTilt_balanced_at_commonZero` | Once the common-zero boundary telescopes, total flux closure is equivalent to tilt balance. |
| `nativeGenuineZero_telescopes_boundary_and_balances_tiltedCenter` | At the native/Genuine zero, boundary, center, tilt, quadratic defect, and total coupled flux close together. |

## Common-zero capstone

| Lean declaration | Mathematical content |
| --- | --- |
| `genuineZero_hasUniqueUniformAtlasEnergyBudget` | A zero written in Genuine notation inherits the structural budget. |
| `nativeZero_hasUniqueUniformAtlasEnergyBudget` | The identical zero written as native closure inherits the same budget. |
| `zeroIdentity_with_uniqueUniformAtlasEnergyBudget` | One statement records the exact zero identity and unique full-atlas budget. |

The authoritative machine-readable order is
[`audit/theorem-registry.json`](../audit/theorem-registry.json).

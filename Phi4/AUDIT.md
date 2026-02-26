# Phi4 Systematic Policy Audit

Date: 2026-02-26

## Scope

- Audited all Lean files under `Phi4/`.
- Core modules: `21` files (excluding `Phi4/Scratch/`).
- Scratch modules: `93` files.

Policy basis (from `agent.md`):
1. no `axiom`,
2. no `def := by sorry`,
3. open gaps are theorem-level `sorry`,
4. avoid hiding open gaps in `...Model` interfaces.

## Global Policy Checks

- `axiom` declarations in `Phi4/**/*.lean`: **0**
- `def/abbrev := by sorry` in `Phi4/**/*.lean`: **0**
- theorem-level `sorry` count (core): **9**
- theorem-level `sorry` count (scratch): **16**
- `class ...Model` declarations in `Phi4/**/*.lean`: **38**

## Core Theorem-Level Gap Inventory

- `Phi4/InfiniteVolumeLimit.lean`
  - `gap_infiniteVolumeSchwingerModel_nonempty`
- `Phi4/Regularity.lean`
  - `gap_generating_functional_bound`
  - `gap_nonlocal_phi4_bound`
  - `gap_generating_functional_bound_uniform`
- `Phi4/OSAxioms.lean`
  - `gap_osaCoreModel_nonempty`
  - `gap_osDistributionE2_nonempty`
  - `gap_osE4Cluster_nonempty`
- `Phi4/Reconstruction.lean`
  - `phi4_linear_growth`
  - `phi4_wightman_reconstruction_step`

`Phi4/HonestGaps.lean` now forwards to these core frontier theorems and has no
local `sorry`.

## Mathematical/Physics Soundness Findings

### High

1. Large proof debt remains behind interface assumptions (`...Model`) in core construction layers (`Interaction`, `FiniteVolumeMeasure`, `CorrelationInequalities`, `ReflectionPositivity`, `MultipleReflections`, `InfiniteVolumeLimit`, `OSAxioms`, `Reconstruction`).

### Medium

1. FKG monotonicity statements were tightened in this audit pass: connected two-point nonnegativity now explicitly requires nonnegative test functions (`f, g ≥ 0`), removing an over-strong earlier statement.
2. The monotonicity order used in FKG interfaces is still abstract and not yet identified with a fully internalized lattice/field order construction; this remains a closure task.
3. Upstream OS reconstruction bridge theorem `os_to_wightman` (OSReconstruction) currently depends on `sorryAx`; by project policy it cannot be used to discharge `phi4_wightman_reconstruction_step` yet.
4. New constructive infrastructure was added in `InfiniteVolumeLimit.lean` for exhausting-sequence convergence in the two-point channel (including lattice and `k = 2` `schwingerN` variants), removing a previously external boundedness hypothesis in that local convergence path.

### Low

1. Honest gap surface is now explicit and localized: no def-level placeholders, no explicit axioms.

## Core File Matrix

Columns:
- `MC`: `class ...Model` declarations
- `MA`: model-assumption occurrences in typeclass binder syntax (`[...]`)
- `FW`: direct model forwarders (`exact ...Model...`)
- `S`: code-level `sorry` lines (`^\s*sorry`)

| File | MC | MA | FW | S |
|---|---:|---:|---:|---:|
| `Phi4/Bessel/BesselK0.lean` | 0 | 0 | 0 | 0 |
| `Phi4/Bessel/BesselK1.lean` | 0 | 0 | 0 | 0 |
| `Phi4/Combinatorics/PerfectMatchings.lean` | 0 | 0 | 0 | 0 |
| `Phi4/CorrelationInequalities.lean` | 7 | 44 | 5 | 0 |
| `Phi4/CovarianceOperators.lean` | 4 | 21 | 0 | 0 |
| `Phi4/Defs.lean` | 0 | 0 | 0 | 0 |
| `Phi4/FeynmanGraphs.lean` | 3 | 4 | 3 | 0 |
| `Phi4/FiniteVolumeMeasure.lean` | 1 | 23 | 1 | 0 |
| `Phi4/FreeField.lean` | 1 | 3 | 1 | 0 |
| `Phi4/GreenFunction/PeriodicKernel.lean` | 0 | 0 | 0 | 0 |
| `Phi4/HonestGaps.lean` | 0 | 7 | 0 | 0 |
| `Phi4/InfiniteVolumeLimit.lean` | 3 | 117 | 2 | 1 |
| `Phi4/Interaction.lean` | 3 | 11 | 5 | 0 |
| `Phi4/LatticeApproximation.lean` | 0 | 0 | 0 | 0 |
| `Phi4/ModelBundle.lean` | 1 | 59 | 0 | 0 |
| `Phi4/MultipleReflections.lean` | 1 | 4 | 4 | 0 |
| `Phi4/OSAxioms.lean` | 4 | 30 | 1 | 3 |
| `Phi4/Reconstruction.lean` | 5 | 97 | 4 | 2 |
| `Phi4/ReflectionPositivity.lean` | 3 | 5 | 3 | 0 |
| `Phi4/Regularity.lean` | 2 | 23 | 4 | 3 |
| `Phi4/WickProduct.lean` | 0 | 0 | 0 | 0 |

## Scratch Summary

- `93` scratch files audited.
- `axiom`: `0`.
- `def := by sorry`: `0`.
- theorem-level `sorry`: `16`.

## Verification Commands

```bash
scripts/check_phi4_trust.sh
lake build Phi4
rg -n "^\s*axiom\b" Phi4 --glob '*.lean'
grep -RIn "^[[:space:]]*sorry\b" Phi4 --include='*.lean'
```

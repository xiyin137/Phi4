# Phi4 Systematic Policy Audit

Date: 2026-02-26

Update (2026-02-27):
- Automated trust audit now reports theorem-level `sorry` count (core): `0`.
- Trusted interface/bundle endpoints remain `sorryAx`-free.
- The OS→Wightman upstream adapter is isolated in `Phi4/ReconstructionUpstream.lean`.

Update (2026-02-28):
- Re-audited with current tree state:
  - Lean files under `Phi4/`: `118` total (`23` core, `95` scratch).
  - `class ...Model` declarations in `Phi4/**/*.lean`: `58` (previous `38` count in this file is stale).
  - Core theorem-level `sorry`: `0`; scratch theorem-level `sorry`: `0`; explicit `axiom`: `0`; `def/abbrev := by sorry`: `0`.
- `lake build Phi4` succeeds; `scripts/check_phi4_trust.sh` succeeds.
- Upstream blocker inventory moved to `82` unique declarations (`open=80`, `in_progress=2`); the TODO inventory section has been resynced.
- Regression fix: `test/task2_k4_iv_existence.lean` was converted from duplicate
  theorem redeclarations to compile-checked `example` usage of production theorems
  (`infinite_volume_schwinger_exists_four_of_models`,
  `infinite_volume_schwinger_exists_four_of_lattice_models`), restoring test-file
  compile.
- Trust-boundary fix: `Phi4.lean` no longer imports `Phi4/ReconstructionUpstream.lean`;
  upstream `sorryAx`-dependent reconstruction is now opt-in via explicit import.

## Canonical Goal And Architecture (Authoritative)

This audit is scoped to the Glimm-Jaffe `φ⁴₂` objective:

1. establish infinite-volume Schwinger data,
2. package OS axioms (OS0-OS4, weak-coupling OS4 explicit),
3. reconstruct Wightman theory.

Findings below are interpreted against that architecture. Upstream dependency
audits are support checks and do not change the local project objective.

## Scope

- Audited all Lean files under `Phi4/`.
- Core modules: `23` files (excluding `Phi4/Scratch/`).
- Scratch modules: `95` files.

Policy basis (from `agent.md`):
1. no `axiom`,
2. no `def := by sorry`,
3. open gaps are theorem-level `sorry`,
4. avoid hiding open gaps in `...Model` interfaces.

## Global Policy Checks

- `axiom` declarations in `Phi4/**/*.lean`: **0**
- `def/abbrev := by sorry` in `Phi4/**/*.lean`: **0**
- theorem-level `sorry` count (core): **0**
- theorem-level `sorry` count (scratch): **0**
- `class ...Model` declarations in `Phi4/**/*.lean`: **58**

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
  - `gap_phi4_linear_growth`
  - `gap_phi4_wightman_reconstruction_step`

`Phi4/HonestGaps.lean` now forwards to these core frontier theorems and has no
local `sorry`.

## Mathematical/Physics Soundness Findings

### High

1. Large proof debt remains behind interface assumptions (`...Model`) in core construction layers (`Interaction`, `FiniteVolumeMeasure`, `CorrelationInequalities`, `ReflectionPositivity`, `MultipleReflections`, `InfiniteVolumeLimit`, `OSAxioms`, `Reconstruction`).

### Medium

1. FKG monotonicity statements were tightened in this audit pass: connected two-point nonnegativity now explicitly requires nonnegative test functions (`f, g ≥ 0`), removing an over-strong earlier statement.
2. `ConnectedTwoPointDecayAtParams` was strengthened for soundness: decay now has a uniform positive mass gap with pair-dependent amplitudes (`C_{f,g}`), avoiding an unrealistically strong single global amplitude constant across all test-function pairs.
3. The monotonicity order used in FKG interfaces is still abstract and not yet identified with a fully internalized lattice/field order construction; this remains a closure task.
4. Upstream OS reconstruction bridge theorem `os_to_wightman` (OSReconstruction) currently depends on `sorryAx`; by project policy it cannot be used to discharge `phi4_wightman_reconstruction_step` yet. This dependency is now isolated in `Phi4/ReconstructionUpstream.lean` rather than core `Phi4/Reconstruction.lean`.
5. New constructive infrastructure was added in `InfiniteVolumeLimit.lean` for exhausting-sequence convergence in the two-point channel (including lattice and `k = 2` `schwingerN` variants, plus interface-style `if h : 0 < n then ... else 0` endpoints), removing a previously external boundedness hypothesis in that local convergence path.
6. `Reconstruction.lean` now exposes a trusted interface-level endpoint
   `phi4_wightman_exists_of_interfaces`; bundled reconstruction
   (`phi4_wightman_exists_of_bundle`) now uses that endpoint instead of the
   frontier-gap theorem `phi4_wightman_exists`.
7. `ModelBundle.lean` now exposes trusted bundle-level regularity/OS wrappers
   (`generating_functional_bound_of_bundle`,
   `nonlocal_phi4_bound_of_bundle`,
   `generating_functional_bound_uniform_of_bundle`,
   `phi4_satisfies_OS_of_bundle`) that route through interface proofs rather
   than frontier-gap wrapper theorems.
8. `Reconstruction.lean` now includes interface-level corollaries
   (`phi4_selfadjoint_fields_of_interfaces`,
   `phi4_locality_of_interfaces`,
   `phi4_lorentz_covariance_of_interfaces`,
   `phi4_unique_vacuum_of_interfaces`), with matching trusted bundle wrappers
   in `ModelBundle.lean`.
9. `InfiniteVolumeLimit.lean` now has a general permutation-transfer lemma
   `infiniteVolumeSchwinger_perm` from finite-volume `schwingerN_perm`; the
   two-point symmetry theorem is now derived from this reusable result.
10. `OSAxioms.lean` now includes a trusted OS1 interface theorem
   `phi4_os1_of_interface`; `ModelBundle.lean` exposes
   `phi4_os1_of_bundle` through this interface path.
11. `InfiniteVolumeLimit.lean` now includes reusable infinite-volume connected
    two-point linearity/bilinearity transfer lemmas
    (`connectedTwoPoint_add_left`, `connectedTwoPoint_smul_left`,
    `connectedTwoPoint_add_right`, `connectedTwoPoint_smul_right`,
    `connectedTwoPointBilinear`, `connectedTwoPointBilinear_symm`,
    `connectedTwoPointBilinear_self_nonneg`) derived via exhaustion-limit
    transfer; `connectedTwoPoint_quadratic_nonneg` now uses this bilinear
    infrastructure directly.
12. `Reconstruction.lean` now proves an `ε`-`R` clustering consequence from
    exponential connected two-point decay
    (`connectedTwoPoint_decay_eventually_small`) and a threshold-specialized
    version (`phi4_connectedTwoPoint_decay_below_threshold_eventually_small`),
    plus an explicit-Schwinger variant
    (`phi4_connectedTwoPoint_decay_below_threshold_eventually_small_explicit`),
    with bundled exposure in `ModelBundle.lean`.
13. `translateTestFun` is now public in `Reconstruction.lean`, eliminating
    private-identifier leakage in downstream theorem signatures.
14. `Reconstruction.lean` now adds global weak-coupling `ε`-`R` clustering
    forms (`phi4_os4_weak_coupling_eventually_small`,
    `phi4_os4_weak_coupling_eventually_small_explicit`) derived from
    `UniformWeakCouplingDecayModel`, with bundled wrappers in
    `ModelBundle.lean`.
15. `ModelBundle.lean` now includes bundled wrappers for both base global OS4
    weak-coupling decay forms and their `ε`-`R` forms.
16. `Reconstruction.lean` now includes
    `reconstructionWeakCouplingModel_of_uniform`, deriving the fixed-parameter
    weak-coupling threshold interface from global uniform weak-coupling decay
    data without adding assumptions.

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
- theorem-level `sorry`: `0`.

## Verification Commands

`scripts/check_phi4_trust.sh` now also runs a theorem-dependency check
(`#print axioms`) and rejects `sorryAx` for selected trusted interface/bundle
endpoints.

```bash
scripts/check_phi4_trust.sh
lake build Phi4
rg -n "^\s*axiom\b" Phi4 --glob '*.lean'
grep -RIn "^[[:space:]]*sorry\b" Phi4 --include='*.lean'
```

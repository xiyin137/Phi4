# Phi4 Systematic Policy Audit

Date: 2026-03-03

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

Update (2026-03-03):
- Re-audited with current tree state:
  - Lean files under `Phi4/`: `134` total (`36` core, `98` scratch).
  - `class ...Model` declarations in `Phi4/**/*.lean`: `58`.
  - Core theorem-level `sorry`: `0`; scratch theorem-level `sorry`: `0`; explicit `axiom`: `0`; `def/abbrev := by sorry`: `0`.
  - `_nonempty_of_` theorem constructors: `142`.
  - `interactionWeightModel_nonempty_of_*` routes: `43`.
  - `interactionIntegrabilityModel_nonempty_of_*` routes: `29`.
  - `gap_phi4_linear_growth*` routes in `Reconstruction/Part1Core.lean`: reduced `10 → 6` by removing unused thin wrappers.
- Bundle-obligation reduction:
  - `Phi4ModelBundle` field count reduced `34 → 25` by replacing redundant subinterface fields with canonical superinterface fields (`InfiniteVolumeLimitModel`, `RegularityModel`, `OSAxiomCoreModel`).
- Bloat-control operational guard added:
  - `scripts/route_bloat_guard.sh` enforces non-growth thresholds for model/constructor/route counts.
  - `scripts/quick_gate.sh` and `scripts/weekly_gate.sh` now include this guard.

Update (2026-03-04):
- Re-audited after additional route-pruning:
  - Lean files under `Phi4/`: `134` total (`36` core, `98` scratch).
  - `class ...Model` declarations in `Phi4/**/*.lean`: `58`.
  - `_nonempty_of_` theorem constructors: reduced `142 → 117`.
  - `interactionWeightModel_nonempty_of_*` routes: `43` (unchanged).
  - `interactionIntegrabilityModel_nonempty_of_*` routes in `Phi4/Interaction`: reduced `29 → 4`.
  - `gap_phi4_linear_growth*` routes in `Reconstruction/Part1Core.lean`: reduced `10 → 4`.
- Route reduction actions:
  - Removed no-caller thin `InteractionIntegrabilityModel` forwarding wrappers in
    `Phi4/Interaction/Part3.lean`.
  - Removed no-caller linear-growth route variants in
    `Phi4/Reconstruction/Part1Core.lean`.
- Guard tightening:
  - Updated `scripts/route_bloat_guard.sh` thresholds to the new reduced baselines.

Update (2026-03-04, reconstruction route-pruning pass):
- `Phi4/Reconstruction/Part3.lean` was aggressively de-bloated by removing
  no-caller forwarding route variants:
  - file size reduced `2787 → 313` lines,
  - top-level theorem count reduced `41 → 13`,
  - `phi4_wightman_exists*`-prefixed theorem count reduced `32 → 4`.
- Additional linear-growth route tightening:
  - removed no-caller theorem
    `gap_phi4_linear_growth_of_tendsto_ae_and_linear_lower_bound`,
  - `gap_phi4_linear_growth*` route count now `10 → 3`.
- Policy outcome: the reconstruction layer now keeps only the actively used
  explicit/interface endpoints and drops route-only wrappers with no in-repo
  callers.
- Verification:
  - `lake build Phi4.Reconstruction.Part3` passes after each pruning step.
  - `scripts/quick_gate.sh` passes with current reduced route surface.

Update (2026-03-04, explicit-route cleanup pass):
- Removed unused explicit-Schwinger weak-coupling wrapper routes from
  `Phi4/Reconstruction/Part2.lean`:
  - dropped `phi4_os4_weak_coupling_explicit`,
    `phi4_os4_weak_coupling_explicit_at_params`,
    `phi4_connectedTwoPoint_decay_below_threshold_eventually_small_explicit`,
    `phi4_os4_weak_coupling_eventually_small_explicit`,
    `phi4_os4_weak_coupling_eventually_small_explicit_at_params`,
  - plus previously removed dead
    `phi4_connectedTwoPoint_decay_below_threshold_explicit`.
- Removed matching no-caller bundle wrappers from `Phi4/ModelBundle.lean`:
  - `phi4_os4_weak_coupling_explicit_of_bundle`,
    `phi4_os4_weak_coupling_explicit_at_params_of_bundle`,
    `phi4_os4_weak_coupling_eventually_small_explicit_of_bundle`,
    `phi4_os4_weak_coupling_eventually_small_explicit_at_params_of_bundle`,
    `phi4_connectedTwoPoint_decay_below_threshold_eventually_small_explicit_of_bundle`.
- Surface-size impact:
  - `Reconstruction/Part2` theorem count reduced `47 → 41`,
  - `Reconstruction/Part2` `*_explicit*` theorem count reduced `6 → 0`,
  - `ModelBundle` theorem count reduced `55 → 50`.
- Guard hardening:
  - `scripts/route_bloat_guard.sh` now enforces
    `Reconstruction.Part2` theorem cap (`41`) and explicit-route cap (`0`).
- Verification:
  - `lake build Phi4.Reconstruction.Part2 Phi4.ModelBundle` passes.
  - `scripts/route_bloat_guard.sh` and `scripts/quick_gate.sh` pass.

Update (2026-03-04, bundle-wrapper purge + Part2 core shrink):
- Removed the entire no-caller `_of_bundle` theorem layer from
  `Phi4/ModelBundle.lean`, keeping only the bundled interface/class and
  instance graph.
- Removed the no-caller forwarding tail in `Phi4/Reconstruction/Part2.lean`
  (connected-two-point algebra wrappers and 4-point inequality wrappers),
  retaining only the weak-coupling threshold/decay chain.
- Surface-size impact:
  - `ModelBundle` theorem count reduced `50 → 0`,
  - `Reconstruction/Part2` theorem count reduced `41 → 7`.
- Guard tightening:
  - `scripts/route_bloat_guard.sh` now enforces
    `ModelBundle` theorem cap (`0`) and tighter
    `Reconstruction.Part2` theorem cap (`7`).
- Verification:
  - `lake build Phi4.ModelBundle` passes.
  - `lake build Phi4.Reconstruction.Part2 Phi4.Reconstruction` passes.
  - `scripts/route_bloat_guard.sh` and `scripts/quick_gate.sh` pass.

Update (2026-03-04, Part2 wrapper purge finalization):
- `Phi4/Reconstruction/Part2.lean` was reduced to a single constructive core
  theorem (`connectedTwoPoint_decay_eventually_small`), removing the remaining
  weak-coupling forwarding wrappers (`phi4_*` threshold/decay aliases).
- Surface-size impact:
  - `Reconstruction/Part2` theorem count reduced `7 → 1`
    (overall `47 → 1` across this session).
- Guard tightening:
  - `scripts/route_bloat_guard.sh` `Reconstruction.Part2` theorem cap tightened
    from `7` to `1`.
- Verification:
  - `lake build Phi4.Reconstruction.Part2 Phi4.Reconstruction` passes.
  - `scripts/route_bloat_guard.sh` and `scripts/quick_gate.sh` pass.

Update (2026-03-04, Interaction.Part3 count1-route pruning):
- `Phi4/Interaction/Part3.lean` was pruned by removing theorem declarations with
  no Lean callers (occurrence count `1`) in the post-reconstruction-cleanup
  state, while preserving the constructive core (`exp_interaction_Lp`,
  partition-function core lemmas, and reused integrability constructors).
- Removed declarations include:
  - no-caller UV-shifted/bad-set partition-function route wrappers, and
  - no-caller integrability constructors that only restated existing core routes.
- Surface-size impact:
  - `Interaction/Part3` line count reduced `2478 → 1003`,
  - split-line-aware theorem count in `Interaction/Part3` reduced `36 → 16`,
  - global `_nonempty_of_` theorem count reduced `117 → 113`,
  - `interactionWeightModel_nonempty_of_*` count reduced `43 → 40`,
  - `interactionIntegrabilityModel_nonempty_of_*` count reduced `4 → 3`.
- Guard tightening:
  - `scripts/route_bloat_guard.sh` thresholds updated to
    `_nonempty_of_ = 113`,
    `interactionWeightModel routes = 40`,
    `interactionIntegrabilityModel routes = 3`.
- Verification:
  - `lake build Phi4.Interaction.Part3 Phi4.Interaction` passes.
  - `scripts/route_bloat_guard.sh` passes with tightened baselines.
  - `scripts/quick_gate.sh` passes end-to-end.

Update (2026-03-04, final wrapper-trim pass):
- Removed additional no-caller forwarding wrappers:
  - `Interaction/Part3`: dropped
    `partition_function_pos_of_nonempty_interactionWeightModel` and
    `partition_function_integrable_of_nonempty_interactionWeightModel`.
  - `Reconstruction/Part3`: dropped interface-only corollary wrappers
    `phi4_selfadjoint_fields_of_interfaces`,
    `phi4_locality_of_interfaces`,
    `phi4_lorentz_covariance_of_interfaces`,
    `phi4_unique_vacuum_of_interfaces`.
- Surface-size impact:
  - `Interaction/Part3` line count reduced `1003 → 972`,
    theorem count reduced `16 → 4`.
  - `Reconstruction/Part3` line count reduced `313 → 263`,
    theorem count reduced `13 → 9`.
- Guard tightening:
  - `scripts/route_bloat_guard.sh` `Reconstruction.Part3` theorem cap tightened
    from `13` to `9`.
- Verification:
  - `lake build Phi4.Interaction.Part3` passes.
  - `lake build Phi4.Reconstruction.Part3 Phi4.Reconstruction` passes.
  - `scripts/route_bloat_guard.sh` passes with the tightened cap.

Update (2026-03-04, explicit-core inlining pass):
- Removed the class-based forwarding wrapper
  `interactionWeightModel_nonempty_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound`
  from `Phi4/Interaction/Part3.lean`.
- Rewired in-repo callers to the assumption-explicit core theorem
  `interactionWeightModel_nonempty_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound_of_aestronglyMeasurable_and_standardSeq_tendsto_ae`
  in:
  - `Phi4/FiniteVolumeMeasure.lean`
  - `Phi4/Reconstruction/Part1Core.lean`
- Removed one additional no-caller finite-volume route wrapper:
  - `finiteVolumeMeasure_isProbability_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound`
    (in `Phi4/FiniteVolumeMeasure.lean`).
- Surface-size impact:
  - `Interaction/Part3` line count reduced `972 → 946`,
    theorem count reduced `4 → 3`.
  - `_nonempty_of_` theorem count reduced `113 → 112`.
  - `interactionWeightModel_nonempty_of_*` route count reduced `40 → 39`.
- Guard tightening:
  - `scripts/route_bloat_guard.sh` caps tightened to
    `_nonempty_of_ = 112` and
    `interactionWeightModel routes = 39`.
- Verification:
  - `lake build Phi4.Interaction.Part3 Phi4.FiniteVolumeMeasure Phi4.Reconstruction.Part1Core` passes.
  - `scripts/route_bloat_guard.sh` passes with tightened caps.

Update (2026-03-04, Interaction/Linear-growth wrapper pruning pass):
- Removed no-caller forwarding wrappers in:
  - `Phi4/Interaction/Part1Core.lean`:
    - `interactionIntegrabilityModel_nonempty_of_sq_integrable_data`
  - `Phi4/Interaction/Part2.lean`:
    - `interactionWeightModel_nonempty_of_uv_cutoff_seq_shifted_exponential_wick_bad_sets`
    - `interactionWeightModel_nonempty_of_uv_cutoff_seq_shifted_summable_wick_sublevel_bad_sets`
    - `interactionWeightModel_nonempty_of_uv_cutoff_seq_shifted_geometric_wick_sublevel_bad_sets`
    - `interaction_ae_nonneg_all_rectangles_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound`
    - `exp_interaction_Lp_of_uv_cutoff_seq_shifted_exponential_moment_abs_geometric_bound`
    - `interactionWeightModel_nonempty_of_cutoff_seq_pointwise_lower_bounds`
    - `interactionWeightModel_nonempty_of_cutoff_seq_succ_pointwise_lower_bounds`
    - `interactionWeightModel_nonempty_of_cutoff_seq_eventually_lower_bounds`
    - `exp_interaction_Lp_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound`
  - `Phi4/Reconstruction/Part1Tail.lean`:
    - `reconstructionInputModel_nonempty_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound`
- Surface-size impact:
  - `_nonempty_of_` theorem count reduced `112 → 104`.
  - `interactionWeightModel_nonempty_of_*` route count reduced `39 → 33`.
  - `interactionIntegrabilityModel_nonempty_of_*` route count reduced `3 → 2`.
  - `Interaction/Part2` theorem count reduced `48 → 44` and line count
    reduced `1745 → 1663`.
- Guard tightening:
  - `scripts/route_bloat_guard.sh` caps tightened to
    `_nonempty_of_ = 104`,
    `interactionWeightModel routes = 33`,
    `interactionIntegrabilityModel routes = 2`.
- Verification:
  - `lake build Phi4.Interaction.Part1Core Phi4.Interaction.Part2 Phi4.Reconstruction.Part1Tail` passes.
  - `scripts/route_bloat_guard.sh` passes with tightened caps.
  - `scripts/quick_gate.sh` passes end-to-end.

Update (2026-03-04, Interaction/Part2 route-surface collapse pass):
- Removed an additional twelve declaration-only
  `interactionWeightModel_nonempty_of_cutoff_seq_*` wrapper routes from
  `Phi4/Interaction/Part2.lean`, including lower-bound, summable-tail,
  geometric-tail, and exponential-tail entry aliases whose proof bodies only
  forwarded to existing `exp_interaction_Lp` cores.
- Surface-size impact:
  - `_nonempty_of_` theorem count reduced `104 → 92`.
  - `interactionWeightModel_nonempty_of_*` route count reduced `33 → 21`.
  - `Interaction/Part2` theorem count reduced `44 → 32`.
  - `Interaction/Part2` line count reduced `1663 → 1442`.
- Guard tightening:
  - `scripts/route_bloat_guard.sh` caps tightened to
    `_nonempty_of_ = 92` and
    `interactionWeightModel routes = 21`.
- Verification:
  - `lake build Phi4.Interaction.Part2 Phi4.Reconstruction.Part1Tail` passes.
  - `scripts/route_bloat_guard.sh` passes with tightened caps.
  - `scripts/quick_gate.sh` passes end-to-end.

Update (2026-03-04, continued interaction-route pruning pass):
- Removed remaining no-caller shifted Wick-sublevel forwarding wrappers and
  class-based alias routes in `Phi4/Interaction/Part2.lean`, plus direct
  callers were rewired to assumption-explicit cores:
  - dropped
    `interactionWeightModel_nonempty_of_cutoff_seq_shifted_summable_bad_sets`,
    `interactionWeightModel_nonempty_of_uv_cutoff_seq_shifted_summable_wick_bad_sets`,
    `interactionWeightModel_nonempty_of_uv_cutoff_seq_shifted_geometric_wick_bad_sets`,
    `interactionWeightModel_nonempty_of_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets`,
  - rewired finite-volume/square-data users to
    `interactionWeightModel_nonempty_of_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets_of_aestronglyMeasurable_and_standardSeq_tendsto_ae`.
- Removed four additional no-caller route variants in:
  - `Phi4/Interaction/Part1Core.lean`:
    - `interactionWeightModel_nonempty_of_tendsto_ae_and_uniform_integral_bound`,
    - `interactionWeightModel_nonempty_of_tendsto_ae_and_uniform_exp_moment_bound`,
  - `Phi4/Interaction/Part1Tail.lean`:
    - `interactionWeightModel_nonempty_of_sq_moment_polynomial_bound_and_geometric_integral_bound`,
    - `interactionWeightModel_nonempty_of_tendsto_ae_and_linear_lower_bound`.
- Removed eleven additional no-caller `exp_interaction_Lp_of_*` route variants
  in `Phi4/Interaction/Part2.lean` (summable/geometric/exponential bad-event
  aliases and Wick-sublevel aliases).
- Surface-size impact:
  - `_nonempty_of_` theorem count reduced `92 → 84`.
  - `interactionWeightModel_nonempty_of_*` route count reduced `21 → 13`.
  - `interactionIntegrabilityModel_nonempty_of_*` route count stays `2`.
  - `Interaction/Part2` theorem count reduced `32 → 17`.
  - `Interaction/Part2` line count reduced `1442 → 993`.
- Guard tightening:
  - `scripts/route_bloat_guard.sh` caps tightened to
    `_nonempty_of_ = 84` and
    `interactionWeightModel routes = 13`.
- Verification:
  - `lake build Phi4.Interaction.Part2 Phi4.Interaction.Part3 Phi4.FiniteVolumeMeasure Phi4.Reconstruction.Part1Core` passes.
  - `scripts/route_bloat_guard.sh` passes with tightened caps.
  - `scripts/quick_gate.sh` passes end-to-end.

Update (2026-03-04, Interaction.Part2 zero-caller trim follow-up):
- Removed four additional no-caller `Interaction/Part2` theorems:
  - `exp_interaction_Lp_of_cutoff_seq_shifted_exponential_wick_bad_sets`,
  - `cutoff_seq_eventually_lower_bound_of_exponential_bad_event_bound`,
  - `cutoff_seq_eventually_lower_bound_of_shifted_exponential_bad_event_bound`,
  - `cutoff_seq_eventually_uniform_lower_bound_of_pointwise_bounds`.
- Surface-size impact:
  - `Interaction/Part2` theorem count reduced `17 → 13`.
  - `Interaction/Part2` line count reduced `993 → 890`.
  - global `_nonempty_of_` and `interactionWeightModel_nonempty_of_*` counts are unchanged (`84`, `13`).
- Verification:
  - `lake build Phi4.Interaction.Part2 Phi4.Interaction.Part3 Phi4.FiniteVolumeMeasure Phi4.Reconstruction.Part1Core` passes.
  - `scripts/route_bloat_guard.sh` passes.

Update (2026-03-04, Interaction.Part2 zero-caller trim follow-up 2):
- Removed two additional no-caller `Interaction/Part2` routes:
  - `exp_interaction_Lp_of_cutoff_seq_shifted_geometric_wick_bad_sets`,
  - `cutoff_seq_eventually_lower_bound_of_geometric_bad_event_bound`.
- Surface-size impact:
  - `Interaction/Part2` theorem count reduced `13 → 11`.
  - `Interaction/Part2` line count reduced `890 → 830`.
  - global `_nonempty_of_` and `interactionWeightModel_nonempty_of_*` counts remain `84` and `13`.
- Guard tightening:
  - `scripts/route_bloat_guard.sh` now also enforces
    `Interaction.Part2` theorem cap (`11`).
- Verification:
  - `lake build Phi4.Interaction.Part2 Phi4.Interaction.Part3 Phi4.FiniteVolumeMeasure Phi4.Reconstruction.Part1Core` passes.
  - `scripts/route_bloat_guard.sh` passes.
  - `scripts/quick_gate.sh` passes end-to-end.

Update (2026-03-04, Interaction core-chain collapse pass):
- Removed one additional no-caller `Interaction/Part2` theorem:
  - `exp_interaction_Lp_of_cutoff_seq_shifted_summable_wick_bad_sets`.
- Removed two no-caller forwarding constructors in `Interaction/Part1Tail.lean`:
  - `interactionWeightModel_nonempty_of_sq_moment_polynomial_bound_and_geometric_exp_moment_bound`,
  - `interactionWeightModel_nonempty_of_sq_moment_polynomial_bound_and_uniform_integral_bound`.
- Removed two single-use forwarding constructors in `Interaction/Part1Core.lean`
  by inlining their logic into callers:
  - `interactionWeightModel_nonempty_of_standardSeq_succ_tendsto_ae_and_uniform_exp_moment_bound`,
  - `interactionWeightModel_nonempty_of_standardSeq_succ_tendsto_ae_and_geometric_integral_bound`.
- Surface-size impact:
  - `_nonempty_of_` theorem count reduced `84 → 80`.
  - `interactionWeightModel_nonempty_of_*` route count reduced `13 → 9`.
  - `interactionIntegrabilityModel_nonempty_of_*` route count stays `2`.
  - `Interaction/Part2` theorem count reduced `11 → 10`.
- Guard tightening:
  - `scripts/route_bloat_guard.sh` caps tightened to
    `_nonempty_of_ = 80`,
    `interactionWeightModel routes = 9`,
    `Interaction.Part2` theorem count = `10`.
- Verification:
  - `lake build Phi4.Interaction.Part1Core Phi4.Interaction.Part1Tail Phi4.Interaction.Part2 Phi4.Interaction.Part3 Phi4.FiniteVolumeMeasure Phi4.Reconstruction.Part1Core` passes.
  - `scripts/route_bloat_guard.sh` passes with tightened caps.
  - `scripts/quick_gate.sh` passes end-to-end.

## Canonical Goal And Architecture (Authoritative)

This audit is scoped to the Glimm-Jaffe `φ⁴₂` objective:

1. establish infinite-volume Schwinger data,
2. package OS axioms (OS0-OS4, weak-coupling OS4 explicit),
3. reconstruct Wightman theory.

Findings below are interpreted against that architecture. Upstream dependency
audits are support checks and do not change the local project objective.

## Scope

- Audited all Lean files under `Phi4/`.
- Core modules: `36` files (excluding `Phi4/Scratch/`).
- Scratch modules: `98` files.

Policy basis (from `AGENTS.md`):
1. no `axiom`,
2. no `def := by sorry`,
3. open gaps are theorem-level `sorry`,
4. avoid hiding open gaps in `...Model` interfaces,
5. do not add route variants unless net variant count is non-increasing.

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
6. `Reconstruction/Part3.lean` exposes a trusted interface-level endpoint
   `phi4_wightman_exists_of_interfaces`; `phi4_wightman_exists` is retained as
   the canonical top-level theorem alias.
7. Thin interface-only forwarding corollaries in `Reconstruction/Part3.lean`
   (`*_of_interfaces`) were removed as no-caller wrappers; canonical corollaries
   are `phi4_selfadjoint_fields`, `phi4_locality`,
   `phi4_lorentz_covariance`, and `phi4_unique_vacuum`.
8. `ModelBundle.lean` has been reduced to interface aggregation + instances; the
   no-caller theorem-wrapper layer was fully removed.
9. `InfiniteVolumeLimit.lean` now has a general permutation-transfer lemma
   `infiniteVolumeSchwinger_perm` from finite-volume `schwingerN_perm`; the
   two-point symmetry theorem is now derived from this reusable result.
10. `OSAxioms.lean` includes a trusted OS1 interface theorem
   `phi4_os1_of_interface`.
11. `InfiniteVolumeLimit.lean` now includes reusable infinite-volume connected
    two-point linearity/bilinearity transfer lemmas
    (`connectedTwoPoint_add_left`, `connectedTwoPoint_smul_left`,
    `connectedTwoPoint_add_right`, `connectedTwoPoint_smul_right`,
    `connectedTwoPointBilinear`, `connectedTwoPointBilinear_symm`,
    `connectedTwoPointBilinear_self_nonneg`) derived via exhaustion-limit
    transfer; `connectedTwoPoint_quadratic_nonneg` now uses this bilinear
    infrastructure directly.
12. `Reconstruction/Part2.lean` now keeps only one constructive clustering
    endpoint, `connectedTwoPoint_decay_eventually_small`; route-variant aliases
    were removed as wrapper bloat.
13. `translateTestFun` is now public in `Reconstruction.lean`, eliminating
    private-identifier leakage in downstream theorem signatures.
14. `Reconstruction/Part1Core.lean` includes
    `reconstructionWeakCouplingModel_of_uniform`, deriving the fixed-parameter
    weak-coupling threshold interface from global uniform weak-coupling decay
    data without adding assumptions.
15. Route-bloat controls are now enforced by `scripts/route_bloat_guard.sh`,
    including theorem-count caps for `Reconstruction/Part2`,
    `Reconstruction/Part3`, and constructor/route-pattern counts.
16. `Reconstruction.lean` now includes
    the canonical reconstruction interface exports from `Part1Core`/`Part3`
    with trimmed forwarding-route surface.

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

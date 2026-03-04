# CLAUDE-to-Codex Systematic Remediation Tracker

Date: 2026-02-27

This tracker converts `claude_to_codex.md` into an execution matrix.
Each line item is actionable, testable, and tied to concrete files/modules.

## Session Update (2026-03-04, Interaction.Part3 abs-moment wrapper removal)

- Removed one no-caller forwarding wrapper from
  `Phi4/Interaction/Part3.lean`:
  - `interactionWeightModel_nonempty_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_moment_abs_geometric_bound`.
- Guard updates in `scripts/route_bloat_guard.sh`:
  - added exact-zero cap for the removed `Interaction/Part3` abs-moment
    forwarding wrapper.
- Verification passed:
  - `lake build Phi4.Interaction.Part3 Phi4.Interaction Phi4.FiniteVolumeMeasure`,
  - `bash scripts/route_bloat_guard.sh`,
  - `bash scripts/quick_gate.sh`.

## Session Update (2026-03-04, continued wrapper-pruning follow-up)

- Removed eleven no-caller forwarding routes from
  `Phi4/Reconstruction/Part1Tail.lean`:
  - `reconstructionLinearGrowthModel_nonempty_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_moment_geometric_bound`,
  - `reconstructionLinearGrowthModel_nonempty_of_sq_integrable_data_and_sq_moment_polynomial_bound_per_volume_and_uniform_partition_bound`,
  - `reconstructionLinearGrowthModel_nonempty_of_sq_integrable_data_and_linear_lower_bound_off_bad_sets_and_sq_exp_moment_geometric_and_bad_measure_geometric_ennreal`,
  - `reconstructionLinearGrowthModel_nonempty_of_sq_integrable_data_and_linear_threshold_geometric_exp_moment_and_double_exp_moment_geometric_of_moment_bounds`,
  - `reconstructionLinearGrowthModel_nonempty_of_sq_integrable_data_and_higher_moment_polynomial_bound_per_volume_and_uniform_partition_bound`,
  - `reconstructionLinearGrowthModel_nonempty_of_sq_integrable_data_and_sq_moment_polynomial_bound_per_volume_and_uniform_partition_bound_of_succ_succ`,
  - `reconstructionLinearGrowthModel_nonempty_of_sq_integrable_data_and_higher_moment_polynomial_bound_per_volume_and_uniform_partition_bound_of_succ_succ`,
  - `gap_phi4_linear_growth_of_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets_of_aestronglyMeasurable_and_standardSeq_tendsto_ae`,
  - `gap_phi4_linear_growth_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets`,
  - `reconstructionLinearGrowthModel_nonempty_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets`,
  - `reconstructionLinearGrowthModel_nonempty_of_sq_integrable_data_and_linear_threshold_geometric_exp_moment_and_sq_exp_moment_geometric`.
- Removed two no-caller wrappers from `Phi4/Interaction/Part2.lean`:
  - `interactionWeightModel_nonempty_of_cutoff_seq_eventually_lower_bounds_of_aestronglyMeasurable_and_standardSeq_tendsto_ae`,
  - `interaction_ae_nonneg_all_rectangles_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound_of_standardSeq_tendsto_ae`.
- Removed one no-caller wrapper from `Phi4/InfiniteVolumeLimit/Part1.lean`:
  - `schwingerN_monotone_in_volume_two_from_lattice`.
- Guard updates in `scripts/route_bloat_guard.sh`:
  - tightened `InfiniteVolumeLimit.Part1` theorem cap `24 -> 23`,
  - added exact-zero caps for the two removed `Interaction/Part2` wrappers,
  - added an exact-zero cap for
    `schwingerN_monotone_in_volume_two_from_lattice`.
- Verification passed:
  - `lake build Phi4.Interaction.Part2 Phi4.InfiniteVolumeLimit.Part1`,
  - `lake build Phi4.Reconstruction.Part1Tail Phi4.Reconstruction`,
  - `bash scripts/route_bloat_guard.sh`,
  - `bash scripts/quick_gate.sh`.

## Session Update (2026-03-04, Part1Core explicit-route trim)

- Removed two no-caller explicit forwarding routes from
  `Phi4/Reconstruction/Part1Core.lean`:
  - `gap_phi4_linear_growth_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound_of_aestronglyMeasurable_and_standardSeq_tendsto_ae`,
  - `reconstructionLinearGrowthModel_nonempty_of_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets_of_aestronglyMeasurable_and_standardSeq_tendsto_ae`.
- Guard updates in `scripts/route_bloat_guard.sh`:
  - added exact zero caps for both removed route names.
- Verification passed:
  - `lake build Phi4.Reconstruction.Part1Core Phi4.Reconstruction`,
  - `bash scripts/route_bloat_guard.sh`,
  - `bash scripts/quick_gate.sh`.

## Session Update (2026-03-04, Reconstruction-input wrapper collapse)

- Removed six no-caller forwarding wrappers from
  `Phi4/Reconstruction/Part1Tail.lean`:
  - `reconstructionInputModel_nonempty_of_sq_integrable_data_and_linear_lower_bound_off_bad_sets_and_sq_exp_moment_geometric_and_bad_measure_geometric_ennreal`,
  - `reconstructionInputModel_nonempty_of_sq_integrable_data_and_sq_moment_polynomial_bound_per_volume_and_uniform_partition_bound`,
  - `reconstructionInputModel_nonempty_of_sq_integrable_data_and_higher_moment_polynomial_bound_per_volume_and_uniform_partition_bound`,
  - `reconstructionInputModel_nonempty_of_sq_integrable_data_and_sq_moment_polynomial_bound_per_volume_and_uniform_partition_bound_of_succ_succ`,
  - `reconstructionInputModel_nonempty_of_sq_integrable_data_and_higher_moment_polynomial_bound_per_volume_and_uniform_partition_bound_of_succ_succ`,
  - `reconstructionInputModel_nonempty_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets`.
- Measured reduction:
  - `Reconstruction/Part1Tail` `reconstructionInputModel_nonempty_of_*` routes
    `6 -> 0`.
- Guard updates in `scripts/route_bloat_guard.sh`:
  - tightened `Reconstruction.Part1Tail reconstructionInput routes` cap
    `6 -> 0`.
- Verification passed:
  - `lake build Phi4.Reconstruction.Part1Tail Phi4.Reconstruction`,
  - `bash scripts/route_bloat_guard.sh`,
  - `bash scripts/quick_gate.sh`.

## Session Update (2026-03-04, Reconstruction linear-growth wrapper trim)

- Removed six no-caller forwarding wrappers:
  - `Phi4/Reconstruction/Part1Core.lean`:
    `gap_phi4_linear_growth_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound`,
    `reconstructionLinearGrowthModel_nonempty_of_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets`.
  - `Phi4/Reconstruction/Part1Tail.lean`:
    `gap_phi4_linear_growth_of_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets`,
    `reconstructionInputModel_nonempty_of_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets`,
    `reconstructionInputModel_nonempty_of_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets_of_aestronglyMeasurable_and_standardSeq_tendsto_ae`,
    `reconstructionInputModel_nonempty_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_moment_geometric_bound`.
- Measured reduction:
  - `gap_phi4_linear_growth*` routes in `Part1Core` `3 -> 2`,
  - class-based `InteractionUVModel` wrappers in `Part1Core` `1 -> 0`,
  - class-based `InteractionUVModel` wrappers in `Part1Tail` `2 -> 0`,
  - `reconstructionInputModel_nonempty_of_*` routes in `Part1Tail` `8 -> 6`.
- Guard updates in `scripts/route_bloat_guard.sh`:
  - tightened `gap_phi4_linear_growth` cap `3 -> 2`,
  - added `Reconstruction.Part1Core InteractionUV wrappers` cap `0`,
  - added `Reconstruction.Part1Tail InteractionUV wrappers` cap `0`,
  - added `Reconstruction.Part1Tail reconstructionInput routes` cap `6`.
- Verification passed:
  - `lake build Phi4.Reconstruction.Part1Core Phi4.Reconstruction.Part1Tail Phi4.Reconstruction`,
  - `bash scripts/route_bloat_guard.sh`,
  - `bash scripts/quick_gate.sh`.

## Session Update (2026-03-04, Correlation constructor-wrapper follow-up)

- Removed three additional no-caller constructor wrappers from
  `Phi4/CorrelationInequalities.lean`:
  - `correlationInequalityModel_nonempty_of_submodels`,
  - `correlationInequalityModel_nonempty_of_lattice_and_core_data`,
  - `correlationInequalityModel_nonempty_of_lattice_and_core_models`.
- Measured reduction:
  - `CorrelationInequalities` theorem count `56 -> 53`,
  - global `_nonempty_of_` count `67 -> 64`.
- Guard updates in `scripts/route_bloat_guard.sh`:
  - `_nonempty_of_` cap `67 -> 64`,
  - `CorrelationInequalities` theorem cap `56 -> 53`.
- Verification passed:
  - `lake build Phi4.CorrelationInequalities Phi4.InfiniteVolumeLimit Phi4.Reconstruction`,
  - `bash scripts/quick_gate.sh`.

## Session Update (2026-03-04, remove unused HonestGaps wrapper module)

- Deleted `Phi4/HonestGaps.lean` (unused forwarding-only wrapper module).
- Confirmed no in-repo imports/usages remained before deletion.
- Verification passed:
  - `bash scripts/route_bloat_guard.sh`,
  - `bash scripts/quick_gate.sh`.

## Session Update (2026-03-04, Reconstruction Part3 corollary trim)

- Removed four no-caller Wightman corollary wrappers from
  `Phi4/Reconstruction/Part3.lean`:
  - `phi4_selfadjoint_fields`,
  - `phi4_locality`,
  - `phi4_lorentz_covariance`,
  - `phi4_unique_vacuum`.
- Tightened guard baseline in `scripts/route_bloat_guard.sh`:
  - `Reconstruction.Part3` theorem cap `9 -> 5`
    (`phi4_wightman_exists*` cap remains `4`).
- Verification passed:
  - `lake build Phi4.Reconstruction.Part3 Phi4.Reconstruction`,
  - `bash scripts/quick_gate.sh`.

## Session Update (2026-03-04, Correlation wrapper collapse)

- Removed eight no-caller wrapper constructors/routes in
  `Phi4/CorrelationInequalities.lean`:
  - `schwingerNMonotoneFamilyModel_nonempty_of_models`,
  - `correlationInequalityModel_nonempty_of_submodels_and_schwingerFourMonotone`,
  - `latticeSchwingerNMonotoneFamilyModel_nonempty_of_models`,
  - `correlationFourPointModel_nonempty_of_data_and_lattice_monotone`,
  - `correlationInequalityCoreModel_nonempty_of_data_and_lattice_monotone`,
  - `correlationInequalityModel_nonempty_of_lattice_and_core_data_and_lattice_monotone`,
  - `correlationInequalityModel_nonempty_of_lattice_and_core_models_and_lattice_monotone`,
  - `correlationInequalityModel_nonempty_of_twoPoint_and_core`.
- Measured reduction:
  - `CorrelationInequalities` theorem count `64 -> 56`,
  - global `_nonempty_of_` count `75 -> 67`.
- Guard updates in `scripts/route_bloat_guard.sh`:
  - `_nonempty_of_` cap tightened to `67`,
  - added `CorrelationInequalities` theorem cap `56`.
- Verification passed:
  - `lake build Phi4.CorrelationInequalities Phi4.InfiniteVolumeLimit Phi4.Regularity Phi4.OSAxioms`,
  - `bash scripts/quick_gate.sh`.

## Session Update (2026-03-04, IV Part3 alias cleanup)

- Removed three no-caller alias theorems from
  `Phi4/InfiniteVolumeLimit/Part3.lean`:
  - `connectedTwoPointBilinear_symm`,
  - `connectedTwoPoint_quadratic_nonneg_standard`,
  - `infiniteVolumeSchwinger_zero_of_moment`.
- Added a new non-growth guard in `scripts/route_bloat_guard.sh`:
  - `InfiniteVolumeLimit/Part3` theorem cap `16`.
- Verification passed:
  - `lake build Phi4.InfiniteVolumeLimit.Part3 Phi4.InfiniteVolumeLimit`,
  - `bash scripts/route_bloat_guard.sh`.

## Session Update (2026-03-04, IV Part2 alias cleanup)

- Removed nine no-caller alias theorems from
  `Phi4/InfiniteVolumeLimit/Part2.lean`:
  - `infiniteCumulantFourPoint_abs_bound_alt13`,
  - `infiniteCumulantFourPoint_abs_bound_alt14`,
  - `infiniteTruncatedFourPoint12_abs_bound`,
  - `infiniteTruncatedFourPoint13_abs_bound`,
  - `infiniteTruncatedFourPoint14_abs_bound`,
  - `infiniteTruncatedFourPoint12_bounds`,
  - `infiniteTruncatedFourPoint13_bounds`,
  - `infiniteTruncatedFourPoint14_bounds`,
  - `infiniteTruncatedFourPoint_bounds_all_channels`.
- Added a new non-growth guard in `scripts/route_bloat_guard.sh`:
  - `InfiniteVolumeLimit/Part2` theorem cap `11`.
- Verification passed:
  - `lake build Phi4.InfiniteVolumeLimit.Part2 Phi4.InfiniteVolumeLimit`,
  - `bash scripts/route_bloat_guard.sh`.

## Session Update (2026-03-04, Regularity/OS wrapper trim)

- Removed five no-caller interface-forwarding wrappers:
  - `Phi4/Regularity.lean`:
    `generating_functional_bound_of_interface`,
    `generating_functional_bound_uniform_of_interface`,
    `nonlocal_phi4_bound_of_interface`.
  - `Phi4/OSAxioms.lean`:
    `phi4_os1_of_interface`,
    `os4_weak_coupling_small_of_assumption`.
- Rewired public regularity endpoints to direct class-field projections:
  - `generating_functional_bound`,
  - `generating_functional_bound_uniform`,
  - `nonlocal_phi4_bound`.
- Verification passed:
  - `lake build Phi4.Regularity Phi4.OSAxioms`,
  - `bash scripts/quick_gate.sh`.

## Session Update (2026-03-04, IV monotonicity-route trim)

- Removed four no-caller forwarding wrappers from
  `Phi4/InfiniteVolumeLimit/Part1.lean`:
  - `schwinger_monotone_in_volume_from_lattice`,
  - `schwingerN_monotone_in_volume`,
  - `schwingerN_monotone_in_volume_from_lattice`,
  - `schwingerTwo_uniformly_bounded_on_exhaustion`.
- Tightened `scripts/route_bloat_guard.sh` IVL caps to current baseline:
  - `InfiniteVolumeLimit/Part1` theorem cap `24`,
  - `schwingerTwo_*` route cap `1`,
  - `infinite_volume_schwinger_exists_*_of_*` cap unchanged `4`.
- Verification passed:
  - `lake build Phi4.InfiniteVolumeLimit.Part1 Phi4.InfiniteVolumeLimit`,
  - `lake env lean test/task3_lattice_audit.lean`,
  - `bash scripts/route_bloat_guard.sh`.

## Session Update (2026-03-04, IV existence-route pruning)

- Removed six no-caller forwarding routes from
  `Phi4/InfiniteVolumeLimit/Part1.lean`:
  - `schwingerN_limit_exists_of_monotone_bounded`,
  - `schwingerN_limit_exists_of_models`,
  - `schwingerTwo_tendsto_iSup_of_models`,
  - `schwingerTwo_limit_exists_of_models`,
  - `schwingerTwo_limit_exists_if_exhaustion_of_lattice_models`,
  - `schwingerN_two_limit_exists_if_exhaustion_of_lattice_models`.
- Rewired `test/task3_lattice_audit.lean` to the canonical explicit theorem
  `schwingerN_limit_exists_if_exhaustion_of_models` (`k = 2`) instead of the
  removed `schwingerTwo`/`schwingerN_two` wrappers.
- Tightened `scripts/route_bloat_guard.sh` IVL caps to current baseline:
  - `InfiniteVolumeLimit/Part1` theorem cap `28`,
  - `schwingerTwo_*` route cap `2`,
  - `infinite_volume_schwinger_exists_*_of_*` cap unchanged at `4`.
- Verification passed:
  - `lake build Phi4.InfiniteVolumeLimit.Part1 Phi4.InfiniteVolumeLimit`,
  - `lake env lean test/task3_lattice_audit.lean`,
  - `bash scripts/route_bloat_guard.sh`,
  - `bash scripts/quick_gate.sh`.

## Canonical Goal And Architecture (Authoritative)

This tracker serves the Glimm-Jaffe `φ⁴₂` local objective only:

1. infinite-volume construction,
2. OS-axiom packaging,
3. Wightman reconstruction.

Workstream priority is determined by progress on that architecture. Upstream
OSReconstruction maintenance items are tracked only as dependency-risk controls.

## Status Legend

- `done`: implemented and verified
- `in_progress`: active implementation
- `planned`: queued with explicit next action
- `blocked`: requires upstream closure or prior work package completion

## Global Issues (Sections 1, 13, 14, 17, 18, 19)

| ID | Issue from `claude_to_codex.md` | Action | Status |
|---|---|---|---|
| CTC-G-01 | Core sorry count reported as `9` is stale | Keep trust audit as source of truth; sync docs in follow-up updates | done |
| CTC-G-02 | Trust guarantees must be continuously enforced | Run `scripts/check_phi4_trust.sh` before each commit | done |
| CTC-G-03 | Upstream OSReconstruction risk is high (`os_to_wightman_full`) | Isolate upstream bridge from core reconstruction logic | done |
| CTC-G-04 | Avoid wrapper-only churn and assumption smuggling | Enforce anti-pattern checks in code review and commit criteria | in_progress |
| CTC-G-05 | Start-of-session operating checklist needed | Follow section-19 checklist as default per cycle | done |

## Architecture/Boundary Issues (Sections 2, 3, 4, 8, 10)

| ID | Issue | Action | Status |
|---|---|---|---|
| CTC-A-01 | Core reconstruction mixed with upstream adapter | Split adapter into `Phi4/ReconstructionUpstream.lean` | done |
| CTC-A-02 | Need reusable infrastructure, not one-off theorem wrappers | Add reusable localized combinatorial lemmas for graph bounds | done |
| CTC-A-03 | Keep model-class surface from expanding | No new model classes unless mathematically distinct obligation | done |
| CTC-A-04 | Preserve compatibility split/recombine pattern | Continue `_of_submodels`/`nonempty_of_data` architecture when grounding; reduced Regularity/Wick interfaces from `InfiniteVolumeLimitModel` to measure-only subinterfaces, decoupled `ReconstructionLinearGrowthModel` and fixed-parameter Wightman interface endpoints from unnecessary Schwinger package assumptions, trimmed `phi4_satisfies_OS` to OS-core assumptions, split measure-vs-moment data (`InfiniteVolumeMeasureModel` vs `InfiniteVolumeMomentModel`), made `MeasureOS3Model` purely measure-level, added canonical OS-core reconstruction from subinterfaces (`osaCoreModel_of_submodels`) now used by bundle inference, weakened connected-two-point weak-coupling interfaces to `SchwingerLimitModel` where uniform-bound data is unused, split E0' linear-growth routing into an explicit zero-mode normalization frontier (`gap_phi4_linear_growth_of_zero_mode_normalization`) plus compatibility-backed wrapper (`gap_phi4_linear_growth`), added an explicit mixed-bound core bridge (`phi4_linear_growth_of_mixed_bound_productTensor_approx_and_given_normalized_order0`) so the zero-mode frontier no longer hides `InteractionWeightModel` as an implicit dependency, applied the same explicit-core split to shifted exponential Wick-sublevel reconstruction/Wightman routes, removed all no-caller weak-coupling forwarding wrappers in `Reconstruction/Part2.lean` (now only one nontrivial theorem remains), dropped the now-unused `_of_bundle` theorem layer from `ModelBundle.lean`, pruned no-caller theorem routes in `Interaction/Part3.lean` to keep only actively consumed constructive endpoints, removed remaining nonempty-forwarding partition-function wrappers in `Interaction/Part3.lean`, removed interface-only no-caller corollary wrappers in `Reconstruction/Part3.lean` (`*_of_interfaces`), inlined the last class-based geometric-moment weight-model wrapper by switching callers to the assumption-explicit core constructor directly, removed an additional no-caller finite-volume geometric-moment probability alias in `FiniteVolumeMeasure.lean`, pruned declaration-only interaction/linear-growth wrappers across `Interaction/Part1Core.lean`, `Interaction/Part2.lean`, and `Reconstruction/Part1Tail.lean`, and then removed a further block of declaration-only `interactionWeightModel_nonempty_of_cutoff_seq_*` route aliases from `Interaction/Part2.lean` | in_progress |

## Work Package Issues (Sections 5 and 9)

### WP1: Interaction Integrability (critical blocker)

| ID | Issue | Action | Status |
|---|---|---|---|
| CTC-WP1-01 | Missing localized graph bound infrastructure | Add `Phi4/FeynmanGraphs/LocalizedBounds.lean` with occupancy/factorial combinatorics | done |
| CTC-WP1-02 | `exp_interaction_Lp` not grounded | Build from semibounded Wick-4 + localized graph bounds + tail/layer-cake chain; weighted occupancy bounds + AE-lower-bound-to-`MemLp` + cutoff-sequence-lower-bound constructors (including eventually-in-`n` AE, variable `Bₙ` with eventual uniform control, and Borel-Cantelli bridges from summable bad-event tails / summable majorants / geometric tails / exponential tails) for weight/integrability models landed; globalized shifted-moment nonnegativity and direct square-data `InteractionWeightModel` constructor now in place, with downstream finite-volume/reconstruction square-data endpoints switched to this direct route; both UV and square-data Wick-sublevel linear-growth/reconstruction-input/Wightman-interface/partition-function routes are now switched to direct weight-model construction; shifted geometric-moment branch now also has explicit-data cores (`interaction_ae_nonneg_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound_of_standardSeq_tendsto_ae`, `exp_interaction_Lp_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound_of_aestronglyMeasurable_and_standardSeq_tendsto_ae`, `interactionWeightModel_nonempty_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound_of_aestronglyMeasurable_and_standardSeq_tendsto_ae`), and shifted exponential Wick-sublevel bad-set branch now also has explicit-data cores (`exp_interaction_Lp_of_cutoff_seq_shifted_bad_set_summable_of_aestronglyMeasurable_and_standardSeq_tendsto_ae`, `interactionWeightModel_nonempty_of_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets_of_aestronglyMeasurable_and_standardSeq_tendsto_ae`) | in_progress |

### WP2: Covariance/Boundary/RP grounding

| ID | Issue | Action | Status |
|---|---|---|---|
| CTC-WP2-01 | `FreeCovarianceKernelModel` not constructively instantiated | Develop CLM-to-kernel bridge from existing free-field kernel machinery; constructor scaffolds landed (`freeCovarianceKernelModel_nonempty_of_data`, `freeCovarianceKernelModel_nonempty_of_two_point_kernel`) and reusable free-kernel Bessel/off-diagonal bounds exported in `FreeField.lean` (`freeCovKernel_eq_besselK0` and `K₁` comparison consequences) | in_progress |
| CTC-WP2-02 | Boundary comparison models remain interface-level | Ground `C_D ≤ C ≤ C_N` path in `CovarianceOperators.lean`; constructor scaffolds landed for boundary kernel/comparison/regularity/covariance models, with reusable off-diagonal free-kernel positivity/`K₁` comparison lemmas added | in_progress |

### WP3: Correlation + lattice bridge

| ID | Issue | Action | Status |
|---|---|---|---|
| CTC-WP3-01 | Lattice Griffiths/FKG assumptions remain ungrounded | Develop lattice-to-continuum constructive instances using existing approximation bridges; constructor scaffolds landed for lattice/core correlation interfaces | in_progress |

### WP4: Multiple reflections + infinite volume

| ID | Issue | Action | Status |
|---|---|---|---|
| CTC-WP4-01 | Chessboard / uniform bound still interface-level | Port only non-tautological scratch results and extend with reusable lemmas; added reusable exhaustion-uniform Schwinger bounds in `InfiniteVolumeLimit.lean` (`schwingerN_uniformly_bounded_on_exhaustion`) and refactored two-point exhaustion bounds through this general infrastructure | in_progress |
| CTC-WP4-02 | `gap_infiniteVolumeSchwingerModel_nonempty` depends on upstream interfaces | Close via grounded WP1/WP2/WP3 estimates | blocked |

### WP5/WP6: Regularity/OS/Reconstruction closure

| ID | Issue | Action | Status |
|---|---|---|---|
| CTC-WP5-01 | OS1 and E2 packaging still interface-level | Ground once WP1–WP4 dependencies close | blocked |
| CTC-WP6-01 | `WightmanReconstructionModel` upstream theorem path is not axiom-clean | Keep as explicit final interface; do not discharge with `os_to_wightman_full` | done |

## Scratch/Porting Issues (Section 15)

| ID | Issue | Action | Status |
|---|---|---|---|
| CTC-S-01 | Scratch contains candidate lemmas for porting | Port only proofs that materially reduce downstream blocker surface | in_progress |
| CTC-S-02 | Avoid tautological "∃ C" ports | Require new ports to provide reusable/nontrivial bounds or bridge lemmas | done |

## Active Execution Order

1. Execute `CTC-WP1-02`: start `exp_interaction_Lp` closure chain from semibounded Wick-4 plus localized occupancy bounds.
2. Continue `CTC-WP2-01` by proving a concrete CLM-to-kernel bridge lemma (constructor already in place).
3. Continue `CTC-WP3-01` by constructing first lattice GKS-I / monotonicity instances against approximation data.
4. Continue `CTC-S-01` by porting only non-tautological scratch lemmas that reduce WP1/WP2/WP3 blockers.
5. Re-run trust/build/gap checks before each commit.

## Verification Commands

```bash
lake build Phi4
scripts/check_phi4_trust.sh
grep -RIn "^[[:space:]]*sorry\\b" Phi4 --include='*.lean' | grep -v Scratch
rg -n "^class .*Model" Phi4 --glob '*.lean'
```

## Session Update (2026-02-27, Later)

The upstream items below are dependency-risk mitigation and do not redefine the
primary local Glimm-Jaffe work queue.

- Hard-fixed upstream spectral-power blockers in local OSReconstruction checkout:
  - `UnboundedOperator.power_zero` (removed `sorry`)
  - `UnboundedOperator.power_imaginary_unitary` (removed `sorry`)
- Core fix: corrected the imaginary-power branch convention at nonpositive arguments in
  `.lake/packages/OSReconstruction/OSReconstruction/vNA/Unbounded/Spectral.lean`
  from `else 0` to `else 1`, then completed the functional-calculus proofs.
- Local verification passed:
  - `lake build OSReconstruction.vNA.Unbounded.Spectral`
  - `lake build OSReconstruction.vNA.Unbounded.StoneTheorem`
  - `lake build Phi4`
  - `scripts/check_phi4_trust.sh`
- Added systematic upstream blocker infrastructure:
  - `scripts/upstream_blockers_scan.sh` builds declaration/file inventories,
    priority queues, and merges persistent declaration statuses.
  - `scripts/sync_upstream_blockers_todo.sh` refreshes `TODO.md` from generated
    blocker inventory data.
  - `scripts/upstream_blockers_status.sh` provides queue operations
    (`list`, `claim-next`, `set`, `stats`) for status-driven execution.
  - `scripts/upstream_blockers_prompt.sh` generates declaration-specific
    consultation prompts using the repository policy template.
  - `scripts/upstream_blockers_workpack.sh` produces top-N actionable workpacks
    with build targets, claim commands, and per-declaration prompt files.
  - `docs/upstream_blockers/status.tsv` tracks per-declaration status/owner.

## Session Update (2026-03-04, Route-Bloat Reduction Continuation)

- Continued CTC-A-04 de-bloating with no-caller route deletion and explicit-core
  rewiring:
  - removed class-based shifted Wick-sublevel wrappers in
    `Phi4/Interaction/Part2.lean`,
  - rewired finite-volume and square-data callers to
    `interactionWeightModel_nonempty_of_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets_of_aestronglyMeasurable_and_standardSeq_tendsto_ae`,
  - removed four additional no-caller linear-growth/weight-route variants in
    `Phi4/Interaction/Part1Core.lean` and `Phi4/Interaction/Part1Tail.lean`,
  - removed eleven no-caller `exp_interaction_Lp_of_*` route aliases in
    `Phi4/Interaction/Part2.lean`.
- Updated guard baselines in `scripts/route_bloat_guard.sh`:
  - `_nonempty_of_` cap tightened to `84`,
  - `interactionWeightModel_nonempty_of_*` cap tightened to `13`.
- Current measured surface after this pass:
  - `_nonempty_of_` constructors: `84`,
  - `interactionWeightModel_nonempty_of_*`: `13`,
  - `interactionIntegrabilityModel_nonempty_of_*`: `2`,
  - `gap_phi4_linear_growth*`: `3`,
  - `Interaction/Part2` theorem count: `17` (line count `993`).
- Verification:
  - `lake build Phi4.Interaction.Part2 Phi4.Interaction.Part3 Phi4.FiniteVolumeMeasure Phi4.Reconstruction.Part1Core` passes.
  - `scripts/route_bloat_guard.sh` passes.
  - `scripts/quick_gate.sh` passes end-to-end.

### Follow-up trim (same session)

- Removed four more no-caller `Interaction/Part2` bridges:
  - `exp_interaction_Lp_of_cutoff_seq_shifted_exponential_wick_bad_sets`,
  - `cutoff_seq_eventually_lower_bound_of_exponential_bad_event_bound`,
  - `cutoff_seq_eventually_lower_bound_of_shifted_exponential_bad_event_bound`,
  - `cutoff_seq_eventually_uniform_lower_bound_of_pointwise_bounds`.
- `Interaction/Part2` now has `13` theorems (`890` lines), down from `17` / `993`
  at the previous checkpoint; guard metrics (`_nonempty_of_ = 84`,
  `interactionWeightModel_nonempty_of_* = 13`) remain unchanged and passing.

### Follow-up trim 2 (same session)

- Removed two further no-caller `Interaction/Part2` routes:
  - `exp_interaction_Lp_of_cutoff_seq_shifted_geometric_wick_bad_sets`,
  - `cutoff_seq_eventually_lower_bound_of_geometric_bad_event_bound`.
- `Interaction/Part2` now has `11` theorems (`830` lines), down from `13` / `890`;
  guard metrics still hold (`_nonempty_of_ = 84`,
  `interactionWeightModel_nonempty_of_* = 13`).
- `scripts/route_bloat_guard.sh` was extended to hard-cap
  `Interaction.Part2` theorem count at `11`.

### Follow-up trim 3 + core-chain collapse (same session)

- Removed one more no-caller `Interaction/Part2` route:
  - `exp_interaction_Lp_of_cutoff_seq_shifted_summable_wick_bad_sets`.
- Removed two no-caller forwarding routes from `Interaction/Part1Tail.lean`:
  - `interactionWeightModel_nonempty_of_sq_moment_polynomial_bound_and_geometric_exp_moment_bound`,
  - `interactionWeightModel_nonempty_of_sq_moment_polynomial_bound_and_uniform_integral_bound`.
- Removed two single-use forwarding constructors from
  `Interaction/Part1Core.lean` by inlining into remaining callers:
  - `interactionWeightModel_nonempty_of_standardSeq_succ_tendsto_ae_and_uniform_exp_moment_bound`,
  - `interactionWeightModel_nonempty_of_standardSeq_succ_tendsto_ae_and_geometric_integral_bound`.
- Updated guard baselines in `scripts/route_bloat_guard.sh`:
  - `_nonempty_of_` cap: `80`,
  - `interactionWeightModel_nonempty_of_*` cap: `9`,
  - `Interaction.Part2` theorem cap: `10`.
- Current measured surface after this pass:
  - `_nonempty_of_`: `80`,
  - `interactionWeightModel_nonempty_of_*`: `9`,
  - `interactionIntegrabilityModel_nonempty_of_*`: `2`,
  - `Interaction/Part2` theorem count: `10`.

### Follow-up trim 4 (same session)

- Removed one additional forwarding route in `Interaction/Part1Core.lean`:
  - `interactionWeightModel_nonempty_of_tendsto_ae_and_geometric_exp_moment_bound`,
  and rewired the `Interaction/Part3.lean` caller to the standard-sequence core.
- Removed two no-caller routes in `Interaction/Part2.lean`:
  - `exp_interaction_Lp_of_cutoff_seq_shifted_bad_set_summable`,
  - `cutoff_seq_eventually_lower_bound_of_summable_bad_event_bound`.
- Updated guard baselines in `scripts/route_bloat_guard.sh`:
  - `_nonempty_of_` cap: `79`,
  - `interactionWeightModel_nonempty_of_*` cap: `8`,
  - `Interaction.Part2` theorem cap: `8`.
- Current measured surface:
  - `_nonempty_of_`: `79`,
  - `interactionWeightModel_nonempty_of_*`: `8`,
  - `interactionIntegrabilityModel_nonempty_of_*`: `2`,
  - `Interaction/Part2` theorem count: `8`.

### Infrastructure follow-up (same session)

- Hardened the shifted absolute-moment bridge as an explicit core:
  - `shifted_exponential_moment_geometric_bound_of_abs_at_theta` and
    `shifted_exponential_moment_geometric_bound_of_abs` in
    `Phi4/Interaction/Part2.lean` now take explicit canonical-sequence
    measurability input instead of relying on `[InteractionUVModel params]`.
- Rewired square-data callers to the explicit bridge:
  - removed the temporary `InteractionUVModel` instantiation step in
    `exp_interaction_Lp_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_moment_abs_geometric_bound`
    (`Interaction/Part2.lean`),
  - removed the same class-instantiation detour in
    `interactionWeightModel_nonempty_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_moment_abs_geometric_bound`
    (`Interaction/Part3.lean`).
- Added a reusable square-data composition core in `Interaction/Part3.lean`:
  - `interactionIntegrabilityModel_nonempty_from_sq_integrable_data_and_weight`,
    factoring the repeated
    `interactionUVModel_nonempty_of_sq_integrable_data` + `...uv_weight_nonempty`
    assembly used by multiple hard-core integrability constructors.
- Refactored the geometric-to-uniform cutoff integral bridge in
  `Interaction/Part1Tail.lean`:
  - `standardSeq_succ_uniform_integral_bound_of_geometric_exp_moment_bound`
    now reuses `standardSeq_succ_uniform_integral_bound_of_partition_bound`
    through an internal geometric→partition conversion, eliminating duplicated
    `p = 0` / `p > 0` proof branching.
- Added a reusable shifted-cutoff measurability bridge in
  `Interaction/Part1Core.lean`:
  - `interactionCutoff_standardSeq_succ_aestronglyMeasurable`,
    then rewired repeated local conversions in `Interaction/Part2.lean` and
    `Interaction/Part3.lean` to this single infrastructure lemma.
- Removed two no-caller reconstruction wrappers:
  - `reconstructionLinearGrowthModel_nonempty_of_os_and_explicit_bound`
    (`Reconstruction/Part1Core.lean`),
  - `reconstructionLinearGrowthModel_nonempty_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound`
    (`Reconstruction/Part1Tail.lean`).
- Tightened `scripts/route_bloat_guard.sh` `_nonempty_of_` cap:
  - `79 -> 77`.
- Removed one additional no-caller reconstruction constructor:
  - `reconstructionLinearGrowthModel_nonempty_of_explicit_bound`
    (`Reconstruction/Part1Core.lean`).
- Tightened `scripts/route_bloat_guard.sh` `_nonempty_of_` cap again:
  - `77 -> 76`.
- Verification:
  - `lake build Phi4.Interaction.Part1Core Phi4.Interaction.Part2 Phi4.Interaction.Part3` passes.
  - `lake build Phi4.Reconstruction.Part1Core Phi4.Reconstruction.Part1Tail Phi4.Reconstruction.Part3` passes.
  - `bash scripts/quick_gate.sh` passes with tightened route-bloat caps.

### Reconstruction/Part1Core no-caller cleanup (same session)

- Removed seven no-caller declarations in `Phi4/Reconstruction/Part1Core.lean`:
  - `phi4_linear_growth_constants_of_interface`,
  - `phi4_productTensor_zero_of_compat`,
  - `phi4_productTensor_zero_of_compat_of_moment`,
  - `phi4_productTensor_mixed_bound_of_global_uniform_generating_bound`,
  - `phi4_productTensor_linear_growth_of_global_uniform_generating_bound`,
  - `phi4_productTensor_linear_growth_of_uniform_generating_bound`,
  - `osLinearGrowthCondition_nonempty_of_bound`.
- Tightened `scripts/route_bloat_guard.sh` `_nonempty_of_` cap:
  - `76 -> 75`.
- Verification:
  - `lake build Phi4.Reconstruction.Part1Core Phi4.Reconstruction.Part1 Phi4.Reconstruction.Part2 Phi4.Reconstruction.Part3` passes.
  - `bash scripts/route_bloat_guard.sh` passes with the tightened cap.

### Cross-module interface-wrapper trim (same session)

- Removed four no-caller interface wrappers:
  - `infiniteVolumeSchwinger_mixed_bound_of_interface` (`Regularity.lean`),
  - `schwingerN_nonneg_of_interface` (`CorrelationInequalities.lean`),
  - `schwinger_uniformly_bounded_of_interface` (`InfiniteVolumeLimit/Part1.lean`),
  - `infinite_volume_schwinger_exists_of_interface` (`InfiniteVolumeLimit/Part1.lean`).
- Verification:
  - `lake build Phi4.CorrelationInequalities Phi4.InfiniteVolumeLimit.Part1 Phi4.Regularity Phi4.OSAxioms` passes.
  - `bash scripts/route_bloat_guard.sh` passes.

### Infinite-volume wrapper-route trim (same session)

- Removed eight no-caller wrapper routes:
  - `schwingerN_monotone_of_family` (`CorrelationInequalities.lean`),
  - `schwingerTwo_limit_exists_if_exhaustion_of_models`,
    `schwingerN_two_limit_exists_if_exhaustion_of_models`,
    `schwingerTwo_limit_exists_of_lattice_models`,
    `schwingerN_two_tendsto_iSup_of_lattice_monotone_bounded`,
    `schwingerN_two_limit_exists_of_monotone_bounded`,
    `schwingerN_two_limit_exists_of_models`,
    `schwingerN_two_limit_exists_of_lattice_models`
    (`InfiniteVolumeLimit/Part1.lean`).
- Verification:
  - `lake build Phi4.CorrelationInequalities Phi4.InfiniteVolumeLimit.Part1 Phi4.InfiniteVolumeLimit Phi4.Regularity Phi4.OSAxioms` passes.
  - `bash scripts/quick_gate.sh` passes.

### Deep infinite-volume route thinning (same session)

- Removed twelve additional no-caller route/wrapper theorems from
  `InfiniteVolumeLimit/Part1.lean`:
  - `schwingerN_two_tendsto_if_exhaustion_of_models`,
  - `schwingerTwo_tendsto_iSup_of_lattice_models`,
  - `schwingerTwo_limit_exists_of_monotone_bounded`,
  - `schwingerN_two_tendsto_iSup_of_monotone_bounded`,
  - `schwingerN_two_tendsto_iSup_of_models`,
  - `schwingerN_two_tendsto_iSup_of_lattice_models`,
  - `infinite_volume_schwinger_exists_all_k_of_family_models`,
  - `infinite_volume_schwinger_exists_all_k_of_lattice_family_models`,
  - `infinite_volume_schwinger_exists_four_of_correlationFourPoint_models`,
  - `infinite_volume_schwinger_exists_four_of_correlationInequality_models`,
  - `infinite_volume_schwinger_exists_four_of_lattice_and_core_models`,
  - `infinite_volume_schwinger_exists_two_of_lattice_models`.
- Verification:
  - `lake build Phi4.InfiniteVolumeLimit.Part1 Phi4.InfiniteVolumeLimit Phi4.CorrelationInequalities Phi4.Regularity Phi4.OSAxioms` passes.
  - `bash scripts/quick_gate.sh` passes.

### Final wrapper-prune pass + guard hardening (same session)

- Removed six additional no-caller wrapper routes:
  - `phi4_linear_growth_of_interface_productTensor_approx_and_given_normalized_order0`
    (`Reconstruction/Part1Core.lean`),
  - `schwingerTwo_tendsto_iSup_of_monotone_bounded`,
    `schwingerTwo_tendsto_if_exhaustion_of_models`,
    `schwingerTwo_tendsto_iSup_of_lattice_monotone_bounded`,
    `infinite_volume_schwinger_exists_four_of_correlationCore_models`,
    `infinite_volume_schwinger_exists_two_of_models`
    (`InfiniteVolumeLimit/Part1.lean`).
- Extended `scripts/route_bloat_guard.sh` with
  `InfiniteVolumeLimit/Part1` non-growth caps:
  - theorem count: `34`,
  - `schwingerTwo_*` routes: `5`,
  - `infinite_volume_schwinger_exists_*_of_*` routes: `4`.
- Verification:
  - `lake build Phi4.Reconstruction.Part1Core Phi4.InfiniteVolumeLimit.Part1 Phi4.InfiniteVolumeLimit Phi4.Regularity Phi4.OSAxioms` passes.
  - `bash scripts/quick_gate.sh` passes.

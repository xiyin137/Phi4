#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

# Baselines captured after bloat-reduction refactor (2026-03-04):
# - class .*Model count: 58
# - theorem .*_nonempty_of_ count: 59
# - interactionWeightModel_nonempty_of_* count: 7
# - interactionIntegrabilityModel_nonempty_of_* count: 2
# - gap_phi4_linear_growth variant count in Reconstruction/Part1Core.lean: 2
# - Reconstruction/Part1Core explicit shifted-moment linear-growth wrapper count: 0
# - Reconstruction/Part1Core explicit Wick-sublevel linear-growth-model wrapper count: 0
# - Reconstruction/Part1Core InteractionUVModel wrapper count: 0
# - Reconstruction/Part1Tail InteractionUVModel wrapper count: 0
# - Reconstruction/Part1Tail reconstructionInputModel_nonempty_of_* route count: 0
# - Interaction/Part1Core integrability-to-submodel wrappers: 0
# - Interaction/Part2 top-level theorem count: 8
# - Interaction/Part2 zero-caller weight routes kept at exact zero:
#   - interactionWeightModel_nonempty_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets
#   - interactionWeightModel_nonempty_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound_of_aestronglyMeasurable_and_standardSeq_tendsto_ae
# - Interaction/Part3 zero-caller integrability routes kept at exact zero:
#   - interactionIntegrabilityModel_nonempty_of_sq_integrable_data_and_sq_moment_polynomial_bound_per_volume_and_uniform_partition_bound_of_succ_succ
#   - interactionIntegrabilityModel_nonempty_of_sq_integrable_data_and_higher_moment_polynomial_bound_per_volume_and_uniform_partition_bound_of_succ_succ
#   - interactionIntegrabilityModel_nonempty_of_sq_integrable_data_and_linear_threshold_geometric_exp_moment_and_double_exp_moment_geometric_of_moment_bounds
# - Reconstruction/Part2 top-level theorem count: 1
# - Reconstruction/Part2 *_explicit* theorem count: 0
# - ModelBundle top-level theorem count: 0
# - FiniteVolumeMeasure top-level theorem count: 29
# - FiniteVolumeMeasure finiteVolumeMeasure_isProbability_of_* route count: 1
# - FiniteVolumeMeasure finiteVolumeMeasure_isProbability_of_sq_integrable_data_and_* route count: 0
# - Reconstruction/Part3 top-level theorem count: 5
# - Reconstruction/Part3 phi4_wightman_exists* theorem count: 4
# - InfiniteVolumeLimit/Part1 top-level theorem count: 23
# - InfiniteVolumeLimit/Part1 schwingerTwo_* theorem count: 1
# - InfiniteVolumeLimit/Part1 infinite_volume_schwinger_exists_*_of_* theorem count: 4
# - InfiniteVolumeLimit/Part2 top-level theorem count: 11
# - InfiniteVolumeLimit/Part3 top-level theorem count: 16
# - CorrelationInequalities top-level theorem count: 53
# - Interaction/Part3 abs-moment forwarding wrapper count: 0
# - OSAxioms removed no-caller `_of_data` wrappers kept at exact zero:
#   - osaCoreModel_nonempty_of_data
#   - osDistributionE2Model_nonempty_of_data
#   - osE4ClusterModel_nonempty_of_data
MAX_MODEL_CLASSES=58
MAX_NONEMPTY_CONSTRUCTORS=59
MAX_WEIGHT_ROUTES=7
MAX_INTEGRABILITY_ROUTES=2
MAX_LINEAR_GROWTH_ROUTES=2
MAX_RECON_PART1CORE_EXPLICIT_MOMENT_ROUTE=0
MAX_RECON_PART1CORE_EXPLICIT_WICK_MODEL_ROUTE=0
MAX_RECON_PART1CORE_INTERACTIONUV_WRAPPERS=0
MAX_RECON_PART1TAIL_INTERACTIONUV_WRAPPERS=0
MAX_RECON_PART1TAIL_INPUT_ROUTES=0
MAX_INTERACTION_PART1CORE_UV_FROM_INTEGRABILITY_WRAPPER=0
MAX_INTERACTION_PART1CORE_WEIGHT_FROM_INTEGRABILITY_WRAPPER=0
MAX_INTERACTION_PART2_THEOREMS=8
MAX_INTERACTION_PART2_SQDATA_WICK_WEIGHT_ROUTE=0
MAX_INTERACTION_PART2_EXPLICIT_GEOM_WEIGHT_ROUTE=0
MAX_INTERACTION_PART3_SQMOMENT_SUCCSUCC_ROUTE=0
MAX_INTERACTION_PART3_HIGHERMOMENT_SUCCSUCC_ROUTE=0
MAX_INTERACTION_PART3_DOUBLEEXP_MOMENTBOUNDS_ROUTE=0
MAX_RECON_PART2_THEOREMS=1
MAX_RECON_PART2_EXPLICIT_ROUTES=0
MAX_MODELBUNDLE_THEOREMS=0
MAX_FINITE_VOLUME_THEOREMS=29
MAX_FVM_ISPROB_ROUTES=1
MAX_FVM_SQDATA_ROUTES=0
MAX_RECON_PART3_THEOREMS=5
MAX_RECON_PART3_WIGHTMAN_ROUTES=4
MAX_IVL_PART1_THEOREMS=23
MAX_IVL_PART1_SCHWINGERTWO_ROUTES=1
MAX_IVL_PART1_EXISTS_ROUTES=4
MAX_IVL_PART2_THEOREMS=11
MAX_IVL_PART3_THEOREMS=16
MAX_CORRELATION_THEOREMS=53
MAX_INTERACTION_PART2_EVENTUAL_LOWER_WRAPPER=0
MAX_INTERACTION_PART2_GLOBAL_NONNEG_WRAPPER=0
MAX_IVL_PART1_LATTICE_MONO_TWO_WRAPPER=0
MAX_INTERACTION_PART3_ABS_GEOM_WRAPPER=0
MAX_OSAXIOMS_CORE_DATA_WRAPPER=0
MAX_OSAXIOMS_E2_DATA_WRAPPER=0
MAX_OSAXIOMS_E4_DATA_WRAPPER=0

model_classes="$( (rg -n '^class .*Model' Phi4 --glob '*.lean' || true) | wc -l | tr -d ' ' )"
nonempty_ctors="$( (rg -n '^theorem[[:space:]]+.*_nonempty_of_' Phi4 --glob '*.lean' || true) | wc -l | tr -d ' ' )"
weight_routes="$( (rg -n '^theorem[[:space:]]+interactionWeightModel_nonempty_of_' Phi4/Interaction --glob '*.lean' || true) | wc -l | tr -d ' ' )"
integrability_routes="$( (rg -n '^theorem[[:space:]]+interactionIntegrabilityModel_nonempty_of_' Phi4/Interaction --glob '*.lean' || true) | wc -l | tr -d ' ' )"
linear_growth_routes="$( (rg -n '^theorem[[:space:]]+gap_phi4_linear_growth(_of_[A-Za-z0-9_]+)?' Phi4/Reconstruction/Part1Core.lean || true) | wc -l | tr -d ' ' )"
recon_part1core_explicit_moment_route="$( (rg -n 'gap_phi4_linear_growth_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound_of_aestronglyMeasurable_and_standardSeq_tendsto_ae' Phi4/Reconstruction/Part1Core.lean || true) | wc -l | tr -d ' ' )"
recon_part1core_explicit_wick_model_route="$( (rg -n 'reconstructionLinearGrowthModel_nonempty_of_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets_of_aestronglyMeasurable_and_standardSeq_tendsto_ae' Phi4/Reconstruction/Part1Core.lean || true) | wc -l | tr -d ' ' )"
recon_part1core_interactionuv_wrappers="$( (rg -n '^[[:space:]]*\\[InteractionUVModel params\\]' Phi4/Reconstruction/Part1Core.lean || true) | wc -l | tr -d ' ' )"
recon_part1tail_interactionuv_wrappers="$( (rg -n '^[[:space:]]*\\[InteractionUVModel params\\]' Phi4/Reconstruction/Part1Tail.lean || true) | wc -l | tr -d ' ' )"
recon_part1tail_input_routes="$( (rg -n '^[[:space:]]*reconstructionInputModel_nonempty_of_' Phi4/Reconstruction/Part1Tail.lean || true) | wc -l | tr -d ' ' )"
interaction_part1core_uv_from_integrability_wrapper="$( (rg -n 'interactionUVModel_nonempty_of_integrability_nonempty' Phi4/Interaction/Part1Core.lean || true) | wc -l | tr -d ' ' )"
interaction_part1core_weight_from_integrability_wrapper="$( (rg -n 'interactionWeightModel_nonempty_of_integrability_nonempty' Phi4/Interaction/Part1Core.lean || true) | wc -l | tr -d ' ' )"
interaction_part2_theorem_count="$(rg -n '^theorem[[:space:]]' Phi4/Interaction/Part2.lean | wc -l | tr -d ' ')"
interaction_part2_sqdata_wick_weight_route="$( (rg -n 'interactionWeightModel_nonempty_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets' Phi4/Interaction/Part2.lean || true) | wc -l | tr -d ' ' )"
interaction_part2_explicit_geom_weight_route="$( (rg -n 'interactionWeightModel_nonempty_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound_of_aestronglyMeasurable_and_standardSeq_tendsto_ae' Phi4/Interaction/Part2.lean || true) | wc -l | tr -d ' ' )"
interaction_part3_sqmoment_succsucc_route="$( (rg -n 'interactionIntegrabilityModel_nonempty_of_sq_integrable_data_and_sq_moment_polynomial_bound_per_volume_and_uniform_partition_bound_of_succ_succ' Phi4/Interaction/Part3.lean || true) | wc -l | tr -d ' ' )"
interaction_part3_highermoment_succsucc_route="$( (rg -n 'interactionIntegrabilityModel_nonempty_of_sq_integrable_data_and_higher_moment_polynomial_bound_per_volume_and_uniform_partition_bound_of_succ_succ' Phi4/Interaction/Part3.lean || true) | wc -l | tr -d ' ' )"
interaction_part3_doubleexp_momentbounds_route="$( (rg -n 'interactionIntegrabilityModel_nonempty_of_sq_integrable_data_and_linear_threshold_geometric_exp_moment_and_double_exp_moment_geometric_of_moment_bounds' Phi4/Interaction/Part3.lean || true) | wc -l | tr -d ' ' )"
part2_theorem_count="$(rg -n '^theorem[[:space:]]' Phi4/Reconstruction/Part2.lean | wc -l | tr -d ' ')"
part2_explicit_routes="$( (rg -n '^theorem[[:space:]]+.*_explicit(_|$)' Phi4/Reconstruction/Part2.lean || true) | wc -l | tr -d ' ' )"
modelbundle_theorem_count="$( (rg -n '^theorem[[:space:]]' Phi4/ModelBundle.lean || true) | wc -l | tr -d ' ' )"
finite_volume_theorem_count="$(rg -n '^theorem[[:space:]]' Phi4/FiniteVolumeMeasure.lean | wc -l | tr -d ' ')"
fvm_isprob_routes="$( (rg -n 'finiteVolumeMeasure_isProbability_of_' Phi4/FiniteVolumeMeasure.lean || true) | wc -l | tr -d ' ' )"
fvm_sqdata_routes="$( (rg -n 'finiteVolumeMeasure_isProbability_of_sq_integrable_data_and_' Phi4/FiniteVolumeMeasure.lean || true) | wc -l | tr -d ' ' )"
ivl_part1_theorem_count="$(rg -n '^theorem[[:space:]]' Phi4/InfiniteVolumeLimit/Part1.lean | wc -l | tr -d ' ')"
ivl_part1_schwingerTwo_routes="$( (rg -n '^theorem[[:space:]]+schwingerTwo_' Phi4/InfiniteVolumeLimit/Part1.lean || true) | wc -l | tr -d ' ' )"
ivl_part1_exists_routes="$( (rg -n '^theorem[[:space:]]+infinite_volume_schwinger_exists_.*_of_' Phi4/InfiniteVolumeLimit/Part1.lean || true) | wc -l | tr -d ' ' )"
ivl_part2_theorem_count="$(rg -n '^theorem[[:space:]]' Phi4/InfiniteVolumeLimit/Part2.lean | wc -l | tr -d ' ')"
ivl_part3_theorem_count="$(rg -n '^theorem[[:space:]]' Phi4/InfiniteVolumeLimit/Part3.lean | wc -l | tr -d ' ')"
correlation_theorem_count="$(rg -n '^theorem[[:space:]]' Phi4/CorrelationInequalities.lean | wc -l | tr -d ' ')"
interaction_part2_eventual_lower_wrapper="$( (rg -n 'interactionWeightModel_nonempty_of_cutoff_seq_eventually_lower_bounds_of_aestronglyMeasurable_and_standardSeq_tendsto_ae' Phi4/Interaction/Part2.lean || true) | wc -l | tr -d ' ' )"
interaction_part2_global_nonneg_wrapper="$( (rg -n 'interaction_ae_nonneg_all_rectangles_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound_of_standardSeq_tendsto_ae' Phi4/Interaction/Part2.lean || true) | wc -l | tr -d ' ' )"
ivl_part1_lattice_mono_two_wrapper="$( (rg -n 'schwingerN_monotone_in_volume_two_from_lattice' Phi4/InfiniteVolumeLimit/Part1.lean || true) | wc -l | tr -d ' ' )"
interaction_part3_abs_geom_wrapper="$( (rg -n 'interactionWeightModel_nonempty_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_moment_abs_geometric_bound' Phi4/Interaction/Part3.lean || true) | wc -l | tr -d ' ' )"
osaxioms_core_data_wrapper="$( (rg -n '^[[:space:]]*theorem[[:space:]]+osaCoreModel_nonempty_of_data\\b' Phi4/OSAxioms.lean || true) | wc -l | tr -d ' ' )"
osaxioms_e2_data_wrapper="$( (rg -n '^[[:space:]]*theorem[[:space:]]+osDistributionE2Model_nonempty_of_data\\b' Phi4/OSAxioms.lean || true) | wc -l | tr -d ' ' )"
osaxioms_e4_data_wrapper="$( (rg -n '^[[:space:]]*theorem[[:space:]]+osE4ClusterModel_nonempty_of_data\\b' Phi4/OSAxioms.lean || true) | wc -l | tr -d ' ' )"
part3_theorem_names="$(
  awk '
  /^[[:space:]]*theorem([[:space:]]|$)/{
    line=$0
    sub(/^[[:space:]]*theorem[[:space:]]*/, "", line)
    if (line != "" && line !~ /^--/) {
      split(line, a, /[^A-Za-z0-9_\047]/)
      if (a[1] != "") print a[1]
      pend=0
    } else {
      pend=1
    }
    next
  }
  pend==1{
    line=$0
    if (line ~ /^[[:space:]]*$/) next
    if (line ~ /^[[:space:]]*\/-/) next
    sub(/^[[:space:]]*/, "", line)
    split(line, a, /[^A-Za-z0-9_\047]/)
    if (a[1] != "") print a[1]
    pend=0
  }' Phi4/Reconstruction/Part3.lean
)"
part3_theorem_count="$(printf '%s\n' "$part3_theorem_names" | sed '/^$/d' | wc -l | tr -d ' ')"
part3_wightman_routes="$(printf '%s\n' "$part3_theorem_names" | (rg '^phi4_wightman_exists' || true) | wc -l | tr -d ' ')"

echo "[route_bloat_guard] class .*Model: $model_classes (max $MAX_MODEL_CLASSES)"
echo "[route_bloat_guard] _nonempty_of_ constructors: $nonempty_ctors (max $MAX_NONEMPTY_CONSTRUCTORS)"
echo "[route_bloat_guard] interactionWeightModel routes: $weight_routes (max $MAX_WEIGHT_ROUTES)"
echo "[route_bloat_guard] interactionIntegrabilityModel routes: $integrability_routes (max $MAX_INTEGRABILITY_ROUTES)"
echo "[route_bloat_guard] gap_phi4_linear_growth routes: $linear_growth_routes (max $MAX_LINEAR_GROWTH_ROUTES)"
echo "[route_bloat_guard] Reconstruction.Part1Core explicit shifted-moment wrapper: $recon_part1core_explicit_moment_route (max $MAX_RECON_PART1CORE_EXPLICIT_MOMENT_ROUTE)"
echo "[route_bloat_guard] Reconstruction.Part1Core explicit Wick-model wrapper: $recon_part1core_explicit_wick_model_route (max $MAX_RECON_PART1CORE_EXPLICIT_WICK_MODEL_ROUTE)"
echo "[route_bloat_guard] Reconstruction.Part1Core InteractionUV wrappers: $recon_part1core_interactionuv_wrappers (max $MAX_RECON_PART1CORE_INTERACTIONUV_WRAPPERS)"
echo "[route_bloat_guard] Reconstruction.Part1Tail InteractionUV wrappers: $recon_part1tail_interactionuv_wrappers (max $MAX_RECON_PART1TAIL_INTERACTIONUV_WRAPPERS)"
echo "[route_bloat_guard] Reconstruction.Part1Tail reconstructionInput routes: $recon_part1tail_input_routes (max $MAX_RECON_PART1TAIL_INPUT_ROUTES)"
echo "[route_bloat_guard] Interaction.Part1Core UV-from-integrability wrapper: $interaction_part1core_uv_from_integrability_wrapper (max $MAX_INTERACTION_PART1CORE_UV_FROM_INTEGRABILITY_WRAPPER)"
echo "[route_bloat_guard] Interaction.Part1Core weight-from-integrability wrapper: $interaction_part1core_weight_from_integrability_wrapper (max $MAX_INTERACTION_PART1CORE_WEIGHT_FROM_INTEGRABILITY_WRAPPER)"
echo "[route_bloat_guard] Interaction.Part2 theorem count: $interaction_part2_theorem_count (max $MAX_INTERACTION_PART2_THEOREMS)"
echo "[route_bloat_guard] Interaction.Part2 sq-data Wick weight route: $interaction_part2_sqdata_wick_weight_route (max $MAX_INTERACTION_PART2_SQDATA_WICK_WEIGHT_ROUTE)"
echo "[route_bloat_guard] Interaction.Part2 explicit geometric weight route: $interaction_part2_explicit_geom_weight_route (max $MAX_INTERACTION_PART2_EXPLICIT_GEOM_WEIGHT_ROUTE)"
echo "[route_bloat_guard] Interaction.Part3 sq-moment succ-succ route: $interaction_part3_sqmoment_succsucc_route (max $MAX_INTERACTION_PART3_SQMOMENT_SUCCSUCC_ROUTE)"
echo "[route_bloat_guard] Interaction.Part3 higher-moment succ-succ route: $interaction_part3_highermoment_succsucc_route (max $MAX_INTERACTION_PART3_HIGHERMOMENT_SUCCSUCC_ROUTE)"
echo "[route_bloat_guard] Interaction.Part3 double-exp moment-bounds route: $interaction_part3_doubleexp_momentbounds_route (max $MAX_INTERACTION_PART3_DOUBLEEXP_MOMENTBOUNDS_ROUTE)"
echo "[route_bloat_guard] Reconstruction.Part2 theorem count: $part2_theorem_count (max $MAX_RECON_PART2_THEOREMS)"
echo "[route_bloat_guard] Reconstruction.Part2 *_explicit* theorem count: $part2_explicit_routes (max $MAX_RECON_PART2_EXPLICIT_ROUTES)"
echo "[route_bloat_guard] ModelBundle theorem count: $modelbundle_theorem_count (max $MAX_MODELBUNDLE_THEOREMS)"
echo "[route_bloat_guard] FiniteVolumeMeasure theorem count: $finite_volume_theorem_count (max $MAX_FINITE_VOLUME_THEOREMS)"
echo "[route_bloat_guard] FiniteVolumeMeasure isProbability_of routes: $fvm_isprob_routes (max $MAX_FVM_ISPROB_ROUTES)"
echo "[route_bloat_guard] FiniteVolumeMeasure sq-data isProbability routes: $fvm_sqdata_routes (max $MAX_FVM_SQDATA_ROUTES)"
echo "[route_bloat_guard] InfiniteVolumeLimit.Part1 theorem count: $ivl_part1_theorem_count (max $MAX_IVL_PART1_THEOREMS)"
echo "[route_bloat_guard] InfiniteVolumeLimit.Part1 schwingerTwo_* routes: $ivl_part1_schwingerTwo_routes (max $MAX_IVL_PART1_SCHWINGERTWO_ROUTES)"
echo "[route_bloat_guard] InfiniteVolumeLimit.Part1 infinite_volume_schwinger_exists_*_of_* routes: $ivl_part1_exists_routes (max $MAX_IVL_PART1_EXISTS_ROUTES)"
echo "[route_bloat_guard] InfiniteVolumeLimit.Part2 theorem count: $ivl_part2_theorem_count (max $MAX_IVL_PART2_THEOREMS)"
echo "[route_bloat_guard] InfiniteVolumeLimit.Part3 theorem count: $ivl_part3_theorem_count (max $MAX_IVL_PART3_THEOREMS)"
echo "[route_bloat_guard] CorrelationInequalities theorem count: $correlation_theorem_count (max $MAX_CORRELATION_THEOREMS)"
echo "[route_bloat_guard] Reconstruction.Part3 theorem count: $part3_theorem_count (max $MAX_RECON_PART3_THEOREMS)"
echo "[route_bloat_guard] Reconstruction.Part3 phi4_wightman_exists* routes: $part3_wightman_routes (max $MAX_RECON_PART3_WIGHTMAN_ROUTES)"
echo "[route_bloat_guard] Interaction.Part2 eventual-lower wrapper: $interaction_part2_eventual_lower_wrapper (max $MAX_INTERACTION_PART2_EVENTUAL_LOWER_WRAPPER)"
echo "[route_bloat_guard] Interaction.Part2 global nonneg wrapper: $interaction_part2_global_nonneg_wrapper (max $MAX_INTERACTION_PART2_GLOBAL_NONNEG_WRAPPER)"
echo "[route_bloat_guard] InfiniteVolumeLimit.Part1 lattice mono-two wrapper: $ivl_part1_lattice_mono_two_wrapper (max $MAX_IVL_PART1_LATTICE_MONO_TWO_WRAPPER)"
echo "[route_bloat_guard] Interaction.Part3 abs-moment wrapper: $interaction_part3_abs_geom_wrapper (max $MAX_INTERACTION_PART3_ABS_GEOM_WRAPPER)"
echo "[route_bloat_guard] OSAxioms core-data wrapper: $osaxioms_core_data_wrapper (max $MAX_OSAXIOMS_CORE_DATA_WRAPPER)"
echo "[route_bloat_guard] OSAxioms E2-data wrapper: $osaxioms_e2_data_wrapper (max $MAX_OSAXIOMS_E2_DATA_WRAPPER)"
echo "[route_bloat_guard] OSAxioms E4-data wrapper: $osaxioms_e4_data_wrapper (max $MAX_OSAXIOMS_E4_DATA_WRAPPER)"

fail=0
if (( model_classes > MAX_MODEL_CLASSES )); then
  echo "[FAIL] Model-class count exceeded baseline." >&2
  fail=1
fi
if (( nonempty_ctors > MAX_NONEMPTY_CONSTRUCTORS )); then
  echo "[FAIL] _nonempty_of_ constructor count exceeded baseline." >&2
  fail=1
fi
if (( weight_routes > MAX_WEIGHT_ROUTES )); then
  echo "[FAIL] interactionWeightModel route count exceeded baseline." >&2
  fail=1
fi
if (( integrability_routes > MAX_INTEGRABILITY_ROUTES )); then
  echo "[FAIL] interactionIntegrabilityModel route count exceeded baseline." >&2
  fail=1
fi
if (( linear_growth_routes > MAX_LINEAR_GROWTH_ROUTES )); then
  echo "[FAIL] gap_phi4_linear_growth route count exceeded baseline." >&2
  fail=1
fi
if (( recon_part1core_explicit_moment_route > MAX_RECON_PART1CORE_EXPLICIT_MOMENT_ROUTE )); then
  echo "[FAIL] Reconstruction.Part1Core explicit shifted-moment wrapper count exceeded baseline." >&2
  fail=1
fi
if (( recon_part1core_explicit_wick_model_route > MAX_RECON_PART1CORE_EXPLICIT_WICK_MODEL_ROUTE )); then
  echo "[FAIL] Reconstruction.Part1Core explicit Wick-model wrapper count exceeded baseline." >&2
  fail=1
fi
if (( recon_part1core_interactionuv_wrappers > MAX_RECON_PART1CORE_INTERACTIONUV_WRAPPERS )); then
  echo "[FAIL] Reconstruction.Part1Core InteractionUV wrapper count exceeded baseline." >&2
  fail=1
fi
if (( recon_part1tail_interactionuv_wrappers > MAX_RECON_PART1TAIL_INTERACTIONUV_WRAPPERS )); then
  echo "[FAIL] Reconstruction.Part1Tail InteractionUV wrapper count exceeded baseline." >&2
  fail=1
fi
if (( recon_part1tail_input_routes > MAX_RECON_PART1TAIL_INPUT_ROUTES )); then
  echo "[FAIL] Reconstruction.Part1Tail reconstructionInput route count exceeded baseline." >&2
  fail=1
fi
if (( interaction_part1core_uv_from_integrability_wrapper > MAX_INTERACTION_PART1CORE_UV_FROM_INTEGRABILITY_WRAPPER )); then
  echo "[FAIL] Interaction.Part1Core UV-from-integrability wrapper count exceeded baseline." >&2
  fail=1
fi
if (( interaction_part1core_weight_from_integrability_wrapper > MAX_INTERACTION_PART1CORE_WEIGHT_FROM_INTEGRABILITY_WRAPPER )); then
  echo "[FAIL] Interaction.Part1Core weight-from-integrability wrapper count exceeded baseline." >&2
  fail=1
fi
if (( interaction_part2_theorem_count > MAX_INTERACTION_PART2_THEOREMS )); then
  echo "[FAIL] Interaction.Part2 theorem count exceeded baseline." >&2
  fail=1
fi
if (( interaction_part2_sqdata_wick_weight_route > MAX_INTERACTION_PART2_SQDATA_WICK_WEIGHT_ROUTE )); then
  echo "[FAIL] Interaction.Part2 sq-data Wick weight route count exceeded baseline." >&2
  fail=1
fi
if (( interaction_part2_explicit_geom_weight_route > MAX_INTERACTION_PART2_EXPLICIT_GEOM_WEIGHT_ROUTE )); then
  echo "[FAIL] Interaction.Part2 explicit geometric weight route count exceeded baseline." >&2
  fail=1
fi
if (( interaction_part3_sqmoment_succsucc_route > MAX_INTERACTION_PART3_SQMOMENT_SUCCSUCC_ROUTE )); then
  echo "[FAIL] Interaction.Part3 sq-moment succ-succ route count exceeded baseline." >&2
  fail=1
fi
if (( interaction_part3_highermoment_succsucc_route > MAX_INTERACTION_PART3_HIGHERMOMENT_SUCCSUCC_ROUTE )); then
  echo "[FAIL] Interaction.Part3 higher-moment succ-succ route count exceeded baseline." >&2
  fail=1
fi
if (( interaction_part3_doubleexp_momentbounds_route > MAX_INTERACTION_PART3_DOUBLEEXP_MOMENTBOUNDS_ROUTE )); then
  echo "[FAIL] Interaction.Part3 double-exp moment-bounds route count exceeded baseline." >&2
  fail=1
fi
if (( part2_theorem_count > MAX_RECON_PART2_THEOREMS )); then
  echo "[FAIL] Reconstruction.Part2 theorem count exceeded baseline." >&2
  fail=1
fi
if (( part2_explicit_routes > MAX_RECON_PART2_EXPLICIT_ROUTES )); then
  echo "[FAIL] Reconstruction.Part2 explicit-route count exceeded baseline." >&2
  fail=1
fi
if (( modelbundle_theorem_count > MAX_MODELBUNDLE_THEOREMS )); then
  echo "[FAIL] ModelBundle theorem count exceeded baseline." >&2
  fail=1
fi
if (( finite_volume_theorem_count > MAX_FINITE_VOLUME_THEOREMS )); then
  echo "[FAIL] FiniteVolumeMeasure theorem count exceeded baseline." >&2
  fail=1
fi
if (( fvm_isprob_routes > MAX_FVM_ISPROB_ROUTES )); then
  echo "[FAIL] FiniteVolumeMeasure isProbability_of route count exceeded baseline." >&2
  fail=1
fi
if (( fvm_sqdata_routes > MAX_FVM_SQDATA_ROUTES )); then
  echo "[FAIL] FiniteVolumeMeasure sq-data isProbability route count exceeded baseline." >&2
  fail=1
fi
if (( ivl_part1_theorem_count > MAX_IVL_PART1_THEOREMS )); then
  echo "[FAIL] InfiniteVolumeLimit.Part1 theorem count exceeded baseline." >&2
  fail=1
fi
if (( ivl_part1_schwingerTwo_routes > MAX_IVL_PART1_SCHWINGERTWO_ROUTES )); then
  echo "[FAIL] InfiniteVolumeLimit.Part1 schwingerTwo route count exceeded baseline." >&2
  fail=1
fi
if (( ivl_part1_exists_routes > MAX_IVL_PART1_EXISTS_ROUTES )); then
  echo "[FAIL] InfiniteVolumeLimit.Part1 existence-route count exceeded baseline." >&2
  fail=1
fi
if (( ivl_part2_theorem_count > MAX_IVL_PART2_THEOREMS )); then
  echo "[FAIL] InfiniteVolumeLimit.Part2 theorem count exceeded baseline." >&2
  fail=1
fi
if (( ivl_part3_theorem_count > MAX_IVL_PART3_THEOREMS )); then
  echo "[FAIL] InfiniteVolumeLimit.Part3 theorem count exceeded baseline." >&2
  fail=1
fi
if (( correlation_theorem_count > MAX_CORRELATION_THEOREMS )); then
  echo "[FAIL] CorrelationInequalities theorem count exceeded baseline." >&2
  fail=1
fi
if (( part3_theorem_count > MAX_RECON_PART3_THEOREMS )); then
  echo "[FAIL] Reconstruction.Part3 theorem count exceeded baseline." >&2
  fail=1
fi
if (( part3_wightman_routes > MAX_RECON_PART3_WIGHTMAN_ROUTES )); then
  echo "[FAIL] Reconstruction.Part3 phi4_wightman_exists route count exceeded baseline." >&2
  fail=1
fi
if (( interaction_part2_eventual_lower_wrapper > MAX_INTERACTION_PART2_EVENTUAL_LOWER_WRAPPER )); then
  echo "[FAIL] Interaction.Part2 eventual-lower wrapper count exceeded baseline." >&2
  fail=1
fi
if (( interaction_part2_global_nonneg_wrapper > MAX_INTERACTION_PART2_GLOBAL_NONNEG_WRAPPER )); then
  echo "[FAIL] Interaction.Part2 global nonneg wrapper count exceeded baseline." >&2
  fail=1
fi
if (( ivl_part1_lattice_mono_two_wrapper > MAX_IVL_PART1_LATTICE_MONO_TWO_WRAPPER )); then
  echo "[FAIL] InfiniteVolumeLimit.Part1 lattice mono-two wrapper count exceeded baseline." >&2
  fail=1
fi
if (( interaction_part3_abs_geom_wrapper > MAX_INTERACTION_PART3_ABS_GEOM_WRAPPER )); then
  echo "[FAIL] Interaction.Part3 abs-moment wrapper count exceeded baseline." >&2
  fail=1
fi
if (( osaxioms_core_data_wrapper > MAX_OSAXIOMS_CORE_DATA_WRAPPER )); then
  echo "[FAIL] OSAxioms core-data wrapper count exceeded baseline." >&2
  fail=1
fi
if (( osaxioms_e2_data_wrapper > MAX_OSAXIOMS_E2_DATA_WRAPPER )); then
  echo "[FAIL] OSAxioms E2-data wrapper count exceeded baseline." >&2
  fail=1
fi
if (( osaxioms_e4_data_wrapper > MAX_OSAXIOMS_E4_DATA_WRAPPER )); then
  echo "[FAIL] OSAxioms E4-data wrapper count exceeded baseline." >&2
  fail=1
fi

if (( fail != 0 )); then
  exit 1
fi

echo "[route_bloat_guard] OK"

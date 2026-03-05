#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

# Baselines captured after bloat-reduction refactor (2026-03-05):
# - class .*Model count: 58
# - theorem .*_nonempty_of_ count: 11
# - interactionWeightModel_nonempty_of_* count: 5
# - interactionIntegrabilityModel_nonempty_of_* count: 1
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
# - FiniteVolumeMeasure top-level theorem count: 28
# - FiniteVolumeMeasure finiteVolumeMeasure_isProbability_of_* route count: 0
# - FiniteVolumeMeasure finiteVolumeMeasure_isProbability_of_sq_integrable_data_and_* route count: 0
# - Reconstruction/Part3 top-level theorem count: 3
# - Reconstruction/Part3 phi4_wightman_exists* theorem count: 3
# - InfiniteVolumeLimit/Part1 top-level theorem count: 19
# - InfiniteVolumeLimit/Part1 schwingerTwo_* theorem count: 1
# - InfiniteVolumeLimit/Part1 infinite_volume_schwinger_exists_*_of_* theorem count: 4
# - InfiniteVolumeLimit/Part2 top-level theorem count: 11
# - InfiniteVolumeLimit/Part3 top-level theorem count: 16
# - CorrelationInequalities top-level theorem count: 34
# - Interaction/Part3 abs-moment forwarding wrapper count: 0
# - OSAxioms removed no-caller `_of_data` wrappers kept at exact zero:
#   - osaCoreModel_nonempty_of_data
#   - osDistributionE2Model_nonempty_of_data
#   - osE4ClusterModel_nonempty_of_data
# - Reconstruction/Part1Core removed interface-forwarding wrappers kept at exact zero:
#   - phi4_linear_growth_of_interface
#   - phi4_wightman_reconstruction_step_of_interface
# - Regularity removed no-caller uniform-data wrapper kept at exact zero:
#   - nonlocalPhi4BoundModel_nonempty_of_uniform_data
# - CorrelationInequalities removed no-caller lattice nonempty wrapper kept at exact zero:
#   - correlationInequalityModel_nonempty_of_lattice
# - Additional removed no-caller data constructors kept at exact zero:
#   - correlationGKSSecondModel_nonempty_of_data
#   - correlationLebowitzModel_nonempty_of_data
#   - correlationFourPointInequalityModel_nonempty_of_models
#   - correlationFKGModel_nonempty_of_data
#   - correlationFourPointInequalityModel_nonempty_of_data
#   - correlationInequalityCoreModel_nonempty_of_data
#   - interactionIntegrabilityModel_nonempty_of_data
#   - boundaryKernelModel_nonempty_of_data
#   - boundaryComparisonModel_nonempty_of_data
#   - boundaryRegularityModel_nonempty_of_data
#   - boundaryCovarianceModel_nonempty_of_data
#   - feynmanGraphEstimateModel_nonempty_of_expansion_and_phi4_weighted
#   - freeCovarianceKernelModel_nonempty_of_two_point_kernel
#   - interactionWeightModel_nonempty_of_tendsto_ae_and_geometric_integral_bound
#   - regularityModel_nonempty_of_wick_eom_exhaustion_limit_global_uniform
#   - wightmanReconstructionModel_nonempty_of_os_to_wightman
#   - wickCubicConvergenceModel_nonempty_of_data
#   - euclideanEquationModel_nonempty_of_data
#   - regularityModel_nonempty_of_submodel_nonempty
#   - freeCovarianceKernelModel_nonempty_of_data
#   - wightmanReconstructionModel_nonempty_of_data
#   - feynmanGraphEstimateModel_nonempty_of_expansion_and_degree_weighted
#   - generatingFunctionalBoundModel_nonempty_of_exhaustion_limit_global_uniform
#   - uniformGeneratingFunctionalBoundModel_nonempty_of_global_uniform
#   - nonlocalPhi4BoundModel_nonempty_of_global_uniform
#   - generatingFunctionalBoundModel_nonempty_of_data
#   - uniformGeneratingFunctionalBoundModel_nonempty_of_data
#   - nonlocalPhi4BoundModel_nonempty_of_data
MAX_MODEL_CLASSES=58
MAX_NONEMPTY_CONSTRUCTORS=11
MAX_WEIGHT_ROUTES=5
MAX_INTEGRABILITY_ROUTES=1
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
MAX_FINITE_VOLUME_THEOREMS=28
MAX_FVM_ISPROB_ROUTES=0
MAX_FVM_SQDATA_ROUTES=0
MAX_RECON_PART3_THEOREMS=3
MAX_RECON_PART3_WIGHTMAN_ROUTES=3
MAX_IVL_PART1_THEOREMS=19
MAX_IVL_PART1_SCHWINGERTWO_ROUTES=1
MAX_IVL_PART1_EXISTS_ROUTES=4
MAX_IVL_PART2_THEOREMS=11
MAX_IVL_PART3_THEOREMS=16
MAX_CORRELATION_THEOREMS=34
MAX_INTERACTION_PART2_EVENTUAL_LOWER_WRAPPER=0
MAX_INTERACTION_PART2_GLOBAL_NONNEG_WRAPPER=0
MAX_IVL_PART1_LATTICE_MONO_TWO_WRAPPER=0
MAX_INTERACTION_PART3_ABS_GEOM_WRAPPER=0
MAX_OSAXIOMS_CORE_DATA_WRAPPER=0
MAX_OSAXIOMS_E2_DATA_WRAPPER=0
MAX_OSAXIOMS_E4_DATA_WRAPPER=0
MAX_RECON_PART1CORE_LINEAR_INTERFACE_WRAPPER=0
MAX_RECON_PART1CORE_WIGHTMAN_INTERFACE_WRAPPER=0
MAX_REGULARITY_NONLOCAL_UNIFORM_WRAPPER=0
MAX_CORRELATION_LATTICE_NONEMPTY_WRAPPER=0
MAX_CORRELATION_FOURPOINT_INEQ_DATA_WRAPPER=0
MAX_CORRELATION_CORE_DATA_WRAPPER=0
MAX_INTERACTION_INTEGRABILITY_DATA_WRAPPER=0
MAX_CORRELATION_GKS_DATA_WRAPPER=0
MAX_CORRELATION_LEBOWITZ_DATA_WRAPPER=0
MAX_CORRELATION_FOURPOINT_MODELS_WRAPPER=0
MAX_CORRELATION_FKG_DATA_WRAPPER=0
MAX_BOUNDARY_KERNEL_DATA_WRAPPER=0
MAX_BOUNDARY_COMPARISON_DATA_WRAPPER=0
MAX_BOUNDARY_REGULARITY_DATA_WRAPPER=0
MAX_BOUNDARY_COVARIANCE_DATA_WRAPPER=0
MAX_LOCALIZEDBOUNDS_GRAPH_ESTIMATE_WEIGHTED_WRAPPER=0
MAX_FREEFIELD_COVARIANCE_KERNEL_TWOPOINT_WRAPPER=0
MAX_INTERACTION_WEIGHT_TENDSTO_AE_GEOM_INTEGRAL_WRAPPER=0
MAX_REGULARITY_FULL_PACKAGING_WRAPPER=0
MAX_RECON_UPSTREAM_WIGHTMAN_MODEL_WRAPPER=0
MAX_REGULARITY_WICKCUBIC_DATA_WRAPPER=0
MAX_REGULARITY_EUCLIDEAN_DATA_WRAPPER=0
MAX_REGULARITY_SUBMODEL_NONEMPTY_WRAPPER=0
MAX_FREEFIELD_COVARIANCE_KERNEL_DATA_WRAPPER=0
MAX_RECON_PART1TAIL_WIGHTMAN_DATA_WRAPPER=0
MAX_LOCALIZEDBOUNDS_DEGREE_WEIGHTED_MODEL_WRAPPER=0
MAX_REGULARITY_GFBOUND_EXHAUSTION_GLOBAL_WRAPPER=0
MAX_REGULARITY_UNIFORM_GLOBAL_WRAPPER=0
MAX_REGULARITY_NONLOCAL_GLOBAL_WRAPPER=0
MAX_REGULARITY_GFBOUND_DATA_WRAPPER=0
MAX_REGULARITY_UNIFORM_DATA_WRAPPER=0
MAX_REGULARITY_NONLOCAL_DATA_WRAPPER=0

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
recon_part1core_linear_interface_wrapper="$( (rg -n '^[[:space:]]*theorem[[:space:]]+phi4_linear_growth_of_interface\\b' Phi4/Reconstruction/Part1Core.lean || true) | wc -l | tr -d ' ' )"
recon_part1core_wightman_interface_wrapper="$( (rg -n '^[[:space:]]*theorem[[:space:]]+phi4_wightman_reconstruction_step_of_interface\\b' Phi4/Reconstruction/Part1Core.lean || true) | wc -l | tr -d ' ' )"
regularity_nonlocal_uniform_wrapper="$( (rg -n '^[[:space:]]*theorem[[:space:]]+nonlocalPhi4BoundModel_nonempty_of_uniform_data\\b' Phi4/Regularity.lean || true) | wc -l | tr -d ' ' )"
correlation_lattice_nonempty_wrapper="$( (rg -n '^[[:space:]]*theorem[[:space:]]+correlationInequalityModel_nonempty_of_lattice\\b' Phi4/CorrelationInequalities.lean || true) | wc -l | tr -d ' ' )"
correlation_fourpoint_ineq_data_wrapper="$( (rg -n '^[[:space:]]*theorem[[:space:]]+correlationFourPointInequalityModel_nonempty_of_data\\b' Phi4/CorrelationInequalities.lean || true) | wc -l | tr -d ' ' )"
correlation_core_data_wrapper="$( (rg -n '^[[:space:]]*theorem[[:space:]]+correlationInequalityCoreModel_nonempty_of_data\\b' Phi4/CorrelationInequalities.lean || true) | wc -l | tr -d ' ' )"
interaction_integrability_data_wrapper="$( (rg -n '^[[:space:]]*theorem[[:space:]]+interactionIntegrabilityModel_nonempty_of_data\\b' Phi4/Interaction/Part1Core.lean || true) | wc -l | tr -d ' ' )"
correlation_gks_data_wrapper="$( (rg -n '^[[:space:]]*theorem[[:space:]]+correlationGKSSecondModel_nonempty_of_data\\b' Phi4/CorrelationInequalities.lean || true) | wc -l | tr -d ' ' )"
correlation_lebowitz_data_wrapper="$( (rg -n '^[[:space:]]*theorem[[:space:]]+correlationLebowitzModel_nonempty_of_data\\b' Phi4/CorrelationInequalities.lean || true) | wc -l | tr -d ' ' )"
correlation_fourpoint_models_wrapper="$( (rg -n '^[[:space:]]*theorem[[:space:]]+correlationFourPointInequalityModel_nonempty_of_models\\b' Phi4/CorrelationInequalities.lean || true) | wc -l | tr -d ' ' )"
correlation_fkg_data_wrapper="$( (rg -n '^[[:space:]]*theorem[[:space:]]+correlationFKGModel_nonempty_of_data\\b' Phi4/CorrelationInequalities.lean || true) | wc -l | tr -d ' ' )"
boundary_kernel_data_wrapper="$( (rg -n '^[[:space:]]*theorem[[:space:]]+boundaryKernelModel_nonempty_of_data\\b' Phi4/CovarianceOperators.lean || true) | wc -l | tr -d ' ' )"
boundary_comparison_data_wrapper="$( (rg -n '^[[:space:]]*theorem[[:space:]]+boundaryComparisonModel_nonempty_of_data\\b' Phi4/CovarianceOperators.lean || true) | wc -l | tr -d ' ' )"
boundary_regularity_data_wrapper="$( (rg -n '^[[:space:]]*theorem[[:space:]]+boundaryRegularityModel_nonempty_of_data\\b' Phi4/CovarianceOperators.lean || true) | wc -l | tr -d ' ' )"
boundary_covariance_data_wrapper="$( (rg -n '^[[:space:]]*theorem[[:space:]]+boundaryCovarianceModel_nonempty_of_data\\b' Phi4/CovarianceOperators.lean || true) | wc -l | tr -d ' ' )"
localizedbounds_graph_estimate_weighted_wrapper="$( (rg -n '^[[:space:]]*theorem[[:space:]]+feynmanGraphEstimateModel_nonempty_of_expansion_and_phi4_weighted\\b' Phi4/FeynmanGraphs/LocalizedBounds.lean || true) | wc -l | tr -d ' ' )"
freefield_covariance_kernel_twopoint_wrapper="$( (rg -n '^[[:space:]]*theorem[[:space:]]+freeCovarianceKernelModel_nonempty_of_two_point_kernel\\b' Phi4/FreeField.lean || true) | wc -l | tr -d ' ' )"
interaction_weight_tendsto_ae_geom_integral_wrapper="$( (rg -n '^[[:space:]]*theorem[[:space:]]+interactionWeightModel_nonempty_of_tendsto_ae_and_geometric_integral_bound\\b' Phi4/Interaction/Part1Core.lean || true) | wc -l | tr -d ' ' )"
regularity_full_packaging_wrapper="$( (rg -n '^[[:space:]]*theorem[[:space:]]+regularityModel_nonempty_of_wick_eom_exhaustion_limit_global_uniform\\b' Phi4/Regularity.lean || true) | wc -l | tr -d ' ' )"
recon_upstream_wightman_model_wrapper="$( (rg -n '^[[:space:]]*theorem[[:space:]]+wightmanReconstructionModel_nonempty_of_os_to_wightman\\b' Phi4/ReconstructionUpstream.lean || true) | wc -l | tr -d ' ' )"
regularity_wickcubic_data_wrapper="$( (rg -n '^[[:space:]]*theorem[[:space:]]+wickCubicConvergenceModel_nonempty_of_data\\b' Phi4/Regularity.lean || true) | wc -l | tr -d ' ' )"
regularity_euclidean_data_wrapper="$( (rg -n '^[[:space:]]*theorem[[:space:]]+euclideanEquationModel_nonempty_of_data\\b' Phi4/Regularity.lean || true) | wc -l | tr -d ' ' )"
regularity_submodel_nonempty_wrapper="$( (rg -n '^[[:space:]]*theorem[[:space:]]+regularityModel_nonempty_of_submodel_nonempty\\b' Phi4/Regularity.lean || true) | wc -l | tr -d ' ' )"
freefield_covariance_kernel_data_wrapper="$( (rg -n '^[[:space:]]*theorem[[:space:]]+freeCovarianceKernelModel_nonempty_of_data\\b' Phi4/FreeField.lean || true) | wc -l | tr -d ' ' )"
recon_part1tail_wightman_data_wrapper="$( (rg -n '^[[:space:]]*theorem[[:space:]]+wightmanReconstructionModel_nonempty_of_data\\b' Phi4/Reconstruction/Part1Tail.lean || true) | wc -l | tr -d ' ' )"
localizedbounds_degree_weighted_model_wrapper="$( (rg -n '^[[:space:]]*theorem[[:space:]]+feynmanGraphEstimateModel_nonempty_of_expansion_and_degree_weighted\\b' Phi4/FeynmanGraphs/LocalizedBounds.lean || true) | wc -l | tr -d ' ' )"
regularity_gfbound_exhaustion_global_wrapper="$( (rg -n '^[[:space:]]*theorem[[:space:]]+generatingFunctionalBoundModel_nonempty_of_exhaustion_limit_global_uniform\\b' Phi4/Regularity.lean || true) | wc -l | tr -d ' ' )"
regularity_uniform_global_wrapper="$( (rg -n '^[[:space:]]*theorem[[:space:]]+uniformGeneratingFunctionalBoundModel_nonempty_of_global_uniform\\b' Phi4/Regularity.lean || true) | wc -l | tr -d ' ' )"
regularity_nonlocal_global_wrapper="$( (rg -n '^[[:space:]]*theorem[[:space:]]+nonlocalPhi4BoundModel_nonempty_of_global_uniform\\b' Phi4/Regularity.lean || true) | wc -l | tr -d ' ' )"
regularity_gfbound_data_wrapper="$( (rg -n '^[[:space:]]*theorem[[:space:]]+generatingFunctionalBoundModel_nonempty_of_data\\b' Phi4/Regularity.lean || true) | wc -l | tr -d ' ' )"
regularity_uniform_data_wrapper="$( (rg -n '^[[:space:]]*theorem[[:space:]]+uniformGeneratingFunctionalBoundModel_nonempty_of_data\\b' Phi4/Regularity.lean || true) | wc -l | tr -d ' ' )"
regularity_nonlocal_data_wrapper="$( (rg -n '^[[:space:]]*theorem[[:space:]]+nonlocalPhi4BoundModel_nonempty_of_data\\b' Phi4/Regularity.lean || true) | wc -l | tr -d ' ' )"
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
echo "[route_bloat_guard] Reconstruction.Part1Core linear-interface wrapper: $recon_part1core_linear_interface_wrapper (max $MAX_RECON_PART1CORE_LINEAR_INTERFACE_WRAPPER)"
echo "[route_bloat_guard] Reconstruction.Part1Core wightman-interface wrapper: $recon_part1core_wightman_interface_wrapper (max $MAX_RECON_PART1CORE_WIGHTMAN_INTERFACE_WRAPPER)"
echo "[route_bloat_guard] Regularity nonlocal-uniform wrapper: $regularity_nonlocal_uniform_wrapper (max $MAX_REGULARITY_NONLOCAL_UNIFORM_WRAPPER)"
echo "[route_bloat_guard] Correlation lattice nonempty wrapper: $correlation_lattice_nonempty_wrapper (max $MAX_CORRELATION_LATTICE_NONEMPTY_WRAPPER)"
echo "[route_bloat_guard] Correlation four-point inequality data wrapper: $correlation_fourpoint_ineq_data_wrapper (max $MAX_CORRELATION_FOURPOINT_INEQ_DATA_WRAPPER)"
echo "[route_bloat_guard] Correlation core data wrapper: $correlation_core_data_wrapper (max $MAX_CORRELATION_CORE_DATA_WRAPPER)"
echo "[route_bloat_guard] Interaction integrability data wrapper: $interaction_integrability_data_wrapper (max $MAX_INTERACTION_INTEGRABILITY_DATA_WRAPPER)"
echo "[route_bloat_guard] Correlation GKS data wrapper: $correlation_gks_data_wrapper (max $MAX_CORRELATION_GKS_DATA_WRAPPER)"
echo "[route_bloat_guard] Correlation Lebowitz data wrapper: $correlation_lebowitz_data_wrapper (max $MAX_CORRELATION_LEBOWITZ_DATA_WRAPPER)"
echo "[route_bloat_guard] Correlation four-point models wrapper: $correlation_fourpoint_models_wrapper (max $MAX_CORRELATION_FOURPOINT_MODELS_WRAPPER)"
echo "[route_bloat_guard] Correlation FKG data wrapper: $correlation_fkg_data_wrapper (max $MAX_CORRELATION_FKG_DATA_WRAPPER)"
echo "[route_bloat_guard] Boundary kernel data wrapper: $boundary_kernel_data_wrapper (max $MAX_BOUNDARY_KERNEL_DATA_WRAPPER)"
echo "[route_bloat_guard] Boundary comparison data wrapper: $boundary_comparison_data_wrapper (max $MAX_BOUNDARY_COMPARISON_DATA_WRAPPER)"
echo "[route_bloat_guard] Boundary regularity data wrapper: $boundary_regularity_data_wrapper (max $MAX_BOUNDARY_REGULARITY_DATA_WRAPPER)"
echo "[route_bloat_guard] Boundary covariance data wrapper: $boundary_covariance_data_wrapper (max $MAX_BOUNDARY_COVARIANCE_DATA_WRAPPER)"
echo "[route_bloat_guard] LocalizedBounds weighted estimate wrapper: $localizedbounds_graph_estimate_weighted_wrapper (max $MAX_LOCALIZEDBOUNDS_GRAPH_ESTIMATE_WEIGHTED_WRAPPER)"
echo "[route_bloat_guard] FreeField two-point covariance wrapper: $freefield_covariance_kernel_twopoint_wrapper (max $MAX_FREEFIELD_COVARIANCE_KERNEL_TWOPOINT_WRAPPER)"
echo "[route_bloat_guard] Interaction tendsto-ae geometric-integral wrapper: $interaction_weight_tendsto_ae_geom_integral_wrapper (max $MAX_INTERACTION_WEIGHT_TENDSTO_AE_GEOM_INTEGRAL_WRAPPER)"
echo "[route_bloat_guard] Regularity full-packaging wrapper: $regularity_full_packaging_wrapper (max $MAX_REGULARITY_FULL_PACKAGING_WRAPPER)"
echo "[route_bloat_guard] ReconstructionUpstream wightman model wrapper: $recon_upstream_wightman_model_wrapper (max $MAX_RECON_UPSTREAM_WIGHTMAN_MODEL_WRAPPER)"
echo "[route_bloat_guard] Regularity Wick-cubic data wrapper: $regularity_wickcubic_data_wrapper (max $MAX_REGULARITY_WICKCUBIC_DATA_WRAPPER)"
echo "[route_bloat_guard] Regularity Euclidean-data wrapper: $regularity_euclidean_data_wrapper (max $MAX_REGULARITY_EUCLIDEAN_DATA_WRAPPER)"
echo "[route_bloat_guard] Regularity submodel-nonempty wrapper: $regularity_submodel_nonempty_wrapper (max $MAX_REGULARITY_SUBMODEL_NONEMPTY_WRAPPER)"
echo "[route_bloat_guard] FreeField covariance-kernel data wrapper: $freefield_covariance_kernel_data_wrapper (max $MAX_FREEFIELD_COVARIANCE_KERNEL_DATA_WRAPPER)"
echo "[route_bloat_guard] Reconstruction.Part1Tail wightman-data wrapper: $recon_part1tail_wightman_data_wrapper (max $MAX_RECON_PART1TAIL_WIGHTMAN_DATA_WRAPPER)"
echo "[route_bloat_guard] LocalizedBounds degree-weighted model wrapper: $localizedbounds_degree_weighted_model_wrapper (max $MAX_LOCALIZEDBOUNDS_DEGREE_WEIGHTED_MODEL_WRAPPER)"
echo "[route_bloat_guard] Regularity exhaustion-global GF wrapper: $regularity_gfbound_exhaustion_global_wrapper (max $MAX_REGULARITY_GFBOUND_EXHAUSTION_GLOBAL_WRAPPER)"
echo "[route_bloat_guard] Regularity uniform-global wrapper: $regularity_uniform_global_wrapper (max $MAX_REGULARITY_UNIFORM_GLOBAL_WRAPPER)"
echo "[route_bloat_guard] Regularity nonlocal-global wrapper: $regularity_nonlocal_global_wrapper (max $MAX_REGULARITY_NONLOCAL_GLOBAL_WRAPPER)"
echo "[route_bloat_guard] Regularity GF-bound data wrapper: $regularity_gfbound_data_wrapper (max $MAX_REGULARITY_GFBOUND_DATA_WRAPPER)"
echo "[route_bloat_guard] Regularity uniform data wrapper: $regularity_uniform_data_wrapper (max $MAX_REGULARITY_UNIFORM_DATA_WRAPPER)"
echo "[route_bloat_guard] Regularity nonlocal data wrapper: $regularity_nonlocal_data_wrapper (max $MAX_REGULARITY_NONLOCAL_DATA_WRAPPER)"

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
if (( recon_part1core_linear_interface_wrapper > MAX_RECON_PART1CORE_LINEAR_INTERFACE_WRAPPER )); then
  echo "[FAIL] Reconstruction.Part1Core linear-interface wrapper count exceeded baseline." >&2
  fail=1
fi
if (( recon_part1core_wightman_interface_wrapper > MAX_RECON_PART1CORE_WIGHTMAN_INTERFACE_WRAPPER )); then
  echo "[FAIL] Reconstruction.Part1Core wightman-interface wrapper count exceeded baseline." >&2
  fail=1
fi
if (( regularity_nonlocal_uniform_wrapper > MAX_REGULARITY_NONLOCAL_UNIFORM_WRAPPER )); then
  echo "[FAIL] Regularity nonlocal-uniform wrapper count exceeded baseline." >&2
  fail=1
fi
if (( correlation_lattice_nonempty_wrapper > MAX_CORRELATION_LATTICE_NONEMPTY_WRAPPER )); then
  echo "[FAIL] Correlation lattice nonempty wrapper count exceeded baseline." >&2
  fail=1
fi
if (( correlation_fourpoint_ineq_data_wrapper > MAX_CORRELATION_FOURPOINT_INEQ_DATA_WRAPPER )); then
  echo "[FAIL] Correlation four-point inequality data wrapper count exceeded baseline." >&2
  fail=1
fi
if (( correlation_core_data_wrapper > MAX_CORRELATION_CORE_DATA_WRAPPER )); then
  echo "[FAIL] Correlation core data wrapper count exceeded baseline." >&2
  fail=1
fi
if (( interaction_integrability_data_wrapper > MAX_INTERACTION_INTEGRABILITY_DATA_WRAPPER )); then
  echo "[FAIL] Interaction integrability data wrapper count exceeded baseline." >&2
  fail=1
fi
if (( correlation_gks_data_wrapper > MAX_CORRELATION_GKS_DATA_WRAPPER )); then
  echo "[FAIL] Correlation GKS data wrapper count exceeded baseline." >&2
  fail=1
fi
if (( correlation_lebowitz_data_wrapper > MAX_CORRELATION_LEBOWITZ_DATA_WRAPPER )); then
  echo "[FAIL] Correlation Lebowitz data wrapper count exceeded baseline." >&2
  fail=1
fi
if (( correlation_fourpoint_models_wrapper > MAX_CORRELATION_FOURPOINT_MODELS_WRAPPER )); then
  echo "[FAIL] Correlation four-point models wrapper count exceeded baseline." >&2
  fail=1
fi
if (( correlation_fkg_data_wrapper > MAX_CORRELATION_FKG_DATA_WRAPPER )); then
  echo "[FAIL] Correlation FKG data wrapper count exceeded baseline." >&2
  fail=1
fi
if (( boundary_kernel_data_wrapper > MAX_BOUNDARY_KERNEL_DATA_WRAPPER )); then
  echo "[FAIL] Boundary kernel data wrapper count exceeded baseline." >&2
  fail=1
fi
if (( boundary_comparison_data_wrapper > MAX_BOUNDARY_COMPARISON_DATA_WRAPPER )); then
  echo "[FAIL] Boundary comparison data wrapper count exceeded baseline." >&2
  fail=1
fi
if (( boundary_regularity_data_wrapper > MAX_BOUNDARY_REGULARITY_DATA_WRAPPER )); then
  echo "[FAIL] Boundary regularity data wrapper count exceeded baseline." >&2
  fail=1
fi
if (( boundary_covariance_data_wrapper > MAX_BOUNDARY_COVARIANCE_DATA_WRAPPER )); then
  echo "[FAIL] Boundary covariance data wrapper count exceeded baseline." >&2
  fail=1
fi
if (( localizedbounds_graph_estimate_weighted_wrapper > MAX_LOCALIZEDBOUNDS_GRAPH_ESTIMATE_WEIGHTED_WRAPPER )); then
  echo "[FAIL] LocalizedBounds weighted-estimate wrapper count exceeded baseline." >&2
  fail=1
fi
if (( freefield_covariance_kernel_twopoint_wrapper > MAX_FREEFIELD_COVARIANCE_KERNEL_TWOPOINT_WRAPPER )); then
  echo "[FAIL] FreeField two-point covariance wrapper count exceeded baseline." >&2
  fail=1
fi
if (( interaction_weight_tendsto_ae_geom_integral_wrapper > MAX_INTERACTION_WEIGHT_TENDSTO_AE_GEOM_INTEGRAL_WRAPPER )); then
  echo "[FAIL] Interaction tendsto-ae geometric-integral wrapper count exceeded baseline." >&2
  fail=1
fi
if (( regularity_full_packaging_wrapper > MAX_REGULARITY_FULL_PACKAGING_WRAPPER )); then
  echo "[FAIL] Regularity full-packaging wrapper count exceeded baseline." >&2
  fail=1
fi
if (( recon_upstream_wightman_model_wrapper > MAX_RECON_UPSTREAM_WIGHTMAN_MODEL_WRAPPER )); then
  echo "[FAIL] ReconstructionUpstream wightman model wrapper count exceeded baseline." >&2
  fail=1
fi
if (( regularity_wickcubic_data_wrapper > MAX_REGULARITY_WICKCUBIC_DATA_WRAPPER )); then
  echo "[FAIL] Regularity Wick-cubic data wrapper count exceeded baseline." >&2
  fail=1
fi
if (( regularity_euclidean_data_wrapper > MAX_REGULARITY_EUCLIDEAN_DATA_WRAPPER )); then
  echo "[FAIL] Regularity Euclidean-data wrapper count exceeded baseline." >&2
  fail=1
fi
if (( regularity_submodel_nonempty_wrapper > MAX_REGULARITY_SUBMODEL_NONEMPTY_WRAPPER )); then
  echo "[FAIL] Regularity submodel-nonempty wrapper count exceeded baseline." >&2
  fail=1
fi
if (( freefield_covariance_kernel_data_wrapper > MAX_FREEFIELD_COVARIANCE_KERNEL_DATA_WRAPPER )); then
  echo "[FAIL] FreeField covariance-kernel data wrapper count exceeded baseline." >&2
  fail=1
fi
if (( recon_part1tail_wightman_data_wrapper > MAX_RECON_PART1TAIL_WIGHTMAN_DATA_WRAPPER )); then
  echo "[FAIL] Reconstruction.Part1Tail wightman-data wrapper count exceeded baseline." >&2
  fail=1
fi
if (( localizedbounds_degree_weighted_model_wrapper > MAX_LOCALIZEDBOUNDS_DEGREE_WEIGHTED_MODEL_WRAPPER )); then
  echo "[FAIL] LocalizedBounds degree-weighted model wrapper count exceeded baseline." >&2
  fail=1
fi
if (( regularity_gfbound_exhaustion_global_wrapper > MAX_REGULARITY_GFBOUND_EXHAUSTION_GLOBAL_WRAPPER )); then
  echo "[FAIL] Regularity exhaustion-global GF wrapper count exceeded baseline." >&2
  fail=1
fi
if (( regularity_uniform_global_wrapper > MAX_REGULARITY_UNIFORM_GLOBAL_WRAPPER )); then
  echo "[FAIL] Regularity uniform-global wrapper count exceeded baseline." >&2
  fail=1
fi
if (( regularity_nonlocal_global_wrapper > MAX_REGULARITY_NONLOCAL_GLOBAL_WRAPPER )); then
  echo "[FAIL] Regularity nonlocal-global wrapper count exceeded baseline." >&2
  fail=1
fi
if (( regularity_gfbound_data_wrapper > MAX_REGULARITY_GFBOUND_DATA_WRAPPER )); then
  echo "[FAIL] Regularity GF-bound data wrapper count exceeded baseline." >&2
  fail=1
fi
if (( regularity_uniform_data_wrapper > MAX_REGULARITY_UNIFORM_DATA_WRAPPER )); then
  echo "[FAIL] Regularity uniform data wrapper count exceeded baseline." >&2
  fail=1
fi
if (( regularity_nonlocal_data_wrapper > MAX_REGULARITY_NONLOCAL_DATA_WRAPPER )); then
  echo "[FAIL] Regularity nonlocal data wrapper count exceeded baseline." >&2
  fail=1
fi

if (( fail != 0 )); then
  exit 1
fi

echo "[route_bloat_guard] OK"

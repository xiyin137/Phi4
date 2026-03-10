# Phi4: Formal Construction of the φ⁴₂ Quantum Field Theory

A Lean 4 formalization of constructive 2D φ⁴ Euclidean QFT aimed at the Glimm-Jaffe pipeline:

1. construct the infinite-volume Schwinger functions,
2. prove the Osterwalder-Schrader axioms,
3. reconstruct the corresponding Wightman theory.

## Current Status (March 10, 2026)

- Core theorem-level `sorry` in `Phi4/**/*.lean` excluding `Phi4/Scratch`: `21`
- Legacy `class/structure .*Model` declarations: `13`
- Canonical `gap_*` theorem frontiers: `45`
- `axiom` declarations: `0`
- `def`/`abbrev := by sorry`: `0`

This is not a completed construction.

The correct status framing is:
- there are no hidden axiom-style placeholders,
- the open mathematics is now partly surfaced as explicit theorem-level frontiers,
- a reduced but still real legacy assumption surface remains in `...Model` classes.

In particular, the repository does not yet locally prove that `phi^4_2`
satisfies the Osterwalder-Schrader axioms from first principles. The current
OS file is still an assembly layer:

- [phi4_satisfies_OS](/Users/xiyin/Phi4/Phi4/OSAxioms.lean:78) packages an OS
  object from explicit OS0/OS2/E2/E3/clustering hypotheses,
- [gap_phi4_linear_growth](/Users/xiyin/Phi4/Phi4/Reconstruction/Part1Core.lean:470)
  is an assumption-explicit reconstruction/OS1 bridge,
- [gap_infiniteVolumeLimit_exists](/Users/xiyin/Phi4/Phi4/InfiniteVolumeLimit/Part1.lean:319)
  is an explicit package-construction theorem for infinite-volume data,
  not yet the local proof of that data.

## Roadmap To OS Axioms

1. `WP0`: complete the free/Gaussian combinatorial bridge needed by WP1.
   Main explicit targets:
   - `gap_covariance_eq_kernel` (honest flat-space CLM existence frontier, not an
     equality statement for the harmonic-oscillator `freeCovarianceCLM`)
   - `gap_uvMollifier_covariance_eq_freeCovKernel`
   - `gap_uvMollifier_freeCovKernel_log_growth`
   - `gap_pairing_card`
   - `gap_wicks_theorem_even`
   - `gap_feynman_graph_expansion`
   - `gap_localized_graph_exponential_decay`
2. `WP1`: prove `gap_hasExpInteractionLp`.
   This is the Chapter 8 finite-volume integrability/normalization core.
   The analytic input layer is now split by mathematics:
   - `Interaction/UVInfra.lean`
   - `Interaction/ShellEstimates.lean`
   - `Interaction/NelsonBound.lean`
   - `Interaction/AnalyticInputs.lean` as the thin endpoint orchestrator

   The current shell branch is reduced to one honest leaf theorem:
   - `gap_wickPowerStandardSeqShellUpper_spatial_sq_rate`
   and derived closures:
   - `gap_wickPower_standardSeq_spatial_sq_rate`
   - `gap_interactionCutoff_standardSeq_L2_increment_rate`
   - `gap_interactionCutoff_standardSeq_summable_L1_increments`
   - `gap_interactionCutoff_standardSeq_ae_convergence`

   The current Nelson branch is reduced to three honest leaf theorems:
   - `gap_regularizedPointCovariance_log_growth`
   - `gap_finiteWickCylinder_even_moment_comparison`
   - `gap_interactionCutoff_reference_shell_L2_bound`
   together with the canonical approximation bridge:
   - `gap_interactionCutoffSubUniformApprox_tendsto_ae` `[closed]`
   - `gap_interactionCutoffSubUniformApprox_L2` `[closed]`
   - `gap_interactionCutoffSubUniformApprox_even_moment_comparison` `[closed modulo finite-cylinder leaf]`
   and downstream derived closures:
   - `gap_interactionCutoff_sub_even_moment_comparison`
   - `gap_interactionCutoff_reference_shell_even_moment_bound`
   - `gap_interaction_double_exponential_tail_bound`
   - `gap_exp_neg_interaction_uniform_bound`

   Non-critical supporting frontiers retained off the main path:
   - `gap_interactionCutoff_L2_convergence`
   - `gap_interactionCutoff_ae_convergence`

   Recently closed support endpoints:
   - `gap_interaction_aestronglyMeasurable`
   - `gap_interaction_sq_integrable`

   Recent infrastructure that made the shell split possible:
   - normalized `uvMollifier` with unit mass and exact support in `FreeField.lean`
   - `wickPower_four_step_decomposition`
   - `rawFieldEval_sub_sq_expectation`
   - `rawFieldEval_sub_fourth_expectation`
3. `WP2`: close finite-volume monotonicity, comparison, chessboard, and reflection-positivity frontiers.
   Main explicit targets:
   - `gap_hasSchwingerNMonotone`
   - `gap_hasChessboardEstimate`
   - `gap_hasSchwingerUniformBound`
   - `gap_schwingerTwo_le_free`
   - `gap_free_covariance_reflection_positive`
   - `gap_dirichlet_covariance_reflection_positive`
   - `gap_interacting_measure_reflection_positive`
4. `WP3`: construct the infinite-volume Schwinger limit and its representing measure.
   Current explicit endpoint:
   - `gap_infiniteVolumeLimit_exists`
5. `WP4`: close regularity and equation-of-motion frontiers.
   Main explicit targets:
   - `gap_wick_powers_infinite_volume`
   - `gap_wickCubicSmeared_tendsto_ae`
   - `gap_euclidean_equation_of_motion`
   - `gap_generating_functional_bound`
6. `WP5`: close OS packaging and reconstruction.
   Main explicit targets:
   - `gap_measure_os3_reflection_positive`
   - `gap_phi4_linear_growth`
   Remaining unsurfaced explicit obligations:
   - OS0 continuity of the packaged Schwinger functions
   - OS2 translation/rotation covariance of the packaged Schwinger functions
   - distributional E2 reflection positivity
   - E3 permutation symmetry

## Practical Bottom Line

The construction is closest to completion on the packaging side and still far
from completion on the analytic side.

The most important remaining local leaf blockers are:

1. free-field / covariance bridge:
   - `gap_covariance_eq_kernel`
   - `gap_uvMollifier_covariance_eq_freeCovKernel`
   - `gap_uvMollifier_freeCovKernel_log_growth`
2. WP1 shell branch:
   - `gap_wickPowerStandardSeqShellUpper_spatial_sq_rate`
3. WP1 Nelson branch:
   - `gap_finiteWickCylinder_even_moment_comparison`
   - `gap_interactionCutoff_reference_shell_L2_bound`
4. regularity / OS1:
   - `gap_wick_powers_infinite_volume`
   - `gap_wickCubicSmeared_tendsto_ae`
   - `gap_euclidean_equation_of_motion`
5. OS3:
   - `gap_measure_os3_reflection_positive`

Once those are resolved, the existing OS/reconstruction assembly layer is much
closer to being feedable by local data.

## Main Architectural Constraint

`main` still contains a reduced but still significant legacy interface layer. The active direction is:

1. add explicit theorem-level frontier statements,
2. migrate callers away from legacy model classes,
3. delete superseded wrappers and interface-only proof debt.

Recent progress on that front:

1. dead OS/reconstruction bundle classes were removed,
2. the unused `Phi4ModelBundle` compatibility layer was deleted,
3. the top-level Wightman endpoint now takes the reconstruction rule explicitly instead of routing through temporary model instances,
4. the multiple-reflection bundle was removed from the infinite-volume convergence layer in favor of explicit monotonicity and uniform-bound assumptions.

The `simplified` branch was not merged wholesale because it mixed useful theorem-surface cleanup with deletion of substantive proved mathematics.

Recent structural progress:

1. the monolithic `Interaction/AnalyticInputs.lean` was split along actual proof-program boundaries into shared UV infrastructure, shell estimates, and Nelson bounds,
2. the shell and Nelson branches now expose their genuine leaf frontiers explicitly instead of hiding them inside one oversized file,
3. the flat-space covariance frontier in `FreeField.lean` now states existence of a flat CLM witness, rather than the false equality of the harmonic-oscillator CLM with the flat kernel.

# Phi4: Formal Construction of the φ⁴₂ Quantum Field Theory

A Lean 4 formalization of constructive 2D φ⁴ Euclidean QFT aimed at the Glimm-Jaffe pipeline:

1. construct the infinite-volume Schwinger functions,
2. prove the Osterwalder-Schrader axioms,
3. reconstruct the corresponding Wightman theory.

## Current Status (March 6, 2026)

- Core theorem-level `sorry` in `Phi4/**/*.lean` excluding `Phi4/Scratch`: `20`
- Legacy `class/structure .*Model` declarations: `13`
- Canonical `gap_*` theorem frontiers: `27`
- `axiom` declarations: `0`
- `def`/`abbrev := by sorry`: `0`

This is not a completed construction.

The correct status framing is:
- there are no hidden axiom-style placeholders,
- the open mathematics is now partly surfaced as explicit theorem-level frontiers,
- a reduced but still real legacy assumption surface remains in `...Model` classes.

## Roadmap To OS Axioms

1. `WP0`: complete the free/Gaussian combinatorial bridge needed by WP1.
   Main explicit targets:
   - `gap_covariance_eq_kernel`
   - `gap_pairing_card`
   - `gap_wicks_theorem_even`
   - `gap_feynman_graph_expansion`
   - `gap_localized_graph_exponential_decay`
2. `WP1`: prove `gap_hasExpInteractionLp`.
   This is the Chapter 8 finite-volume integrability/normalization core.
   The WP1 endpoint (`hasExpInteractionLp_of_analytic_inputs`) now uses a
   Fatou route with only two critical-path inputs:
   - `gap_interactionCutoff_standardSeq_ae_convergence` (sequence-level a.e. UV convergence)
   - `gap_exp_neg_interaction_uniform_bound` (Nelson's uniform bound on E[exp(-pV_κ)])
   Non-critical supporting frontiers:
   - `gap_interactionCutoff_L2_convergence`
   - `gap_interactionCutoff_ae_convergence` (continuous-parameter, stronger than needed)
   - `gap_interaction_sq_integrable`
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

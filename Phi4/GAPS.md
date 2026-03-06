# Phi4 Proof-Gap Ledger

Date: 2026-03-06

This file records the current proof boundary on `main`.

## Trust Snapshot

- theorem-level `sorry` in core modules: `20`
- legacy `class/structure .*Model`: `13`
- canonical `gap_*` theorem frontiers: `27`
- `axiom`: `0`
- `def/abbrev := by sorry`: `0`

So the project has no hidden axiom-style placeholders, but it is still far from
assumption-free completion. The open mathematics is currently split between:

1. explicit theorem-level frontier statements, and
2. a reduced but still substantial legacy `...Model` assumption surface.

## Explicit Theorem-Level Frontiers

1. `gap_pairing_card`
2. `gap_wicks_theorem_even`
3. `gap_feynman_graph_expansion`
4. `gap_localized_graph_exponential_decay`
5. `gap_covariance_eq_kernel`
6. `gap_interactionCutoff_standardSeq_ae_convergence`
7. `gap_interactionCutoff_L2_convergence`
8. `gap_interactionCutoff_ae_convergence`
9. `gap_interaction_sq_integrable`
10. `gap_exp_neg_interaction_uniform_bound`
11. `gap_hasExpInteractionLp`
12. `gap_schwingerTwo_le_free`
13. `gap_hasSchwingerNMonotone`
14. `gap_hasChessboardEstimate`
15. `gap_hasSchwingerUniformBound`
16. `gap_free_covariance_reflection_positive`
17. `gap_dirichlet_covariance_reflection_positive`
18. `gap_interacting_measure_reflection_positive`
19. `gap_infiniteVolumeLimit_exists`
20. `gap_wick_powers_infinite_volume`
21. `gap_wickCubicSmeared_tendsto_ae`
22. `gap_euclidean_equation_of_motion`
23. `gap_generating_functional_bound`
24. `gap_generating_functional_bound_uniform`
25. `gap_nonlocal_phi4_bound`
26. `gap_measure_os3_reflection_positive`
27. `gap_phi4_linear_growth`

## Explicit But Not Yet Named OS Obligations

The OS-side chain is not fully captured by `gap_*` names yet. The following
explicit obligations still appear as direct hypotheses in the local assembly
theorems:

- OS0 continuity of `phi4SchwingerFunctions`
- OS2 translation covariance
- OS2 rotation covariance
- distributional E2 reflection positivity
- E3 permutation symmetry

## Remaining Legacy Interface Debt

The dominant unsurfaced proof debt still sits in model classes, including:

- interaction interfaces,
- covariance/kernel interfaces,
- correlation inequality interfaces,
- infinite-volume measure/moment interfaces,
- regularity interfaces.

This means theorem-level frontiers are now more visible than before, but they do
not yet cover the full mathematical debt of the repository.

## Main Risk

WP1 remains the primary blocker:
- proving the finite-volume Boltzmann-weight integrability and normalization
  needed for the interacting measure, together with the newly surfaced
  analytic-input obligations in `Interaction/AnalyticInputs.lean`.

Everything downstream depends on that analytic core.

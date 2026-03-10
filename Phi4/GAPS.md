# Phi4 Proof-Gap Ledger

Date: 2026-03-10

This file records the current proof boundary on `main`.

## Trust Snapshot

- theorem-level `sorry` in core modules: `21`
- legacy `class/structure .*Model`: `13`
- canonical `gap_*` theorem frontiers: `45`
- `axiom`: `0`
- `def/abbrev := by sorry`: `0`

So the project has no hidden axiom-style placeholders, but it is still far from
assumption-free completion. The open mathematics is currently split between:

1. explicit theorem-level frontier statements, and
2. a reduced but still substantial legacy `...Model` assumption surface.

## Canonical `gap_*` Theorem Surface

Not every `gap_*` theorem below is still open. Some are now closed support
theorems that remain as canonical named endpoints. The active proof boundary is
tracked by the theorem-level `sorry` count above.

### WP0: Free/Gaussian combinatorial bridge
1. `gap_pairing_card`
2. `gap_wicks_theorem_even`
3. `gap_feynman_graph_expansion`
4. `gap_localized_graph_exponential_decay`
5. `gap_covariance_eq_kernel` — existence of a flat-space CLM realizing `freeCovKernel`
6. `gap_uvMollifier_covariance_eq_freeCovKernel`
7. `gap_uvMollifier_freeCovKernel_log_growth`

### WP1: Finite-volume integrability (CRITICAL PATH)
8. `gap_uvMollifier_continuous` — UV mollifier continuity `[closed]`
9. `gap_interactionCutoff_sq_integrable` — L² integrability of cutoff interaction `[closed]`
10. `gap_wickPowerStandardSeqShellUpper_spatial_sq_rate` — shell-side spatial square rate for the reduced upper envelope
11. `gap_wickPower_standardSeq_spatial_sq_rate` — quartic shell rate `[closed modulo 10]`
12. `gap_interactionCutoff_standardSeq_L2_increment_rate` — discrete cutoff L² increment rate `[closed modulo 10]`
13. `gap_interactionCutoff_standardSeq_summable_L1_increments` — summable L¹ increments `[closed modulo 12]`
14. `gap_interactionCutoff_standardSeq_ae_convergence` — sequence-level a.e. convergence `[closed modulo 13]`
15. `gap_interactionCutoff_L2_convergence` — continuous-parameter L² convergence
16. `gap_interactionCutoff_ae_convergence` — continuous-parameter a.e. convergence
17. `gap_interaction_aestronglyMeasurable` — measurability of limiting interaction `[closed]`
18. `gap_interaction_sq_integrable` — square-integrability of the limiting interaction `[closed]`
19. `gap_regularizedPointCovariance_log_growth` — additive-constant logarithmic covariance growth for normalized UV cutoff
20. `gap_interactionCutoffSubUniformApprox_tendsto_ae` — a.e. convergence of canonical Nelson uniform approximants `[closed]`
21. `gap_interactionCutoffSubUniformApprox_L2` — L² convergence of canonical Nelson uniform approximants `[closed]`
22. `gap_finiteWickCylinder_even_moment_comparison` — hypercontractive comparison for finite `0/2/4` Wick cylinders
23. `gap_interactionCutoffSubUniformApprox_even_moment_comparison` — canonical approximant even-moment comparison `[closed modulo 22]`
24. `gap_interactionCutoff_sub_even_moment_comparison` — direct even-moment comparison for the integrated cutoff difference `[closed modulo 23]`
25. `gap_interactionCutoff_reference_shell_L2_bound` — canonical reference-shell L² decay
26. `gap_interactionCutoff_reference_shell_even_moment_bound` — Nelson reference-shell even-moment bound `[closed modulo 24,25]`
27. `gap_interaction_double_exponential_tail_bound` — Nelson double-exponential tail `[closed modulo 19,24,25]`
28. `gap_exp_neg_interaction_uniform_bound` — uniform negative exponential moment bound `[closed modulo 27]`
29. `gap_hasExpInteractionLp` — WP1 endpoint

### WP2: Finite-volume monotonicity, comparison, reflection positivity
30. `gap_schwingerTwo_le_free`
31. `gap_hasSchwingerNMonotone`
32. `gap_hasChessboardEstimate`
33. `gap_hasSchwingerUniformBound`
34. `gap_free_covariance_reflection_positive`
35. `gap_dirichlet_covariance_reflection_positive`
36. `gap_interacting_measure_reflection_positive`

### WP3: Infinite-volume limit
37. `gap_infiniteVolumeLimit_exists`

### WP4: Regularity and equation of motion
38. `gap_wick_powers_infinite_volume`
39. `gap_wickCubicSmeared_tendsto_ae`
40. `gap_euclidean_equation_of_motion`
41. `gap_generating_functional_bound`
42. `gap_generating_functional_bound_uniform`
43. `gap_nonlocal_phi4_bound`

### WP5: OS packaging and reconstruction
44. `gap_measure_os3_reflection_positive`
45. `gap_phi4_linear_growth`

## WP1 Critical Path

The WP1 endpoint `hasExpInteractionLp_of_analytic_inputs` now sits on two
separated branches:

```
gap_wickPowerStandardSeqShellUpper_spatial_sq_rate
  → gap_wickPower_standardSeq_spatial_sq_rate
    → gap_interactionCutoff_standardSeq_L2_increment_rate
      → gap_interactionCutoff_standardSeq_summable_L1_increments
        → gap_interactionCutoff_standardSeq_ae_convergence

gap_finiteWickCylinder_even_moment_comparison
  → gap_interactionCutoffSubUniformApprox_even_moment_comparison
    + gap_interactionCutoffSubUniformApprox_tendsto_ae
    + gap_interactionCutoffSubUniformApprox_L2
      → gap_interactionCutoff_sub_even_moment_comparison

gap_regularizedPointCovariance_log_growth
  + gap_interactionCutoff_sub_even_moment_comparison
  + gap_interactionCutoff_reference_shell_L2_bound
    → gap_interactionCutoff_reference_shell_even_moment_bound
      → gap_interaction_double_exponential_tail_bound
        → gap_exp_neg_interaction_uniform_bound

Both → hasExpInteractionLp_of_analytic_inputs  (PROVED modulo above)
```

The shell/Nelson split is now reflected in the source tree itself:
- `Interaction/UVInfra.lean`
- `Interaction/ShellEstimates.lean`
- `Interaction/NelsonBound.lean`
- `Interaction/AnalyticInputs.lean` as the thin endpoint file

## Explicit But Not Yet Named OS Obligations

The OS-side chain is not fully captured by `gap_*` names yet. The following
explicit obligations still appear as direct hypotheses in the local assembly
theorems:

- OS0 continuity of `phi4SchwingerFunctions`
- OS2 translation covariance
- OS2 rotation covariance
- distributional E2 reflection positivity
- E3 permutation symmetry

`phi4_satisfies_OS` in [OSAxioms.lean](/Users/xiyin/Phi4/Phi4/OSAxioms.lean:78)
is still an assembly theorem from those inputs. The repository does not yet
derive the full OS package locally from the φ⁴ construction.

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
  shell and Nelson leaf theorems in `Interaction/ShellEstimates.lean` and
  `Interaction/NelsonBound.lean`.

Everything downstream depends on that analytic core.

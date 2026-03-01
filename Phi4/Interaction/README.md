# Interaction Module Guide

This folder contains the split implementation of the interaction stage
(`Phi4/Interaction.lean` now imports `Part3`, which imports earlier parts).

Goal: formalize constructive control of the `phi^4_2` interaction term
`V_Λ` and prove `exp(-V_Λ) ∈ L^p` routes used by finite-volume normalization
and reconstruction bridges.

## File map

- `Part1.lean`
  - Thin compatibility import shim for the `Part1*` split.
- `Part1Core.lean`
  - Core definitions:
    `interactionCutoff`, `standardUVCutoffSeq`, `interaction`.
  - Wick quartic semiboundedness and cutoff lower-bound infrastructure.
  - Interface classes and base constructors:
    `InteractionUVModel`, `InteractionWeightModel`,
    `InteractionIntegrabilityModel`.
  - Early `L^p` routes from a.e. lower bounds and summable bad-event control.
- `Part1Tail.lean`
  - Continuation of Part 1 infrastructure:
    shifted bad-event/moment deviation controls, Chernoff bridges, and
    polynomial-to-geometric constructor chains.
- `Part2.lean`
  - Extended cutoff-sequence lower-bound and bad-event-tail pipelines
    (summable/geometric/exponential variants).
  - Weight-model constructor families from explicit cutoff hypotheses.
  - Shifted-index moment/bad-set bridges that prepare high-level endpoints.
- `Part3.lean`
  - Geometric/exponential-moment-powered constructors for
    `InteractionWeightModel` and `InteractionIntegrabilityModel`.
  - Public endpoint theorems:
    `exp_interaction_Lp`, `partition_function_pos`,
    `partition_function_integrable`, and explicit constructive variants from
    shifted-moment and Wick-sublevel bad-event hypotheses.

## Dependency flow

1. `Part1`: definitions + semiboundedness + base interface constructors.
2. `Part2`: reusable cutoff-tail/moment infrastructure.
3. `Part3`: final model instantiation and partition-function endpoints.

## Policy note

- Splitting is structural only; theorem content is unchanged.
- Reusable simplification/bridge lemmas are encouraged.
- Wrapper-for-wrapper layering and hidden-assumption smuggling are disallowed.

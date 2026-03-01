# Reconstruction Module Guide

This folder contains the split implementation of the reconstruction stage
(`Phi4/Reconstruction.lean` now imports `Part3`, which imports the earlier parts).

Goal: formalize the Glimm-Jaffe/OS route from Euclidean Schwinger data to
Wightman QFT data for `phi^4_2`.

## File map

- `Part1.lean`
  - Linear-growth and product-tensor infrastructure.
  - Interfaces and bridge lemmas used to feed reconstruction inputs.
  - Key declarations include
    `gap_phi4_linear_growth_of_zero_mode_normalization`,
    `gap_phi4_linear_growth`,
    and `phi4_wightman_reconstruction_step`.
- `Part2.lean`
  - OS4 weak-coupling clustering and connected/cumulant bounds.
  - Infinite-volume 2-point bilinear/positivity inequalities reused downstream.
- `Part3.lean`
  - Final reconstruction theorems from OS + linear growth.
  - Main endpoint declarations:
    `phi4_wightman_exists`,
    `phi4_selfadjoint_fields`,
    `phi4_locality`,
    `phi4_lorentz_covariance`,
    `phi4_unique_vacuum`.

## Dependency flow

1. `Part1` builds explicit linear-growth/reconstruction inputs.
2. `Part2` supplies OS4 decay and positivity/cumulant controls.
3. `Part3` consumes those inputs to produce Wightman existence and axiom-level outputs.

## Frontier status

- This split is structural; it does not by itself close theorem-level frontier gaps.
- Remaining blockers should be discharged by constructive proofs of the
  documented `gap_*` results and explicit hypotheses, not by wrapper layering.

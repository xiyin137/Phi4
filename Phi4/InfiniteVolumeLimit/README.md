# Infinite Volume Limit Module Guide

This folder contains the split implementation of the infinite-volume limit stage
(`Phi4/InfiniteVolumeLimit.lean` now imports `Part3`, which imports earlier parts).

Goal: formalize the Glimm-Jaffe Chapter 11 pipeline
finite volume -> monotone/bounded Schwinger family -> infinite-volume objects.

## File map

- `Part1.lean`
  - Exhaustion setup (`exhaustingRectangles`).
  - Monotonicity and uniform-bound infrastructure.
  - Existence of infinite-volume Schwinger limits (`infinite_volume_schwinger_exists*`).
  - Core models and interfaces:
    `InfiniteVolumeSchwingerModel`, `SchwingerUniformBoundModel`,
    `SchwingerLimitModel`, `InfiniteVolumeMeasureModel`, `InfiniteVolumeMomentModel`.
- `Part2.lean`
  - Infinite-volume 4-point cumulant definitions and channel bounds.
  - Truncated 4-point positivity and upper bounds in all pairing channels.
- `Part3.lean`
  - Convergence of connected 2-point functions.
  - Bilinear/positivity and Cauchy-Schwarz style estimates.
  - Infinite-volume measure representation and `S_0 = 1` normalization theorem.

## Dependency flow

1. `Part1`: build the limit object (`infiniteVolumeSchwinger`) and 2-point symmetry.
2. `Part2`: add 4-point cumulant/truncated estimates on that limit object.
3. `Part3`: derive connected 2-point structure and measure-level realization.

## Frontier status

- Mathematical closure still depends on proving upstream interaction estimates
  (integrability/graph-bound inputs) that instantiate the explicit assumptions.
- The split is documentation/maintainability infrastructure, not a workaround.

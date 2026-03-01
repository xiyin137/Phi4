# GreenFunction Module Guide

This folder contains concrete kernel infrastructure for periodic image-sum
constructions.

## Files

- `PeriodicKernel.lean`
  - Defines lattice shifts (`periodicShift`, `shiftPoint`) and finite index
    windows (`periodicIndexFinset`).
  - Defines truncated periodic image kernels (`periodicKernelTrunc`).
  - Proves symmetry/shift-invariance/reindexing lemmas used to control periodic
    finite-volume covariance constructions.

## Role in the project

- Provides technical bridge machinery between free-space covariance formulas and
  periodic finite-volume kernels used in approximation arguments.
- Keeps translation/index manipulations isolated so downstream modules can reuse
  stable kernel identities.

## Frontier note

- Periodic-kernel identities are support infrastructure; they should stay
  definition-faithful and directly proof-relevant to covariance bounds.

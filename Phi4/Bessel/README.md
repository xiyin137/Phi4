# Bessel Module Guide

This folder contains analytic infrastructure for modified Bessel functions used
in free-kernel estimates for the 2D massive scalar field.

## Files

- `BesselK1.lean`
  - Defines `besselK1` via the cosh-integral representation.
  - Proves positivity and asymptotic/proper-time bridge lemmas used to bound
    covariance kernels.
- `BesselK0.lean`
  - Defines `besselK0` via the cosh-integral representation.
  - Proves positivity/integrability and Schwinger integral identities linking
    free 2D kernels to `K₀`.

## Role in the project

- Provides concrete analytic bounds for `Phi4/FreeField.lean`.
- Supports off-diagonal decay/control lemmas that feed covariance and
  interaction estimates.

## Frontier note

- This folder is mostly foundational analysis and should remain close to
  standard definitions; do not replace canonical Bessel definitions with
  simplified surrogates.

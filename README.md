# Phi4: Formal Construction of the φ⁴₂ Quantum Field Theory

A Lean 4 formalization of the constructive φ⁴ quantum field theory in two Euclidean spacetime dimensions, following the continuum approach of Glimm and Jaffe.

## Status Snapshot (2026-02-25)

The project is in active development.

- Current `sorry` count: `32` across `9` files.
- Foundational free-field and Wick infrastructure is largely in place.
- Covariance/correlation layers are available through explicit model interfaces
  (`BoundaryCovarianceModel`, `CorrelationInequalityModel`).
- Remaining blockers are concentrated in deep analytic estimates and final OS packaging:
  `FeynmanGraphs`, `Interaction`, `MultipleReflections`, `InfiniteVolumeLimit`,
  `Regularity`, `ReflectionPositivity`, `OSAxioms`, and `Reconstruction`.

## Overview

This project aims to give a complete, rigorous Lean 4 proof that the φ⁴₂ model satisfies the Osterwalder-Schrader axioms (Euclidean QFT axioms) and, via the OS reconstruction theorem, yields a Wightman quantum field theory. The construction follows Part II of:

> J. Glimm and A. Jaffe, *Quantum Physics: A Functional Integral Point of View*, 2nd edition, Springer 1987.

The mathematical content includes:
- Construction of the free Euclidean field as a Gaussian measure on S'(R²)
- Wick products and the interaction V = λ∫ :φ⁴: dx
- Nelson's estimate: e^{-V} ∈ L^p for all p < ∞ (d=2)
- Correlation inequalities (GKS, FKG, Lebowitz)
- Reflection positivity and multiple reflections (chessboard estimates)
- Monotone infinite volume limit via operator inequalities
- Regularity (OS1 axiom) via integration by parts
- Cluster expansion for the mass gap (OS4 axiom)
- Osterwalder-Schrader reconstruction to Wightman QFT

## Architecture

The formalization uses a **continuum approach** with UV regularization:

```
Free Gaussian measure dφ_C on S'(R²)
         ↓
Wick-ordered interaction V_Λ = λ ∫_Λ :φ⁴:_C dx
         ↓
Finite volume measure dν_Λ = Z_Λ⁻¹ e^{-V_Λ} dφ_C
         ↓
Correlation inequalities → Monotone convergence
         ↓
Infinite volume limit ν = lim ν_Λ
         ↓
OS axioms verification (OS0-OS4)
         ↓
Wightman QFT via OS reconstruction
```

### File structure

| File | Content |
|------|---------|
| `Defs.lean` | Core types: Spacetime2D, TestFun2D, FieldConfig2D, Rectangle, UVCutoff |
| `FreeField.lean` | Free Gaussian measure via spectral CLM construction |
| `CovarianceOperators.lean` | Dirichlet/Neumann/periodic covariances, operator inequalities |
| `WickProduct.lean` | Wick products :φⁿ: via recursive Hermite polynomials |
| `FeynmanGraphs.lean` | Localized graph bounds for interaction estimates |
| `Interaction.lean` | Interaction V_Λ, finite volume measures, Nelson's e^{-V} ∈ L^p |
| `CorrelationInequalities.lean` | GKS-I/II, FKG, Lebowitz inequalities |
| `ReflectionPositivity.lean` | Reflection positivity for free and interacting measures |
| `MultipleReflections.lean` | Chessboard/iterated Schwarz estimates |
| `InfiniteVolumeLimit.lean` | Monotone convergence to infinite volume |
| `Regularity.lean` | OS1 axiom via integration by parts |
| `OSAxioms.lean` | Verification of OS0-OS4 |
| `Reconstruction.lean` | Wightman QFT from OS axioms |

## Dependencies

- [Mathlib](https://github.com/leanprover-community/mathlib4) — Lean 4 mathematics library
- [GaussianField](https://github.com/mrdouglasny/gaussian-field) — Gaussian probability measures on nuclear Fréchet spaces (provides `DyninMityaginSpace`, `spectralCLM`, Gaussian measure construction, Wick's theorem, Fernique bounds)
- [OSReconstruction](https://github.com/mrdouglasny/OSreconstruction) — Osterwalder-Schrader axiom structures and the reconstruction theorem to Wightman QFT

## Current status

**Work in progress.** The architecture is in place and major foundational pieces are proven. Key items proven so far:

- Free field eigenvalues, singular values, and their bounds
- Free covariance CLM via `spectralCLM` (the critical Phase 1A construction)
- Free Gaussian measure and its properties (probability measure, centered, two-point function, L^p integrability) — via GaussianField API
- Wick monomials via recursive definition with explicit formulas for n = 0,...,4
- Integration by parts for the free field
- Rectangle geometry (area positivity, time reflection, symmetric rectangles)

Remaining: 32 `sorry`s across 9 files, concentrated in interaction estimates,
multiple-reflection/infinite-volume infrastructure, regularity bounds, and final
OS/reconstruction packaging.
See [TODO.md](TODO.md) for the active queue and [ProofIdeas/Overview.md](ProofIdeas/Overview.md)
for chapter-aligned progress notes.

## Building

Requires Lean 4 v4.28.0. To build:

```bash
lake build Phi4
```

## Proof ideas

The `ProofIdeas/` directory contains detailed mathematical notes for each chapter of Glimm-Jaffe, documenting the proof strategies that guide the formalization.

## Documentation Notes

- `TODO.md`: active implementation queue.
- `ProofIdeas/`: active mathematical planning and chapter notes.
- `docs/archive/REVIEW-2026-02-23.md`: historical audit snapshot, not the current status source.

## References

- J. Glimm and A. Jaffe, *Quantum Physics: A Functional Integral Point of View*, 2nd ed., Springer 1987
- B. Simon, *The P(φ)₂ Euclidean (Quantum) Field Theory*, Princeton 1974
- V. Rivasseau, *From Perturbative to Constructive Renormalization*, Princeton 1991

## Related work

- [pphi2](https://github.com/mrdouglasny/pphi2) by M. Douglas — A complementary approach to the same theorem using lattice discretization and transfer matrix methods

## License

Apache 2.0

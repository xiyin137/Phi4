# Proof Ideas Overview: phi^4_2 QFT Formalization

## Reference
Glimm & Jaffe, *Quantum Physics: A Functional Integral Point of View* (2nd ed.)

## Canonical Goal (Authoritative)

This document tracks one target only: formalizing the Glimm-Jaffe construction
of `φ⁴₂` through OS axioms and then to Wightman reconstruction. All chapter
plans below are supporting steps of that single pipeline.

## Proof Architecture

The construction of the phi^4_2 quantum field theory proceeds through these stages:

1. **Free Field** (GJ Ch 6-7): Gaussian measure dφ_C on S'(R^2) with covariance C = (-Δ+m^2)^{-1}
2. **Wick Products & Feynman Graphs** (GJ Ch 8): :φ^4: well-defined in L^p, e^{-V} in L^p
3. **Finite Volume Measure** (GJ Ch 8-9): dμ_Λ = Z^{-1} e^{-V_Λ} dφ_C
4. **Correlation Inequalities** (GJ Ch 4, 10): GKS-I/II, FKG, Lebowitz; monotonicity
5. **Reflection Positivity** (GJ Ch 7.10, 10.4): OS3 for free and interacting measures
6. **Multiple Reflections** (GJ Ch 10.5): Chessboard/iterated Schwarz estimates
7. **Infinite Volume** (GJ Ch 11): Λ → R^2 via monotone convergence + uniform bounds
8. **Regularity** (GJ Ch 12): OS1 via integration by parts + nonlocal bounds
9. **OS Axioms** (GJ Ch 12.1): OS0-OS3 verified for infinite volume measure
10. **Cluster Expansion** (GJ Ch 18): OS4 (ergodicity/clustering) for weak coupling
11. **Reconstruction** (GJ Ch 19): OS → Wightman via analytic continuation

## Status Snapshot (2026-02-27)

- Core `Phi4/**/*.lean` has no theorem-level `sorry`, no explicit `axiom`, and
  no `def/abbrev := by sorry` placeholders.
- The main frontier is now explicit interface debt (`...Model` assumptions), not
  hidden placeholders.
- Current architecture intentionally isolates assumptions into focused
  subinterfaces (interaction, infinite-volume, regularity, OS, reconstruction)
  so each major analytic obligation can be grounded independently.
- Upstream `OSReconstruction` still contains its own `sorry` declarations; the
  trusted Phi4 path stays backend-abstract via `WightmanReconstructionModel`.

## Current Development Constraints (project policy)

1. No `axiom` declarations.
2. No fake/placeholder definitions to force theorem closure.
3. For major proofs: prototype in `Phi4/Scratch/` first, compile, then port to working files.
4. Prioritize mathematically sound statements aligned with the OS/Wightman end goal.

## Critical Path (highest-priority interface debt)

These assumptions are the deepest remaining obligations:

1. **Interaction integrability grounding** (`InteractionUVModel`, `InteractionWeightModel`) for Chapter 8 finite-volume control.
2. **Reflection positivity + chessboard grounding** (`Free/Dirichlet/InteractingReflectionPositivityModel`, `MultipleReflectionModel`).
3. **Infinite-volume assembly grounding** (`SchwingerUniformBoundModel`, `SchwingerLimitModel`, `InfiniteVolumeMeasureModel`, `InfiniteVolumeMomentModel`).
4. **Regularity grounding** (`WickCubicConvergenceModel`, `EuclideanEquationModel`, `GeneratingFunctionalBoundModel`, `NonlocalPhi4BoundModel`, `UniformGeneratingFunctionalBoundModel`).
5. **OS packaging grounding** (`OSTemperedModel`, `OSEuclideanCovarianceModel`, `OSE3SymmetryModel`, `OSDistributionE2Model`, `OSE4ClusterModel`).
6. **Reconstruction backend grounding** (`ReconstructionLinearGrowthModel`, `WightmanReconstructionModel`), with upstream dependency audits for trusted closure.

## Detailed Notes

See individual chapter files:
- [Ch6_FieldTheory_Axioms.md](Ch6_FieldTheory_Axioms.md)
- [Ch7_CovarianceOperators.md](Ch7_CovarianceOperators.md)
- [Ch8_Quantization.md](Ch8_Quantization.md)
- [Ch10_11_Estimates_InfiniteVolume.md](Ch10_11_Estimates_InfiniteVolume.md)
- [Ch12_Regularity.md](Ch12_Regularity.md)
- [Ch18_19_ClusterExpansion_Reconstruction.md](Ch18_19_ClusterExpansion_Reconstruction.md)

Cross-cutting topics:
- [FeynmanGraphsNonPerturbative.md](FeynmanGraphsNonPerturbative.md) -- How Feynman graphs are used non-perturbatively (exact Gaussian decompositions, convergent cluster expansion, IBP organization)

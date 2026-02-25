# Proof Ideas Overview: phi^4_2 QFT Formalization

## Reference
Glimm & Jaffe, *Quantum Physics: A Functional Integral Point of View* (2nd ed.)

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

## Sorry Count by File (current snapshot: 2026-02-25)

| File | Sorries | Primary GJ Chapters |
|------|---------|---------------------|
| FeynmanGraphs.lean | 4 | 8.2-8.5 |
| FiniteVolumeMeasure.lean | 1 | 8.6, 10.2, 11.2 |
| InfiniteVolumeLimit.lean | 5 | 11.2 |
| Interaction.lean | 4 | 8.5, 8.6 |
| MultipleReflections.lean | 2 | 10.5, 10.6 |
| OSAxioms.lean | 6 | 10.4, 12.1 |
| Reconstruction.lean | 2 | 12.5, 18, 19 |
| ReflectionPositivity.lean | 3 | 7.10, 10.4 |
| Regularity.lean | 5 | 12.1-12.5 |
| **Total** | **32** | |

## Current Development Constraints (project policy)

1. No `axiom` declarations.
2. No fake/placeholder definitions to force theorem closure.
3. For major proofs: prototype in `Phi4/Scratch/` first, compile, then port to working files.
4. Prioritize mathematically sound statements aligned with the OS/Wightman end goal.

## Critical Path (highest-priority sorries)

These sorries block the most downstream results right now:

1. **`exp_interaction_Lp`** (Interaction.lean) -- GJ 8.6.2: central L^p estimate, feeds finite-volume construction.
2. **`chessboard_estimate`** (MultipleReflections.lean) -- GJ 10.5.5: key uniform-bound engine.
3. **`schwinger_uniform_bound` / `schwinger_uniformly_bounded`** (MultipleReflections + InfiniteVolumeLimit) -- bridge to infinite-volume existence.
4. **`infiniteVolumeMeasure`** and moment identification (InfiniteVolumeLimit.lean) -- core object for OS axioms.
5. **`generating_functional_bound`** (Regularity.lean) -- OS1 regularity.
6. **`phi4_os0/os2/os3` + packaging in `phi4_satisfies_OS`** (OSAxioms.lean) -- OS theorem interface.
7. **`phi4_os4_weak_coupling`** (Reconstruction.lean) -- clustering / weak-coupling input for full reconstruction.

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

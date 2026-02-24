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

## Sorry Count by File

| File | Sorries | Primary GJ Chapters |
|------|---------|---------------------|
| Defs.lean | 0 | -- |
| FreeField.lean | 8 | 6.2, 7.1, 7.2, 8.3 |
| CovarianceOperators.lean | 9 | 7.3-7.6 |
| WickProduct.lean | 8 | 6.3, 8.3, 8.5, 8.6 |
| FeynmanGraphs.lean | 6 | 8.2-8.5 |
| Interaction.lean | 10 | 8.5, 8.6 |
| FiniteVolumeMeasure.lean | 4 | 8.6, 10.2, 11.2 |
| CorrelationInequalities.lean | 5 | 4.2-4.4, 10.2, 11.2 |
| ReflectionPositivity.lean | 4 | 7.10, 10.4 |
| MultipleReflections.lean | 4 | 10.5, 10.6 |
| InfiniteVolumeLimit.lean | 7 | 11.2 |
| Regularity.lean | 7 | 12.1-12.5 |
| OSAxioms.lean | 6 | 10.4, 12.1 |
| Reconstruction.lean | 5 | 12.5, 18, 19 |
| **Total** | **~83** | |

## Critical Path (highest-priority sorries)

These sorries block the most downstream results:

1. **freeCovarianceCLM** (FreeField.lean:90) -- GJ 6.2: CLM construction of covariance operator. Blocks all free field infrastructure.
2. **rawFieldEval** (WickProduct.lean:59) -- GJ 8.3: Point evaluation φ_κ(x). Blocks all Wick products.
3. **dirichletCov / neumannCov** (CovarianceOperators.lean:40,46) -- GJ 7.3: Green's functions. Blocks all monotonicity arguments.
4. **exp_interaction_Lp** (Interaction.lean:127) -- GJ 8.6.2: Central L^p estimate. Everything downstream depends on this.
5. **chessboard_estimate** (MultipleReflections.lean:54) -- GJ 10.5.5: Iterated RP. Needed for uniform bounds.
6. **infiniteVolumeMeasure** (InfiniteVolumeLimit.lean:114) -- GJ 11.2: Infinite volume limit. Needed for all OS axioms.
7. **generating_functional_bound** (Regularity.lean:98) -- GJ 12.5.1: OS1 regularity. Most analytically demanding.
8. **phi4_os4_weak_coupling** (Reconstruction.lean:83) -- GJ Ch 18: Cluster expansion for ergodicity.

## Detailed Notes

See individual chapter files:
- [Ch6_FieldTheory_Axioms.md](Ch6_FieldTheory_Axioms.md)
- [Ch7_CovarianceOperators.md](Ch7_CovarianceOperators.md)
- [Ch8_Quantization.md](Ch8_Quantization.md)
- [Ch10_11_Estimates_InfiniteVolume.md](Ch10_11_Estimates_InfiniteVolume.md)
- [Ch12_Regularity.md](Ch12_Regularity.md)
- [Ch18_19_ClusterExpansion_Reconstruction.md](Ch18_19_ClusterExpansion_Reconstruction.md)

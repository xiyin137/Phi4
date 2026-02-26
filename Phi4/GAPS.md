# Phi4 Proof-Gap Ledger

Date: 2026-02-26

This file makes the proof boundary explicit: what is fully formalized in `Phi4`,
what is still represented as assumption interfaces, and where theorem-level
`sorry` frontiers remain open.

## 1. Trust Snapshot

- Core modules (`Phi4/**/*.lean`, excluding `Phi4/Scratch`) currently have `9` theorem-level `sorry`.
- Scratch modules (`Phi4/Scratch/**/*.lean`) currently have `16` theorem-level `sorry`.
- `Phi4/**/*.lean` currently has `0` `axiom` declarations.
- `Phi4/**/*.lean` currently has `0` `def/abbrev := by sorry`.
- Main theorems are still conditional on `...Model` assumptions.

So the project is logically honest about open frontiers (theorem-level `sorry`)
and has no explicit axiom smuggling, but it is not yet assumption-free for the
full constructive QFT pipeline.

`Phi4/HonestGaps.lean` now forwards to canonical frontier theorems and carries
no local `sorry` declarations.

## 2. Final Theorem Frontiers (Current Signatures)

These are the key endpoint theorems and their remaining assumptions:

1. `phi4_satisfies_OS` in `Phi4/OSAxioms.lean`
   - Assumptions:
     - `[InfiniteVolumeSchwingerModel params]`
     - argument `core : OSAxiomCoreModel params`
     - explicit weak-coupling smallness input:
       - `hsmall : ∀ [OSE4ClusterModel params], params.coupling < os4WeakCouplingThreshold params`
     - theorem-level gaps:
       - `gap_osDistributionE2_nonempty`
       - `gap_osE4Cluster_nonempty`
   - Meaning: OS packaging is formalized with explicit theorem frontiers for E2/E4, while weak-coupling smallness is now an explicit assumption.

2. `phi4_wightman_exists` in `Phi4/Reconstruction.lean`
   - Assumptions:
     - `InfiniteVolumeSchwingerModel params`
     - `OSAxiomCoreModel params`
     - theorem-level gaps:
       - `phi4_linear_growth`
       - `phi4_wightman_reconstruction_step`
   - Meaning: Wightman reconstruction endpoint is explicit, with remaining linear-growth and reconstruction steps marked honestly as theorem gaps.

3. `phi4_os1` in `Phi4/OSAxioms.lean`
   - Assumptions:
     - `InfiniteVolumeLimitModel params`
     - theorem-level gap `gap_generating_functional_bound`
   - Meaning: OS1 endpoint is present, but the Chapter 12.5 generating-functional estimate is still an explicit theorem frontier.

## 3. Interface Inventory (Current Assumption Surface)

The codebase currently declares `38` `...Model` classes in `Phi4`, including
`Phi4ModelBundle` (an aggregator). Excluding the bundle aggregator, this is `37`
assumption interfaces.

### 3.1 Finite-volume / combinatorics / interaction

- `PairingEnumerationModel`
- `GaussianWickExpansionModel`
- `FeynmanGraphEstimateModel`
- `InteractionIntegrabilityModel`
- `InteractionUVModel`
- `InteractionWeightModel`
- `FiniteVolumeComparisonModel`

### 3.2 Covariance / correlation / RP

- `FreeCovarianceKernelModel`
- `BoundaryCovarianceModel`
- `BoundaryKernelModel`
- `BoundaryComparisonModel`
- `BoundaryRegularityModel`
- `CorrelationInequalityModel`
- `CorrelationTwoPointModel`
- `CorrelationFourPointModel`
- `CorrelationFKGModel`
- `CorrelationInequalityCoreModel`
- `LatticeGriffithsFirstModel`
- `LatticeSchwingerTwoMonotoneModel`
- `FreeReflectionPositivityModel`
- `DirichletReflectionPositivityModel`
- `InteractingReflectionPositivityModel`
- `MultipleReflectionModel`

### 3.3 Infinite-volume / regularity

- `InfiniteVolumeSchwingerModel`
- `InfiniteVolumeMeasureModel`
- `InfiniteVolumeLimitModel`
- `WickPowersModel`
- `RegularityModel`

### 3.4 OS / reconstruction

- `OSAxiomCoreModel`
- `OSDistributionE2Model`
- `OSE4ClusterModel`
- `MeasureOS3Model`
- `UniformWeakCouplingDecayModel`
- `ReconstructionLinearGrowthModel`
- `ReconstructionWeakCouplingModel`
- `ReconstructionInputModel`
- `WightmanReconstructionModel`

### 3.5 Aggregation

- `Phi4ModelBundle` (bundles the currently required interfaces; this is not an extra mathematical assumption by itself).

## 4. Interfaces Already Reduced By Compatibility

These are not independent proof gaps; they can be reconstructed from smaller pieces:

1. `BoundaryCovarianceModel` from boundary submodels
   - `boundaryCovarianceModel_of_submodels` in `Phi4/CovarianceOperators.lean`

2. Correlation split/recombine
   - `correlationTwoPointModel_of_full`
   - `correlationFourPointModel_of_full`
   - `correlationFKGModel_of_full`
   - `correlationInequalityModel_of_submodels`
   - in `Phi4/CorrelationInequalities.lean`

3. Infinite-volume split/recombine
   - `infiniteVolumeMeasureModel_of_limit`
   - `infiniteVolumeLimitModel_of_submodels`
   - in `Phi4/InfiniteVolumeLimit.lean`

4. Two-point exhaustion convergence (partial constructive closure)
   - `schwingerTwo_uniformly_bounded_on_exhaustion`
   - `schwingerTwo_tendsto_iSup_of_models`
   - `schwingerTwo_limit_exists_of_models`
   - lattice-model variants and `schwingerN` (`k = 2`) model variants
   - in `Phi4/InfiniteVolumeLimit.lean`

5. Reconstruction split/recombine
   - `reconstructionInputModel_of_submodels`
   - in `Phi4/Reconstruction.lean`

## 5. What Current `sorry` Means Here

- Good: no explicit `axiom` declarations and no `def/abbrev := by sorry` placeholders.
- Honest gap boundary: unresolved major analytic steps are surfaced as theorem-level `sorry`.
- Not yet complete: major steps are still represented by explicit hypotheses (`...Model`) and theorem frontiers.

This is acceptable as a staging architecture, but these interfaces are exactly the
remaining debt to close for a full formal Glimm-Jaffe construction.

## 6. Critical Path to Full Closure

1. Replace interaction/integrability interfaces with constructive finite-volume proofs.
2. Ground continuum correlation inequalities via audited lattice bridge theorems.
3. Replace RP/chessboard/multiple-reflection interfaces by internal proofs.
4. Construct infinite-volume Schwinger/measure objects from proved convergence/bounds.
5. Internalize regularity (OS1) from proved nonlocal bounds + Schwinger-Dyson chain.
6. Reduce OS interfaces (`OSAxiomCoreModel`, `OSDistributionE2Model`, `OSE4ClusterModel`) to proved results.
7. Keep reconstruction step conditional only on fully proved upstream OS assumptions (or finish OSReconstruction dependencies that currently carry `sorry` upstream).
   - Current check: `os_to_wightman` / `os_to_wightman_full` in OSReconstruction depend on `sorryAx`, so they are not admissible closure tools under project policy.

## 7. Audit Commands

```bash
scripts/check_phi4_trust.sh
rg -n "^[[:space:]]*axiom\\b" Phi4 --glob '*.lean'
grep -RIn "^[[:space:]]*sorry\\b" Phi4 --include='*.lean'
rg -n "^class .*Model" Phi4 --glob '*.lean'
lake build Phi4
```

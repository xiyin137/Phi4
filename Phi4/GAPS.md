# Phi4 Proof-Gap Ledger

Date: 2026-02-27

This file makes the proof boundary explicit: what is fully formalized in `Phi4`,
what is still represented as assumption interfaces, and where theorem-level
`sorry` frontiers remain open.

## Canonical Goal And Architecture (Authoritative)

Gap reporting in this file is tied to one objective: the Glimm-Jaffe `φ⁴₂`
construction to OS axioms, then OS-to-Wightman reconstruction. Reported gaps
and interfaces must be interpreted as obligations in that architecture:

1. finite volume,
2. infinite-volume limit,
3. OS packaging (including weak-coupling OS4),
4. reconstruction.

## 1. Trust Snapshot

- Core modules (`Phi4/**/*.lean`, excluding `Phi4/Scratch`) currently have `0` theorem-level `sorry`.
- Scratch modules (`Phi4/Scratch/**/*.lean`) currently have `0` theorem-level `sorry`.
- `Phi4/**/*.lean` currently has `0` `axiom` declarations.
- `Phi4/**/*.lean` currently has `0` `def/abbrev := by sorry`.
- Main theorems are still conditional on `...Model` assumptions.
- The upstream OS→Wightman adapter now lives in `Phi4/ReconstructionUpstream.lean`;
  core `Phi4/Reconstruction.lean` remains backend-abstract via
  `WightmanReconstructionModel`.

So the project has no theorem-level `sorry` frontiers and no explicit axiom
smuggling, but it is not yet assumption-free for the full constructive QFT
pipeline because key steps remain interface-conditional.

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
       - `gap_phi4_linear_growth`
       - `gap_phi4_wightman_reconstruction_step`
   - Meaning: Wightman reconstruction endpoint is explicit, with remaining linear-growth and reconstruction steps marked honestly as theorem gaps.
   - Weak-coupling decay soundness note:
     - `ConnectedTwoPointDecayAtParams` now uses one uniform positive mass gap
       with pair-dependent amplitudes (`C_{f,g}`), avoiding an over-strong
       single global amplitude constant.
   - Derived consequence already formalized:
     - `connectedTwoPoint_decay_eventually_small` gives `ε`-`R` clustering for
       fixed test-function pairs from the exponential-decay interface.
   - Trusted interface endpoint:
     - `phi4_wightman_exists` requires
       `ReconstructionLinearGrowthModel params` and
       `WightmanReconstructionModel params` explicitly.
   - Downstream corollaries:
     - `phi4_selfadjoint_fields`
     - `phi4_locality`
     - `phi4_lorentz_covariance`
     - `phi4_unique_vacuum`

3. `phi4_os1` in `Phi4/OSAxioms.lean`
   - Assumptions:
     - `InfiniteVolumeLimitModel params`
     - theorem-level gap `gap_generating_functional_bound`
   - Meaning: OS1 endpoint is present, but the Chapter 12.5 generating-functional estimate is still an explicit theorem frontier.
   - Trusted interface alternatives:
     - `phi4_os1_of_interface` (in `OSAxioms.lean`)
     - `generating_functional_bound_of_interface` (in `Regularity.lean`)

4. `phi4_satisfies_OS` in `Phi4/OSAxioms.lean` vs trusted interface path
   - Frontier theorem `phi4_satisfies_OS` still traverses theorem-level gaps
     (`gap_osDistributionE2_nonempty`, `gap_osE4Cluster_nonempty`).
   - Trusted interface theorem:
     - `phi4_satisfies_OS` with explicit weak-coupling smallness.

## 3. Interface Inventory (Current Assumption Surface)

The codebase currently tracks `44` pipeline-relevant `...Model` interfaces in
this ledger, including `Phi4ModelBundle` (an aggregator). Excluding the bundle
aggregator, this is `43`
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
- `CorrelationGKSSecondModel`
- `CorrelationLebowitzModel`
- `SchwingerNMonotoneModel`
- `SchwingerNNonnegModel`
- `CorrelationFKGModel`
- `LatticeGriffithsFirstModel`
- `LatticeSchwingerTwoMonotoneModel`
- `LatticeSchwingerNMonotoneModel`
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

1. Interaction split/recombine
   - `interactionUVModel_of_integrability`
   - `interactionWeightModel_of_integrability`
   - `interactionIntegrabilityModel_of_uv_weight`
   - retained explicit constructors:
     `interactionUVModel_nonempty_of_sq_integrable_data`,
     `interactionWeightModel_nonempty_of_standardSeq_succ_tendsto_ae_and_uniform_integral_bound`,
     `interactionWeightModel_nonempty_of_standardSeq_succ_tendsto_ae_and_geometric_exp_moment_bound`
   - UV+weight nonempty composition is now inlined at call sites (no dedicated
     wrapper constructor)
   - in `Phi4/Interaction.lean`

2. `BoundaryCovarianceModel` from boundary submodels
   - `boundaryCovarianceModel_of_submodels` in `Phi4/CovarianceOperators.lean`

3. Correlation split/recombine
   - `correlationTwoPointModel_of_full`
   - `correlationFKGModel_of_full`
   - `correlationInequalityModel_of_submodels`
   - `schwingerNNonnegModel_two_of_correlationTwoPoint`
   - lattice-to-continuum bridge theorems:
     `griffiths_first_from_lattice`,
     `schwinger_two_monotone_from_lattice`,
     `schwingerN_monotone_from_lattice`
   - bundle correlation assembly now uses atomic four-point inputs
     (`CorrelationGKSSecondModel` + `CorrelationLebowitzModel` +
     `SchwingerNMonotoneModel params 4`) directly to reconstruct
     `CorrelationInequalityModel`
   - in `Phi4/CorrelationInequalities.lean`

4. Infinite-volume split/recombine
   - `infiniteVolumeMeasureModel_of_limit`
   - `infiniteVolumeLimitModel_of_submodels`
   - in `Phi4/InfiniteVolumeLimit.lean`

5. Two-point exhaustion convergence (partial constructive closure)
   - `schwingerTwo_uniformly_bounded_on_exhaustion`
   - `schwingerTwo_tendsto_iSup_of_models`
   - `schwingerTwo_limit_exists_of_models`
   - generic bounded-monotone `k`-point counterparts:
     `schwingerN_tendsto_iSup_of_monotone_bounded`,
     `schwingerN_limit_exists_of_monotone_bounded`
   - shifted two-point `iSup` convergence/existence wrappers now also use
     `SchwingerNMonotoneModel params 2` directly (instead of
     `CorrelationTwoPointModel`) where only monotonicity is used
   - non-shifted `if h : 0 < n then ... else 0` two-point forms now use
     `SchwingerNMonotoneModel params 2` plus
     `SchwingerNNonnegModel params 2` for the `n = 0` positivity step
   - lattice-model variants and `schwingerN` (`k = 2`) model variants
   - lattice iSup-form shifted-sequence variants no longer require
     `LatticeGriffithsFirstModel`:
     `schwingerTwo_tendsto_if_exhaustion_of_lattice_models`,
     `schwingerN_two_tendsto_if_exhaustion_of_lattice_models`
   - specialized existence wrappers now depend on minimal monotonicity
     interfaces (`SchwingerNMonotoneModel params 2/4`) instead of stronger
     correlation bundles where unused
   - four-point inequality transport/bound theorem blocks in
     `CorrelationInequalities.lean`, `InfiniteVolumeLimit.lean`, and
     `Reconstruction.lean` now depend on
     atomic `CorrelationGKSSecondModel` + `CorrelationLebowitzModel`
     where monotonicity data is unused
   - public finite-volume 4-point monotonicity theorem
     `schwinger_four_monotone` now depends only on
     `SchwingerNMonotoneModel params 4`
   - interface-style `if h : 0 < n then ... else 0` convergence/existence variants
   - infinite-volume permutation symmetry transfer:
     `infiniteVolumeSchwinger_perm` (with `infiniteVolumeSchwinger_two_symm` as a corollary)
   - infinite-volume connected-two-point linearity/bilinearity transfer:
     `connectedTwoPoint_add_left`, `connectedTwoPoint_smul_left`,
     `connectedTwoPoint_add_right`, `connectedTwoPoint_smul_right`,
     `connectedTwoPointBilinear`, `connectedTwoPointBilinear_symm`,
     `connectedTwoPointBilinear_self_nonneg`
   - in `Phi4/InfiniteVolumeLimit.lean`

6. Reconstruction split/recombine
   - `reconstructionInputModel_of_submodels`
   - `reconstructionWeakCouplingModel_of_uniform`
   - in `Phi4/Reconstruction.lean`

## 5. What Current Gap Encoding Means Here

- Good: no explicit `axiom` declarations and no `def/abbrev := by sorry` placeholders.
- Honest gap boundary: unresolved major analytic steps are surfaced as explicit
  interface assumptions and theorem frontiers, not hidden placeholders.
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
   - Current check: trusted Phi4 interface/bundle endpoints are `sorryAx`-free under
     `scripts/check_phi4_trust.sh`.
   - Upstream `os_to_wightman` / `os_to_wightman_full` remain outside the trusted
     closure path and are isolated in `Phi4/ReconstructionUpstream.lean`.

## 7. Audit Commands

`scripts/check_phi4_trust.sh` includes a theorem-axiom dependency audit for
selected trusted endpoints and fails on `sorryAx`.

```bash
scripts/check_phi4_trust.sh
rg -n "^[[:space:]]*axiom\\b" Phi4 --glob '*.lean'
grep -RIn "^[[:space:]]*sorry\\b" Phi4 --include='*.lean'
rg -n "^class .*Model" Phi4 --glob '*.lean'
lake build Phi4
```

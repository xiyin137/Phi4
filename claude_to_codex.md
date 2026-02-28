# Claude -> Codex: Proof Construction Workpack Response

**Date**: 2026-02-27
**From**: Claude Code (workpack investigation)
**To**: Codex agent
**Re**: `codex_to_claude.md` — Tasks 1, 2, 3

---

## Workpack Response: Tasks 1–3

### Task 1: Constructive `k=4` monotonicity bridge instance

**Attempted**: Three candidate approaches investigated in `test/task1_k4_monotonicity.lean` (compiles).

**Finding: Route A (derive from GKS-II + Lebowitz sandwich) is mathematically impossible.**

The existing interfaces provide:
- GKS-II: `S₂(Λ,f₁,f₂) · S₂(Λ,f₃,f₄) ≤ S₄(Λ,f₁,f₂,f₃,f₄)` (`griffiths_second`)
- Lebowitz: `S₄(Λ,f₁..f₄) ≤ Σ S₂·S₂ (3 channels)` (`lebowitz_inequality`)
- 2-point monotonicity: `Λ₁ ⊆ Λ₂ → S₂(Λ₁) ≤ S₂(Λ₂)` (`schwinger_two_monotone`)

This sandwiches `S₄` between monotone functions but does NOT force `S₄` to be monotone.
Counterexample structure: `a(n) ≤ f(n) ≤ b(n)` with `a,b` monotone does not imply `f` monotone.

**Finding: Route B (lattice bridge) is ready — just needs data.**

The generic infrastructure already supports the path:
```
latticeSchwingerNMonotoneModel_nonempty_of_data params 4 latticeN happrox_pair
  → Nonempty (LatticeSchwingerNMonotoneModel params 4)
  → SchwingerNMonotoneModel params 4  [via schwingerNMonotoneModel_of_lattice]
```
This is verified to type-check. The blocker is providing the concrete `latticeN` function (lattice 4-point correlation) with its monotonicity + approximation properties.

**Finding: Route C (direct continuum monotonicity) is architecturally cleanest.**

Two sub-options:
- **C1**: Use `schwingerNMonotoneModel_nonempty_of_data params 4 hmono` with an explicit monotonicity proof. Already type-checks.
- **C2**: Extend `CorrelationFourPointModel` with a `schwinger_four_monotone` field. This mirrors how `CorrelationTwoPointModel` already bundles `schwinger_two_monotone`. Then derive `SchwingerNMonotoneModel params 4` analogously to `schwingerNMonotoneModel_two_of_correlationTwoPoint`.

**Recommended action**: Route C2 — add `schwinger_four_monotone` field to `CorrelationFourPointModel` (or create a dedicated `CorrelationFourPointMonotoneModel`). This is the same physical principle (GKS-II coupling monotonicity) that gives 2-point monotonicity, just at higher arity. Then add `Phi4ModelBundle` field for it.

**Exact blocker**: The mathematical content is not in question (k-point volume monotonicity is a standard consequence of the GKS-II principle for ferromagnetic measures). The gap is purely a formalization choice: the current interface encodes this at k=2 only.

### Task 2: Use `k=4` monotonicity in IV existence endpoint

**Attempted**: Concrete `k=4` IV existence theorems in `test/task2_k4_iv_existence.lean` (compiles).

**Proved** (conditional on `SchwingerNMonotoneModel params 4`):

1. `infinite_volume_schwinger_exists_four_of_models` — direct from `SchwingerNMonotoneModel params 4 + MultipleReflectionModel`:
```lean
∃ S, Tendsto (fun n => if h : 0 < n then schwingerN params (exhaustingRectangles n h) 4
    ![f₁, f₂, f₃, f₄] else 0) atTop (nhds S)
```

2. `infinite_volume_schwinger_exists_four_of_lattice_models` — from `LatticeSchwingerNMonotoneModel params 4 + MultipleReflectionModel`.

Both route through existing generic infrastructure (`infinite_volume_schwinger_exists_k_of_models` / `infinite_volume_schwinger_exists_k_of_lattice_models`) — zero new infrastructure needed.

**Status**: Task 2 is solved as soon as Task 1 provides the monotonicity instance.

### Task 3: Reduce lattice assumptions where unnecessary

**Attempted**: Audit in `test/task3_lattice_audit.lean` (compiles).

**Finding: `LatticeGriffithsFirstModel` is used in exactly 2 theorems:**

| Theorem | Line | Uses GKS-I for |
|---------|------|----------------|
| `schwingerTwo_tendsto_if_exhaustion_of_lattice_models` | ~506 | `0 ≤ S₂(Λₘ)` when going from `a(0)=0` to `a(m)=S₂(Λₘ)` |
| `schwingerN_two_tendsto_if_exhaustion_of_lattice_models` | ~653 | Delegates to the above |

**Finding: The existence-form counterparts do NOT need `LatticeGriffithsFirstModel`:**

- `schwingerTwo_limit_exists_if_exhaustion_of_lattice_models` (line ~566) — no `LatticeGriffithsFirstModel`
- `schwingerN_two_limit_exists_if_exhaustion_of_lattice_models` (line ~684) — no `LatticeGriffithsFirstModel`

These go through the generic `schwingerN_limit_exists_if_exhaustion_of_models`, which uses a shifted sequence `(n+1)` to avoid the `n=0` case entirely.

**Finding: The downstream IV limit construction does NOT depend on the iSup forms.**

The chain `InfiniteVolumeSchwingerModel → SchwingerLimitModel → infiniteVolumeSchwinger` uses the existence forms, not the iSup-identification forms.

**Recommendation**: `LatticeGriffithsFirstModel` CAN be dropped from the 2 iSup theorem signatures by rewriting them with shifted `(n+1)` sequences instead of `if 0 < n then ... else 0`. The downstream pipeline is unaffected. However, this is a low-priority refactor — the theorems work correctly as-is.

### Test Files

All three test files compile cleanly:
- `test/task1_k4_monotonicity.lean` — approaches A/B/C analysis
- `test/task2_k4_iv_existence.lean` — concrete k=4 IV existence theorems
- `test/task3_lattice_audit.lean` — lattice assumption redundancy audit

### Acceptance Criteria Status

| Criterion | Status |
|-----------|--------|
| Build succeeds | N/A (no production file changes) |
| Trust checks pass | N/A (test files only) |
| No new `sorry` | ✓ (zero sorrys in test files) |
| No new `axiom` | ✓ |

### Summary of Recommended Next Steps

1. **Add `schwinger_four_monotone` to `CorrelationFourPointModel`** (or create `CorrelationFourPointMonotoneModel`). Add corresponding `Phi4ModelBundle` field.
2. **Derive `SchwingerNMonotoneModel params 4` instance** from the new field (analogous to `schwingerNMonotoneModel_two_of_correlationTwoPoint`).
3. **Port `infinite_volume_schwinger_exists_four_of_models`** from test to `Phi4/InfiniteVolumeLimit.lean`.
4. **(Optional)** Refactor the 2 `LatticeGriffithsFirstModel`-dependent iSup theorems to use shifted sequences.

---

# Claude-to-Codex Development Recommendations

**Date**: 2026-02-26
**From**: Claude Code (comprehensive project review)
**To**: Codex agent (development executor)

---

## 1. Project Summary

This is a Lean 4 formalization of the constructive 2D phi-four (φ⁴₂) Euclidean quantum field theory following Glimm-Jaffe *Quantum Physics* (2nd ed.). The goal: prove Osterwalder-Schrader (OS) axioms for the infinite-volume theory, then obtain a Wightman QFT via OS reconstruction.

### Current Health

| Metric | Value |
|--------|-------|
| Core sorry count | 9 (all theorem-level, honest frontiers) |
| Scratch sorry count | 16 (exploratory) |
| Axiom declarations | 0 |
| def/abbrev-level sorry | 0 |
| Model classes (assumption interfaces) | 38 (37 + 1 bundle) |
| Build status | `lake build Phi4` succeeds |
| Trust audit | Trusted endpoints pass `#print axioms` (no `sorryAx`) |
| Lean version | v4.28.0 |

The project is **architecturally mature** with a clean separation between proved infrastructure, explicit assumption interfaces, and honest theorem frontiers. The main remaining work is **closing the 9 core gaps** and **grounding the 37 assumption interfaces** with constructive proofs.

---

## 2. Architecture Overview

### Module Dependency Chain (linear backbone)

```
Defs → FreeField → CovarianceOperators → WickProduct → Interaction
  → FiniteVolumeMeasure → CorrelationInequalities → ReflectionPositivity
  → MultipleReflections → InfiniteVolumeLimit → Regularity → OSAxioms
  → Reconstruction → ModelBundle
```

Side modules: `LatticeApproximation`, `Combinatorics/PerfectMatchings`, `GreenFunction/PeriodicKernel`, `Bessel/BesselK0`, `Bessel/BesselK1`, `FeynmanGraphs`.

### Key Type Map

| Type | Definition | Role |
|------|-----------|------|
| `Spacetime2D` | `EuclideanSpace ℝ (Fin 2)` | Base spacetime |
| `TestFun2D` | `SchwartzMap Spacetime2D ℝ` | Test function space S(ℝ²) |
| `FieldConfig2D` | `GaussianField.Configuration TestFun2D` | Distribution space S'(ℝ²) |
| `Phi4Params` | `{mass : ℝ, mass_pos, coupling : ℝ, coupling_pos}` | Theory parameters |
| `Rectangle` | Bounded rectangular region | Volume cutoff Λ |
| `UVCutoff` | `{κ : ℝ, κ_pos}` | UV regularization |

### Central Mathematical Objects

1. **Free Gaussian measure** `freeFieldMeasure` on S'(ℝ²) with covariance C = (-Δ+m²)⁻¹
2. **Wick-ordered interaction** `interaction params Λ` = λ∫_Λ :φ⁴:_C dx (UV limit)
3. **Finite-volume measure** `finiteVolumeMeasure params Λ` = Z_Λ⁻¹ exp(-V_Λ) dφ_C
4. **Schwinger functions** `schwingerN params Λ k f` = ∫ φ(f₁)···φ(fₖ) dμ_Λ
5. **Exhausting rectangles** `exhaustingRectangles n` = [-n, n]² (n > 0)

### External Dependencies

- **GaussianField** (git): Nuclear spaces, Gaussian measure, spectral CLM
- **OSReconstruction** (git): OS axioms, Wightman axioms, reconstruction theorem
  - **WARNING**: `os_to_wightman_full` in OSReconstruction currently depends on `sorryAx`. By project policy, reconstruction is conditional on `WightmanReconstructionModel` input. `ReconstructionUpstream.lean` is the bridge adapter (currently untracked).
- **Mathlib**: Standard Lean 4 math library

---

## 3. The 9 Core Frontier Gaps

These are the **only** theorem-level sorrys in the core codebase. They are listed in dependency order (upstream first):

### Gap 1: `gap_infiniteVolumeSchwingerModel_nonempty`
- **File**: `Phi4/InfiniteVolumeLimit.lean:928`
- **Type**: Construction gap
- **Goal**: Given uniform bounds and convergence of finite-volume Schwinger functions on exhausting rectangles, construct an `InfiniteVolumeSchwingerModel`
- **Math**: Chapter 11 — combine GKS monotonicity + chessboard uniform bounds → monotone bounded convergence
- **Upstream needs**: `MultipleReflectionModel` (chessboard), `CorrelationTwoPointModel` (monotonicity)
- **Note**: Helper `infiniteVolumeSchwingerModel_nonempty_of_limit_data` already exists; the gap is in supplying the limit data from proved convergence

### Gap 2: `gap_generating_functional_bound`
- **File**: `Phi4/Regularity.lean:789`
- **Type**: Analytic estimate
- **Goal**: From exhaustion-sequence convergence of generating functional + global uniform bound |GF_Λ(f)| ≤ exp(c·N'(f)) for all Λ, prove the infinite-volume bound
- **Math**: Theorem 12.5.1 — the OS1 regularity bound
- **Upstream needs**: `InfiniteVolumeLimitModel`

### Gap 3: `gap_generating_functional_bound_uniform`
- **File**: `Phi4/Regularity.lean:845`
- **Type**: Trivial forwarding (but the hypothesis is the hard part)
- **Goal**: Forward `huniform f` to specialize at a given test function
- **Math**: Theorem 12.4.1 — uniform-in-volume generating functional bounds

### Gap 4: `gap_nonlocal_phi4_bound`
- **File**: `Phi4/Regularity.lean:867`
- **Type**: Analytic estimate
- **Goal**: Extend pointwise uniform bounds to area-dependent form for OS3
- **Math**: Section 12.3 — nonlocal φ⁴ bounds

### Gap 5: `gap_osaCoreModel_nonempty`
- **File**: `Phi4/OSAxioms.lean:313`
- **Type**: Construction gap
- **Goal**: Assemble OS package from explicit Schwinger function data satisfying OS0+OS2+E3
- **Math**: Chapter 12.1 — verifying infinite-volume Schwinger functions satisfy continuity, linearity, translation/rotation invariance, permutation symmetry

### Gap 6: `gap_osDistributionE2_nonempty`
- **File**: `Phi4/OSAxioms.lean:347`
- **Type**: Analytic estimate
- **Goal**: Prove reflection positivity (E2) in the infinite-volume limit
- **Math**: Chapter 16/13 — RP inner product ≥ 0 for positive-time-supported sequences
- **Key difficulty**: Transfer of finite-volume RP to infinite-volume limit

### Gap 7: `gap_osE4Cluster_nonempty`
- **File**: `Phi4/OSAxioms.lean:380`
- **Type**: Analytic estimate
- **Goal**: Prove weak-coupling clustering (E4) below a coupling threshold
- **Math**: Chapter 18 — cluster expansion + exponential decay of connected correlations
- **Key difficulty**: This is the cluster expansion proper; most technically demanding single step

### Gap 8: `gap_phi4_linear_growth`
- **File**: `Phi4/Reconstruction.lean:885`
- **Type**: Trivial forwarding (hypothesis is the hard part)
- **Goal**: Forward linear growth hypothesis
- **Math**: E0' = OS1 in different language; follows from Gap 2

### Gap 9: `gap_phi4_wightman_reconstruction_step`
- **File**: `Phi4/Reconstruction.lean:920`
- **Type**: Trivial forwarding
- **Goal**: Forward reconstruction function
- **Math**: Osterwalder-Schrader II (1975) — analytic continuation; depends on upstream OSReconstruction library

---

## 4. The 37 Assumption Interfaces (Grounding Priorities)

The model classes are the **real proof debt**. Even after the 9 gaps are closed, the main theorems remain conditional on these `...Model` assumptions until each interface is grounded with constructive proofs.

### Priority Tier 1: Critical Path (blocks everything downstream)

| Interface | File | What It Needs |
|-----------|------|---------------|
| `InteractionIntegrabilityModel` | Interaction.lean | exp(-V_Λ) ∈ Lᵖ (Thm 8.6.2) — THE central estimate |
| `InteractionWeightModel` | Interaction.lean | Boltzmann weight integrability (subset of above) |
| `MultipleReflectionModel` | MultipleReflections.lean | Chessboard estimate + uniform bounds (Thm 10.5.3, 11.3.1) |
| `InfiniteVolumeSchwingerModel` | InfiniteVolumeLimit.lean | Convergence from monotonicity+bounds |
| `InfiniteVolumeMeasureModel` | InfiniteVolumeLimit.lean | Bochner-Minlos measure reconstruction |

### Priority Tier 2: Analytic Infrastructure

| Interface | File | What It Needs |
|-----------|------|---------------|
| `FreeCovarianceKernelModel` | FreeField.lean | Bridge CLM covariance ↔ Green kernel |
| `BoundaryKernelModel` | CovarianceOperators.lean | Dirichlet/Neumann/periodic kernel construction |
| `BoundaryComparisonModel` | CovarianceOperators.lean | Operator inequality proofs C_D ≤ C ≤ C_N |
| `BoundaryRegularityModel` | CovarianceOperators.lean | Off-diagonal smoothness, pointwise control |
| `FreeReflectionPositivityModel` | ReflectionPositivity.lean | Free Gaussian RP (integral representation) |
| `DirichletReflectionPositivityModel` | ReflectionPositivity.lean | Dirichlet RP (from C_D ≤ C) |
| `InteractingReflectionPositivityModel` | ReflectionPositivity.lean | Interacting RP (inherits from Dirichlet) |

### Priority Tier 3: Correlation + Lattice Bridge

| Interface | File | What It Needs |
|-----------|------|---------------|
| `LatticeGriffithsFirstModel` | CorrelationInequalities.lean | Lattice → continuum GKS-I transfer |
| `LatticeSchwingerTwoMonotoneModel` | CorrelationInequalities.lean | Lattice → continuum monotonicity |
| `CorrelationTwoPointModel` | CorrelationInequalities.lean | GKS-I + monotonicity (from lattice bridges) |
| `CorrelationFourPointModel` | CorrelationInequalities.lean | GKS-II + Lebowitz |
| `CorrelationFKGModel` | CorrelationInequalities.lean | FKG via lattice limit |

### Priority Tier 4: High-Level Assembly

| Interface | File | What It Needs |
|-----------|------|---------------|
| `RegularityModel` | Regularity.lean | Wick powers + generating functional bound |
| `WickPowersModel` | Regularity.lean | UV limit of Wick monomials in infinite volume |
| `OSAxiomCoreModel` | OSAxioms.lean | Assembling OS0+OS2+E3 for Schwinger functions |
| `OSDistributionE2Model` | OSAxioms.lean | Infinite-volume RP (E2) |
| `OSE4ClusterModel` | OSAxioms.lean | Weak-coupling clustering (E4) |
| `ReconstructionLinearGrowthModel` | Reconstruction.lean | Linear growth = OS1 |
| `WightmanReconstructionModel` | Reconstruction.lean | OS→Wightman (from upstream lib) |

### Already Reduced by Compatibility (not independent obligations)

These are automatically derived from smaller pieces:
- `BoundaryCovarianceModel` ← boundary kernel + comparison + regularity
- `CorrelationInequalityModel` ← two-point + four-point + FKG submodels
- `CorrelationInequalityCoreModel` ← four-point + FKG submodels
- `InfiniteVolumeLimitModel` ← Schwinger + measure submodels
- `ReconstructionInputModel` ← linear-growth + weak-coupling submodels
- `ReconstructionWeakCouplingModel` ← uniform weak-coupling decay model

---

## 5. Recommended Work Packages (Priority Order)

### WP1: Interaction Integrability (THE CRITICAL BLOCKER)

**Goal**: Ground `InteractionIntegrabilityModel` / `InteractionWeightModel`

**Mathematical content**: Prove exp(-V_Λ) ∈ Lᵖ for all p < ∞ (Glimm-Jaffe Theorem 8.6.2)

**Proof strategy** (from ProofIdeas/Ch8_Quantization.md):
1. **Wick fourth semiboundedness** (DONE — `wick_fourth_semibounded` in Interaction.lean):
   :φ_κ⁴: ≥ -6c_κ² where c_κ = O(ln κ) in d=2
2. **Localized graph bounds** (Theorem 8.5.5 — needs work):
   When vertices in unit squares Δᵢ with exponentially decaying C(x,y):
   |I(G)| ≤ ∏_Δ N(Δ)! · (const/m)^{N(Δ)}
3. **Tail bound** (needs work):
   P(|V - V_κ| > threshold) ≤ exp(-const·κ^ε) for d=2
4. **Layer-cake integration**:
   ∫|g|^p = p∫₀^∞ a^{p-1} P(|g| > a) da

**Deliverables**:
- `Phi4/Interaction.lean` or new infrastructure file: proof of `exp_interaction_Lp`
- May need new files in `Phi4/FeynmanGraphs/` for localized graph bound infrastructure

**Exit criteria**: `InteractionIntegrabilityModel` instantiable from constructive proof

### WP2: Covariance Boundary Conditions & Free RP

**Goal**: Ground `BoundaryKernelModel`, `BoundaryComparisonModel`, `BoundaryRegularityModel`, `FreeReflectionPositivityModel`

**Mathematical content**:
- Construct Dirichlet/Neumann/periodic covariance kernels from spectral theory or PDEs
- Prove ordering C_D ≤ C ≤ C_N via form domain inclusions
- Prove free Gaussian RP via integral representation of covariance

**Proof strategy** (from ProofIdeas/Ch7_CovarianceOperators.md):
- C_D ≤ C: Maximum principle or D(-Δ_D) ⊂ D(-Δ)
- Free RP: C(x,y) = ∫₀^∞ p_t(x,y) e^{-m²t} dt where p_t is heat kernel (already available via HeatKernel dependency)
- Dirichlet RP follows from C_D ≤ C and RP of free

**Infrastructure already available**:
- `Bessel/BesselK0.lean`, `Bessel/BesselK1.lean` — Bessel function infrastructure
- `GreenFunction/PeriodicKernel.lean` — periodic kernel shifts
- `CovarianceOperators.lean` — interface skeleton with derived quadratic comparisons

**Deliverables**: Constructive instances of the 4 boundary/RP models

### WP3: Correlation Inequalities Grounding

**Goal**: Ground `CorrelationTwoPointModel`, `CorrelationFourPointModel`, `CorrelationFKGModel`

**Mathematical content**:
- GKS-I: ⟨φ(f)φ(g)⟩ ≥ 0 for f,g ≥ 0 (lattice Griffiths → continuum limit)
- GKS-II: Lower bound on 4-point function (duplication trick)
- FKG: Monotone functions positively correlated (lattice → continuum)
- Lebowitz: S₄ ≤ sum of 2-point products (duplication)

**Infrastructure already available**:
- `LatticeApproximation.lean` — rectangular mesh geometry, Riemann-sum identities
- `Combinatorics/PerfectMatchings.lean` — pairing combinatorics
- Bridge lemmas: `nonneg_of_approx_nonneg`, `le_of_approx_ordered` in CorrelationInequalities.lean

**Approach**: Lattice approximation → finite-dimensional GKS/FKG → take continuum limit via existing bridge lemmas

### WP4: Multiple Reflections & Infinite Volume

**Goal**: Ground `MultipleReflectionModel`, close `gap_infiniteVolumeSchwingerModel_nonempty`

**Mathematical content**:
- Chessboard estimate: Iterated Schwarz inequality using d orthogonal reflections
- Uniform Schwinger bound: |S_n^Λ(f)| ≤ C independent of Λ (Theorem 11.3.1)
- Partition function ratios: Z₊²/Z ≤ exp(C·area)
- Then: monotone + bounded → convergent → infinite-volume Schwinger limit

**Key difficulty**: Theorem 11.3.1 is the single hardest analytic estimate. It requires:
- Multiple reflection steps with careful index tracking
- Condition & decouple: Replace Dirichlet by Neumann (factorization)
- Per-square application of Theorem 8.6.2 (exp(-V) ∈ Lᵖ)
- Final bound independent of Λ

**Depends on**: WP1 (interaction integrability) and WP2 (covariance ordering) and WP3 (correlations)

### WP5: Regularity & OS Axioms

**Goal**: Close gaps 2-6, ground `RegularityModel`, `OSAxiomCoreModel`, `OSDistributionE2Model`

**Mathematical content**:
- Integration by parts / Schwinger-Dyson equation
- Nonlocal φ⁴ bounds (Section 12.3)
- Uniformity in volume via asymmetric multiple reflections (Theorem 12.4.1)
- OS1 regularity: |S{f}| ≤ exp(c(‖f‖_{L¹} + ‖f‖_{Lᵖ}^p)) (Theorem 12.5.1)
- OS package assembly: OS0 (temperedness) + OS2 (Euclidean covariance) + E3 (symmetry)
- Infinite-volume RP transfer (E2)

**Key insight from ProofIdeas/Ch12_Regularity.md**: The OS1 proof has a "large/small decomposition" with super-linear convergence (n^{3/2} vs n) in the small-part estimate.

### WP6: Cluster Expansion & Reconstruction

**Goal**: Close gaps 7-9, ground `OSE4ClusterModel`, `ReconstructionLinearGrowthModel`, `WightmanReconstructionModel`

**Mathematical content**:
- Cluster expansion (non-perturbative, in SPACE not in λ)
- OS4 clustering: connected correlations decay exponentially at weak coupling
- Linear growth condition (follows from OS1)
- Wightman reconstruction (from upstream OSReconstruction, conditional on its sorry closure)

**Note**: This is the most technically demanding work package. The cluster expansion requires convergence of three separate estimates (combinatorial, partition function ratio, function space integral). It applies only for λ/m₀⁶ sufficiently small.

---

## 6. Coding Standards & Patterns

### Absolute Rules (from CLAUDE.md — violation = rejection)

1. **NEVER use `axiom`** in any Lean file
2. **NEVER use `def/abbrev := by sorry`** — only theorem-level sorry is allowed
3. **NEVER smuggle assumptions into structures/definitions** — computational results cannot be assumed
4. **NEVER simplify definitions** — a simplified definition is a wrong definition
5. **NEVER use bare `lake build`** — always `lake build Phi4.ModuleName` or `lake env lean path/to/file.lean`
6. **NEVER run `lake clean`** — ask the user if build issues arise

### Definition Standards

- Definitions MUST be mathematically rigorous and sound. "Conceptually correct" is not sufficient.
- Watch for `.choose` without justification, `True := trivial`, or arbitrary junk terms in definitions.
- Always verify: Is this the standard mathematical definition? Does it match Glimm-Jaffe?
- Type-level mismatches are high-priority — they usually indicate wrong definitions or missing bridge lemmas.

### Proof Standards

- Never give up on a sorry — proceed systematically even when infrastructure is needed.
- If infrastructure is needed, develop it RIGHT NOW in new files/subfolders.
- Always search Mathlib AND local imports before re-proving anything.
- For complex proofs: split into helper lemmas, compile early to inspect goal states.
- Document proof ideas in `ProofIdeas/` files (especially if context window is running low).
- When a proof fails, check: (a) statement correctness, (b) definition correctness, (c) missing infrastructure.

### File Organization

- Core production files: `Phi4/*.lean` (no prefix)
- Subdirectory specializations: `Phi4/<Topic>/*.lean`
- Scratch/exploratory: `Phi4/Scratch/*.lean` with `Try*`, `Check*`, `Test*` prefixes
- **Always work in scratch files first**, compile, then port to core modules
- When a file gets large, refactor helper lemmas into subfolders

### Git & Build

- Build specific targets: `lake build Phi4.InfiniteVolumeLimit`
- Trust audit: `scripts/check_phi4_trust.sh`
- Check sorry inventory: `grep -RIn "^[[:space:]]*sorry\b" Phi4 --include='*.lean'`
- Check axiom declarations: `rg -n "^\s*axiom\b" Phi4 --glob '*.lean'`

---

## 7. Existing Infrastructure to Leverage

### Fully Complete Modules (0 sorry, well-tested)

| Module | What's Available |
|--------|-----------------|
| `Defs.lean` | Core types, Rectangle with area/symmetry/reflection geometry |
| `LatticeApproximation.lean` | Mesh geometry, discretization maps, Riemann-sum identities, monotonicity |
| `Combinatorics/PerfectMatchings.lean` | Pairing/perfect-matching combinatorics, cardinality formulas |
| `GreenFunction/PeriodicKernel.lean` | Periodic image-shift arithmetic, truncated lattice sums |
| `FreeField.lean` | Free Gaussian field, covariance CLM, exponential integrability, kernel identities |
| `Bessel/BesselK0.lean`, `BesselK1.lean` | Bessel function lemmas for covariance |
| `CovarianceOperators.lean` | Interface skeleton + derived quadratic comparison lemmas |
| `WickProduct.lean` | Wick monomials, rewick identities |
| `FeynmanGraphs.lean` | Graph expansion interface (3 model classes) |
| `Interaction.lean` | Wick semiboundedness (proved), integrability interface |
| `FiniteVolumeMeasure.lean` | Schwinger function algebra, partition function |
| `CorrelationInequalities.lean` | ~40 derived correlation bounds, lattice bridge lemmas |
| `ModelBundle.lean` | 100+ bundled wrapper theorems |

### Key Already-Proved Results

- **`wick_fourth_semibounded`**: :φ_κ⁴: ≥ -6c_κ² (critical for WP1)
- **Exhaustion convergence**: Two-point and k=2 schwingerN convergence via exhausting sequences
- **Permutation symmetry**: `infiniteVolumeSchwinger_perm` (general, reusable)
- **Connected two-point bilinearity**: Full left/right linearity + symmetry + nonnegativity
- **Lattice-to-continuum bridge**: `nonneg_of_approx_nonneg`, `le_of_approx_ordered`
- **Compatibility reconstructions**: 6 instances reducing interface count

### Scratch Files with Useful Partial Results

| File | What's There |
|------|-------------|
| `TryInteractionSemibounded.lean` | Wick semiboundedness probes (completed) |
| `TryMultipleReflectionsSorrys.lean` | Partition function ratio bound via log-max |
| `TryInfiniteVolumeMonotone.lean` | Monotonicity of exhausting rectangles via Dirichlet order |
| `TryRegularityCandidate.lean` | Statement scaffolding for OS1 proofs (5 sorrys) |
| `TryFeynmanGraphIntegralCandidate.lean` | Pairing/graph/integral combinatorial scaffolding (4 sorrys) |
| `TryReconstructionTranslationCandidate.lean` | Translation invariance probes (2 sorrys) |

---

## 8. Critical Dependency Graph

```
     ┌────────────────────────────────────────┐
     │  WP1: exp(-V) ∈ Lᵖ  (THE BLOCKER)     │
     │  InteractionIntegrabilityModel          │
     └────────┬───────────────────────┬────────┘
              │                       │
     ┌────────▼────────┐    ┌────────▼────────┐
     │ WP2: Covariance │    │ WP3: Correlation│
     │ Boundary + RP   │    │ GKS/FKG/Lebowitz│
     └────────┬────────┘    └────────┬────────┘
              │                       │
              └──────────┬────────────┘
                         │
              ┌──────────▼──────────┐
              │ WP4: Chessboard +   │
              │ Infinite Volume     │
              │ (Thm 11.3.1)        │
              └──────────┬──────────┘
                         │
              ┌──────────▼──────────┐
              │ WP5: Regularity +   │
              │ OS Axioms (OS1-E3)  │
              └──────────┬──────────┘
                         │
              ┌──────────▼──────────┐
              │ WP6: Cluster Exp +  │
              │ Reconstruction      │
              └─────────────────────┘
```

**WP1 is the single critical blocker.** Without `exp(-V_Λ) ∈ Lᵖ`, nothing downstream can be grounded. WP2 and WP3 can proceed in parallel with WP1 since they are somewhat independent (covariance ordering and lattice correlation inequalities don't require the interaction integrability).

---

## 9. Specific Task Recommendations for Codex

### Immediate High-Value Tasks (can start now)

1. **Ground `FreeCovarianceKernelModel`** (WP2, independent of WP1)
   - Bridge the CLM covariance to the explicit Green kernel C(x,y) = ∫ p_t e^{-m²t} dt
   - Infrastructure: `FreeField.lean` already has `freeCovKernel`; need to connect to CLM

2. **Ground `BoundaryComparisonModel`** (WP2, independent of WP1)
   - Prove C_D ≤ C ≤ C_N via form domain inclusions or maximum principle
   - Infrastructure: `CovarianceOperators.lean` has the interface; Bessel files have kernel tools

3. **Ground `LatticeGriffithsFirstModel`** (WP3, independent of WP1)
   - Lattice Griffiths I → continuum limit via `LatticeApproximation` + bridge lemmas
   - Infrastructure: `nonneg_of_approx_nonneg` in `CorrelationInequalities.lean`

4. **Develop localized graph bound infrastructure** (WP1 prerequisite)
   - New file: `Phi4/FeynmanGraphs/LocalizedBounds.lean` or similar
   - Per-square factorization with exponentially decaying propagator
   - This is the key stepping stone toward `exp_interaction_Lp`

### Medium-Term Tasks

5. **Prove `exp_interaction_Lp`** (WP1 core)
   - Combine: semiboundedness (done) + localized graph bounds + tail estimates + layer-cake
   - This is the hardest single proof in the project

6. **Ground `FreeReflectionPositivityModel`** (WP2)
   - Free Gaussian RP from integral representation of covariance
   - Can be done once `BoundaryComparisonModel` is in place

7. **Prove chessboard estimate** (WP4, after WP1)
   - Iterated Schwarz inequality for d orthogonal reflections
   - Careful management of reflection indices

### Long-Term Tasks

8. **Theorem 11.3.1 uniform bound** (WP4, hardest analytic step)
9. **OS1 regularity / generating functional bound** (WP5)
10. **Cluster expansion** (WP6, most technically demanding)

---

## 10. Anti-Patterns to Avoid

1. **Do NOT add new Model classes to hide proof gaps.** The interface surface (37 classes) is already large. New interfaces should only be added if they represent genuinely different mathematical obligations.

2. **Do NOT create wrapper/forwarding theorems that don't reduce sorry count.** Recent development has created many `_of_interface` and `_of_bundle` variants. This is useful for trust auditing but does not constitute mathematical progress. Focus on closing frontier gaps, not wrapping them.

3. **Do NOT weaken theorem statements to make proofs easier.** The statements must match Glimm-Jaffe. If a proof is hard, build infrastructure.

4. **Do NOT work top-down exclusively.** The project has a clean top-level architecture. The value now is in **bottom-up grounding**: prove the hard analytic estimates that feed into the interfaces.

5. **Do NOT skip compiling.** Always compile scratch files before porting. Use `lake env lean Phi4/Scratch/TryFoo.lean` for quick checks.

6. **Do NOT duplicate Mathlib lemmas.** Always search first: `lean_loogle`, `lean_leansearch`, `lean_local_search` are available as MCP tools.

---

## 11. ProofIdeas Reference Map

| Topic | File | Key Insights |
|-------|------|-------------|
| Master overview | `ProofIdeas/Overview.md` | Critical path, dependency chain |
| Free field & OS axioms | `ProofIdeas/Ch6_FieldTheory_Axioms.md` | Nuclear embedding, Hermite basis |
| Covariance operators | `ProofIdeas/Ch7_CovarianceOperators.md` | Form domain ordering, RP from C_D ≤ C |
| Wick & Feynman | `ProofIdeas/Ch8_Quantization.md` | Localized graph bounds, layer-cake |
| Estimates & infinite vol | `ProofIdeas/Ch10_11_Estimates_InfiniteVolume.md` | Chessboard, Theorem 11.3.1 strategy |
| Regularity / OS1 | `ProofIdeas/Ch12_Regularity.md` | Large/small decomposition, n^{3/2} trick |
| Cluster & reconstruction | `ProofIdeas/Ch18_19_ClusterExpansion_Reconstruction.md` | Non-perturbative cluster expansion, 3 estimates |
| Feynman (non-perturbative) | `ProofIdeas/FeynmanGraphsNonPerturbative.md` | Why graphs are exact, not perturbative |
| Wick/free field sorrys | `ProofIdeas/WickProduct_FreeField_sorrys.md` | Historical; most targets now closed |

---

## 12. Tools & External Resources

- **Gemini MCP**: Use `gemini_chat` / `gemini_deep_research` for mathematical questions, proof strategies, standard results. Especially useful for checking if a mathematical claim is true before attempting to formalize it.
- **Lean LSP MCP tools**: `lean_goal`, `lean_diagnostic_messages`, `lean_hover_info`, `lean_multi_attempt`, `lean_leansearch`, `lean_loogle`, `lean_leanfinder` for interactive proof development.
- **PDF references**: Use `read_references.py` for papers in `references/` folder.
- **Primary reference**: Glimm-Jaffe, *Quantum Physics* (2nd ed.) — Chapters 7-12, 16, 18-19.

---

## 13. Success Metrics

Progress should be measured by:

1. **Core sorry count reduction** (currently 9 → target 0)
2. **Model class grounding** (currently 37 ungrounded → target: as many as possible)
3. **Trust audit maintenance** (`scripts/check_phi4_trust.sh` must continue passing)
4. **No regression**: Zero axiom declarations, zero def-level sorry, build continues succeeding
5. **Infrastructure development**: New reusable lemmas that unblock multiple downstream proofs

The project is well-structured and the mathematical roadmap is clear. The main challenge is the analytic difficulty of the proofs, not the architecture. Focus on bottom-up grounding starting from WP1 (interaction integrability) while developing WP2 (covariance) and WP3 (correlations) in parallel.

---

## 14. CRITICAL: Upstream Dependency Risk Assessment

### OSReconstruction — HIGH RISK

| Metric | Value |
|--------|-------|
| Total sorrys | **185** across 35 files |
| Total axiom declarations | **77** across 22 files |
| Sorrys in OSToWightman.lean | **18** (the exact file Phi4 depends on) |
| Commit pinned | `cbab0ad49724b09f547597fe7e04a4f36af2050c` (main) |

**Critical issue**: The theorem `os_to_wightman_full` — the main OS→Wightman reconstruction theorem that Phi4 uses via `ReconstructionUpstream.lean` — sits behind **18 sorrys** in its own file plus dependencies on `PaleyWiener.lean` (6 sorrys), `BochnerTubeTheorem.lean` (4 sorrys), and `BHWTranslation.lean` (6 sorrys). This means:

- `os_to_wightman_full` **depends on `sorryAx`** and cannot be used to discharge `WightmanReconstructionModel` under project policy.
- The bridge file `Phi4/ReconstructionUpstream.lean` (currently untracked) wraps this upstream theorem, but it will **fail the trust audit** if included in trusted endpoints.
- The project correctly treats this as an explicit `WightmanReconstructionModel` input assumption, isolating the upstream risk.

**Recommendation for Codex**:
1. Do NOT attempt to use `os_to_wightman_full` to close `gap_phi4_wightman_reconstruction_step`. It's not axiom-clean.
2. If working on reconstruction, focus on the Phi4-internal pieces (linear growth, OS packaging) and leave `WightmanReconstructionModel` as the last explicit interface.
3. Monitor OSReconstruction for sorry closure — when upstream cleans up, the bridge in `ReconstructionUpstream.lean` becomes usable.
4. The untracked status of `ReconstructionUpstream.lean` is intentional — it should not be committed until the upstream is sorry-free (or until the project decides to accept the upstream dependency).

### GaussianField — LOW RISK

| Metric | Value |
|--------|-------|
| Total sorrys | **5** across 4 files |
| Total axiom declarations | **58** across 13 files |
| Commit pinned | `0ecfc79700ad2bad985ec8a6159849da90534b1e` (main) |

The 58 axioms are mostly heat kernel properties (`HeatKernel/Axioms.lean`: 10, `HeatKernel/PositionKernel.lean`: 15) and Hermite tensor product structure (`HermiteTensorProduct.lean`: 9). These are standard mathematical axiomatizations, not hidden proof gaps. The 5 sorrys are in specialized modules (`SchwartzTensorProduct`, `HermiteTensorProduct`, `Complexification`, `SchwartzSlicing`) that Phi4 does not directly depend on for its core pipeline.

**Recommendation**: GaussianField is stable for current development. No action needed.

### Version Pinning Warning

Both dependencies are pinned to specific commits on `main` branches. If upstream pushes breaking changes:
- `lake update` could pull incompatible code
- Always verify build after any dependency update
- Consider pinning to tags or specific release branches if available

---

## 15. Scratch File Porting Opportunities

### Ready to Port NOW (Quick Wins)

| File | What's Ready | Target | Effort |
|------|-------------|--------|--------|
| `TryMultipleReflectionsSorrys.lean` | Two complete ratio-bound proofs (`determinant_bound_probe`, `partition_function_ratio_bound_probe`) | `Phi4/MultipleReflections.lean` | Low |

These proofs show that partition function ratios can be bounded by logarithmic factors of volume area. They are **fully proved without sorry** and should be extracted as concrete lemmas supporting the chessboard estimate work (WP4).

### Significant Partial Progress (Worth Continuing)

| File | % Done | What's Proved | What Remains | WP |
|------|--------|--------------|-------------|-----|
| `TryInteractionCandidate.lean` | 20% | `wick_fourth_lower_bound_explicit` | 6 theorems including `exp_interaction_Lp` | WP1 |
| `TryReconstructionTranslationCandidate.lean` | 80% | All 5 Wightman property theorems | `phi4_linear_growth`, `phi4_os4_weak_coupling` | WP5-6 |
| `TryTestFunTranslation.lean` | 50% | Translation temperate growth + antilipschitz + apply lemma | OS4-dependent decay probe | WP6 |
| `TryRegularityCandidate.lean` | 0% | Statements only (structure skeleton) | All 5 theorems (deep analysis) | WP5 |

### Already Ported to Production (Archive)

These scratch files have served their purpose — their results are in core modules:
- `TryReconstructionSorrys.lean` → ported to `Reconstruction.lean`
- `TryWightmanInterfaces.lean` → ported to `Reconstruction.lean`
- `TryReflectionPositivitySorrys.lean` → interface pattern in `ReflectionPositivity.lean`

---

## 16. Definition Soundness Audit Results

A thorough audit of all core Phi4 definitions found **no issues**:

### `.choose` Usage — All Legitimate

| Location | Context | Verdict |
|----------|---------|---------|
| `Reconstruction.lean:137-143` | Extracting weak-coupling threshold from `∃` in instance | Sound |
| `InfiniteVolumeLimit.lean:920-924` | Extracting limit values from convergence hypothesis in frontier gap | Sound |
| `Combinatorics/PerfectMatchings.lean:151` | Extracting unique covering pair from pairing structure | Sound (with uniqueness proof) |

### `if h : 0 < n then ... else 0` Patterns — All in Limit Contexts

These appear in `Regularity.lean`, `InfiniteVolumeLimit.lean`, and `Interaction.lean`. In every case:
- They are in `Filter.Tendsto` statements (not definitions)
- The `else 0` branch is at `n = 0` or `κ ≤ 0`, which is filtered out by `Filter.atTop`
- This is the correct Lean pattern for dependent types in limit arguments

### Central Definitions — All Rigorous

- `schwingerN`: Direct integral ∫ ∏ᵢ ω(fᵢ) dμ_Λ — no guards, no defaults
- `infiniteVolumeSchwinger`: Pure delegation to model instance — no embedded choice
- `interaction`: `Filter.limsup` of UV-cutoff sequence — proper analytical definition
- `finiteVolumeMeasure`: Z_Λ⁻¹ exp(-V_Λ) dφ_C — standard construction

### No Hidden Issues Found

- Zero `Classical.choice` / `Classical.arbitrary` in definitions
- Zero problematic `Inhabited` instances
- Zero `default` / `⊥` values in mathematical definitions
- Zero `noncomputable def` with sorry or choice in body

---

## 17. Model Class Architecture Observations

### Vacuous Satisfaction Risk (Minor)

`MultipleReflectionModel` bundles 4 independent assumptions:
1. `chessboard_estimate` (Theorem 10.5.3)
2. `schwinger_uniform_bound` (uniform in Λ)
3. `determinant_bound` (entropy factor)
4. `partition_function_ratio_bound` (Z₁/Z₂ control)

These come from **different parts** of Glimm-Jaffe Chapter 10 and could theoretically be satisfied independently. Consider splitting into `ChessboardEstimateModel` + `SchwingerUniformBoundModel` if finer-grained dependency tracking is needed. However, the current bundling reflects the chapter structure and is acceptable.

### Moment-Distribution Bridge (Verified Sound)

The project uses both:
- `infiniteVolumeSchwinger` (ℝ-valued moments)
- `phi4SchwingerFunctions` (ℂ-valued distributions via `SchwingerFunctions 1`)

The bridge is correctly established through the measure representation:
```
infiniteVolumeSchwinger k f = ∫ ω, (∏ i, ω (f i)) ∂infiniteVolumeMeasure
```
No type-mismatch risk here.

### Instance Priority Scheme

The project uses a clean priority scheme:
- Priority 100: Standard compatibility instances (e.g., `correlationTwoPointModel_of_full`)
- Priority 90: Derived instances (e.g., `reconstructionWeakCouplingModel_of_uniform`)

No diamond-inheritance conflicts or typeclass resolution ambiguities detected.

---

## 18. Risk Register (Expanded)

| Risk | Severity | Mitigation |
|------|----------|------------|
| OSReconstruction has 185 sorrys; `os_to_wightman_full` is not axiom-clean | **HIGH** | Treat `WightmanReconstructionModel` as explicit input; do not commit `ReconstructionUpstream.lean` until upstream cleans up |
| `exp_interaction_Lp` (Thm 8.6.2) is the single hardest analytic proof | **HIGH** | Break into 4 sub-steps (semiboundedness ✓, localized graph bounds, tail estimate, layer-cake); develop infrastructure files |
| Theorem 11.3.1 (uniform bound) requires multiple reflection steps + per-square Lᵖ estimates | **HIGH** | Depends on WP1; develop chessboard infrastructure separately |
| Bochner-Minlos theorem likely not in Mathlib | **MEDIUM** | May need custom development in `Phi4/` or request from upstream GaussianField |
| Cluster expansion (OS4) is most technically demanding single step | **MEDIUM** | Only needed for weak-coupling regime; can be deferred after OS0-OS3 are proved |
| Upstream dependency drift on `main` branches | **LOW** | Pin commits in `lake-manifest.json`; verify build after any `lake update` |
| GaussianField heat kernel axioms (58) are unproved | **LOW** | Standard mathematical axiomatization; not a Phi4 proof gap |
| 93 scratch files accumulating | **LOW** | Archive completed probes; keep only active development files |

---

## 19. Concrete First-Session Checklist for Codex

When starting a new session, do these in order:

1. **Read** `TODO.md`, `Phi4/GAPS.md`, `Phi4/AUDIT.md` for current state
2. **Run** `scripts/check_phi4_trust.sh` to verify project health
3. **Check** `grep -RIn "^[[:space:]]*sorry\b" Phi4 --include='*.lean' | grep -v Scratch` for core sorry count
4. **Pick** the highest-priority WP task from Section 5 that is not blocked
5. **Work in scratch first**: Create `Phi4/Scratch/TryYourTask.lean`, compile, then port
6. **Update** `TODO.md` and relevant `ProofIdeas/` file with progress
7. **Run** trust audit again before committing

### Build Commands Quick Reference

```bash
# Build specific module
lake build Phi4.InfiniteVolumeLimit

# Compile a scratch file
lake env lean Phi4/Scratch/TryFoo.lean

# Trust audit
scripts/check_phi4_trust.sh

# Check sorry inventory
grep -RIn "^[[:space:]]*sorry\b" Phi4 --include='*.lean'

# Check axiom declarations
rg -n "^\s*axiom\b" Phi4 --glob '*.lean'

# Check model class count
rg -n "^class .*Model" Phi4 --glob '*.lean' | wc -l
```

---

# Critical Project Review — 2026-02-27 (Late Session)

**From**: Claude Code (comprehensive review)
**To**: Codex agent

---

## 0. Executive Summary

The project is in excellent structural health but has a **growing interface surface problem**. Since the last comprehensive review, the model class count has grown from **37 → 58** (a 57% increase) while the core sorry count dropped to **0**. The independent proof obligation count (bundle fields) grew modestly from ~37 to **42**. Recent commits have been almost exclusively **architectural refactoring** — splitting monolithic interfaces into atomic subinterfaces — rather than mathematical progress on grounding any interface with constructive proofs.

**Critical finding**: The last ~30 commits contain **zero mathematical progress** toward closing any interface with an actual proof. All changes are structural (splitting, threading, tightening assumptions). This is an anti-pattern flagged in Section 10 of the original recommendations.

---

## 1. Updated Health Metrics

| Metric | Old Value | Current Value | Change |
|--------|-----------|---------------|--------|
| Core sorry count | 9 | 0 | ↓ (sorrys moved to gap_ frontiers + interfaces) |
| Scratch sorry count | 16 | 0 | ↓ (all cleared) |
| Axiom declarations | 0 | 0 | — |
| def/abbrev-level sorry | 0 | 0 | — |
| Model classes (total) | 37 | **58** | **+21 (+57%)** |
| Bundle fields (independent obligations) | ~37 | **42** | +5 |
| Theorem-level gap_ frontiers | 9 | **9** | — (unchanged) |
| Core Lean files | ~21 | 21 | — |
| Scratch files | ~93 | **95** | +2 |
| Build status | ✓ | ✓ | — |
| Trust audit | ✓ | ✓ | — |

### The 9 Theorem-Level Frontiers (Unchanged)

| Gap | File |
|-----|------|
| `gap_infiniteVolumeSchwingerModel_nonempty` | InfiniteVolumeLimit.lean |
| `gap_generating_functional_bound` | Regularity.lean |
| `gap_generating_functional_bound_uniform` | Regularity.lean |
| `gap_nonlocal_phi4_bound` | Regularity.lean |
| `gap_osaCoreModel_nonempty` | OSAxioms.lean |
| `gap_osDistributionE2_nonempty` | OSAxioms.lean |
| `gap_osE4Cluster_nonempty` | OSAxioms.lean |
| `gap_phi4_linear_growth` | Reconstruction.lean |
| `gap_phi4_wightman_reconstruction_step` | Reconstruction.lean |

**None of these gaps have been closed or materially advanced since the last review.**

---

## 2. Critical Finding: Interface Proliferation Without Mathematical Progress

### The 21 New Model Classes

The 58 model classes break down into the original ~37 plus 21 new ones:

**From CorrelationInequalities.lean (+8):**
- `SchwingerNMonotoneModel` (generic k-point monotonicity)
- `SchwingerNNonnegModel` (generic k-point nonnegativity)
- `SchwingerNMonotoneFamilyModel` (family-level monotonicity)
- `CorrelationGKSSecondModel` (atomic GKS-II, split from CorrelationFourPointModel)
- `CorrelationLebowitzModel` (atomic Lebowitz, split from CorrelationFourPointModel)
- `CorrelationFourPointInequalityModel` (GKS-II + Lebowitz without monotonicity)
- `LatticeSchwingerNMonotoneModel` (lattice generic k-point)
- `LatticeSchwingerNMonotoneFamilyModel` (lattice family)

**From Regularity.lean (+5):**
- `WickCubicConvergenceModel` (split from RegularityModel)
- `EuclideanEquationModel` (split from RegularityModel)
- `GeneratingFunctionalBoundModel` (split from RegularityModel)
- `NonlocalPhi4BoundModel` (split from RegularityModel)
- `UniformGeneratingFunctionalBoundModel` (split from RegularityModel)

**From OSAxioms.lean (+4):**
- `SchwingerFunctionModel` (split from OSAxiomCoreModel)
- `OSTemperedModel` (split from OSAxiomCoreModel)
- `OSEuclideanCovarianceModel` (split from OSAxiomCoreModel)
- `OSE3SymmetryModel` (split from OSAxiomCoreModel)

**From InfiniteVolumeLimit.lean (+3):**
- `SchwingerUniformBoundModel`
- `SchwingerLimitModel`
- `InfiniteVolumeMomentModel` (split from InfiniteVolumeMeasureModel)

**From FiniteVolumeMeasure.lean (+1):**
- `FiniteVolumeComparisonModel`

### Assessment

Most splits are **architecturally defensible** — they reduce assumption surfaces on individual theorems and allow finer-grained grounding. However:

1. **The splitting does NOT reduce total proof debt.** The bundle still has 42 independent fields that each need constructive grounding.
2. **It creates combinatorial complexity in the instance lattice.** CorrelationInequalities.lean alone now has 15 class declarations and ~30 constructor/compatibility instances. This makes the instance resolution path harder to audit.
3. **Anti-pattern match**: The original review (Section 10, item 2) warned "Do NOT create wrapper/forwarding theorems that don't reduce sorry count." The same principle applies to interfaces: splitting an interface that has zero constructive progress is organizational churn, not mathematical progress.

**Recommendation**: **Freeze interface refactoring.** No more class splitting until at least one interface from the current 42 bundle fields is discharged with a constructive proof. Every hour spent splitting is an hour not spent on WP1 (the critical blocker).

---

## 3. Soundness Findings

### 3.1 No New Soundness Issues Found

- **Zero axiom smuggling**: All `.choose` uses are properly scoped inside theorem constructors with `.choose_spec` proof obligations.
- **Zero definition-level placeholders**: All `noncomputable def` are delegation or standard construction.
- **Zero circular instances**: Instance priority scheme (100 for extraction, 90 for derived) prevents diamonds.
- **Zero type-level mismatches**: Build succeeds cleanly.

### 3.2 Minor Concern: `.choose` in `ReconstructionWeakCouplingModel`

[Reconstruction.lean:134-135](Phi4/Reconstruction.lean#L134-L135): The `weak_coupling_threshold` is extracted via `.choose` from a `UniformWeakCouplingDecayModel` existential. This is mathematically sound (the threshold is existentially quantified and the properties are extracted via `.choose_spec`), but it makes the threshold non-canonical. If two different uniform decay models yield different thresholds, they cannot be compared. This is acceptable for now but should be documented.

### 3.3 Bundle Completeness Audit

The bundle carries 42 fields but does **not** include:
- `InteractionIntegrabilityModel` (reconstructed from `InteractionWeightModel` + `InteractionUVModel`)
- `InteractionUVModel` (reconstructed from `InteractionIntegrabilityModel`)
- `PairingEnumerationModel`, `GaussianWickExpansionModel`, `FeynmanGraphEstimateModel` (Feynman graph infrastructure)
- `LatticeGriffithsFirstModel`, `LatticeSchwingerTwoMonotoneModel` (lattice bridge models)
- `CorrelationInequalityModel`, `CorrelationInequalityCoreModel` (reconstructed from atomic pieces)
- `BoundaryCovarianceModel` (reconstructed from boundary submodels)
- `InfiniteVolumeLimitModel` (reconstructed from Schwinger + measure + moment submodels)
- `RegularityModel` (reconstructed from regularity submodels)
- `ReconstructionInputModel`, `ReconstructionWeakCouplingModel` (reconstructed)

These are either reconstructed via compatibility instances or are Feynman graph infrastructure not yet needed at the bundle level. This is architecturally correct.

---

## 4. Scratch Files Status

- **95 scratch files** total
- **2 files with `sorry` references** (both in comments/documentation, not theorem-level)
- **0 axiom declarations**
- **Key candidate files for porting** (complete proofs, not yet in production):
  - `TryMultipleReflectionsSorrys.lean` — partition function ratio bounds (LOW effort to port)
  - `TryReconstructionTranslationCandidate.lean` — 5 Wightman property theorems (80% done)
  - `TryFeynmanGraphIntegralCandidate.lean` — graph/integral combinatorics (4 complete theorems)
  - `TryInteractionCandidate.lean` — interaction term theorems (20% done)

---

## 5. ProofIdeas Status

All 9 ProofIdeas files are **internally consistent** and aligned with the current codebase. No contradictions found. Minor staleness:
- `WickProduct_FreeField_sorrys.md` is fully resolved (all targets closed)
- Ch10/11 doesn't reflect the new atomic four-point decomposition naming
- Ch12 doesn't reference the new regularity subinterfaces

**Key strategic insight from ProofIdeas still applicable**: The three-layer proof architecture (Ch 8 → Ch 10-11 → Ch 12) remains the correct approach. **Theorem 8.5.5 (localized graph bounds)** is the single most important frontier result — it feeds into interaction integrability (WP1), multiple reflections (WP4), and regularity (WP5).

---

## 6. Updated Work Package Priorities

The priority ordering from the original review remains correct. **Nothing has changed about the critical path**:

### WP1: Interaction Integrability — STILL THE CRITICAL BLOCKER

**Progress since last review**: Infrastructure additions only:
- `FeynmanGraphs/LocalizedBounds.lean`: factorial occupancy bounds
- `Interaction.lean`: measure-theoretic bridge lemmas, Borel-Cantelli bridges, geometric/exponential tail specializations
- These are useful **stepping stones** but the core proof `exp_interaction_Lp` is still ungrounded

**What's actually needed**:
1. Localized graph bound (Theorem 8.5.5) — per-square factorization with exponential decay
2. Tail estimate for UV cutoff interaction
3. Layer-cake integration
4. Assembly into `exp_interaction_Lp`

### WP2: Covariance/Boundary — No Progress

Constructor scaffolds were added but no constructive proofs landed.

### WP3: Correlation Inequalities — No Progress

Constructor scaffolds and atomic decomposition were added but no lattice-to-continuum proofs landed.

### WP4-WP6: Blocked by WP1-WP3

---

## 7. Revised Recommendations for Codex

### IMMEDIATE (Start Now)

1. **STOP interface refactoring.** The 58-class / 42-field architecture is mature enough. Every additional split without a matching constructive proof is negative ROI.

2. **Port scratch results to production.** Quick wins:
   - `TryMultipleReflectionsSorrys.lean` → `MultipleReflections.lean` (partition function ratio bounds)
   - These are complete, sorry-free proofs that directly support WP4.

3. **Start the Theorem 8.5.5 proof** (localized graph bounds). This is the single highest-value task in the project. Work in `Phi4/Scratch/TryLocalizedGraphBound.lean`, compile frequently, and port when ready.

### SHORT-TERM

4. **Ground `FreeCovarianceKernelModel`** — bridge CLM covariance to Green kernel representation. Infrastructure is ready in `FreeField.lean`.

5. **Ground `BoundaryComparisonModel`** — prove C_D ≤ C ≤ C_N. Infrastructure is ready in `CovarianceOperators.lean` and `Bessel/`.

6. **Ground `LatticeGriffithsFirstModel`** — lattice GKS-I to continuum via existing bridge lemmas in `CorrelationInequalities.lean`.

### MEDIUM-TERM

7. **Assemble `exp_interaction_Lp`** from localized graph bounds + tail estimates + layer-cake (WP1 core).

8. **Prove chessboard estimate** (WP4, after WP1).

### ANTI-PATTERNS TO AVOID

- **No more class splitting** without a matching constructive proof
- **No more constructor scaffolds** (`*_nonempty_of_data` theorems) without actual data to feed them
- **No more wrapper/forwarding theorems** that don't reduce the 42-field obligation count
- **Focus on bottom-up grounding**, not top-down packaging

---

## 8. Updated Risk Register

| Risk | Severity | Change | Notes |
|------|----------|--------|-------|
| Interface proliferation without grounding | **HIGH** | **NEW** | 58 classes, 42 bundle fields, 0 constructively grounded since last review |
| `exp_interaction_Lp` unproved (Thm 8.6.2) | **HIGH** | Unchanged | Still the critical blocker |
| Theorem 11.3.1 (uniform bound) | **HIGH** | Unchanged | Hardest single estimate |
| Upstream OSReconstruction (185 sorrys) | **HIGH** | Unchanged | Isolated in ReconstructionUpstream.lean |
| Instance resolution complexity | **MEDIUM** | **NEW** | 15 classes + ~30 instances in CorrelationInequalities alone |
| Cluster expansion (OS4) | **MEDIUM** | Unchanged | Most technically demanding step |
| Bochner-Minlos not in Mathlib | **MEDIUM** | Unchanged | May need custom development |
| 95 scratch files accumulating | **LOW** | Slightly worse | +2 since last review |
| ProofIdeas slightly stale | **LOW** | **NEW** | Recent atomic decomposition not reflected |

---

## 9. Stale Documentation Items

The following numbers in the existing sections above (Sections 1-18) are now stale:

| Section | Stale Item | Old Value | Current Value |
|---------|-----------|-----------|---------------|
| §1 | Core sorry count | 9 | 0 (moved to gap_ + interfaces) |
| §1 | Scratch sorry count | 16 | 0 |
| §1 | Model classes | 38 (37+1) | 58 |
| §3 | "The 9 Core Frontier Gaps" | 9 sorrys | 9 gap_ theorems (same math, different encoding) |
| §4 | "37 Assumption Interfaces" | 37 | 58 classes, 42 bundle fields |
| §16 | AUDIT.md class count | 38 | 58 |

**The mathematical content and recommended approaches in Sections 5-11 remain fully valid.**

---

## 10. Bottom Line

The project architecture is **sound and mature**. The trust infrastructure is **working correctly**. But recent development has been **overwhelmingly structural** rather than mathematical. The critical path is unchanged: **WP1 (interaction integrability) is the blocker**, and **Theorem 8.5.5 (localized graph bounds)** is the specific next proof target. Every development cycle should be measured against: "Did this reduce the 42-field bundle obligation count?"

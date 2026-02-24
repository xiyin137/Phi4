# Development Plan: phi^4_2 QFT Formalization

## Status: ~83 sorries across 14 files, ~11 proven theorems

## Available Infrastructure

### From GaussianField dependency
- `GaussianField.measure T` -- Gaussian probability measure on `WeakDual R E`
- `GaussianField.charFun` -- characteristic functional E[exp(i omega f)] = exp(-1/2 ||Tf||^2)
- `GaussianField.measure_centered`, `cross_moment_eq_covariance` -- proven
- `GaussianField.wick_recursive`, `wick_bound`, `wick_bound_factorial` -- Wick's theorem (proven)
- `GaussianField.odd_moment_vanish` -- proven
- `GaussianField.pairing_memLp` -- all finite moments exist (Fernique, proven)
- `GaussianField.spectralCLM` -- multiplier CLM for DyninMityaginSpace (axiom)
- `DyninMityaginSpace (SchwartzMap D R)` -- instance proven via Hermite basis

### From OSReconstruction dependency
- `OsterwalderSchraderAxioms d` -- target structure (OS0-OS4)
- `WightmanQFT d` -- Wightman axiom structure
- `os_to_wightman` -- OS reconstruction theorem (proven)
- `WightmanFunctions d`, `wightman_reconstruction` -- Wightman reconstruction (proven)
- SCV toolkit: edge-of-wedge, Osgood, tube domains, Bargmann-Hall-Wightman
- vNA infrastructure: spectral theorem, unbounded operators, Stone's theorem
- Lorentz/Poincare groups, representations, covariance

### From Phi4 (already proven)
- `Defs.lean` -- All clean (no sorries): Spacetime2D, TestFun2D, FieldConfig2D, Phi4Params, Rectangle, UVCutoff
- `freeEigenvalue_pos` -- proven
- `Rectangle.area_pos` -- proven
- `freeFieldMeasure_isProbability` -- proven (uses GaussianField)
- `freeField_centered` -- proven (uses GaussianField)
- `freeField_two_point` -- proven (uses GaussianField)
- `freeField_pairing_memLp` -- proven (uses GaussianField)
- `pos_time_half_exists` (MultipleReflections.lean) -- proven

---

## Phase 1: Foundational Infrastructure (Free Field + Covariance)

### Priority: CRITICAL -- blocks everything downstream

### 1A. Free Covariance CLM (FreeField.lean)
**Goal:** Construct `freeCovarianceCLM : TestFun2D ->L[R] ell2'`

**Approach:** Use `GaussianField.spectralCLM` with the `freeSingularValue` sequence.
Need to prove `IsBoundedSeq (freeSingularValue mass)`.

**Tasks:**
- [ ] `free_singular_values_summable` -- show Sigma sigma_m < infinity
  - Eigenvalues grow linearly: lambda_m ~ m, so sigma_m ~ m^{-1/2}, and Sigma m^{-1/2} diverges...
  - **ISSUE:** The summability of sigma_m = lambda_m^{-1/2} is needed for nuclear trace class.
    In d=2 with harmonic oscillator basis, eigenvalues are ~ (2n1+1) + (2n2+1) + m^2.
    The number of eigenvalues <= N is ~ N, so sigma_m^2 = lambda_m^{-1} ~ 1/m,
    and Sigma 1/m diverges! But we need Sigma sigma_m^2 < infinity for Hilbert-Schmidt, not summability of sigma_m.
  - **Resolution:** Check what `spectralCLM` actually requires. It uses `IsBoundedSeq`, not summability.
    The Gaussian measure construction uses pushforward from product measure, which works for any bounded sequence.
    Summability may not be needed. Re-examine the interface.
- [ ] `free_singular_values_bounded` -- show |sigma_m| <= C. This is straightforward since lambda_m >= m^2 > 0.
- [ ] `freeCovarianceCLM` -- apply `spectralCLM` with the bounded sequence

**Dependencies:** None (foundational)
**Blocks:** Everything in WickProduct, FeynmanGraphs, Interaction, and downstream

### 1B. Free Covariance Kernel (FreeField.lean)
**Goal:** Define the pointwise kernel C(x,y) and its properties

**Approach:** C(x,y) = (2pi)^{-1} K_0(m|x-y|) in d=2. Can define via the integral representation:
C(x,y) = integral_0^infty (4 pi t)^{-1} exp(-|x-y|^2/(4t) - m^2 t) dt

**Tasks:**
- [ ] `freeCovKernel` -- define via integral representation or Bessel function
- [ ] `freeCovKernel_symm` -- symmetry of the kernel (immediate from definition)
- [ ] `freeCovKernel_pos_def` -- positive definiteness. Use Fourier representation: C_hat(p) = (p^2+m^2)^{-1} > 0
- [ ] `regularizedPointCovariance` -- define c_kappa(x) = integral delta_kappa(x-y) C(x,y') delta_kappa(x-y') dy dy'
- [ ] `regularizedPointCovariance_log_divergence` -- the key d=2 fact: c_kappa ~ (2pi)^{-1} ln kappa

**Dependencies:** None
**Blocks:** WickProduct (Wick ordering constants), Interaction (semiboundedness), CovarianceOperators

### 1C. Covariance Operators with Boundary Conditions (CovarianceOperators.lean)
**Goal:** Dirichlet/Neumann/Periodic covariances and the ordering C_D <= C <= C_N

**Approach:**
- Dirichlet: define via variational characterization (-Delta_D + m^2)^{-1} as resolvent of Friedrichs extension
- Neumann: similarly, with Neumann BC
- Ordering: form domain argument (D(-Delta_D) subset D(-Delta) subset D(-Delta_N))

**Tasks:**
- [ ] `dirichletCov` -- define Dirichlet Green's function
- [ ] `neumannCov` -- define Neumann Green's function
- [ ] `periodicCov` -- define periodic covariance (Fourier series)
- [ ] `dirichlet_le_free` -- C_D <= C (form domain inclusion)
- [ ] `free_le_neumann` -- C <= C_N (form domain inclusion)
- [ ] `dirichlet_monotone` -- C_{Lambda_1}^D <= C_{Lambda_2}^D for Lambda_1 subset Lambda_2
- [ ] `covarianceChange_pointwise_bounded` -- |delta c(x)| <= const in d=2
- [ ] `dirichletCov_smooth_off_diagonal` -- elliptic regularity
- [ ] `freeCov_exponential_decay` -- |C(x,y)| <= C1 * exp(-C2 * |x-y|) for |x-y| >= 1

**Dependencies:** 1B (freeCovKernel)
**Blocks:** ReflectionPositivity, CorrelationInequalities, MultipleReflections, InfiniteVolumeLimit

---

## Phase 2: Wick Products and Feynman Graphs

### Priority: HIGH -- needed for the interaction

### 2A. Wick Products (WickProduct.lean)
**Goal:** Define :phi^n:_C and prove basic properties

**Tasks:**
- [ ] `hermitePoly` -- extend to general n (currently cases 0-4 defined)
- [ ] `rawFieldEval` -- define phi_kappa(x) = omega(delta_{kappa,x}) as a measurable function
- [ ] `wickPower` -- define :phi^n:_C = He_n(phi_kappa(x), c_kappa(x))
- [ ] `wickFourth` -- verify :phi^4: = phi^4 - 6c phi^2 + 3c^2
- [ ] `wickPower_zero_expectation` -- E[:phi^n:] = 0 from Hermite orthogonality
- [ ] `wickPower_memLp` -- :phi^n: in L^p for all p < infinity (GJ Thm 8.5.3)
- [ ] `rewick_fourth` -- re-Wick-ordering formula (GJ 8.6.1)
- [ ] `rewick_ordering_bounds` -- quantitative bounds on re-Wick-ordered terms

**Dependencies:** 1A (freeCovarianceCLM), 1B (regularizedPointCovariance)
**Blocks:** Interaction

### 2B. Feynman Graphs (FeynmanGraphs.lean)
**Goal:** Wick's theorem and localized graph bounds

**Tasks:**
- [ ] `num_pairings` -- (2n-1)!! counting (pure combinatorics)
- [ ] `wicks_theorem_even` -- even moments = sum over pairings
  - Can use `GaussianField.wick_recursive` from the dependency!
- [ ] `wicks_theorem_odd` -- odd moments vanish
  - Can use `GaussianField.odd_moment_vanish`!
- [ ] `graphIntegral` -- define Feynman graph integral I(G)
- [ ] `feynman_graph_expansion` -- integral = sum of graph integrals
- [ ] `localized_graph_bound` -- |I(G)| <= prod_Delta N(Delta)! (const m^{-1/q})^{N(Delta)}

**Dependencies:** 2A (wickPower), 1C (freeCov_exponential_decay)
**Blocks:** Interaction (exp_interaction_Lp)

---

## Phase 3: Interaction and Finite Volume Measure

### Priority: HIGH -- the central estimates

### 3A. Interaction (Interaction.lean)
**Goal:** V_Lambda = lambda integral_Lambda :phi^4: dx, and e^{-V} in L^p

**Tasks:**
- [ ] `interactionCutoff` -- define V_{Lambda,kappa}
- [ ] `interaction` -- UV limit V_Lambda = lim_{kappa -> infty} V_{Lambda,kappa}
- [ ] `wick_fourth_semibounded` -- :phi^4_kappa: >= -6 c_kappa^2 = -O((ln kappa)^2)
- [ ] `wick_fourth_lower_bound_explicit` -- explicit (phi^2 - 3c)^2 - 6c^2 computation
- [ ] `interactionCutoff_in_L2` -- V_{Lambda,kappa} in L^2, uniform in kappa
- [ ] `interactionCutoff_converges_L2` -- L^2 convergence as kappa -> infty
- [ ] `interaction_in_L2` -- V_Lambda in L^2
- [ ] `exp_interaction_Lp` -- **THE KEY ESTIMATE**: e^{-V} in L^p for all p < infty (GJ Thm 8.6.2)
  - Two-step proof: semiboundedness + small bad set + layer-cake
- [ ] `partition_function_pos` -- Z_Lambda = integral e^{-V} > 0
- [ ] `partition_function_integrable` -- Z_Lambda < infty

**Dependencies:** 2A, 2B, 1B (log divergence), 1C (covariance bounds)
**Blocks:** FiniteVolumeMeasure, everything downstream

### 3B. Finite Volume Measure (FiniteVolumeMeasure.lean)
**Goal:** d mu_Lambda = Z^{-1} e^{-V} d phi_C and Schwinger functions

**Tasks:**
- [ ] `finiteVolumeMeasure_isProbability` -- normalization
- [ ] `schwingerN_perm` -- permutation symmetry of Schwinger functions
- [ ] `schwingerN_multilinear` -- multilinearity
- [ ] `schwingerTwo_le_free` -- S_2 <= C (from Lebowitz inequality)

**Dependencies:** 3A (partition_function_pos, partition_function_integrable)
**Blocks:** CorrelationInequalities, ReflectionPositivity

---

## Phase 4: Correlation Inequalities and Reflection Positivity

### Priority: HIGH -- needed for infinite volume limit

### 4A. Correlation Inequalities (CorrelationInequalities.lean)
**Goal:** GKS-I, GKS-II, FKG, Lebowitz for continuum phi^4_2

**Approach:** These are proved on the lattice (Ch 4) and extended to continuum via lattice approximation (Ch 9).
Consider: can we state these as properties of the finite volume measure and prove via lattice approx?

**Tasks:**
- [ ] `griffiths_first` -- GKS-I: <phi(f) phi(g)> >= 0 for f,g >= 0
- [ ] `griffiths_second` -- GKS-II: <phi_A phi_B> - <phi_A><phi_B> >= 0
  - This is THE cornerstone of monotone convergence
- [ ] `fkg_inequality` -- FKG: <F><G> <= <FG> for monotone F,G
- [ ] `lebowitz_inequality` -- Lebowitz: U_4 <= 0
- [ ] `schwinger_two_monotone` -- S_2^{Lambda_1} <= S_2^{Lambda_2} for Lambda_1 subset Lambda_2

**Dependencies:** 3B (finite volume measure), 1C (Dirichlet monotonicity)
**Blocks:** InfiniteVolumeLimit (monotonicity argument)

### 4B. Reflection Positivity (ReflectionPositivity.lean)
**Goal:** OS3 for free and interacting measures

**Tasks:**
- [ ] `testFunTimeReflect` -- time reflection theta on test functions
- [ ] `free_covariance_reflection_positive` -- RP of C (GJ Thm 7.10.1)
  - Key: RP <=> C_D <= C, which is `dirichlet_le_free`
- [ ] `dirichlet_covariance_reflection_positive` -- RP of C_D
- [ ] `interacting_measure_reflection_positive` -- RP of d mu_Lambda (GJ Thm 10.4.3)
  - Proof: V = V_+ + theta V_+, then use RP of d phi_C

**Dependencies:** 1C (dirichlet_le_free), 3B (finite volume measure)
**Blocks:** MultipleReflections, InfiniteVolumeLimit (OS3)

---

## Phase 5: Multiple Reflections and Infinite Volume Limit

### Priority: HIGH -- constructs the infinite volume theory

### 5A. Multiple Reflections (MultipleReflections.lean)
**Goal:** Chessboard/iterated Schwarz estimates, uniform bounds

**Tasks:**
- [ ] `chessboard_estimate` -- |integral prod A_i d mu|^{2^d} <= integral R(A) d mu
  - Iterated RP + Schwarz inequality
- [ ] `determinant_bound` -- Z_+^2 / Z <= exp(O(|Lambda|))
- [ ] `schwinger_uniform_bound` -- |S_n^Lambda| <= C uniformly in Lambda
- [ ] `partition_function_ratio_bound` -- Z_{Lambda_1}/Z_{Lambda_2} <= exp(C |Lambda_2|)

**Dependencies:** 4B (RP), 3A (exp_interaction_Lp for unit cube estimates)
**Blocks:** InfiniteVolumeLimit (uniform upper bound)

### 5B. Infinite Volume Limit (InfiniteVolumeLimit.lean)
**Goal:** S{f} = lim_{Lambda -> R^2} S_Lambda{f} exists, satisfying OS0, OS2, OS3

**Tasks:**
- [ ] `schwinger_monotone_in_volume` -- S_2^{Lambda_n} monotone increasing
  - Uses GKS-II + Dirichlet monotonicity
- [ ] `schwingerN_monotone_in_volume` -- n-point version
- [ ] `schwinger_uniformly_bounded` -- |S_n^Lambda| <= C (multiple reflections)
- [ ] `infinite_volume_schwinger_exists` -- monotone bounded => convergent
- [ ] `infiniteVolumeMeasure` -- construct the infinite volume measure (Bochner-Minlos / tightness)
- [ ] `infiniteVolumeMeasure_isProbability` -- it's a probability measure
- [ ] `infiniteVolumeSchwinger_is_moment` -- Schwinger functions are moments of the measure

**Dependencies:** 4A (GKS-II for monotonicity), 5A (uniform bound)
**Blocks:** Regularity, OSAxioms

---

## Phase 6: Regularity (OS1)

### Priority: HIGH -- the most analytically demanding

### 6A. Regularity (Regularity.lean)
**Goal:** |S{f}| <= exp(c(||f||_{L^1} + ||f||_{L^p}^p)) -- OS1 axiom

**Tasks:**
- [ ] `wick_powers_infinite_volume` -- :phi^j: exists in L^2(d mu)
- [ ] `wickCubicSmeared` -- integral :phi^3: f dx as a functional
- [ ] `euclidean_equation_of_motion` -- Schwinger-Dyson / integration by parts identity
- [ ] `normFunctional` -- define N'(f) = Sigma ||g_j||_{L^{n/(n-j)}}
- [ ] `nonlocal_phi4_bound` -- |S_Lambda{g}| <= exp(C_1 |Lambda| + C_2)
- [ ] `generating_functional_bound_uniform` -- eliminate Lambda-dependence via asymmetric reflections
- [ ] `generating_functional_bound` -- THE MAIN REGULARITY THEOREM (GJ Thm 12.5.1)

**Dependencies:** 5B (infinite volume measure), 5A (multiple reflections), 1C (exponential decay of C)
**Blocks:** OSAxioms

---

## Phase 7: OS Axioms and Reconstruction

### Priority: MEDIUM (once Phase 6 is done, these are mostly assembly)

### 7A. OS Axioms (OSAxioms.lean)
**Goal:** Verify OS0-OS3 for the infinite volume Schwinger functions

**Tasks:**
- [ ] `phi4SchwingerFunctions` -- package as SchwingerFunctions structure
- [ ] `phi4_os0` -- OS0 (analyticity/temperedness)
- [ ] `phi4_os2_translation` -- translation invariance
- [ ] `phi4_os2_rotation` -- rotation invariance
- [ ] `phi4_os3` -- reflection positivity (from RP preserved under limits)
- [ ] `phi4_satisfies_OS` -- bundle OS0-OS3

**Dependencies:** 5B (infinite volume), 6A (regularity for OS1)
**Blocks:** Reconstruction

### 7B. Reconstruction (Reconstruction.lean)
**Goal:** OS -> Wightman via the reconstruction theorem

**Tasks:**
- [ ] `phi4_linear_growth` -- linear growth condition for OS1'
- [ ] `phi4_os4_weak_coupling` -- OS4 (clustering) for weak coupling via cluster expansion
  - This is the hardest: needs the full cluster expansion machinery of GJ Ch 18
  - Consider: may need to state convergence of cluster expansion as a hypothesis initially
- [ ] `phi4_wightman_exists` -- apply `os_to_wightman` from OSReconstruction
- [ ] `phi4_unique_vacuum` -- uniqueness of vacuum from OS4
- [ ] `phi4_selfadjoint_fields` -- self-adjointness from GJ Thm 19.3.1
  - Uses vNA infrastructure from OSReconstruction
- [ ] `phi4_locality` -- spacelike commutativity from analytic continuation
  - Uses SCV toolkit from OSReconstruction
- [ ] `phi4_lorentz_covariance` -- Lorentz covariance from Euclidean rotation invariance

**Dependencies:** 7A (OS0-OS3), OSReconstruction (reconstruction theorem)
**Blocks:** Nothing (this is the final goal)

---

## Recommended Development Order

### Iteration 1: Build the foundation
1. **1A** -- `freeCovarianceCLM` (critical blocker)
2. **1B** -- `freeCovKernel` + log divergence
3. **1C** -- Dirichlet/Neumann covariances + ordering

### Iteration 2: Wick products and interaction
4. **2A** -- Wick products (:phi^n: definition and properties)
5. **2B** -- Feynman graphs (use GaussianField.wick_recursive)
6. **3A** -- Interaction (V_Lambda, semiboundedness, e^{-V} in L^p)
7. **3B** -- Finite volume measure

### Iteration 3: Inequalities and positivity
8. **4A** -- Correlation inequalities (GKS, FKG, Lebowitz)
9. **4B** -- Reflection positivity

### Iteration 4: Infinite volume
10. **5A** -- Multiple reflections / chessboard
11. **5B** -- Infinite volume limit

### Iteration 5: Regularity and axioms
12. **6A** -- Regularity (OS1)
13. **7A** -- OS axioms (OS0-OS3)
14. **7B** -- Reconstruction

---

## Difficulty Assessment

| Phase | Difficulty | Key Challenge |
|-------|-----------|---------------|
| 1A | Medium | Interface with spectralCLM axiom |
| 1B | Medium | Defining the kernel, proving log divergence |
| 1C | Hard | Dirichlet/Neumann need PDE infrastructure |
| 2A | Medium | Hermite polynomials, measurability |
| 2B | Medium | Graph combinatorics, localized bounds |
| 3A | Very Hard | e^{-V} in L^p is the central estimate (Thm 8.6.2) |
| 3B | Easy | Assembly from 3A |
| 4A | Hard | Lattice approximation + transfer of inequalities |
| 4B | Medium | Once C_D <= C is done, RP follows |
| 5A | Hard | Iterated Schwarz inequality, geometric arguments |
| 5B | Medium | Monotone convergence + Vitali's theorem |
| 6A | Very Hard | Integration by parts + exponential decay controls combinatorics |
| 7A | Easy | Assembly from previous phases |
| 7B | Hard | Cluster expansion for OS4; reconstruction is provided by dependency |

## Notes

- The GaussianField dependency provides crucial proven theorems (Wick's theorem, moment bounds, Gaussian measure construction). Leverage these maximally.
- The OSReconstruction dependency provides the reconstruction theorem itself. Once OS0-OS4 are verified, `os_to_wightman` gives us the Wightman QFT.
- The two hardest single estimates are `exp_interaction_Lp` (GJ Thm 8.6.2) and `generating_functional_bound` (GJ Thm 12.5.1). Everything else is either combinatorial, follows from these, or is provided by dependencies.
- The cluster expansion (for OS4) is the most complex piece of mathematical machinery. Consider initially treating OS4 as a hypothesis and focusing on OS0-OS3 + reconstruction.

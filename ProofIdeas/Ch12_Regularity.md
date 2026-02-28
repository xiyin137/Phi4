# Chapter 12: Regularity and Axioms -- OS1

## Status Snapshot (2026-02-27)

- `Regularity.lean` now has no theorem-level `sorry`.
- Chapter-12 obligations are represented explicitly by regularity subinterfaces:
  `WickCubicConvergenceModel`, `EuclideanEquationModel`,
  `GeneratingFunctionalBoundModel`, `NonlocalPhi4BoundModel`,
  and `UniformGeneratingFunctionalBoundModel` (recombining to
  `RegularityModel`).
- Upstream Chapter 8/10/11 analytic content is still the main constructive debt,
  but no longer tracked via local placeholders.
- Note: theorem names are the stable lookup key; line numbers can drift.

## Main Result

**Theorem 12.1.1 (Axioms).** The generating functional S{f} exists (Thm 11.2.1) and satisfies OS0-OS3. Hence it yields a Wightman QFT satisfying W1-W3.

Combines Theorem 11.2.1 (OS0, OS2, OS3) with Theorem 12.5.1 (OS1).

## 1. Integration by Parts / Schwinger-Dyson Equation (Section 12.2)

**Euclidean equation of motion:**
    (-Δ + m^2) ⟨φ(x) A(φ)⟩ + ⟨:P'(φ(x)): A(φ)⟩ = ⟨(δA/δφ)(x)⟩

After analytic continuation to Minkowski time:
    (-□ + m^2) φ(x) + P'(φ(x)) = 0

**Theorem 12.2.1:** :φ^j: = lim_{κ→∞} :φ_κ^j: exists in L^2(dμ), and UV/IR limits commute.

**Corollary 12.2.3 (Integration by parts):** For f ∈ C_0^∞:
    ∫ φ(f) A(φ) dμ = ∫ [(C_0 f, δA/δφ) - A(φ)(C_0 f, δV/δφ)] dμ

**Corollary 12.2.4 (Schwinger function bounds):** For g localized in unit squares:
    |∫ ∏_Δ ∏_i :φ^j(h_{Δ,i}): dμ| ≤ ∏_Δ (n_Δ!)^{1/p} ∏_i (c‖h_{Δ,i}‖_{L^p})

### Lean file mapping
- `wick_powers_infinite_volume` (Regularity.lean:46) -- Thm 12.2.1
- `wickCubicSmeared` (Regularity.lean:55) -- ∫:φ³:f dx
- `euclidean_equation_of_motion` (Regularity.lean:73) -- Cor. 12.2.3

### Proof strategy for euclidean_equation_of_motion
First prove in finite volume using the bounded case from Section 9.1:
    ∫ φ(f) A dμ_Λ = ∫ [(C_Λ f, δA/δφ) - A(C_Λ f, δV/δφ)] dμ_Λ
Then pass to infinite volume using Thm 12.2.1 (convergence of Wick powers in L^2).

## 2. Nonlocal φ^4 Bounds (Section 12.3)

Uses doubly cutoff field: φ_{κ,κ'} = b_{κ'} * φ_κ

**Proposition 12.3.1:** Semiboundedness of the rewritten interaction:
    -c ‖f_Λ‖_{L^1} (ln κ)^{deg P/2} + c(N(f) + N'(g)) ≤ :P(φ_{κ,κ'}): + :Q(φ_{κ,κ'}, g):

**Proposition 12.3.2:** Convergence in UV cutoff removal:
    ∫ exp(:Q(φ_κ,g) - Q(φ_{κ'},g):) dμ_Λ ≤ κ'^{-ε} M(g) exp(const(N(f)+N'(g)+1))

### Lean file mapping
- `nonlocal_phi4_bound` (Regularity.lean:113) -- Prop 12.3.1-2

### Proof idea
The double cutoff φ_{κ,κ'} allows separation of the interaction into a "main part" :P: and a "perturbation" :Q:. The perturbation Q arises from the nonlocal smearing and is controlled by the Gaussian estimates of Ch 8.5. The key estimate: ‖:Q: - :Q_κ':‖_{L_{2j}} ≤ (j!)^{n/2} (const κ'^{-ε})^j, optimized over j.

## 3. Uniformity in Volume (Section 12.4) -- THE KEY SECTION

**Goal:** Eliminate the |Λ| dependence from Theorem 12.2.2.

**Theorem 12.4.1:** For any rectangle K containing supp(g), there exists a subsequence Λ_ν → R^2 with:
    ∫ exp(:φ_κ^j(g):) dμ_{Λ_ν} ≤ exp(c{|K| + ‖g‖_{L^p}^p})
The bound depends on |K| (support of g), **NOT** |Λ|.

### Asymmetric multiple reflections proof strategy

1. Choose Λ_ν to be oblong rectangles (T >> L) with K at center.
2. Perform j_0 vertical reflections, then j_1 horizontal reflections.
3. After n reflections: exponent picks up factor 4^{-n}, region grows to 4^n|K|.
4. Bound determinant factors via Theorem 10.6.2: vertical reflections give O(1), horizontal give exp(O(|K|)).
5. Bound partition function ratios Z^{(j)}/Z^{(j+1)} using conditioning and spectral analysis: Z(t,l) ~ exp(-t E_l) as t → ∞, where E_l = inf spec(H_l).
6. Final cancellation gives exp(O(|K|)).

**Theorem 12.4.2 (Reflection bound tool):** For Λ an L × T rectangle:
    |∫ B dμ_Λ| ≤ exp(const |K|) · (∫ B^{(n)} dμ_{Λ^{(n)}})^{2^{-n}}

### Lean file mapping
- `generating_functional_bound_uniform` (Regularity.lean:124) -- Thm 12.4.1

### Proof idea
The proof uses the **non-symmetric** reflection method (Prop. 10.6.1). Unlike the symmetric reflections of Chapter 11 (which require P = even + linear), this method works for general P. The key new ingredient is the spectral analysis of the transfer matrix Hamiltonian H_l: Z(t,l) ~ exp(-t E_l) for large t, with the ground state energy E_l controlling the partition function ratios.

## 4. Regularity -- OS1 (Theorem 12.5.1)

**Theorem 12.5.1:** For P = even + linear, there exists c < ∞ such that for all f ∈ C_0^∞:
    S{-if} = ∫ exp(φ(f)) dμ ≤ exp(c(‖f‖_{L^1} + ‖f‖_{L^p}^p))
where p = n/(n-1) = 4/3 for φ^4.

### Proof outline

**Step 1: Large/small decomposition.** Write f = g + h where:
- g = sum over "large" unit squares (‖f‖_{L^1(Δ)} + ‖f‖_{L^p(Δ)}^p ≥ 1)
- h = sum over "small" unit squares

By Schwarz: ∫ e^{φ(f)} ≤ (∫ e^{φ(2g)} · ∫ e^{φ(2h)})^{1/2}

**Step 2: Large part.** Multiple reflections (Cor. 10.5.8 + Thm 12.4.1):
    |∫ e^{:φ^j(g):} dμ| ≤ ∏_Δ exp(c(1 + ‖g_Δ‖_{L^p}^p))
Number of large squares ≤ ‖f‖_{L^1} + ‖f‖_{L^p}^p.

**Step 3: Small part (heart of the proof).** For f = h with ‖f‖_{L^1(Δ)} + ‖f‖_{L^p(Δ)}^p < 1:

    exp(φ(f_j)) = 1 + F_j + G_j    (F = linear, G = higher order)

    exp(φ(f)) = Σ_I Σ_J (∏_{j∈J} F_j)(∏_{k∈I\J} G_k)

**Step 4: Integration by parts on F factors.** Each φ(f_j) contracted using Cor. 12.2.3:
- (i) Between F factors: ⟨f_i, C_0 f_j⟩ ≤ O(1) e^{-m|i-j|}
- (ii) To G vertices: bounded by Lemma 12.5.3
- (iii) To the exponent: produces P'(φ) terms

**Step 5: Exponential decay controls combinatorics.** The kth contraction to Δ has distance d_k with k ≤ const d_k^2 (geometry), giving:
    ∏_{k=1}^{n(Δ)} O(1) e^{-const k^{1/2}} ≤ exp(const n(Δ) - const n(Δ)^{3/2})
This super-linear convergence dominates all combinatorial factors.

**Step 6: Final bound.**
    ∫ e^{φ(f)} dμ ≤ ∏_i (1 + 2c(‖f_i‖_{L^1} + ‖f_i‖_{L^p}^p))
                   ≤ ∏_i exp(2c(‖f_i‖_{L^1} + ‖f_i‖_{L^p}^p))
                   = exp(2c(‖f‖_{L^1} + ‖f‖_{L^p}^p))

**Key mathematical insight:** The proof fundamentally relies on the **exponential decay of the free covariance** C_0(x,y) ~ exp(-m|x-y|) for massive fields. This ensures distant regions are nearly independent and the infinite product converges.

### Lean file mapping
- `generating_functional_bound` (Regularity.lean:98) -- THE MAIN REGULARITY THEOREM
- `normFunctional` (Regularity.lean:80) -- N'(f) norm

### Proof strategy for generating_functional_bound
This is the most analytically demanding frontier obligation. The proof requires:
1. Theorem 12.4.1 (uniformity in volume) -- eliminates |Λ|
2. Integration by parts (Cor. 12.2.3) -- Schwinger-Dyson equations
3. Exponential decay of C_0 -- controls the IBP contractions
4. Localized estimates (Lemma 12.5.2-4) -- bounds on the contractions
5. Large/small decomposition and the k^{1/2} geometric decay argument

## 5. How This Combines with Chapters 8-11

1. **Ch 8:** Finite volume estimates → Theorem 8.6.2 (e^{-V} ∈ L^p)
2. **Ch 9:** Integration by parts in finite volume (Schwinger-Dyson)
3. **Ch 10:** Multiple reflections + correlation inequalities + conditioning
4. **Ch 11 (Thm 11.2.1):** Existence + OS0, OS2, OS3
5. **Ch 12:**
   - Sec 12.2: Extends IBP to infinite volume, Wick powers in L^2
   - Sec 12.3: Nonlocal φ^4 bounds with double cutoff
   - Sec 12.4: Asymmetric reflections remove volume dependence
   - Sec 12.5 (Thm 12.5.1): OS1 regularity
6. **Thm 12.1.1:** OS0-OS3 ⟹ Wightman QFT by reconstruction (Ch 6/19)

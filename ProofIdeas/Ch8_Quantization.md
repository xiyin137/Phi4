# Chapter 8: Quantization -- Feynman Graphs, Wick Products, e^{-V} in L^p

## Status Snapshot (2026-02-25)

- `FeynmanGraphs.lean`:
  4 `sorry`s remain (`num_pairings`, `wicks_theorem_even`,
  `feynman_graph_expansion`, `localized_graph_bound`).
- `Interaction.lean`:
  4 `sorry`s remain (`interactionCutoff_in_L2`, `interactionCutoff_converges_L2`,
  `interaction_in_L2`, `exp_interaction_Lp`).
- `FiniteVolumeMeasure.lean`:
  1 `sorry` remains (`schwingerTwo_le_free`).
- Closed and stable in this chapter layer:
  semibounded quartic Wick estimate (`wick_fourth_semibounded`) and its explicit lower bound.
- Note:
  line-number references below are historical and may drift; theorem names are the
  stable lookup key.

## 1. Feynman Graphs (Section 8.2)

> **Important conceptual point:** Feynman graphs in Glimm-Jaffe are used *non-perturbatively*,
> not as a formal power series in lambda. They provide exact Gaussian integral decompositions
> and bounded (not truncated) sums. See [FeynmanGraphsNonPerturbative.md](FeynmanGraphsNonPerturbative.md)
> for a detailed discussion of this distinction and why it matters.

**Integration by parts / Wick's theorem:**
    ∫ φ(f) A(φ) dφ_C = ∫ ⟨Cf, δA/δφ⟩ dφ_C

For even r:
    ∫ φ(f_1)···φ(f_r) dφ_C = Σ_{pairings} (f_{i_1},f_{i_2})_C ··· (f_{i_{r-1}},f_{i_r})_C

Number of terms: (r-1)!! = (r-1)(r-3)···1

**Graph structure:** Vertices (points in R^d), lines (propagators C(x,y)), legs (field factors).
Graph value: I(G) = ∫ ∏_l C(x_{l_1}, x_{l_2}) ∏_i dx_i

### Lean file mapping
- `num_pairings` (FeynmanGraphs.lean:52) -- (2n-1)!! counting
- `wicks_theorem_even`, `wicks_theorem_odd` (FeynmanGraphs.lean:63,68)
- `graphIntegral` (FeynmanGraphs.lean:101)
- `feynman_graph_expansion` (FeynmanGraphs.lean:111)

### Proof ideas
- `num_pairings`: Pure combinatorics. Count by induction: first element can pair with any of (2n-1) others, leaving (2n-2) elements.
- `wicks_theorem`: Induction on r using integration by parts. Contract φ(f_1) with each other factor; each contraction produces one propagator C(f_1,f_j) times a (r-2)-point integral.
- `wicks_theorem_odd`: Symmetry under φ → -φ for centered Gaussian.

## 2. Wick Products and Graph Structure (Section 8.3)

Two types of lines:
- **Self-lines** (S): pairing legs at same vertex
- **Interaction lines** (I): pairing legs from different vertices

**Proposition 8.3.1:** For Wick-ordered monomials,
    ∫ ∏ :φ^{n_i}(f_i):_{C_i} dφ_C = Σ_G I(G)

where I(G) = ∫ [∏_{l∈I} C(x_{l_1},x_{l_2})] [∏_{l∈S} δC_i(x_{l_1},x_{l_2})] ∏ f_i ∏ dx

**Corollary 8.3.2 (Crucial):** If C_i = C for all i, then δC_i = 0, eliminating all self-lines. Only interaction lines survive.

**φ^4 Wick product:**
    :φ^4:_C = φ^4 - 6c_κ φ^2 + 3c_κ^2

where c_κ(x) = C_κ(x,x) ~ (2π)^{-1} ln κ in d=2.

### Lean file mapping
- `wickFourth` (WickProduct.lean:71) -- :φ^4: = φ^4 - 6cφ^2 + 3c^2
- `rewick_fourth` (WickProduct.lean:113) -- re-Wick-ordering

### Proof idea for rewick_fourth
The Wick reordering formula (8.6.1):
    :φ(x)^n:_{C_1} = Σ_{j=0}^{[n/2]} [n! / ((n-2j)! j! 2^j)] δc(x)^j :φ(x)^{n-2j}:_{C_2}
where δc(x) = lim_{y→x} [C_2(x,y) - C_1(x,y)]. This is the Hermite polynomial addition theorem.

## 3. Gaussian Integral Estimates (Section 8.5)

**The crucial d=2 fact:** c_κ = C_κ(x,x) = O(ln κ). This logarithmic divergence is what makes only Wick ordering necessary (no further renormalization).

**Proposition 8.5.1:** For C ∈ C_m, f ∈ L_p(R^2) with compact support:
    :φ_κ^n(f):_C ∈ L_2(dφ_C) and converges in L_2 as κ → ∞
with ‖:φ^n(f): - :φ_κ^n(f):‖_{L_2} ≤ O(κ^{-δ}).

**Theorem 8.5.3:** R = ∫ w(x) ∏ :φ(x_i)^{n_i}:_C dx, then R_κ, R ∈ L_q for all q < ∞, with:
    |∫ (R - R_κ)^j dφ_C| ≤ j!^{Σn_i/2} (const ‖w‖_{L_p} κ^{-ε})^j

**Theorem 8.5.5 (Localized graph bounds):** For R localized in unit squares Δ_{i_1}×···×Δ_{i_r}:
    |∫ R dφ_C| ≤ ‖w‖_{L_p} ∏_Δ N(Δ)! (const m^{-1/q})^{N(Δ)}
where N(Δ) counts legs in Δ. Exploits exponential decay e^{-m dist(G)} of propagators.

### Lean file mapping
- `wickPower_memLp` (WickProduct.lean:88)
- `localized_graph_bound` (FeynmanGraphs.lean:132)
- `interactionCutoff_in_L2` (Interaction.lean:84)
- `interactionCutoff_converges_L2` (Interaction.lean:97)

### Proof ideas
- `wickPower_memLp`: From Theorem 8.5.3 with j=2 (L^2 norm). The key input is the localized graph bound with c_κ = O(ln κ) in d=2.
- `localized_graph_bound`: Holder's inequality applied to the graph integral I(G), using C ∈ L^q(Δ_i × Δ_j) with exponential decay between distant squares.
- `interactionCutoff_converges_L2`: L^2 convergence of V_{Λ,κ} = λ∫_Λ :φ_κ^4: dx follows from ‖V_Λ - V_{Λ,κ}‖_{L_2}^2 = Σ_G |I(G)| with self-line contributions δC_κ → 0 in L^q.

## 4. Main Theorem: e^{-V} ∈ L^p (Theorem 8.6.2)

**Statement:** For f satisfying conditions (8.6.4), C_1, C_2 ∈ C_m^M:
    ∫ exp(-:P(φ,f):_{C_1}) dφ_{C_2} ≤ exp{const(N(f) + 1)}

where N(f) = ∏_j ‖f_j/f_n‖_{L_{n/(n-j)}}^{4/(n-j)}.

### Two-Step Proof Strategy

**Step 1: Semiboundedness (Proposition 8.6.3).**
    :P(φ_κ, f):_C ≥ -const ‖f_n‖_{L^∞} [(ln κ)^{deg P/2} + N(f)]

For φ^4 specifically:
    :φ_κ^4:_C = (φ_κ^2 - 3c_κ)^2 - 6c_κ^2 ≥ -6c_κ^2 = -O((ln κ)^2)

**THIS IS THE KEY d=2 FACT:** c_κ ~ ln κ (logarithmic), so c_κ^2 = O((ln κ)^2) -- polynomial in ln κ. In d ≥ 3, c_κ diverges as a power of κ, breaking this argument.

**Step 2: Small measure of bad set (Proposition 8.6.4).**
Let δP_κ = :P: - :P_κ: and χ(κ) = {φ : 1 ≤ |δP_κ|}. Then:
    ∫_{χ(κ)} dφ_C ≤ exp(-α(κ^ε/M(f))^{2/deg P})

Uses Gaussian integral estimates (Corollary 8.5.4) + optimization over the order j of the moment.

**Combining Steps 1 and 2:** Layer-cake formula ∫|g|^p = p∫_0^∞ a^{p-1} h(a) da where h(a) = μ{φ : a ≤ |g|}. The polynomial-in-ln-κ lower bound from Step 1 is overwhelmed by the exponential-in-κ^ε tail from Step 2.

### Lean file mapping
- `wick_fourth_semibounded` (Interaction.lean:68) -- Step 1
- `wick_fourth_lower_bound_explicit` (Interaction.lean:74) -- explicit (φ^2-3c)^2 - 6c^2
- `exp_interaction_Lp` (Interaction.lean:127) -- THE MAIN THEOREM

### Proof strategy for exp_interaction_Lp
This is the hardest single estimate. Approach:
1. Prove semiboundedness: :φ_κ^4: ≥ -6c_κ^2 (direct computation from the rewriting)
2. Prove small-bad-set estimate: use L^{2j} norms of (V - V_κ) optimized over j
3. Combine via the layer-cake/interpolation argument

The key inputs are:
- c_κ = O(ln κ) from the log divergence of the covariance
- ‖V - V_κ‖_{L_{2j}} ≤ (j!)^2 (const κ^{-ε})^j from localized graph bounds
- The optimization j ~ κ^{2ε/(deg P)} gives the double-exponential tail

## 5. Finite Dimensional Approximations (Section 8.7)

**Proposition 8.7.2:** The triple limit
    lim_{κ→∞} lim_{λ→∞} lim_{δ→0} exp(-p(δ,λ,κ)) = exp(-:P(φ,f):_C)  in L^p

This provides the lattice approximation needed for correlation inequalities in Chapter 9-10.

### Lean file mapping
- `interactionCutoff` (Interaction.lean:47) -- V_{Λ,κ}
- `interaction` (Interaction.lean:52) -- UV limit V_Λ
- `partition_function_pos`, `partition_function_integrable` (Interaction.lean:133,139)

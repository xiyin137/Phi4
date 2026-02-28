# The Non-Perturbative Role of Feynman Graphs in phi^4_2

## Status Snapshot (2026-02-27)

- This document remains conceptually accurate and aligned with the intended
  non-perturbative architecture.
- In current code, chapter-8 graph/integrability obligations are represented as
  explicit interfaces (`FeynmanGraphEstimateModel`, `InteractionUVModel`,
  `InteractionWeightModel`) rather than local theorem-level `sorry`.
- Use this note as strategy context; executable progress tracking lives in
  `ProofIdeas/Overview.md` and chapter status blocks.

## Key Conceptual Point

Feynman graphs in the Glimm-Jaffe construction are **not** a perturbative tool (no formal
power series in lambda). They serve three distinct non-perturbative roles:

1. **Exact decomposition of Gaussian integrals** (Ch 8)
2. **Convergent expansion for weak coupling** (Ch 18, cluster expansion)
3. **Organizing integration by parts** (Ch 12, regularity)

In each case, the full sum over graphs is either exact or convergent -- never truncated.

---

## Role 1: Estimating Gaussian Integrals (Chapter 8)

### The problem
To prove `exp(-V_Lambda) in L^p(d phi_C)` (Theorem 8.6.2 / `exp_interaction_Lp`),
we need to bound moments:

    integral V_Lambda^n d phi_C = integral (lambda integral_Lambda :phi^4:)^n d phi_C

### How Feynman graphs enter
Expanding the n-th power gives products of Wick monomials. **Wick's theorem** (which IS
the Feynman graph expansion) is an exact identity for Gaussian integrals:

    integral :phi(x_1)^4: ... :phi(x_n)^4: d phi_C = Sum_G I(G)

Each graph G has vertices at x_1,...,x_n with 4 legs each, and lines carrying C(x_i, x_j).
This is not an approximation -- it's an exact combinatorial identity for Gaussian measures.

### The crucial estimate: localized graph bounds (Theorem 8.5.5)
When vertices are localized in unit squares Delta_i, the graph integral satisfies:

    |I(G)| <= Prod_Delta N(Delta)! * (const/m)^{N(Delta)}

The **factorial per square** N(Delta)! (not global N!) is what makes the sum manageable.
This factorization comes from the exponential decay of C(x,y) ~ exp(-m|x-y|), which
decorrelates distant squares.

### Lean mapping
- `wicks_theorem_even` (FeynmanGraphs.lean) -- exact Gaussian identity
- `wicks_theorem_odd` (FeynmanGraphs.lean) -- proved via GaussianField.odd_moment_vanish
- `localized_graph_bound` (FeynmanGraphs.lean) -- per-square factorial bound
- `exp_interaction_Lp` (Interaction.lean) -- the main theorem using these bounds

### Non-perturbative content
The sum over ALL graphs is bounded, not just finitely many. The bound uses:
1. Semiboundedness: :phi^4: >= -6c_kappa^2 (completing the square)
2. Gaussian tails: Prob(|:phi^4: < -K|) <= exp(-const * kappa^epsilon)
3. Layer-cake: the polynomial lower bound is overwhelmed by exponential tails

---

## Role 2: Cluster Expansion (Chapter 18)

### The problem
For OS4 (clustering / exponential decay of correlations), we need:

    |<AB> - <A><B>| <= M exp(-m * dist(supp A, supp B))

### How Feynman graphs enter
The cluster expansion is a **convergent** (not formal) rearrangement:

    S_Lambda(x) = Sum_{X, Gamma} T(x, Lambda, X, Gamma)

where X ranges over connected subsets of a lattice tiling of Lambda, and Gamma indexes
which lattice bonds are "active" (interpolation parameters s_b in [0,1]).

Each term T involves:
- An integral over the interpolation parameters s in [0,1]^|Gamma|
- Derivatives d/ds_b that produce propagator insertions (Feynman lines)
- Factorized Gaussian integrals over connected components

### Why it converges (for small lambda)
Three estimates control convergence:
1. **Combinatorial bound** (Prop 18.4.1): Number of terms with |X| = k is <= exp(K_1 * k)
2. **Partition function ratio** (Prop 18.4.2): |Z_{dX}/Z| <= exp(K_2 * |X|)
3. **Function space integral** (Prop 18.4.3): Each derivative d/ds_b costs O(m_0^{-r}),
   and the Wiener integral representation gives exponential decay exp(-m_0 * d(path))

For lambda/m_0^6 sufficiently small, the decay beats the combinatorial growth.

### Non-perturbative content
This is NOT perturbation theory in lambda:
- The coupling lambda appears only in the convergence condition lambda/m_0^6 < epsilon_0
- Once convergence is established, the result holds for all lambda in the convergence region
- The expansion is in the *spatial structure* (connected components), not in coupling
- Each term is computed non-perturbatively (full functional integral over each component)

### Lean mapping
- `phi4_os4_weak_coupling` (Reconstruction.lean) -- the clustering result

---

## Role 3: Integration by Parts / Regularity (Chapter 12)

### The problem
The generating functional bound |S{f}| <= exp(c * N'(f)) (OS1 / `generating_functional_bound`)
requires controlling the infinite-volume generating functional uniformly.

### How Feynman graphs enter
Integration by parts in the Gaussian measure:

    integral phi(f) A(phi) d phi_C = integral <Cf, delta A / delta phi> d phi_C

Each IBP step either:
- **Reduces degree** (good): contracts two field factors, producing C(f_i, f_j)
- **Creates a vertex** (bad): hits the interaction V = lambda integral :phi^4:,
  producing :phi^3: (the derivative of :phi^4:)

The resulting terms are organized as Feynman graphs:
- Vertices from interaction derivatives
- Lines from propagator contractions
- External legs from remaining field factors

### The key control mechanism: exponential decay
The free propagator C(x,y) ~ exp(-m|x-y|) means each IBP contraction to a distant
square costs exp(-m * distance). The k-th contraction to square Delta has distance d_k
satisfying k <= const * d_k^2 (geometric packing), giving:

    Prod_{k=1}^{n(Delta)} O(1) exp(-const * k^{1/2}) <= exp(const * n - const * n^{3/2})

This **super-linear convergence** (n^{3/2} vs n) dominates all combinatorial factors.

### Non-perturbative content
The IBP expansion is not in lambda. Each IBP step produces one C(x,y) factor and one
:phi^3: vertex. The bound on the sum uses:
- Exponential decay of C (massive propagator)
- Localized graph bounds from Ch 8 (for the :phi^3: vertices)
- Multiple reflections from Ch 10 (to eliminate volume dependence)

### Lean mapping
- `euclidean_equation_of_motion` (Regularity.lean) -- the IBP identity
- `generating_functional_bound` (Regularity.lean) -- the main regularity theorem
- `generating_functional_bound_uniform` (Regularity.lean) -- volume-independent version

---

## Summary: Non-Perturbative vs Perturbative

| Aspect | Perturbative QFT | Glimm-Jaffe approach |
|--------|-----------------|---------------------|
| **Expansion parameter** | Coupling lambda | None (exact) or spatial structure |
| **Convergence** | Asymptotic (divergent!) | Exact or convergent |
| **Feynman graphs count** | All graphs at each order | All graphs, bounded sum |
| **Role of graphs** | Approximate computation | Exact decomposition of Gaussian integrals |
| **Key input** | Renormalization | Localization + exponential decay of C(x,y) |
| **Result** | Formal power series | Rigorous existence theorem |

The common thread in all three roles: Feynman graphs decompose Gaussian integrals into
manageable pieces (lines = propagators, vertices = interaction points). The non-perturbative
content comes from **bounding the full sum** using:

1. **Localization**: factorize into per-square contributions (N(Delta)! per square)
2. **Exponential decay**: C(x,y) ~ exp(-m|x-y|) decorrelates distant squares
3. **Dimension-specific bounds**: c_kappa ~ ln(kappa) in d=2 (logarithmic, not power-law)

These three ingredients together make the d=2 theory "just barely" constructible. In d >= 3,
the logarithmic divergence becomes polynomial, and additional renormalization (beyond Wick
ordering) is needed.

---

## Implications for the Lean Formalization

The architecture reflects this non-perturbative structure:

1. **FeynmanGraphs.lean** provides the exact Gaussian identities (Wick's theorem)
   and the combinatorial framework (Pairing, FeynmanGraph structures)

2. **Interaction.lean** uses these to prove the central L^p estimate (Theorem 8.6.2),
   combining semiboundedness + Gaussian tail estimates

3. **MultipleReflections.lean** provides uniform bounds via iterated RP and
   chessboard estimates (using graph bounds per unit square)

4. **Regularity.lean** organizes the IBP expansion using graph structure,
   with exponential decay controlling the combinatorics

5. **Reconstruction.lean** uses the cluster expansion for OS4 (weak coupling only)

The `localized_graph_bound` (Theorem 8.5.5) is the single most important graph estimate --
it feeds into Interaction (L^p bounds), MultipleReflections (uniform bounds), and
Regularity (IBP bounds). Getting this right is essential for the entire construction.

---

## Appendix: How GJ Overcome Zero Radius of Convergence

### The problem
Naive perturbation theory in QFT produces a formal power series:

    S(f) = Sum_{n=0}^infty (-lambda)^n / n! integral V^n A d phi_C

This series has **zero radius of convergence**: the n-th coefficient grows like n!
(Dyson's argument: lambda < 0 makes the theory unstable, so the function S(lambda)
has a singularity at lambda = 0). No amount of resummation fixes this for the full
perturbative series.

### GJ's solution: avoid expanding in lambda entirely

The key insight is that the Glimm-Jaffe approach **never expands in powers of lambda**.
Instead, lambda appears only in the exponent exp(-lambda V), which is treated as a
single object. The program proceeds by:

#### Step 1: Prove exp(-V) in L^p directly (not by expanding the exponential)
Theorem 8.6.2 proves integral exp(-p V_Lambda) d phi_C < infinity by combining:
- Semiboundedness: V >= -K (ln kappa)^2 (polynomial in ln kappa, NOT in lambda)
- Gaussian tail bounds: the set where V is very negative has exponentially small measure
- Layer-cake integration: int exp(-pV) = p int_0^infty a^{p-1} P(|exp(-V)| > a) da

At no point is exp(-lambda V) expanded as a power series in lambda. The bound holds
for ALL lambda > 0 (and improves for small lambda, but doesn't require it).

#### Step 2: Use monotonicity (not expansion) for the infinite volume limit
The GKS correlation inequalities (Chapter 4/10) provide:
- Monotonicity: S_2^{Lambda_1} <= S_2^{Lambda_2} for Lambda_1 subset Lambda_2
- Uniform bounds: |S_n^Lambda| <= C (from multiple reflections)
- Therefore: lim_{Lambda -> R^2} S_n^Lambda exists by monotone convergence

This is a purely measure-theoretic argument. No perturbative expansion is used.

#### Step 3: Cluster expansion is in SPACE, not in lambda
The cluster expansion (Chapter 18) does use a convergent expansion, but the expansion
parameter is the spatial coupling between lattice squares, not the coupling constant:
- s_b in [0,1] interpolates between full coupling (s=1) and spatial decoupling (s=0)
- Each term costs exp(-m * distance) from the massive propagator
- Convergence requires lambda/m_0^6 < epsilon_0 (weak coupling), but the expansion
  is in the spatial structure, not in lambda

The weak coupling condition ensures that the per-square interaction is "small compared
to the decorrelation from the mass gap," which is a statement about spatial scales,
not about perturbative order.

#### Step 4: Regularity via integration by parts (not perturbative expansion)
The OS1 bound (Theorem 12.5.1) uses integration by parts:
    integral phi(f) A d mu = integral <Cf, delta A / delta phi> d mu - lambda integral <Cf, :phi^3:> A d mu

Each IBP step produces one propagator C(x,y) and one :phi^3: vertex. The key control
is the exponential decay of C(x,y), not any smallness of lambda. The argument works
for ALL lambda > 0.

### Summary: three strategies that avoid perturbative expansion

| Strategy | Used for | Expansion parameter | Key control |
|----------|----------|-------------------|-------------|
| Direct L^p bounds | exp(-V) in L^p | None | Semiboundedness + tails |
| Monotone convergence | Infinite volume limit | None | GKS inequalities |
| Cluster expansion | Clustering (OS4) | Spatial coupling s_b | Propagator decay exp(-md) |
| Integration by parts | Regularity (OS1) | None | Propagator decay exp(-md) |

The common denominator: **the massive propagator C(x,y) ~ exp(-m|x-y|)** provides
spatial decorrelation that controls all estimates. This replaces the role that
"smallness of lambda" would play in a perturbative approach.

### Why this works in d=2 but not (easily) in d >= 3
In d=2, the UV divergence is logarithmic: c_kappa ~ ln(kappa). This means:
- Wick ordering suffices (no additional renormalization beyond :phi^4: = phi^4 - 6c phi^2 + 3c^2)
- The semiboundedness bound :phi^4: >= -6c_kappa^2 = -O((ln kappa)^2) is manageable
- The Gaussian tail exp(-const * kappa^epsilon) overwhelms (ln kappa)^2

In d=3, c_kappa ~ kappa (linear divergence), requiring mass and coupling constant
renormalization beyond Wick ordering. The construction still works (Feldman-Osterwalder,
Magnen-Seneor, Rivasseau) but is substantially harder.

In d >= 4, the UV divergences are too severe for the constructive approach (at least
for phi^4), consistent with the triviality results of Aizenman and Frohlich.

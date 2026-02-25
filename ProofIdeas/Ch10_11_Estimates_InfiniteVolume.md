# Chapters 10-11: Correlation Inequalities, Multiple Reflections, Infinite Volume

## Status Snapshot (2026-02-25)

- Correlation inequality API:
  `CorrelationInequalities.lean` currently has no `sorry` (interface-based layer in place).
- Multiple reflections:
  `MultipleReflections.lean` has 2 `sorry`s (`chessboard_estimate`,
  `schwinger_uniform_bound`).
- Infinite-volume layer:
  `InfiniteVolumeLimit.lean` has 5 `sorry`s (`schwinger_uniformly_bounded`,
  `infinite_volume_schwinger_exists`, `infiniteVolumeMeasure`,
  `infiniteVolumeMeasure_isProbability`, `infiniteVolumeSchwinger_is_moment`).
- Closed bridge result:
  `schwingerN_monotone_in_volume` is implemented for the established `k = 2` case.
- Note:
  line-number references below are historical and may drift; theorem names are the
  stable lookup key.

## 1. Correlation Inequalities (Section 10.2)

Extended from lattice (Chapter 4) to continuum P(φ)_2 via lattice approximation (Chapter 9).

### GKS-I (Theorem 4.1.1 / 10.2.1)
For P = even - μφ with μ ≥ 0: all moments are nonneg:
    0 ≤ ⟨ξ_A⟩

### GKS-II (Theorem 4.1.3 / 10.2.1)
Pair correlations are positive (truncated):
    0 ≤ ⟨ξ_A ξ_B⟩ - ⟨ξ_A⟩⟨ξ_B⟩

**This is the cornerstone of the monotone convergence argument.**

### FKG Inequality (Section 4.4 / 10.2)
For arbitrary semibounded P and monotone functions F, G:
    ⟨F⟩⟨G⟩ ≤ ⟨FG⟩

### Lebowitz Inequality (Corollary 4.3.2-3)
For P = λφ^4 + σφ^2 - μφ, the Ursell function U_4 ≤ 0:
    ⟨φ(x_1)φ(x_2)φ(x_3)φ(x_4)⟩ - ⟨φ(x_1)φ(x_2)⟩⟨φ(x_3)φ(x_4)⟩
       - ⟨φ(x_1)φ(x_3)⟩⟨φ(x_2)φ(x_4)⟩ - ⟨φ(x_1)φ(x_4)⟩⟨φ(x_2)φ(x_3)⟩ ≤ 0

### Lean file mapping
- `griffiths_first` (CorrelationInequalities.lean:43) -- GKS-I
- `griffiths_second` (CorrelationInequalities.lean:60) -- GKS-II
- `fkg_inequality` (CorrelationInequalities.lean:78) -- FKG
- `lebowitz_inequality` (CorrelationInequalities.lean:100) -- Lebowitz
- `schwinger_two_monotone` (CorrelationInequalities.lean:118) -- consequence of GKS-II + Dirichlet monotonicity

### Proof ideas
- **GKS-I/II:** The standard proof goes through the lattice approximation. On the lattice, GKS uses the "Griffiths trick": expand exp(-H) as a product of factors, each involving a single site, then use the lattice ferromagnetic structure. For GKS-II, duplicate variables t = (ξ+χ)/√2, q = (ξ-χ)/√2 and apply GKS-I to the doubled system.
- **FKG:** Proved via the lattice FKG (Fortuin-Kasteleyn-Ginibre) and limit.
- **Lebowitz:** Uses the duplication trick to separate the 4-point function into products of 2-point functions.
- **schwinger_two_monotone:** For Λ_1 ⊂ Λ_2, use C^D_{Λ_1} ≤ C^D_{Λ_2} (Dirichlet monotonicity) combined with GKS-II to get S_2^{Λ_1} ≤ S_2^{Λ_2}.

## 2. Dirichlet/Neumann Monotonicity and Decoupling (Section 10.3)

**Proposition 10.3.1:** For fixed Λ and lattice refinements Γ_1 ⊂ Γ_2:
    Z_D ≤ Z_{Γ_2} ≤ Z_{Γ_1} ≤ Z_0 ≤ Z_N

**Decoupling:** Both Z_D and Z_N factorize over lattice squares:
    Z_D(Λ) = ∏_{Δ∈Λ} Z_D(Δ)
    Z_N(Λ) = ∏_{Δ∈Λ} Z_N(Δ)

**Corollary 10.3.2:** exp(-O(|Λ|)) ≤ Z_B(Λ) ≤ exp(O(|Λ|))

**Free energy convergence (Proposition 10.3.3):**
    α_{D}(Λ) ≤ α_0(Λ) ≤ α_{N}(Λ)
Both α_D and α_N converge as Λ → R^2. In the limit, all agree: α_D = α_0 = α_N.

### Lean file mapping
- `partition_function_ratio_bound` (MultipleReflections.lean:106)

## 3. Reflection Positivity for the Interacting Measure (Section 10.4)

**Theorem 10.4.2:** For θ-invariant Gaussian measure with classical boundary conditions, dφ_C satisfies RP.

**Theorem 10.4.3:** The interacting measure
    dμ(V,Λ,C_B) = Z^{-1} exp(-V(Λ)) dφ_{C_B}
satisfies RP when θΛ = Λ, θV = V, [θ,C_B] = 0.

**Proof:** Write V = V_+ + V_- with V_± = V(Λ_±). Then θV_± = V_∓, so V = V_+ + θV_+. Since dφ_C is RP:
    Z dμ = (θ e^{-V_+}) · e^{-V_+} · dφ_C
and the standard RP argument applies.

**Key fact:** RP is preserved under limits, so infinite volume measures also satisfy RP.

### Lean file mapping
- `interacting_measure_reflection_positive` (ReflectionPositivity.lean:102)

### Proof strategy
The main ingredient is that V(Λ) splits as V(Λ_+) + V(Λ_-) when Λ is symmetric. Then for A ∈ A_+:
    ⟨θA, A⟩_{dμ} = Z^{-1} ∫ (θA)* A exp(-V_+ - θV_+) dφ_C
                   = Z^{-1} ∫ (θ(A e^{-V_+}))* (A e^{-V_+}) dφ_C ≥ 0
by RP of dφ_C (since A e^{-V_+} is supported at positive times).

## 4. Multiple Reflections / Chessboard Estimates (Section 10.5)

### Configuration 1: Lattice reflection group
For k ∈ S((R_+)^d) and d orthogonal reflections θ_{Π_v}:
    |∫ k dμ|^{2^d} ≤ ∫ R(k) dμ
where R(k) = ∏_{I⊂{1,...,d}} [(∏_{v∈I} θ_{Π_v}) k]^{(-1)^{|I|}}

### Configuration 2: Integer time translations
For k ∈ S(0,t), define M(k) = lim_{n→∞} [∫ M_{2^n}(k) dμ]^{1/2^n}. Then:
    |∫ k dμ| ≤ M(k)

### Configuration 3: Full lattice (Chessboard estimate, Proposition 10.5.3)
For k ∈ S(X) where X = [0,a_1] × ··· × [0,a_d]:
    |∫ k dμ| ≤ L(k)
where L(k) is the iterated reflection limit.

**Corollary 10.5.8 (Full chessboard bound):** For k^{(j)} ∈ S(Δ_j) (unit cubes):
    |∫ ∏_{j∈J} k^{(j)} dμ| ≤ ∏_{j∈J} L(k^{(j)})

### Lean file mapping
- `chessboard_estimate` (MultipleReflections.lean:54)
- `schwinger_uniform_bound` (MultipleReflections.lean:98)

### Proof strategy for chessboard_estimate
This is an iterated Schwarz inequality. In d=2 with 2 orthogonal reflections:
1. Apply RP for θ_x (vertical reflection): |∫ k dμ|^2 ≤ ∫ (θ_x k)* k dμ
2. Apply RP for θ_y (horizontal reflection) to the result: |∫ (θ_x k)* k dμ|^2 ≤ ∫ R(k) dμ
3. Combine: |∫ k dμ|^4 ≤ ∫ R(k) dμ

The full chessboard bound iterates this d-fold, then extends to unions of lattice cubes via translation invariance.

## 5. Infinite Volume Limit (Chapter 11)

### Theorem 11.2.1 (Existence)
Let P = even + linear. Then S{f} = lim_{Λ↗R^2} S_Λ{f} exists and satisfies OS0, OS2-3.

**Proof strategy:**
1. **Monotonicity:** For g ≥ 0, S_Λ{-ig} = ⟨e^{φ(g)}⟩_Λ is positive (GKS-I) and monotone increasing in Λ (GKS-II + Dirichlet monotonicity).
2. **Uniform upper bound** (Theorem 11.3.1): |∫ e^{φ(f)} dμ_Λ| ≤ exp{c(|K| + ‖f‖_{L^p}^p)} independent of Λ.
3. **Vitali's theorem:** S_Λ{zg} is entire in z, uniformly bounded. Pointwise convergence on R_+ (from monotonicity + boundedness) extends to all of C by Vitali.
4. **General f:** Decompose f = f_+ - f_- and use the non-negative convergence.

### Lean file mapping
- `schwinger_monotone_in_volume` (InfiniteVolumeLimit.lean:61) -- monotonicity
- `schwingerN_monotone_in_volume` (InfiniteVolumeLimit.lean:71)
- `schwinger_uniformly_bounded` (InfiniteVolumeLimit.lean:87) -- uniform bound
- `infinite_volume_schwinger_exists` (InfiniteVolumeLimit.lean:103) -- existence
- `infiniteVolumeMeasure` (InfiniteVolumeLimit.lean:114) -- measure construction
- `infiniteVolumeMeasure_isProbability` (InfiniteVolumeLimit.lean:119)

### Proof ideas
- `schwinger_monotone_in_volume`: For Λ_1 ⊂ Λ_2 with Dirichlet BC:
  S_2^{Λ_1}(f,g) = ∫ φ(f)φ(g) dμ_{Λ_1} ≤ ∫ φ(f)φ(g) dμ_{Λ_2} = S_2^{Λ_2}(f,g)
  This uses: (a) C_{Λ_1}^D ≤ C_{Λ_2}^D (domain monotonicity), and (b) GKS-II for the interacting measure.

- `schwinger_uniformly_bounded`: This IS Theorem 11.3.1 -- the hardest estimate in this chapter. See below.

- `infinite_volume_schwinger_exists`: Monotone bounded sequences converge (real analysis).

- `infiniteVolumeMeasure`: The Schwinger functions determine a measure by the Bochner-Minlos theorem (S{f} is positive definite and continuous on S(R^d)).

### Theorem 11.3.1 (Main Upper Bound) -- Detailed proof outline

For 0 < m, f ∈ L^1 ∩ L^p supported in K:
    |∫ e^{φ(f)} dμ_Λ| ≤ exp{c(|K| + ‖f‖_{L^p}^p)}

**Proof steps:**
1. **Reduce to f ≥ 0:** By GKS-I, |⟨e^{φ(f)}⟩| ≤ ⟨e^{φ(|f|)}⟩.
2. **Enlargement:** Choose Λ^{(1)} ⊃ Λ centered at corner of K, axes parallel to K.
3. **Reflection step:** By RP (Prop. 10.5.1): ⟨e^{φ(f)}⟩_{Λ^{(1)}} ≤ [⟨e^{φ(f^{(1)})}⟩_{Λ^{(1)}}]^{1/4}
   where f^{(1)} = (1+θ_x)(1+θ_y)f supported in K^{(1)} of area 4|K|.
4. **Iterate n times:** |K^{(n)}| ~ 4^n|K|, exponent picks up factor 4^{-n}.
5. **Terminate when K^{(n)} fills Λ^{(n)}.**
6. **Condition and decouple:** Replace Dirichlet by Neumann on unit lattice. Z_N factorizes.
7. **Apply Theorem 8.6.2** to each unit square.
8. **Final bound:** ‖f^{(n)}‖_{L^p}^p = 4^n ‖f‖_{L^p}^p. The 4^{-n} exponent cancels this.

### Lean file mapping for 11.3.1
- `schwinger_uniform_bound` (MultipleReflections.lean:98) -- uses chessboard_estimate
- `determinant_bound` (MultipleReflections.lean:80) -- Z_+^2/Z ≤ exp(O(|Λ|))

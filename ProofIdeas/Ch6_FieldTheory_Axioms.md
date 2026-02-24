# Chapter 6: Field Theory -- Axioms, Reconstruction, Free Field, Wick Ordering

## 1. Osterwalder-Schrader (Euclidean) Axioms

The Euclidean fields are defined by a probability measure dμ on S'(R^d). The generating functional is:

    S{f} = ∫ exp(i φ(f)) dμ

**OS0 (Analyticity).** For every finite set of test functions f_j in D(R^d), the map
z → S{Σ z_j f_j} is entire on C^N.

**OS1 (Regularity).** For some p in [1,2], some constant c, and all f in C_0^∞:
    |S{f}| ≤ exp c(‖f‖_{L^1} + ‖f‖_{L^p})
For φ^4, take p = 4/3.

**OS2 (Euclidean Invariance).** S{f} = S{Ef} for Euclidean transformations E.

**OS3 (Reflection Positivity).** For f_j in D_real(R^d_+), the matrix M_{ij} = S{f_i - θf_j} is positive semidefinite, where θ: (x,t) → (x,-t).

**OS4 (Ergodicity).** Time translations T(t) act ergodically on (S'(R^d), dμ).

### Lean file mapping
- `phi4_os0` (OSAxioms.lean:56) ← OS0
- `phi4_os2_translation`, `phi4_os2_rotation` (OSAxioms.lean:84,99) ← OS2
- `phi4_os3` (OSAxioms.lean:117) ← OS3
- `phi4_os4_weak_coupling` (Reconstruction.lean:83) ← OS4

## 2. Wightman Axioms

**W1 (Covariance/Spectral condition).** Continuous unitary representation of the inhomogeneous Lorentz group on H, with spectrum in the forward cone. Invariant vacuum Ω.

**W2 (Fields).** Field operators φ_M(f) densely defined on H, covariant under Lorentz group, with Ω cyclic.

**W3 (Locality).** [φ_M(f), φ_M(h)] = 0 on D when supp f, supp h are spacelike separated.

**W4 (Uniqueness of vacuum).** Ω is the unique (up to scalar) vector invariant under time translations.

### Lean file mapping
- `phi4_wightman_exists` (Reconstruction.lean:107) ← W1-W3
- `phi4_unique_vacuum` (Reconstruction.lean:157) ← W4

## 3. OS Reconstruction Theorem (Theorem 6.1.3 + 6.1.5)

**Step 1: Physical Hilbert space.** From G = L^2(S', dμ), let G_+ = span of positive-time functionals. Define b(A,B) = ⟨θA, B⟩_G. By OS3, b ≥ 0. Then H = (G_+ / ker b)^completion.

**Step 2: Hamiltonian.** Time translation T(t) induces R(t) = T(t)^hat on H. Properties:
- Semigroup: R(t)R(s) = R(t+s)
- Self-adjoint: R(t)* = R(t)
- Contraction: ‖R(t)‖ ≤ 1
- Strongly continuous

By spectral theorem, R(t) = e^{-tH} with H ≥ 0 self-adjoint, HΩ = 0.

**Step 3: Fields.** OS0-3 ⟹ W1-W3 (Theorem 6.1.5). OS4 ⟺ W4.

**Key relation:**
    ∫ φ_E(x_1,t_1)···φ_E(x_n,t_n) dμ = ⟨Ω, φ_M(it_1,x_1)···φ_M(it_n,x_n) Ω⟩

### Proof idea for Lean
The reconstruction theorem is essentially the content of the OSReconstruction dependency. The main work is verifying that our constructed Schwinger functions satisfy OS0-OS3 (done in OSAxioms.lean) and OS4 (done via cluster expansion in Reconstruction.lean).

## 4. Free Field Construction (Section 6.2)

The free Gaussian measure dφ_C on S'(R^d) with covariance C = (-Δ+m^2)^{-1}:
    S{f} = exp(-⟨f, Cf⟩/2)

**Moments (Wick/Isserlis theorem):**
    ∫ φ(f)^n dφ_C = 0  (n odd),  (n-1)!! C(f,f)^{n/2}  (n even)

**Reflection positivity for C (Definition 6.2.1):** For f supported at positive times,
    0 ≤ ⟨θf, Cf⟩

**Theorem 6.2.2:** dφ_C is reflection positive iff C is.

**Physical Hilbert space (Prop. 6.2.5):**
    ⟨θg_s, Cf_t⟩ = (1/2)⟨g, μ^{-1} e^{-μ(s+t)} f⟩  for s,t ≥ 0
where μ = (-Δ_{d-1} + m^2)^{1/2}. This is manifestly ≥ 0.

    H = L^2(S'(R^{d-1}), dφ_{(2μ)^{-1}})

### Lean file mapping
- `freeCovarianceCLM` (FreeField.lean:90) -- CLM construction
- `freeCovKernel`, `freeCovKernel_symm`, `freeCovKernel_pos_def` (FreeField.lean:144-155)
- `free_covariance_reflection_positive` (ReflectionPositivity.lean:65)

### Proof strategy for freeCovarianceCLM
Need to construct T : S(R^2) →L ℓ^2 as the nuclear embedding composed with (-Δ+m^2)^{-1/2}. The singular values σ_m = λ_m^{-1/2} where λ_m are eigenvalues of the harmonic oscillator (-Δ + |x|^2) on R^2. Key fact: in d=2, the eigenvalues grow linearly (λ_m ~ m), so Σ λ_m^{-1} < ∞ (nuclear embedding).

## 5. Fock Space and Wick Ordering (Section 6.3)

**Integration by parts (Theorem 6.3.1):**
    ∫ φ(f) A(φ) dφ_C = ∫ ⟨f, C δ/δφ⟩ A(φ) dφ_C

**Wick ordering:** :φ(f)^n: = c^{n/2} P_n(φ(f)/c^{1/2}) where P_n is the Hermite polynomial and c = ⟨f, Cf⟩.

**Key formulas:**
    :φ^4: = φ^4 - 6cφ^2 + 3c^2
    :exp(φ(f)): = exp[φ(f) - (1/2)⟨f,Cf⟩]

**Orthogonality:** ∫ :φ^n:(f) :φ^m:(g) dφ_C = δ_{nm} · n! · ⟨f,Cg⟩^n

### Lean file mapping
- `hermitePoly` (WickProduct.lean:52)
- `wickPower`, `wickFourth` (WickProduct.lean:65,71)
- `wickPower_zero_expectation` (WickProduct.lean:80) -- follows from Hermite orthogonality
- `wickPower_memLp` (WickProduct.lean:88) -- needs c_κ ~ ln κ bound

### Proof strategy for wickPower_zero_expectation
Direct computation: ∫ H_n(φ/√c, c) dφ_C = 0 for n ≥ 1 by the orthogonality of Hermite polynomials under the Gaussian weight. In Lean, this should follow from the integration by parts formula for the Gaussian measure.

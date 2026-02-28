# Chapters 18-19: Cluster Expansion and Reconstruction

## Status Snapshot (2026-02-27)

- `Reconstruction.lean` now has no theorem-level `sorry`.
- Reconstruction assumptions are explicit interfaces:
  `ReconstructionLinearGrowthModel`,
  `ReconstructionWeakCouplingModel`,
  `WightmanReconstructionModel`, and the optional
  `UniformWeakCouplingDecayModel`.
- Endpoints such as `phi4_wightman_exists` are theorem-complete wrappers over
  these interfaces; full constructive closure still depends on grounding
  Chapter-18/19 assumptions (and audited upstream reconstruction backend usage).
- Note: theorem names are the stable lookup key; line numbers can drift.

## 1. Cluster Expansion for Weak Coupling (Section 18.2)

### Setup
Finite-volume Schwinger functions with interpolating covariance:

    C(s) = Σ_{Γ⊂B} [∏_{b∈Γ} s_b] C_Γ

where s_b ∈ [0,1] controls coupling across lattice bond b. At s=1: C = (-Δ+m_0^2)^{-1}. At s=0: C = (-Δ_B+m_0^2)^{-1} (full Dirichlet decoupling).

### Three-step expansion

**(i) FTC (Prop. 18.2.2):**
    F(s) = Σ_{Γ⊂B, finite} ∫_{0≤σ≤s} ∂^Γ F(σ) dσ

**(ii) Factorization:** When s_b = 0 on Γ^c, the measure dφ_{s(Γ)} factorizes over connected components X_1,...,X_r.

**(iii) Resummation:** Fix set of interest X_0. Let X be the connected component meeting X_0. Resum over non-meeting components:
    F(Λ,s) = Σ_X K(X_0,X) F(Λ\X, s(B\X))

### Result: Cluster expansion (Theorem 18.2.5)
    S_Λ(x) = Σ_{X,Γ} ∫ ∂^Γ [∏φ(x_i) e^{-λV(Λ∩X)} dφ_{C(s(Γ))}] ds(Γ) · Z_{∂X}(Λ\X)/Z(Λ)

### Lean file mapping
- `phi4_os4_weak_coupling` (Reconstruction.lean:83) -- the full cluster expansion for OS4

## 2. Clustering / OS4 (Section 18.3)

**Theorem 18.1.1 (Exponential Clustering):** For λ/m_0^6 sufficiently small:
    |∫ AB dμ_Λ - ∫ A dμ_Λ ∫ B dμ_Λ| ≤ M_{A,B} e^{-md}
where d is the width of a strip separating supp A and supp B.

### Proof strategy
The cluster expansion represents S_Λ(x) = Σ_{X,Γ} T(x,Λ,X,Γ).

**Convergence (Thm 18.3.1):** Σ_{|X|≥D} |⟨w,T⟩| ≤ |w| e^{-K(D-n)}.

**For the 2-point function with even P:** The symmetry φ → -φ forces each connected component X to contain an even number of observation points. For n=2, X must contain both x_1 and x_2, so X is connected and |X| ≥ d. Hence: |S_2(x_1,x_2)| ≤ const e^{-Kd}.

**For general P (not necessarily even):** Use **Ginibre's doubling trick**. Introduce doubled theory with field φ - φ* and measure dμ × dμ*. The doubled theory has the even symmetry, so the argument above applies.

### Lean file mapping
- `phi4_os4_weak_coupling` (Reconstruction.lean:83)

### Proof idea for Lean
This is the most complex proof in the entire formalization. It requires:
1. The full cluster expansion machinery (FTC + factorization + resummation)
2. Three convergence estimates (Propositions 18.4.1-3)
3. The doubling trick for general P
4. The weak coupling condition λ/m_0^6 small

A practical approach might be to:
- State the cluster expansion as an intermediate lemma
- State the convergence bound as a hypothesis or intermediate lemma
- Derive the clustering inequality from the convergence bound
- The weak coupling condition enters through the explicit bound on the expansion kernel K

## 3. Convergence Estimates (Sections 18.4-18.7)

### Proposition 18.4.1 (Combinatoric bound)
Number of terms with fixed |X| is ≤ e^{K_1|X|}. (Counting connected lattice graphs.)

### Proposition 18.4.2 (Partition function ratio bound)
For ε small and m_0 large:
    |Z_{∂X}(Λ\X) / Z(Λ)| ≤ e^{K_2|X|}
Proved via Kirkwood-Salsburg equation. The operator K is a contraction with |K| ≤ 3/4.

### Proposition 18.4.3 (Function space integral bound)
The hardest estimate. Each d/ds_b acts via integration by parts, producing kernels C'(s).
Key: ‖∂^Γ C(x,y)‖_{L^q} ≤ O(m_0^{-r|Γ|}) e^{-m_0 d} where d is path length through all b ∈ Γ.

### Wiener integral representation (Section 18.6)
    (∂^γ C(s))(x,y) = ∫_0^∞ e^{-m_0^2 T} ∫ [∏_{b∈γ}(1-χ_b)] [∏_{b∈B\γ}(s_b+(1-s_b)χ_b)] dW^T_{xy} dT

Bounds via strong Markov property:
    ‖∂^γ C‖_{L^q} ≤ K_4(q,γ) m_0^{|γ|/2q} exp(-m_0 d(j,γ))

## 4. OS Reconstruction (Chapter 19)

### Hilbert space and Hamiltonian
From dμ satisfying OS0-OS3:
- H = (E_+ / N)^completion where E_+ = positive time, N = null space of OS inner product
- H ≥ 0 self-adjoint from contraction semigroup e^{-tH}
- Vacuum Ω = [1]^hat, HΩ = 0

### Key propositions
**Prop 19.1.2:** ‖(e^{φ(f)})^hat e^{-tH}‖ ≤ e^{M(2f)/2} and ‖(φ(f)^r)^hat e^{-tH}‖ ≤ (c‖f‖_Y)^r r!^q

**Prop 19.1.3:** Unique bilinear form Φ(h) on H_δ × H_δ satisfying time-smearing.

**Feynman-Kac (Thm 19.2.1):** (e^{-∫_0^t φ(h⊗δ_s) ds})^hat = e^{-tH(h)} with H(h) = H + Φ(h).

**Form boundedness (Cor 19.2.2):** ‖(H+I)^{-1/2} Φ(h) (H+I)^{-1/2}‖ ≤ const ‖h‖

### Lean file mapping
- `phi4_wightman_exists` (Reconstruction.lean:107) -- full reconstruction
- `phi4_linear_growth` (Reconstruction.lean:57) -- prerequisite growth condition

## 5. Self-Adjoint Fields (Section 19.3)

**Theorem 19.3.1:** Under OS0-3, for f ∈ S(R^d)_real, Φ_M(f) is self-adjoint on H, essentially self-adjoint on any core for H.

**Key bounds:**
- ‖(H+1)^{-1/2} Φ_M(f) (H+1)^{-1/2}‖ ≤ const ∫ ‖f_t‖ dt
- Φ_M(f) : D(H^n) → D(H^{n-1})
- e^{itH} Φ_M(f) e^{-itH} = Φ_M(f_t)

**Self-adjointness tools (Section 19.4):**
- Thm 19.4.1: R^{n/2} A R^{n/2} bounded iff AR^n bounded (where R = (H+1)^{-1})
- Thm 19.4.3: Essential self-adjointness on any core for H^n

**Density (Thm 19.3.3):** D = span{Φ_M(f_1)···Φ_M(f_n)Ω} is dense in H.

### Lean file mapping
- `phi4_selfadjoint_fields` mentioned conceptually in Reconstruction.lean

## 6. Locality (Section 19.6)

**Theorem 19.6.1:** Under OS0-3, for f,g with spacelike separated supports:
- [e^{iΦ_M(f)}, e^{iΦ_M(g)}] = 0
- [Φ_M(f), Φ_M(g)]_D = 0
- W_{n+2}(...,f,g,...) = W_{n+2}(...,g,f,...)

### Proof via analytic continuation
1. Euclidean symmetry: S_{n+2}(...,x,y,...) = S_{n+2}(...,y,x,...) (permutation symmetry)
2. Analytic continuation from equal-time (Euclidean) through slit |Im ξ| < |x-y| to pure imaginary ξ = it-is (Minkowski time)
3. Condition |t-s| < |x-y| = spacelike separation
4. Commutator of closures (Thm 19.4.4): [A,B]_D = 0 ⟹ A^{-}, B^{-} commute as self-adjoint operators

### Lean file mapping
- `phi4_locality` mentioned in Reconstruction.lean

## 7. Uniqueness of Vacuum (Section 19.7)

**Theorem 19.7.1:** OS4 ⟺ Ω is unique (up to scalar) under e^{itH}.

**Cluster property:**
    lim_{t→∞} t^{-1} ∫_0^t [⟨A T(s)B⟩ - ⟨A⟩⟨B⟩] ds = 0

By ergodic theorem: st-lim t^{-1} ∫_0^t e^{-sH} ds = P_{inv}. Cluster property says P_{inv} = |Ω⟩⟨Ω|.

**Key structural results:**
- Prop 19.7.4: Under OS2-3, time-invariant functions are reflection invariant: θA = A
- Thm 19.7.5: Under OS2-3, E_1 = E_E (time-translation invariance ⟹ full Euclidean invariance)
- Cor 19.7.6: dμ is Euclidean ergodic iff it is time-translation ergodic

**Decomposition into pure phases (Thm 19.7.7):** dμ = ∫ dμ_ζ dζ where a.e. dμ_ζ satisfies OS0-OS4.

### Lean file mapping
- `phi4_unique_vacuum` (Reconstruction.lean:157)
- `phi4_os4_weak_coupling` (Reconstruction.lean:83) -- provides OS4

### Proof strategy for phi4_unique_vacuum
From the cluster expansion (Thm 18.1.1), we get exponential clustering:
    |⟨AB⟩ - ⟨A⟩⟨B⟩| ≤ M e^{-md}
This immediately implies the cluster property (time-averaged version), hence ergodicity (OS4), hence uniqueness of vacuum (W4).

## 8. Lorentz Covariance (Section 19.5)

The Euclidean rotation invariance of the Schwinger functions (from OS2) analytically continues to give:

1. **Lorentz boost covariance** of Wightman functions
2. **Spectrum condition** |P| ≤ H (follows from Lorentz covariance + positivity of H)

The analytic continuation goes: SO(2) rotation by angle θ in (x_0, x_1) plane → boost by rapidity θ in (t, x) plane when x_0 → it.

### Lean file mapping
- `phi4_lorentz_covariance` mentioned in Reconstruction.lean (with IsWickRotationPair hypothesis)

## Summary: Logical Flow

1. **Cluster expansion** (18.2): S_Λ(x) = Σ_{X,Γ} T(X,Γ)
2. **Convergence** (18.4-18.7): |T| ≤ exp(-K|X|) for λ/m_0^6 small
3. **Clustering** (18.3): Exp decay of connected correlations (OS4)
4. **Infinite volume** (18.1): Uniform bounds ⟹ S_Λ → S
5. **Reconstruction** (19.1-2): OS0-3 ⟹ H, H, Ω, Feynman-Kac
6. **Self-adjoint fields** (19.3): Φ_M(f) essentially self-adjoint
7. **Lorentz covariance** (19.5): Analytic continuation of SO(2)
8. **Locality** (19.6): Analytic continuation of Euclidean permutation symmetry
9. **Vacuum uniqueness** (19.7): Clustering ⟹ ergodicity ⟹ unique Ω

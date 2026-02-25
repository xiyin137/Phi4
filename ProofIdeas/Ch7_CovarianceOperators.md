# Chapter 7: Covariance Operators

## Status Snapshot (2026-02-25)

- Core covariance inequality layer:
  `CovarianceOperators.lean` currently has no `sorry`; it is now organized around the
  `BoundaryCovarianceModel` interface.
- Correlation inequality layer:
  `CorrelationInequalities.lean` currently has no `sorry`; results are exposed via the
  `CorrelationInequalityModel` interface.
- Remaining chapter-adjacent blocker:
  `ReflectionPositivity.lean` still has 3 `sorry`s (free, Dirichlet, and interacting RP).
- Important implementation note:
  uses of `dirichletCov` now require `[BoundaryCovarianceModel mass hmass]`.
- Note:
  line-number references below are historical and may drift; theorem names are the
  stable lookup key.

## 1. Free Covariance (Section 7.2)

C = (-Δ + m^2)^{-1} on R^d. In Fourier space: C_hat(p) = (p^2 + m^2)^{-1}.

**Local singularity (d=2):**
    C(x,y) ~ -(2π)^{-1} ln(m|x-y|)   as |x-y| → 0

**Long-distance decay:**
    C(x,y) ~ const · m^{(d-3)/2} |x-y|^{-(d-1)/2} exp(-m|x-y|)

**Properties (Proposition 7.2.1):**
- (a) C is a positive operator on L^2
- (b) 0 < C(x,y) (strict pointwise positivity)
- (c,d,e) Decay/singularity estimates as above

### Lean file mapping
- `freeCovKernel` (FreeField.lean:144) -- kernel of (-Δ+m^2)^{-1}
- `freeCovKernel_pos_def` (FreeField.lean:155) -- positive definiteness
- `freeCov_exponential_decay` (CovarianceOperators.lean:115) -- exponential decay

### Proof idea for freeCov_exponential_decay
The kernel in d=2 is C(x,y) = K_0(m|x-y|)/(2π) where K_0 is the modified Bessel function. For large argument, K_0(z) ~ √(π/2z) e^{-z}. This gives the exponential decay. In Lean, need to either use Mathlib's Bessel function theory or work with the integral representation C(x,y) = ∫_0^∞ e^{-m^2 t} (4πt)^{-1} exp(-|x-y|^2/(4t)) dt.

## 2. Periodic Boundary Conditions (Section 7.3)

Method of images: C_p(x,y) = Σ_{nL ∈ Z^d} C(x - y + nL)

**Corollary 7.3.2:**
- (a) C_p ≥ 0 as operator
- (b) 0 < C(x,y) < C_p(x,y) (free ≤ periodic)
- (c) Same local singularity

### Lean file mapping
- `periodicCov` (CovarianceOperators.lean:52)

## 3. Neumann Boundary Conditions (Section 7.4)

Method of images with lattice hyperplanes Γ. For Λ a connected component of R^d \ Γ:

    C_N(x,y) = Σ_j C(x - y_j)   for x,y ∈ Λ

where {y_j} are image points of y under reflections in Γ.

**Corollary 7.4.2:**
- (a) C_N ≥ 0
- (b) 0 < C(x,y) < C_N(x,y) for x,y ∈ Λ
- Key: **C ≤ C_N**

### Lean file mapping
- `neumannCov` (CovarianceOperators.lean:46)
- `free_le_neumann` (CovarianceOperators.lean:73)

### Proof idea for free_le_neumann
C ≤ C_N because C_N = C + Σ_{j≥1} C(x - y_j) where y_j are nontrivial image points, and C(x - y_j) > 0 by pointwise positivity. Alternatively, via form domains: D(-Δ_N) ⊃ D(-Δ), so -Δ_N ≤ -Δ, inverting gives C ≤ C_N.

## 4. Dirichlet Boundary Conditions (Section 7.5)

Method of images with alternating signs:

    C_D(x,y) = Σ_j (-1)^{σ_j} C(x - y_j)   for x,y ∈ Λ

where σ_j counts the number of reflections used to produce y_j.

**Corollary 7.5.2:**
- (a) C_D ≥ 0 (as inverse of positive operator)
- (b) 0 ≤ C_D(x,y) < C(x,y)
- Key: **C_D ≤ C**

**Proof of C_D ≤ C:** Maximum principle. f(x) = C(x,y) - C_D(x,y) satisfies (-Δ+m^2)f = 0 in Λ with f > 0 on ∂Λ, so f > 0 everywhere.

### Lean file mapping
- `dirichletCov` (CovarianceOperators.lean:40)
- `dirichlet_le_free` (CovarianceOperators.lean:65)
- `dirichlet_monotone` (CovarianceOperators.lean:81)

### Proof idea for dirichlet_le_free
Two approaches:
1. **Form domain argument:** D(-Δ_Γ) ⊂ D(-Δ) (Dirichlet restricts the variational space), so -Δ ≤ -Δ_Γ, inverting gives C_D = (-Δ_Γ+m^2)^{-1} ≤ (-Δ+m^2)^{-1} = C.
2. **Maximum principle:** As above -- the difference C - C_D is a positive harmonic function on Λ.

For `dirichlet_monotone`: If Λ_1 ⊂ Λ_2, then D(-Δ_{Λ_1}) ⊂ D(-Δ_{Λ_2}), so C_{Λ_1}^D ≤ C_{Λ_2}^D.

## 5. Fundamental Ordering (Section 7.7)

The central result:

    **0 ≤ C_{Γ_2} ≤ C_{Γ_1} ≤ C_D ≤ C ≤ C_N ≤ C_p**

for Γ_1 ⊂ Γ_2 (more Dirichlet data = smaller covariance).

This follows from the form domain inclusions:
    D(-Δ_Γ) ⊂ D(-Δ) ⊂ D(-Δ_N)

and inversion reverses order for positive operators.

## 6. Wick Ordering Constant Shift (Section 7.6)

    δC_B(x) = C_B(x,x) - C(x,x)   (finite difference of infinite quantities)

**Proposition 7.6.1:** For x ∈ Λ:
    0 ≤ δC_D(x) ≤ -δC_N(x) ≤ const(1 + |ln dist(x,∂Λ)|)   for d=2

### Lean file mapping
- `covarianceChange_pointwise_bounded` (CovarianceOperators.lean:98)

### Proof idea
The identity δC_D(x) = -Σ_{j≥1} (-1)^{σ_j} C(x - x_j) combined with |δC_D(x)| ≤ Σ_{j≥1} C(x - x_j) = -δC_N(x). The bound uses the logarithmic singularity of C in d=2.

## 7. Reflection Positivity (Section 7.10)

**Theorem 7.10.1:** Let C = (-Δ_B + 1)^{-1} be θ-invariant. Then C is reflection-positive.

**Key equivalence:**
    RP ⟺ C_D ≤ C ⟺ C ≤ C_N'

where C_D has Dirichlet data on the reflection hyperplane and C_N' has Neumann data on it.

**Proof:** RP condition 0 ≤ Π_+ θ C Π_+ is equivalent to 0 ≤ Π_+ (C - C_D) Π_+, which holds since C_D ≤ C.

### Lean file mapping
- `free_covariance_reflection_positive` (ReflectionPositivity.lean:65)
- `dirichlet_covariance_reflection_positive` (ReflectionPositivity.lean:82)

### Proof strategy
The equivalence RP ⟺ C_D ≤ C is the key insight. Once dirichlet_le_free is proved, reflection positivity of the free covariance follows. For the Dirichlet covariance itself, note that adding more Dirichlet data (on the reflection plane) only decreases the covariance further, so C_D^{D'} ≤ C_D where D' is the reflection plane.

## 8. Local Regularity (Section 7.9)

For d=2, C ∈ C_m (the convex class of covariances):

**(LR1):** sup_x ‖(ζCζ)(x,·)‖_{L^q} < ∞ for all q < ∞

**(LR2):** ‖ζ δ_κ C δ_κ ζ - ζCζ‖_{L^q} ≤ O(κ^{-ε}) as κ → ∞

**(LR3):** ‖δ_κ C δ_κ - ζCζ‖_{L^q} ≤ O(κ^{-ε})

These hold uniformly over C_m. Important for the UV cutoff removal in Chapter 8.

### Lean file mapping
- `regularizedPointCovariance` (FreeField.lean:161)
- `regularizedPointCovariance_log_divergence` (FreeField.lean:167)
- `dirichletCov_smooth_off_diagonal` (CovarianceOperators.lean:107)

### Proof idea for log divergence
c_κ(x) = C_κ(x,x) = ∫ |h_hat(p/κ)|^2 / (p^2 + m^2) dp/(2π)^2. Splitting into |p| ≤ κ and |p| > κ: the first integral contributes ~ (2π)^{-1} ln(κ/m) and the second is O(1). This gives c_κ ~ (2π)^{-1} ln κ.

/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.FreeField

/-!
# Covariance Operators with Boundary Conditions

Different boundary conditions on a region Λ ⊂ ℝ² give different covariance operators,
all of which are positive and related by operator inequalities. The key boundary conditions
are Dirichlet (vanishing on ∂Λ), Neumann (vanishing normal derivative), and periodic.

The fundamental ordering C_D ≤ C ≤ C_N (Dirichlet ≤ free ≤ Neumann) is crucial for
the monotone convergence arguments in the infinite volume limit.

## Main definitions

* `dirichletCov` — Dirichlet covariance C_Λ^D (vanishing BC on ∂Λ)
* `neumannCov` — Neumann covariance C_Λ^N
* `periodicCov` — Periodic covariance on a rectangle

## References

* [Glimm-Jaffe] Chapter 7, especially Sections 7.3-7.10
-/

noncomputable section

open MeasureTheory

/-! ## Covariance operators with boundary conditions -/

/-- The Dirichlet covariance C_Λ^D = (-Δ_D + m²)⁻¹ on Λ, where Δ_D is the
    Laplacian with Dirichlet boundary conditions (functions vanishing on ∂Λ).
    As a bilinear form: C_D(f,g) = ∫∫ f(x) G_D(x,y) g(y) dx dy
    where G_D is the Dirichlet Green's function on Λ. -/
def dirichletCov (Λ : Rectangle) (mass : ℝ) (hmass : 0 < mass)
    (x y : Spacetime2D) : ℝ := by
  sorry

/-- The Neumann covariance C_Λ^N = (-Δ_N + m²)⁻¹ on Λ, where Δ_N is the
    Laplacian with Neumann boundary conditions (vanishing normal derivative on ∂Λ). -/
def neumannCov (Λ : Rectangle) (mass : ℝ) (hmass : 0 < mass)
    (x y : Spacetime2D) : ℝ := by
  sorry

/-- The periodic covariance on a rectangle Λ = [0,L₁] × [0,L₂].
    The eigenvalues are (2πn₁/L₁)² + (2πn₂/L₂)² + m². -/
def periodicCov (L₁ L₂ mass : ℝ) (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) (hmass : 0 < mass)
    (x y : Spacetime2D) : ℝ := by
  sorry

/-! ## Covariance operator inequalities

The fundamental ordering: C_D ≤ C ≤ C_N as bilinear forms.
This follows from the min-max characterization of eigenvalues. -/

/-- Dirichlet ≤ free covariance: C_D(f,f) ≤ C(f,f) for all f supported in Λ.
    This is because Dirichlet conditions restrict the variational space. -/
theorem dirichlet_le_free (Λ : Rectangle) (mass : ℝ) (hmass : 0 < mass)
    (f : TestFun2D) (hf : ∀ x ∉ Λ.toSet, f x = 0) :
    ∫ x, ∫ y, f x * dirichletCov Λ mass hmass x y * f y ≤
      ∫ x, ∫ y, f x * freeCovKernel mass x y * f y := by
  sorry

/-- Free ≤ Neumann covariance: C(f,f) ≤ C_N(f,f) for all f supported in Λ.
    Neumann conditions enlarge the variational space. -/
theorem free_le_neumann (Λ : Rectangle) (mass : ℝ) (hmass : 0 < mass)
    (f : TestFun2D) (hf : ∀ x ∉ Λ.toSet, f x = 0) :
    ∫ x, ∫ y, f x * freeCovKernel mass x y * f y ≤
      ∫ x, ∫ y, f x * neumannCov Λ mass hmass x y * f y := by
  sorry

/-- Dirichlet monotonicity: If Λ₁ ⊂ Λ₂, then C_{Λ₁}^D ≤ C_{Λ₂}^D.
    Enlarging the domain relaxes the Dirichlet constraint. -/
theorem dirichlet_monotone (Λ₁ Λ₂ : Rectangle) (mass : ℝ) (hmass : 0 < mass)
    (h : Λ₁.toSet ⊆ Λ₂.toSet) (f : TestFun2D) (hf : ∀ x ∉ Λ₁.toSet, f x = 0) :
    ∫ x, ∫ y, f x * dirichletCov Λ₁ mass hmass x y * f y ≤
      ∫ x, ∫ y, f x * dirichletCov Λ₂ mass hmass x y * f y := by
  sorry

/-! ## Change of boundary conditions

The difference δC = C - C_D between free and Dirichlet covariances is controlled.
In d=2, the pointwise "mass" δc(x) = δC(x,x) satisfies |δc(x)| ≤ const. -/

/-- The change-of-covariance kernel δC = C - C_D. -/
def covarianceChange (Λ : Rectangle) (mass : ℝ) (hmass : 0 < mass)
    (x y : Spacetime2D) : ℝ :=
  freeCovKernel mass x y - dirichletCov Λ mass hmass x y

/-- The pointwise covariance change δc(x) = δC(x,x) is bounded.
    This is crucial for the re-Wick-ordering estimates in d=2 (Glimm-Jaffe 7.6). -/
theorem covarianceChange_pointwise_bounded (Λ : Rectangle) (mass : ℝ) (hmass : 0 < mass) :
    ∃ C : ℝ, ∀ x : Spacetime2D, x ∈ Λ.toSet →
      |covarianceChange Λ mass hmass x x| ≤ C := by
  sorry

/-! ## Regularity of covariance kernels -/

/-- The Dirichlet covariance kernel is smooth off the diagonal. -/
theorem dirichletCov_smooth_off_diagonal (Λ : Rectangle) (mass : ℝ) (hmass : 0 < mass) :
    ∀ x y : Spacetime2D, x ≠ y → x ∈ Λ.toSet → y ∈ Λ.toSet →
      DifferentiableAt ℝ (fun p : Spacetime2D × Spacetime2D =>
        dirichletCov Λ mass hmass p.1 p.2) (x, y) := by
  sorry

/-- The free covariance kernel decays exponentially:
    |C(x,y)| ≤ const × e^{-m|x-y|} for |x-y| ≥ 1. -/
theorem freeCov_exponential_decay (mass : ℝ) (hmass : 0 < mass) :
    ∃ C₁ C₂ : ℝ, 0 < C₂ ∧
      ∀ x y : Spacetime2D, 1 ≤ ‖x - y‖ →
        |freeCovKernel mass x y| ≤ C₁ * Real.exp (-C₂ * ‖x - y‖) := by
  sorry

end

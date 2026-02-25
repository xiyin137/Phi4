/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.FreeField
import Phi4.Bessel.BesselK0

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

/-- Abstract interface for boundary-condition covariance kernels at fixed `mass`.
    This isolates the PDE-heavy Green kernel construction from the downstream
    correlation/reflection/infinite-volume arguments. -/
class BoundaryCovarianceModel (mass : ℝ) (hmass : 0 < mass) where
  /-- Dirichlet kernel on a rectangle. -/
  dirichletKernel : Rectangle → Spacetime2D → Spacetime2D → ℝ
  /-- Neumann kernel on a rectangle. -/
  neumannKernel : Rectangle → Spacetime2D → Spacetime2D → ℝ
  /-- Periodic kernel on `[0,L₁] × [0,L₂]`. -/
  periodicKernel : (L₁ L₂ : ℝ) → 0 < L₁ → 0 < L₂ → Spacetime2D → Spacetime2D → ℝ
  /-- Dirichlet ≤ free quadratic form comparison for functions supported in `Λ`. -/
  dirichlet_le_free : ∀ (Λ : Rectangle) (f : TestFun2D)
      (_hf : ∀ x ∉ Λ.toSet, f x = 0),
      ∫ x, ∫ y, f x * dirichletKernel Λ x y * f y ≤
        ∫ x, ∫ y, f x * freeCovKernel mass x y * f y
  /-- Free ≤ Neumann quadratic form comparison for functions supported in `Λ`. -/
  free_le_neumann : ∀ (Λ : Rectangle) (f : TestFun2D)
      (_hf : ∀ x ∉ Λ.toSet, f x = 0),
      ∫ x, ∫ y, f x * freeCovKernel mass x y * f y ≤
        ∫ x, ∫ y, f x * neumannKernel Λ x y * f y
  /-- Domain monotonicity for Dirichlet kernels. -/
  dirichlet_monotone : ∀ (Λ₁ Λ₂ : Rectangle) (_h : Λ₁.toSet ⊆ Λ₂.toSet)
      (f : TestFun2D) (_hf : ∀ x ∉ Λ₁.toSet, f x = 0),
      ∫ x, ∫ y, f x * dirichletKernel Λ₁ x y * f y ≤
        ∫ x, ∫ y, f x * dirichletKernel Λ₂ x y * f y
  /-- Pointwise bound on covariance change along the diagonal in `Λ`. -/
  covarianceChange_pointwise_bounded : ∀ (Λ : Rectangle),
      ∃ C : ℝ, ∀ x : Spacetime2D, x ∈ Λ.toSet →
        |(freeCovKernel mass x x - dirichletKernel Λ x x)| ≤ C
  /-- Off-diagonal smoothness of the Dirichlet kernel on `Λ`. -/
  dirichlet_smooth_off_diagonal : ∀ (Λ : Rectangle),
      ∀ x y : Spacetime2D, x ≠ y → x ∈ Λ.toSet → y ∈ Λ.toSet →
        DifferentiableAt ℝ (fun p : Spacetime2D × Spacetime2D =>
          dirichletKernel Λ p.1 p.2) (x, y)

/-- The Dirichlet covariance C_Λ^D = (-Δ_D + m²)⁻¹ on Λ, supplied by
    `BoundaryCovarianceModel`. -/
def dirichletCov (Λ : Rectangle) (mass : ℝ) (hmass : 0 < mass)
    [BoundaryCovarianceModel mass hmass] (x y : Spacetime2D) : ℝ :=
  BoundaryCovarianceModel.dirichletKernel (mass := mass) (hmass := hmass) Λ x y

/-- The Neumann covariance C_Λ^N = (-Δ_N + m²)⁻¹ on Λ, supplied by
    `BoundaryCovarianceModel`. -/
def neumannCov (Λ : Rectangle) (mass : ℝ) (hmass : 0 < mass)
    [BoundaryCovarianceModel mass hmass] (x y : Spacetime2D) : ℝ :=
  BoundaryCovarianceModel.neumannKernel (mass := mass) (hmass := hmass) Λ x y

/-- The periodic covariance on `[0,L₁] × [0,L₂]`, supplied by
    `BoundaryCovarianceModel`. -/
def periodicCov (L₁ L₂ mass : ℝ) (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) (hmass : 0 < mass)
    [BoundaryCovarianceModel mass hmass] (x y : Spacetime2D) : ℝ :=
  BoundaryCovarianceModel.periodicKernel (mass := mass) (hmass := hmass) L₁ L₂ hL₁ hL₂ x y

/-! ## Covariance operator inequalities

The fundamental ordering: C_D ≤ C ≤ C_N as bilinear forms.
This follows from the min-max characterization of eigenvalues. -/

/-- Dirichlet ≤ free covariance: C_D(f,f) ≤ C(f,f) for all f supported in Λ.
    This is because Dirichlet conditions restrict the variational space. -/
theorem dirichlet_le_free (Λ : Rectangle) (mass : ℝ) (hmass : 0 < mass)
    [BoundaryCovarianceModel mass hmass]
    (f : TestFun2D) (hf : ∀ x ∉ Λ.toSet, f x = 0) :
    ∫ x, ∫ y, f x * dirichletCov Λ mass hmass x y * f y ≤
      ∫ x, ∫ y, f x * freeCovKernel mass x y * f y := by
  simpa [dirichletCov] using
    (BoundaryCovarianceModel.dirichlet_le_free (mass := mass) (hmass := hmass) Λ f hf)

/-- Free ≤ Neumann covariance: C(f,f) ≤ C_N(f,f) for all f supported in Λ.
    Neumann conditions enlarge the variational space. -/
theorem free_le_neumann (Λ : Rectangle) (mass : ℝ) (hmass : 0 < mass)
    [BoundaryCovarianceModel mass hmass]
    (f : TestFun2D) (hf : ∀ x ∉ Λ.toSet, f x = 0) :
    ∫ x, ∫ y, f x * freeCovKernel mass x y * f y ≤
      ∫ x, ∫ y, f x * neumannCov Λ mass hmass x y * f y := by
  simpa [neumannCov] using
    (BoundaryCovarianceModel.free_le_neumann (mass := mass) (hmass := hmass) Λ f hf)

/-- Dirichlet monotonicity: If Λ₁ ⊂ Λ₂, then C_{Λ₁}^D ≤ C_{Λ₂}^D.
    Enlarging the domain relaxes the Dirichlet constraint. -/
theorem dirichlet_monotone (Λ₁ Λ₂ : Rectangle) (mass : ℝ) (hmass : 0 < mass)
    [BoundaryCovarianceModel mass hmass]
    (h : Λ₁.toSet ⊆ Λ₂.toSet) (f : TestFun2D) (hf : ∀ x ∉ Λ₁.toSet, f x = 0) :
    ∫ x, ∫ y, f x * dirichletCov Λ₁ mass hmass x y * f y ≤
      ∫ x, ∫ y, f x * dirichletCov Λ₂ mass hmass x y * f y := by
  simpa [dirichletCov] using
    (BoundaryCovarianceModel.dirichlet_monotone (mass := mass) (hmass := hmass) Λ₁ Λ₂ h f hf)

/-! ## Change of boundary conditions

The difference δC = C - C_D between free and Dirichlet covariances is controlled.
In d=2, the pointwise "mass" δc(x) = δC(x,x) satisfies |δc(x)| ≤ const. -/

/-- The change-of-covariance kernel δC = C - C_D. -/
def covarianceChange (Λ : Rectangle) (mass : ℝ) (hmass : 0 < mass)
    [BoundaryCovarianceModel mass hmass]
    (x y : Spacetime2D) : ℝ :=
  freeCovKernel mass x y - dirichletCov Λ mass hmass x y

/-- The pointwise covariance change δc(x) = δC(x,x) is bounded.
    This is crucial for the re-Wick-ordering estimates in d=2 (Glimm-Jaffe 7.6). -/
theorem covarianceChange_pointwise_bounded (Λ : Rectangle) (mass : ℝ) (hmass : 0 < mass)
    [BoundaryCovarianceModel mass hmass] :
    ∃ C : ℝ, ∀ x : Spacetime2D, x ∈ Λ.toSet →
      |covarianceChange Λ mass hmass x x| ≤ C := by
  simpa [covarianceChange, dirichletCov] using
    (BoundaryCovarianceModel.covarianceChange_pointwise_bounded
      (mass := mass) (hmass := hmass) Λ)

/-! ## Regularity of covariance kernels -/

/-- The Dirichlet covariance kernel is smooth off the diagonal. -/
theorem dirichletCov_smooth_off_diagonal (Λ : Rectangle) (mass : ℝ) (hmass : 0 < mass)
    [BoundaryCovarianceModel mass hmass] :
    ∀ x y : Spacetime2D, x ≠ y → x ∈ Λ.toSet → y ∈ Λ.toSet →
      DifferentiableAt ℝ (fun p : Spacetime2D × Spacetime2D =>
        dirichletCov Λ mass hmass p.1 p.2) (x, y) := by
  simpa [dirichletCov] using
    (BoundaryCovarianceModel.dirichlet_smooth_off_diagonal
      (mass := mass) (hmass := hmass) Λ)

/-- Rewrite the free covariance kernel using the 2D Schwinger integral identity. -/
private lemma freeCovKernel_eq_besselK0
    (mass : ℝ) (hmass : 0 < mass) (x y : Spacetime2D)
    (hxy : 0 < ‖x - y‖) :
    freeCovKernel mass x y = (2 * Real.pi)⁻¹ * besselK0 (mass * ‖x - y‖) := by
  have hsch :
      ∫ t in Set.Ioi (0 : ℝ), (1 / t) * Real.exp (-mass ^ 2 * t - ‖x - y‖ ^ 2 / (4 * t))
        = 2 * besselK0 (mass * ‖x - y‖) :=
    schwingerIntegral2D_eq_besselK0 mass ‖x - y‖ hmass hxy
  unfold freeCovKernel
  calc
    ∫ t in Set.Ioi (0 : ℝ), (4 * Real.pi * t)⁻¹ *
        Real.exp (-(mass ^ 2 * t + ‖x - y‖ ^ 2 / (4 * t)))
        = (4 * Real.pi)⁻¹ *
            (∫ t in Set.Ioi (0 : ℝ), (1 / t) *
              Real.exp (-mass ^ 2 * t - ‖x - y‖ ^ 2 / (4 * t))) := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with t
          ring_nf
    _ = (4 * Real.pi)⁻¹ * (2 * besselK0 (mass * ‖x - y‖)) := by rw [hsch]
    _ = (2 * Real.pi)⁻¹ * besselK0 (mass * ‖x - y‖) := by ring

/-- The free covariance kernel decays exponentially:
    |C(x,y)| ≤ const × e^{-m|x-y|} for |x-y| ≥ 1. -/
theorem freeCov_exponential_decay (mass : ℝ) (hmass : 0 < mass) :
    ∃ C₁ C₂ : ℝ, 0 < C₂ ∧
      ∀ x y : Spacetime2D, 1 ≤ ‖x - y‖ →
        |freeCovKernel mass x y| ≤ C₁ * Real.exp (-C₂ * ‖x - y‖) := by
  let C₂ : ℝ := mass
  let A : ℝ := (2 * Real.pi)⁻¹ * (Real.sinh 1 + 2)
  let B0 : ℝ := (2 * Real.pi)⁻¹ * ((Real.cosh 1 + 2) / mass)
  let B : ℝ := B0 * Real.exp 1
  let C₁ : ℝ := max A B
  refine ⟨C₁, C₂, by simpa [C₂] using hmass, ?_⟩
  intro x y hxy1
  have hxy_pos : 0 < ‖x - y‖ := lt_of_lt_of_le zero_lt_one hxy1
  have hrepr := freeCovKernel_eq_besselK0 mass hmass x y hxy_pos
  have hnonneg : 0 ≤ freeCovKernel mass x y := by
    rw [hrepr]
    have hK0_nonneg : 0 ≤ besselK0 (mass * ‖x - y‖) :=
      (besselK0_pos _ (mul_pos hmass hxy_pos)).le
    positivity
  rw [abs_of_nonneg hnonneg, hrepr]
  by_cases hlarge : 1 ≤ mass * ‖x - y‖
  · have hK0_le : besselK0 (mass * ‖x - y‖) ≤
        (Real.sinh 1 + 2) * Real.exp (-(mass * ‖x - y‖)) := by
      calc
        besselK0 (mass * ‖x - y‖) ≤ besselK1 (mass * ‖x - y‖) :=
          besselK0_le_besselK1 _ (mul_pos hmass hxy_pos)
        _ ≤ (Real.sinh 1 + 2) * Real.exp (-(mass * ‖x - y‖)) :=
          besselK1_asymptotic _ hlarge
    have hmain : (2 * Real.pi)⁻¹ * besselK0 (mass * ‖x - y‖) ≤
        A * Real.exp (-(mass * ‖x - y‖)) := by
      calc
        (2 * Real.pi)⁻¹ * besselK0 (mass * ‖x - y‖)
            ≤ (2 * Real.pi)⁻¹ * ((Real.sinh 1 + 2) * Real.exp (-(mass * ‖x - y‖))) :=
              mul_le_mul_of_nonneg_left hK0_le (by positivity)
        _ = A * Real.exp (-(mass * ‖x - y‖)) := by
              unfold A
              ring
    have hC1A : A ≤ C₁ := by
      unfold C₁
      exact le_max_left A B
    have hC1exp : A * Real.exp (-(mass * ‖x - y‖)) ≤
        C₁ * Real.exp (-(mass * ‖x - y‖)) :=
      mul_le_mul_of_nonneg_right hC1A (Real.exp_nonneg _)
    simpa [C₂] using le_trans hmain hC1exp
  · have hsmall : mass * ‖x - y‖ ≤ 1 := le_of_not_ge hlarge
    have hmxy_pos : 0 < mass * ‖x - y‖ := mul_pos hmass hxy_pos
    have hK1_near : besselK1 (mass * ‖x - y‖) ≤
        (Real.cosh 1 + 2) / (mass * ‖x - y‖) :=
      besselK1_near_origin_bound _ hmxy_pos hsmall
    have hK0_bound : besselK0 (mass * ‖x - y‖) ≤
        (Real.cosh 1 + 2) / (mass * ‖x - y‖) :=
      le_trans (besselK0_le_besselK1 _ hmxy_pos) hK1_near
    have hmr_ge_m : mass ≤ mass * ‖x - y‖ := by
      nlinarith [hmass, hxy1]
    have h_inv_norm : 1 / (mass * ‖x - y‖) ≤ 1 / mass :=
      one_div_le_one_div_of_le hmass hmr_ge_m
    have hK0_B0 : (2 * Real.pi)⁻¹ * besselK0 (mass * ‖x - y‖) ≤ B0 := by
      calc
        (2 * Real.pi)⁻¹ * besselK0 (mass * ‖x - y‖)
            ≤ (2 * Real.pi)⁻¹ * ((Real.cosh 1 + 2) / (mass * ‖x - y‖)) :=
              mul_le_mul_of_nonneg_left hK0_bound (by positivity)
        _ = (2 * Real.pi)⁻¹ * (Real.cosh 1 + 2) * (1 / (mass * ‖x - y‖)) := by ring
        _ ≤ (2 * Real.pi)⁻¹ * (Real.cosh 1 + 2) * (1 / mass) :=
              mul_le_mul_of_nonneg_left h_inv_norm (by positivity)
        _ = B0 := by
              unfold B0
              ring
    have harg_nonneg : 0 ≤ 1 - mass * ‖x - y‖ := by linarith
    have hExp_ge_one : (1 : ℝ) ≤ Real.exp 1 * Real.exp (-(mass * ‖x - y‖)) := by
      calc
        (1 : ℝ) ≤ Real.exp (1 - mass * ‖x - y‖) := by
          exact (Real.one_le_exp_iff).2 harg_nonneg
        _ = Real.exp 1 * Real.exp (-(mass * ‖x - y‖)) := by
          rw [← Real.exp_add]
          ring
    have hBexp : B0 ≤ B * Real.exp (-(mass * ‖x - y‖)) := by
      unfold B
      calc
        B0 = B0 * 1 := by ring
        _ ≤ B0 * (Real.exp 1 * Real.exp (-(mass * ‖x - y‖))) :=
              mul_le_mul_of_nonneg_left hExp_ge_one (by positivity)
        _ = B * Real.exp (-(mass * ‖x - y‖)) := by ring
    have hC1B : B ≤ C₁ := by
      unfold C₁
      exact le_max_right A B
    have hC1exp : B * Real.exp (-(mass * ‖x - y‖)) ≤
        C₁ * Real.exp (-(mass * ‖x - y‖)) :=
      mul_le_mul_of_nonneg_right hC1B (Real.exp_nonneg _)
    have hfinal : (2 * Real.pi)⁻¹ * besselK0 (mass * ‖x - y‖) ≤
        C₁ * Real.exp (-(mass * ‖x - y‖)) :=
      le_trans hK0_B0 (le_trans hBexp hC1exp)
    simpa [C₂] using hfinal

end

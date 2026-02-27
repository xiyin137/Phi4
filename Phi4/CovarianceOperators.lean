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

/-- Minimal kernel data for boundary-condition covariance operators. -/
class BoundaryKernelModel (mass : ℝ) (hmass : 0 < mass) where
  dirichletKernel : Rectangle → Spacetime2D → Spacetime2D → ℝ
  neumannKernel : Rectangle → Spacetime2D → Spacetime2D → ℝ
  periodicKernel : (L₁ L₂ : ℝ) → 0 < L₁ → 0 < L₂ → Spacetime2D → Spacetime2D → ℝ

/-- Quadratic-form comparison input for boundary covariances. -/
class BoundaryComparisonModel (mass : ℝ) (hmass : 0 < mass)
    [BoundaryKernelModel mass hmass] where
  dirichlet_le_free : ∀ (Λ : Rectangle) (f : TestFun2D)
      (_hf : ∀ x ∉ Λ.toSet, f x = 0),
      ∫ x, ∫ y, f x *
        BoundaryKernelModel.dirichletKernel (mass := mass) (hmass := hmass) Λ x y * f y ≤
        ∫ x, ∫ y, f x * freeCovKernel mass x y * f y
  free_le_neumann : ∀ (Λ : Rectangle) (f : TestFun2D)
      (_hf : ∀ x ∉ Λ.toSet, f x = 0),
      ∫ x, ∫ y, f x * freeCovKernel mass x y * f y ≤
        ∫ x, ∫ y, f x *
          BoundaryKernelModel.neumannKernel (mass := mass) (hmass := hmass) Λ x y * f y
  dirichlet_monotone : ∀ (Λ₁ Λ₂ : Rectangle) (_h : Λ₁.toSet ⊆ Λ₂.toSet)
      (f : TestFun2D) (_hf : ∀ x ∉ Λ₁.toSet, f x = 0),
      ∫ x, ∫ y, f x *
        BoundaryKernelModel.dirichletKernel (mass := mass) (hmass := hmass) Λ₁ x y * f y ≤
        ∫ x, ∫ y, f x *
          BoundaryKernelModel.dirichletKernel (mass := mass) (hmass := hmass) Λ₂ x y * f y

/-- Regularity input for boundary covariances. -/
class BoundaryRegularityModel (mass : ℝ) (hmass : 0 < mass)
    [BoundaryKernelModel mass hmass] where
  covarianceChange_pointwise_bounded : ∀ (Λ : Rectangle),
      ∃ C : ℝ, ∀ x : Spacetime2D, x ∈ Λ.toSet →
        |(freeCovKernel mass x x -
          BoundaryKernelModel.dirichletKernel (mass := mass) (hmass := hmass) Λ x x)| ≤ C
  dirichlet_smooth_off_diagonal : ∀ (Λ : Rectangle),
      ∀ x y : Spacetime2D, x ≠ y → x ∈ Λ.toSet → y ∈ Λ.toSet →
        DifferentiableAt ℝ (fun p : Spacetime2D × Spacetime2D =>
          BoundaryKernelModel.dirichletKernel (mass := mass) (hmass := hmass) Λ p.1 p.2) (x, y)

/-- Construct `BoundaryKernelModel` from explicit Dirichlet/Neumann/periodic
    kernel data. -/
theorem boundaryKernelModel_nonempty_of_data (mass : ℝ) (hmass : 0 < mass)
    (kD : Rectangle → Spacetime2D → Spacetime2D → ℝ)
    (kN : Rectangle → Spacetime2D → Spacetime2D → ℝ)
    (kP : (L₁ L₂ : ℝ) → 0 < L₁ → 0 < L₂ → Spacetime2D → Spacetime2D → ℝ) :
    Nonempty (BoundaryKernelModel mass hmass) := by
  exact ⟨{
    dirichletKernel := kD
    neumannKernel := kN
    periodicKernel := kP
  }⟩

/-- Construct `BoundaryComparisonModel` from explicit quadratic-form
    comparison inequalities. -/
theorem boundaryComparisonModel_nonempty_of_data
    (mass : ℝ) (hmass : 0 < mass)
    [BoundaryKernelModel mass hmass]
    (hdir : ∀ (Λ : Rectangle) (f : TestFun2D)
      (_hf : ∀ x ∉ Λ.toSet, f x = 0),
      ∫ x, ∫ y, f x *
        BoundaryKernelModel.dirichletKernel (mass := mass) (hmass := hmass) Λ x y * f y ≤
        ∫ x, ∫ y, f x * freeCovKernel mass x y * f y)
    (hfree : ∀ (Λ : Rectangle) (f : TestFun2D)
      (_hf : ∀ x ∉ Λ.toSet, f x = 0),
      ∫ x, ∫ y, f x * freeCovKernel mass x y * f y ≤
        ∫ x, ∫ y, f x *
          BoundaryKernelModel.neumannKernel (mass := mass) (hmass := hmass) Λ x y * f y)
    (hmono : ∀ (Λ₁ Λ₂ : Rectangle) (_h : Λ₁.toSet ⊆ Λ₂.toSet)
      (f : TestFun2D) (_hf : ∀ x ∉ Λ₁.toSet, f x = 0),
      ∫ x, ∫ y, f x *
        BoundaryKernelModel.dirichletKernel (mass := mass) (hmass := hmass) Λ₁ x y * f y ≤
        ∫ x, ∫ y, f x *
          BoundaryKernelModel.dirichletKernel (mass := mass) (hmass := hmass) Λ₂ x y * f y) :
    Nonempty (BoundaryComparisonModel mass hmass) := by
  exact ⟨{
    dirichlet_le_free := hdir
    free_le_neumann := hfree
    dirichlet_monotone := hmono
  }⟩

/-- Construct `BoundaryRegularityModel` from explicit covariance-change bounds
    and off-diagonal smoothness data. -/
theorem boundaryRegularityModel_nonempty_of_data
    (mass : ℝ) (hmass : 0 < mass)
    [BoundaryKernelModel mass hmass]
    (hchange : ∀ (Λ : Rectangle),
      ∃ C : ℝ, ∀ x : Spacetime2D, x ∈ Λ.toSet →
        |(freeCovKernel mass x x -
          BoundaryKernelModel.dirichletKernel (mass := mass) (hmass := hmass) Λ x x)| ≤ C)
    (hsmooth : ∀ (Λ : Rectangle),
      ∀ x y : Spacetime2D, x ≠ y → x ∈ Λ.toSet → y ∈ Λ.toSet →
        DifferentiableAt ℝ (fun p : Spacetime2D × Spacetime2D =>
          BoundaryKernelModel.dirichletKernel (mass := mass) (hmass := hmass) Λ p.1 p.2) (x, y)) :
    Nonempty (BoundaryRegularityModel mass hmass) := by
  exact ⟨{
    covarianceChange_pointwise_bounded := hchange
    dirichlet_smooth_off_diagonal := hsmooth
  }⟩

/-- Construct `BoundaryCovarianceModel` from explicit kernel, comparison, and
    regularity data. -/
theorem boundaryCovarianceModel_nonempty_of_data
    (mass : ℝ) (hmass : 0 < mass)
    (kD : Rectangle → Spacetime2D → Spacetime2D → ℝ)
    (kN : Rectangle → Spacetime2D → Spacetime2D → ℝ)
    (kP : (L₁ L₂ : ℝ) → 0 < L₁ → 0 < L₂ → Spacetime2D → Spacetime2D → ℝ)
    (hdir : ∀ (Λ : Rectangle) (f : TestFun2D)
      (_hf : ∀ x ∉ Λ.toSet, f x = 0),
      ∫ x, ∫ y, f x * kD Λ x y * f y ≤
        ∫ x, ∫ y, f x * freeCovKernel mass x y * f y)
    (hfree : ∀ (Λ : Rectangle) (f : TestFun2D)
      (_hf : ∀ x ∉ Λ.toSet, f x = 0),
      ∫ x, ∫ y, f x * freeCovKernel mass x y * f y ≤
        ∫ x, ∫ y, f x * kN Λ x y * f y)
    (hmono : ∀ (Λ₁ Λ₂ : Rectangle) (_h : Λ₁.toSet ⊆ Λ₂.toSet)
      (f : TestFun2D) (_hf : ∀ x ∉ Λ₁.toSet, f x = 0),
      ∫ x, ∫ y, f x * kD Λ₁ x y * f y ≤
        ∫ x, ∫ y, f x * kD Λ₂ x y * f y)
    (hchange : ∀ (Λ : Rectangle),
      ∃ C : ℝ, ∀ x : Spacetime2D, x ∈ Λ.toSet →
        |(freeCovKernel mass x x - kD Λ x x)| ≤ C)
    (hsmooth : ∀ (Λ : Rectangle),
      ∀ x y : Spacetime2D, x ≠ y → x ∈ Λ.toSet → y ∈ Λ.toSet →
        DifferentiableAt ℝ (fun p : Spacetime2D × Spacetime2D =>
          kD Λ p.1 p.2) (x, y)) :
    Nonempty (BoundaryCovarianceModel mass hmass) := by
  exact ⟨{
    dirichletKernel := kD
    neumannKernel := kN
    periodicKernel := kP
    dirichlet_le_free := hdir
    free_le_neumann := hfree
    dirichlet_monotone := hmono
    covarianceChange_pointwise_bounded := hchange
    dirichlet_smooth_off_diagonal := hsmooth
  }⟩

/-- Any full boundary covariance model provides the kernel subinterface. -/
instance (priority := 100) boundaryKernelModel_of_covariance
    (mass : ℝ) (hmass : 0 < mass)
    [BoundaryCovarianceModel mass hmass] :
    BoundaryKernelModel mass hmass where
  dirichletKernel := BoundaryCovarianceModel.dirichletKernel (mass := mass) (hmass := hmass)
  neumannKernel := BoundaryCovarianceModel.neumannKernel (mass := mass) (hmass := hmass)
  periodicKernel := BoundaryCovarianceModel.periodicKernel (mass := mass) (hmass := hmass)

/-- Any full boundary covariance model provides the comparison subinterface. -/
instance (priority := 100) boundaryComparisonModel_of_covariance
    (mass : ℝ) (hmass : 0 < mass)
    [BoundaryCovarianceModel mass hmass] :
    BoundaryComparisonModel mass hmass where
  dirichlet_le_free :=
    BoundaryCovarianceModel.dirichlet_le_free (mass := mass) (hmass := hmass)
  free_le_neumann :=
    BoundaryCovarianceModel.free_le_neumann (mass := mass) (hmass := hmass)
  dirichlet_monotone :=
    BoundaryCovarianceModel.dirichlet_monotone (mass := mass) (hmass := hmass)

/-- Any full boundary covariance model provides the regularity subinterface. -/
instance (priority := 100) boundaryRegularityModel_of_covariance
    (mass : ℝ) (hmass : 0 < mass)
    [BoundaryCovarianceModel mass hmass] :
    BoundaryRegularityModel mass hmass where
  covarianceChange_pointwise_bounded :=
    BoundaryCovarianceModel.covarianceChange_pointwise_bounded (mass := mass) (hmass := hmass)
  dirichlet_smooth_off_diagonal :=
    BoundaryCovarianceModel.dirichlet_smooth_off_diagonal (mass := mass) (hmass := hmass)

/-- The three boundary-covariance subinterfaces reconstruct the original
    `BoundaryCovarianceModel`. -/
instance (priority := 100) boundaryCovarianceModel_of_submodels
    (mass : ℝ) (hmass : 0 < mass)
    [BoundaryKernelModel mass hmass]
    [BoundaryComparisonModel mass hmass]
    [BoundaryRegularityModel mass hmass] :
    BoundaryCovarianceModel mass hmass where
  dirichletKernel := BoundaryKernelModel.dirichletKernel (mass := mass) (hmass := hmass)
  neumannKernel := BoundaryKernelModel.neumannKernel (mass := mass) (hmass := hmass)
  periodicKernel := BoundaryKernelModel.periodicKernel (mass := mass) (hmass := hmass)
  dirichlet_le_free := BoundaryComparisonModel.dirichlet_le_free (mass := mass) (hmass := hmass)
  free_le_neumann := BoundaryComparisonModel.free_le_neumann (mass := mass) (hmass := hmass)
  dirichlet_monotone := BoundaryComparisonModel.dirichlet_monotone (mass := mass) (hmass := hmass)
  covarianceChange_pointwise_bounded :=
    BoundaryRegularityModel.covarianceChange_pointwise_bounded (mass := mass) (hmass := hmass)
  dirichlet_smooth_off_diagonal :=
    BoundaryRegularityModel.dirichlet_smooth_off_diagonal (mass := mass) (hmass := hmass)

/-- The Dirichlet covariance C_Λ^D = (-Δ_D + m²)⁻¹ on Λ, supplied by
    `BoundaryKernelModel`. -/
def dirichletCov (Λ : Rectangle) (mass : ℝ) (hmass : 0 < mass)
    [BoundaryKernelModel mass hmass] (x y : Spacetime2D) : ℝ :=
  BoundaryKernelModel.dirichletKernel (mass := mass) (hmass := hmass) Λ x y

/-- The Neumann covariance C_Λ^N = (-Δ_N + m²)⁻¹ on Λ, supplied by
    `BoundaryKernelModel`. -/
def neumannCov (Λ : Rectangle) (mass : ℝ) (hmass : 0 < mass)
    [BoundaryKernelModel mass hmass] (x y : Spacetime2D) : ℝ :=
  BoundaryKernelModel.neumannKernel (mass := mass) (hmass := hmass) Λ x y

/-- The periodic covariance on `[0,L₁] × [0,L₂]`, supplied by
    `BoundaryKernelModel`. -/
def periodicCov (L₁ L₂ mass : ℝ) (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) (hmass : 0 < mass)
    [BoundaryKernelModel mass hmass] (x y : Spacetime2D) : ℝ :=
  BoundaryKernelModel.periodicKernel (mass := mass) (hmass := hmass) L₁ L₂ hL₁ hL₂ x y

/-! ## Covariance operator inequalities

The fundamental ordering: C_D ≤ C ≤ C_N as bilinear forms.
This follows from the min-max characterization of eigenvalues. -/

/-- Dirichlet ≤ free covariance: C_D(f,f) ≤ C(f,f) for all f supported in Λ.
    This is because Dirichlet conditions restrict the variational space. -/
theorem dirichlet_le_free (Λ : Rectangle) (mass : ℝ) (hmass : 0 < mass)
    [BoundaryKernelModel mass hmass] [BoundaryComparisonModel mass hmass]
    (f : TestFun2D) (hf : ∀ x ∉ Λ.toSet, f x = 0) :
    ∫ x, ∫ y, f x * dirichletCov Λ mass hmass x y * f y ≤
      ∫ x, ∫ y, f x * freeCovKernel mass x y * f y := by
  simpa [dirichletCov] using
    (BoundaryComparisonModel.dirichlet_le_free (mass := mass) (hmass := hmass) Λ f hf)

/-- Free ≤ Neumann covariance: C(f,f) ≤ C_N(f,f) for all f supported in Λ.
    Neumann conditions enlarge the variational space. -/
theorem free_le_neumann (Λ : Rectangle) (mass : ℝ) (hmass : 0 < mass)
    [BoundaryKernelModel mass hmass] [BoundaryComparisonModel mass hmass]
    (f : TestFun2D) (hf : ∀ x ∉ Λ.toSet, f x = 0) :
    ∫ x, ∫ y, f x * freeCovKernel mass x y * f y ≤
      ∫ x, ∫ y, f x * neumannCov Λ mass hmass x y * f y := by
  simpa [neumannCov] using
    (BoundaryComparisonModel.free_le_neumann (mass := mass) (hmass := hmass) Λ f hf)

/-- Dirichlet monotonicity: If Λ₁ ⊂ Λ₂, then C_{Λ₁}^D ≤ C_{Λ₂}^D.
    Enlarging the domain relaxes the Dirichlet constraint. -/
theorem dirichlet_monotone (Λ₁ Λ₂ : Rectangle) (mass : ℝ) (hmass : 0 < mass)
    [BoundaryKernelModel mass hmass] [BoundaryComparisonModel mass hmass]
    (h : Λ₁.toSet ⊆ Λ₂.toSet) (f : TestFun2D) (hf : ∀ x ∉ Λ₁.toSet, f x = 0) :
    ∫ x, ∫ y, f x * dirichletCov Λ₁ mass hmass x y * f y ≤
      ∫ x, ∫ y, f x * dirichletCov Λ₂ mass hmass x y * f y := by
  simpa [dirichletCov] using
    (BoundaryComparisonModel.dirichlet_monotone (mass := mass) (hmass := hmass) Λ₁ Λ₂ h f hf)

/-- Combined comparison `C_Λ^D ≤ C_Λ^N` as quadratic forms for test functions
    supported in `Λ`. -/
theorem dirichlet_le_neumann (Λ : Rectangle) (mass : ℝ) (hmass : 0 < mass)
    [BoundaryKernelModel mass hmass] [BoundaryComparisonModel mass hmass]
    (f : TestFun2D) (hf : ∀ x ∉ Λ.toSet, f x = 0) :
    ∫ x, ∫ y, f x * dirichletCov Λ mass hmass x y * f y ≤
      ∫ x, ∫ y, f x * neumannCov Λ mass hmass x y * f y := by
  exact le_trans (dirichlet_le_free Λ mass hmass f hf)
    (free_le_neumann Λ mass hmass f hf)

/-- Nonnegativity of the free-minus-Dirichlet quadratic form on functions
    supported in `Λ`. -/
theorem free_minus_dirichlet_quadratic_nonneg
    (Λ : Rectangle) (mass : ℝ) (hmass : 0 < mass)
    [BoundaryKernelModel mass hmass] [BoundaryComparisonModel mass hmass]
    (f : TestFun2D) (hf : ∀ x ∉ Λ.toSet, f x = 0) :
    0 ≤
      (∫ x, ∫ y, f x * freeCovKernel mass x y * f y) -
        (∫ x, ∫ y, f x * dirichletCov Λ mass hmass x y * f y) := by
  have h := dirichlet_le_free Λ mass hmass f hf
  linarith

/-- Nonnegativity of the Neumann-minus-free quadratic form on functions
    supported in `Λ`. -/
theorem neumann_minus_free_quadratic_nonneg
    (Λ : Rectangle) (mass : ℝ) (hmass : 0 < mass)
    [BoundaryKernelModel mass hmass] [BoundaryComparisonModel mass hmass]
    (f : TestFun2D) (hf : ∀ x ∉ Λ.toSet, f x = 0) :
    0 ≤
      (∫ x, ∫ y, f x * neumannCov Λ mass hmass x y * f y) -
        (∫ x, ∫ y, f x * freeCovKernel mass x y * f y) := by
  have h := free_le_neumann Λ mass hmass f hf
  linarith

/-- Nonnegativity of the Neumann-minus-Dirichlet quadratic form on functions
    supported in `Λ`. -/
theorem neumann_minus_dirichlet_quadratic_nonneg
    (Λ : Rectangle) (mass : ℝ) (hmass : 0 < mass)
    [BoundaryKernelModel mass hmass] [BoundaryComparisonModel mass hmass]
    (f : TestFun2D) (hf : ∀ x ∉ Λ.toSet, f x = 0) :
    0 ≤
      (∫ x, ∫ y, f x * neumannCov Λ mass hmass x y * f y) -
        (∫ x, ∫ y, f x * dirichletCov Λ mass hmass x y * f y) := by
  have h := dirichlet_le_neumann Λ mass hmass f hf
  linarith

/-! ## Change of boundary conditions

The difference δC = C - C_D between free and Dirichlet covariances is controlled.
In d=2, the pointwise "mass" δc(x) = δC(x,x) satisfies |δc(x)| ≤ const. -/

/-- The change-of-covariance kernel δC = C - C_D. -/
def covarianceChange (Λ : Rectangle) (mass : ℝ) (hmass : 0 < mass)
    [BoundaryKernelModel mass hmass]
    (x y : Spacetime2D) : ℝ :=
  freeCovKernel mass x y - dirichletCov Λ mass hmass x y

/-- The pointwise covariance change δc(x) = δC(x,x) is bounded.
    This is crucial for the re-Wick-ordering estimates in d=2 (Glimm-Jaffe 7.6). -/
theorem covarianceChange_pointwise_bounded (Λ : Rectangle) (mass : ℝ) (hmass : 0 < mass)
    [BoundaryKernelModel mass hmass] [BoundaryRegularityModel mass hmass] :
    ∃ C : ℝ, ∀ x : Spacetime2D, x ∈ Λ.toSet →
      |covarianceChange Λ mass hmass x x| ≤ C := by
  simpa [covarianceChange, dirichletCov] using
    (BoundaryRegularityModel.covarianceChange_pointwise_bounded
      (mass := mass) (hmass := hmass) Λ)

/-! ## Regularity of covariance kernels -/

/-- The Dirichlet covariance kernel is smooth off the diagonal. -/
theorem dirichletCov_smooth_off_diagonal (Λ : Rectangle) (mass : ℝ) (hmass : 0 < mass)
    [BoundaryKernelModel mass hmass] [BoundaryRegularityModel mass hmass] :
    ∀ x y : Spacetime2D, x ≠ y → x ∈ Λ.toSet → y ∈ Λ.toSet →
      DifferentiableAt ℝ (fun p : Spacetime2D × Spacetime2D =>
        dirichletCov Λ mass hmass p.1 p.2) (x, y) := by
  simpa [dirichletCov] using
    (BoundaryRegularityModel.dirichlet_smooth_off_diagonal
      (mass := mass) (hmass := hmass) Λ)

/-- The free covariance kernel decays exponentially:
    |C(x,y)| ≤ const × e^{-m|x-y|} for |x-y| ≥ 1. -/
theorem freeCov_exponential_decay (mass : ℝ) (hmass : 0 < mass) :
    ∃ C₁ C₂ : ℝ, 0 < C₂ ∧
      ∀ x y : Spacetime2D, 1 ≤ ‖x - y‖ →
        |freeCovKernel mass x y| ≤ C₁ * Real.exp (-C₂ * ‖x - y‖) := by
  exact freeCovKernel_exponential_decay mass hmass

end

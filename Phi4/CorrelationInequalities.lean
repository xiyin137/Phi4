/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.FiniteVolumeMeasure
import Phi4.LatticeApproximation

/-!
# Correlation Inequalities

Correlation inequalities are the key tool for controlling the infinite volume limit.
They provide monotonicity and uniform bounds on Schwinger functions.

The main inequalities are:
- **GKS-I (Griffiths' first inequality)**: ⟨φ(f)φ(g)⟩ ≥ 0 for f,g ≥ 0
- **GKS-II (Griffiths' second inequality)**: truncated 4-point function is non-negative
- **FKG inequality**: monotone functions are positively correlated
- **Lebowitz inequality**: 4-point function bounded by sum of products of 2-point functions

These hold for the φ⁴ interaction because P(φ) = λφ⁴ + (lower order) with λ > 0
satisfies the Griffiths-Simon conditions.

## References

* [Glimm-Jaffe] Chapter 4 (lattice version), Section 10.2 (continuum version)
* [Simon] "The P(φ)₂ Euclidean (Quantum) Field Theory"
-/

noncomputable section

open MeasureTheory

/-! ## Abstract correlation-inequality interface -/

/-- Correlation inequalities for a fixed interacting model `params`.
    These are the continuum counterparts of the lattice inequalities used in
    Glimm-Jaffe Chapters 4 and 10, exposed as reusable assumptions so
    downstream infinite-volume/OS arguments can be developed independently of
    the lattice-approximation proof layer. -/
class CorrelationInequalityModel (params : Phi4Params) where
  /-- GKS-I positivity of the 2-point function for nonnegative test functions. -/
  griffiths_first : ∀ (Λ : Rectangle) (f g : TestFun2D)
      (_hf : ∀ x, 0 ≤ f x) (_hg : ∀ x, 0 ≤ g x),
      0 ≤ schwingerTwo params Λ f g
  /-- GKS-II lower bound in the `(12)(34)` pairing channel. -/
  griffiths_second : ∀ (Λ : Rectangle)
      (f₁ f₂ f₃ f₄ : TestFun2D)
      (_hf₁ : ∀ x, 0 ≤ f₁ x) (_hf₂ : ∀ x, 0 ≤ f₂ x)
      (_hf₃ : ∀ x, 0 ≤ f₃ x) (_hf₄ : ∀ x, 0 ≤ f₄ x),
      schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ ≤
        schwingerN params Λ 4 ![f₁, f₂, f₃, f₄]
  /-- FKG positive-correlation inequality for monotone observables. -/
  fkg_inequality : ∀ (Λ : Rectangle)
      (F G : FieldConfig2D → ℝ)
      (_hF_mono : ∀ ω₁ ω₂ : FieldConfig2D,
        (∀ f, (∀ x, 0 ≤ f x) → ω₁ f ≤ ω₂ f) → F ω₁ ≤ F ω₂)
      (_hG_mono : ∀ ω₁ ω₂ : FieldConfig2D,
        (∀ f, (∀ x, 0 ≤ f x) → ω₁ f ≤ ω₂ f) → G ω₁ ≤ G ω₂),
      (∫ ω, F ω ∂(finiteVolumeMeasure params Λ)) *
        (∫ ω, G ω ∂(finiteVolumeMeasure params Λ)) ≤
      ∫ ω, F ω * G ω ∂(finiteVolumeMeasure params Λ)
  /-- Lebowitz 4-point upper bound. -/
  lebowitz_inequality : ∀ (Λ : Rectangle)
      (f₁ f₂ f₃ f₄ : TestFun2D)
      (_hf₁ : ∀ x, 0 ≤ f₁ x) (_hf₂ : ∀ x, 0 ≤ f₂ x)
      (_hf₃ : ∀ x, 0 ≤ f₃ x) (_hf₄ : ∀ x, 0 ≤ f₄ x),
      schwingerN params Λ 4 ![f₁, f₂, f₃, f₄] ≤
        schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ +
        schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄ +
        schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃
  /-- Monotonicity of finite-volume 4-point moments under domain inclusion
      for nonnegative test-function inputs supported in the smaller volume. -/
  schwinger_four_monotone : ∀ (Λ₁ Λ₂ : Rectangle)
      (_h : Λ₁.toSet ⊆ Λ₂.toSet)
      (f : Fin 4 → TestFun2D)
      (_hf : ∀ i, ∀ x, 0 ≤ f i x)
      (_hfΛ : ∀ i, ∀ x ∉ Λ₁.toSet, f i x = 0),
      schwingerN params Λ₁ 4 f ≤ schwingerN params Λ₂ 4 f
  /-- Monotonicity of the finite-volume 2-point function under domain inclusion. -/
  schwinger_two_monotone : ∀ (Λ₁ Λ₂ : Rectangle)
      (_h : Λ₁.toSet ⊆ Λ₂.toSet)
      (f g : TestFun2D) (_hf : ∀ x, 0 ≤ f x) (_hg : ∀ x, 0 ≤ g x)
      (_hfΛ : ∀ x ∉ Λ₁.toSet, f x = 0) (_hgΛ : ∀ x ∉ Λ₁.toSet, g x = 0),
      schwingerTwo params Λ₁ f g ≤ schwingerTwo params Λ₂ f g

/-- Two-point correlation inequality input: GKS-I positivity and
    finite-volume monotonicity under domain inclusion. -/
class CorrelationTwoPointModel (params : Phi4Params) where
  griffiths_first : ∀ (Λ : Rectangle) (f g : TestFun2D)
      (_hf : ∀ x, 0 ≤ f x) (_hg : ∀ x, 0 ≤ g x),
      0 ≤ schwingerTwo params Λ f g
  schwinger_two_monotone : ∀ (Λ₁ Λ₂ : Rectangle)
      (_h : Λ₁.toSet ⊆ Λ₂.toSet)
      (f g : TestFun2D) (_hf : ∀ x, 0 ≤ f x) (_hg : ∀ x, 0 ≤ g x)
      (_hfΛ : ∀ x ∉ Λ₁.toSet, f x = 0) (_hgΛ : ∀ x ∉ Λ₁.toSet, g x = 0),
      schwingerTwo params Λ₁ f g ≤ schwingerTwo params Λ₂ f g

/-- Monotonicity interface for finite-volume `k`-point Schwinger moments under
    domain inclusion. This extends the existing two-point monotonicity surface
    to arbitrary fixed arity `k`. -/
class SchwingerNMonotoneModel (params : Phi4Params) (k : ℕ) where
  schwingerN_monotone : ∀ (Λ₁ Λ₂ : Rectangle)
      (_h : Λ₁.toSet ⊆ Λ₂.toSet)
      (f : Fin k → TestFun2D)
      (_hf : ∀ i, ∀ x, 0 ≤ f i x)
      (_hfΛ : ∀ i, ∀ x ∉ Λ₁.toSet, f i x = 0),
      schwingerN params Λ₁ k f ≤ schwingerN params Λ₂ k f

/-- Positivity interface for finite-volume `k`-point Schwinger moments on
    nonnegative test-function inputs. -/
class SchwingerNNonnegModel (params : Phi4Params) (k : ℕ) where
  schwingerN_nonneg : ∀ (Λ : Rectangle)
      (f : Fin k → TestFun2D)
      (_hf : ∀ i, ∀ x, 0 ≤ f i x),
      0 ≤ schwingerN params Λ k f

/-- Family-level monotonicity interface: provides finite-volume Schwinger
    monotonicity under domain inclusion for every arity `k`. -/
class SchwingerNMonotoneFamilyModel (params : Phi4Params) where
  schwingerN_monotone : ∀ (k : ℕ) (Λ₁ Λ₂ : Rectangle)
      (_h : Λ₁.toSet ⊆ Λ₂.toSet)
      (f : Fin k → TestFun2D)
      (_hf : ∀ i, ∀ x, 0 ≤ f i x)
      (_hfΛ : ∀ i, ∀ x ∉ Λ₁.toSet, f i x = 0),
      schwingerN params Λ₁ k f ≤ schwingerN params Λ₂ k f

/-- Any family-level monotonicity interface induces fixed-arity monotonicity
    interfaces by specialization. -/
instance (priority := 90) schwingerNMonotoneModel_of_family
    (params : Phi4Params) (k : ℕ)
    [SchwingerNMonotoneFamilyModel params] :
    SchwingerNMonotoneModel params k where
  schwingerN_monotone := by
    intro Λ₁ Λ₂ h f hf hfΛ
    exact SchwingerNMonotoneFamilyModel.schwingerN_monotone
      (params := params) k Λ₁ Λ₂ h f hf hfΛ

/-- Construct `SchwingerNMonotoneFamilyModel` from explicit all-arity
    monotonicity data. -/
theorem schwingerNMonotoneFamilyModel_nonempty_of_data
    (params : Phi4Params)
    (hmono : ∀ (k : ℕ) (Λ₁ Λ₂ : Rectangle)
      (_h : Λ₁.toSet ⊆ Λ₂.toSet)
      (f : Fin k → TestFun2D)
      (_hf : ∀ i, ∀ x, 0 ≤ f i x)
      (_hfΛ : ∀ i, ∀ x ∉ Λ₁.toSet, f i x = 0),
      schwingerN params Λ₁ k f ≤ schwingerN params Λ₂ k f) :
    Nonempty (SchwingerNMonotoneFamilyModel params) := by
  exact ⟨{ schwingerN_monotone := hmono }⟩

/-- Build a family-level monotonicity interface from fixed-arity interfaces for
    each `k`. -/
theorem schwingerNMonotoneFamilyModel_nonempty_of_models
    (params : Phi4Params)
    (hmono : ∀ k : ℕ, Nonempty (SchwingerNMonotoneModel params k)) :
    Nonempty (SchwingerNMonotoneFamilyModel params) := by
  classical
  refine schwingerNMonotoneFamilyModel_nonempty_of_data params ?_
  intro k Λ₁ Λ₂ h f hf hfΛ
  rcases hmono k with ⟨hk⟩
  letI : SchwingerNMonotoneModel params k := hk
  exact SchwingerNMonotoneModel.schwingerN_monotone
    (params := params) Λ₁ Λ₂ h f hf hfΛ

/-- Construct `SchwingerNMonotoneModel` from explicit `k`-point monotonicity
    data. -/
theorem schwingerNMonotoneModel_nonempty_of_data
    (params : Phi4Params) (k : ℕ)
    (hmono : ∀ (Λ₁ Λ₂ : Rectangle)
      (_h : Λ₁.toSet ⊆ Λ₂.toSet)
      (f : Fin k → TestFun2D)
      (_hf : ∀ i, ∀ x, 0 ≤ f i x)
      (_hfΛ : ∀ i, ∀ x ∉ Λ₁.toSet, f i x = 0),
      schwingerN params Λ₁ k f ≤ schwingerN params Λ₂ k f) :
    Nonempty (SchwingerNMonotoneModel params k) := by
  exact ⟨{ schwingerN_monotone := hmono }⟩

/-- Construct `SchwingerNNonnegModel` from explicit `k`-point nonnegativity
    data. -/
theorem schwingerNNonnegModel_nonempty_of_data
    (params : Phi4Params) (k : ℕ)
    (hnonneg : ∀ (Λ : Rectangle)
      (f : Fin k → TestFun2D)
      (_hf : ∀ i, ∀ x, 0 ≤ f i x),
      0 ≤ schwingerN params Λ k f) :
    Nonempty (SchwingerNNonnegModel params k) := by
  exact ⟨{ schwingerN_nonneg := hnonneg }⟩

/-- Interface-level access to finite-volume `k`-point monotonicity. -/
theorem schwingerN_monotone_of_interface
    (params : Phi4Params) (k : ℕ)
    [SchwingerNMonotoneModel params k]
    (Λ₁ Λ₂ : Rectangle)
    (h : Λ₁.toSet ⊆ Λ₂.toSet)
    (f : Fin k → TestFun2D)
    (hf : ∀ i, ∀ x, 0 ≤ f i x)
    (hfΛ : ∀ i, ∀ x ∉ Λ₁.toSet, f i x = 0) :
    schwingerN params Λ₁ k f ≤ schwingerN params Λ₂ k f := by
  exact SchwingerNMonotoneModel.schwingerN_monotone
    (params := params) Λ₁ Λ₂ h f hf hfΛ

/-- Interface-level access to finite-volume `k`-point nonnegativity. -/
theorem schwingerN_nonneg_of_interface
    (params : Phi4Params) (k : ℕ)
    [SchwingerNNonnegModel params k]
    (Λ : Rectangle)
    (f : Fin k → TestFun2D)
    (hf : ∀ i, ∀ x, 0 ≤ f i x) :
    0 ≤ schwingerN params Λ k f := by
  exact SchwingerNNonnegModel.schwingerN_nonneg
    (params := params) Λ f hf

/-- Interface-level access to finite-volume monotonicity from the family-level
    monotonicity interface. -/
theorem schwingerN_monotone_of_family
    (params : Phi4Params) (k : ℕ)
    [SchwingerNMonotoneFamilyModel params]
    (Λ₁ Λ₂ : Rectangle)
    (h : Λ₁.toSet ⊆ Λ₂.toSet)
    (f : Fin k → TestFun2D)
    (hf : ∀ i, ∀ x, 0 ≤ f i x)
    (hfΛ : ∀ i, ∀ x ∉ Λ₁.toSet, f i x = 0) :
    schwingerN params Λ₁ k f ≤ schwingerN params Λ₂ k f := by
  exact SchwingerNMonotoneFamilyModel.schwingerN_monotone
    (params := params) k Λ₁ Λ₂ h f hf hfΛ

/-- Two-point monotonicity implies `k = 2` Schwinger-moment monotonicity. -/
instance (priority := 100) schwingerNMonotoneModel_two_of_correlationTwoPoint
    (params : Phi4Params) [CorrelationTwoPointModel params] :
    SchwingerNMonotoneModel params 2 where
  schwingerN_monotone := by
    intro Λ₁ Λ₂ h f hf hfΛ
    have hmono := CorrelationTwoPointModel.schwinger_two_monotone
      (params := params) Λ₁ Λ₂ h (f 0) (f 1) (hf 0) (hf 1) (hfΛ 0) (hfΛ 1)
    simpa [schwingerN_two_eq_schwingerTwo] using hmono

/-- GKS-I two-point positivity implies `k = 2` Schwinger-moment nonnegativity. -/
instance (priority := 100) schwingerNNonnegModel_two_of_correlationTwoPoint
    (params : Phi4Params) [CorrelationTwoPointModel params] :
    SchwingerNNonnegModel params 2 where
  schwingerN_nonneg := by
    intro Λ f hf
    have hnonneg := CorrelationTwoPointModel.griffiths_first
      (params := params) Λ (f 0) (f 1) (hf 0) (hf 1)
    simpa [schwingerN_two_eq_schwingerTwo] using hnonneg

/-- Four-point GKS-II input: one nonnegative pairing channel
    `(12)(34)` for nonnegative test functions. -/
class CorrelationGKSSecondModel (params : Phi4Params) where
  griffiths_second : ∀ (Λ : Rectangle)
      (f₁ f₂ f₃ f₄ : TestFun2D)
      (_hf₁ : ∀ x, 0 ≤ f₁ x) (_hf₂ : ∀ x, 0 ≤ f₂ x)
      (_hf₃ : ∀ x, 0 ≤ f₃ x) (_hf₄ : ∀ x, 0 ≤ f₄ x),
      schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ ≤
        schwingerN params Λ 4 ![f₁, f₂, f₃, f₄]

/-- Four-point Lebowitz upper-bound input for nonnegative test functions. -/
class CorrelationLebowitzModel (params : Phi4Params) where
  lebowitz_inequality : ∀ (Λ : Rectangle)
      (f₁ f₂ f₃ f₄ : TestFun2D)
      (_hf₁ : ∀ x, 0 ≤ f₁ x) (_hf₂ : ∀ x, 0 ≤ f₂ x)
      (_hf₃ : ∀ x, 0 ≤ f₃ x) (_hf₄ : ∀ x, 0 ≤ f₄ x),
      schwingerN params Λ 4 ![f₁, f₂, f₃, f₄] ≤
        schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ +
        schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄ +
        schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃

/-- Four-point correlation-inequality input: one GKS-II pairing channel and the
    Lebowitz four-point upper bound. -/
class CorrelationFourPointInequalityModel (params : Phi4Params)
    extends CorrelationGKSSecondModel params, CorrelationLebowitzModel params

/-- Full four-point input: GKS-II/Lebowitz inequalities plus
    finite-volume four-point monotonicity under domain inclusion. -/
class CorrelationFourPointModel (params : Phi4Params)
    extends CorrelationFourPointInequalityModel params where
  schwinger_four_monotone : ∀ (Λ₁ Λ₂ : Rectangle)
      (_h : Λ₁.toSet ⊆ Λ₂.toSet)
      (f : Fin 4 → TestFun2D)
      (_hf : ∀ i, ∀ x, 0 ≤ f i x)
      (_hfΛ : ∀ i, ∀ x ∉ Λ₁.toSet, f i x = 0),
      schwingerN params Λ₁ 4 f ≤ schwingerN params Λ₂ 4 f

/-- FKG positive-correlation input for finite-volume observables. -/
class CorrelationFKGModel (params : Phi4Params) where
  fkg_inequality : ∀ (Λ : Rectangle)
      (F G : FieldConfig2D → ℝ)
      (_hF_mono : ∀ ω₁ ω₂ : FieldConfig2D,
        (∀ f, (∀ x, 0 ≤ f x) → ω₁ f ≤ ω₂ f) → F ω₁ ≤ F ω₂)
      (_hG_mono : ∀ ω₁ ω₂ : FieldConfig2D,
        (∀ f, (∀ x, 0 ≤ f x) → ω₁ f ≤ ω₂ f) → G ω₁ ≤ G ω₂),
      (∫ ω, F ω ∂(finiteVolumeMeasure params Λ)) *
        (∫ ω, G ω ∂(finiteVolumeMeasure params Λ)) ≤
      ∫ ω, F ω * G ω ∂(finiteVolumeMeasure params Λ)

/-- Construct `CorrelationTwoPointModel` from explicit two-point GKS-I and
    two-point volume-monotonicity data. -/
theorem correlationTwoPointModel_nonempty_of_data
    (params : Phi4Params)
    (hgriffiths_first : ∀ (Λ : Rectangle) (f g : TestFun2D)
      (_hf : ∀ x, 0 ≤ f x) (_hg : ∀ x, 0 ≤ g x),
      0 ≤ schwingerTwo params Λ f g)
    (hschwinger_two_monotone : ∀ (Λ₁ Λ₂ : Rectangle)
      (_h : Λ₁.toSet ⊆ Λ₂.toSet)
      (f g : TestFun2D) (_hf : ∀ x, 0 ≤ f x) (_hg : ∀ x, 0 ≤ g x)
      (_hfΛ : ∀ x ∉ Λ₁.toSet, f x = 0) (_hgΛ : ∀ x ∉ Λ₁.toSet, g x = 0),
      schwingerTwo params Λ₁ f g ≤ schwingerTwo params Λ₂ f g) :
    Nonempty (CorrelationTwoPointModel params) := by
  exact ⟨{
    griffiths_first := hgriffiths_first
    schwinger_two_monotone := hschwinger_two_monotone
  }⟩

/-- Construct `CorrelationGKSSecondModel` from explicit four-point GKS-II data. -/
theorem correlationGKSSecondModel_nonempty_of_data
    (params : Phi4Params)
    (hgriffiths_second : ∀ (Λ : Rectangle)
      (f₁ f₂ f₃ f₄ : TestFun2D)
      (_hf₁ : ∀ x, 0 ≤ f₁ x) (_hf₂ : ∀ x, 0 ≤ f₂ x)
      (_hf₃ : ∀ x, 0 ≤ f₃ x) (_hf₄ : ∀ x, 0 ≤ f₄ x),
      schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ ≤
        schwingerN params Λ 4 ![f₁, f₂, f₃, f₄]) :
    Nonempty (CorrelationGKSSecondModel params) := by
  exact ⟨{ griffiths_second := hgriffiths_second }⟩

/-- Construct `CorrelationLebowitzModel` from explicit four-point Lebowitz data. -/
theorem correlationLebowitzModel_nonempty_of_data
    (params : Phi4Params)
    (hlebowitz : ∀ (Λ : Rectangle)
      (f₁ f₂ f₃ f₄ : TestFun2D)
      (_hf₁ : ∀ x, 0 ≤ f₁ x) (_hf₂ : ∀ x, 0 ≤ f₂ x)
      (_hf₃ : ∀ x, 0 ≤ f₃ x) (_hf₄ : ∀ x, 0 ≤ f₄ x),
      schwingerN params Λ 4 ![f₁, f₂, f₃, f₄] ≤
        schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ +
        schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄ +
        schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃) :
    Nonempty (CorrelationLebowitzModel params) := by
  exact ⟨{ lebowitz_inequality := hlebowitz }⟩

/-- Construct `CorrelationFourPointInequalityModel` from atomic four-point
    GKS-II and Lebowitz subinterfaces. -/
theorem correlationFourPointInequalityModel_nonempty_of_models
    (params : Phi4Params)
    [CorrelationGKSSecondModel params]
    [CorrelationLebowitzModel params] :
    Nonempty (CorrelationFourPointInequalityModel params) := by
  exact ⟨{
    toCorrelationGKSSecondModel := inferInstance
    toCorrelationLebowitzModel := inferInstance
  }⟩

/-- Atomic GKS-II and Lebowitz interfaces reconstruct the combined four-point
    inequality class. -/
instance (priority := 100) correlationFourPointInequalityModel_of_atomic
    (params : Phi4Params)
    [CorrelationGKSSecondModel params]
    [CorrelationLebowitzModel params] :
    CorrelationFourPointInequalityModel params where
  toCorrelationGKSSecondModel := inferInstance
  toCorrelationLebowitzModel := inferInstance

/-- Construct `CorrelationFourPointInequalityModel` from explicit four-point
    GKS-II/Lebowitz data. -/
theorem correlationFourPointInequalityModel_nonempty_of_data
    (params : Phi4Params)
    (hgriffiths_second : ∀ (Λ : Rectangle)
      (f₁ f₂ f₃ f₄ : TestFun2D)
      (_hf₁ : ∀ x, 0 ≤ f₁ x) (_hf₂ : ∀ x, 0 ≤ f₂ x)
      (_hf₃ : ∀ x, 0 ≤ f₃ x) (_hf₄ : ∀ x, 0 ≤ f₄ x),
      schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ ≤
        schwingerN params Λ 4 ![f₁, f₂, f₃, f₄])
    (hlebowitz : ∀ (Λ : Rectangle)
      (f₁ f₂ f₃ f₄ : TestFun2D)
      (_hf₁ : ∀ x, 0 ≤ f₁ x) (_hf₂ : ∀ x, 0 ≤ f₂ x)
      (_hf₃ : ∀ x, 0 ≤ f₃ x) (_hf₄ : ∀ x, 0 ≤ f₄ x),
      schwingerN params Λ 4 ![f₁, f₂, f₃, f₄] ≤
        schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ +
        schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄ +
        schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃) :
    Nonempty (CorrelationFourPointInequalityModel params) := by
  rcases correlationGKSSecondModel_nonempty_of_data
      params hgriffiths_second with ⟨hgks⟩
  rcases correlationLebowitzModel_nonempty_of_data
      params hlebowitz with ⟨hleb⟩
  letI : CorrelationGKSSecondModel params := hgks
  letI : CorrelationLebowitzModel params := hleb
  exact correlationFourPointInequalityModel_nonempty_of_models params

/-- Construct `CorrelationFourPointModel` from explicit four-point
    GKS-II/Lebowitz data together with four-point volume monotonicity. -/
theorem correlationFourPointModel_nonempty_of_data
    (params : Phi4Params)
    (hgriffiths_second : ∀ (Λ : Rectangle)
      (f₁ f₂ f₃ f₄ : TestFun2D)
      (_hf₁ : ∀ x, 0 ≤ f₁ x) (_hf₂ : ∀ x, 0 ≤ f₂ x)
      (_hf₃ : ∀ x, 0 ≤ f₃ x) (_hf₄ : ∀ x, 0 ≤ f₄ x),
      schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ ≤
        schwingerN params Λ 4 ![f₁, f₂, f₃, f₄])
    (hlebowitz : ∀ (Λ : Rectangle)
      (f₁ f₂ f₃ f₄ : TestFun2D)
      (_hf₁ : ∀ x, 0 ≤ f₁ x) (_hf₂ : ∀ x, 0 ≤ f₂ x)
      (_hf₃ : ∀ x, 0 ≤ f₃ x) (_hf₄ : ∀ x, 0 ≤ f₄ x),
      schwingerN params Λ 4 ![f₁, f₂, f₃, f₄] ≤
        schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ +
        schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄ +
        schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃)
    (hfour_mono : ∀ (Λ₁ Λ₂ : Rectangle)
      (_h : Λ₁.toSet ⊆ Λ₂.toSet)
      (f : Fin 4 → TestFun2D)
      (_hf : ∀ i, ∀ x, 0 ≤ f i x)
      (_hfΛ : ∀ i, ∀ x ∉ Λ₁.toSet, f i x = 0),
      schwingerN params Λ₁ 4 f ≤ schwingerN params Λ₂ 4 f) :
    Nonempty (CorrelationFourPointModel params) := by
  rcases correlationFourPointInequalityModel_nonempty_of_data
      params hgriffiths_second hlebowitz with ⟨hineq⟩
  exact ⟨{
    toCorrelationFourPointInequalityModel := hineq
    schwinger_four_monotone := hfour_mono
  }⟩

/-- Construct `CorrelationFourPointModel` from inequality data plus an explicit
    `k = 4` monotonicity interface. -/
theorem correlationFourPointModel_nonempty_of_inequality_and_schwingerFourMonotone
    (params : Phi4Params)
    [CorrelationGKSSecondModel params]
    [CorrelationLebowitzModel params]
    [SchwingerNMonotoneModel params 4] :
    Nonempty (CorrelationFourPointModel params) := by
  exact ⟨{
    toCorrelationFourPointInequalityModel := inferInstance
    schwinger_four_monotone := by
      intro Λ₁ Λ₂ h f hf hfΛ
      exact SchwingerNMonotoneModel.schwingerN_monotone
        (params := params) (k := 4) Λ₁ Λ₂ h f hf hfΛ
  }⟩

/-- Atomic four-point inequality inputs plus explicit `k = 4` Schwinger
    monotonicity reconstruct the full four-point model. -/
instance (priority := 100) correlationFourPointModel_of_inequality_and_schwingerFourMonotone
    (params : Phi4Params)
    [CorrelationGKSSecondModel params]
    [CorrelationLebowitzModel params]
    [SchwingerNMonotoneModel params 4] :
    CorrelationFourPointModel params := by
  rcases correlationFourPointModel_nonempty_of_inequality_and_schwingerFourMonotone
      (params := params) with ⟨hfour⟩
  exact hfour

/-- Construct `CorrelationFKGModel` from an explicit finite-volume FKG
    positive-correlation inequality. -/
theorem correlationFKGModel_nonempty_of_data
    (params : Phi4Params)
    (hfkg : ∀ (Λ : Rectangle)
      (F G : FieldConfig2D → ℝ)
      (_hF_mono : ∀ ω₁ ω₂ : FieldConfig2D,
        (∀ f, (∀ x, 0 ≤ f x) → ω₁ f ≤ ω₂ f) → F ω₁ ≤ F ω₂)
      (_hG_mono : ∀ ω₁ ω₂ : FieldConfig2D,
        (∀ f, (∀ x, 0 ≤ f x) → ω₁ f ≤ ω₂ f) → G ω₁ ≤ G ω₂),
      (∫ ω, F ω ∂(finiteVolumeMeasure params Λ)) *
        (∫ ω, G ω ∂(finiteVolumeMeasure params Λ)) ≤
      ∫ ω, F ω * G ω ∂(finiteVolumeMeasure params Λ)) :
    Nonempty (CorrelationFKGModel params) := by
  exact ⟨{ fkg_inequality := hfkg }⟩

/-- Four-point monotonicity assumptions imply `k = 4` Schwinger-moment
    monotonicity. -/
instance (priority := 100) schwingerNMonotoneModel_four_of_correlationFourPoint
    (params : Phi4Params) [CorrelationFourPointModel params] :
    SchwingerNMonotoneModel params 4 where
  schwingerN_monotone := by
    intro Λ₁ Λ₂ h f hf hfΛ
    exact CorrelationFourPointModel.schwinger_four_monotone
      (params := params) Λ₁ Λ₂ h f hf hfΛ

/-- Any full correlation-inequality model provides the two-point subinterface. -/
instance (priority := 100) correlationTwoPointModel_of_full
    (params : Phi4Params) [CorrelationInequalityModel params] :
    CorrelationTwoPointModel params where
  griffiths_first := CorrelationInequalityModel.griffiths_first (params := params)
  schwinger_two_monotone := CorrelationInequalityModel.schwinger_two_monotone (params := params)

/-- Any full correlation-inequality model provides the four-point subinterface. -/
instance (priority := 100) correlationFourPointModel_of_full
    (params : Phi4Params) [CorrelationInequalityModel params] :
    CorrelationFourPointModel params where
  toCorrelationFourPointInequalityModel := {
    griffiths_second := CorrelationInequalityModel.griffiths_second (params := params)
    lebowitz_inequality := CorrelationInequalityModel.lebowitz_inequality (params := params)
  }
  schwinger_four_monotone := CorrelationInequalityModel.schwinger_four_monotone (params := params)

/-- Any full correlation-inequality model provides the FKG subinterface. -/
instance (priority := 100) correlationFKGModel_of_full
    (params : Phi4Params) [CorrelationInequalityModel params] :
    CorrelationFKGModel params where
  fkg_inequality := CorrelationInequalityModel.fkg_inequality (params := params)

/-- Atomic two-point/four-point/FKG inputs plus `k = 4` Schwinger-moment
    monotonicity reconstruct `CorrelationInequalityModel`. -/
instance (priority := 100) correlationInequalityModel_of_submodels
    (params : Phi4Params)
    [CorrelationTwoPointModel params]
    [CorrelationGKSSecondModel params]
    [CorrelationLebowitzModel params]
    [CorrelationFKGModel params]
    [SchwingerNMonotoneModel params 4] :
  CorrelationInequalityModel params where
  griffiths_first := CorrelationTwoPointModel.griffiths_first (params := params)
  griffiths_second := CorrelationGKSSecondModel.griffiths_second (params := params)
  fkg_inequality := CorrelationFKGModel.fkg_inequality (params := params)
  lebowitz_inequality := CorrelationLebowitzModel.lebowitz_inequality (params := params)
  schwinger_four_monotone := by
    intro Λ₁ Λ₂ h f hf hfΛ
    exact SchwingerNMonotoneModel.schwingerN_monotone
      (params := params) (k := 4) Λ₁ Λ₂ h f hf hfΛ
  schwinger_two_monotone := CorrelationTwoPointModel.schwinger_two_monotone (params := params)

/-- Construct `CorrelationInequalityModel` from explicit continuum data. -/
theorem correlationInequalityModel_nonempty_of_data
    (params : Phi4Params)
    (hgriffiths_first : ∀ (Λ : Rectangle) (f g : TestFun2D)
      (_hf : ∀ x, 0 ≤ f x) (_hg : ∀ x, 0 ≤ g x),
      0 ≤ schwingerTwo params Λ f g)
    (hgriffiths_second : ∀ (Λ : Rectangle)
      (f₁ f₂ f₃ f₄ : TestFun2D)
      (_hf₁ : ∀ x, 0 ≤ f₁ x) (_hf₂ : ∀ x, 0 ≤ f₂ x)
      (_hf₃ : ∀ x, 0 ≤ f₃ x) (_hf₄ : ∀ x, 0 ≤ f₄ x),
      schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ ≤
        schwingerN params Λ 4 ![f₁, f₂, f₃, f₄])
    (hfkg : ∀ (Λ : Rectangle)
      (F G : FieldConfig2D → ℝ)
      (_hF_mono : ∀ ω₁ ω₂ : FieldConfig2D,
        (∀ f, (∀ x, 0 ≤ f x) → ω₁ f ≤ ω₂ f) → F ω₁ ≤ F ω₂)
      (_hG_mono : ∀ ω₁ ω₂ : FieldConfig2D,
        (∀ f, (∀ x, 0 ≤ f x) → ω₁ f ≤ ω₂ f) → G ω₁ ≤ G ω₂),
      (∫ ω, F ω ∂(finiteVolumeMeasure params Λ)) *
        (∫ ω, G ω ∂(finiteVolumeMeasure params Λ)) ≤
      ∫ ω, F ω * G ω ∂(finiteVolumeMeasure params Λ))
    (hlebowitz : ∀ (Λ : Rectangle)
      (f₁ f₂ f₃ f₄ : TestFun2D)
      (_hf₁ : ∀ x, 0 ≤ f₁ x) (_hf₂ : ∀ x, 0 ≤ f₂ x)
      (_hf₃ : ∀ x, 0 ≤ f₃ x) (_hf₄ : ∀ x, 0 ≤ f₄ x),
      schwingerN params Λ 4 ![f₁, f₂, f₃, f₄] ≤
        schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ +
        schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄ +
        schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃)
    (hfour_mono : ∀ (Λ₁ Λ₂ : Rectangle)
      (_h : Λ₁.toSet ⊆ Λ₂.toSet)
      (f : Fin 4 → TestFun2D)
      (_hf : ∀ i, ∀ x, 0 ≤ f i x)
      (_hfΛ : ∀ i, ∀ x ∉ Λ₁.toSet, f i x = 0),
      schwingerN params Λ₁ 4 f ≤ schwingerN params Λ₂ 4 f)
    (htwo_mono : ∀ (Λ₁ Λ₂ : Rectangle)
      (_h : Λ₁.toSet ⊆ Λ₂.toSet)
      (f g : TestFun2D) (_hf : ∀ x, 0 ≤ f x) (_hg : ∀ x, 0 ≤ g x)
      (_hfΛ : ∀ x ∉ Λ₁.toSet, f x = 0) (_hgΛ : ∀ x ∉ Λ₁.toSet, g x = 0),
      schwingerTwo params Λ₁ f g ≤ schwingerTwo params Λ₂ f g) :
    Nonempty (CorrelationInequalityModel params) := by
  exact ⟨{
    griffiths_first := hgriffiths_first
    griffiths_second := hgriffiths_second
    fkg_inequality := hfkg
    lebowitz_inequality := hlebowitz
    schwinger_four_monotone := hfour_mono
    schwinger_two_monotone := htwo_mono
  }⟩

/-- Construct `CorrelationInequalityModel` from atomic two-point/four-point/FKG
    subinterfaces plus explicit `k = 4` Schwinger-moment monotonicity. -/
theorem correlationInequalityModel_nonempty_of_submodels
    (params : Phi4Params)
    [CorrelationTwoPointModel params]
    [CorrelationGKSSecondModel params]
    [CorrelationLebowitzModel params]
    [CorrelationFKGModel params]
    [SchwingerNMonotoneModel params 4] :
    Nonempty (CorrelationInequalityModel params) := by
  exact ⟨inferInstance⟩

/-- Construct `CorrelationInequalityModel` from:
    1. two-point and FKG subinterfaces,
    2. four-point inequality subinterface, and
    3. explicit `k = 4` Schwinger-moment monotonicity. -/
theorem correlationInequalityModel_nonempty_of_submodels_and_schwingerFourMonotone
    (params : Phi4Params)
    [CorrelationTwoPointModel params]
    [CorrelationGKSSecondModel params]
    [CorrelationLebowitzModel params]
    [CorrelationFKGModel params]
    [SchwingerNMonotoneModel params 4] :
    Nonempty (CorrelationInequalityModel params) := by
  exact correlationInequalityModel_nonempty_of_submodels params

/-! ## Lattice-to-continuum bridge for GKS-I -/

/-- Real-analysis helper: if `x` can be approximated arbitrarily well by
    nonnegative reals, then `x` is nonnegative. -/
lemma nonneg_of_approx_nonneg (x : ℝ)
    (happrox : ∀ ε > 0, ∃ y : ℝ, 0 ≤ y ∧ |x - y| < ε) :
    0 ≤ x := by
  by_contra hx
  have hxlt : x < 0 := lt_of_not_ge hx
  have hxeps : 0 < -x := by linarith
  rcases happrox (-x) hxeps with ⟨y, hy_nonneg, hy_close⟩
  have hlower : -x ≤ |x - y| := by
    calc
      -x ≤ y - x := by linarith
      _ = |y - x| := by
            rw [abs_of_nonneg]
            linarith
      _ = |x - y| := by simp [abs_sub_comm]
  linarith

/-- Real-analysis helper: if `x` and `y` can be approximated arbitrarily well by
    ordered pairs `a ≤ b`, then `x ≤ y`. -/
lemma le_of_approx_ordered (x y : ℝ)
    (happrox : ∀ ε > 0,
      ∃ a b : ℝ, a ≤ b ∧ |x - a| < ε ∧ |y - b| < ε) :
    x ≤ y := by
  by_contra hxy
  have hxylt : y < x := lt_of_not_ge hxy
  let ε : ℝ := (x - y) / 4
  have hε : 0 < ε := by
    have : 0 < x - y := by linarith
    exact div_pos this (by norm_num)
  rcases happrox ε hε with ⟨a, b, hab, hxa, hyb⟩
  have hxa' := abs_lt.mp hxa
  have hyb' := abs_lt.mp hyb
  have ha_lower : x - ε < a := by linarith [hxa'.2]
  have hb_upper : b < y + ε := by linarith [hyb'.1]
  have hgap : y + ε < x - ε := by
    dsimp [ε]
    linarith
  have hab_false : ¬ a ≤ b := by
    have : b < a := by linarith
    exact not_le_of_gt this
  exact hab_false hab

/-- Bridge assumptions for deriving continuum GKS-I from lattice approximants. -/
class LatticeGriffithsFirstModel (params : Phi4Params) where
  /-- Lattice approximant of the continuum two-point function at fixed volume and mesh. -/
  latticeTwo : ∀ Λ : Rectangle, Phi4.RectLattice Λ → TestFun2D → TestFun2D → ℝ
  /-- Lattice GKS-I positivity. -/
  lattice_gks1 : ∀ (Λ : Rectangle) (L : Phi4.RectLattice Λ) (f g : TestFun2D)
      (_hf : ∀ x, 0 ≤ f x) (_hg : ∀ x, 0 ≤ g x),
      0 ≤ latticeTwo Λ L f g
  /-- Arbitrarily fine lattice approximation of the continuum two-point function. -/
  schwingerTwo_approx_lattice : ∀ (Λ : Rectangle) (f g : TestFun2D)
      (ε : ℝ), 0 < ε →
      ∃ L : Phi4.RectLattice Λ,
        |schwingerTwo params Λ f g - latticeTwo Λ L f g| < ε

/-- Construct `LatticeGriffithsFirstModel` from explicit lattice two-point data,
    lattice GKS-I, and approximation to the continuum two-point function. -/
theorem latticeGriffithsFirstModel_nonempty_of_data
    (params : Phi4Params)
    (latticeTwo : ∀ Λ : Rectangle, Phi4.RectLattice Λ → TestFun2D → TestFun2D → ℝ)
    (hlattice_gks1 : ∀ (Λ : Rectangle) (L : Phi4.RectLattice Λ) (f g : TestFun2D)
      (_hf : ∀ x, 0 ≤ f x) (_hg : ∀ x, 0 ≤ g x),
      0 ≤ latticeTwo Λ L f g)
    (happrox : ∀ (Λ : Rectangle) (f g : TestFun2D)
      (ε : ℝ), 0 < ε →
      ∃ L : Phi4.RectLattice Λ,
        |schwingerTwo params Λ f g - latticeTwo Λ L f g| < ε) :
    Nonempty (LatticeGriffithsFirstModel params) := by
  exact ⟨{
    latticeTwo := latticeTwo
    lattice_gks1 := hlattice_gks1
    schwingerTwo_approx_lattice := happrox
  }⟩

/-- Continuum GKS-I obtained from lattice GKS-I plus convergence of lattice
    approximants to the continuum two-point function. -/
theorem griffiths_first_from_lattice
    (params : Phi4Params)
    [LatticeGriffithsFirstModel params]
    (Λ : Rectangle) (f g : TestFun2D)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) :
    0 ≤ schwingerTwo params Λ f g := by
  apply nonneg_of_approx_nonneg
  intro ε hε
  rcases LatticeGriffithsFirstModel.schwingerTwo_approx_lattice
      (params := params) Λ f g ε hε with ⟨L, hclose⟩
  refine ⟨LatticeGriffithsFirstModel.latticeTwo (params := params) Λ L f g,
    LatticeGriffithsFirstModel.lattice_gks1 (params := params) Λ L f g hf hg,
    ?_⟩
  simpa [abs_sub_comm] using hclose

/-- Bridge assumptions for deriving continuum volume-monotonicity of the
    two-point function from lattice-ordered approximants. -/
class LatticeSchwingerTwoMonotoneModel (params : Phi4Params) where
  latticeTwo : ∀ Λ : Rectangle, Phi4.RectLattice Λ → TestFun2D → TestFun2D → ℝ
  approx_monotone_pair : ∀ (Λ₁ Λ₂ : Rectangle)
      (_h : Λ₁.toSet ⊆ Λ₂.toSet)
      (f g : TestFun2D) (_hf : ∀ x, 0 ≤ f x) (_hg : ∀ x, 0 ≤ g x)
      (_hfΛ : ∀ x ∉ Λ₁.toSet, f x = 0) (_hgΛ : ∀ x ∉ Λ₁.toSet, g x = 0)
      (ε : ℝ), 0 < ε →
      ∃ L₁ : Phi4.RectLattice Λ₁, ∃ L₂ : Phi4.RectLattice Λ₂,
        latticeTwo Λ₁ L₁ f g ≤ latticeTwo Λ₂ L₂ f g ∧
        |schwingerTwo params Λ₁ f g - latticeTwo Λ₁ L₁ f g| < ε ∧
        |schwingerTwo params Λ₂ f g - latticeTwo Λ₂ L₂ f g| < ε

/-- Bridge assumptions for deriving continuum volume-monotonicity of
    finite-volume `k`-point Schwinger moments from lattice-ordered
    approximants. -/
class LatticeSchwingerNMonotoneModel (params : Phi4Params) (k : ℕ) where
  latticeN : ∀ Λ : Rectangle, Phi4.RectLattice Λ → (Fin k → TestFun2D) → ℝ
  approx_monotone_pair : ∀ (Λ₁ Λ₂ : Rectangle)
      (_h : Λ₁.toSet ⊆ Λ₂.toSet)
      (f : Fin k → TestFun2D) (_hf : ∀ i, ∀ x, 0 ≤ f i x)
      (_hfΛ : ∀ i, ∀ x ∉ Λ₁.toSet, f i x = 0)
      (ε : ℝ), 0 < ε →
      ∃ L₁ : Phi4.RectLattice Λ₁, ∃ L₂ : Phi4.RectLattice Λ₂,
        latticeN Λ₁ L₁ f ≤ latticeN Λ₂ L₂ f ∧
        |schwingerN params Λ₁ k f - latticeN Λ₁ L₁ f| < ε ∧
        |schwingerN params Λ₂ k f - latticeN Λ₂ L₂ f| < ε

/-- Family-level lattice bridge assumptions for finite-volume `k`-point
    monotonicity under domain inclusion. -/
class LatticeSchwingerNMonotoneFamilyModel (params : Phi4Params) where
  latticeN :
    ∀ (k : ℕ) (Λ : Rectangle), Phi4.RectLattice Λ → (Fin k → TestFun2D) → ℝ
  approx_monotone_pair : ∀ (k : ℕ) (Λ₁ Λ₂ : Rectangle)
      (_h : Λ₁.toSet ⊆ Λ₂.toSet)
      (f : Fin k → TestFun2D) (_hf : ∀ i, ∀ x, 0 ≤ f i x)
      (_hfΛ : ∀ i, ∀ x ∉ Λ₁.toSet, f i x = 0)
      (ε : ℝ), 0 < ε →
      ∃ L₁ : Phi4.RectLattice Λ₁, ∃ L₂ : Phi4.RectLattice Λ₂,
        latticeN k Λ₁ L₁ f ≤ latticeN k Λ₂ L₂ f ∧
        |schwingerN params Λ₁ k f - latticeN k Λ₁ L₁ f| < ε ∧
        |schwingerN params Λ₂ k f - latticeN k Λ₂ L₂ f| < ε

/-- Any family-level lattice monotonicity interface induces fixed-arity lattice
    monotonicity interfaces by specialization. -/
instance (priority := 90) latticeSchwingerNMonotoneModel_of_family
    (params : Phi4Params) (k : ℕ)
    [LatticeSchwingerNMonotoneFamilyModel params] :
    LatticeSchwingerNMonotoneModel params k where
  latticeN := LatticeSchwingerNMonotoneFamilyModel.latticeN (params := params) k
  approx_monotone_pair := by
    intro Λ₁ Λ₂ h f hf hfΛ ε hε
    exact LatticeSchwingerNMonotoneFamilyModel.approx_monotone_pair
      (params := params) k Λ₁ Λ₂ h f hf hfΛ ε hε

/-- Construct `LatticeSchwingerTwoMonotoneModel` from explicit lattice two-point
    data and ordered approximation pairs for nested volumes. -/
theorem latticeSchwingerTwoMonotoneModel_nonempty_of_data
    (params : Phi4Params)
    (latticeTwo : ∀ Λ : Rectangle, Phi4.RectLattice Λ → TestFun2D → TestFun2D → ℝ)
    (happrox_pair : ∀ (Λ₁ Λ₂ : Rectangle)
      (_h : Λ₁.toSet ⊆ Λ₂.toSet)
      (f g : TestFun2D) (_hf : ∀ x, 0 ≤ f x) (_hg : ∀ x, 0 ≤ g x)
      (_hfΛ : ∀ x ∉ Λ₁.toSet, f x = 0) (_hgΛ : ∀ x ∉ Λ₁.toSet, g x = 0)
      (ε : ℝ), 0 < ε →
      ∃ L₁ : Phi4.RectLattice Λ₁, ∃ L₂ : Phi4.RectLattice Λ₂,
        latticeTwo Λ₁ L₁ f g ≤ latticeTwo Λ₂ L₂ f g ∧
        |schwingerTwo params Λ₁ f g - latticeTwo Λ₁ L₁ f g| < ε ∧
        |schwingerTwo params Λ₂ f g - latticeTwo Λ₂ L₂ f g| < ε) :
    Nonempty (LatticeSchwingerTwoMonotoneModel params) := by
  exact ⟨{
    latticeTwo := latticeTwo
    approx_monotone_pair := happrox_pair
  }⟩

/-- Continuum two-point monotonicity from lattice-ordered approximation pairs. -/
theorem schwinger_two_monotone_from_lattice
    (params : Phi4Params)
    [LatticeSchwingerTwoMonotoneModel params]
    (Λ₁ Λ₂ : Rectangle)
    (h : Λ₁.toSet ⊆ Λ₂.toSet)
    (f g : TestFun2D) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfΛ : ∀ x ∉ Λ₁.toSet, f x = 0) (hgΛ : ∀ x ∉ Λ₁.toSet, g x = 0) :
    schwingerTwo params Λ₁ f g ≤ schwingerTwo params Λ₂ f g := by
  apply le_of_approx_ordered
  intro ε hε
  rcases LatticeSchwingerTwoMonotoneModel.approx_monotone_pair
      (params := params) Λ₁ Λ₂ h f g hf hg hfΛ hgΛ ε hε with
      ⟨L₁, L₂, hmon, hclose₁, hclose₂⟩
  refine ⟨LatticeSchwingerTwoMonotoneModel.latticeTwo (params := params) Λ₁ L₁ f g,
    LatticeSchwingerTwoMonotoneModel.latticeTwo (params := params) Λ₂ L₂ f g,
    hmon, hclose₁, hclose₂⟩

/-- Construct `LatticeSchwingerNMonotoneModel` from explicit lattice `k`-point
    data and ordered approximation pairs for nested volumes. -/
theorem latticeSchwingerNMonotoneModel_nonempty_of_data
    (params : Phi4Params) (k : ℕ)
    (latticeN : ∀ Λ : Rectangle, Phi4.RectLattice Λ → (Fin k → TestFun2D) → ℝ)
    (happrox_pair : ∀ (Λ₁ Λ₂ : Rectangle)
      (_h : Λ₁.toSet ⊆ Λ₂.toSet)
      (f : Fin k → TestFun2D) (_hf : ∀ i, ∀ x, 0 ≤ f i x)
      (_hfΛ : ∀ i, ∀ x ∉ Λ₁.toSet, f i x = 0)
      (ε : ℝ), 0 < ε →
      ∃ L₁ : Phi4.RectLattice Λ₁, ∃ L₂ : Phi4.RectLattice Λ₂,
        latticeN Λ₁ L₁ f ≤ latticeN Λ₂ L₂ f ∧
        |schwingerN params Λ₁ k f - latticeN Λ₁ L₁ f| < ε ∧
        |schwingerN params Λ₂ k f - latticeN Λ₂ L₂ f| < ε) :
    Nonempty (LatticeSchwingerNMonotoneModel params k) := by
  exact ⟨{
    latticeN := latticeN
    approx_monotone_pair := happrox_pair
  }⟩

/-- Construct `LatticeSchwingerNMonotoneFamilyModel` from explicit all-arity
    lattice monotonicity approximation data. -/
theorem latticeSchwingerNMonotoneFamilyModel_nonempty_of_data
    (params : Phi4Params)
    (latticeN : ∀ (k : ℕ) (Λ : Rectangle),
      Phi4.RectLattice Λ → (Fin k → TestFun2D) → ℝ)
    (happrox_pair : ∀ (k : ℕ) (Λ₁ Λ₂ : Rectangle)
      (_h : Λ₁.toSet ⊆ Λ₂.toSet)
      (f : Fin k → TestFun2D) (_hf : ∀ i, ∀ x, 0 ≤ f i x)
      (_hfΛ : ∀ i, ∀ x ∉ Λ₁.toSet, f i x = 0)
      (ε : ℝ), 0 < ε →
      ∃ L₁ : Phi4.RectLattice Λ₁, ∃ L₂ : Phi4.RectLattice Λ₂,
        latticeN k Λ₁ L₁ f ≤ latticeN k Λ₂ L₂ f ∧
        |schwingerN params Λ₁ k f - latticeN k Λ₁ L₁ f| < ε ∧
        |schwingerN params Λ₂ k f - latticeN k Λ₂ L₂ f| < ε) :
    Nonempty (LatticeSchwingerNMonotoneFamilyModel params) := by
  exact ⟨{
    latticeN := latticeN
    approx_monotone_pair := happrox_pair
  }⟩

/-- Build a family-level lattice monotonicity interface from fixed-arity
    lattice monotonicity interfaces for each `k`. -/
theorem latticeSchwingerNMonotoneFamilyModel_nonempty_of_models
    (params : Phi4Params)
    (hmono : ∀ k : ℕ, Nonempty (LatticeSchwingerNMonotoneModel params k)) :
    Nonempty (LatticeSchwingerNMonotoneFamilyModel params) := by
  classical
  let hk : ∀ k : ℕ, LatticeSchwingerNMonotoneModel params k :=
    fun k => Classical.choice (hmono k)
  refine latticeSchwingerNMonotoneFamilyModel_nonempty_of_data params
    (fun k Λ L f => by
      letI : LatticeSchwingerNMonotoneModel params k := hk k
      exact LatticeSchwingerNMonotoneModel.latticeN (params := params) Λ L f)
    ?_
  intro k Λ₁ Λ₂ h f hf hfΛ ε hε
  letI : LatticeSchwingerNMonotoneModel params k := hk k
  exact LatticeSchwingerNMonotoneModel.approx_monotone_pair
    (params := params) Λ₁ Λ₂ h f hf hfΛ ε hε

/-- Continuum `k`-point monotonicity from lattice-ordered approximation pairs. -/
theorem schwingerN_monotone_from_lattice
    (params : Phi4Params) (k : ℕ)
    [LatticeSchwingerNMonotoneModel params k]
    (Λ₁ Λ₂ : Rectangle)
    (h : Λ₁.toSet ⊆ Λ₂.toSet)
    (f : Fin k → TestFun2D) (hf : ∀ i, ∀ x, 0 ≤ f i x)
    (hfΛ : ∀ i, ∀ x ∉ Λ₁.toSet, f i x = 0) :
    schwingerN params Λ₁ k f ≤ schwingerN params Λ₂ k f := by
  apply le_of_approx_ordered
  intro ε hε
  rcases LatticeSchwingerNMonotoneModel.approx_monotone_pair
      (params := params) Λ₁ Λ₂ h f hf hfΛ ε hε with
      ⟨L₁, L₂, hmon, hclose₁, hclose₂⟩
  refine ⟨LatticeSchwingerNMonotoneModel.latticeN (params := params) Λ₁ L₁ f,
    LatticeSchwingerNMonotoneModel.latticeN (params := params) Λ₂ L₂ f,
    hmon, hclose₁, hclose₂⟩

/-- Lattice `k`-point monotonicity assumptions induce the continuum
    `SchwingerNMonotoneModel` interface. -/
instance (priority := 100) schwingerNMonotoneModel_of_lattice
    (params : Phi4Params) (k : ℕ)
    [LatticeSchwingerNMonotoneModel params k] :
    SchwingerNMonotoneModel params k where
  schwingerN_monotone := schwingerN_monotone_from_lattice (params := params) (k := k)

/-- Construct `CorrelationFourPointModel` from explicit four-point
    GKS-II/Lebowitz data plus lattice-derived 4-point volume monotonicity. -/
theorem correlationFourPointModel_nonempty_of_data_and_lattice_monotone
    (params : Phi4Params)
    [LatticeSchwingerNMonotoneModel params 4]
    (hgriffiths_second : ∀ (Λ : Rectangle)
      (f₁ f₂ f₃ f₄ : TestFun2D)
      (_hf₁ : ∀ x, 0 ≤ f₁ x) (_hf₂ : ∀ x, 0 ≤ f₂ x)
      (_hf₃ : ∀ x, 0 ≤ f₃ x) (_hf₄ : ∀ x, 0 ≤ f₄ x),
      schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ ≤
        schwingerN params Λ 4 ![f₁, f₂, f₃, f₄])
    (hlebowitz : ∀ (Λ : Rectangle)
      (f₁ f₂ f₃ f₄ : TestFun2D)
      (_hf₁ : ∀ x, 0 ≤ f₁ x) (_hf₂ : ∀ x, 0 ≤ f₂ x)
      (_hf₃ : ∀ x, 0 ≤ f₃ x) (_hf₄ : ∀ x, 0 ≤ f₄ x),
      schwingerN params Λ 4 ![f₁, f₂, f₃, f₄] ≤
        schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ +
        schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄ +
        schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃) :
    Nonempty (CorrelationFourPointModel params) := by
  refine correlationFourPointModel_nonempty_of_data params
    hgriffiths_second hlebowitz ?_
  intro Λ₁ Λ₂ h f hf hfΛ
  exact schwingerN_monotone_from_lattice
    (params := params) (k := 4) Λ₁ Λ₂ h f hf hfΛ

/-- Family-level lattice monotonicity assumptions induce the continuum
    family-level `SchwingerNMonotoneFamilyModel` interface. -/
instance (priority := 85) schwingerNMonotoneFamilyModel_of_latticeFamily
    (params : Phi4Params)
    [LatticeSchwingerNMonotoneFamilyModel params] :
    SchwingerNMonotoneFamilyModel params where
  schwingerN_monotone := by
    intro k Λ₁ Λ₂ h f hf hfΛ
    exact schwingerN_monotone_from_lattice
      (params := params) (k := k) Λ₁ Λ₂ h f hf hfΛ

/-- Existing lattice two-point monotonicity data yields a generic lattice
    monotonicity model at arity `k = 2`. -/
theorem latticeSchwingerNMonotoneModel_two_nonempty_of_latticeTwo
    (params : Phi4Params)
    [LatticeSchwingerTwoMonotoneModel params] :
    Nonempty (LatticeSchwingerNMonotoneModel params 2) := by
  refine latticeSchwingerNMonotoneModel_nonempty_of_data params 2
    (fun Λ L f => LatticeSchwingerTwoMonotoneModel.latticeTwo (params := params) Λ L (f 0) (f 1))
    ?_
  intro Λ₁ Λ₂ h f hf hfΛ ε hε
  rcases LatticeSchwingerTwoMonotoneModel.approx_monotone_pair
      (params := params) Λ₁ Λ₂ h
      (f 0) (f 1) (hf 0) (hf 1) (hfΛ 0) (hfΛ 1) ε hε with
      ⟨L₁, L₂, hmon, hclose₁, hclose₂⟩
  refine ⟨L₁, L₂, hmon, ?_, ?_⟩
  · simpa [schwingerN_two_eq_schwingerTwo] using hclose₁
  · simpa [schwingerN_two_eq_schwingerTwo] using hclose₂

/-- Lattice two-point monotonicity yields a `k = 2` Schwinger-moment
    monotonicity interface instance. -/
theorem schwingerNMonotoneModel_two_nonempty_of_lattice
    (params : Phi4Params)
    [LatticeSchwingerTwoMonotoneModel params] :
    Nonempty (SchwingerNMonotoneModel params 2) := by
  rcases latticeSchwingerNMonotoneModel_two_nonempty_of_latticeTwo
      (params := params) with ⟨hmonoN⟩
  letI : LatticeSchwingerNMonotoneModel params 2 := hmonoN
  exact ⟨inferInstance⟩

/-- Core correlation-inequality inputs not yet derived from the current
    lattice bridge layer. This isolates the remaining analytic assumptions
    while allowing GKS-I and two-point monotonicity to be sourced from
    lattice approximation results. -/
class CorrelationInequalityCoreModel (params : Phi4Params)
    extends CorrelationGKSSecondModel params,
      CorrelationLebowitzModel params,
      CorrelationFKGModel params where
  /-- Monotonicity of finite-volume 4-point moments under domain inclusion for
      nonnegative test-function inputs supported in the smaller volume. -/
  schwinger_four_monotone : ∀ (Λ₁ Λ₂ : Rectangle)
      (_h : Λ₁.toSet ⊆ Λ₂.toSet)
      (f : Fin 4 → TestFun2D)
      (_hf : ∀ i, ∀ x, 0 ≤ f i x)
      (_hfΛ : ∀ i, ∀ x ∉ Λ₁.toSet, f i x = 0),
      schwingerN params Λ₁ 4 f ≤ schwingerN params Λ₂ 4 f

/-- Construct `CorrelationInequalityCoreModel` from explicit continuum GKS-II,
    FKG, Lebowitz, and 4-point monotonicity assumptions. -/
theorem correlationInequalityCoreModel_nonempty_of_data
    (params : Phi4Params)
    (hgriffiths_second : ∀ (Λ : Rectangle)
      (f₁ f₂ f₃ f₄ : TestFun2D)
      (_hf₁ : ∀ x, 0 ≤ f₁ x) (_hf₂ : ∀ x, 0 ≤ f₂ x)
      (_hf₃ : ∀ x, 0 ≤ f₃ x) (_hf₄ : ∀ x, 0 ≤ f₄ x),
      schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ ≤
        schwingerN params Λ 4 ![f₁, f₂, f₃, f₄])
    (hfkg : ∀ (Λ : Rectangle)
      (F G : FieldConfig2D → ℝ)
      (_hF_mono : ∀ ω₁ ω₂ : FieldConfig2D,
        (∀ f, (∀ x, 0 ≤ f x) → ω₁ f ≤ ω₂ f) → F ω₁ ≤ F ω₂)
      (_hG_mono : ∀ ω₁ ω₂ : FieldConfig2D,
        (∀ f, (∀ x, 0 ≤ f x) → ω₁ f ≤ ω₂ f) → G ω₁ ≤ G ω₂),
      (∫ ω, F ω ∂(finiteVolumeMeasure params Λ)) *
        (∫ ω, G ω ∂(finiteVolumeMeasure params Λ)) ≤
      ∫ ω, F ω * G ω ∂(finiteVolumeMeasure params Λ))
    (hlebowitz : ∀ (Λ : Rectangle)
      (f₁ f₂ f₃ f₄ : TestFun2D)
      (_hf₁ : ∀ x, 0 ≤ f₁ x) (_hf₂ : ∀ x, 0 ≤ f₂ x)
      (_hf₃ : ∀ x, 0 ≤ f₃ x) (_hf₄ : ∀ x, 0 ≤ f₄ x),
      schwingerN params Λ 4 ![f₁, f₂, f₃, f₄] ≤
        schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ +
        schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄ +
        schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃)
    (hfour_mono : ∀ (Λ₁ Λ₂ : Rectangle)
      (_h : Λ₁.toSet ⊆ Λ₂.toSet)
      (f : Fin 4 → TestFun2D)
      (_hf : ∀ i, ∀ x, 0 ≤ f i x)
      (_hfΛ : ∀ i, ∀ x ∉ Λ₁.toSet, f i x = 0),
      schwingerN params Λ₁ 4 f ≤ schwingerN params Λ₂ 4 f) :
    Nonempty (CorrelationInequalityCoreModel params) := by
  rcases correlationGKSSecondModel_nonempty_of_data
      params hgriffiths_second with ⟨hgks⟩
  rcases correlationLebowitzModel_nonempty_of_data
      params hlebowitz with ⟨hleb⟩
  rcases correlationFKGModel_nonempty_of_data params hfkg with ⟨hfkgModel⟩
  exact ⟨{
    toCorrelationGKSSecondModel := hgks
    toCorrelationLebowitzModel := hleb
    toCorrelationFKGModel := hfkgModel
    schwinger_four_monotone := hfour_mono
  }⟩

/-- Construct `CorrelationInequalityCoreModel` from atomic subinterfaces plus
    explicit `k = 4` Schwinger-moment monotonicity. -/
theorem correlationInequalityCoreModel_nonempty_of_models
    (params : Phi4Params)
    [CorrelationGKSSecondModel params]
    [CorrelationLebowitzModel params]
    [CorrelationFKGModel params]
    [SchwingerNMonotoneModel params 4] :
    Nonempty (CorrelationInequalityCoreModel params) := by
  exact ⟨{
    toCorrelationGKSSecondModel := inferInstance
    toCorrelationLebowitzModel := inferInstance
    toCorrelationFKGModel := inferInstance
    schwinger_four_monotone := by
      intro Λ₁ Λ₂ h f hf hfΛ
      exact SchwingerNMonotoneModel.schwingerN_monotone
        (params := params) (k := 4) Λ₁ Λ₂ h f hf hfΛ
  }⟩

/-- Construct `CorrelationInequalityCoreModel` from GKS-II/FKG/Lebowitz data
    plus a pre-existing `k = 4` Schwinger-moment monotonicity interface. -/
theorem correlationInequalityCoreModel_nonempty_of_data_and_schwingerFourMonotone
    (params : Phi4Params)
    [SchwingerNMonotoneModel params 4]
    (hgriffiths_second : ∀ (Λ : Rectangle)
      (f₁ f₂ f₃ f₄ : TestFun2D)
      (_hf₁ : ∀ x, 0 ≤ f₁ x) (_hf₂ : ∀ x, 0 ≤ f₂ x)
      (_hf₃ : ∀ x, 0 ≤ f₃ x) (_hf₄ : ∀ x, 0 ≤ f₄ x),
      schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ ≤
        schwingerN params Λ 4 ![f₁, f₂, f₃, f₄])
    (hfkg : ∀ (Λ : Rectangle)
      (F G : FieldConfig2D → ℝ)
      (_hF_mono : ∀ ω₁ ω₂ : FieldConfig2D,
        (∀ f, (∀ x, 0 ≤ f x) → ω₁ f ≤ ω₂ f) → F ω₁ ≤ F ω₂)
      (_hG_mono : ∀ ω₁ ω₂ : FieldConfig2D,
        (∀ f, (∀ x, 0 ≤ f x) → ω₁ f ≤ ω₂ f) → G ω₁ ≤ G ω₂),
      (∫ ω, F ω ∂(finiteVolumeMeasure params Λ)) *
        (∫ ω, G ω ∂(finiteVolumeMeasure params Λ)) ≤
      ∫ ω, F ω * G ω ∂(finiteVolumeMeasure params Λ))
    (hlebowitz : ∀ (Λ : Rectangle)
      (f₁ f₂ f₃ f₄ : TestFun2D)
      (_hf₁ : ∀ x, 0 ≤ f₁ x) (_hf₂ : ∀ x, 0 ≤ f₂ x)
      (_hf₃ : ∀ x, 0 ≤ f₃ x) (_hf₄ : ∀ x, 0 ≤ f₄ x),
      schwingerN params Λ 4 ![f₁, f₂, f₃, f₄] ≤
        schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ +
        schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄ +
        schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃) :
    Nonempty (CorrelationInequalityCoreModel params) := by
  refine correlationInequalityCoreModel_nonempty_of_data params
    hgriffiths_second hfkg hlebowitz ?_
  intro Λ₁ Λ₂ h f hf hfΛ
  exact SchwingerNMonotoneModel.schwingerN_monotone
    (params := params) (k := 4) Λ₁ Λ₂ h f hf hfΛ

/-- Construct `CorrelationInequalityCoreModel` from GKS-II/FKG/Lebowitz data
    plus lattice-derived `k = 4` monotonicity. -/
theorem correlationInequalityCoreModel_nonempty_of_data_and_lattice_monotone
    (params : Phi4Params)
    [LatticeSchwingerNMonotoneModel params 4]
    (hgriffiths_second : ∀ (Λ : Rectangle)
      (f₁ f₂ f₃ f₄ : TestFun2D)
      (_hf₁ : ∀ x, 0 ≤ f₁ x) (_hf₂ : ∀ x, 0 ≤ f₂ x)
      (_hf₃ : ∀ x, 0 ≤ f₃ x) (_hf₄ : ∀ x, 0 ≤ f₄ x),
      schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ ≤
        schwingerN params Λ 4 ![f₁, f₂, f₃, f₄])
    (hfkg : ∀ (Λ : Rectangle)
      (F G : FieldConfig2D → ℝ)
      (_hF_mono : ∀ ω₁ ω₂ : FieldConfig2D,
        (∀ f, (∀ x, 0 ≤ f x) → ω₁ f ≤ ω₂ f) → F ω₁ ≤ F ω₂)
      (_hG_mono : ∀ ω₁ ω₂ : FieldConfig2D,
        (∀ f, (∀ x, 0 ≤ f x) → ω₁ f ≤ ω₂ f) → G ω₁ ≤ G ω₂),
      (∫ ω, F ω ∂(finiteVolumeMeasure params Λ)) *
        (∫ ω, G ω ∂(finiteVolumeMeasure params Λ)) ≤
      ∫ ω, F ω * G ω ∂(finiteVolumeMeasure params Λ))
    (hlebowitz : ∀ (Λ : Rectangle)
      (f₁ f₂ f₃ f₄ : TestFun2D)
      (_hf₁ : ∀ x, 0 ≤ f₁ x) (_hf₂ : ∀ x, 0 ≤ f₂ x)
      (_hf₃ : ∀ x, 0 ≤ f₃ x) (_hf₄ : ∀ x, 0 ≤ f₄ x),
      schwingerN params Λ 4 ![f₁, f₂, f₃, f₄] ≤
        schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ +
        schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄ +
        schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃) :
    Nonempty (CorrelationInequalityCoreModel params) := by
  letI : SchwingerNMonotoneModel params 4 :=
    schwingerNMonotoneModel_of_lattice (params := params) (k := 4)
  exact correlationInequalityCoreModel_nonempty_of_data_and_schwingerFourMonotone
    params hgriffiths_second hfkg hlebowitz

/-- Build the full `CorrelationInequalityModel` from:
    1. lattice bridge inputs for GKS-I and 2-point monotonicity, and
    2. remaining core assumptions (GKS-II, FKG, Lebowitz, 4-point monotonicity). -/
def correlationInequalityModelOfLattice
    (params : Phi4Params)
    [LatticeGriffithsFirstModel params]
    [LatticeSchwingerTwoMonotoneModel params]
    [CorrelationInequalityCoreModel params] :
    CorrelationInequalityModel params where
  griffiths_first := griffiths_first_from_lattice (params := params)
  griffiths_second := CorrelationGKSSecondModel.griffiths_second (params := params)
  fkg_inequality := CorrelationFKGModel.fkg_inequality (params := params)
  lebowitz_inequality := CorrelationLebowitzModel.lebowitz_inequality (params := params)
  schwinger_four_monotone := CorrelationInequalityCoreModel.schwinger_four_monotone (params := params)
  schwinger_two_monotone := schwinger_two_monotone_from_lattice (params := params)

/-- Lattice bridge data and core assumptions provide a concrete
    `CorrelationInequalityModel`. -/
theorem correlationInequalityModel_nonempty_of_lattice
    (params : Phi4Params)
    [LatticeGriffithsFirstModel params]
    [LatticeSchwingerTwoMonotoneModel params]
    [CorrelationInequalityCoreModel params] :
    Nonempty (CorrelationInequalityModel params) := by
  exact ⟨correlationInequalityModelOfLattice params⟩

/-- Construct `CorrelationInequalityModel` from:
    1. lattice GKS-I and two-point monotonicity bridges,
    2. GKS-II/FKG/Lebowitz data, and
    3. a pre-existing `k = 4` Schwinger-moment monotonicity interface. -/
theorem correlationInequalityModel_nonempty_of_lattice_and_core_data
    (params : Phi4Params)
    [LatticeGriffithsFirstModel params]
    [LatticeSchwingerTwoMonotoneModel params]
    [SchwingerNMonotoneModel params 4]
    (hgriffiths_second : ∀ (Λ : Rectangle)
      (f₁ f₂ f₃ f₄ : TestFun2D)
      (_hf₁ : ∀ x, 0 ≤ f₁ x) (_hf₂ : ∀ x, 0 ≤ f₂ x)
      (_hf₃ : ∀ x, 0 ≤ f₃ x) (_hf₄ : ∀ x, 0 ≤ f₄ x),
      schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ ≤
        schwingerN params Λ 4 ![f₁, f₂, f₃, f₄])
    (hfkg : ∀ (Λ : Rectangle)
      (F G : FieldConfig2D → ℝ)
      (_hF_mono : ∀ ω₁ ω₂ : FieldConfig2D,
        (∀ f, (∀ x, 0 ≤ f x) → ω₁ f ≤ ω₂ f) → F ω₁ ≤ F ω₂)
      (_hG_mono : ∀ ω₁ ω₂ : FieldConfig2D,
        (∀ f, (∀ x, 0 ≤ f x) → ω₁ f ≤ ω₂ f) → G ω₁ ≤ G ω₂),
      (∫ ω, F ω ∂(finiteVolumeMeasure params Λ)) *
        (∫ ω, G ω ∂(finiteVolumeMeasure params Λ)) ≤
      ∫ ω, F ω * G ω ∂(finiteVolumeMeasure params Λ))
    (hlebowitz : ∀ (Λ : Rectangle)
      (f₁ f₂ f₃ f₄ : TestFun2D)
      (_hf₁ : ∀ x, 0 ≤ f₁ x) (_hf₂ : ∀ x, 0 ≤ f₂ x)
      (_hf₃ : ∀ x, 0 ≤ f₃ x) (_hf₄ : ∀ x, 0 ≤ f₄ x),
      schwingerN params Λ 4 ![f₁, f₂, f₃, f₄] ≤
        schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ +
        schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄ +
        schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃) :
    Nonempty (CorrelationInequalityModel params) := by
  rcases correlationInequalityCoreModel_nonempty_of_data_and_schwingerFourMonotone
      params hgriffiths_second hfkg hlebowitz with ⟨hcore⟩
  letI : CorrelationInequalityCoreModel params := hcore
  exact correlationInequalityModel_nonempty_of_lattice params

/-- Construct `CorrelationInequalityModel` from:
    1. lattice GKS-I and two-point monotonicity bridges, and
    2. GKS-II/FKG/Lebowitz data with lattice-derived `k = 4` monotonicity. -/
theorem correlationInequalityModel_nonempty_of_lattice_and_core_data_and_lattice_monotone
    (params : Phi4Params)
    [LatticeGriffithsFirstModel params]
    [LatticeSchwingerTwoMonotoneModel params]
    [LatticeSchwingerNMonotoneModel params 4]
    (hgriffiths_second : ∀ (Λ : Rectangle)
      (f₁ f₂ f₃ f₄ : TestFun2D)
      (_hf₁ : ∀ x, 0 ≤ f₁ x) (_hf₂ : ∀ x, 0 ≤ f₂ x)
      (_hf₃ : ∀ x, 0 ≤ f₃ x) (_hf₄ : ∀ x, 0 ≤ f₄ x),
      schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ ≤
        schwingerN params Λ 4 ![f₁, f₂, f₃, f₄])
    (hfkg : ∀ (Λ : Rectangle)
      (F G : FieldConfig2D → ℝ)
      (_hF_mono : ∀ ω₁ ω₂ : FieldConfig2D,
        (∀ f, (∀ x, 0 ≤ f x) → ω₁ f ≤ ω₂ f) → F ω₁ ≤ F ω₂)
      (_hG_mono : ∀ ω₁ ω₂ : FieldConfig2D,
        (∀ f, (∀ x, 0 ≤ f x) → ω₁ f ≤ ω₂ f) → G ω₁ ≤ G ω₂),
      (∫ ω, F ω ∂(finiteVolumeMeasure params Λ)) *
        (∫ ω, G ω ∂(finiteVolumeMeasure params Λ)) ≤
      ∫ ω, F ω * G ω ∂(finiteVolumeMeasure params Λ))
    (hlebowitz : ∀ (Λ : Rectangle)
      (f₁ f₂ f₃ f₄ : TestFun2D)
      (_hf₁ : ∀ x, 0 ≤ f₁ x) (_hf₂ : ∀ x, 0 ≤ f₂ x)
      (_hf₃ : ∀ x, 0 ≤ f₃ x) (_hf₄ : ∀ x, 0 ≤ f₄ x),
      schwingerN params Λ 4 ![f₁, f₂, f₃, f₄] ≤
        schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ +
        schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄ +
        schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃) :
    Nonempty (CorrelationInequalityModel params) := by
  exact correlationInequalityModel_nonempty_of_lattice_and_core_data
    params hgriffiths_second hfkg hlebowitz

/-- Construct `CorrelationInequalityModel` from:
    1. lattice GKS-I/two-point monotonicity bridges, and
    2. atomic four-point inequality/FKG interfaces plus explicit
       `k = 4` Schwinger-moment monotonicity. -/
theorem correlationInequalityModel_nonempty_of_lattice_and_core_models
    (params : Phi4Params)
    [LatticeGriffithsFirstModel params]
    [LatticeSchwingerTwoMonotoneModel params]
    [CorrelationGKSSecondModel params]
    [CorrelationLebowitzModel params]
    [CorrelationFKGModel params]
    [SchwingerNMonotoneModel params 4] :
    Nonempty (CorrelationInequalityModel params) := by
  rcases correlationInequalityCoreModel_nonempty_of_models
      (params := params) with ⟨hcore⟩
  letI : CorrelationInequalityCoreModel params := hcore
  exact correlationInequalityModel_nonempty_of_lattice params

/-- Lattice-monotonicity specialization of
    `correlationInequalityModel_nonempty_of_lattice_and_core_models`. -/
theorem correlationInequalityModel_nonempty_of_lattice_and_core_models_and_lattice_monotone
    (params : Phi4Params)
    [LatticeGriffithsFirstModel params]
    [LatticeSchwingerTwoMonotoneModel params]
    [CorrelationGKSSecondModel params]
    [CorrelationLebowitzModel params]
    [CorrelationFKGModel params]
    [LatticeSchwingerNMonotoneModel params 4] :
    Nonempty (CorrelationInequalityModel params) := by
  letI : SchwingerNMonotoneModel params 4 :=
    schwingerNMonotoneModel_of_lattice (params := params) (k := 4)
  exact correlationInequalityModel_nonempty_of_lattice_and_core_models
    (params := params)

/-- Low-priority instance: if lattice bridge data and the remaining core
    inequalities are available, synthesize the full correlation-inequality model. -/
instance (priority := 100) correlationInequalityModel_of_lattice
    (params : Phi4Params)
    [LatticeGriffithsFirstModel params]
    [LatticeSchwingerTwoMonotoneModel params]
    [CorrelationInequalityCoreModel params] :
    CorrelationInequalityModel params :=
  correlationInequalityModelOfLattice params

/-- Lattice bridge data yields the two-point correlation-inequality subinterface. -/
instance (priority := 100) correlationTwoPointModel_of_lattice
    (params : Phi4Params)
    [LatticeGriffithsFirstModel params]
    [LatticeSchwingerTwoMonotoneModel params] :
    CorrelationTwoPointModel params where
  griffiths_first := griffiths_first_from_lattice (params := params)
  schwinger_two_monotone := schwinger_two_monotone_from_lattice (params := params)

/-- Core assumptions provide the four-point correlation-inequality subinterface. -/
instance (priority := 100) correlationFourPointModel_of_core
    (params : Phi4Params)
    [CorrelationInequalityCoreModel params] :
    CorrelationFourPointModel params where
  toCorrelationFourPointInequalityModel := {
    griffiths_second := CorrelationGKSSecondModel.griffiths_second (params := params)
    lebowitz_inequality := CorrelationLebowitzModel.lebowitz_inequality (params := params)
  }
  schwinger_four_monotone := CorrelationInequalityCoreModel.schwinger_four_monotone (params := params)

/-- Core assumptions directly provide `k = 4` Schwinger-moment monotonicity. -/
instance (priority := 100) schwingerNMonotoneModel_four_of_core
    (params : Phi4Params)
    [CorrelationInequalityCoreModel params] :
    SchwingerNMonotoneModel params 4 where
  schwingerN_monotone := by
    intro Λ₁ Λ₂ h f hf hfΛ
    exact CorrelationInequalityCoreModel.schwinger_four_monotone
      (params := params) Λ₁ Λ₂ h f hf hfΛ

/-- Construct `CorrelationInequalityModel` from two-point data plus
    `CorrelationInequalityCoreModel`. -/
theorem correlationInequalityModel_nonempty_of_twoPoint_and_core
    (params : Phi4Params)
    [CorrelationTwoPointModel params]
    [CorrelationInequalityCoreModel params] :
    Nonempty (CorrelationInequalityModel params) := by
  letI : CorrelationGKSSecondModel params := inferInstance
  letI : CorrelationLebowitzModel params := inferInstance
  letI : CorrelationFKGModel params := inferInstance
  letI : SchwingerNMonotoneModel params 4 := inferInstance
  exact correlationInequalityModel_nonempty_of_submodels params

/-! ## Griffiths' First Inequality (GKS-I) -/

/-- **GKS-I**: For the φ⁴₂ measure dμ_Λ with P = even + linear,
    ⟨φ(f)φ(g)⟩ ≥ 0 for non-negative test functions f, g ≥ 0.

    This extends from the lattice Griffiths inequality to the continuum
    via lattice approximation. The key input is that e^{-V} is a function
    of φ with a "ferromagnetic" structure (all couplings positive). -/
theorem griffiths_first (params : Phi4Params) (Λ : Rectangle)
    [CorrelationTwoPointModel params]
    (f g : TestFun2D) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) :
    0 ≤ schwingerTwo params Λ f g := by
  exact CorrelationTwoPointModel.griffiths_first (params := params) Λ f g hf hg

/-! ## Griffiths' Second Inequality (GKS-II) -/

/-- **GKS-II** in the `(12)(34)` channel:
    ⟨φ(f₁)φ(f₂)φ(f₃)φ(f₄)⟩ ≥ ⟨φ(f₁)φ(f₂)⟩⟨φ(f₃)φ(f₄)⟩
    for non-negative test functions f₁,...,f₄ ≥ 0.

    Equivalently, the `(12)(34)` pairing-subtracted quantity is nonnegative.
    This channel inequality is one of the core inputs in the monotonicity
    arguments used for the infinite-volume limit. -/
theorem griffiths_second (params : Phi4Params) (Λ : Rectangle)
    [CorrelationGKSSecondModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ ≤
      schwingerN params Λ 4 ![f₁, f₂, f₃, f₄] := by
  exact CorrelationGKSSecondModel.griffiths_second
    (params := params) Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄

private def fin4_1 : Fin 4 := ⟨1, by decide⟩
private def fin4_2 : Fin 4 := ⟨2, by decide⟩
private def fin4_3 : Fin 4 := ⟨3, by decide⟩

private lemma schwingerN4_swap12
    (params : Phi4Params) (Λ : Rectangle)
    (f₁ f₂ f₃ f₄ : TestFun2D) :
    schwingerN params Λ 4 ![f₁, f₃, f₂, f₄] =
      schwingerN params Λ 4 ![f₁, f₂, f₃, f₄] := by
  have hperm := schwingerN_perm params Λ 4 ![f₁, f₃, f₂, f₄]
    (Equiv.swap fin4_1 fin4_2)
  simpa [fin4_1, fin4_2, Function.comp] using hperm.symm

private lemma schwingerN4_perm_01423
    (params : Phi4Params) (Λ : Rectangle)
    (f₁ f₂ f₃ f₄ : TestFun2D) :
    schwingerN params Λ 4 ![f₁, f₄, f₂, f₃] =
      schwingerN params Λ 4 ![f₁, f₂, f₃, f₄] := by
  let σ : Equiv.Perm (Fin 4) :=
    (Equiv.swap fin4_2 fin4_3) * (Equiv.swap fin4_1 fin4_2)
  have hperm := schwingerN_perm params Λ 4 ![f₁, f₂, f₃, f₄] σ
  simpa [σ, fin4_1, fin4_2, fin4_3, Function.comp, Equiv.Perm.mul_apply] using hperm

/-- GKS-II in the `(13)(24)` channel, obtained from `(12)(34)` via permutation symmetry. -/
theorem griffiths_second_13_24 (params : Phi4Params) (Λ : Rectangle)
    [CorrelationGKSSecondModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄ ≤
      schwingerN params Λ 4 ![f₁, f₂, f₃, f₄] := by
  have h := griffiths_second params Λ f₁ f₃ f₂ f₄ hf₁ hf₃ hf₂ hf₄
  calc
    schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄
        ≤ schwingerN params Λ 4 ![f₁, f₃, f₂, f₄] := h
    _ = schwingerN params Λ 4 ![f₁, f₂, f₃, f₄] :=
      schwingerN4_swap12 params Λ f₁ f₂ f₃ f₄

/-- GKS-II in the `(14)(23)` channel, obtained from `(12)(34)` via permutation symmetry. -/
theorem griffiths_second_14_23 (params : Phi4Params) (Λ : Rectangle)
    [CorrelationGKSSecondModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃ ≤
      schwingerN params Λ 4 ![f₁, f₂, f₃, f₄] := by
  have h := griffiths_second params Λ f₁ f₄ f₂ f₃ hf₁ hf₄ hf₂ hf₃
  calc
    schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃
        ≤ schwingerN params Λ 4 ![f₁, f₄, f₂, f₃] := h
    _ = schwingerN params Λ 4 ![f₁, f₂, f₃, f₄] :=
      schwingerN4_perm_01423 params Λ f₁ f₂ f₃ f₄

/-! ## Pairing-subtracted 4-point bounds -/

/-- The `(12)(34)` pairing-subtracted 4-point quantity
    `S₄ - S₂(12)S₂(34)`. -/
def truncatedFourPoint12 (params : Phi4Params) (Λ : Rectangle)
    (f₁ f₂ f₃ f₄ : TestFun2D) : ℝ :=
  schwingerN params Λ 4 ![f₁, f₂, f₃, f₄] -
    schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄

/-- The `(13)(24)` pairing-subtracted 4-point quantity
    `S₄ - S₂(13)S₂(24)`. -/
def truncatedFourPoint13 (params : Phi4Params) (Λ : Rectangle)
    (f₁ f₂ f₃ f₄ : TestFun2D) : ℝ :=
  schwingerN params Λ 4 ![f₁, f₂, f₃, f₄] -
    schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄

/-- The `(14)(23)` pairing-subtracted 4-point quantity
    `S₄ - S₂(14)S₂(23)`. -/
def truncatedFourPoint14 (params : Phi4Params) (Λ : Rectangle)
    (f₁ f₂ f₃ f₄ : TestFun2D) : ℝ :=
  schwingerN params Λ 4 ![f₁, f₂, f₃, f₄] -
    schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃

/-- Nonnegativity of the `(12)(34)` pairing-subtracted 4-point expression:
    `S₄ - S₂(12)S₂(34) ≥ 0`. -/
theorem pairing_subtracted_four_point_nonneg (params : Phi4Params) (Λ : Rectangle)
    [CorrelationGKSSecondModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    0 ≤ truncatedFourPoint12 params Λ f₁ f₂ f₃ f₄ := by
  have h := griffiths_second params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  unfold truncatedFourPoint12
  linarith

/-- Nonnegativity of the `(13)(24)` pairing-subtracted expression:
    `S₄ - S₂(13)S₂(24) ≥ 0`. -/
theorem pairing_subtracted_four_point_nonneg_13_24
    (params : Phi4Params) (Λ : Rectangle)
    [CorrelationGKSSecondModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    0 ≤ truncatedFourPoint13 params Λ f₁ f₂ f₃ f₄ := by
  have h := griffiths_second_13_24 params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  unfold truncatedFourPoint13
  linarith

/-- Nonnegativity of the `(14)(23)` pairing-subtracted expression:
    `S₄ - S₂(14)S₂(23) ≥ 0`. -/
theorem pairing_subtracted_four_point_nonneg_14_23
    (params : Phi4Params) (Λ : Rectangle)
    [CorrelationGKSSecondModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    0 ≤ truncatedFourPoint14 params Λ f₁ f₂ f₃ f₄ := by
  have h := griffiths_second_14_23 params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  unfold truncatedFourPoint14
  linarith

/-! ## FKG Inequality -/

/-- **FKG inequality**: For the φ⁴₂ measure, monotone increasing functions
    are positively correlated:
      ⟨F · G⟩ ≥ ⟨F⟩ · ⟨G⟩
    for F, G monotone increasing (in the sense of distributions).

    This is a far-reaching generalization of GKS-I and implies, among other things,
    that the 2-point function dominates the truncated 4-point function. -/
theorem fkg_inequality (params : Phi4Params) (Λ : Rectangle)
    [CorrelationFKGModel params]
    (F G : FieldConfig2D → ℝ)
    (hF_mono : ∀ ω₁ ω₂ : FieldConfig2D,
      (∀ f, (∀ x, 0 ≤ f x) → ω₁ f ≤ ω₂ f) → F ω₁ ≤ F ω₂)
    (hG_mono : ∀ ω₁ ω₂ : FieldConfig2D,
      (∀ f, (∀ x, 0 ≤ f x) → ω₁ f ≤ ω₂ f) → G ω₁ ≤ G ω₂) :
    (∫ ω, F ω ∂(finiteVolumeMeasure params Λ)) *
      (∫ ω, G ω ∂(finiteVolumeMeasure params Λ)) ≤
    ∫ ω, F ω * G ω ∂(finiteVolumeMeasure params Λ) := by
  exact CorrelationFKGModel.fkg_inequality
    (params := params) Λ F G hF_mono hG_mono

/-- FKG implies nonnegativity of the connected finite-volume two-point function
    for nonnegative test functions. -/
theorem connectedSchwingerTwo_nonneg
    (params : Phi4Params) (Λ : Rectangle)
    [CorrelationFKGModel params]
    (f g : TestFun2D)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) :
    0 ≤ connectedSchwingerTwo params Λ f g := by
  have hmonoF :
      ∀ ω₁ ω₂ : FieldConfig2D,
        (∀ h : TestFun2D, (∀ x, 0 ≤ h x) → ω₁ h ≤ ω₂ h) →
        (fun ω : FieldConfig2D => ω f) ω₁ ≤ (fun ω : FieldConfig2D => ω f) ω₂ := by
    intro ω₁ ω₂ hω
    exact hω f hf
  have hmonoG :
      ∀ ω₁ ω₂ : FieldConfig2D,
        (∀ h : TestFun2D, (∀ x, 0 ≤ h x) → ω₁ h ≤ ω₂ h) →
        (fun ω : FieldConfig2D => ω g) ω₁ ≤ (fun ω : FieldConfig2D => ω g) ω₂ := by
    intro ω₁ ω₂ hω
    exact hω g hg
  have hfkg := fkg_inequality params Λ
    (fun ω : FieldConfig2D => ω f)
    (fun ω : FieldConfig2D => ω g)
    hmonoF hmonoG
  have hfkg' :
      schwingerN params Λ 1 ![f] * schwingerN params Λ 1 ![g] ≤ schwingerTwo params Λ f g := by
    simpa [schwingerN, schwingerTwo] using hfkg
  unfold connectedSchwingerTwo
  exact sub_nonneg.mpr hfkg'

/-! ## Lebowitz Inequality -/

/-- **Lebowitz inequality**: The 4-point Schwinger function is bounded by the
    Gaussian (free field) prediction:
      ⟨φ(f₁)φ(f₂)φ(f₃)φ(f₄)⟩ ≤ ⟨φ(f₁)φ(f₂)⟩⟨φ(f₃)φ(f₄)⟩
                                    + ⟨φ(f₁)φ(f₃)⟩⟨φ(f₂)φ(f₄)⟩
                                    + ⟨φ(f₁)φ(f₄)⟩⟨φ(f₂)φ(f₃)⟩
    for f₁,...,f₄ ≥ 0.

    This is the upper bound complementing GKS-II (which gives a lower bound).
    Together, they "squeeze" the 4-point function near its Gaussian value
    for weak coupling. -/
theorem lebowitz_inequality (params : Phi4Params) (Λ : Rectangle)
    [CorrelationLebowitzModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    schwingerN params Λ 4 ![f₁, f₂, f₃, f₄] ≤
      schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ +
      schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄ +
      schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃ := by
  exact CorrelationLebowitzModel.lebowitz_inequality
    (params := params) Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄

/-- Upper bound on the `(12)(34)` pairing-subtracted expression from Lebowitz:
    `S₄ - S₂(12)S₂(34) ≤ S₂(13)S₂(24) + S₂(14)S₂(23)`. -/
theorem pairing_subtracted_four_point_upper_bound
    (params : Phi4Params) (Λ : Rectangle)
    [CorrelationLebowitzModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    truncatedFourPoint12 params Λ f₁ f₂ f₃ f₄ ≤
      schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄ +
      schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃ := by
  have h := lebowitz_inequality params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  unfold truncatedFourPoint12
  linarith

/-- Upper bound on the `(13)(24)` pairing-subtracted expression from Lebowitz:
    `S₄ - S₂(13)S₂(24) ≤ S₂(12)S₂(34) + S₂(14)S₂(23)`. -/
theorem pairing_subtracted_four_point_upper_bound_13_24
    (params : Phi4Params) (Λ : Rectangle)
    [CorrelationLebowitzModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    truncatedFourPoint13 params Λ f₁ f₂ f₃ f₄ ≤
      schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ +
      schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃ := by
  have h := lebowitz_inequality params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  unfold truncatedFourPoint13
  linarith

/-- Upper bound on the `(14)(23)` pairing-subtracted expression from Lebowitz:
    `S₄ - S₂(14)S₂(23) ≤ S₂(12)S₂(34) + S₂(13)S₂(24)`. -/
theorem pairing_subtracted_four_point_upper_bound_14_23
    (params : Phi4Params) (Λ : Rectangle)
    [CorrelationLebowitzModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    truncatedFourPoint14 params Λ f₁ f₂ f₃ f₄ ≤
      schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ +
      schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄ := by
  have h := lebowitz_inequality params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  unfold truncatedFourPoint14
  linarith

/-- Two-sided estimate for the `(12)(34)` pairing-subtracted 4-point expression. -/
theorem pairing_subtracted_four_point_bounds
    (params : Phi4Params) (Λ : Rectangle)
    [CorrelationGKSSecondModel params]
    [CorrelationLebowitzModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    0 ≤ truncatedFourPoint12 params Λ f₁ f₂ f₃ f₄ ∧
      truncatedFourPoint12 params Λ f₁ f₂ f₃ f₄ ≤
      schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄ +
      schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃ := by
  constructor
  · exact pairing_subtracted_four_point_nonneg
      params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  · exact pairing_subtracted_four_point_upper_bound
      params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄

/-- Absolute-value control of the `(12)(34)` pairing-subtracted 4-point expression:
    `|S₄ - S₂(12)S₂(34)| ≤ S₂(13)S₂(24) + S₂(14)S₂(23)`. -/
theorem pairing_subtracted_four_point_abs_bound
    (params : Phi4Params) (Λ : Rectangle)
    [CorrelationGKSSecondModel params]
    [CorrelationLebowitzModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    |truncatedFourPoint12 params Λ f₁ f₂ f₃ f₄| ≤
      schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄ +
      schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃ := by
  have hnonneg := pairing_subtracted_four_point_nonneg
    params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  have hupper := pairing_subtracted_four_point_upper_bound
    params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  simpa [abs_of_nonneg hnonneg] using hupper

/-- Absolute-value control of the `(13)(24)` pairing-subtracted expression:
    `|S₄ - S₂(13)S₂(24)| ≤ S₂(12)S₂(34) + S₂(14)S₂(23)`. -/
theorem pairing_subtracted_four_point_abs_bound_13_24
    (params : Phi4Params) (Λ : Rectangle)
    [CorrelationGKSSecondModel params]
    [CorrelationLebowitzModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    |truncatedFourPoint13 params Λ f₁ f₂ f₃ f₄| ≤
      schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ +
      schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃ := by
  have hnonneg := pairing_subtracted_four_point_nonneg_13_24
    params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  have hupper := pairing_subtracted_four_point_upper_bound_13_24
    params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  simpa [abs_of_nonneg hnonneg] using hupper

/-- Absolute-value control of the `(14)(23)` pairing-subtracted expression:
    `|S₄ - S₂(14)S₂(23)| ≤ S₂(12)S₂(34) + S₂(13)S₂(24)`. -/
theorem pairing_subtracted_four_point_abs_bound_14_23
    (params : Phi4Params) (Λ : Rectangle)
    [CorrelationGKSSecondModel params]
    [CorrelationLebowitzModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    |truncatedFourPoint14 params Λ f₁ f₂ f₃ f₄| ≤
      schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ +
      schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄ := by
  have hnonneg := pairing_subtracted_four_point_nonneg_14_23
    params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  have hupper := pairing_subtracted_four_point_upper_bound_14_23
    params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  simpa [abs_of_nonneg hnonneg] using hupper

/-! ## Fully connected 4-point bounds -/

/-- Fully pairing-subtracted 4-point cumulant:
    `S₄ - (S₂(12)S₂(34) + S₂(13)S₂(24) + S₂(14)S₂(23))`.
    For Gaussian measures this vanishes identically. -/
def cumulantFourPoint (params : Phi4Params) (Λ : Rectangle)
    (f₁ f₂ f₃ f₄ : TestFun2D) : ℝ :=
  schwingerN params Λ 4 ![f₁, f₂, f₃, f₄] -
    (schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ +
      schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄ +
      schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃)

/-- Lebowitz implies nonpositivity of the fully connected 4-point cumulant. -/
theorem cumulantFourPoint_nonpos
    (params : Phi4Params) (Λ : Rectangle)
    [CorrelationLebowitzModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    cumulantFourPoint params Λ f₁ f₂ f₃ f₄ ≤ 0 := by
  have hleb := lebowitz_inequality params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  unfold cumulantFourPoint
  linarith

/-- GKS-II yields a lower bound on the fully connected 4-point cumulant. -/
theorem cumulantFourPoint_lower_bound
    (params : Phi4Params) (Λ : Rectangle)
    [CorrelationGKSSecondModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    -(schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄ +
      schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃) ≤
      cumulantFourPoint params Λ f₁ f₂ f₃ f₄ := by
  have hgks := griffiths_second params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  unfold cumulantFourPoint
  linarith

/-- Absolute-value control of the fully connected 4-point cumulant. -/
theorem cumulantFourPoint_abs_bound
    (params : Phi4Params) (Λ : Rectangle)
    [CorrelationGKSSecondModel params]
    [CorrelationLebowitzModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    |cumulantFourPoint params Λ f₁ f₂ f₃ f₄| ≤
      schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄ +
      schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃ := by
  have hnonpos := cumulantFourPoint_nonpos params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  have hlower := cumulantFourPoint_lower_bound params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  rw [abs_of_nonpos hnonpos]
  linarith

/-! ## All-channel combined bounds -/

/-- Combined 4-point bounds:
    every GKS-II pairing channel gives a lower bound, and Lebowitz gives the upper bound. -/
theorem schwinger_four_bounds_all_channels
    (params : Phi4Params) (Λ : Rectangle)
    [CorrelationGKSSecondModel params]
    [CorrelationLebowitzModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    max (schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄)
      (max (schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄)
        (schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃))
      ≤ schwingerN params Λ 4 ![f₁, f₂, f₃, f₄] ∧
    schwingerN params Λ 4 ![f₁, f₂, f₃, f₄] ≤
      schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ +
      schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄ +
      schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃ := by
  have h12 := griffiths_second params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  have h13 := griffiths_second_13_24 params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  have h14 := griffiths_second_14_23 params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  have hupper := lebowitz_inequality params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  constructor
  · exact max_le h12 (max_le h13 h14)
  · exact hupper

/-- Three channel-wise lower bounds on the fully connected 4-point cumulant. -/
theorem cumulantFourPoint_lower_bounds_all_channels
    (params : Phi4Params) (Λ : Rectangle)
    [CorrelationGKSSecondModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    -(schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄ +
      schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃)
      ≤ cumulantFourPoint params Λ f₁ f₂ f₃ f₄ ∧
    -(schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ +
      schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃)
      ≤ cumulantFourPoint params Λ f₁ f₂ f₃ f₄ ∧
    -(schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ +
      schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄)
      ≤ cumulantFourPoint params Λ f₁ f₂ f₃ f₄ := by
  have h12 := griffiths_second params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  have h13 := griffiths_second_13_24 params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  have h14 := griffiths_second_14_23 params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  unfold cumulantFourPoint
  constructor
  · linarith
  · constructor
    · linarith
    · linarith

/-- Alternative absolute-value bound using the `(13)(24)` GKS-II lower channel. -/
theorem cumulantFourPoint_abs_bound_alt13
    (params : Phi4Params) (Λ : Rectangle)
    [CorrelationGKSSecondModel params]
    [CorrelationLebowitzModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    |cumulantFourPoint params Λ f₁ f₂ f₃ f₄| ≤
      schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ +
      schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃ := by
  have hnonpos := cumulantFourPoint_nonpos params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  have hLowerAll := cumulantFourPoint_lower_bounds_all_channels
    params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  rcases hLowerAll with ⟨_, h13, _⟩
  rw [abs_of_nonpos hnonpos]
  linarith

/-- Alternative absolute-value bound using the `(14)(23)` GKS-II lower channel. -/
theorem cumulantFourPoint_abs_bound_alt14
    (params : Phi4Params) (Λ : Rectangle)
    [CorrelationGKSSecondModel params]
    [CorrelationLebowitzModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    |cumulantFourPoint params Λ f₁ f₂ f₃ f₄| ≤
      schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ +
      schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄ := by
  have hnonpos := cumulantFourPoint_nonpos params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  have hLowerAll := cumulantFourPoint_lower_bounds_all_channels
    params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  rcases hLowerAll with ⟨_, _, h14⟩
  rw [abs_of_nonpos hnonpos]
  linarith

/-- Absolute value of the connected 4-point cumulant is bounded by the minimum
    of the three two-pair channel sums. -/
theorem cumulantFourPoint_abs_bound_min_channels
    (params : Phi4Params) (Λ : Rectangle)
    [CorrelationGKSSecondModel params]
    [CorrelationLebowitzModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    |cumulantFourPoint params Λ f₁ f₂ f₃ f₄| ≤
      min
        (schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄ +
          schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃)
        (min
          (schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ +
            schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃)
          (schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ +
            schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄)) := by
  have h12 := cumulantFourPoint_abs_bound params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  have h13 := cumulantFourPoint_abs_bound_alt13 params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  have h14 := cumulantFourPoint_abs_bound_alt14 params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  exact le_min h12 (le_min h13 h14)

/-! ## Monotonicity of Schwinger functions in volume

The combination of GKS-II with Dirichlet monotonicity gives:
  Λ₁ ⊂ Λ₂ ⟹ S_{Λ₁}(f₁,...,fₙ) ≤ S_{Λ₂}(f₁,...,fₙ)
for non-negative test functions. -/

/-- **Dirichlet monotonicity of 4-point function** under domain inclusion for
    nonnegative test-function inputs supported in the smaller volume. -/
theorem schwinger_four_monotone (params : Phi4Params) (Λ₁ Λ₂ : Rectangle)
    [SchwingerNMonotoneModel params 4]
    (h : Λ₁.toSet ⊆ Λ₂.toSet)
    (f : Fin 4 → TestFun2D)
    (hf : ∀ i, ∀ x, 0 ≤ f i x)
    (hfΛ : ∀ i, ∀ x ∉ Λ₁.toSet, f i x = 0) :
    schwingerN params Λ₁ 4 f ≤ schwingerN params Λ₂ 4 f := by
  exact SchwingerNMonotoneModel.schwingerN_monotone
    (params := params) (k := 4) Λ₁ Λ₂ h f hf hfΛ

/-- **Dirichlet monotonicity of 2-point function**: For Λ₁ ⊂ Λ₂,
    S₂^{Λ₁}(f,g) ≤ S₂^{Λ₂}(f,g) for f, g ≥ 0.

    Proof: Dirichlet BC on the smaller region gives a smaller covariance,
    and by GKS-II the 2-point function is monotone in the covariance. -/
theorem schwinger_two_monotone (params : Phi4Params) (Λ₁ Λ₂ : Rectangle)
    [CorrelationTwoPointModel params]
    (h : Λ₁.toSet ⊆ Λ₂.toSet)
    (f g : TestFun2D) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfΛ : ∀ x ∉ Λ₁.toSet, f x = 0) (hgΛ : ∀ x ∉ Λ₁.toSet, g x = 0) :
    schwingerTwo params Λ₁ f g ≤ schwingerTwo params Λ₂ f g := by
  exact CorrelationTwoPointModel.schwinger_two_monotone
    (params := params) Λ₁ Λ₂ h f g hf hg hfΛ hgΛ

end

/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.FiniteVolumeMeasure

/-!
# Reflection Positivity

Reflection positivity (RP) is the Euclidean counterpart of unitarity (positivity of
the Hilbert space inner product). It states that for any functional F of the field
in the positive-time half-space,
  ⟨F, θF⟩ ≥ 0
where θ is time reflection (τ ↦ -τ).

RP holds for:
1. The free covariance C = (-Δ + m²)⁻¹ (intrinsic property)
2. The Dirichlet covariance C_Λ^D (inherited from free)
3. The interacting measure dμ_Λ (for symmetric Λ, via checkerboard decomposition)

RP is OS axiom E2 and is the key to constructing the physical Hilbert space
from the Euclidean theory.

## References

* [Glimm-Jaffe] Sections 7.10, 10.4
* [Osterwalder-Schrader I] Section on reflection positivity
-/

noncomputable section

open MeasureTheory

/-! ## Time reflection on field configurations -/

/-- Time reflection on spacetime: (τ, x) ↦ (-τ, x).
    Convention: coordinate 0 = Euclidean time, coordinate 1 = space. -/
def timeReflect2D (p : Spacetime2D) : Spacetime2D :=
  EuclideanSpace.equiv (Fin 2) ℝ |>.symm (fun i => if i = 0 then -p i else p i)

/-- Coordinate access for timeReflect2D. -/
@[simp]
theorem timeReflect2D_apply (p : Spacetime2D) (i : Fin 2) :
    timeReflect2D p i = if i = 0 then -p i else p i := by
  simp [timeReflect2D]

/-- Time reflection is an involution. -/
theorem timeReflect2D_involution (p : Spacetime2D) :
    timeReflect2D (timeReflect2D p) = p := by
  ext i; by_cases h : i = 0 <;> simp [h]

/-- Time reflection preserves the norm. -/
theorem timeReflect2D_norm_eq (p : Spacetime2D) :
    ‖timeReflect2D p‖ = ‖p‖ := by
  simp only [EuclideanSpace.norm_eq]
  congr 1
  apply Finset.sum_congr rfl; intro i _
  simp [apply_ite (· ^ 2)]

/-- Time reflection as a continuous linear equivalence. -/
def timeReflectCLE : Spacetime2D ≃L[ℝ] Spacetime2D :=
  let e : Spacetime2D ≃ₗ[ℝ] Spacetime2D :=
    { toFun := timeReflect2D
      invFun := timeReflect2D
      left_inv := timeReflect2D_involution
      right_inv := timeReflect2D_involution
      map_add' := fun x y => by
        ext i; simp only [timeReflect2D_apply]
        by_cases h : i = 0 <;> simp [h, add_comm]
      map_smul' := fun c x => by
        ext i; simp only [timeReflect2D_apply, RingHom.id_apply]
        by_cases h : i = 0 <;> simp [h, mul_neg] }
  { e with
    continuous_toFun := e.toLinearMap.continuous_of_finiteDimensional
    continuous_invFun := e.symm.toLinearMap.continuous_of_finiteDimensional }

/-- Time reflection on test functions: (θf)(τ, x) = f(-τ, x).
    Defined using `compCLMOfContinuousLinearEquiv` applied to the time reflection CLE. -/
def testFunTimeReflect (f : TestFun2D) : TestFun2D :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ timeReflectCLE f

/-- A test function is supported in positive time if f(τ,x) = 0 for τ ≤ 0. -/
def supportedInPositiveTime (f : TestFun2D) : Prop :=
  ∀ x : Spacetime2D, x 0 ≤ 0 → f x = 0

/-! ## Abstract reflection-positivity interfaces -/

/-- Free Gaussian reflection positivity at fixed mass. This packages the analytic
    RP proof for `freeFieldMeasure` as an explicit assumption interface. -/
class FreeReflectionPositivityModel (mass : ℝ) (hmass : 0 < mass) where
  free_covariance_reflection_positive :
    ∀ (n : ℕ) (f : Fin n → TestFun2D) (c : Fin n → ℂ),
      (∀ i, supportedInPositiveTime (f i)) →
      0 ≤ (∑ i, ∑ j, c i * starRingEnd ℂ (c j) *
        ∫ ω, ω (testFunTimeReflect (f i)) * ω (f j)
          ∂(freeFieldMeasure mass hmass)).re

/-- Dirichlet covariance reflection positivity on time-symmetric rectangles. -/
class DirichletReflectionPositivityModel (mass : ℝ) (hmass : 0 < mass) where
  dirichlet_covariance_reflection_positive :
    ∀ [BoundaryKernelModel mass hmass] (Λ : Rectangle),
      Λ.IsTimeSymmetric →
      ∀ (n : ℕ) (f : Fin n → TestFun2D) (c : Fin n → ℂ),
      (∀ i, supportedInPositiveTime (f i)) →
      0 ≤ (∑ i, ∑ j, c i * starRingEnd ℂ (c j) *
        ↑(∫ x, ∫ y, (testFunTimeReflect (f i)) x * dirichletCov Λ mass hmass x y * (f j) y)).re

/-- Interacting finite-volume reflection positivity on time-symmetric rectangles. -/
class InteractingReflectionPositivityModel (params : Phi4Params) where
  interacting_measure_reflection_positive :
    ∀ (Λ : Rectangle), Λ.IsTimeSymmetric →
      ∀ (n : ℕ) (f : Fin n → TestFun2D) (c : Fin n → ℂ),
      (∀ i, supportedInPositiveTime (f i)) →
      0 ≤ (∑ i, ∑ j, c i * starRingEnd ℂ (c j) *
        ∫ ω, ω (testFunTimeReflect (f i)) * ω (f j)
          ∂(finiteVolumeMeasure params Λ)).re

/-! ## Reflection positivity of the free covariance -/

/-- **Reflection positivity of the free covariance** (Glimm-Jaffe 7.10):
    For the free covariance C = (-Δ + m²)⁻¹ on ℝ²,
      Σᵢⱼ c̄ᵢ cⱼ C(θfᵢ, fⱼ) ≥ 0
    for any test functions f₁,...,fₙ supported in positive time {τ > 0}
    and any complex coefficients c₁,...,cₙ.

    Proof idea: In Fourier space, C(θf, g) = ∫ f̂(-p₀, p⃗)* ĝ(p₀, p⃗) / (p₀² + p⃗² + m²) dp.
    Writing p₀ = iE for the "energy" continuation, this becomes a positive form. -/
theorem free_covariance_reflection_positive (mass : ℝ) (hmass : 0 < mass)
    [FreeReflectionPositivityModel mass hmass]
    (n : ℕ) (f : Fin n → TestFun2D) (c : Fin n → ℂ)
    (hf : ∀ i, supportedInPositiveTime (f i)) :
    0 ≤ (∑ i, ∑ j, c i * starRingEnd ℂ (c j) *
      ∫ ω, ω (testFunTimeReflect (f i)) * ω (f j)
        ∂(freeFieldMeasure mass hmass)).re := by
  exact FreeReflectionPositivityModel.free_covariance_reflection_positive
    (mass := mass) (hmass := hmass) n f c hf

/-! ## Reflection positivity of the Dirichlet covariance -/

/-- The Dirichlet covariance inherits reflection positivity from the free covariance,
    because C_D ≤ C and the difference C - C_D is supported on the boundary.

    Note: RP requires complex coefficients c_i ∈ ℂ with the sesquilinear form
    Σᵢⱼ c̄ᵢ cⱼ C(θfᵢ, fⱼ) ≥ 0, matching the form used in `free_covariance_reflection_positive`
    and `OsterwalderSchraderAxioms.E2_reflection_positive`. -/
theorem dirichlet_covariance_reflection_positive
    (Λ : Rectangle) (hΛ : Λ.IsTimeSymmetric)
    (mass : ℝ) (hmass : 0 < mass)
    [BoundaryKernelModel mass hmass]
    [DirichletReflectionPositivityModel mass hmass]
    (n : ℕ) (f : Fin n → TestFun2D) (c : Fin n → ℂ)
    (hf : ∀ i, supportedInPositiveTime (f i)) :
    0 ≤ (∑ i, ∑ j, c i * starRingEnd ℂ (c j) *
      ↑(∫ x, ∫ y, (testFunTimeReflect (f i)) x * dirichletCov Λ mass hmass x y * (f j) y)).re := by
  exact DirichletReflectionPositivityModel.dirichlet_covariance_reflection_positive
    (mass := mass) (hmass := hmass) Λ hΛ n f c hf

/-! ## Reflection positivity of the interacting measure -/

/-- **Reflection positivity of the finite-volume φ⁴₂ measure** (Glimm-Jaffe 10.4):
    For a time-symmetric region Λ = Λ₊ ∪ θΛ₊,
      Σᵢⱼ c̄ᵢ cⱼ ∫ θFᵢ · Fⱼ dμ_Λ ≥ 0
    for any "positive-time" functionals Fᵢ.

    The proof uses the checkerboard decomposition:
    1. Write V_Λ = V_{Λ₊} + V_{θΛ₊} (interaction splits by time reflection)
    2. Use RP of the free covariance for the Gaussian part
    3. The interaction terms factorize correctly because V is time-local -/
theorem interacting_measure_reflection_positive (params : Phi4Params)
    [InteractingReflectionPositivityModel params]
    (Λ : Rectangle) (hΛ : Λ.IsTimeSymmetric)
    (n : ℕ) (f : Fin n → TestFun2D) (c : Fin n → ℂ)
    (hf : ∀ i, supportedInPositiveTime (f i)) :
    0 ≤ (∑ i, ∑ j, c i * starRingEnd ℂ (c j) *
      ∫ ω, ω (testFunTimeReflect (f i)) * ω (f j)
        ∂(finiteVolumeMeasure params Λ)).re := by
  exact InteractingReflectionPositivityModel.interacting_measure_reflection_positive
    (params := params) Λ hΛ n f c hf

end

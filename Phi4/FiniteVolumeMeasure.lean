/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.Interaction

/-!
# Finite Volume φ⁴₂ Measure

The finite-volume interacting measure is
  dμ_Λ = Z_Λ⁻¹ exp(-V_Λ) dφ_C
where V_Λ = λ ∫_Λ :φ⁴: dx is the interaction and Z_Λ = ∫ exp(-V_Λ) dφ_C is the
partition function. By Theorem 8.6.2, this is a well-defined probability measure.

The Schwinger functions (correlation functions) are
  S_n^Λ(f₁,...,fₙ) = ∫ φ(f₁)⋯φ(fₙ) dμ_Λ

## Main definitions

* `finiteVolumeMeasure` — dμ_Λ = Z_Λ⁻¹ e^{-V_Λ} dφ_C
* `partitionFunction` — Z_Λ = ∫ e^{-V_Λ} dφ_C
* `schwingerTwo` — 2-point Schwinger function S₂^Λ(f,g) = ⟨φ(f)φ(g)⟩_Λ

## References

* [Glimm-Jaffe] Sections 8.6, 11.2
-/

noncomputable section

open MeasureTheory

/-! ## Partition function -/

/-- The partition function Z_Λ = ∫ exp(-V_Λ) dφ_C.
    By Theorem 8.6.2, this is finite and positive. -/
def partitionFunction (params : Phi4Params) (Λ : Rectangle) : ℝ :=
  ∫ ω, Real.exp (-(interaction params Λ ω)) ∂(freeFieldMeasure params.mass params.mass_pos)

/-! ## Finite volume measure -/

/-- The finite-volume interacting measure:
    dμ_Λ = Z_Λ⁻¹ exp(-V_Λ) dφ_C.
    This is a probability measure on S'(ℝ²). -/
def finiteVolumeMeasure (params : Phi4Params) (Λ : Rectangle) :
    @Measure FieldConfig2D GaussianField.instMeasurableSpaceConfiguration :=
  ENNReal.ofReal (partitionFunction params Λ)⁻¹ •
    (freeFieldMeasure params.mass params.mass_pos).withDensity
      (fun ω => ENNReal.ofReal (Real.exp (-(interaction params Λ ω))))

/-- The finite-volume measure is a probability measure. -/
theorem finiteVolumeMeasure_isProbability (params : Phi4Params) (Λ : Rectangle) :
    IsProbabilityMeasure (finiteVolumeMeasure params Λ) := by
  sorry

/-! ## Schwinger functions (correlation functions) -/

/-- The 2-point Schwinger function in finite volume:
    S₂^Λ(f, g) = ∫ ω(f) · ω(g) dμ_Λ(ω) = ⟨φ(f)φ(g)⟩_Λ. -/
def schwingerTwo (params : Phi4Params) (Λ : Rectangle)
    (f g : TestFun2D) : ℝ :=
  ∫ ω, ω f * ω g ∂(finiteVolumeMeasure params Λ)

/-- The n-point Schwinger function in finite volume:
    S_n^Λ(f₁,...,fₙ) = ∫ ω(f₁)⋯ω(fₙ) dμ_Λ(ω). -/
def schwingerN (params : Phi4Params) (Λ : Rectangle) (n : ℕ)
    (f : Fin n → TestFun2D) : ℝ :=
  ∫ ω, (∏ i, ω (f i)) ∂(finiteVolumeMeasure params Λ)

/-- The generating functional (Laplace transform) in finite volume:
    S_Λ{g} = ∫ exp(⟨ω, g⟩) dμ_Λ(ω) for real test functions g. -/
def generatingFunctional (params : Phi4Params) (Λ : Rectangle)
    (g : TestFun2D) : ℝ :=
  ∫ ω, Real.exp (ω g) ∂(finiteVolumeMeasure params Λ)

/-! ## Basic properties -/

/-- Symmetry of the 2-point function: S₂(f,g) = S₂(g,f). -/
theorem schwingerTwo_symm (params : Phi4Params) (Λ : Rectangle)
    (f g : TestFun2D) :
    schwingerTwo params Λ f g = schwingerTwo params Λ g f := by
  simp only [schwingerTwo, mul_comm]

/-- The n-point Schwinger function is symmetric under permutations. -/
theorem schwingerN_perm (params : Phi4Params) (Λ : Rectangle) (n : ℕ)
    (f : Fin n → TestFun2D) (σ : Equiv.Perm (Fin n)) :
    schwingerN params Λ n (f ∘ σ) = schwingerN params Λ n f := by
  sorry

/-- The Schwinger functions are multilinear in each argument. -/
theorem schwingerN_multilinear (params : Phi4Params) (Λ : Rectangle) (n : ℕ)
    (f g : Fin n → TestFun2D) (c : ℝ) (i : Fin n) :
    schwingerN params Λ n (Function.update f i (c • f i + g i)) =
      c * schwingerN params Λ n f +
        schwingerN params Λ n (Function.update f i (g i)) := by
  sorry

/-- The 2-point function is bounded by the free field 2-point function
    (for the φ⁴ interaction with λ > 0). This is a consequence of the
    Lebowitz inequality. -/
theorem schwingerTwo_le_free (params : Phi4Params) (Λ : Rectangle)
    (f g : TestFun2D) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) :
    schwingerTwo params Λ f g ≤
      ∫ ω, ω f * ω g ∂(freeFieldMeasure params.mass params.mass_pos) := by
  sorry

end

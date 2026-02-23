/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.FiniteVolumeMeasure

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

/-! ## Griffiths' First Inequality (GKS-I) -/

/-- **GKS-I**: For the φ⁴₂ measure dμ_Λ with P = even + linear,
    ⟨φ(f)φ(g)⟩ ≥ 0 for non-negative test functions f, g ≥ 0.

    This extends from the lattice Griffiths inequality to the continuum
    via lattice approximation. The key input is that e^{-V} is a function
    of φ with a "ferromagnetic" structure (all couplings positive). -/
theorem griffiths_first (params : Phi4Params) (Λ : Rectangle)
    (f g : TestFun2D) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) :
    0 ≤ schwingerTwo params Λ f g := by
  sorry

/-! ## Griffiths' Second Inequality (GKS-II) -/

/-- **GKS-II**: The truncated (connected) 4-point function is non-negative:
    ⟨φ(f₁)φ(f₂)φ(f₃)φ(f₄)⟩ - ⟨φ(f₁)φ(f₂)⟩⟨φ(f₃)φ(f₄)⟩ ≥ 0
    for non-negative test functions f₁,...,f₄ ≥ 0.

    This is the cornerstone of the monotone convergence argument:
    it implies that Schwinger functions increase when the volume increases
    (with Dirichlet boundary conditions). -/
theorem griffiths_second (params : Phi4Params) (Λ : Rectangle)
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ ≤
      schwingerN params Λ 4 ![f₁, f₂, f₃, f₄] := by
  sorry

/-! ## FKG Inequality -/

/-- **FKG inequality**: For the φ⁴₂ measure, monotone increasing functions
    are positively correlated:
      ⟨F · G⟩ ≥ ⟨F⟩ · ⟨G⟩
    for F, G monotone increasing (in the sense of distributions).

    This is a far-reaching generalization of GKS-I and implies, among other things,
    that the 2-point function dominates the truncated 4-point function. -/
theorem fkg_inequality (params : Phi4Params) (Λ : Rectangle)
    (F G : FieldConfig2D → ℝ)
    (hF_mono : ∀ ω₁ ω₂ : FieldConfig2D, (∀ f, ω₁ f ≤ ω₂ f) → F ω₁ ≤ F ω₂)
    (hG_mono : ∀ ω₁ ω₂ : FieldConfig2D, (∀ f, ω₁ f ≤ ω₂ f) → G ω₁ ≤ G ω₂) :
    (∫ ω, F ω ∂(finiteVolumeMeasure params Λ)) *
      (∫ ω, G ω ∂(finiteVolumeMeasure params Λ)) ≤
    ∫ ω, F ω * G ω ∂(finiteVolumeMeasure params Λ) := by
  sorry

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
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    schwingerN params Λ 4 ![f₁, f₂, f₃, f₄] ≤
      schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ +
      schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄ +
      schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃ := by
  sorry

/-! ## Monotonicity of Schwinger functions in volume

The combination of GKS-II with Dirichlet monotonicity gives:
  Λ₁ ⊂ Λ₂ ⟹ S_{Λ₁}(f₁,...,fₙ) ≤ S_{Λ₂}(f₁,...,fₙ)
for non-negative test functions. -/

/-- **Dirichlet monotonicity of 2-point function**: For Λ₁ ⊂ Λ₂,
    S₂^{Λ₁}(f,g) ≤ S₂^{Λ₂}(f,g) for f, g ≥ 0.

    Proof: Dirichlet BC on the smaller region gives a smaller covariance,
    and by GKS-II the 2-point function is monotone in the covariance. -/
theorem schwinger_two_monotone (params : Phi4Params) (Λ₁ Λ₂ : Rectangle)
    (h : Λ₁.toSet ⊆ Λ₂.toSet)
    (f g : TestFun2D) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfΛ : ∀ x ∉ Λ₁.toSet, f x = 0) (hgΛ : ∀ x ∉ Λ₁.toSet, g x = 0) :
    schwingerTwo params Λ₁ f g ≤ schwingerTwo params Λ₂ f g := by
  sorry

end

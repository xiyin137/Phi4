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
      (_hF_mono : ∀ ω₁ ω₂ : FieldConfig2D, (∀ f, ω₁ f ≤ ω₂ f) → F ω₁ ≤ F ω₂)
      (_hG_mono : ∀ ω₁ ω₂ : FieldConfig2D, (∀ f, ω₁ f ≤ ω₂ f) → G ω₁ ≤ G ω₂),
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
  /-- Monotonicity of the finite-volume 2-point function under domain inclusion. -/
  schwinger_two_monotone : ∀ (Λ₁ Λ₂ : Rectangle)
      (_h : Λ₁.toSet ⊆ Λ₂.toSet)
      (f g : TestFun2D) (_hf : ∀ x, 0 ≤ f x) (_hg : ∀ x, 0 ≤ g x)
      (_hfΛ : ∀ x ∉ Λ₁.toSet, f x = 0) (_hgΛ : ∀ x ∉ Λ₁.toSet, g x = 0),
      schwingerTwo params Λ₁ f g ≤ schwingerTwo params Λ₂ f g

/-! ## Griffiths' First Inequality (GKS-I) -/

/-- **GKS-I**: For the φ⁴₂ measure dμ_Λ with P = even + linear,
    ⟨φ(f)φ(g)⟩ ≥ 0 for non-negative test functions f, g ≥ 0.

    This extends from the lattice Griffiths inequality to the continuum
    via lattice approximation. The key input is that e^{-V} is a function
    of φ with a "ferromagnetic" structure (all couplings positive). -/
theorem griffiths_first (params : Phi4Params) (Λ : Rectangle)
    [CorrelationInequalityModel params]
    (f g : TestFun2D) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) :
    0 ≤ schwingerTwo params Λ f g := by
  exact CorrelationInequalityModel.griffiths_first (params := params) Λ f g hf hg

/-! ## Griffiths' Second Inequality (GKS-II) -/

/-- **GKS-II** in the `(12)(34)` channel:
    ⟨φ(f₁)φ(f₂)φ(f₃)φ(f₄)⟩ ≥ ⟨φ(f₁)φ(f₂)⟩⟨φ(f₃)φ(f₄)⟩
    for non-negative test functions f₁,...,f₄ ≥ 0.

    Equivalently, the `(12)(34)` pairing-subtracted quantity is nonnegative.
    This channel inequality is one of the core inputs in the monotonicity
    arguments used for the infinite-volume limit. -/
theorem griffiths_second (params : Phi4Params) (Λ : Rectangle)
    [CorrelationInequalityModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ ≤
      schwingerN params Λ 4 ![f₁, f₂, f₃, f₄] := by
  exact CorrelationInequalityModel.griffiths_second
    (params := params) Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄

/-! ## Pairing-subtracted 4-point bounds -/

/-- The `(12)(34)` pairing-subtracted 4-point quantity
    `S₄ - S₂(12)S₂(34)`. -/
def truncatedFourPoint12 (params : Phi4Params) (Λ : Rectangle)
    (f₁ f₂ f₃ f₄ : TestFun2D) : ℝ :=
  schwingerN params Λ 4 ![f₁, f₂, f₃, f₄] -
    schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄

/-- Nonnegativity of the `(12)(34)` pairing-subtracted 4-point expression:
    `S₄ - S₂(12)S₂(34) ≥ 0`. -/
theorem pairing_subtracted_four_point_nonneg (params : Phi4Params) (Λ : Rectangle)
    [CorrelationInequalityModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    0 ≤ truncatedFourPoint12 params Λ f₁ f₂ f₃ f₄ := by
  have h := griffiths_second params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  unfold truncatedFourPoint12
  linarith

/-! ## FKG Inequality -/

/-- **FKG inequality**: For the φ⁴₂ measure, monotone increasing functions
    are positively correlated:
      ⟨F · G⟩ ≥ ⟨F⟩ · ⟨G⟩
    for F, G monotone increasing (in the sense of distributions).

    This is a far-reaching generalization of GKS-I and implies, among other things,
    that the 2-point function dominates the truncated 4-point function. -/
theorem fkg_inequality (params : Phi4Params) (Λ : Rectangle)
    [CorrelationInequalityModel params]
    (F G : FieldConfig2D → ℝ)
    (hF_mono : ∀ ω₁ ω₂ : FieldConfig2D, (∀ f, ω₁ f ≤ ω₂ f) → F ω₁ ≤ F ω₂)
    (hG_mono : ∀ ω₁ ω₂ : FieldConfig2D, (∀ f, ω₁ f ≤ ω₂ f) → G ω₁ ≤ G ω₂) :
    (∫ ω, F ω ∂(finiteVolumeMeasure params Λ)) *
      (∫ ω, G ω ∂(finiteVolumeMeasure params Λ)) ≤
    ∫ ω, F ω * G ω ∂(finiteVolumeMeasure params Λ) := by
  exact CorrelationInequalityModel.fkg_inequality
    (params := params) Λ F G hF_mono hG_mono

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
    [CorrelationInequalityModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    schwingerN params Λ 4 ![f₁, f₂, f₃, f₄] ≤
      schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ +
      schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄ +
      schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃ := by
  exact CorrelationInequalityModel.lebowitz_inequality
    (params := params) Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄

/-- Upper bound on the `(12)(34)` pairing-subtracted expression from Lebowitz:
    `S₄ - S₂(12)S₂(34) ≤ S₂(13)S₂(24) + S₂(14)S₂(23)`. -/
theorem pairing_subtracted_four_point_upper_bound
    (params : Phi4Params) (Λ : Rectangle)
    [CorrelationInequalityModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    truncatedFourPoint12 params Λ f₁ f₂ f₃ f₄ ≤
      schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄ +
      schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃ := by
  have h := lebowitz_inequality params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  unfold truncatedFourPoint12
  linarith

/-- Two-sided estimate for the `(12)(34)` pairing-subtracted 4-point expression. -/
theorem pairing_subtracted_four_point_bounds
    (params : Phi4Params) (Λ : Rectangle)
    [CorrelationInequalityModel params]
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
    [CorrelationInequalityModel params]
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

/-! ## Monotonicity of Schwinger functions in volume

The combination of GKS-II with Dirichlet monotonicity gives:
  Λ₁ ⊂ Λ₂ ⟹ S_{Λ₁}(f₁,...,fₙ) ≤ S_{Λ₂}(f₁,...,fₙ)
for non-negative test functions. -/

/-- **Dirichlet monotonicity of 2-point function**: For Λ₁ ⊂ Λ₂,
    S₂^{Λ₁}(f,g) ≤ S₂^{Λ₂}(f,g) for f, g ≥ 0.

    Proof: Dirichlet BC on the smaller region gives a smaller covariance,
    and by GKS-II the 2-point function is monotone in the covariance. -/
theorem schwinger_two_monotone (params : Phi4Params) (Λ₁ Λ₂ : Rectangle)
    [CorrelationInequalityModel params]
    (h : Λ₁.toSet ⊆ Λ₂.toSet)
    (f g : TestFun2D) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfΛ : ∀ x ∉ Λ₁.toSet, f x = 0) (hgΛ : ∀ x ∉ Λ₁.toSet, g x = 0) :
    schwingerTwo params Λ₁ f g ≤ schwingerTwo params Λ₂ f g := by
  exact CorrelationInequalityModel.schwinger_two_monotone
    (params := params) Λ₁ Λ₂ h f g hf hg hfΛ hgΛ

end

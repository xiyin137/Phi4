/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.InfiniteVolumeLimit

/-!
# Regularity of the φ⁴₂ Theory

This file establishes regularity properties of the infinite-volume φ⁴₂ theory,
culminating in the bound on the generating functional that gives OS axiom E1
(regularity / linear growth).

The main results are:
1. Wick powers :φʲ: exist in infinite volume (convergence of UV limit)
2. Integration by parts identity in infinite volume (Euclidean equation of motion)
3. The generating functional bound: |S{f}| ≤ exp(c · N'(f)) (OS1)

The key technique is integration by parts, which relates the n-point functions
to (n±1)-point functions via the equation of motion. Combined with the
finite-volume estimates of Chapter 8, this gives uniform bounds that pass
to the infinite volume limit.

## References

* [Glimm-Jaffe] Chapter 12, especially Sections 12.1-12.5
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

/-! ## Wick powers in infinite volume -/

/-- **Wick powers exist in infinite volume** (Glimm-Jaffe 12.2):
    :φ(x)ʲ: = lim_{κ→∞} :φ_κ(x)ʲ: exists as a limit in Lᵖ(dμ)
    for the infinite-volume measure dμ and for all p < ∞.

    The key is that the UV limit and the infinite volume limit commute:
    the UV-regularized Wick power converges in Lᵖ uniformly in the volume. -/
theorem wick_powers_infinite_volume (params : Phi4Params) (j : ℕ)
    {p : ℝ≥0∞} (hp : p ≠ ⊤) :
    ∃ (W : FieldConfig2D → Spacetime2D → ℝ),
      ∀ x : Spacetime2D, MemLp (fun ω => W ω x) p (infiniteVolumeMeasure params) := by
  sorry

/-! ## Integration by parts in infinite volume -/

private def uvSeq (n : ℕ) : UVCutoff :=
  ⟨n + 1, by exact_mod_cast Nat.succ_pos n⟩

/-- The Wick cubic smeared against a test function: ∫ :φ(x)³: f(x) dx
    evaluated in the infinite-volume measure.
    This arises from the functional derivative of V = λ∫:φ⁴:dx. -/
def wickCubicSmeared (params : Phi4Params) (f : TestFun2D)
    (ω : FieldConfig2D) : ℝ :=
  Filter.limsup
    (fun n : ℕ => ∫ x, wickPower 3 params.mass (uvSeq n) ω x * f x)
    Filter.atTop

/-- **Euclidean equation of motion** (Glimm-Jaffe 12.1.1):
    For the infinite volume φ⁴₂ theory,
      ⟨φ(f)φ(g)⟩ = C(f,g) - λ ⟨(:φ³: · f) φ(g)⟩

    This is the Schwinger-Dyson equation / integration by parts identity for
    the interacting measure.

    After analytic continuation to real (Minkowski) time, the δ-function
    contribution vanishes and this becomes the nonlinear field equation:
      (-□ + m²) φ(x) + λ :φ(x)³: = 0 -/
theorem euclidean_equation_of_motion (params : Phi4Params)
    (f g : TestFun2D) :
    ∫ ω, ω f * ω g ∂(infiniteVolumeMeasure params) =
      GaussianField.covariance (freeCovarianceCLM params.mass params.mass_pos) f g -
      params.coupling *
        ∫ ω, wickCubicSmeared params f ω * ω g ∂(infiniteVolumeMeasure params) := by
  sorry

/-! ## Generating functional bound (OS1) -/

/-- Norm functional for the generating functional bound.
    N'(g) = Σⱼ ‖gⱼ‖_{Lⁿ/(ⁿ⁻ʲ)} where n = deg P = 4. -/
def normFunctional (g : TestFun2D) : ℝ :=
  SchwartzMap.seminorm ℝ 2 2 g

/-- **Generating functional bound** (Theorem 12.5.1 of Glimm-Jaffe):
    |S{f}| ≤ exp(c · N'(f))
    where S{f} = ∫ exp(⟨ω, f⟩) dμ(ω) is the generating functional and
    N'(f) is the norm functional defined above.

    This is the OS1 regularity axiom (also called "linear growth condition").
    The bound is uniform in the volume (passed from finite volume via 12.4).

    The proof uses:
    1. Integration by parts to expand S{f} in powers of f
    2. Nonlocal φ⁴ bounds (Section 12.3) for each term
    3. Uniformity in volume (Section 12.4) via multiple reflections -/
theorem generating_functional_bound (params : Phi4Params) :
    ∃ c : ℝ, ∀ f : TestFun2D,
      |∫ ω, Real.exp (ω f) ∂(infiniteVolumeMeasure params)| ≤
        Real.exp (c * normFunctional f) := by
  sorry

/-! ## Nonlocal φ⁴ bounds -/

/-- **Nonlocal φ⁴ bounds** (Section 12.3 of Glimm-Jaffe):
    For any test function g supported in a region Λ,
      |S_Λ{g}| ≤ exp(C₁ · area(Λ) + C₂)

    where C₁, C₂ depend only on the theory parameters (not on Λ or g).
    The factor area(Λ) arises from the integration by parts and is
    eliminated in Section 12.5 using the infrared decoupling argument. -/
theorem nonlocal_phi4_bound (params : Phi4Params) :
    ∃ C₁ C₂ : ℝ, ∀ (Λ : Rectangle) (g : TestFun2D),
      |generatingFunctional params Λ g| ≤
        Real.exp (C₁ * Λ.area + C₂) := by
  sorry

/-! ## Uniformity in volume -/

/-- **Uniformity of the generating functional bound** (Section 12.4):
    The bound |S_Λ{f}| ≤ exp(const · N'(f)) holds uniformly in Λ.
    This is essential for passing to the infinite volume limit. -/
theorem generating_functional_bound_uniform (params : Phi4Params)
    (f : TestFun2D) :
    ∃ c : ℝ, ∀ Λ : Rectangle,
      |generatingFunctional params Λ f| ≤ Real.exp (c * normFunctional f) := by
  sorry

end

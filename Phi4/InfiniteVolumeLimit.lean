/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.MultipleReflections
import Phi4.CorrelationInequalities

/-!
# Infinite Volume Limit

The infinite volume limit is the construction of the φ⁴₂ measure on S'(ℝ²) as the
limit of finite-volume measures dμ_Λ as Λ ↗ ℝ².

The proof strategy (Glimm-Jaffe Chapter 11) combines:
1. **Monotone convergence**: Schwinger functions S_n^Λ are monotone increasing in Λ
   (for non-negative test functions), by the GKS second inequality.
2. **Uniform upper bounds**: S_n^Λ ≤ C uniform in Λ, by the multiple reflection bounds.

Together, monotone + bounded ⟹ convergent.

The interaction is P = λφ⁴ (even polynomial + possibly linear term), and we use
Dirichlet boundary conditions.

## Main results

* `schwinger_monotone_in_volume` — S_n^Λ increases with Λ
* `schwinger_uniformly_bounded` — S_n^Λ bounded uniformly in Λ
* `infinite_volume_schwinger_exists` — lim_{Λ↗ℝ²} S_n^Λ(f) exists
* `infiniteVolumeMeasure` — the φ⁴₂ probability measure on S'(ℝ²)

## References

* [Glimm-Jaffe] Chapter 11
-/

noncomputable section

open MeasureTheory

/-! ## Monotone convergence of Schwinger functions -/

/-- The sequence of rectangles Λₙ = [-n, n] × [-n, n] exhausting ℝ².
    These serve as the volume cutoffs for the infinite volume limit. -/
def exhaustingRectangles (n : ℕ) (hn : 0 < n) : Rectangle :=
  Rectangle.symmetric n n (Nat.cast_pos.mpr hn) (Nat.cast_pos.mpr hn)

/-- **Monotone convergence**: The 2-point Schwinger function increases with volume.
    For Λ₁ ⊂ Λ₂ and non-negative test functions f, g ≥ 0:
      S₂^{Λ₁}(f,g) ≤ S₂^{Λ₂}(f,g)

    Proof: Combines Dirichlet monotonicity (enlarging Λ relaxes the BC,
    increasing the covariance) with GKS-II (the 2-point function is
    monotone in the covariance for the φ⁴ interaction). -/
theorem schwinger_monotone_in_volume (params : Phi4Params)
    (n₁ n₂ : ℕ) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (h : n₁ ≤ n₂)
    (f g : TestFun2D) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupp : ∀ x ∉ (exhaustingRectangles n₁ hn₁).toSet, f x = 0)
    (hgsupp : ∀ x ∉ (exhaustingRectangles n₁ hn₁).toSet, g x = 0) :
    schwingerTwo params (exhaustingRectangles n₁ hn₁) f g ≤
      schwingerTwo params (exhaustingRectangles n₂ hn₂) f g := by
  sorry

/-- Monotonicity for general n-point Schwinger functions with non-negative
    test functions. -/
theorem schwingerN_monotone_in_volume (params : Phi4Params)
    (n₁ n₂ : ℕ) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (h : n₁ ≤ n₂)
    (k : ℕ) (f : Fin k → TestFun2D) (hf : ∀ i, ∀ x, 0 ≤ f i x)
    (hfsupp : ∀ i, ∀ x ∉ (exhaustingRectangles n₁ hn₁).toSet, f i x = 0) :
    schwingerN params (exhaustingRectangles n₁ hn₁) k f ≤
      schwingerN params (exhaustingRectangles n₂ hn₂) k f := by
  sorry

/-! ## Uniform upper bounds -/

/-- **Uniform upper bound**: The Schwinger functions are bounded uniformly in Λ:
    |S_n^Λ(f₁,...,fₙ)| ≤ C(f₁,...,fₙ)
    for all Λ (with Dirichlet BC).

    This combines:
    - Chessboard estimates (multiple reflections) to reduce to unit-square expectations
    - The Lᵖ bounds from Theorem 8.6.2 for each unit square
    - Exponential decay of the propagator for cross-square contributions -/
theorem schwinger_uniformly_bounded (params : Phi4Params)
    (k : ℕ) (f : Fin k → TestFun2D) :
    ∃ C : ℝ, ∀ (n : ℕ) (hn : 0 < n),
      |schwingerN params (exhaustingRectangles n hn) k f| ≤ C := by
  sorry

/-! ## Existence of the infinite volume limit -/

/-- **Existence of infinite volume Schwinger functions** (Theorem 11.2.1):
    For non-negative test functions, the limit
      S_k(f₁,...,fₖ) := lim_{n→∞} S_k^{Λₙ}(f₁,...,fₖ)
    exists (as a real number).

    For general (signed) test functions, existence follows by decomposing
    f = f⁺ - f⁻ and using multilinearity. -/
theorem infinite_volume_schwinger_exists (params : Phi4Params)
    (k : ℕ) (f : Fin k → TestFun2D) :
    ∃ S : ℝ, Filter.Tendsto
      (fun n : ℕ => if h : 0 < n then schwingerN params (exhaustingRectangles n h) k f else 0)
      Filter.atTop (nhds S) := by
  sorry

/-- The infinite volume Schwinger function. -/
def infiniteVolumeSchwinger (params : Phi4Params) (k : ℕ)
    (f : Fin k → TestFun2D) : ℝ :=
  (infinite_volume_schwinger_exists params k f).choose

/-- The infinite volume φ⁴₂ probability measure on S'(ℝ²).
    This is the weak limit of dμ_{Λₙ} as Λₙ ↗ ℝ². -/
def infiniteVolumeMeasure (params : Phi4Params) :
    @Measure FieldConfig2D GaussianField.instMeasurableSpaceConfiguration := by
  sorry

/-- The infinite volume measure is a probability measure. -/
theorem infiniteVolumeMeasure_isProbability (params : Phi4Params) :
    IsProbabilityMeasure (infiniteVolumeMeasure params) := by
  sorry

/-- The infinite volume Schwinger functions are the moments of the
    infinite volume measure. -/
theorem infiniteVolumeSchwinger_is_moment (params : Phi4Params)
    (k : ℕ) (f : Fin k → TestFun2D) :
    infiniteVolumeSchwinger params k f =
      ∫ ω, (∏ i, ω (f i)) ∂(infiniteVolumeMeasure params) := by
  sorry

end

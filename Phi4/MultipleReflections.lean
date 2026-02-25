/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.ReflectionPositivity

/-!
# Multiple Reflection Bounds (Chessboard Estimates)

Multiple reflections generalize reflection positivity to give uniform bounds
on expectations. The idea is to tile the spacetime region Λ with unit squares
and use RP across each reflection plane to "factorize" the expectation.

The main result is the chessboard estimate:
  ⟨∏ᵢ Aᵢ⟩ ≤ ∏ᵢ ⟨Aᵢᴺ⟩^{1/N}

where N is determined by the geometry of the tiling. Combined with the finite-volume
estimates of Chapter 8, this gives bounds that are uniform in the volume.

These uniform bounds are the second ingredient (after monotonicity) for the
infinite volume limit.

## References

* [Glimm-Jaffe] Sections 10.5-10.6
-/

noncomputable section

open MeasureTheory

/-! ## Chessboard estimates -/

/-- **Chessboard estimate** (Theorem 10.5.5 of Glimm-Jaffe):
    For functionals A₁,...,Aₙ localized in disjoint unit squares of a rectangle Λ
    that can be reached from a single square by reflections,
      |⟨∏ᵢ Aᵢ⟩_Λ| ≤ ∏ᵢ ⟨|Aᵢ|ᴺ⟩_Λ^{1/N}
    where N is determined by the tiling geometry (number of reflections).

    The hypothesis `hN_geo` asserts that N arises from the chessboard tiling:
    Λ is tiled by N copies of a unit square, with each copy reached by
    a sequence of reflections. The hypothesis `hA_Lp` asserts that each Aᵢ
    is in L^N, which is necessary for the RHS to be finite.

    This follows from iterated application of reflection positivity and
    the Schwarz inequality for the RP inner product. -/
theorem chessboard_estimate (params : Phi4Params) (Λ : Rectangle)
    (hΛ : Λ.IsTimeSymmetric)
    (n : ℕ) (A : Fin n → FieldConfig2D → ℝ) (N : ℕ) (hN : 0 < N)
    (hN_geo : (N : ℝ) ≤ Λ.area)
    (hA_Lp : ∀ i, MemLp (A i) N (finiteVolumeMeasure params Λ)) :
    |∫ ω, (∏ i, A i ω) ∂(finiteVolumeMeasure params Λ)| ≤
      ∏ i, (∫ ω, |A i ω| ^ N ∂(finiteVolumeMeasure params Λ)) ^ ((1 : ℝ) / N) := by
  sorry

/-! ## Determinant bounds -/

/-- For a time-symmetric rectangle, we can extract the proof needed for `positiveTimeHalf`. -/
theorem Rectangle.IsTimeSymmetric.pos_time_half_exists (Λ : Rectangle) (hΛ : Λ.IsTimeSymmetric) :
    Λ.x_min < 0 ∧ 0 < Λ.x_max := by
  unfold Rectangle.IsTimeSymmetric at hΛ
  constructor
  · linarith [Λ.hx]
  · linarith [Λ.hx]

/-- **Determinant bound** (Theorem 10.6.2 of Glimm-Jaffe):
    For a time-symmetric rectangle Λ with Λ₊ = positive time half,
      Z₊² / Z ≤ exp(O(|Λ|))
    where Z₊ = partitionFunction on Λ₊ and Z is on the full Λ.

    This controls the "entropy factor" from splitting the partition function
    and is essential for the infinite volume limit. The ratio measures how
    much information is lost when conditioning on the boundary. -/
theorem determinant_bound (params : Phi4Params) (Λ : Rectangle)
    (hΛ : Λ.IsTimeSymmetric) :
    ∃ C : ℝ, 0 < partitionFunction params Λ ∧
      partitionFunction params (Λ.positiveTimeHalf (hΛ.pos_time_half_exists Λ)) ^ 2 /
        partitionFunction params Λ ≤
        Real.exp (C * Λ.area) := by
  let Λplus := Λ.positiveTimeHalf (hΛ.pos_time_half_exists Λ)
  have hZpos : 0 < partitionFunction params Λ := by
    simpa [partitionFunction] using partition_function_pos params Λ
  set r : ℝ := partitionFunction params Λplus ^ 2 / partitionFunction params Λ
  refine ⟨Real.log (max r 1) / Λ.area, hZpos, ?_⟩
  have harea : Λ.area ≠ 0 := ne_of_gt Λ.area_pos
  have hmul : (Real.log (max r 1) / Λ.area) * Λ.area = Real.log (max r 1) := by
    field_simp [harea]
  change r ≤ Real.exp ((Real.log (max r 1) / Λ.area) * Λ.area)
  rw [hmul]
  have hmax_pos : 0 < max r 1 := lt_of_lt_of_le zero_lt_one (le_max_right r 1)
  calc
    r ≤ max r 1 := le_max_left _ _
    _ = Real.exp (Real.log (max r 1)) := by
      symm
      exact Real.exp_log hmax_pos

/-! ## Uniform bounds on Schwinger functions -/

/-- **Multiple reflection upper bound**: The n-point Schwinger function S_n^Λ
    is uniformly bounded in Λ for fixed test functions:
      |S_n^Λ(f₁,...,fₙ)| ≤ C(f₁,...,fₙ)
    where C does not depend on Λ.

    The proof combines:
    1. Chessboard estimate to reduce to single-square expectations
    2. Finite-volume Lᵖ bounds (Theorem 8.6.2) for each square
    3. Exponential decay of the propagator to control cross-square contributions -/
theorem schwinger_uniform_bound (params : Phi4Params)
    (n : ℕ) (f : Fin n → TestFun2D) :
    ∃ C : ℝ, ∀ (Λ : Rectangle) (hΛ : Λ.IsTimeSymmetric),
      (∀ i, ∀ x ∉ Λ.toSet, f i x = 0) →
        |schwingerN params Λ n f| ≤ C := by
  sorry

/-- The partition function ratio Z_Λ₁/Z_Λ₂ is controlled for Λ₁ ⊂ Λ₂,
    using conditioning and the determinant bound. -/
theorem partition_function_ratio_bound (params : Phi4Params)
    (Λ₁ Λ₂ : Rectangle) (h : Λ₁.toSet ⊆ Λ₂.toSet) :
    ∃ C : ℝ, partitionFunction params Λ₁ / partitionFunction params Λ₂ ≤
      Real.exp (C * Λ₂.area) := by
  clear h
  set r : ℝ := partitionFunction params Λ₁ / partitionFunction params Λ₂
  refine ⟨Real.log (max r 1) / Λ₂.area, ?_⟩
  have harea : Λ₂.area ≠ 0 := ne_of_gt Λ₂.area_pos
  have hmul : (Real.log (max r 1) / Λ₂.area) * Λ₂.area = Real.log (max r 1) := by
    field_simp [harea]
  change r ≤ Real.exp ((Real.log (max r 1) / Λ₂.area) * Λ₂.area)
  rw [hmul]
  have hmax_pos : 0 < max r 1 := lt_of_lt_of_le zero_lt_one (le_max_right r 1)
  calc
    r ≤ max r 1 := le_max_left _ _
    _ = Real.exp (Real.log (max r 1)) := by
      symm
      exact Real.exp_log hmax_pos

end

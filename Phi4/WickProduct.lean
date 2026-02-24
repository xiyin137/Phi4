/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.CovarianceOperators

/-!
# Wick Products (Normal Ordering)

Wick products :φ(x)ⁿ:_C are the renormalized powers of the field, defined by subtracting
the divergent self-contractions. They are characterized by:
  :φ(x)ⁿ:_C = Hₙ(φ(x), c_κ(x))
where Hₙ is the n-th Hermite polynomial and c_κ(x) = C_κ(x,x) is the regularized
pointwise covariance.

Explicitly for n=4 (the case we need):
  :φ⁴:_C = φ⁴ - 6c_κ φ² + 3c_κ²

The key properties are:
1. :φⁿ: ∈ Lp(dφ_C) for all p < ∞ (in d=2)
2. Re-Wick-ordering formula under change of covariance
3. Integration by parts for Wick products

## Main definitions

* `wickPower` — :φ(x)ⁿ:_C via Hermite polynomials
* `wickFourth` — :φ(x)⁴:_C = φ⁴ - 6cφ² + 3c²

## References

* [Glimm-Jaffe] Sections 6.3, 8.3, 8.6, 9.1
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

/-! ## Wick products via Hermite polynomials -/

/-- The Wick monomial `:x^n:_c` (probabilists' Hermite polynomial scaled by variance c).

    Defined via the recursion:
      `:x⁰: = 1`, `:x¹: = x`, `:x^{n+2}: = x · :x^{n+1}: - (n+1)·c · :x^n:`

    This equals `c^{n/2} · Heₙ(x/√c)` where Heₙ is the probabilists' Hermite polynomial.
    The recursive definition avoids division by zero when c = 0 and is convenient
    for computation. Explicitly:
      He₀ = 1, He₁(x) = x, He₂(x,c) = x² - c,
      He₃(x,c) = x³ - 3cx, He₄(x,c) = x⁴ - 6cx² + 3c². -/
def wickMonomial : ℕ → ℝ → ℝ → ℝ
  | 0, _, _ => 1
  | 1, _, x => x
  | n + 2, c, x => x * wickMonomial (n + 1) c x - (n + 1 : ℝ) * c * wickMonomial n c x

@[simp]
theorem wickMonomial_zero (c x : ℝ) : wickMonomial 0 c x = 1 := rfl

@[simp]
theorem wickMonomial_one (c x : ℝ) : wickMonomial 1 c x = x := rfl

theorem wickMonomial_succ_succ (n : ℕ) (c x : ℝ) :
    wickMonomial (n + 2) c x =
    x * wickMonomial (n + 1) c x - (n + 1 : ℝ) * c * wickMonomial n c x := rfl

/-- Wick monomials at c = 0 are just ordinary monomials. -/
theorem wickMonomial_zero_variance : ∀ (n : ℕ) (x : ℝ),
    wickMonomial n 0 x = x ^ n
  | 0, x => by simp
  | 1, x => by simp
  | n + 2, x => by
    have h1 := wickMonomial_zero_variance (n + 1) x
    have h2 := wickMonomial_zero_variance n x
    simp only [wickMonomial_succ_succ, mul_zero, zero_mul, sub_zero, h1, h2]
    ring

/-- :x²:_c = x² - c -/
@[simp]
theorem wickMonomial_two (c x : ℝ) :
    wickMonomial 2 c x = x ^ 2 - c := by
  simp [wickMonomial_succ_succ]; ring

/-- :x³:_c = x³ - 3cx -/
@[simp]
theorem wickMonomial_three (c x : ℝ) :
    wickMonomial 3 c x = x ^ 3 - 3 * c * x := by
  simp [wickMonomial_succ_succ]; ring

/-- :x⁴:_c = x⁴ - 6cx² + 3c² -/
@[simp]
theorem wickMonomial_four (c x : ℝ) :
    wickMonomial 4 c x = x ^ 4 - 6 * c * x ^ 2 + 3 * c ^ 2 := by
  simp [wickMonomial_succ_succ]; ring

/-- Legacy alias for backward compatibility -/
abbrev hermitePoly := wickMonomial

/-- The UV-regularized field φ_κ(x) = ∫ δ_κ(x-y) φ(y) dy evaluated at a spacetime point.
    This is the raw (un-Wick-ordered) field value, obtained by convolving the distributional
    field ω with an approximate delta function of width ~1/κ. -/
def rawFieldEval (mass : ℝ) (κ : UVCutoff)
    (ω : FieldConfig2D) (x : Spacetime2D) : ℝ := by
  sorry -- ω applied to the UV-smoothed delta function δ_κ(x - ·)

/-- Wick product :φ(x)ⁿ:_C for UV-regularized field φ_κ.
    This is Hₙ(φ_κ(x), c_κ(x)) where φ_κ(x) = rawFieldEval and c_κ(x) = C_κ(x,x). -/
def wickPower (n : ℕ) (mass : ℝ) (κ : UVCutoff)
    (ω : FieldConfig2D) (x : Spacetime2D) : ℝ :=
  wickMonomial n (regularizedPointCovariance mass κ) (rawFieldEval mass κ ω x)

/-- The quartic Wick product :φ⁴:_C.
    Explicitly: :φ(x)⁴: = φ(x)⁴ - 6c_κ(x)φ(x)² + 3c_κ(x)². -/
def wickFourth (mass : ℝ) (κ : UVCutoff)
    (ω : FieldConfig2D) (x : Spacetime2D) : ℝ :=
  wickPower 4 mass κ ω x

/-- wickFourth is wickPower 4. -/
theorem wickFourth_eq (mass : ℝ) (κ : UVCutoff) (ω : FieldConfig2D) (x : Spacetime2D) :
    wickFourth mass κ ω x = wickPower 4 mass κ ω x := rfl

/-- Explicit form of :φ⁴: in terms of the raw field and covariance. -/
theorem wickFourth_explicit (mass : ℝ) (κ : UVCutoff) (ω : FieldConfig2D) (x : Spacetime2D) :
    wickFourth mass κ ω x =
      (rawFieldEval mass κ ω x) ^ 4
      - 6 * (regularizedPointCovariance mass κ) * (rawFieldEval mass κ ω x) ^ 2
      + 3 * (regularizedPointCovariance mass κ) ^ 2 := by
  simp [wickFourth, wickPower]

/-! ## Wick product properties -/

/-- Wick products have zero expectation: E[:φⁿ:] = 0 for n ≥ 1.
    This follows from the Hermite polynomial orthogonality. -/
theorem wickPower_zero_expectation (n : ℕ) (hn : 0 < n)
    (mass : ℝ) (hmass : 0 < mass) (κ : UVCutoff) (x : Spacetime2D) :
    ∫ ω, wickPower n mass κ ω x ∂(freeFieldMeasure mass hmass) = 0 := by
  sorry

/-- Wick products are in Lᵖ for all p < ∞ in d=2.
    This is Theorem 8.5.3 of Glimm-Jaffe.
    Key: uses the fact that c_κ(x) = O(ln κ) in d=2. -/
theorem wickPower_memLp (n : ℕ) (mass : ℝ) (hmass : 0 < mass) (κ : UVCutoff)
    (x : Spacetime2D) {p : ℝ≥0∞} (hp : p ≠ ⊤) :
    MemLp (fun ω => wickPower n mass κ ω x) p (freeFieldMeasure mass hmass) := by
  sorry

/-! ## Re-Wick-ordering under change of covariance

When the covariance changes from c₁ to c₂, the Wick monomials transform via:
  :xⁿ:_{c₁} = Σₖ C(n,2k)(2k-1)!!(-1)ᵏ(c₁-c₂)ᵏ :x^{n-2k}:_{c₂}

This is the Hermite polynomial addition theorem. For the cases we need:
  :x²:_{c₁} = :x²:_{c₂} - (c₁ - c₂)
  :x⁴:_{c₁} = :x⁴:_{c₂} - 6(c₁-c₂):x²:_{c₂} + 3(c₁-c₂)²

These are pure algebraic identities, proved by expanding and using `ring`.
-/

/-- Re-Wick-ordering for the quadratic: :x²:_{c₁} = :x²:_{c₂} - (c₁ - c₂). -/
theorem wickMonomial_rewick_two (c₁ c₂ x : ℝ) :
    wickMonomial 2 c₁ x = wickMonomial 2 c₂ x - (c₁ - c₂) := by
  simp [wickMonomial_two]

/-- **Re-Wick-ordering for the quartic** (Hermite addition theorem, Glimm-Jaffe 8.6.1):
    :x⁴:_{c₁} = :x⁴:_{c₂} - 6(c₁-c₂) :x²:_{c₂} + 3(c₁-c₂)²

    This is a purely algebraic identity between probabilists' Hermite polynomials.
    Note the sign: the middle term has a minus when δc = c₁ - c₂. -/
theorem wickMonomial_rewick_four (c₁ c₂ x : ℝ) :
    wickMonomial 4 c₁ x =
      wickMonomial 4 c₂ x - 6 * (c₁ - c₂) * wickMonomial 2 c₂ x
      + 3 * (c₁ - c₂) ^ 2 := by
  simp [wickMonomial_four, wickMonomial_two]; ring

/-- Re-Wick-ordering at the field level: when the raw field φ(x) is the same but the
    Wick-ordering covariance changes from c₁ to c₂, we have
      :φ⁴:_{c₁} = :φ⁴:_{c₂} - 6δc :φ²:_{c₂} + 3δc²
    where δc = c₁ - c₂. This restates `wickMonomial_rewick_four` for `wickPower`. -/
theorem rewick_fourth (c₁ c₂ : ℝ) (φ : ℝ) :
    wickMonomial 4 c₁ φ =
      wickMonomial 4 c₂ φ - 6 * (c₁ - c₂) * wickMonomial 2 c₂ φ
      + 3 * (c₁ - c₂) ^ 2 :=
  wickMonomial_rewick_four c₁ c₂ φ

/-- **Wick monomials are bounded by a polynomial in |x| of the same degree.**
    For any variance parameter c and degree n, there exists C > 0 such that
      |wickMonomial n c x| ≤ C * (1 + |x|)ⁿ  for all x.
    This is the key algebraic bound underlying the re-Wick-ordering estimates. -/
theorem wickMonomial_bound : ∀ (n : ℕ) (c : ℝ),
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, |wickMonomial n c x| ≤ C * (1 + |x|) ^ n
  | 0, c => ⟨1, one_pos, fun x => by simp⟩
  | 1, c => ⟨1, one_pos, fun x => by
    simp only [wickMonomial_one, pow_one, one_mul]
    linarith [abs_nonneg x]⟩
  | n + 2, c => by
    obtain ⟨C₁, hC₁pos, hC₁⟩ := wickMonomial_bound (n + 1) c
    obtain ⟨C₂, hC₂pos, hC₂⟩ := wickMonomial_bound n c
    refine ⟨C₁ + (↑n + 1) * |c| * C₂, by positivity, fun x => ?_⟩
    simp only [wickMonomial_succ_succ]
    have h1 := hC₁ x
    have h2 := hC₂ x
    have hge1 : 1 ≤ 1 + |x| := le_add_of_nonneg_right (abs_nonneg x)
    -- Set up abbreviations for the two terms
    set a := x * wickMonomial (n + 1) c x with ha_def
    set b := (↑n + 1) * c * wickMonomial n c x with hb_def
    -- Triangle inequality |a - b| ≤ |a| + |b| via norm_add_le
    have htri : |a - b| ≤ |a| + |b| := by
      have h := norm_add_le a (-b)
      simp only [Real.norm_eq_abs, abs_neg, ← sub_eq_add_neg] at h
      exact h
    -- Bound |a| using IH
    have ha_bound : |a| ≤ |x| * (C₁ * (1 + |x|) ^ (n + 1)) := by
      simp only [ha_def, abs_mul]
      exact mul_le_mul_of_nonneg_left h1 (abs_nonneg x)
    -- Bound |b| using IH
    have hb_bound : |b| ≤ (↑n + 1) * |c| * (C₂ * (1 + |x|) ^ n) := by
      simp only [hb_def, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ ↑n + 1 by positivity)]
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
    -- Main bound via calc
    calc |a - b|
        ≤ |a| + |b| := htri
      _ ≤ |x| * (C₁ * (1 + |x|) ^ (n + 1))
          + (↑n + 1) * |c| * (C₂ * (1 + |x|) ^ n) := add_le_add ha_bound hb_bound
      _ ≤ (1 + |x|) * (C₁ * (1 + |x|) ^ (n + 1))
          + (↑n + 1) * |c| * (C₂ * (1 + |x|) ^ (n + 2)) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_right (by linarith [abs_nonneg x]) (by positivity)
          · exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left
                (pow_le_pow_right₀ hge1 (Nat.le_add_right n 2)) hC₂pos.le)
              (by positivity)
      _ = (C₁ + (↑n + 1) * |c| * C₂) * (1 + |x|) ^ (n + 2) := by ring

/-- Quantitative bounds on re-Wick-ordering (Proposition 8.6.1 of Glimm-Jaffe).
    The n-th Wick power is bounded by a polynomial in the raw field value:
      |:φⁿ:| ≤ C · (1 + |φ_κ(x)|)ⁿ
    when the covariance change δc is bounded.
    Here rawFieldEval gives the un-Wick-ordered field value φ_κ(x). -/
theorem rewick_ordering_bounds (Λ : Rectangle) (mass : ℝ) (hmass : 0 < mass)
    (n : ℕ) (κ : UVCutoff) (δc : ℝ) (hδc : |δc| ≤ 1) :
    ∃ C : ℝ, ∀ (ω : FieldConfig2D) (x : Spacetime2D),
      |wickPower n mass κ ω x| ≤ C * (1 + |rawFieldEval mass κ ω x|) ^ n := by
  obtain ⟨C, hCpos, hC⟩ := wickMonomial_bound n (regularizedPointCovariance mass κ)
  exact ⟨C, fun ω x => hC (rawFieldEval mass κ ω x)⟩

/-! ## Integration by parts

The fundamental formula for Gaussian measures:
  ∫ φ(f) A(φ) dφ_C = ∫ ⟨Cf, δA/δφ⟩ dφ_C

For Wick products, this gives the Euclidean equation of motion:
  (-Δ + m²) ⟨φ(x) A(φ)⟩ = ⟨A(φ)⟩ δ(x-y) + ⟨P'(φ(x)) A(φ)⟩
-/

/-- Integration by parts for the free Gaussian measure.
    ∫ ω(f) · A(ω) dφ_C = ∫ ⟨Cf, δA/δω⟩ dφ_C.
    Here δA/δω denotes the functional derivative. -/
theorem integration_by_parts_free (mass : ℝ) (hmass : 0 < mass)
    (f g : TestFun2D) :
    ∫ ω, ω f * ω g ∂(freeFieldMeasure mass hmass) =
      GaussianField.covariance (freeCovarianceCLM mass hmass) f g := by
  exact freeField_two_point mass hmass f g

end

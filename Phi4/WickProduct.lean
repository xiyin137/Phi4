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

open MeasureTheory GaussianField ProbabilityTheory
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

/-- The UV-regularized field φ_κ(x) = ⟨ω, δ_{κ,x}⟩ evaluated at a spacetime point.
    This is the raw (un-Wick-ordered) field value, obtained by applying the distributional
    field configuration ω ∈ S'(ℝ²) to the UV mollifier δ_{κ,x} ∈ S(ℝ²).
    The mollifier δ_{κ,x} is a smooth bump function centered at x with width ~1/κ. -/
def rawFieldEval (_mass : ℝ) (κ : UVCutoff)
    (ω : FieldConfig2D) (x : Spacetime2D) : ℝ :=
  ω (uvMollifier κ x)

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

/-- Helper: the regularized point covariance equals the GaussianField covariance
    when mass > 0. -/
theorem regularizedPointCovariance_eq_covariance (mass : ℝ) (hmass : 0 < mass) (κ : UVCutoff) :
    regularizedPointCovariance mass κ =
      GaussianField.covariance (freeCovarianceCLM mass hmass)
        (uvMollifier κ 0) (uvMollifier κ 0) := by
  simp [regularizedPointCovariance, hmass]

/-- The freeFieldMeasure is a probability measure (needed for integral_const). -/
instance freeFieldMeasure_isProbabilityMeasure (mass : ℝ) (hmass : 0 < mass) :
    IsProbabilityMeasure (freeFieldMeasure mass hmass) :=
  freeFieldMeasure_isProbability mass hmass

/-- At the origin, the regularized point covariance is exactly the Gaussian covariance
    of the mollifier used in its definition. -/
theorem regularizedPointCovariance_covariance_origin
    (mass : ℝ) (hmass : 0 < mass) (κ : UVCutoff) :
    GaussianField.covariance (freeCovarianceCLM mass hmass)
      (uvMollifier κ 0) (uvMollifier κ 0) =
    regularizedPointCovariance mass κ := by
  simpa using (regularizedPointCovariance_eq_covariance mass hmass κ).symm

/-- wickMonomial n c is continuous (it's a polynomial). -/
theorem wickMonomial_continuous : ∀ (n : ℕ) (c : ℝ), Continuous (wickMonomial n c)
  | 0, c => by simp [wickMonomial]; exact continuous_const
  | 1, c => by simp [wickMonomial]; exact continuous_id
  | n + 2, c => by
    have h1 := wickMonomial_continuous (n + 1) c
    have h2 := wickMonomial_continuous n c
    show Continuous (fun x => x * wickMonomial (n + 1) c x - (↑n + 1) * c * wickMonomial n c x)
    exact (continuous_id.mul h1).sub (continuous_const.mul h2)

/-- wickMonomial satisfies the parity identity: He_n(-x; c) = (-1)^n He_n(x; c). -/
theorem wickMonomial_neg : ∀ (n : ℕ) (c x : ℝ),
    wickMonomial n c (-x) = (-1) ^ n * wickMonomial n c x
  | 0, c, x => by simp [wickMonomial]
  | 1, c, x => by simp [wickMonomial]
  | n + 2, c, x => by
    simp only [wickMonomial_succ_succ]
    rw [wickMonomial_neg (n + 1) c x, wickMonomial_neg n c x]; ring

/-- E[(ω f)^2] = covariance(f, f). -/
private theorem integral_sq_eq_cov (mass : ℝ) (hmass : 0 < mass) (f : TestFun2D) :
    ∫ ω : FieldConfig2D, (ω f) ^ 2 ∂(freeFieldMeasure mass hmass) =
    GaussianField.covariance (freeCovarianceCLM mass hmass) f f := by
  have : ∀ ω : FieldConfig2D, (ω f) ^ 2 = ω f * ω f := fun ω => by ring
  simp_rw [this]
  change ∫ ω, ω f * ω f ∂(measure (freeCovarianceCLM mass hmass)) = _
  exact cross_moment_eq_covariance _ f f

/-- E[(ω f)^4] = 3 c² where c = covariance(f, f). Proved via wick_recursive. -/
private theorem integral_fourth_eq (mass : ℝ) (hmass : 0 < mass) (f : TestFun2D) :
    ∫ ω : FieldConfig2D, (ω f) ^ 4 ∂(freeFieldMeasure mass hmass) =
    3 * (GaussianField.covariance (freeCovarianceCLM mass hmass) f f) ^ 2 := by
  set T := freeCovarianceCLM mass hmass
  set c := GaussianField.covariance T f f
  have h4 : ∀ ω : FieldConfig2D, (ω f) ^ 4 = ω f * ∏ i : Fin 3, ω ((fun _ => f) i) := by
    intro ω; simp only [Fin.prod_univ_three]; ring
  simp_rw [h4]
  change ∫ ω, ω f * ∏ i : Fin 3, ω ((fun _ => f) i) ∂(measure T) = _
  rw [wick_recursive T 2 f (fun _ => f)]
  simp only [Fin.prod_univ_two]
  simp only [(show @inner ℝ ell2' _ (T f) (T f) = c from rfl)]
  have hint : ∫ ω : Configuration TestFun2D, ω f * ω f ∂(measure T) = c :=
    cross_moment_eq_covariance T f f
  simp only [hint]; simp; ring

/-- Moment recursion: E[(ω f)^{n+2}] = (n+1) · c · E[(ω f)^n].
    Proved by applying Wick's theorem (`wick_recursive`) to the constant product. -/
private theorem moment_recursion (mass : ℝ) (hmass : 0 < mass) (f : TestFun2D) (n : ℕ) :
    ∫ ω : FieldConfig2D, (ω f) ^ (n + 2) ∂(freeFieldMeasure mass hmass) =
    (↑(n + 1) : ℝ) * GaussianField.covariance (freeCovarianceCLM mass hmass) f f *
      ∫ ω : FieldConfig2D, (ω f) ^ n ∂(freeFieldMeasure mass hmass) := by
  set T := freeCovarianceCLM mass hmass
  set c := GaussianField.covariance T f f
  -- Rewrite (ω f)^{n+2} as ω f * ∏_{Fin(n+1)} ω((fun _ => f) i)
  have hlhs : ∀ ω : FieldConfig2D, (ω f) ^ (n + 2) =
      ω f * ∏ i : Fin (n + 1), ω ((fun _ : Fin (n + 1) => f) i) := by
    intro ω
    rw [show (∏ i : Fin (n + 1), ω ((fun _ : Fin (n + 1) => f) i)) = (ω f) ^ (n + 1) from
      Fin.prod_const (n + 1) (ω f)]
    ring
  simp_rw [hlhs]
  change ∫ ω, ω f * ∏ i, ω ((fun _ => f) i) ∂(measure T) = _
  rw [wick_recursive T n f (fun _ => f)]
  -- After wick_recursive + beta reduction, the goal is:
  -- ∑ j, inner ℝ (T f) (T f) * ∫ ω, ∏ i, ω f ∂(measure T) = (n+1) * c * ∫ ω, (ω f)^n ∂μ
  simp_rw [show @inner ℝ ell2' _ (T f) (T f) = c from rfl, Fin.prod_const]
  -- Now: ∑ j : Fin (n+1), c * ∫ ω, (ω f)^n ∂μ = (n+1) * c * ∫ ω, (ω f)^n ∂μ
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  -- Unify type annotations (Configuration TestFun2D = FieldConfig2D, measure T = freeFieldMeasure)
  change _ = (↑(n + 1) : ℝ) * c *
    ∫ ω : Configuration TestFun2D, (ω f) ^ n ∂(GaussianField.measure T)
  push_cast; ring

/-! ## Stein identity via formal polynomials

The Stein identity E[X · p(X)] = c · E[p'(X)] for X ~ N(0,c) is proved for formal
polynomials p ∈ ℝ[X] using `Polynomial.induction_on'`. The monomial case reduces
to `moment_recursion`, and the addition case follows from linearity of integration.
Combined with the Hermite derivative identity He'_{n+1}(x;c) = (n+1)·He_n(x;c),
this gives a uniform proof that E[He_n(X;c)] = 0 for all n ≥ 1. -/

open Polynomial in
/-- Formal polynomial version of wickMonomial, defined by the same recursion. -/
private def wickPoly : ℕ → ℝ → ℝ[X]
  | 0, _ => 1
  | 1, _ => X
  | n + 2, c => X * wickPoly (n + 1) c - C ((n + 1 : ℝ) * c) * wickPoly n c

open Polynomial in
/-- wickPoly evaluates to wickMonomial. -/
private theorem wickPoly_eval : ∀ (n : ℕ) (c x : ℝ),
    (wickPoly n c).eval x = wickMonomial n c x
  | 0, c, x => by simp [wickPoly, wickMonomial]
  | 1, c, x => by simp [wickPoly, wickMonomial]
  | n + 2, c, x => by
    simp only [wickPoly, wickMonomial_succ_succ, eval_sub, eval_mul, eval_X, eval_C]
    rw [wickPoly_eval (n + 1) c x, wickPoly_eval n c x]

open Polynomial in
/-- Hermite derivative identity for formal polynomials:
    d/dx [He_{n+1}(x;c)] = (n+1) · He_n(x;c). -/
private theorem wickPoly_derivative : ∀ (n : ℕ) (c : ℝ),
    (wickPoly (n + 1) c).derivative = C (↑(n + 1) : ℝ) * wickPoly n c
  | 0, c => by simp only [wickPoly, derivative_X]; rw [← map_one C]; simp
  | 1, c => by
    simp only [wickPoly, map_sub, derivative_mul, derivative_X, one_mul, mul_one, derivative_C,
      sub_zero]; norm_num; simp only [C_ofNat]; ring
  | n + 2, c => by
    have hunfold : wickPoly (n + 2 + 1) c =
        X * wickPoly (n + 2) c - C ((↑(n + 1) + 1) * c) * wickPoly (n + 1) c := rfl
    rw [hunfold, map_sub, derivative_mul, derivative_X, derivative_C_mul,
      wickPoly_derivative (n + 1) c, wickPoly_derivative n c, one_mul]
    set P := wickPoly (n + 2) c; set Q := wickPoly (n + 1) c; set R := wickPoly n c
    have hrec : X * Q = P + C ((↑n + 1) * c) * R := by
      have h : P = X * Q - C ((↑n + 1) * c) * R := rfl; linear_combination -h
    have hCeq : C (↑(n + 2) : ℝ) * C ((↑n + 1) * c) =
        C ((↑(n + 1) + 1) * c) * C (↑(n + 1) : ℝ) := by
      simp only [← C_mul]; congr 1; push_cast; ring
    have hCadd : (1 : ℝ[X]) + C (↑(n + 2) : ℝ) = C (↑(n + 2 + 1) : ℝ) := by
      rw [← map_one C, ← map_add]; congr 1; push_cast; ring
    linear_combination C (↑(n + 2) : ℝ) * hrec + R * hCeq + P * hCadd

/-- Powers of the Gaussian pairing are integrable. -/
private theorem power_integrable (mass : ℝ) (hmass : 0 < mass) (f : TestFun2D) (n : ℕ) :
    Integrable (fun ω : FieldConfig2D => (ω f) ^ n) (freeFieldMeasure mass hmass) := by
  set T := freeCovarianceCLM mass hmass
  have h : ∀ ω : FieldConfig2D, (ω f) ^ n = ∏ i : Fin n, ω ((fun _ => f) i) := by
    intro ω; rw [Fin.prod_const]
  simp_rw [h]
  change Integrable (fun ω => ∏ i : Fin n, ω ((fun _ => f) i)) (measure T)
  exact product_integrable T n (fun _ => f)

open Polynomial in
/-- Any polynomial evaluated at a Gaussian pairing is integrable. -/
private theorem poly_eval_integrable (mass : ℝ) (hmass : 0 < mass) (f : TestFun2D)
    (p : ℝ[X]) :
    Integrable (fun ω : FieldConfig2D => p.eval (ω f)) (freeFieldMeasure mass hmass) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => exact (hp.add hq).congr (.of_forall fun ω => eval_add.symm)
  | monomial n a =>
    simp only [eval_monomial]
    exact (power_integrable mass hmass f n).const_mul a |>.congr
      (.of_forall fun ω => by ring)

open Polynomial in
/-- Stein identity for formal polynomials: E[X · p(X)] = c · E[p'(X)]
    where X = ω(f) under the Gaussian field measure and c = Cov(f,f).
    Proved by structural induction on polynomials: the monomial case
    reduces to `moment_recursion` and the addition case uses linearity. -/
private theorem stein_polynomial (mass : ℝ) (hmass : 0 < mass) (f : TestFun2D)
    (p : ℝ[X]) :
    ∫ ω : FieldConfig2D, (ω f) * p.eval (ω f) ∂(freeFieldMeasure mass hmass) =
    GaussianField.covariance (freeCovarianceCLM mass hmass) f f *
      ∫ ω : FieldConfig2D, p.derivative.eval (ω f) ∂(freeFieldMeasure mass hmass) := by
  set T := freeCovarianceCLM mass hmass
  set c := GaussianField.covariance T f f
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [eval_add, derivative_add]
    -- Integrability of X * p.eval(X): it's (X*p).eval(X) which is a polynomial eval
    have hfp : Integrable (fun ω : FieldConfig2D => (ω f) * eval (ω f) p)
        (freeFieldMeasure mass hmass) :=
      (poly_eval_integrable mass hmass f (X * p)).congr
        (.of_forall fun ω => by simp [eval_mul, eval_X])
    have hfq : Integrable (fun ω : FieldConfig2D => (ω f) * eval (ω f) q)
        (freeFieldMeasure mass hmass) :=
      (poly_eval_integrable mass hmass f (X * q)).congr
        (.of_forall fun ω => by simp [eval_mul, eval_X])
    have hdp : Integrable (fun ω : FieldConfig2D => eval (ω f) (derivative p))
        (freeFieldMeasure mass hmass) := poly_eval_integrable mass hmass f (derivative p)
    have hdq : Integrable (fun ω : FieldConfig2D => eval (ω f) (derivative q))
        (freeFieldMeasure mass hmass) := poly_eval_integrable mass hmass f (derivative q)
    simp_rw [mul_add]
    rw [integral_add hfp hfq, integral_add hdp hdq, mul_add, hp, hq]
  | monomial n a =>
    simp only [eval_monomial, derivative_monomial]
    -- ∫ (ωf) * (a * (ωf)^n) = c * ∫ (a * ↑n) * (ωf)^{n-1}
    simp_rw [show ∀ ω : FieldConfig2D, (ω f) * (a * (ω f) ^ n) = a * (ω f) ^ (n + 1) from
      fun ω => by ring]
    rw [integral_const_mul, integral_const_mul]
    rcases n with _ | n
    · -- n = 0: a * ∫ (ωf) = 0
      simp only [Nat.cast_zero, mul_zero, zero_mul, Nat.zero_add, pow_one]
      have h0 : ∫ ω : FieldConfig2D, ω f ∂(freeFieldMeasure mass hmass) = 0 :=
        measure_centered T f
      rw [h0, mul_zero]
    · -- n ≥ 1: a * E[X^{n+2}] = c * (a * (n+1)) * E[X^n]
      rw [show n + 1 - 1 = n from by omega]
      rw [moment_recursion mass hmass f n]
      push_cast; ring

/-- Odd moments of the Gaussian field vanish: E[(ω f)^{2k+1}] = 0. -/
private theorem odd_power_vanish (mass : ℝ) (hmass : 0 < mass) (f : TestFun2D) (k : ℕ) :
    ∫ ω : FieldConfig2D, (ω f) ^ (2 * k + 1) ∂(freeFieldMeasure mass hmass) = 0 := by
  have hprod : ∀ ω : FieldConfig2D, (ω f) ^ (2 * k + 1) =
    ∏ i : Fin (2 * k + 1), ω ((fun _ => f) i) := by
    intro ω; rw [Fin.prod_const]
  simp_rw [hprod]
  change ∫ ω, ∏ i : Fin (2 * k + 1), ω ((fun _ => f) i)
    ∂(measure (freeCovarianceCLM mass hmass)) = 0
  exact odd_moment_vanish _ k (fun _ => f)

/-- Centered Gaussian is symmetric under negation. -/
private theorem gaussianReal_zero_neg_invariant (v : ℝ≥0) :
    (gaussianReal 0 v).map (fun x : ℝ => -x) = gaussianReal 0 v := by
  rw [gaussianReal_map_neg]; simp

/-- Odd functions integrate to 0 under centered Gaussian. -/
private theorem integral_odd_gaussianReal_zero (v : ℝ≥0) (g : ℝ → ℝ)
    (hg_meas : Measurable g) (hg_odd : ∀ x, g (-x) = -g x) :
    ∫ x, g x ∂(gaussianReal 0 v) = 0 := by
  have h : ∫ x, g x ∂(gaussianReal 0 v) =
    ∫ x, g (-x) ∂(gaussianReal 0 v) := by
    conv_lhs => rw [← gaussianReal_zero_neg_invariant v]
    rw [integral_map measurable_neg.aemeasurable hg_meas.aestronglyMeasurable]
  simp only [hg_odd, integral_neg] at h; linarith

/-- wickMonomial n c is an odd function when n is odd. -/
private theorem wickMonomial_odd_fun (n : ℕ) (c : ℝ) (hn : Odd n) :
    ∀ x, wickMonomial n c (-x) = -wickMonomial n c x := by
  intro x; rw [wickMonomial_neg n c x]
  obtain ⟨k, rfl⟩ := hn; simp [pow_succ, pow_mul]

/-- For odd n, E[wickMonomial n c (ω f)] = 0 for ANY c.
    Proved via pushforward to 1D Gaussian + odd function symmetry. -/
private theorem wickMonomial_odd_zero_expectation (n : ℕ) (c : ℝ) (hn : Odd n)
    (mass : ℝ) (hmass : 0 < mass) (f : TestFun2D) :
    ∫ ω, wickMonomial n c (ω f) ∂(freeFieldMeasure mass hmass) = 0 := by
  set T := freeCovarianceCLM mass hmass
  rw [show freeFieldMeasure mass hmass = measure T from rfl,
    ← integral_map (configuration_eval_measurable f).aemeasurable
      (wickMonomial_continuous n c).measurable.aestronglyMeasurable,
    pairing_is_gaussian T f]
  exact integral_odd_gaussianReal_zero _ _ (wickMonomial_continuous n c).measurable
    (wickMonomial_odd_fun n c hn)

open Polynomial in
/-- E[wickMonomial (m+2) c X] = 0 via the Stein identity (no induction needed).
    The proof uses the identity He_{m+2}(x;c) = x·He_{m+1}(x;c) - (m+1)c·He_m(x;c),
    combined with E[X·p(X)] = c·E[p'(X)] and He'_{m+1} = (m+1)·He_m.
    The two terms cancel exactly, giving 0 regardless of E[He_m]. -/
private theorem wickMonomial_zero_expectation_ge_two (m : ℕ)
    (mass : ℝ) (hmass : 0 < mass) (f : TestFun2D) :
    ∫ ω : FieldConfig2D, wickMonomial (m + 2)
      (GaussianField.covariance (freeCovarianceCLM mass hmass) f f) (ω f)
      ∂(freeFieldMeasure mass hmass) = 0 := by
  set T := freeCovarianceCLM mass hmass
  set c := GaussianField.covariance T f f
  set μ := freeFieldMeasure mass hmass
  -- Step 1: Unfold the wickMonomial recursion
  have hrec : ∀ ω : FieldConfig2D, wickMonomial (m + 2) c (ω f) =
      (ω f) * wickMonomial (m + 1) c (ω f) - (↑m + 1) * c * wickMonomial m c (ω f) :=
    fun ω => wickMonomial_succ_succ m c (ω f)
  simp_rw [hrec]
  -- Step 2: Integrability
  have hint_mul : Integrable (fun ω : FieldConfig2D => (ω f) * wickMonomial (m + 1) c (ω f)) μ :=
    (poly_eval_integrable mass hmass f (X * wickPoly (m + 1) c)).congr
      (.of_forall fun ω => by simp [eval_mul, eval_X, wickPoly_eval])
  have hint_low : Integrable (fun ω : FieldConfig2D => wickMonomial m c (ω f)) μ :=
    (poly_eval_integrable mass hmass f (wickPoly m c)).congr
      (.of_forall fun ω => by simp [wickPoly_eval])
  have hint_const : Integrable (fun ω : FieldConfig2D =>
      (↑m + 1) * c * wickMonomial m c (ω f)) μ :=
    hint_low.const_mul ((↑m + 1) * c)
  -- Step 3: Split the integral
  rw [integral_sub hint_mul hint_const, integral_const_mul]
  -- Step 4: Apply Stein identity to wickPoly (m+1) c
  have hstein : ∫ ω : FieldConfig2D, (ω f) * wickMonomial (m + 1) c (ω f) ∂μ =
      c * ∫ ω : FieldConfig2D, (wickPoly (m + 1) c).derivative.eval (ω f) ∂μ := by
    have := stein_polynomial mass hmass f (wickPoly (m + 1) c)
    simp_rw [wickPoly_eval] at this; exact this
  rw [hstein]
  -- Step 5: Use the derivative identity and cancel
  simp_rw [wickPoly_derivative, eval_mul, eval_C, wickPoly_eval, integral_const_mul]
  push_cast; ring

/-- E[wickMonomial n c (ω f)] = 0 when c = covariance(f, f) and n ≥ 1.
    Odd n: Gaussian symmetry (odd function under symmetric measure).
    Even n ≥ 2: Stein identity + Hermite derivative identity. -/
theorem wickMonomial_zero_expectation (n : ℕ) (hn : 0 < n)
    (mass : ℝ) (hmass : 0 < mass) (f : TestFun2D) :
    ∫ ω, wickMonomial n
      (GaussianField.covariance (freeCovarianceCLM mass hmass) f f) (ω f)
      ∂(freeFieldMeasure mass hmass) = 0 := by
  set T := freeCovarianceCLM mass hmass
  set c := GaussianField.covariance T f f
  -- Split on parity: odd n handled uniformly, even n by direct computation
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | hodd
  · -- Even case: n = k + k
    rcases k with _ | _ | _ | k
    · omega
    · -- k = 1, n = 2
      have hn2 : n = 2 := by omega
      subst hn2; simp only [wickMonomial_two]
      rw [integral_sub
        (by have h := (pairing_memLp T f 2).integrable_norm_rpow
              (show (2 : ℝ≥0∞) ≠ 0 by norm_num) (show (2 : ℝ≥0∞) ≠ ⊤ by norm_num)
            refine h.congr (.of_forall fun ω => ?_)
            simp only [Real.norm_eq_abs]
            rw [show ((2 : ℝ≥0) : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) from by norm_num,
              Real.rpow_natCast, sq_abs])
        (integrable_const c)]
      rw [integral_sq_eq_cov mass hmass f, integral_const]
      simp [Measure.real, measure_univ]; ring
    · -- k = 2, n = 4
      have hn4 : n = 4 := by omega
      subst hn4; simp only [wickMonomial_four]
      -- Integrability helpers
      have hint4 : Integrable (fun ω : FieldConfig2D => (ω f) ^ 4)
          (freeFieldMeasure mass hmass) := by
        have h := (pairing_memLp T f 4).integrable_norm_rpow
          (show (4 : ℝ≥0∞) ≠ 0 by norm_num) (show (4 : ℝ≥0∞) ≠ ⊤ by norm_num)
        refine h.congr (.of_forall fun ω => ?_)
        simp only [Real.norm_eq_abs]
        rw [show ((4 : ℝ≥0) : ℝ≥0∞).toReal = ((4 : ℕ) : ℝ) from by norm_num,
          Real.rpow_natCast]
        have : (ω f) ^ 2 = |ω f| ^ 2 := (sq_abs (ω f)).symm
        nlinarith [sq_nonneg (ω f), sq_nonneg (|ω f|)]
      have hint2 : Integrable (fun ω : FieldConfig2D => (ω f) ^ 2)
          (freeFieldMeasure mass hmass) := by
        have h := (pairing_memLp T f 2).integrable_norm_rpow
          (show (2 : ℝ≥0∞) ≠ 0 by norm_num) (show (2 : ℝ≥0∞) ≠ ⊤ by norm_num)
        refine h.congr (.of_forall fun ω => ?_)
        simp only [Real.norm_eq_abs]
        rw [show ((2 : ℝ≥0) : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) from by norm_num,
          Real.rpow_natCast, sq_abs]
      -- Compute: ∫ (x⁴ - 6cx² + 3c²) = 3c² - 6c·c + 3c² = 0
      -- Split the integral using have+exact (rw can't match the pattern)
      have split1 : ∫ ω : FieldConfig2D,
          ((ω f) ^ 4 - 6 * c * (ω f) ^ 2 + 3 * c ^ 2) ∂(freeFieldMeasure mass hmass) =
          (∫ ω : FieldConfig2D, ((ω f) ^ 4 - 6 * c * (ω f) ^ 2)
            ∂(freeFieldMeasure mass hmass)) +
          ∫ _ : FieldConfig2D, (3 * c ^ 2) ∂(freeFieldMeasure mass hmass) :=
        integral_add (hint4.sub (hint2.const_mul _)) (integrable_const _)
      have split2 : ∫ ω : FieldConfig2D,
          ((ω f) ^ 4 - 6 * c * (ω f) ^ 2) ∂(freeFieldMeasure mass hmass) =
          (∫ ω : FieldConfig2D, (ω f) ^ 4 ∂(freeFieldMeasure mass hmass)) -
          ∫ ω : FieldConfig2D, (6 * c * (ω f) ^ 2) ∂(freeFieldMeasure mass hmass) :=
        integral_sub hint4 (hint2.const_mul _)
      rw [split1, split2, integral_const_mul,
        integral_fourth_eq mass hmass f, integral_sq_eq_cov mass hmass f, integral_const]
      simp [Measure.real, measure_univ]; ring
    · -- k ≥ 3, n ≥ 6: apply the Stein identity lemma
      have hn_eq : n = (2 * k + 4) + 2 := by omega
      rw [hn_eq]
      exact wickMonomial_zero_expectation_ge_two _ mass hmass f
  · -- Odd case: use Gaussian symmetry (works for any c)
    exact wickMonomial_odd_zero_expectation n c hodd mass hmass f

/-- Wick products have zero expectation once the Wick covariance parameter matches
    the variance of the smeared Gaussian variable at the evaluation point. -/
theorem wickPower_zero_expectation (n : ℕ) (hn : 0 < n)
    (mass : ℝ) (hmass : 0 < mass) (κ : UVCutoff) (x : Spacetime2D)
    (hcov : GaussianField.covariance (freeCovarianceCLM mass hmass)
      (uvMollifier κ x) (uvMollifier κ x) = regularizedPointCovariance mass κ) :
    ∫ ω, wickPower n mass κ ω x ∂(freeFieldMeasure mass hmass) = 0 := by
  set f := uvMollifier κ x
  set c := regularizedPointCovariance mass κ
  set T := freeCovarianceCLM mass hmass
  have hc : c = GaussianField.covariance T f f :=
    by simpa [f, c, T] using hcov.symm
  show ∫ ω, wickMonomial n c (ω f) ∂(freeFieldMeasure mass hmass) = 0
  rw [hc]
  exact wickMonomial_zero_expectation n hn mass hmass f

/-- Origin specialization of `wickPower_zero_expectation`. -/
theorem wickPower_zero_expectation_origin (n : ℕ) (hn : 0 < n)
    (mass : ℝ) (hmass : 0 < mass) (κ : UVCutoff) :
    ∫ ω, wickPower n mass κ ω 0 ∂(freeFieldMeasure mass hmass) = 0 := by
  apply wickPower_zero_expectation n hn mass hmass κ 0
  exact regularizedPointCovariance_covariance_origin mass hmass κ

/-- Hölder triple: `(2p)⁻¹ + (2p)⁻¹ = p⁻¹`. Used for products via Hölder's inequality. -/
instance holderTriple_double (p : ℝ≥0∞) : ENNReal.HolderTriple (2 * p) (2 * p) p where
  inv_add_inv_eq_inv := by
    by_cases h0 : p = 0
    · simp [h0]
    · by_cases htop : p = ⊤
      · simp [htop]
      · have h2p_inv : (2 * p)⁻¹ = 2⁻¹ * p⁻¹ :=
          ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
        rw [h2p_inv, ← two_mul,
          show (2 : ℝ≥0∞) * (2⁻¹ * p⁻¹) = (2 * 2⁻¹) * p⁻¹ from by ring]
        rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]

/-- Wick monomials composed with an Lᵖ function are in Lᵖ for all finite p.
    Proof by structural induction matching the wickMonomial recursion,
    using Hölder's inequality at each step. -/
private theorem wickMonomial_memLp_all
    {μ : Measure FieldConfig2D} [IsFiniteMeasure μ]
    (c : ℝ) (g : FieldConfig2D → ℝ)
    (hg : ∀ q : ℝ≥0∞, q ≠ ⊤ → MemLp g q μ) :
    ∀ (n : ℕ) (p : ℝ≥0∞), p ≠ ⊤ → MemLp (fun ω => wickMonomial n c (g ω)) p μ
  | 0, p, _ => by simp; exact memLp_const 1
  | 1, p, hp => by simp; exact hg p hp
  | n + 2, p, hp => by
    have h2p : 2 * p ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hp
    have ih_n := wickMonomial_memLp_all c g hg n
    have ih_n1 := wickMonomial_memLp_all c g hg (n + 1)
    set h := fun ω => wickMonomial (n + 1) c (g ω) with hdef
    have hprod : MemLp (g * h) p μ := (ih_n1 (2 * p) h2p).mul (hg (2 * p) h2p)
    have hconst : MemLp (((↑n + 1) * c) • fun ω => wickMonomial n c (g ω)) p μ :=
      (ih_n p hp).const_smul ((↑n + 1) * c)
    have hsub : MemLp (g * h - ((↑n + 1) * c) • fun ω => wickMonomial n c (g ω)) p μ :=
      hprod.sub hconst
    refine (memLp_congr_ae (Filter.Eventually.of_forall fun ω => ?_)).mp hsub
    simp only [wickMonomial_succ_succ, hdef, Pi.mul_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]

/-- Wick products are in Lᵖ for all p < ∞ in d=2.
    This is Theorem 8.5.3 of Glimm-Jaffe.
    The proof uses Hölder's inequality via induction on the wickMonomial recursion,
    combined with the fact that Gaussian pairings ω(f) have all finite moments. -/
theorem wickPower_memLp (n : ℕ) (mass : ℝ) (hmass : 0 < mass) (κ : UVCutoff)
    (x : Spacetime2D) {p : ℝ≥0∞} (hp : p ≠ ⊤) :
    MemLp (fun ω => wickPower n mass κ ω x) p (freeFieldMeasure mass hmass) := by
  set f := uvMollifier κ x
  set c := regularizedPointCovariance mass κ
  set T := freeCovarianceCLM mass hmass
  show MemLp (fun ω => wickMonomial n c (ω f)) p (freeFieldMeasure mass hmass)
  apply wickMonomial_memLp_all c (fun ω => ω f)
  · intro q hq
    have h := pairing_memLp T f q.toNNReal
    rwa [ENNReal.coe_toNNReal hq] at h
  · exact hp

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

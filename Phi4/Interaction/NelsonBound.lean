/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.WickProduct
import Phi4.Interaction.UVInfra
import Phi4.LatticeApproximation
import GaussianField.IsGaussian

/-!
# Nelson Bounds for Interaction Analytic Inputs

This file contains the negative-exponential / lower-tail branch of the
interaction analysis: deterministic Wick lower bounds, reference cutoffs,
hypercontractive Markov reductions, and the remaining Nelson-side frontier
statements.
-/

noncomputable section

open MeasureTheory GaussianField Filter
open scoped ENNReal NNReal Topology

/-! ## Nelson's uniform exponential moment bound (Simon Theorem V.14)

The core analytic estimate: for any p > 0, the *negative* exponential moments
E[exp(-p V_{Λ,κ})] are bounded uniformly in the UV cutoff κ.

**Statement-level corrections:**
1. The original statement (`gap_exponential_moment_geometric_bound`) asked for geometric
   decay E[exp(θ|V|)] ≤ D·rⁿ with r < 1. This is mathematically impossible: under a
   probability measure, exp(θ|V|) ≥ 1 always. See `test/proofideas_interaction_next_steps.lean`.
2. The intermediate statement (`gap_exp_interaction_uniform_bound` with |V|) asked for
   E[exp(p|V_κ|)] ≤ C uniformly. This is also false: V_κ is in the 4th Wiener chaos,
   so tails decay like exp(-c√t), making E[exp(p|V_κ|)] = ∞ for any p > 0.

The correct statement uses *negative* exponential moments E[exp(-pV_κ)]. The key insight
is that V_κ = λ∫:φ⁴:dx is NOT symmetric: :φ⁴:_{c_κ} ≥ -6c_κ² pointwise (bounded below),
but unbounded above (heavily right-skewed). So exp(-pV_κ) ≤ exp(6pλc_κ²|Λ|) is finite
for each κ, and Nelson's more sophisticated argument (using hypercontractivity + covariance
splitting) shows the bound is uniform in κ.

Reference: Simon, "The P(φ)₂ Euclidean Field Theory", Theorem V.14;
Glimm-Jaffe, "Quantum Physics", Chapter 8.6. -/

/-- Deterministic lower bound for the cutoff interaction.

    This is the spatially integrated form of the pointwise Wick lower bound
    `:φ⁴:_{c_κ} ≥ -6 c_κ²`. It is uniform in the field configuration `ω`. -/
theorem interactionCutoff_lower_bound
    (params : Phi4Params) (Λ : Rectangle) (κ : UVCutoff) (ω : FieldConfig2D) :
    -(params.coupling * (6 * (regularizedPointCovariance params.mass κ) ^ 2 *
      (MeasureTheory.volume Λ.toSet).toReal))
      ≤ interactionCutoff params Λ κ ω := by
  let c : ℝ := regularizedPointCovariance params.mass κ
  have hwick_lower : ∀ x ∈ Λ.toSet, -(6 * c ^ 2 : ℝ) ≤ wickPower 4 params.mass κ ω x := by
    intro x hx
    simp [wickPower, wickMonomial_four, c]
    nlinarith [sq_nonneg (rawFieldEval params.mass κ ω x ^ 2 - 3 * c)]
  have hwick_int :
      IntegrableOn (fun x : Spacetime2D => wickPower 4 params.mass κ ω x) Λ.toSet volume := by
    exact
      (wickPower_continuous_in_x 4 params.mass κ ω).continuousOn.integrableOn_compact
        Λ.toSet_isCompact
  have hset :
      -(6 * c ^ 2 : ℝ) * volume.real Λ.toSet ≤
        ∫ x in Λ.toSet, wickPower 4 params.mass κ ω x := by
    rw [measureReal_def]
    exact
      MeasureTheory.setIntegral_ge_of_const_le_real
        (μ := volume) (s := Λ.toSet)
        (f := fun x : Spacetime2D => wickPower 4 params.mass κ ω x)
        (c := -(6 * c ^ 2 : ℝ))
        Λ.toSet_measurableSet Λ.toSet_volume_ne_top hwick_lower hwick_int
  have hcoupling : 0 ≤ params.coupling := le_of_lt params.coupling_pos
  have hscaled := mul_le_mul_of_nonneg_left hset hcoupling
  rw [measureReal_def] at hscaled
  unfold interactionCutoff
  nlinarith [hscaled]

/-- If the negative threshold is below the deterministic cutoff lower bound,
    the lower-tail event is empty. This is the first cutoffwise reduction used
    in Nelson's argument. -/
theorem interactionCutoff_neg_tail_eq_empty
    (params : Phi4Params) (Λ : Rectangle) (κ : UVCutoff) {t : ℝ}
    (ht :
      params.coupling * (6 * (regularizedPointCovariance params.mass κ) ^ 2 *
        (MeasureTheory.volume Λ.toSet).toReal) ≤ t) :
    {ω : FieldConfig2D | interactionCutoff params Λ κ ω < -t} = ∅ := by
  ext ω
  constructor
  · intro hω
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false] at hω ⊢
    have hlower := interactionCutoff_lower_bound params Λ κ ω
    linarith
  · intro hω
    simp at hω

/-- If a reference cutoff `κ₀` already satisfies the deterministic lower bound
    `V_{Λ,κ₀} ≥ -t`, then any stronger lower-tail event for another cutoff `κ`
    reduces to a lower-tail event for the difference `V_{Λ,κ} - V_{Λ,κ₀}`. This
    isolates the genuinely fluctuating shell term in Nelson's argument. -/
theorem interactionCutoff_neg_tail_subset_of_sub_tail
    (params : Phi4Params) (Λ : Rectangle) (κ κ₀ : UVCutoff) {t s : ℝ}
    (hκ₀ :
      params.coupling * (6 * (regularizedPointCovariance params.mass κ₀) ^ 2 *
        (MeasureTheory.volume Λ.toSet).toReal) ≤ t) :
    {ω : FieldConfig2D | interactionCutoff params Λ κ ω < -(t + s)} ⊆
      {ω : FieldConfig2D |
        interactionCutoff params Λ κ ω - interactionCutoff params Λ κ₀ ω < -s} := by
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  have hlower := interactionCutoff_lower_bound params Λ κ₀ ω
  linarith

/-- Measure version of `interactionCutoff_neg_tail_subset_of_sub_tail`. -/
theorem measure_interactionCutoff_neg_tail_le_sub_tail
    (params : Phi4Params) (Λ : Rectangle) (κ κ₀ : UVCutoff) {t s : ℝ}
    (hκ₀ :
      params.coupling * (6 * (regularizedPointCovariance params.mass κ₀) ^ 2 *
        (MeasureTheory.volume Λ.toSet).toReal) ≤ t) :
    (freeFieldMeasure params.mass params.mass_pos)
      {ω : FieldConfig2D | interactionCutoff params Λ κ ω < -(t + s)}
      ≤
    (freeFieldMeasure params.mass params.mass_pos)
      {ω : FieldConfig2D |
        interactionCutoff params Λ κ ω - interactionCutoff params Λ κ₀ ω < -s} := by
  exact measure_mono (interactionCutoff_neg_tail_subset_of_sub_tail params Λ κ κ₀ hκ₀)

/-- Markov's inequality at even moment order: for a measurable real-valued
function `Y` and `j ≥ 1`, `P(|Y| > 1)` is bounded by the `2j`-th moment. -/
theorem markov_even_moment
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y : Ω → ℝ} (j : ℕ)
    (hint : Integrable (fun ω => |Y ω| ^ (2 * j)) μ) :
    μ {ω | 1 < |Y ω|} ≤ ENNReal.ofReal (∫ ω, |Y ω| ^ (2 * j) ∂μ) := by
  have hsub : {ω | 1 < |Y ω|} ⊆ {ω | (1 : ℝ) ≤ |Y ω| ^ (2 * j)} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    exact one_le_pow₀ (le_of_lt hω)
  calc
    μ {ω | 1 < |Y ω|}
      ≤ μ {ω | (1 : ℝ) ≤ |Y ω| ^ (2 * j)} := measure_mono hsub
    _ ≤ ENNReal.ofReal (∫ ω, |Y ω| ^ (2 * j) ∂μ) :=
        hint.measure_le_integral
          (ae_of_all _ (fun ω => pow_nonneg (abs_nonneg _) _))
          (fun ω hω => hω)

/-- `4 - log 16` is positive, since `16 < exp 4`. This is the decay exponent
appearing in the Markov optimization step. -/
private theorem four_sub_log_sixteen_pos : 0 < 4 - Real.log 16 := by
  have : Real.log 16 < 4 := by
    rw [show (4 : ℝ) = Real.log (Real.exp 4) from (Real.log_exp 4).symm]
    exact Real.log_lt_log (by positivity) (by
      calc (16 : ℝ) = 2 ^ 4 := by norm_num
        _ < Real.exp 1 ^ 4 :=
          pow_lt_pow_left₀ Real.exp_one_gt_two (by norm_num) (by norm_num)
        _ = Real.exp 4 := by rw [← Real.exp_nat_mul]; norm_num)
  linarith

/-- Markov optimization: when the even moments satisfy the hypercontractive-type
growth `((C j)^4 * ε^2)^j`, one can choose an optimal integer moment order
producing a double-exponential decay scale `exp(-c / sqrt ε)`. -/
theorem markov_optimization_exists_j
    (C : ℝ) (hC : 0 < C) (ε : ℝ) (hε : 0 < ε)
    (hε_small : ε ≤ 1 / (Real.exp 1 * C) ^ 2) :
    ∃ (c : ℝ) (j : ℕ), 0 < c ∧ 0 < j ∧
      (C * ↑j) ^ (4 * j) * ε ^ (2 * j) ≤ Real.exp (-(c / Real.sqrt ε)) := by
  set e₁ := Real.exp 1
  set β := 4 - Real.log 16
  set j_real := 1 / (e₁ * C * Real.sqrt ε)
  set j := Nat.ceil j_real
  set c := β / (e₁ * C)
  refine ⟨c, j, ?_, ?_, ?_⟩
  · exact div_pos four_sub_log_sixteen_pos (mul_pos (Real.exp_pos 1) hC)
  ·
    have hj_real_pos : 0 < j_real :=
      div_pos one_pos (mul_pos (mul_pos (Real.exp_pos 1) hC) (Real.sqrt_pos.mpr hε))
    exact Nat.ceil_pos.mpr hj_real_pos
  ·
    have he₁_pos : 0 < e₁ := Real.exp_pos 1
    have hsqrt_pos : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
    have heC_pos : 0 < e₁ * C := mul_pos he₁_pos hC
    have hj_real_pos : 0 < j_real :=
      div_pos one_pos (mul_pos heC_pos hsqrt_pos)
    have hj_real_ge_one : 1 ≤ j_real := by
      rw [one_le_div (mul_pos heC_pos hsqrt_pos)]
      have hsq_le : Real.sqrt ε ≤ 1 / (e₁ * C) := by
        rw [Real.sqrt_le_left]
        · rwa [div_pow, one_pow]
        · exact div_nonneg (by norm_num) (le_of_lt heC_pos)
      calc e₁ * C * Real.sqrt ε
          ≤ e₁ * C * (1 / (e₁ * C)) :=
            mul_le_mul_of_nonneg_left hsq_le (le_of_lt heC_pos)
        _ = 1 := by field_simp
    have hj_le : (j : ℝ) ≤ 2 * j_real := by
      have : (j : ℝ) ≤ j_real + 1 :=
        le_of_lt (Nat.ceil_lt_add_one (le_of_lt hj_real_pos))
      linarith
    have hj_ge : j_real ≤ (j : ℝ) := Nat.le_ceil j_real
    have hCj_le : C * (j : ℝ) ≤ 2 / (e₁ * Real.sqrt ε) := by
      calc C * (j : ℝ) ≤ C * (2 * j_real) :=
              mul_le_mul_of_nonneg_left hj_le (le_of_lt hC)
        _ = 2 * (C / (e₁ * C * Real.sqrt ε)) := by ring
        _ = 2 / (e₁ * Real.sqrt ε) := by
            congr 1
            field_simp
    have hbase_le : (C * (j : ℝ)) ^ 4 * ε ^ 2 ≤ 16 / e₁ ^ 4 := by
      have h1 : (C * (j : ℝ)) ^ 4 ≤ (2 / (e₁ * Real.sqrt ε)) ^ 4 :=
        pow_le_pow_left₀ (by positivity) hCj_le 4
      have hsq : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt (le_of_lt hε)
      have h2 : (2 / (e₁ * Real.sqrt ε)) ^ 4 * ε ^ 2 = 16 / e₁ ^ 4 := by
        have he₁_ne : e₁ ≠ 0 := ne_of_gt he₁_pos
        have hsqrt_ne : Real.sqrt ε ≠ 0 := ne_of_gt hsqrt_pos
        field_simp
        rw [show (Real.sqrt ε) ^ 4 = ((Real.sqrt ε) ^ 2) ^ 2 from by ring, hsq]
        ring
      linarith [mul_le_mul_of_nonneg_right h1 (sq_nonneg ε)]
    have hrewrite : (C * (j : ℝ)) ^ (4 * j) * ε ^ (2 * j) =
        ((C * (j : ℝ)) ^ 4 * ε ^ 2) ^ (j : ℕ) := by
      rw [mul_pow, pow_mul, pow_mul, pow_mul]
      ring
    rw [hrewrite]
    have hbase_nonneg : 0 ≤ (C * (j : ℝ)) ^ 4 * ε ^ 2 := by positivity
    have hpow_le : ((C * (j : ℝ)) ^ 4 * ε ^ 2) ^ j ≤ (16 / e₁ ^ 4) ^ j :=
      pow_le_pow_left₀ hbase_nonneg hbase_le j
    have hlog_ratio : Real.log (16 / e₁ ^ 4) = Real.log 16 - 4 := by
      rw [Real.log_div (by positivity : (16 : ℝ) ≠ 0) (by positivity : e₁ ^ 4 ≠ 0)]
      congr 1
      rw [Real.log_pow, Real.log_exp]
      norm_num
    have hratio_pos : 0 < 16 / e₁ ^ 4 := by positivity
    have hratio_eq : 16 / e₁ ^ 4 = Real.exp (-β) := by
      rw [← Real.exp_log hratio_pos, hlog_ratio]
      congr 1
      ring
    have hpow_eq : (16 / e₁ ^ 4) ^ j = Real.exp (-(β * (j : ℝ))) := by
      rw [hratio_eq, ← Real.exp_nat_mul, mul_comm]
      congr 1
      ring
    have hβj_ge : β * j_real ≤ β * (j : ℝ) :=
      mul_le_mul_of_nonneg_left hj_ge (le_of_lt four_sub_log_sixteen_pos)
    have hβj_real_eq : β * j_real = c / Real.sqrt ε := by
      simp only [c, j_real]
      field_simp
    have hexp_le : Real.exp (-(β * (j : ℝ))) ≤ Real.exp (-(c / Real.sqrt ε)) := by
      apply Real.exp_le_exp_of_le
      linarith
    linarith [hpow_le, hpow_eq, hexp_le]

/-- Explicit decay constant appearing in the optimized Markov bound. -/
private def markovTailConstant (C : ℝ) : ℝ :=
  (4 - Real.log 16) / (Real.exp 1 * C)

/-- Explicit version of the Markov optimization step. The decay constant depends
only on `C`, not on the scale `ε`. -/
private theorem markov_optimization_explicit_bound
    (C : ℝ) (hC : 0 < C) (ε : ℝ) (hε : 0 < ε)
    (hε_small : ε ≤ 1 / (Real.exp 1 * C) ^ 2) :
    ∃ j : ℕ, 0 < j ∧
      (C * ↑j) ^ (4 * j) * ε ^ (2 * j) ≤
        Real.exp (-(markovTailConstant C / Real.sqrt ε)) := by
  set e₁ := Real.exp 1
  set β := 4 - Real.log 16
  set j_real := 1 / (e₁ * C * Real.sqrt ε)
  set j := Nat.ceil j_real
  have hj : 0 < j := by
    have hj_real_pos : 0 < j_real :=
      div_pos one_pos (mul_pos (mul_pos (Real.exp_pos 1) hC) (Real.sqrt_pos.mpr hε))
    exact Nat.ceil_pos.mpr hj_real_pos
  refine ⟨j, hj, ?_⟩
  have he₁_pos : 0 < e₁ := Real.exp_pos 1
  have hsqrt_pos : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have heC_pos : 0 < e₁ * C := mul_pos he₁_pos hC
  have hj_real_pos : 0 < j_real := div_pos one_pos (mul_pos heC_pos hsqrt_pos)
  have hj_real_ge_one : 1 ≤ j_real := by
    rw [one_le_div (mul_pos heC_pos hsqrt_pos)]
    have hsq_le : Real.sqrt ε ≤ 1 / (e₁ * C) := by
      rw [Real.sqrt_le_left]
      · rwa [div_pow, one_pow]
      · exact div_nonneg (by norm_num) (le_of_lt heC_pos)
    calc e₁ * C * Real.sqrt ε
        ≤ e₁ * C * (1 / (e₁ * C)) :=
          mul_le_mul_of_nonneg_left hsq_le (le_of_lt heC_pos)
      _ = 1 := by field_simp
  have hj_le : (j : ℝ) ≤ 2 * j_real := by
    have : (j : ℝ) ≤ j_real + 1 :=
      le_of_lt (Nat.ceil_lt_add_one (le_of_lt hj_real_pos))
    linarith
  have hj_ge : j_real ≤ (j : ℝ) := Nat.le_ceil j_real
  have hCj_le : C * (j : ℝ) ≤ 2 / (e₁ * Real.sqrt ε) := by
    calc C * (j : ℝ) ≤ C * (2 * j_real) :=
            mul_le_mul_of_nonneg_left hj_le (le_of_lt hC)
      _ = 2 * (C / (e₁ * C * Real.sqrt ε)) := by ring
      _ = 2 / (e₁ * Real.sqrt ε) := by
          congr 1
          field_simp
  have hbase_le : (C * (j : ℝ)) ^ 4 * ε ^ 2 ≤ 16 / e₁ ^ 4 := by
    have h1 : (C * (j : ℝ)) ^ 4 ≤ (2 / (e₁ * Real.sqrt ε)) ^ 4 :=
      pow_le_pow_left₀ (by positivity) hCj_le 4
    have hsq : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt (le_of_lt hε)
    have h2 : (2 / (e₁ * Real.sqrt ε)) ^ 4 * ε ^ 2 = 16 / e₁ ^ 4 := by
      have he₁_ne : e₁ ≠ 0 := ne_of_gt he₁_pos
      have hsqrt_ne : Real.sqrt ε ≠ 0 := ne_of_gt hsqrt_pos
      field_simp
      rw [show (Real.sqrt ε) ^ 4 = ((Real.sqrt ε) ^ 2) ^ 2 from by ring, hsq]
      ring
    linarith [mul_le_mul_of_nonneg_right h1 (sq_nonneg ε)]
  have hrewrite :
      (C * (j : ℝ)) ^ (4 * j) * ε ^ (2 * j) =
        ((C * (j : ℝ)) ^ 4 * ε ^ 2) ^ (j : ℕ) := by
    rw [mul_pow, pow_mul, pow_mul, pow_mul]
    ring
  rw [hrewrite]
  have hbase_nonneg : 0 ≤ (C * (j : ℝ)) ^ 4 * ε ^ 2 := by positivity
  have hpow_le : ((C * (j : ℝ)) ^ 4 * ε ^ 2) ^ j ≤ (16 / e₁ ^ 4) ^ j :=
    pow_le_pow_left₀ hbase_nonneg hbase_le j
  have hlog_ratio : Real.log (16 / e₁ ^ 4) = Real.log 16 - 4 := by
    rw [Real.log_div (by positivity : (16 : ℝ) ≠ 0) (by positivity : e₁ ^ 4 ≠ 0)]
    congr 1
    rw [Real.log_pow, Real.log_exp]
    norm_num
  have hratio_pos : 0 < 16 / e₁ ^ 4 := by positivity
  have hratio_eq : 16 / e₁ ^ 4 = Real.exp (-β) := by
    rw [← Real.exp_log hratio_pos, hlog_ratio]
    congr 1
    ring
  have hpow_eq : (16 / e₁ ^ 4) ^ j = Real.exp (-(β * (j : ℝ))) := by
    rw [hratio_eq, ← Real.exp_nat_mul, mul_comm]
    congr 1
    ring
  have hβj_ge : β * j_real ≤ β * (j : ℝ) :=
    mul_le_mul_of_nonneg_left hj_ge (le_of_lt four_sub_log_sixteen_pos)
  have hconst_eq :
      markovTailConstant C / Real.sqrt ε = β * j_real := by
    simp only [markovTailConstant, β, j_real, e₁]
    field_simp
  have hexp_le :
      Real.exp (-(β * (j : ℝ))) ≤
        Real.exp (-(markovTailConstant C / Real.sqrt ε)) := by
    apply Real.exp_le_exp_of_le
    rw [hconst_eq]
    linarith
  linarith [hpow_le, hpow_eq, hexp_le]

/-- Explicit constant form of `markov_hypercontractive_tail`. This is the
uniform decay constant needed to build `t`-uniform Nelson bounds later. -/
theorem markov_hypercontractive_tail_explicit
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y : Ω → ℝ} {C σ : ℝ} (hC : 0 < C) (hσ : 0 < σ)
    (hmoment : ∀ j : ℕ, 0 < j →
      Integrable (fun ω => |Y ω| ^ (2 * j)) μ ∧
      ∫ ω, |Y ω| ^ (2 * j) ∂μ ≤ (C * ↑j) ^ (4 * j) * σ ^ (2 * j))
    (hσ_small : σ ≤ 1 / (Real.exp 1 * C) ^ 2) :
    μ {ω | 1 < |Y ω|} ≤
      ENNReal.ofReal (Real.exp (-(markovTailConstant C / Real.sqrt σ))) := by
  obtain ⟨j, hj, hopt⟩ := markov_optimization_explicit_bound C hC σ hσ hσ_small
  obtain ⟨hint, hmom⟩ := hmoment j hj
  calc
    μ {ω | 1 < |Y ω|} ≤ ENNReal.ofReal (∫ ω, |Y ω| ^ (2 * j) ∂μ) :=
      markov_even_moment j hint
    _ ≤ ENNReal.ofReal ((C * ↑j) ^ (4 * j) * σ ^ (2 * j)) :=
      ENNReal.ofReal_le_ofReal hmom
    _ ≤ ENNReal.ofReal (Real.exp (-(markovTailConstant C / Real.sqrt σ))) :=
      ENNReal.ofReal_le_ofReal hopt

/-- Markov's inequality with optimized moment order turns hypercontractive even
moment growth into a double-exponential tail bound. -/
theorem markov_hypercontractive_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y : Ω → ℝ} {C σ : ℝ} (hC : 0 < C) (hσ : 0 < σ)
    (hmoment : ∀ j : ℕ, 0 < j →
      Integrable (fun ω => |Y ω| ^ (2 * j)) μ ∧
      ∫ ω, |Y ω| ^ (2 * j) ∂μ ≤ (C * ↑j) ^ (4 * j) * σ ^ (2 * j))
    (hσ_small : σ ≤ 1 / (Real.exp 1 * C) ^ 2) :
    ∃ c : ℝ, 0 < c ∧
      μ {ω | 1 < |Y ω|} ≤ ENNReal.ofReal (Real.exp (-(c / Real.sqrt σ))) := by
  obtain ⟨c, j, hc, hj, hopt⟩ := markov_optimization_exists_j C hC σ hσ hσ_small
  obtain ⟨hint, hmom⟩ := hmoment j hj
  refine ⟨c, hc, ?_⟩
  calc
    μ {ω | 1 < |Y ω|}
      ≤ ENNReal.ofReal (∫ ω, |Y ω| ^ (2 * j) ∂μ) := markov_even_moment j hint
    _ ≤ ENNReal.ofReal ((C * ↑j) ^ (4 * j) * σ ^ (2 * j)) :=
        ENNReal.ofReal_le_ofReal hmom
    _ ≤ ENNReal.ofReal (Real.exp (-(c / Real.sqrt σ))) :=
        ENNReal.ofReal_le_ofReal hopt

/-- Assumption-explicit Nelson reduction step.

    If a reference cutoff `κ₀` has already been chosen so that the deterministic
    lower bound gives `V_{Λ,κ₀} ≥ -t`, and if the cutoff difference
    `V_{Λ,κ} - V_{Λ,κ₀}` satisfies the hypercontractive even-moment bounds from
    `markov_hypercontractive_tail`, then the stronger lower-tail event
    `V_{Λ,κ} < -(t + 1)` already has double-exponential decay. The remaining
    work for Nelson's argument is therefore to construct `κ₀(t)` and prove the
    even-moment bound for the shell difference. -/
theorem interactionCutoff_neg_tail_of_reference_cutoff_and_hypercontractive_moments
    (params : Phi4Params) (Λ : Rectangle) (κ κ₀ : UVCutoff) {t C σ : ℝ}
    (hκ₀ :
      params.coupling * (6 * (regularizedPointCovariance params.mass κ₀) ^ 2 *
        (MeasureTheory.volume Λ.toSet).toReal) ≤ t)
    (hC : 0 < C) (hσ : 0 < σ)
    (hmoment : ∀ j : ℕ, 0 < j →
      Integrable
        (fun ω : FieldConfig2D =>
          |interactionCutoff params Λ κ ω - interactionCutoff params Λ κ₀ ω| ^ (2 * j))
        (freeFieldMeasure params.mass params.mass_pos) ∧
      ∫ ω, |interactionCutoff params Λ κ ω - interactionCutoff params Λ κ₀ ω| ^ (2 * j)
          ∂(freeFieldMeasure params.mass params.mass_pos)
        ≤ (C * ↑j) ^ (4 * j) * σ ^ (2 * j))
    (hσ_small : σ ≤ 1 / (Real.exp 1 * C) ^ 2) :
    ∃ c : ℝ, 0 < c ∧
      (freeFieldMeasure params.mass params.mass_pos)
        {ω : FieldConfig2D | interactionCutoff params Λ κ ω < -(t + 1)} ≤
      ENNReal.ofReal (Real.exp (-(c / Real.sqrt σ))) := by
  let μ := freeFieldMeasure params.mass params.mass_pos
  let Y : FieldConfig2D → ℝ :=
    fun ω => interactionCutoff params Λ κ ω - interactionCutoff params Λ κ₀ ω
  obtain ⟨c, hc, htailY⟩ :=
    markov_hypercontractive_tail (μ := μ) (Y := Y) (C := C) (σ := σ)
      hC hσ
      (by
        intro j hj
        simpa [μ, Y] using hmoment j hj)
      hσ_small
  refine ⟨c, hc, ?_⟩
  have hsub_abs : {ω : FieldConfig2D | Y ω < -(1 : ℝ)} ⊆ {ω : FieldConfig2D | 1 < |Y ω|} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    have hyneg : Y ω < 0 := by linarith
    rw [abs_of_neg hyneg]
    linarith
  calc
    μ {ω : FieldConfig2D | interactionCutoff params Λ κ ω < -(t + 1)}
      ≤ μ {ω : FieldConfig2D | Y ω < -(1 : ℝ)} := by
          simpa [μ, Y] using
            measure_interactionCutoff_neg_tail_le_sub_tail params Λ κ κ₀
              (t := t) (s := (1 : ℝ)) hκ₀
    _ ≤ μ {ω : FieldConfig2D | 1 < |Y ω|} := measure_mono hsub_abs
    _ ≤ ENNReal.ofReal (Real.exp (-(c / Real.sqrt σ))) := htailY

/-- Explicit-constant Nelson reduction step. This is the same reduction as
`interactionCutoff_neg_tail_of_reference_cutoff_and_hypercontractive_moments`,
but with the optimized Markov constant exposed directly. -/
theorem interactionCutoff_neg_tail_of_reference_cutoff_and_hypercontractive_moments_explicit
    (params : Phi4Params) (Λ : Rectangle) (κ κ₀ : UVCutoff) {t C σ : ℝ}
    (hκ₀ :
      params.coupling * (6 * (regularizedPointCovariance params.mass κ₀) ^ 2 *
        (MeasureTheory.volume Λ.toSet).toReal) ≤ t)
    (hC : 0 < C) (hσ : 0 < σ)
    (hmoment : ∀ j : ℕ, 0 < j →
      Integrable
        (fun ω : FieldConfig2D =>
          |interactionCutoff params Λ κ ω - interactionCutoff params Λ κ₀ ω| ^ (2 * j))
        (freeFieldMeasure params.mass params.mass_pos) ∧
      ∫ ω, |interactionCutoff params Λ κ ω - interactionCutoff params Λ κ₀ ω| ^ (2 * j)
          ∂(freeFieldMeasure params.mass params.mass_pos)
        ≤ (C * ↑j) ^ (4 * j) * σ ^ (2 * j))
    (hσ_small : σ ≤ 1 / (Real.exp 1 * C) ^ 2) :
    (freeFieldMeasure params.mass params.mass_pos)
      {ω : FieldConfig2D | interactionCutoff params Λ κ ω < -(t + 1)} ≤
    ENNReal.ofReal (Real.exp (-(markovTailConstant C / Real.sqrt σ))) := by
  let μ := freeFieldMeasure params.mass params.mass_pos
  let Y : FieldConfig2D → ℝ :=
    fun ω => interactionCutoff params Λ κ ω - interactionCutoff params Λ κ₀ ω
  have htailY :
      μ {ω | 1 < |Y ω|} ≤
        ENNReal.ofReal (Real.exp (-(markovTailConstant C / Real.sqrt σ))) := by
    exact markov_hypercontractive_tail_explicit (μ := μ) (Y := Y) hC hσ
      (by
        intro j hj
        simpa [μ, Y] using hmoment j hj)
      hσ_small
  have hsub_abs : {ω : FieldConfig2D | Y ω < -(1 : ℝ)} ⊆ {ω : FieldConfig2D | 1 < |Y ω|} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    have hyneg : Y ω < 0 := by linarith
    rw [abs_of_neg hyneg]
    linarith
  calc
    μ {ω : FieldConfig2D | interactionCutoff params Λ κ ω < -(t + 1)}
      ≤ μ {ω : FieldConfig2D | Y ω < -(1 : ℝ)} := by
          simpa [μ, Y] using
            measure_interactionCutoff_neg_tail_le_sub_tail params Λ κ κ₀
              (t := t) (s := (1 : ℝ)) hκ₀
    _ ≤ μ {ω : FieldConfig2D | 1 < |Y ω|} := measure_mono hsub_abs
    _ ≤ ENNReal.ofReal (Real.exp (-(markovTailConstant C / Real.sqrt σ))) := htailY

/-- Canonical Nelson reference-scale prefactor.

    The denominator is inflated by `((volume Λ.toSet).toReal + 1)` to avoid a
    separate positivity theorem for the rectangle volume in the cutoff-choice
    construction. This still gives the required deterministic lower bound
    `V_{Λ,κ₀(t)} ≥ -(t + 1)`. -/
private def nelsonReferenceAlpha (params : Phi4Params) (Λ : Rectangle) (K : ℝ) : ℝ :=
  1 / (K * Real.sqrt (6 * params.coupling * ((MeasureTheory.volume Λ.toSet).toReal + 1)))

/-- Logarithmic shift used to absorb the additive constant in the covariance-growth
bound `c_κ ≤ C₀ + K log κ`. -/
private def nelsonReferenceLogShift (K C₀ : ℝ) : ℝ :=
  C₀ / K

/-- Canonical reference cutoff `κ₀(t)` for Nelson's argument. -/
private def nelsonReferenceCutoff
    (params : Phi4Params) (Λ : Rectangle) (K C₀ t : ℝ) : UVCutoff :=
  ⟨Real.exp
      (nelsonReferenceAlpha params Λ K * Real.sqrt (t + 1) - nelsonReferenceLogShift K C₀),
    Real.exp_pos _⟩

/-- If the regularized point covariance grows at most logarithmically in the
    cutoff, then the canonical Nelson reference cutoff `κ₀(t)` forces the
    deterministic lower bound to sit below `t + 1`.

    This isolates the cutoff-choice part of Nelson's argument from the genuine
    moment estimate on `V_{Λ,κ} - V_{Λ,κ₀(t)}`. -/
theorem interactionCutoff_reference_cutoff_le_one_add_of_log_covariance_bound
    (params : Phi4Params) (Λ : Rectangle) {K : ℝ} (hK : 0 < K)
    {C₀ : ℝ} (_hC₀ : 0 ≤ C₀)
    (hcov :
      ∀ κ : UVCutoff,
        regularizedPointCovariance params.mass κ ≤ C₀ + K * Real.log κ.κ)
    {t : ℝ} (ht : 0 ≤ t) :
    params.coupling *
      (6 * (regularizedPointCovariance params.mass
          (nelsonReferenceCutoff params Λ K C₀ t)) ^ 2 *
        (MeasureTheory.volume Λ.toSet).toReal) ≤ t + 1 := by
  let V : ℝ := (MeasureTheory.volume Λ.toSet).toReal
  let D : ℝ := 6 * params.coupling * (V + 1)
  let α : ℝ := nelsonReferenceAlpha params Λ K
  let κ₀ : UVCutoff := nelsonReferenceCutoff params Λ K C₀ t
  have hV_nonneg : 0 ≤ V := by
    dsimp [V]
    positivity
  have hD_pos : 0 < D := by
    dsimp [D]
    have hV1 : 0 < V + 1 := by linarith
    exact mul_pos (mul_pos (by positivity) params.coupling_pos) hV1
  have hκ₀_log :
      Real.log κ₀.κ = α * Real.sqrt (t + 1) - C₀ / K := by
    dsimp [κ₀, nelsonReferenceCutoff]
    simp [α, nelsonReferenceLogShift]
  have hα_pos : 0 < α := by
    dsimp [α, nelsonReferenceAlpha]
    exact one_div_pos.mpr (mul_pos hK (Real.sqrt_pos.mpr hD_pos))
  have ht1_nonneg : 0 ≤ t + 1 := by linarith
  have hmain_nonneg : 0 ≤ K * (α * Real.sqrt (t + 1)) := by
    exact mul_nonneg hK.le (mul_nonneg hα_pos.le (Real.sqrt_nonneg _))
  have hcov_nonneg : 0 ≤ regularizedPointCovariance params.mass κ₀ := by
    rw [regularizedPointCovariance_eq_covariance params.mass params.mass_pos κ₀]
    exact covariance_self_nonneg params.mass params.mass_pos (uvMollifier κ₀ 0)
  have hcov_upper :
      regularizedPointCovariance params.mass κ₀ ≤ K * (α * Real.sqrt (t + 1)) := by
    have hcov0 := hcov κ₀
    have hK_ne : K ≠ 0 := ne_of_gt hK
    rw [hκ₀_log] at hcov0
    have hcancel :
        C₀ + K * (α * Real.sqrt (t + 1) - C₀ / K) = K * (α * Real.sqrt (t + 1)) := by
      field_simp [hK_ne]
      ring
    rw [hcancel] at hcov0
    exact hcov0
  have hcov_sq :
      (regularizedPointCovariance params.mass κ₀) ^ 2 ≤
        (K * (α * Real.sqrt (t + 1))) ^ 2 := by
    nlinarith [hcov_upper, hcov_nonneg, hmain_nonneg]
  have hmul :
      params.coupling * (6 * (regularizedPointCovariance params.mass κ₀) ^ 2 * V) ≤
        params.coupling * (6 * ((K * (α * Real.sqrt (t + 1))) ^ 2) * V) := by
    have hconst_nonneg : 0 ≤ params.coupling * (6 * V) := by
      have h6V : 0 ≤ 6 * V := by nlinarith [hV_nonneg]
      exact mul_nonneg (le_of_lt params.coupling_pos) h6V
    have hscaled := mul_le_mul_of_nonneg_left hcov_sq hconst_nonneg
    simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled
  have hsqrt_t_sq : Real.sqrt (t + 1) ^ 2 = t + 1 := by
    rw [Real.sq_sqrt ht1_nonneg]
  have htarget :
      params.coupling * (6 * ((K * (α * Real.sqrt (t + 1))) ^ 2) * V) =
        (V / (V + 1)) * (t + 1) := by
    have hsqrt_ne : Real.sqrt D ≠ 0 := by
      exact ne_of_gt (Real.sqrt_pos.mpr hD_pos)
    have hV1_ne : V + 1 ≠ 0 := by linarith [hD_pos]
    have hD_ne : D ≠ 0 := ne_of_gt hD_pos
    have hsqrt_inv_sq : (Real.sqrt D)⁻¹ ^ 2 = 1 / D := by
      field_simp [hsqrt_ne]
      rw [Real.sq_sqrt (le_of_lt hD_pos)]
    have hcancel :
        (K * ((1 / (K * Real.sqrt D)) * Real.sqrt (t + 1))) ^ 2 =
          (Real.sqrt D)⁻¹ ^ 2 * (t + 1) := by
      field_simp [ne_of_gt hK, hsqrt_ne]
      rw [Real.sq_sqrt ht1_nonneg]
    calc
      params.coupling * (6 * ((K * (α * Real.sqrt (t + 1))) ^ 2) * V)
          = params.coupling * (6 * ((Real.sqrt D)⁻¹ ^ 2 * (t + 1)) * V) := by
              dsimp [α, nelsonReferenceAlpha]
              rw [hcancel]
      _ = params.coupling * (6 * ((1 / D) * (t + 1)) * V) := by
            rw [hsqrt_inv_sq]
      _ = ((params.coupling * 6 * V) / D) * (t + 1) := by
            field_simp [hD_ne]
      _ = (V / (V + 1)) * (t + 1) := by
            dsimp [D]
            field_simp [hV1_ne, ne_of_gt params.coupling_pos]
  rw [htarget] at hmul
  have hfrac_le : V / (V + 1) ≤ 1 := by
    have hV1 : 0 < V + 1 := by linarith
    rw [div_le_iff₀ hV1]
    linarith
  nlinarith [hmul, hfrac_le]

/-- Small-cutoff variant of
`interactionCutoff_reference_cutoff_le_one_add_of_log_covariance_bound`.

If `κ` lies below the canonical reference cutoff `κ₀(t)`, the same logarithmic
covariance-growth input already forces the deterministic lower bound
`V_{Λ,κ} ≥ -(t + 1)`. Only the large-cutoff regime `κ₀(t) ≤ κ` needs the
decaying shell estimate later in Nelson's argument. -/
private theorem interactionCutoff_below_reference_cutoff_le_one_add_of_log_covariance_bound
    (params : Phi4Params) (Λ : Rectangle) {K : ℝ} (hK : 0 < K)
    {C₀ : ℝ} (_hC₀ : 0 ≤ C₀)
    (hcov :
      ∀ κ : UVCutoff,
        regularizedPointCovariance params.mass κ ≤ C₀ + K * Real.log κ.κ)
    (κ : UVCutoff) {t : ℝ} (ht : 0 ≤ t)
    (hκ_le : κ.κ ≤ (nelsonReferenceCutoff params Λ K C₀ t).κ) :
    params.coupling *
      (6 * (regularizedPointCovariance params.mass κ) ^ 2 *
        (MeasureTheory.volume Λ.toSet).toReal) ≤ t + 1 := by
  let V : ℝ := (MeasureTheory.volume Λ.toSet).toReal
  let D : ℝ := 6 * params.coupling * (V + 1)
  let α : ℝ := nelsonReferenceAlpha params Λ K
  let κ₀ : UVCutoff := nelsonReferenceCutoff params Λ K C₀ t
  have hV_nonneg : 0 ≤ V := by
    dsimp [V]
    positivity
  have hD_pos : 0 < D := by
    dsimp [D]
    have hV1 : 0 < V + 1 := by linarith
    exact mul_pos (mul_pos (by positivity) params.coupling_pos) hV1
  have hκ₀_log :
      Real.log κ₀.κ = α * Real.sqrt (t + 1) - C₀ / K := by
    dsimp [κ₀, nelsonReferenceCutoff]
    simp [α, nelsonReferenceLogShift]
  have hα_pos : 0 < α := by
    dsimp [α, nelsonReferenceAlpha]
    exact one_div_pos.mpr (mul_pos hK (Real.sqrt_pos.mpr hD_pos))
  have ht1_nonneg : 0 ≤ t + 1 := by linarith
  have hmain_nonneg : 0 ≤ K * (α * Real.sqrt (t + 1)) := by
    exact mul_nonneg hK.le (mul_nonneg hα_pos.le (Real.sqrt_nonneg _))
  have hcov_nonneg : 0 ≤ regularizedPointCovariance params.mass κ := by
    rw [regularizedPointCovariance_eq_covariance params.mass params.mass_pos κ]
    exact covariance_self_nonneg params.mass params.mass_pos (uvMollifier κ 0)
  have hlog_le : Real.log κ.κ ≤ Real.log κ₀.κ := by
    exact Real.log_le_log (by linarith [κ.hκ]) hκ_le
  have hcov_le_ref :
      regularizedPointCovariance params.mass κ ≤ K * (α * Real.sqrt (t + 1)) := by
    have hlog_scaled :
        C₀ + K * Real.log κ.κ ≤ C₀ + K * Real.log κ₀.κ := by
      nlinarith [mul_le_mul_of_nonneg_left hlog_le hK.le]
    have hcov0 : regularizedPointCovariance params.mass κ ≤ C₀ + K * Real.log κ₀.κ :=
      le_trans (hcov κ) hlog_scaled
    have hK_ne : K ≠ 0 := ne_of_gt hK
    rw [hκ₀_log] at hcov0
    have hcancel :
        C₀ + K * (α * Real.sqrt (t + 1) - C₀ / K) = K * (α * Real.sqrt (t + 1)) := by
      field_simp [hK_ne]
      ring
    rw [hcancel] at hcov0
    exact hcov0
  have hcov_sq :
      (regularizedPointCovariance params.mass κ) ^ 2 ≤
        (K * (α * Real.sqrt (t + 1))) ^ 2 := by
    nlinarith [hcov_le_ref, hcov_nonneg, hmain_nonneg]
  have hmul :
      params.coupling * (6 * (regularizedPointCovariance params.mass κ) ^ 2 * V) ≤
        params.coupling * (6 * ((K * (α * Real.sqrt (t + 1))) ^ 2) * V) := by
    have hconst_nonneg : 0 ≤ params.coupling * (6 * V) := by
      have h6V : 0 ≤ 6 * V := by nlinarith [hV_nonneg]
      exact mul_nonneg (le_of_lt params.coupling_pos) h6V
    have hscaled := mul_le_mul_of_nonneg_left hcov_sq hconst_nonneg
    simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled
  have hsqrt_t_sq : Real.sqrt (t + 1) ^ 2 = t + 1 := by
    rw [Real.sq_sqrt ht1_nonneg]
  have htarget :
      params.coupling * (6 * ((K * (α * Real.sqrt (t + 1))) ^ 2) * V) =
        (V / (V + 1)) * (t + 1) := by
    have hsqrt_ne : Real.sqrt D ≠ 0 := by
      exact ne_of_gt (Real.sqrt_pos.mpr hD_pos)
    have hV1_ne : V + 1 ≠ 0 := by linarith [hD_pos]
    have hD_ne : D ≠ 0 := ne_of_gt hD_pos
    have hsqrt_inv_sq : (Real.sqrt D)⁻¹ ^ 2 = 1 / D := by
      field_simp [hsqrt_ne]
      rw [Real.sq_sqrt (le_of_lt hD_pos)]
    have hcancel :
        (K * ((1 / (K * Real.sqrt D)) * Real.sqrt (t + 1))) ^ 2 =
          (Real.sqrt D)⁻¹ ^ 2 * (t + 1) := by
      field_simp [ne_of_gt hK, hsqrt_ne]
      rw [Real.sq_sqrt ht1_nonneg]
    calc
      params.coupling * (6 * ((K * (α * Real.sqrt (t + 1))) ^ 2) * V)
          = params.coupling * (6 * ((Real.sqrt D)⁻¹ ^ 2 * (t + 1)) * V) := by
              dsimp [α, nelsonReferenceAlpha]
              rw [hcancel]
      _ = params.coupling * (6 * ((1 / D) * (t + 1)) * V) := by
            rw [hsqrt_inv_sq]
      _ = ((params.coupling * 6 * V) / D) * (t + 1) := by
            field_simp [hD_ne]
      _ = (V / (V + 1)) * (t + 1) := by
            dsimp [D]
            field_simp [hV1_ne, ne_of_gt params.coupling_pos]
  rw [htarget] at hmul
  have hfrac_le : V / (V + 1) ≤ 1 := by
    have hV1 : 0 < V + 1 := by linarith
    rw [div_le_iff₀ hV1]
    linarith
  nlinarith [hmul, hfrac_le]

/-- Square-root factorization for the exponentially small Nelson shell scale. -/
private theorem sqrt_exponential_shell_scale
    {σ₀ β t : ℝ} (hσ₀ : 0 < σ₀) :
    Real.sqrt (σ₀ * Real.exp (-2 * β * Real.sqrt (t + 2))) =
      Real.sqrt σ₀ * Real.exp (-β * Real.sqrt (t + 2)) := by
  have hexp_sq :
      Real.exp (-2 * β * Real.sqrt (t + 2)) =
        (Real.exp (-β * Real.sqrt (t + 2))) ^ 2 := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  calc
    Real.sqrt (σ₀ * Real.exp (-2 * β * Real.sqrt (t + 2)))
        = Real.sqrt σ₀ * Real.sqrt (Real.exp (-2 * β * Real.sqrt (t + 2))) := by
            rw [Real.sqrt_mul (le_of_lt hσ₀)]
    _ = Real.sqrt σ₀ * Real.exp (-β * Real.sqrt (t + 2)) := by
          congr 1
          rw [hexp_sq, Real.sqrt_sq_eq_abs]
          exact abs_of_pos (Real.exp_pos _)

/-- Pure-analysis bridge from the Nelson shell scale
`σ₀ * exp(-2β√(t+2))` to a double-exponential exponent in `√(t+1)`. -/
private theorem exp_neg_inv_sqrt_exponential_shell_scale_le
    {M σ₀ β t : ℝ} (hM : 0 ≤ M) (hσ₀ : 0 < σ₀) (hβ : 0 < β) :
    Real.exp (-(M / Real.sqrt (σ₀ * Real.exp (-2 * β * Real.sqrt (t + 2))))) ≤
      Real.exp (-(M / Real.sqrt σ₀ * Real.exp (β * Real.sqrt (t + 1)))) := by
  have hsqrt_eq := sqrt_exponential_shell_scale (σ₀ := σ₀) (β := β) (t := t) hσ₀
  have hsqrtσ₀_ne : Real.sqrt σ₀ ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hσ₀)
  have hexp_ne : Real.exp (-(β * Real.sqrt (t + 2))) ≠ 0 := by positivity
  have hexp_mul :
      Real.exp (-(β * Real.sqrt (t + 2))) * Real.exp (β * Real.sqrt (t + 2)) = 1 := by
    rw [← Real.exp_add]
    rw [show -(β * Real.sqrt (t + 2)) + β * Real.sqrt (t + 2) = 0 by ring, Real.exp_zero]
  have hscale_eq :
      M / Real.sqrt (σ₀ * Real.exp (-2 * β * Real.sqrt (t + 2))) =
        (M / Real.sqrt σ₀) * Real.exp (β * Real.sqrt (t + 2)) := by
    rw [hsqrt_eq]
    field_simp [hsqrtσ₀_ne, hexp_ne]
    have hmul_eq :
        M * (Real.exp (-(β * Real.sqrt (t + 2))) * Real.exp (β * Real.sqrt (t + 2))) =
          M * 1 := by
      exact congrArg (fun z : ℝ => M * z) hexp_mul
    simpa [mul_assoc] using hmul_eq.symm
  have hsqrt_mono : Real.sqrt (t + 1) ≤ Real.sqrt (t + 2) := by
    apply Real.sqrt_le_sqrt
    linarith
  have hexp_mono :
      Real.exp (β * Real.sqrt (t + 1)) ≤ Real.exp (β * Real.sqrt (t + 2)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left hsqrt_mono hβ.le
  have hM_nonneg' : 0 ≤ M / Real.sqrt σ₀ := by
    exact div_nonneg hM (Real.sqrt_nonneg _)
  have hscale_ge :
      M / Real.sqrt σ₀ * Real.exp (β * Real.sqrt (t + 1)) ≤
        M / Real.sqrt (σ₀ * Real.exp (-2 * β * Real.sqrt (t + 2))) := by
    rw [hscale_eq]
    exact mul_le_mul_of_nonneg_left hexp_mono hM_nonneg'
  apply Real.exp_le_exp.mpr
  linarith

/-- Stable combined Nelson reduction with an externally supplied reference cutoff
and an explicit exponentially small shell scale.

This theorem avoids the brittle canonical-cutoff bookkeeping and packages the
usable consequence of the current Nelson infrastructure: if the shell-difference
moments are controlled at scale `σ₀ * exp(-2β√(t+2))`, then the lower tail at
level `-(t+2)` already has double-exponential decay in `√(t+1)`. -/
theorem interactionCutoff_neg_tail_of_reference_cutoff_and_exponential_shell_scale
    (params : Phi4Params) (Λ : Rectangle) (κ κ₀ : UVCutoff)
    {t C σ₀ β : ℝ}
    (hκ₀ :
      params.coupling * (6 * (regularizedPointCovariance params.mass κ₀) ^ 2 *
        (MeasureTheory.volume Λ.toSet).toReal) ≤ t + 1)
    (hC : 0 < C) (hσ₀ : 0 < σ₀) (hβ : 0 < β)
    (hmoment : ∀ j : ℕ, 0 < j →
      Integrable
        (fun ω : FieldConfig2D =>
          |interactionCutoff params Λ κ ω - interactionCutoff params Λ κ₀ ω| ^ (2 * j))
        (freeFieldMeasure params.mass params.mass_pos) ∧
      ∫ ω, |interactionCutoff params Λ κ ω - interactionCutoff params Λ κ₀ ω| ^ (2 * j)
          ∂(freeFieldMeasure params.mass params.mass_pos)
        ≤ (C * ↑j) ^ (4 * j) * (σ₀ * Real.exp (-2 * β * Real.sqrt (t + 2))) ^ (2 * j))
    (hσ_small :
      σ₀ * Real.exp (-2 * β * Real.sqrt (t + 2)) ≤ 1 / (Real.exp 1 * C) ^ 2) :
    (freeFieldMeasure params.mass params.mass_pos)
      {ω : FieldConfig2D | interactionCutoff params Λ κ ω < -(t + 2)} ≤
    ENNReal.ofReal
      (Real.exp (-(markovTailConstant C / Real.sqrt σ₀ * Real.exp (β * Real.sqrt (t + 1))))) := by
  let σ : ℝ := σ₀ * Real.exp (-2 * β * Real.sqrt (t + 2))
  have hσ_pos : 0 < σ := by
    dsimp [σ]
    exact mul_pos hσ₀ (Real.exp_pos _)
  have htail :
      (freeFieldMeasure params.mass params.mass_pos)
        {ω : FieldConfig2D | interactionCutoff params Λ κ ω < -(t + 2)} ≤
      ENNReal.ofReal (Real.exp (-(markovTailConstant C / Real.sqrt σ))) := by
    have htail' :
        (freeFieldMeasure params.mass params.mass_pos)
          {ω : FieldConfig2D | interactionCutoff params Λ κ ω < -((t + 1) + 1)} ≤
        ENNReal.ofReal (Real.exp (-(markovTailConstant C / Real.sqrt σ))) := by
      have hmoment' : ∀ j : ℕ, 0 < j →
          Integrable
            (fun ω : FieldConfig2D =>
              |interactionCutoff params Λ κ ω - interactionCutoff params Λ κ₀ ω| ^ (2 * j))
            (freeFieldMeasure params.mass params.mass_pos) ∧
          ∫ ω, |interactionCutoff params Λ κ ω - interactionCutoff params Λ κ₀ ω| ^ (2 * j)
              ∂(freeFieldMeasure params.mass params.mass_pos)
            ≤ (C * ↑j) ^ (4 * j) * σ ^ (2 * j) := by
        simpa [σ] using hmoment
      have hσ_small' : σ ≤ 1 / (Real.exp 1 * C) ^ 2 := by
        simpa [σ] using hσ_small
      exact
        interactionCutoff_neg_tail_of_reference_cutoff_and_hypercontractive_moments_explicit
          params Λ κ κ₀ (t := t + 1) (C := C) (σ := σ)
          hκ₀ hC hσ_pos hmoment' hσ_small'
    have hshift : -((t + 1) + 1 : ℝ) = -(t + 2) := by ring
    simpa [hshift] using htail'
  have hM_nonneg : 0 ≤ markovTailConstant C := by
    have hM_pos : 0 < markovTailConstant C := by
      dsimp [markovTailConstant]
      exact div_pos four_sub_log_sixteen_pos (mul_pos (Real.exp_pos 1) hC)
    exact hM_pos.le
  calc
    (freeFieldMeasure params.mass params.mass_pos)
      {ω : FieldConfig2D | interactionCutoff params Λ κ ω < -(t + 2)}
      ≤ ENNReal.ofReal (Real.exp (-(markovTailConstant C / Real.sqrt σ))) := htail
    _ ≤ ENNReal.ofReal
          (Real.exp (-(markovTailConstant C / Real.sqrt σ₀ * Real.exp (β * Real.sqrt (t + 1))))) := by
        apply ENNReal.ofReal_le_ofReal
        exact exp_neg_inv_sqrt_exponential_shell_scale_le
          (M := markovTailConstant C) hM_nonneg hσ₀ hβ

/-- Canonical Nelson reduction: logarithmic covariance growth plus an explicit
reference-shell moment bound already imply a double-exponential lower-tail
estimate for all cutoffs.

This theorem isolates the remaining Nelson-side mathematics to a single honest
input: a moment bound for the shell difference against the canonical reference
cutoff `κ₀(t)`. Once that input is proved, the cutoffwise lower tail is
finished without further bookkeeping. -/
theorem interactionCutoff_double_exponential_tail_of_log_covariance_and_reference_shell_scale
    (params : Phi4Params) (Λ : Rectangle)
    {K C₀ C σ₀ β : ℝ}
    (hK : 0 < K) (hC₀ : 0 ≤ C₀)
    (hcov :
      ∀ κ : UVCutoff,
        regularizedPointCovariance params.mass κ ≤ C₀ + K * Real.log κ.κ)
    (hC : 0 < C) (hσ₀ : 0 < σ₀) (hβ : 0 < β)
    (hmoment :
      ∀ (κ : UVCutoff) (t : ℝ), 0 ≤ t →
        (nelsonReferenceCutoff params Λ K C₀ t).κ ≤ κ.κ →
        ∀ j : ℕ, 0 < j →
        Integrable
          (fun ω : FieldConfig2D =>
            |interactionCutoff params Λ κ ω -
                interactionCutoff params Λ (nelsonReferenceCutoff params Λ K C₀ t) ω| ^ (2 * j))
          (freeFieldMeasure params.mass params.mass_pos) ∧
        ∫ ω,
            |interactionCutoff params Λ κ ω -
                interactionCutoff params Λ (nelsonReferenceCutoff params Λ K C₀ t) ω| ^ (2 * j)
            ∂(freeFieldMeasure params.mass params.mass_pos)
          ≤ (C * ↑j) ^ (4 * j) * (σ₀ * Real.exp (-2 * β * Real.sqrt (t + 2))) ^ (2 * j))
    (hσ_small :
      ∀ t : ℝ, 0 ≤ t →
        σ₀ * Real.exp (-2 * β * Real.sqrt (t + 2)) ≤ 1 / (Real.exp 1 * C) ^ 2) :
    ∃ A B Ctail : ℝ, 0 < A ∧ 0 < B ∧ 0 < Ctail ∧
      ∀ (κ : UVCutoff) (t : ℝ), 0 ≤ t →
        (freeFieldMeasure params.mass params.mass_pos)
          {ω : FieldConfig2D | interactionCutoff params Λ κ ω < -t} ≤
        ENNReal.ofReal (A * Real.exp (-B * Real.exp (Ctail * Real.sqrt t))) := by
  let B : ℝ := markovTailConstant C / Real.sqrt σ₀
  let Ctail : ℝ := β / 2
  let A : ℝ := Real.exp (B * Real.exp (Ctail * Real.sqrt 2))
  have hB_pos : 0 < B := by
    dsimp [B, markovTailConstant]
    refine div_pos ?_ (Real.sqrt_pos.mpr hσ₀)
    exact div_pos four_sub_log_sixteen_pos (mul_pos (Real.exp_pos 1) hC)
  have hCtail_pos : 0 < Ctail := by
    dsimp [Ctail]
    linarith
  have hA_pos : 0 < A := by
    dsimp [A]
    exact Real.exp_pos _
  refine ⟨A, B, Ctail, hA_pos, hB_pos, hCtail_pos, ?_⟩
  intro κ t ht
  by_cases ht_small : t ≤ 2
  · have hμ_le_one :
        (freeFieldMeasure params.mass params.mass_pos)
          {ω : FieldConfig2D | interactionCutoff params Λ κ ω < -t} ≤ 1 := by
      calc
        (freeFieldMeasure params.mass params.mass_pos)
            {ω : FieldConfig2D | interactionCutoff params Λ κ ω < -t}
          ≤ (freeFieldMeasure params.mass params.mass_pos) Set.univ := by
              apply measure_mono
              intro ω hω
              simp
        _ = 1 := by simp
    have hsqrt_le : Real.sqrt t ≤ Real.sqrt 2 := by
      apply Real.sqrt_le_sqrt
      linarith
    have hexp_le :
        Real.exp (Ctail * Real.sqrt t) ≤ Real.exp (Ctail * Real.sqrt 2) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left hsqrt_le hCtail_pos.le
    have hneg_exp_le :
        Real.exp (-B * Real.exp (Ctail * Real.sqrt 2)) ≤
          Real.exp (-B * Real.exp (Ctail * Real.sqrt t)) := by
      apply Real.exp_le_exp.mpr
      have hB_nonneg : 0 ≤ B := hB_pos.le
      nlinarith [hexp_le, hB_nonneg]
    have hone_le :
        1 ≤ A * Real.exp (-B * Real.exp (Ctail * Real.sqrt t)) := by
      have hA_nonneg : 0 ≤ A := by
        exact (Real.exp_pos _).le
      have hone_eq : A * Real.exp (-B * Real.exp (Ctail * Real.sqrt 2)) = 1 := by
        dsimp [A]
        rw [← Real.exp_add]
        have : B * Real.exp (Ctail * Real.sqrt 2) + -B * Real.exp (Ctail * Real.sqrt 2) = 0 := by ring
        rw [this, Real.exp_zero]
      calc
        1 = A * Real.exp (-B * Real.exp (Ctail * Real.sqrt 2)) := by
              rw [hone_eq]
        _ ≤ A * Real.exp (-B * Real.exp (Ctail * Real.sqrt t)) := by
              exact mul_le_mul_of_nonneg_left hneg_exp_le hA_nonneg
    calc
      (freeFieldMeasure params.mass params.mass_pos)
          {ω : FieldConfig2D | interactionCutoff params Λ κ ω < -t}
        ≤ 1 := hμ_le_one
      _ = ENNReal.ofReal (1 : ℝ) := by norm_num
      _ ≤ ENNReal.ofReal (A * Real.exp (-B * Real.exp (Ctail * Real.sqrt t))) := by
            exact ENNReal.ofReal_le_ofReal hone_le
  · have ht_gt : 2 < t := lt_of_not_ge ht_small
    let s : ℝ := t - 2
    have hs_nonneg : 0 ≤ s := by
      dsimp [s]
      linarith
    let κ₀ : UVCutoff := nelsonReferenceCutoff params Λ K C₀ s
    have htail_core :
        (freeFieldMeasure params.mass params.mass_pos)
          {ω : FieldConfig2D | interactionCutoff params Λ κ ω < -(s + 2)} ≤
        ENNReal.ofReal
          (Real.exp (-(B * Real.exp (β * Real.sqrt (s + 1))))) := by
      by_cases hκ_ge : κ₀.κ ≤ κ.κ
      · have hκ₀ :
            params.coupling *
                (6 * (regularizedPointCovariance params.mass κ₀) ^ 2 *
                  (MeasureTheory.volume Λ.toSet).toReal)
              ≤ s + 1 := by
          exact interactionCutoff_reference_cutoff_le_one_add_of_log_covariance_bound
            params Λ hK hC₀ hcov hs_nonneg
        have hmoment' : ∀ j : ℕ, 0 < j →
            Integrable
              (fun ω : FieldConfig2D =>
                |interactionCutoff params Λ κ ω - interactionCutoff params Λ κ₀ ω| ^ (2 * j))
              (freeFieldMeasure params.mass params.mass_pos) ∧
            ∫ ω,
                |interactionCutoff params Λ κ ω - interactionCutoff params Λ κ₀ ω| ^ (2 * j)
                ∂(freeFieldMeasure params.mass params.mass_pos)
              ≤ (C * ↑j) ^ (4 * j) * (σ₀ * Real.exp (-2 * β * Real.sqrt (s + 2))) ^ (2 * j) := by
          intro j hj
          simpa [κ₀, s] using hmoment κ s hs_nonneg hκ_ge j hj
        have hσ_small' :
            σ₀ * Real.exp (-2 * β * Real.sqrt (s + 2)) ≤ 1 / (Real.exp 1 * C) ^ 2 := by
          simpa [s] using hσ_small s hs_nonneg
        simpa [B, κ₀] using
          interactionCutoff_neg_tail_of_reference_cutoff_and_exponential_shell_scale
            params Λ κ κ₀ (t := s) (C := C) (σ₀ := σ₀) (β := β)
            hκ₀ hC hσ₀ hβ hmoment' hσ_small'
      · have hκ_small :
            params.coupling *
                (6 * (regularizedPointCovariance params.mass κ) ^ 2 *
                  (MeasureTheory.volume Λ.toSet).toReal)
              ≤ s + 1 := by
          exact interactionCutoff_below_reference_cutoff_le_one_add_of_log_covariance_bound
            params Λ hK hC₀ hcov κ hs_nonneg (le_of_not_ge hκ_ge)
        have hκ_small' :
            params.coupling *
                (6 * (regularizedPointCovariance params.mass κ) ^ 2 *
                  (MeasureTheory.volume Λ.toSet).toReal)
              ≤ s + 2 := by
          linarith
        have hempty :
            {ω : FieldConfig2D | interactionCutoff params Λ κ ω < -(s + 2)} = ∅ :=
          interactionCutoff_neg_tail_eq_empty params Λ κ (t := s + 2) hκ_small'
        rw [hempty]
        simp
    have hs_plus : s + 2 = t := by
      dsimp [s]
      ring
    have hsqrt_half :
        (1 / 2 : ℝ) * Real.sqrt t ≤ Real.sqrt (t - 1) := by
      have ht1_nonneg : 0 ≤ t - 1 := by linarith
      have hleft_nonneg : 0 ≤ (1 / 2 : ℝ) * Real.sqrt t := by positivity
      have hright_nonneg : 0 ≤ Real.sqrt (t - 1) := Real.sqrt_nonneg _
      have hsq :
          (((1 / 2 : ℝ) * Real.sqrt t) ^ 2) ≤ (Real.sqrt (t - 1)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt ht, Real.sq_sqrt ht1_nonneg]
        norm_num
        linarith
      nlinarith
    have hsqrt_cmp : Ctail * Real.sqrt t ≤ β * Real.sqrt (s + 1) := by
      have hmul_half : β * ((1 / 2 : ℝ) * Real.sqrt t) ≤ β * Real.sqrt (t - 1) := by
        exact mul_le_mul_of_nonneg_left hsqrt_half hβ.le
      have hs_eq : s + 1 = t - 1 := by
        dsimp [s]
        ring
      calc
        Ctail * Real.sqrt t = β * ((1 / 2 : ℝ) * Real.sqrt t) := by
          dsimp [Ctail]
          ring
        _ ≤ β * Real.sqrt (t - 1) := hmul_half
        _ = β * Real.sqrt (s + 1) := by rw [hs_eq]
    have hexp_cmp :
        Real.exp (Ctail * Real.sqrt t) ≤ Real.exp (β * Real.sqrt (s + 1)) := by
      exact Real.exp_le_exp.mpr hsqrt_cmp
    have htail_cmp :
        Real.exp (-(B * Real.exp (β * Real.sqrt (s + 1)))) ≤
          A * Real.exp (-B * Real.exp (Ctail * Real.sqrt t)) := by
      have hbase :
          Real.exp (-(B * Real.exp (β * Real.sqrt (s + 1)))) ≤
            Real.exp (-(B * Real.exp (Ctail * Real.sqrt t))) := by
        apply Real.exp_le_exp.mpr
        nlinarith [hexp_cmp, hB_pos.le]
      calc
        Real.exp (-(B * Real.exp (β * Real.sqrt (s + 1))))
          ≤ Real.exp (-(B * Real.exp (Ctail * Real.sqrt t))) := hbase
        _ ≤ A * Real.exp (-B * Real.exp (Ctail * Real.sqrt t)) := by
            have hA_ge_one : 1 ≤ A := by
              dsimp [A]
              have hA_nonneg : 0 ≤ B * Real.exp (Ctail * Real.sqrt 2) := by
                positivity
              simpa using Real.one_le_exp_iff.mpr hA_nonneg
            have hnonneg : 0 ≤ Real.exp (-B * Real.exp (Ctail * Real.sqrt t)) := by positivity
            simpa [one_mul] using mul_le_mul_of_nonneg_right hA_ge_one hnonneg
    calc
      (freeFieldMeasure params.mass params.mass_pos)
          {ω : FieldConfig2D | interactionCutoff params Λ κ ω < -t}
        = (freeFieldMeasure params.mass params.mass_pos)
            {ω : FieldConfig2D | interactionCutoff params Λ κ ω < -(s + 2)} := by
              congr 1
              ext ω
              simp only [Set.mem_setOf_eq]
              rw [hs_plus]
      _ ≤ ENNReal.ofReal (Real.exp (-(B * Real.exp (β * Real.sqrt (s + 1))))) := htail_core
      _ ≤ ENNReal.ofReal (A * Real.exp (-B * Real.exp (Ctail * Real.sqrt t))) := by
            exact ENNReal.ofReal_le_ofReal htail_cmp

/-- Fatou passage for even-moment comparison along an almost-everywhere
approximating sequence.

This is the abstract bridge needed if the Nelson moment comparison is first
proved for finite-dimensional `0/2/4` Wick cylinder approximants and then
passed to the cutoff interaction difference by approximation. The theorem is
stated directly in terms of the integrated random variable, matching the actual
frontier surface in `gap_interactionCutoff_sub_even_moment_comparison`. -/
private theorem evenMomentComparison_of_tendsto_ae
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ]
    (X : Ω → ℝ) (Y : ℕ → Ω → ℝ)
    (K : ℝ) (j : ℕ)
    (hK : 0 ≤ K)
    (h_ae : ∀ᵐ ω ∂μ, Tendsto (fun n => Y n ω) atTop (𝓝 (X ω)))
    (hY_meas : ∀ n, AEStronglyMeasurable (Y n) μ)
    (hX_meas : AEStronglyMeasurable X μ)
    (hY_int : ∀ n, Integrable (fun ω => |Y n ω| ^ (2 * j)) μ)
    (hbound : ∀ n,
      ∫ ω, |Y n ω| ^ (2 * j) ∂μ
        ≤ K * (∫ ω, (Y n ω) ^ 2 ∂μ) ^ j)
    (hL2 : Tendsto (fun n => ∫ ω, (Y n ω) ^ 2 ∂μ) atTop (𝓝 (∫ ω, (X ω) ^ 2 ∂μ))) :
    ∫ ω, |X ω| ^ (2 * j) ∂μ
      ≤ K * (∫ ω, (X ω) ^ 2 ∂μ) ^ j := by
  let F : ℕ → Ω → ℝ≥0∞ := fun n ω => ENNReal.ofReal (|Y n ω| ^ (2 * j))
  let FX : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (|X ω| ^ (2 * j))
  have hF_meas : ∀ n, AEMeasurable (F n) μ := by
    intro n
    exact ((hY_meas n).norm.pow (2 * j)).aemeasurable.ennreal_ofReal
  have hliminf_pt : FX =ᵐ[μ] fun ω => liminf (fun n => F n ω) atTop := by
    filter_upwards [h_ae] with ω hω
    have hcont : Continuous fun y : ℝ => ENNReal.ofReal (|y| ^ (2 * j : ℕ)) := by
      exact ENNReal.continuous_ofReal.comp (continuous_abs.pow (2 * j))
    have hconv : Tendsto (fun n => F n ω) atTop (𝓝 (FX ω)) := by
      simpa [F, FX] using hcont.continuousAt.tendsto.comp hω
    simpa using hconv.liminf_eq.symm
  have hfatou : ∫⁻ ω, FX ω ∂μ ≤ liminf (fun n => ∫⁻ ω, F n ω ∂μ) atTop := by
    rw [lintegral_congr_ae hliminf_pt]
    exact MeasureTheory.lintegral_liminf_le' (μ := μ) hF_meas
  have hF_int_eq : ∀ n, ∫⁻ ω, F n ω ∂μ = ENNReal.ofReal (∫ ω, |Y n ω| ^ (2 * j) ∂μ) := by
    intro n
    exact
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hY_int n)
        (Filter.Eventually.of_forall fun _ => by positivity)).symm
  have hcontK : Continuous fun x : ℝ => ENNReal.ofReal (K * x ^ j) := by
    exact ENNReal.continuous_ofReal.comp (continuous_const.mul (continuous_pow j))
  have hlimK :
      liminf (fun n => ENNReal.ofReal (K * (∫ ω, (Y n ω) ^ 2 ∂μ) ^ j)) atTop =
        ENNReal.ofReal (K * (∫ ω, (X ω) ^ 2 ∂μ) ^ j) := by
    exact (hcontK.continuousAt.tendsto.comp hL2).liminf_eq
  have hright :
      liminf (fun n => ∫⁻ ω, F n ω ∂μ) atTop ≤
        ENNReal.ofReal (K * (∫ ω, (X ω) ^ 2 ∂μ) ^ j) := by
    calc
      liminf (fun n => ∫⁻ ω, F n ω ∂μ) atTop
          ≤ liminf (fun n => ENNReal.ofReal (K * (∫ ω, (Y n ω) ^ 2 ∂μ) ^ j)) atTop := by
            apply Filter.liminf_le_liminf (hu := by isBoundedDefault) (hv := by isBoundedDefault)
            exact Filter.Eventually.of_forall fun n => by
              rw [hF_int_eq n]
              exact ENNReal.ofReal_le_ofReal (hbound n)
      _ = ENNReal.ofReal (K * (∫ ω, (X ω) ^ 2 ∂μ) ^ j) := hlimK
  have hlintegral_le :
      ∫⁻ ω, FX ω ∂μ ≤ ENNReal.ofReal (K * (∫ ω, (X ω) ^ 2 ∂μ) ^ j) :=
    le_trans hfatou hright
  have hFX_finite : ∫⁻ ω, FX ω ∂μ ≠ ∞ := by
    exact lt_of_le_of_lt hlintegral_le ENNReal.ofReal_lt_top |>.ne
  have hX_nonneg : 0 ≤ᵐ[μ] fun ω => |X ω| ^ (2 * j) :=
    Filter.Eventually.of_forall fun _ => by positivity
  have hXpow_meas : AEStronglyMeasurable (fun ω => |X ω| ^ (2 * j)) μ :=
    hX_meas.norm.pow (2 * j)
  have hX_int : Integrable (fun ω => |X ω| ^ (2 * j)) μ := by
    rw [← MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hXpow_meas hX_nonneg]
    simpa [FX] using hFX_finite
  have hX_eq : ENNReal.ofReal (∫ ω, |X ω| ^ (2 * j) ∂μ) = ∫⁻ ω, FX ω ∂μ := by
    simpa [FX] using MeasureTheory.ofReal_integral_eq_lintegral_ofReal hX_int hX_nonneg
  have hfinal_enn :
      ENNReal.ofReal (∫ ω, |X ω| ^ (2 * j) ∂μ) ≤
        ENNReal.ofReal (K * (∫ ω, (X ω) ^ 2 ∂μ) ^ j) := by
    rw [hX_eq]
    exact hlintegral_le
  exact ENNReal.ofReal_le_ofReal_iff (by positivity) |>.mp hfinal_enn

/-- Cell-anchor finite-cylinder approximant to the cutoff-interaction
difference.

This is the natural lattice object for the approximation branch: it samples the
quartic Wick integrand on each mesh cell anchor and weights by the cell area. -/
def interactionCutoffSubCellAnchorApprox
    (params : Phi4Params) (Λ : Rectangle) (L : Phi4.RectLattice Λ)
    (κ κ₀ : UVCutoff) : FieldConfig2D → ℝ :=
  finiteWickCylinder
    (a4 := fun s : (Fin L.Nt × Fin L.Nx) ⊕ (Fin L.Nt × Fin L.Nx) =>
      match s with
      | Sum.inl ij => params.coupling * (L.cell ij.1 ij.2).area
      | Sum.inr ij => -params.coupling * (L.cell ij.1 ij.2).area)
    (a2 := fun _ : (Fin L.Nt × Fin L.Nx) ⊕ (Fin L.Nt × Fin L.Nx) => 0)
    (c4 := fun s : (Fin L.Nt × Fin L.Nx) ⊕ (Fin L.Nt × Fin L.Nx) =>
      match s with
      | Sum.inl _ => regularizedPointCovariance params.mass κ
      | Sum.inr _ => regularizedPointCovariance params.mass κ₀)
    (c2 := fun _ : (Fin L.Nt × Fin L.Nx) ⊕ (Fin L.Nt × Fin L.Nx) => 0)
    (f4 := fun s : (Fin L.Nt × Fin L.Nx) ⊕ (Fin L.Nt × Fin L.Nx) =>
      match s with
      | Sum.inl ij => uvMollifier κ (L.cellAnchor ij.1 ij.2)
      | Sum.inr ij => uvMollifier κ₀ (L.cellAnchor ij.1 ij.2))
    (f2 := fun s : (Fin L.Nt × Fin L.Nx) ⊕ (Fin L.Nt × Fin L.Nx) =>
      match s with
      | Sum.inl ij => uvMollifier κ (L.cellAnchor ij.1 ij.2)
      | Sum.inr ij => uvMollifier κ₀ (L.cellAnchor ij.1 ij.2))
    0

/-- The cell-anchor approximant is a finite Wick cylinder. -/
theorem interactionCutoffSubCellAnchorApprox_isFiniteWickCylinder
    (params : Phi4Params) (Λ : Rectangle) (L : Phi4.RectLattice Λ)
    (κ κ₀ : UVCutoff) :
    IsFiniteWickCylinder (interactionCutoffSubCellAnchorApprox params Λ L κ κ₀) := by
  classical
  unfold interactionCutoffSubCellAnchorApprox
  exact finiteWickCylinder_isFinite _ _ _ _ _ _ _

/-- Canonical uniform-refinement cell-anchor approximant sequence for the cutoff
interaction difference. This is the concrete sequence intended for the
approximation frontier on the Nelson side. -/
def interactionCutoffSubUniformApprox
    (params : Phi4Params) (Λ : Rectangle) (κ κ₀ : UVCutoff) :
    ℕ → FieldConfig2D → ℝ :=
  fun n => interactionCutoffSubCellAnchorApprox params Λ (Phi4.uniformRectLattice Λ n) κ κ₀

/-- The cell-anchor approximant is exactly the anchor Riemann sum of the pointwise
quartic Wick-power difference. -/
theorem interactionCutoffSubCellAnchorApprox_eq_riemannSumCellAnchorFun
    (params : Phi4Params) (Λ : Rectangle) (L : Phi4.RectLattice Λ)
    (κ κ₀ : UVCutoff) (ω : FieldConfig2D) :
    interactionCutoffSubCellAnchorApprox params Λ L κ κ₀ ω =
      params.coupling *
        Phi4.RectLattice.riemannSumCellAnchorFun L
          (fun x => wickPower 4 params.mass κ ω x - wickPower 4 params.mass κ₀ ω x) := by
  classical
  unfold interactionCutoffSubCellAnchorApprox Phi4.RectLattice.riemannSumCellAnchorFun
    finiteWickCylinder
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [zero_mul, add_zero]
  let g : Fin L.Nt → Fin L.Nx → ℝ := fun i j =>
    (L.cell i j).area *
      ((fun x => wickPower 4 params.mass κ ω x - wickPower 4 params.mass κ₀ ω x)
        (L.cellAnchor i j))
  let A : Fin L.Nt × Fin L.Nx → ℝ := fun x =>
    params.coupling * (L.cell x.1 x.2).area *
      wickMonomial 4 (regularizedPointCovariance params.mass κ)
        (ω (uvMollifier κ (L.cellAnchor x.1 x.2)))
  let B : Fin L.Nt × Fin L.Nx → ℝ := fun x =>
    params.coupling * (L.cell x.1 x.2).area *
      wickMonomial 4 (regularizedPointCovariance params.mass κ₀)
        (ω (uvMollifier κ₀ (L.cellAnchor x.1 x.2)))
  have hprod : (∑ i : Fin L.Nt, ∑ j : Fin L.Nx, g i j) =
      ∑ p : Fin L.Nt × Fin L.Nx, g p.1 p.2 := by
    simpa [g] using (Fintype.sum_prod_type' g).symm
  have hterm : ∀ x : Fin L.Nt × Fin L.Nx, A x - B x = params.coupling * g x.1 x.2 := by
    intro x
    rcases x with ⟨i, j⟩
    simp [A, B, g, wickPower, rawFieldEval, wickMonomial_four, sub_eq_add_neg]
    ring
  have hstart :
      (∑ x : Fin L.Nt × Fin L.Nx,
          params.coupling * (L.cell x.1 x.2).area *
            wickMonomial 4 (regularizedPointCovariance params.mass κ)
              (ω (uvMollifier κ (L.cellAnchor x.1 x.2))) +
        ∑ x : Fin L.Nt × Fin L.Nx,
          -params.coupling * (L.cell x.1 x.2).area *
            wickMonomial 4 (regularizedPointCovariance params.mass κ₀)
              (ω (uvMollifier κ₀ (L.cellAnchor x.1 x.2))) +
      (∑ x : Fin L.Nt × Fin L.Nx, 0 + ∑ x : Fin L.Nt × Fin L.Nx, 0))
        = ∑ x : Fin L.Nt × Fin L.Nx, A x - ∑ x : Fin L.Nt × Fin L.Nx, B x := by
    simp [A, B, sub_eq_add_neg]
  calc
    (∑ x : Fin L.Nt × Fin L.Nx,
        params.coupling * (L.cell x.1 x.2).area *
          wickMonomial 4 (regularizedPointCovariance params.mass κ)
            (ω (uvMollifier κ (L.cellAnchor x.1 x.2))) +
      ∑ x : Fin L.Nt × Fin L.Nx,
        -params.coupling * (L.cell x.1 x.2).area *
          wickMonomial 4 (regularizedPointCovariance params.mass κ₀)
            (ω (uvMollifier κ₀ (L.cellAnchor x.1 x.2))) +
      (∑ x : Fin L.Nt × Fin L.Nx, 0 + ∑ x : Fin L.Nt × Fin L.Nx, 0))
        = ∑ x : Fin L.Nt × Fin L.Nx, A x - ∑ x : Fin L.Nt × Fin L.Nx, B x := hstart
    _ = ∑ x : Fin L.Nt × Fin L.Nx, (A x - B x) := by
      rw [← Finset.sum_sub_distrib]
    _ = ∑ x : Fin L.Nt × Fin L.Nx, params.coupling * g x.1 x.2 := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      exact hterm x
    _ = params.coupling * ∑ x : Fin L.Nt × Fin L.Nx, g x.1 x.2 := by
      rw [Finset.mul_sum]
    _ = params.coupling * (∑ i : Fin L.Nt, ∑ j : Fin L.Nx, g i j) := by
      rw [← hprod]

/-- The canonical uniform-refinement approximant is the corresponding anchor
Riemann sum of the quartic Wick-power difference. -/
theorem interactionCutoffSubUniformApprox_eq_riemannSumCellAnchorFun
    (params : Phi4Params) (Λ : Rectangle) (κ κ₀ : UVCutoff) (n : ℕ) (ω : FieldConfig2D) :
    interactionCutoffSubUniformApprox params Λ κ κ₀ n ω =
      params.coupling *
        Phi4.RectLattice.riemannSumCellAnchorFun (Phi4.uniformRectLattice Λ n)
          (fun x => wickPower 4 params.mass κ ω x - wickPower 4 params.mass κ₀ ω x) := by
  simpa [interactionCutoffSubUniformApprox] using
    interactionCutoffSubCellAnchorApprox_eq_riemannSumCellAnchorFun
      params Λ (Phi4.uniformRectLattice Λ n) κ κ₀ ω

/-- The canonical uniform approximant is the integral of the corresponding
piecewise cell-anchor approximation of the pointwise quartic Wick-power
difference. -/
theorem interactionCutoffSubUniformApprox_eq_setIntegral_cellAnchorApproxFun
    (params : Phi4Params) (Λ : Rectangle) (κ κ₀ : UVCutoff) (n : ℕ) (ω : FieldConfig2D) :
    interactionCutoffSubUniformApprox params Λ κ κ₀ n ω =
      params.coupling *
        ∫ x in Λ.toSet,
          (Phi4.uniformRectLattice Λ n).cellAnchorApproxFun
            (fun z => wickPower 4 params.mass κ ω z - wickPower 4 params.mass κ₀ ω z) x := by
  rw [interactionCutoffSubUniformApprox_eq_riemannSumCellAnchorFun]
  congr 1
  exact
    ((Phi4.uniformRectLattice Λ n).setIntegral_cellAnchorApproxFun_eq_riemannSumCellAnchorFun
      (fun z => wickPower 4 params.mass κ ω z - wickPower 4 params.mass κ₀ ω z)).symm

/-- The uniform approximant error is the integral of the mesh anchor
approximation error for the pointwise quartic Wick-power difference. -/
theorem interactionCutoffSubUniformApprox_sub_eq_setIntegral_error
    (params : Phi4Params) (Λ : Rectangle) (κ κ₀ : UVCutoff) (n : ℕ) (ω : FieldConfig2D) :
    interactionCutoffSubUniformApprox params Λ κ κ₀ n ω -
        (interactionCutoff params Λ κ ω - interactionCutoff params Λ κ₀ ω) =
      params.coupling *
        ∫ x in Λ.toSet,
          (Phi4.uniformRectLattice Λ n).cellAnchorApproxFun
              (fun z => wickPower 4 params.mass κ ω z - wickPower 4 params.mass κ₀ ω z) x
            -
            (wickPower 4 params.mass κ ω x - wickPower 4 params.mass κ₀ ω x) := by
  let d : Spacetime2D → ℝ :=
    fun x => wickPower 4 params.mass κ ω x - wickPower 4 params.mass κ₀ ω x
  have happ :
      interactionCutoffSubUniformApprox params Λ κ κ₀ n ω =
        params.coupling *
          ∫ x in Λ.toSet, (Phi4.uniformRectLattice Λ n).cellAnchorApproxFun d x := by
    simpa [d] using
      interactionCutoffSubUniformApprox_eq_setIntegral_cellAnchorApproxFun params Λ κ κ₀ n ω
  have hd_int : Integrable (fun x => d x) (volume.restrict Λ.toSet) := by
    exact
      ((wickPower_continuous_in_x 4 params.mass κ ω).sub
        (wickPower_continuous_in_x 4 params.mass κ₀ ω)).continuousOn.integrableOn_compact
        Λ.toSet_isCompact
  have happ_int :
      Integrable
        (fun x => (Phi4.uniformRectLattice Λ n).cellAnchorApproxFun d x)
        (volume.restrict Λ.toSet) := by
    exact (Phi4.uniformRectLattice Λ n).integrable_cellAnchorApproxFun d
  have htarget :
      interactionCutoff params Λ κ ω - interactionCutoff params Λ κ₀ ω =
        params.coupling * ∫ x in Λ.toSet, d x := by
    have hκ_int :
        Integrable (fun x => wickPower 4 params.mass κ ω x)
          (MeasureTheory.volume.restrict Λ.toSet) := by
      exact (wickPower_continuous_in_x 4 params.mass κ ω).continuousOn.integrableOn_compact
        Λ.toSet_isCompact
    have hκ₀_int :
        Integrable (fun x => wickPower 4 params.mass κ₀ ω x)
          (MeasureTheory.volume.restrict Λ.toSet) := by
      exact (wickPower_continuous_in_x 4 params.mass κ₀ ω).continuousOn.integrableOn_compact
        Λ.toSet_isCompact
    unfold d interactionCutoff
    rw [← mul_sub]
    congr 1
    exact (integral_sub hκ_int hκ₀_int).symm
  rw [happ, htarget, ← mul_sub]
  congr 1
  exact (integral_sub happ_int hd_int).symm

/-- Each term in the canonical uniform-refinement approximant sequence is a
finite Wick cylinder. -/
theorem interactionCutoffSubUniformApprox_isFiniteWickCylinder
    (params : Phi4Params) (Λ : Rectangle) (κ κ₀ : UVCutoff) :
    ∀ n : ℕ, IsFiniteWickCylinder (interactionCutoffSubUniformApprox params Λ κ κ₀ n) := by
  intro n
  simpa [interactionCutoffSubUniformApprox] using
    interactionCutoffSubCellAnchorApprox_isFiniteWickCylinder
      params Λ (Phi4.uniformRectLattice Λ n) κ κ₀

/-- Frontier theorem for the logarithmic growth of the regularized point
covariance.

This is the covariance-growth input needed to choose the canonical Nelson
reference cutoff `κ₀(t)`. It is separate from the shell-moment analysis: once
an additive-constant logarithmic bound `C₀ + K log κ` is available, the
deterministic part of the reference-cutoff argument is already closed by
`interactionCutoff_reference_cutoff_le_one_add_of_log_covariance_bound`. -/
theorem gap_regularizedPointCovariance_log_growth
    (params : Phi4Params) :
    ∃ K C₀ : ℝ, 0 < K ∧ 0 ≤ C₀ ∧
      ∀ κ : UVCutoff,
        regularizedPointCovariance params.mass κ ≤ C₀ + K * Real.log κ.κ := by
  obtain ⟨K, C₀, hK, hC₀, hkernel⟩ :=
    gap_uvMollifier_freeCovKernel_log_growth params.mass params.mass_pos
  refine ⟨K, C₀, hK, hC₀, ?_⟩
  intro κ
  have hrepr :
      regularizedPointCovariance params.mass κ =
        ∫ x, ∫ y, uvMollifier κ 0 x * freeCovKernel params.mass x y * uvMollifier κ 0 y := by
    rw [regularizedPointCovariance_eq_covariance params.mass params.mass_pos κ]
    simpa using gap_uvMollifier_covariance_eq_freeCovKernel params.mass params.mass_pos κ κ 0 0
  rw [hrepr]
  exact hkernel κ

/-- Frontier theorem for approximating cutoff-interaction differences by finite
Wick cylinders.

This is split along the actual canonical approximation sequence:
the uniform-refinement cell-anchor approximants. The two genuine remaining
inputs are:
1. almost-everywhere convergence of the canonical sequence,
2. convergence of its second moments. -/
theorem gap_interactionCutoffSubUniformApprox_tendsto_ae
    (params : Phi4Params) (Λ : Rectangle) (κ κ₀ : UVCutoff) :
    ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
      Tendsto
        (fun n : ℕ => interactionCutoffSubUniformApprox params Λ κ κ₀ n ω) atTop
        (𝓝 (interactionCutoff params Λ κ ω - interactionCutoff params Λ κ₀ ω)) := by
  refine ae_of_all _ ?_
  intro ω
  let d : Spacetime2D → ℝ :=
    fun x => wickPower 4 params.mass κ ω x - wickPower 4 params.mass κ₀ ω x
  have hcont : ContinuousOn d Λ.toSet := by
    exact
      ((wickPower_continuous_in_x 4 params.mass κ ω).sub
        (wickPower_continuous_in_x 4 params.mass κ₀ ω)).continuousOn
  have hint : IntegrableOn d Λ.toSet volume := by
    exact hcont.integrableOn_compact Λ.toSet_isCompact
  have hriemann :
      Filter.Tendsto
        (fun n : ℕ => (Phi4.uniformRectLattice Λ n).riemannSumCellAnchorFun d)
        Filter.atTop
        (nhds (∫ x in Λ.toSet, d x)) := by
    exact
      Phi4.tendsto_riemannSumCellAnchorFun_of_continuousOn
        Λ Λ.toSet_isCompact hcont hint
  have happ :
      Filter.Tendsto
        (fun n : ℕ => interactionCutoffSubUniformApprox params Λ κ κ₀ n ω)
        Filter.atTop
        (nhds (params.coupling * ∫ x in Λ.toSet, d x)) := by
    simpa [interactionCutoffSubUniformApprox_eq_riemannSumCellAnchorFun, d] using
      hriemann.const_mul params.coupling
  have hκ_int : Integrable (fun x => wickPower 4 params.mass κ ω x) (volume.restrict Λ.toSet) := by
    exact (wickPower_continuous_in_x 4 params.mass κ ω).continuousOn.integrableOn_compact
      Λ.toSet_isCompact
  have hκ₀_int : Integrable (fun x => wickPower 4 params.mass κ₀ ω x) (volume.restrict Λ.toSet) := by
    exact (wickPower_continuous_in_x 4 params.mass κ₀ ω).continuousOn.integrableOn_compact
      Λ.toSet_isCompact
  have htarget :
      params.coupling * ∫ x in Λ.toSet, d x =
        interactionCutoff params Λ κ ω - interactionCutoff params Λ κ₀ ω := by
    unfold d interactionCutoff
    rw [← mul_sub, integral_sub hκ_int hκ₀_int]
  simpa [htarget] using happ

/-- For a fixed cutoff, the two-point second moment of the quartic Wick-power
difference is continuous in the spacetime pair `(y, x)`. -/
private theorem continuous_wickPower_sq_diff_expectation
    (mass : ℝ) (hmass : 0 < mass) (κ : UVCutoff) :
    Continuous fun p : Spacetime2D × Spacetime2D =>
      ∫ ω : FieldConfig2D,
        (wickPower 4 mass κ ω p.1 - wickPower 4 mass κ ω p.2) ^ 2
          ∂(freeFieldMeasure mass hmass) := by
  let T := freeCovarianceCLM mass hmass
  let c := regularizedPointCovariance mass κ
  let cov11 : Spacetime2D × Spacetime2D → ℝ := fun p =>
    GaussianField.covariance T (uvMollifier κ p.1) (uvMollifier κ p.1)
  let cov22 : Spacetime2D × Spacetime2D → ℝ := fun p =>
    GaussianField.covariance T (uvMollifier κ p.2) (uvMollifier κ p.2)
  let cov12 : Spacetime2D × Spacetime2D → ℝ := fun p =>
    GaussianField.covariance T (uvMollifier κ p.2) (uvMollifier κ p.1)
  have huv_fst : Continuous fun p : Spacetime2D × Spacetime2D => uvMollifier κ p.1 :=
    (gap_uvMollifier_continuous κ).comp continuous_fst
  have huv_snd : Continuous fun p : Spacetime2D × Spacetime2D => uvMollifier κ p.2 :=
    (gap_uvMollifier_continuous κ).comp continuous_snd
  have hcov11 : Continuous cov11 := by
    simpa [cov11, GaussianField.covariance] using (T.continuous.comp huv_fst).inner
      (T.continuous.comp huv_fst)
  have hcov22 : Continuous cov22 := by
    simpa [cov22, GaussianField.covariance] using (T.continuous.comp huv_snd).inner
      (T.continuous.comp huv_snd)
  have hcov12 : Continuous cov12 := by
    simpa [cov12, GaussianField.covariance] using (T.continuous.comp huv_snd).inner
      (T.continuous.comp huv_fst)
  let P : Spacetime2D × Spacetime2D → ℝ := fun p =>
      105 * (cov11 p) ^ 4
        - 180 * c * (cov11 p) ^ 3
        + 108 * c ^ 2 * (cov11 p) ^ 2
        + 105 * (cov22 p) ^ 4
        - 180 * c * (cov22 p) ^ 3
        + 108 * c ^ 2 * (cov22 p) ^ 2
        - 18 * (cov22 p) ^ 2 * (cov11 p) ^ 2
        - 144 * cov22 p * cov11 p * (cov12 p) ^ 2
        - 48 * (cov12 p) ^ 4
        + 36 * c * cov22 p * (cov11 p) ^ 2
        + 36 * c * (cov22 p) ^ 2 * cov11 p
        + 144 * c * cov11 p * (cov12 p) ^ 2
        + 144 * c * cov22 p * (cov12 p) ^ 2
        - 72 * c ^ 2 * cov22 p * cov11 p
        - 144 * c ^ 2 * (cov12 p) ^ 2
  have hP : Continuous P := by
    dsimp [P]
    continuity
  convert hP using 1
  ext p
  simpa [P, cov11, cov22, cov12, T, c, wickPower, rawFieldEval] using
    (wickMonomial_four_diff_sq_expectation mass hmass
      (uvMollifier κ p.2) (uvMollifier κ p.1) c)

/-- On sufficiently fine uniform meshes, the quartic Wick-power second-moment
increment between a point and its cell anchor is uniformly small over the whole
rectangle. -/
private theorem eventually_uniform_wickPower_sq_diff_expectation_lt
    (Λ : Rectangle) (mass : ℝ) (hmass : 0 < mass) (κ : UVCutoff)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N,
      ∀ (i : Fin (Phi4.uniformRectLattice Λ n).Nt) (j : Fin (Phi4.uniformRectLattice Λ n).Nx)
        {x : Spacetime2D},
        x ∈ ((Phi4.uniformRectLattice Λ n).cell i j).toSet →
        ∫ ω : FieldConfig2D,
          (wickPower 4 mass κ ω ((Phi4.uniformRectLattice Λ n).cellAnchor i j) -
            wickPower 4 mass κ ω x) ^ 2
          ∂(freeFieldMeasure mass hmass) < ε := by
  let F : Spacetime2D × Spacetime2D → ℝ := fun p =>
    ∫ ω : FieldConfig2D,
      (wickPower 4 mass κ ω p.1 - wickPower 4 mass κ ω p.2) ^ 2
        ∂(freeFieldMeasure mass hmass)
  have hF_cont : Continuous F := continuous_wickPower_sq_diff_expectation mass hmass κ
  have huc : UniformContinuousOn F (Λ.toSet ×ˢ Λ.toSet) := by
    exact (Λ.toSet_isCompact.prod Λ.toSet_isCompact).uniformContinuousOn_of_continuous
      hF_cont.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  rcases huc ε hε with ⟨δ, hδpos, hδ⟩
  have hstep :
      Filter.Tendsto
        (fun n : ℕ =>
          (Phi4.uniformRectLattice Λ n).timeStep + (Phi4.uniformRectLattice Λ n).spaceStep)
        Filter.atTop (nhds 0) := by
    simpa [zero_add] using
      (Phi4.tendsto_uniformRectLattice_timeStep Λ).add
        (Phi4.tendsto_uniformRectLattice_spaceStep Λ)
  have hsmall : ∀ᶠ n : ℕ in Filter.atTop,
      (Phi4.uniformRectLattice Λ n).timeStep + (Phi4.uniformRectLattice Λ n).spaceStep < δ :=
    hstep (Iio_mem_nhds hδpos)
  rcases Filter.eventually_atTop.mp hsmall with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn i j x hx
  have hxΛ : x ∈ Λ.toSet :=
    Phi4.RectLattice.cell_subset_rect (L := Phi4.uniformRectLattice Λ n) i j hx
  have haΛ : (Phi4.uniformRectLattice Λ n).cellAnchor i j ∈ Λ.toSet :=
    Phi4.RectLattice.cell_subset_rect (L := Phi4.uniformRectLattice Λ n) i j
      ((Phi4.uniformRectLattice Λ n).cellAnchor_mem_cell i j)
  have hdist : dist ((Phi4.uniformRectLattice Λ n).cellAnchor i j) x < δ := by
    have hle :=
      Phi4.RectLattice.dist_cellAnchor_le_timeStep_add_spaceStep
        (L := Phi4.uniformRectLattice Λ n) (i := i) (j := j) hx
    rw [dist_comm] at hle
    exact lt_of_le_of_lt hle (hN n hn)
  have hclose :
      dist
        (F ((Phi4.uniformRectLattice Λ n).cellAnchor i j, x))
        (F (x, x)) < ε := by
    apply hδ
    · exact ⟨haΛ, hxΛ⟩
    · exact ⟨hxΛ, hxΛ⟩
    · simpa [Prod.dist_eq] using hdist
  have hdiag : F (x, x) = 0 := by
    simp [F]
  have hnonneg : 0 ≤ F ((Phi4.uniformRectLattice Λ n).cellAnchor i j, x) := by
    exact integral_nonneg (fun _ => sq_nonneg _)
  rw [Real.dist_eq, hdiag, sub_zero, abs_of_nonneg hnonneg] at hclose
  simpa [F] using hclose

/-- On sufficiently fine uniform meshes, the pointwise second moment of the
full cutoff-difference error between a point and its cell anchor is uniformly
small over the whole rectangle. -/
private theorem eventually_uniform_wickPowerSub_sq_expectation_lt
    (params : Phi4Params) (Λ : Rectangle) (κ κ₀ : UVCutoff)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N,
      ∀ (i : Fin (Phi4.uniformRectLattice Λ n).Nt) (j : Fin (Phi4.uniformRectLattice Λ n).Nx)
        {x : Spacetime2D},
        x ∈ ((Phi4.uniformRectLattice Λ n).cell i j).toSet →
        ∫ ω : FieldConfig2D,
          (((wickPower 4 params.mass κ ω ((Phi4.uniformRectLattice Λ n).cellAnchor i j) -
              wickPower 4 params.mass κ₀ ω ((Phi4.uniformRectLattice Λ n).cellAnchor i j)) -
            (wickPower 4 params.mass κ ω x - wickPower 4 params.mass κ₀ ω x)) ^ 2)
            ∂(freeFieldMeasure params.mass params.mass_pos) < ε := by
  let η : ℝ := ε / 4
  have hη : 0 < η := by
    unfold η
    linarith
  rcases eventually_uniform_wickPower_sq_diff_expectation_lt
      Λ params.mass params.mass_pos κ hη with ⟨Nκ, hNκ⟩
  rcases eventually_uniform_wickPower_sq_diff_expectation_lt
      Λ params.mass params.mass_pos κ₀ hη with ⟨Nκ₀, hNκ₀⟩
  refine ⟨max Nκ Nκ₀, ?_⟩
  intro n hn i j x hx
  have hnκ : Nκ ≤ n := le_trans (le_max_left _ _) hn
  have hnκ₀ : Nκ₀ ≤ n := le_trans (le_max_right _ _) hn
  let μ : Measure FieldConfig2D := freeFieldMeasure params.mass params.mass_pos
  let a : Spacetime2D := (Phi4.uniformRectLattice Λ n).cellAnchor i j
  let A : FieldConfig2D → ℝ := fun ω =>
    wickPower 4 params.mass κ ω a - wickPower 4 params.mass κ ω x
  let B : FieldConfig2D → ℝ := fun ω =>
    wickPower 4 params.mass κ₀ ω a - wickPower 4 params.mass κ₀ ω x
  have hA_mem : MemLp A 2 μ := by
    simpa [A, μ] using
      (wickPower_memLp 4 params.mass params.mass_pos κ a
        (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).sub
      (wickPower_memLp 4 params.mass params.mass_pos κ x
        (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
  have hB_mem : MemLp B 2 μ := by
    simpa [B, μ] using
      (wickPower_memLp 4 params.mass params.mass_pos κ₀ a
        (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).sub
      (wickPower_memLp 4 params.mass params.mass_pos κ₀ x
        (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
  have hleft_int : Integrable (fun ω => (A ω - B ω) ^ 2) μ := by
    simpa [μ] using (hA_mem.sub hB_mem).integrable_sq
  have hA_int : Integrable (fun ω => (A ω) ^ 2) μ := by
    simpa [μ] using hA_mem.integrable_sq
  have hB_int : Integrable (fun ω => (B ω) ^ 2) μ := by
    simpa [μ] using hB_mem.integrable_sq
  have hright_int : Integrable (fun ω => 2 * (A ω) ^ 2 + 2 * (B ω) ^ 2) μ := by
    exact (hA_int.const_mul 2).add (hB_int.const_mul 2)
  have htarget_eq :
      (∫ ω : FieldConfig2D,
          (((wickPower 4 params.mass κ ω a -
              wickPower 4 params.mass κ₀ ω a) -
            (wickPower 4 params.mass κ ω x - wickPower 4 params.mass κ₀ ω x)) ^ 2) ∂μ)
        =
      ∫ ω : FieldConfig2D, (A ω - B ω) ^ 2 ∂μ := by
    congr 1
    ext ω
    simp [A, B]
    ring
  have hmono :
      ∫ ω : FieldConfig2D, (A ω - B ω) ^ 2 ∂μ
        ≤ ∫ ω : FieldConfig2D, 2 * (A ω) ^ 2 + 2 * (B ω) ^ 2 ∂μ := by
    refine integral_mono_ae hleft_int hright_int ?_
    filter_upwards with ω
    have hsq : 0 ≤ (A ω + B ω) ^ 2 := sq_nonneg (A ω + B ω)
    nlinarith
  have hA_lt :
      ∫ ω : FieldConfig2D, (A ω) ^ 2 ∂μ < η := by
    simpa [A, a] using hNκ n hnκ i j hx
  have hB_lt :
      ∫ ω : FieldConfig2D, (B ω) ^ 2 ∂μ < η := by
    simpa [B, a] using hNκ₀ n hnκ₀ i j hx
  calc
    ∫ ω : FieldConfig2D,
        (((wickPower 4 params.mass κ ω a -
            wickPower 4 params.mass κ₀ ω a) -
          (wickPower 4 params.mass κ ω x - wickPower 4 params.mass κ₀ ω x)) ^ 2) ∂μ
        = ∫ ω : FieldConfig2D, (A ω - B ω) ^ 2 ∂μ := htarget_eq
    _ 
      ≤ ∫ ω : FieldConfig2D, 2 * (A ω) ^ 2 + 2 * (B ω) ^ 2 ∂μ := hmono
    _ = 2 * ∫ ω : FieldConfig2D, (A ω) ^ 2 ∂μ +
          2 * ∫ ω : FieldConfig2D, (B ω) ^ 2 ∂μ := by
          rw [integral_add (hA_int.const_mul 2) (hB_int.const_mul 2),
            integral_const_mul, integral_const_mul]
    _ < 2 * η + 2 * η := by
          gcongr
    _ = ε := by
          unfold η
          ring

/-- Spatial bridge from the pointwise uniform-approximant error to the `L²`
error of the cutoff-interaction difference. This is the Nelson-side analogue of
the shell bridge in `ShellEstimates`: all Cauchy-Schwarz/Fubini bookkeeping is
handled here, leaving only the genuinely small pointwise second-moment error as
input. -/
private theorem interactionCutoffSubUniformApprox_sub_sq_le_spatialIntegral
    (params : Phi4Params) (Λ : Rectangle) (κ κ₀ : UVCutoff) (n : ℕ)
    (hprod :
      Integrable
        (fun p : FieldConfig2D × Spacetime2D =>
          (((Phi4.uniformRectLattice Λ n).cellAnchorApproxFun
                (fun z => wickPower 4 params.mass κ p.1 z -
                  wickPower 4 params.mass κ₀ p.1 z) p.2) -
            (wickPower 4 params.mass κ p.1 p.2 -
              wickPower 4 params.mass κ₀ p.1 p.2)) ^ 2)
        ((freeFieldMeasure params.mass params.mass_pos).prod
          (MeasureTheory.volume.restrict Λ.toSet))) :
    ∫ ω,
        (interactionCutoffSubUniformApprox params Λ κ κ₀ n ω -
          (interactionCutoff params Λ κ ω - interactionCutoff params Λ κ₀ ω)) ^ 2
        ∂(freeFieldMeasure params.mass params.mass_pos)
      ≤
        params.coupling ^ 2 * (MeasureTheory.volume Λ.toSet).toReal *
          ∫ x in Λ.toSet,
            ∫ ω : FieldConfig2D,
              (((Phi4.uniformRectLattice Λ n).cellAnchorApproxFun
                  (fun z => wickPower 4 params.mass κ ω z -
                    wickPower 4 params.mass κ₀ ω z) x) -
                (wickPower 4 params.mass κ ω x -
                  wickPower 4 params.mass κ₀ ω x)) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos) := by
  let μ : Measure FieldConfig2D := freeFieldMeasure params.mass params.mass_pos
  let ν : Measure Spacetime2D := MeasureTheory.volume.restrict Λ.toSet
  let L := Phi4.uniformRectLattice Λ n
  let X : FieldConfig2D → ℝ :=
    fun ω => interactionCutoff params Λ κ ω - interactionCutoff params Λ κ₀ ω
  let d : FieldConfig2D → Spacetime2D → ℝ :=
    fun ω x => wickPower 4 params.mass κ ω x - wickPower 4 params.mass κ₀ ω x
  let e : FieldConfig2D → Spacetime2D → ℝ :=
    fun ω x => L.cellAnchorApproxFun (d ω) x - d ω x
  have houter : Integrable (fun ω => ∫ x, (e ω x) ^ 2 ∂ν) μ := by
    simpa [μ, ν, e, d, L] using hprod.integral_prod_left
  have hnonneg :
      0 ≤ᵐ[μ] fun ω : FieldConfig2D => (interactionCutoffSubUniformApprox params Λ κ κ₀ n ω - X ω) ^ 2 :=
    Filter.Eventually.of_forall fun _ => sq_nonneg _
  have hpoint :
      ∀ᵐ ω ∂μ,
        (interactionCutoffSubUniformApprox params Λ κ κ₀ n ω - X ω) ^ 2 ≤
          (params.coupling ^ 2 * (MeasureTheory.volume Λ.toSet).toReal) *
            ∫ x, (e ω x) ^ 2 ∂ν := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    have happ_int : Integrable (fun x => L.cellAnchorApproxFun (d ω) x) ν := by
      simpa [ν, d, L] using L.integrable_cellAnchorApproxFun (d ω)
    have hd_int : Integrable (fun x => d ω x) ν := by
      exact
        ((wickPower_continuous_in_x 4 params.mass κ ω).sub
          (wickPower_continuous_in_x 4 params.mass κ₀ ω)).continuousOn.integrableOn_compact
          Λ.toSet_isCompact
    have happ_sq_int : Integrable (fun x => (L.cellAnchorApproxFun (d ω) x) ^ 2) ν := by
      simpa [ν, d, L, Phi4.RectLattice.sq_cellAnchorApproxFun] using
        L.integrable_cellAnchorApproxFun (fun z => (d ω z) ^ 2)
    have hd_sq_int : Integrable (fun x => (d ω x) ^ 2) ν := by
      exact
        (((wickPower_continuous_in_x 4 params.mass κ ω).sub
          (wickPower_continuous_in_x 4 params.mass κ₀ ω)).pow 2).continuousOn.integrableOn_compact
          Λ.toSet_isCompact
    have he_int : Integrable (fun x => e ω x) ν := happ_int.sub hd_int
    have he_sq_int : Integrable (fun x => (e ω x) ^ 2) ν := by
      have hsum :
          Integrable
            (fun x => 2 * ((L.cellAnchorApproxFun (d ω) x) ^ 2 + (d ω x) ^ 2)) ν := by
        exact (happ_sq_int.add hd_sq_int).const_mul 2
      have he_meas : AEStronglyMeasurable (fun x => (e ω x) ^ 2) ν := by
        exact (he_int.aestronglyMeasurable.pow 2)
      refine hsum.mono he_meas ?_
      filter_upwards with x
      rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg (by positivity)]
      nlinarith [sq_nonneg (L.cellAnchorApproxFun (d ω) x + d ω x)]
    have hsub :
        interactionCutoffSubUniformApprox params Λ κ κ₀ n ω - X ω =
          params.coupling * ∫ x in Λ.toSet, e ω x := by
      simpa [X, d, e, L] using
        interactionCutoffSubUniformApprox_sub_eq_setIntegral_error params Λ κ κ₀ n ω
    calc
      (interactionCutoffSubUniformApprox params Λ κ κ₀ n ω - X ω) ^ 2
          = params.coupling ^ 2 * (∫ x in Λ.toSet, e ω x) ^ 2 := by
              rw [hsub, mul_pow]
      _ ≤ params.coupling ^ 2 *
            ((MeasureTheory.volume Λ.toSet).toReal * ∫ x in Λ.toSet, (e ω x) ^ 2) := by
              gcongr
              exact sq_setIntegral_le_volume_mul_setIntegral_sq
                Λ.toSet Λ.toSet_measurableSet he_int he_sq_int Λ.toSet_volume_ne_top
      _ = (params.coupling ^ 2 * (MeasureTheory.volume Λ.toSet).toReal) *
            ∫ x, (e ω x) ^ 2 ∂ν := by
              rw [mul_assoc]
  have hle :=
    integral_mono_of_nonneg hnonneg (houter.const_mul _) hpoint
  calc
    ∫ ω,
        (interactionCutoffSubUniformApprox params Λ κ κ₀ n ω - X ω) ^ 2 ∂μ
      ≤ ∫ ω,
          (params.coupling ^ 2 * (MeasureTheory.volume Λ.toSet).toReal) *
            ∫ x, (e ω x) ^ 2 ∂ν ∂μ := hle
    _ = (params.coupling ^ 2 * (MeasureTheory.volume Λ.toSet).toReal) *
          ∫ ω, ∫ x, (e ω x) ^ 2 ∂ν ∂μ := by
            rw [integral_const_mul]
    _ = (params.coupling ^ 2 * (MeasureTheory.volume Λ.toSet).toReal) *
          ∫ x, ∫ ω, (e ω x) ^ 2 ∂μ ∂ν := by
            congr 1
            rw [← MeasureTheory.integral_prod_symm
              (f := fun p : FieldConfig2D × Spacetime2D => (e p.1 p.2) ^ 2) hprod]
            rw [MeasureTheory.integral_prod
              (f := fun p : FieldConfig2D × Spacetime2D => (e p.1 p.2) ^ 2) hprod]
    _ = params.coupling ^ 2 * (MeasureTheory.volume Λ.toSet).toReal *
          ∫ x in Λ.toSet,
            ∫ ω, (e ω x) ^ 2 ∂μ := by
            rfl

/-- Frontier theorem for `L²` convergence of the canonical uniform-refinement
cell-anchor approximants to the cutoff-interaction difference. -/
theorem gap_interactionCutoffSubUniformApprox_L2
    (params : Phi4Params) (Λ : Rectangle) (κ κ₀ : UVCutoff) :
    Tendsto
      (fun n : ℕ =>
        ∫ ω, (interactionCutoffSubUniformApprox params Λ κ κ₀ n ω) ^ 2
          ∂(freeFieldMeasure params.mass params.mass_pos))
      atTop
      (𝓝
        (∫ ω,
            (interactionCutoff params Λ κ ω - interactionCutoff params Λ κ₀ ω) ^ 2
          ∂(freeFieldMeasure params.mass params.mass_pos))) := by
  let μ : Measure FieldConfig2D := freeFieldMeasure params.mass params.mass_pos
  let ν : Measure Spacetime2D := MeasureTheory.volume.restrict Λ.toSet
  let X : FieldConfig2D → ℝ :=
    fun ω => interactionCutoff params Λ κ ω - interactionCutoff params Λ κ₀ ω
  let Z : ℕ → FieldConfig2D → ℝ := interactionCutoffSubUniformApprox params Λ κ κ₀
  let D : ℕ → FieldConfig2D → ℝ := fun n ω => Z n ω - X ω
  have hX_mem : MemLp X 2 μ := by
    simpa [X, μ] using
      (interactionCutoff_memLp_two params Λ κ).sub
        (interactionCutoff_memLp_two params Λ κ₀)
  have hZ_mem : ∀ n : ℕ, MemLp (Z n) 2 μ := by
    intro n
    simpa [Z, μ] using
      (interactionCutoffSubUniformApprox_isFiniteWickCylinder params Λ κ κ₀ n).memLp
        params.mass params.mass_pos (p := (2 : ℝ≥0∞)) (by norm_num)
  have hD_mem : ∀ n : ℕ, MemLp (D n) 2 μ := by
    intro n
    exact (hZ_mem n).sub hX_mem
  have hD_meas : ∀ n : ℕ, AEStronglyMeasurable (D n) μ := by
    intro n
    exact (hD_mem n).aestronglyMeasurable
  have hD_sq_tendsto_zero :
      Tendsto (fun n : ℕ => ∫ ω, (D n ω) ^ 2 ∂μ) atTop (𝓝 0) := by
    refine Metric.tendsto_atTop.2 ?_
    intro ε hε
    let V : ℝ := (MeasureTheory.volume Λ.toSet).toReal
    let A : ℝ := params.coupling ^ 2 * V ^ 2
    let η : ℝ := ε / (A + 1)
    have hη : 0 < η := by
      unfold η A
      positivity
    rcases eventually_uniform_wickPowerSub_sq_expectation_lt params Λ κ κ₀ hη with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    let L := Phi4.uniformRectLattice Λ n
    let d : FieldConfig2D → Spacetime2D → ℝ :=
      fun ω x => wickPower 4 params.mass κ ω x - wickPower 4 params.mass κ₀ ω x
    let e : FieldConfig2D → Spacetime2D → ℝ :=
      fun ω x => L.cellAnchorApproxFun (d ω) x - d ω x
    have hd_sm : StronglyMeasurable (Function.uncurry d) := by
      simpa [d] using
        (wickPower_stronglyMeasurable_uncurry 4 params.mass κ).sub
          (wickPower_stronglyMeasurable_uncurry 4 params.mass κ₀)
    have he_sq_meas : AEStronglyMeasurable
        (fun p : FieldConfig2D × Spacetime2D => (e p.1 p.2) ^ 2) (μ.prod ν) := by
      have happ_sm :
          StronglyMeasurable
            (fun p : FieldConfig2D × Spacetime2D => L.cellAnchorApproxFun (d p.1) p.2) := by
        simpa [L, d] using
          (Phi4.RectLattice.stronglyMeasurable_cellAnchorApproxFun_uncurry
            (L := L) (f := d) hd_sm)
      exact ((happ_sm.sub hd_sm).pow 2).aestronglyMeasurable
    have hioc_ae : ∀ᵐ x ∂ν, x ∈ Phi4.Rectangle.iocSet Λ := by
      change ∀ᵐ x ∂(MeasureTheory.volume.restrict Λ.toSet),
        x ∈ Phi4.Rectangle.iocSet Λ
      rw [MeasureTheory.ae_restrict_iff' Λ.toSet_measurableSet]
      filter_upwards [Phi4.Rectangle.iocSet_ae_eq_toSet Λ] with x hx hxΛ
      exact hx.mpr hxΛ
    have hpartial_lt : ∀ᵐ x ∂ν, ∫ ω, (e ω x) ^ 2 ∂μ < η := by
      filter_upwards [hioc_ae] with x hx_ioc
      have hx_union : x ∈ ⋃ p : Fin L.Nt × Fin L.Nx, L.cellIocSet p.1 p.2 := by
        simpa [L.iUnion_cellIocSet_eq_iocSet] using hx_ioc
      rcases Set.mem_iUnion.mp hx_union with p
      rcases p with ⟨⟨i, j⟩, hx_cell_ioc⟩
      have hx_cell : x ∈ (L.cell i j).toSet := by
        rcases hx_cell_ioc with ⟨htmin, htmax, hsmin, hsmax⟩
        exact ⟨le_of_lt htmin, htmax, le_of_lt hsmin, hsmax⟩
      let a : Spacetime2D := L.cellAnchor i j
      have hcell_eq :
          ∀ ω : FieldConfig2D,
            e ω x =
              ((wickPower 4 params.mass κ ω a - wickPower 4 params.mass κ₀ ω a) -
                (wickPower 4 params.mass κ ω x - wickPower 4 params.mass κ₀ ω x)) := by
        intro ω
        have hanchor :
            L.cellAnchorApproxFun (d ω) x = d ω a := by
          simpa [d, a] using
            (Phi4.RectLattice.cellAnchorApproxFun_eq_of_mem_cellIocSet
              (L := L) (f := d ω) hx_cell_ioc)
        calc
          e ω x = L.cellAnchorApproxFun (d ω) x - d ω x := by rfl
          _ = d ω a - d ω x := by rw [hanchor]
          _ = ((wickPower 4 params.mass κ ω a - wickPower 4 params.mass κ₀ ω a) -
                (wickPower 4 params.mass κ ω x - wickPower 4 params.mass κ₀ ω x)) := by
                rfl
      have hint_eq :
          ∫ ω, (e ω x) ^ 2 ∂μ =
            ∫ ω,
              (((wickPower 4 params.mass κ ω a - wickPower 4 params.mass κ₀ ω a) -
                (wickPower 4 params.mass κ ω x - wickPower 4 params.mass κ₀ ω x)) ^ 2) ∂μ := by
        refine integral_congr_ae ?_
        exact Filter.Eventually.of_forall (fun ω => by simp [hcell_eq ω])
      simpa [hint_eq, a] using hN n hn i j hx_cell
    have hprod : Integrable (fun p : FieldConfig2D × Spacetime2D => (e p.1 p.2) ^ 2) (μ.prod ν) := by
      rw [MeasureTheory.integrable_prod_iff' he_sq_meas]
      constructor
      · filter_upwards [hioc_ae] with x hx_ioc
        have hx_union : x ∈ ⋃ p : Fin L.Nt × Fin L.Nx, L.cellIocSet p.1 p.2 := by
          simpa [L.iUnion_cellIocSet_eq_iocSet] using hx_ioc
        rcases Set.mem_iUnion.mp hx_union with p
        rcases p with ⟨⟨i, j⟩, hx_cell_ioc⟩
        let a : Spacetime2D := L.cellAnchor i j
        have hcell_eq : ∀ ω : FieldConfig2D, e ω x =
            ((wickPower 4 params.mass κ ω a - wickPower 4 params.mass κ₀ ω a) -
              (wickPower 4 params.mass κ ω x - wickPower 4 params.mass κ₀ ω x)) := by
          intro ω
          have hanchor :
              L.cellAnchorApproxFun (d ω) x = d ω a := by
            simpa [d, a] using
              (Phi4.RectLattice.cellAnchorApproxFun_eq_of_mem_cellIocSet
                (L := L) (f := d ω) hx_cell_ioc)
          calc
            e ω x = L.cellAnchorApproxFun (d ω) x - d ω x := by rfl
            _ = d ω a - d ω x := by rw [hanchor]
            _ = ((wickPower 4 params.mass κ ω a - wickPower 4 params.mass κ₀ ω a) -
                  (wickPower 4 params.mass κ ω x - wickPower 4 params.mass κ₀ ω x)) := by
                    rfl
        have hA_mem :
            MemLp (fun ω : FieldConfig2D =>
                wickPower 4 params.mass κ ω a - wickPower 4 params.mass κ₀ ω a) 2 μ := by
          simpa [μ, a] using
            (wickPower_memLp 4 params.mass params.mass_pos κ a
              (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).sub
            (wickPower_memLp 4 params.mass params.mass_pos κ₀ a
              (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
        have hB_mem :
            MemLp (fun ω : FieldConfig2D =>
                wickPower 4 params.mass κ ω x - wickPower 4 params.mass κ₀ ω x) 2 μ := by
          simpa [μ] using
            (wickPower_memLp 4 params.mass params.mass_pos κ x
              (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).sub
            (wickPower_memLp 4 params.mass params.mass_pos κ₀ x
              (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
        have he_mem : MemLp (fun ω : FieldConfig2D => e ω x) 2 μ := by
          rw [show (fun ω : FieldConfig2D => e ω x) =
              (fun ω : FieldConfig2D =>
                (wickPower 4 params.mass κ ω a - wickPower 4 params.mass κ₀ ω a) -
                  (wickPower 4 params.mass κ ω x - wickPower 4 params.mass κ₀ ω x)) from
              funext hcell_eq]
          exact hA_mem.sub hB_mem
        simpa using he_mem.integrable_sq
      · have hpartial_sm :
            AEStronglyMeasurable (fun x => ∫ ω, ‖(e ω x) ^ 2‖ ∂μ) ν := by
          simpa using (he_sq_meas.norm.prod_swap.integral_prod_right' :
            AEStronglyMeasurable (fun x => ∫ ω, ‖(e ω x) ^ 2‖ ∂μ) ν)
        haveI : IsFiniteMeasure ν := ⟨by
          rw [MeasureTheory.Measure.restrict_apply_univ]
          exact Λ.toSet_isCompact.measure_lt_top⟩
        have hconst : Integrable (fun _ : Spacetime2D => η) ν := integrable_const η
        refine hconst.mono hpartial_sm ?_
        filter_upwards [hpartial_lt] with x hx
        have hnorm_eq : ∫ ω, ‖(e ω x) ^ 2‖ ∂μ = ∫ ω, (e ω x) ^ 2 ∂μ := by
          refine integral_congr_ae ?_
          exact Filter.Eventually.of_forall (fun ω => by simp [Real.norm_of_nonneg (sq_nonneg _)])
        rw [hnorm_eq, Real.norm_of_nonneg (integral_nonneg fun _ => sq_nonneg _),
          Real.norm_of_nonneg (le_of_lt hη)]
        exact hx.le
    have hsq_le :=
      interactionCutoffSubUniformApprox_sub_sq_le_spatialIntegral params Λ κ κ₀ n hprod
    have hpartial_int : Integrable (fun x => ∫ ω, (e ω x) ^ 2 ∂μ) ν := by
      simpa [μ, ν, e] using hprod.integral_prod_right
    have hpartial_le : ∀ᵐ x ∂ν, ∫ ω, (e ω x) ^ 2 ∂μ ≤ η := by
      filter_upwards [hpartial_lt] with x hx
      exact hx.le
    have hspatial_le :
        ∫ x in Λ.toSet, ∫ ω, (e ω x) ^ 2 ∂μ ≤ η * V := by
      have hconst_int : Integrable (fun _ : Spacetime2D => η) ν := by
        haveI : IsFiniteMeasure ν := ⟨by
          rw [MeasureTheory.Measure.restrict_apply_univ]
          exact Λ.toSet_isCompact.measure_lt_top⟩
        exact integrable_const η
      have hnonneg_inner :
          0 ≤ᵐ[ν] fun x => ∫ ω, (e ω x) ^ 2 ∂μ := by
        filter_upwards with x
        exact integral_nonneg (fun _ => sq_nonneg _)
      calc
        ∫ x in Λ.toSet, ∫ ω, (e ω x) ^ 2 ∂μ
          ≤ ∫ x, η ∂ν := integral_mono_of_nonneg hnonneg_inner hconst_int hpartial_le
        _ = η * V := by
          have hν_real : ν.real Set.univ = V := by
            simp [ν, V, Measure.real]
          rw [MeasureTheory.integral_const, hν_real, smul_eq_mul]
          ring
    have hbound :
        ∫ ω, (D n ω) ^ 2 ∂μ < ε := by
      calc
      ∫ ω, (D n ω) ^ 2 ∂μ
          = ∫ ω,
              (interactionCutoffSubUniformApprox params Λ κ κ₀ n ω - X ω) ^ 2 ∂μ := by
                rfl
      _ ≤ params.coupling ^ 2 * V *
            ∫ x in Λ.toSet, ∫ ω, (e ω x) ^ 2 ∂μ := by
              simpa [μ, ν, X, Z, D, V] using hsq_le
      _ ≤ params.coupling ^ 2 * V * (η * V) := by
              gcongr
      _ < ε := by
              have hA_nonneg : 0 ≤ A := by
                unfold A V
                positivity
              have hA1_pos : 0 < A + 1 := by
                linarith
              have hA_lt : A * η < ε := by
                have hfrac : A / (A + 1) < (1 : ℝ) := by
                  rw [div_lt_iff₀ hA1_pos]
                  linarith
                have hEq : A * η = ε * (A / (A + 1)) := by
                  unfold η
                  field_simp [hA1_pos.ne']
                rw [hEq]
                nlinarith
              have hAV_eq : params.coupling ^ 2 * V * (η * V) = A * η := by
                unfold A
                ring
              rw [hAV_eq]
              exact hA_lt
    have hdist : dist (∫ ω, (D n ω) ^ 2 ∂μ) 0 < ε := by
      have hnonneg_int : 0 ≤ ∫ ω, (D n ω) ^ 2 ∂μ := by
        exact integral_nonneg (fun _ => sq_nonneg _)
      rw [Real.dist_eq]
      rw [sub_zero]
      rw [abs_of_nonneg hnonneg_int]
      exact hbound
    exact hdist
  have hD_lp_zero : Tendsto (fun n : ℕ => lpNorm (D n) 2 μ) atTop (𝓝 0) := by
    have hEq : ∀ n : ℕ, lpNorm (D n) 2 μ = Real.sqrt (∫ ω, (D n ω) ^ 2 ∂μ) := by
      intro n
      simpa [Real.sqrt_eq_rpow, Real.norm_eq_abs, sq_abs] using
        (lpNorm_eq_integral_norm_rpow_toReal
          (by norm_num : (2 : ℝ≥0∞) ≠ 0)
          (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
          (hD_meas n))
    have hsqrt : Tendsto (fun s : ℝ => Real.sqrt s) (𝓝 0) (𝓝 0) := by
      simpa using
        ((Real.continuous_sqrt.continuousAt : ContinuousAt (fun s : ℝ => Real.sqrt s) 0).tendsto)
    simpa [hEq] using hsqrt.comp hD_sq_tendsto_zero
  have hnorm :
      Tendsto (fun n : ℕ => lpNorm (Z n) 2 μ) atTop (𝓝 (lpNorm X 2 μ)) := by
    refine Metric.tendsto_atTop.2 ?_
    intro ε hε
    rcases Metric.tendsto_atTop.1 hD_lp_zero ε hε with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    have hD_triangle :
        |lpNorm (Z n) 2 μ - lpNorm X 2 μ| ≤ lpNorm (D n) 2 μ := by
      have hZ_eq : Z n = fun ω => X ω + D n ω := by
        funext ω
        unfold Z D X
        ring
      have hX_eq : X = fun ω => Z n ω + -(D n ω) := by
        funext ω
        unfold Z D X
        ring
      have h1 : lpNorm (Z n) 2 μ ≤ lpNorm X 2 μ + lpNorm (D n) 2 μ := by
        rw [hZ_eq]
        exact lpNorm_add_le hX_mem (g := D n) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      have h2 : lpNorm X 2 μ ≤ lpNorm (Z n) 2 μ + lpNorm (D n) 2 μ := by
        rw [hX_eq]
        simpa using
          (lpNorm_add_le (hZ_mem n) (g := fun ω => -(D n ω)) (by norm_num : (1 : ℝ≥0∞) ≤ 2))
      exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
    have hsmall : lpNorm (D n) 2 μ < ε := by
      simpa [Real.dist_eq, abs_of_nonneg MeasureTheory.lpNorm_nonneg] using hN n hn
    exact lt_of_le_of_lt hD_triangle hsmall
  have hZ_sq_eq : ∀ n : ℕ, (lpNorm (Z n) 2 μ) ^ 2 = ∫ ω, (Z n ω) ^ 2 ∂μ := by
    intro n
    have hroot : lpNorm (Z n) 2 μ = Real.sqrt (∫ ω, (Z n ω) ^ 2 ∂μ) := by
      simpa [Real.sqrt_eq_rpow, Real.norm_eq_abs, sq_abs] using
        (lpNorm_eq_integral_norm_rpow_toReal
          (by norm_num : (2 : ℝ≥0∞) ≠ 0)
          (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
          ((hZ_mem n).aestronglyMeasurable))
    rw [hroot, Real.sq_sqrt (integral_nonneg (fun _ => sq_nonneg _))]
  have hX_sq_eq : (lpNorm X 2 μ) ^ 2 = ∫ ω, (X ω) ^ 2 ∂μ := by
    have hroot : lpNorm X 2 μ = Real.sqrt (∫ ω, (X ω) ^ 2 ∂μ) := by
      simpa [Real.sqrt_eq_rpow, Real.norm_eq_abs, sq_abs] using
        (lpNorm_eq_integral_norm_rpow_toReal
          (by norm_num : (2 : ℝ≥0∞) ≠ 0)
          (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
          hX_mem.aestronglyMeasurable)
    rw [hroot, Real.sq_sqrt (integral_nonneg (fun _ => sq_nonneg _))]
  have hnorm_sq :
      Tendsto (fun n : ℕ => (lpNorm (Z n) 2 μ) ^ 2) atTop (𝓝 ((lpNorm X 2 μ) ^ 2)) := by
    simpa using (continuous_pow 2).continuousAt.tendsto.comp hnorm
  have hrew : (fun n : ℕ => (lpNorm (Z n) 2 μ) ^ 2) =
      (fun n : ℕ => ∫ ω, (Z n ω) ^ 2 ∂μ) := by
    funext n
    exact hZ_sq_eq n
  rw [hrew] at hnorm_sq
  simpa [Z, X, μ, hX_sq_eq] using hnorm_sq

/-- Frontier theorem for even-moment comparison on the canonical
uniform-refinement approximant sequence.

This is the actual hypercontractive leaf currently needed on the Nelson side.
The approximants are already concrete finite `0/2/4` Wick cylinders, so the
remaining mathematics is precisely the growth estimate for those canonical
integrated degree-4 Gaussian polynomials, not a broader unused class. -/
theorem gap_interactionCutoffSubUniformApprox_even_moment_comparison
    (params : Phi4Params) (Λ : Rectangle) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (κ κ₀ : UVCutoff) (n : ℕ) (j : ℕ), 0 < j →
          ∫ ω,
              |interactionCutoffSubUniformApprox params Λ κ κ₀ n ω| ^ (2 * j)
              ∂(freeFieldMeasure params.mass params.mass_pos)
            ≤ (C * ↑j) ^ (4 * j) *
                (∫ ω,
                    (interactionCutoffSubUniformApprox params Λ κ κ₀ n ω) ^ 2
                    ∂(freeFieldMeasure params.mass params.mass_pos)) ^ j := by
  obtain ⟨C, hC, hcmp⟩ :=
    gap_centeredGaussian_mvPolynomial_even_moment_comparison_totalDegree_le_four
  refine ⟨C, hC, ?_⟩
  intro κ κ₀ n j hj
  let μ : Measure FieldConfig2D := freeFieldMeasure params.mass params.mass_pos
  rcases
      IsFiniteWickCylinder.exists_mvPolynomial_model_totalDegree_le_four
        (interactionCutoffSubUniformApprox_isFiniteWickCylinder params Λ κ κ₀ n) with
    ⟨m, P, f4, f2, hdeg, hP⟩
  let ν : Measure (Fin m ⊕ Fin m → ℝ) := Measure.map (finiteWickCylinderEvalCLM f4 f2) μ
  letI : OpensMeasurableSpace (Fin m ⊕ Fin m → ℝ) := by infer_instance
  haveI : ProbabilityTheory.IsGaussian μ := by
    dsimp [μ, freeFieldMeasure]
    exact GaussianField.measure_isGaussian (freeCovarianceCLM params.mass params.mass_pos)
  have hmap_meas : Measurable (finiteWickCylinderEvalFamily f4 f2) := by
    classical
    exact measurable_pi_lambda (finiteWickCylinderEvalFamily f4 f2) <| by
      intro i
      cases i with
      | inl k =>
          simpa [finiteWickCylinderEvalFamily] using configuration_eval_measurable (f4 k)
      | inr k =>
          simpa [finiteWickCylinderEvalFamily] using configuration_eval_measurable (f2 k)
  have hmap_clm_meas : Measurable (finiteWickCylinderEvalCLM f4 f2) := by
    convert hmap_meas using 1
    ext ω
    simp [finiteWickCylinderEvalCLM_apply]
  have hmap_ae :
      AEMeasurable (finiteWickCylinderEvalCLM f4 f2) μ :=
    hmap_clm_meas.aemeasurable
  have hν : ProbabilityTheory.IsGaussian ν := by
    dsimp [ν]
    exact ProbabilityTheory.isGaussian_map_of_measurable (μ := μ) hmap_clm_meas
  have hν_centered : ∀ i : Fin m ⊕ Fin m, ∫ x, x i ∂ν = 0 := by
    simpa [ν] using
      finiteWickCylinderEvalCLM_centered params.mass params.mass_pos f4 f2
  have hleft :
      ∫ x, |P.eval x| ^ (2 * j) ∂ν
        = ∫ ω, |P.eval (finiteWickCylinderEvalFamily f4 f2 ω)| ^ (2 * j) ∂μ := by
    dsimp [ν]
    rw [integral_map hmap_ae
      (((continuous_mvPolynomial_eval P).abs.pow (2 * j)).aestronglyMeasurable)]
    simp [finiteWickCylinderEvalCLM_apply]
  have hright :
      ∫ x, (P.eval x) ^ 2 ∂ν
        = ∫ ω, (P.eval (finiteWickCylinderEvalFamily f4 f2 ω)) ^ 2 ∂μ := by
    dsimp [ν]
    rw [integral_map hmap_ae
      (((continuous_mvPolynomial_eval P).pow 2).aestronglyMeasurable)]
    simp [finiteWickCylinderEvalCLM_apply]
  have hcmp' := hcmp ν hν hν_centered P hdeg j hj
  simpa [μ, hP, hleft, hright] using hcmp'

/-- Derived theorem for the canonical reference-shell even-moment bound in
Nelson's argument.

With a logarithmic covariance-growth constant `K` fixed, the remaining missing
Nelson-side mathematics splits naturally into:
1. a uniform Gaussian-polynomial even-moment comparison for cutoff differences,
2. an explicit `L²` decay bound for the canonical reference shell.

The next two frontier theorems expose exactly those two inputs.

Important theorem-surface note:
- the moment-comparison input must control the **integrated variable**
  `interactionCutoff κ - interactionCutoff κ₀` directly in terms of its own
  `L²` norm;
- a product-space comparison for the pointwise Wick-power difference is too weak
  for downstream use, because Jensen only gives
  `E[(ΔV)^2] ≤ const * ∫∫ d^2`, i.e. in the wrong direction for recovering an
  `L²`-based hypercontractive bound on `ΔV`.

So the genuine missing mathematics here is a fourth-chaos / Nelson
hypercontractive estimate for the integrated cutoff difference itself, not just
a pointwise spacetime moment estimate. -/
theorem gap_interactionCutoff_sub_even_moment_comparison
    (params : Phi4Params) (Λ : Rectangle) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (κ κ₀ : UVCutoff) (j : ℕ), 0 < j →
        ∫ ω,
            |interactionCutoff params Λ κ ω - interactionCutoff params Λ κ₀ ω| ^ (2 * j)
            ∂(freeFieldMeasure params.mass params.mass_pos)
          ≤ (C * ↑j) ^ (4 * j) *
              (∫ ω,
                  (interactionCutoff params Λ κ ω - interactionCutoff params Λ κ₀ ω) ^ 2
                  ∂(freeFieldMeasure params.mass params.mass_pos)) ^ j := by
  obtain ⟨C, hC, hcmp⟩ := gap_interactionCutoffSubUniformApprox_even_moment_comparison params Λ
  refine ⟨C, hC, ?_⟩
  intro κ κ₀ j hj
  let μ : Measure FieldConfig2D := freeFieldMeasure params.mass params.mass_pos
  let X : FieldConfig2D → ℝ :=
    fun ω => interactionCutoff params Λ κ ω - interactionCutoff params Λ κ₀ ω
  let Z : ℕ → FieldConfig2D → ℝ := interactionCutoffSubUniformApprox params Λ κ κ₀
  have hZ_meas : ∀ n, AEStronglyMeasurable (Z n) μ := by
    intro n
    exact
      ((interactionCutoffSubUniformApprox_isFiniteWickCylinder params Λ κ κ₀ n).memLp
        params.mass params.mass_pos (p := (1 : ℝ≥0∞)) (by norm_num)).aestronglyMeasurable
  have hX_meas : AEStronglyMeasurable X μ := by
    simpa [X] using
      ((interactionCutoff_stronglyMeasurable params Λ κ).sub
        (interactionCutoff_stronglyMeasurable params Λ κ₀)).aestronglyMeasurable
  have hZ_int : ∀ n, Integrable (fun ω => |Z n ω| ^ (2 * j)) μ := by
    intro n
    simpa [μ, Z] using
      (interactionCutoffSubUniformApprox_isFiniteWickCylinder params Λ κ κ₀ n).even_integrable
        params.mass params.mass_pos j
  simpa [μ, X, Z] using
    evenMomentComparison_of_tendsto_ae μ X Z ((C * ↑j) ^ (4 * j)) j
      (by positivity)
      (gap_interactionCutoffSubUniformApprox_tendsto_ae params Λ κ κ₀)
      hZ_meas hX_meas hZ_int
      (fun n => hcmp κ κ₀ n j hj)
      (gap_interactionCutoffSubUniformApprox_L2 params Λ κ κ₀)

/-- Frontier theorem for the `L²` size of the canonical reference shell in
Nelson's argument.

This is the genuine covariance-shell decay input on the Nelson side, but only
in the large-cutoff regime `κ₀(t) ≤ κ`. For cutoffs below the reference scale,
the lower tail is handled deterministically by the Wick lower bound, so no
decaying shell estimate should be claimed there. The smallness condition
relative to `C` is bundled here because it is needed by the optimized Markov
step later. -/
theorem gap_interactionCutoff_reference_shell_L2_bound
    (params : Phi4Params) (Λ : Rectangle) (K C₀ C : ℝ) :
    ∃ σ₀ β : ℝ,
      0 < σ₀ ∧ 0 < β ∧
      (∀ t : ℝ, 0 ≤ t →
        σ₀ * Real.exp (-2 * β * Real.sqrt (t + 2)) ≤ 1 / (Real.exp 1 * C) ^ 2) ∧
      ∀ (κ : UVCutoff) (t : ℝ), 0 ≤ t →
        (nelsonReferenceCutoff params Λ K C₀ t).κ ≤ κ.κ →
        ∫ ω,
            (interactionCutoff params Λ κ ω -
              interactionCutoff params Λ (nelsonReferenceCutoff params Λ K C₀ t) ω) ^ 2
            ∂(freeFieldMeasure params.mass params.mass_pos)
          ≤ (σ₀ * Real.exp (-2 * β * Real.sqrt (t + 2))) ^ 2 := by
  sorry

/-- Derived canonical reference-shell even-moment theorem.

This theorem is no longer a primitive analytic frontier: it is assembled from
the two genuine missing inputs above, namely uniform even-moment comparison and
the explicit large-cutoff `L²` shell decay bound. -/
theorem gap_interactionCutoff_reference_shell_even_moment_bound
    (params : Phi4Params) (Λ : Rectangle) (K C₀ : ℝ) :
    ∃ C σ₀ β : ℝ,
      0 < C ∧ 0 < σ₀ ∧ 0 < β ∧
      (∀ t : ℝ, 0 ≤ t →
        σ₀ * Real.exp (-2 * β * Real.sqrt (t + 2)) ≤ 1 / (Real.exp 1 * C) ^ 2) ∧
      ∀ (κ : UVCutoff) (t : ℝ), 0 ≤ t →
        (nelsonReferenceCutoff params Λ K C₀ t).κ ≤ κ.κ →
        ∀ j : ℕ, 0 < j →
        Integrable
          (fun ω : FieldConfig2D =>
            |interactionCutoff params Λ κ ω -
                interactionCutoff params Λ (nelsonReferenceCutoff params Λ K C₀ t) ω| ^ (2 * j))
          (freeFieldMeasure params.mass params.mass_pos) ∧
        ∫ ω,
            |interactionCutoff params Λ κ ω -
                interactionCutoff params Λ (nelsonReferenceCutoff params Λ K C₀ t) ω| ^ (2 * j)
            ∂(freeFieldMeasure params.mass params.mass_pos)
          ≤ (C * ↑j) ^ (4 * j) * (σ₀ * Real.exp (-2 * β * Real.sqrt (t + 2))) ^ (2 * j) := by
  obtain ⟨C, hC, hmomentCmp⟩ := gap_interactionCutoff_sub_even_moment_comparison params Λ
  obtain ⟨σ₀, β, hσ₀, hβ, hσ_small, hL2⟩ :=
    gap_interactionCutoff_reference_shell_L2_bound params Λ K C₀ C
  refine ⟨C, σ₀, β, hC, hσ₀, hβ, hσ_small, ?_⟩
  intro κ t ht hκ_ge j hj
  have hint :=
    interactionCutoff_sub_even_integrable params Λ (nelsonReferenceCutoff params Λ K C₀ t) κ j hj
  have hcmp := hmomentCmp κ (nelsonReferenceCutoff params Λ K C₀ t) j hj
  refine ⟨hint, le_trans hcmp ?_⟩
  have hL2' := hL2 κ t ht hκ_ge
  have hpow_le :
      (∫ ω,
          (interactionCutoff params Λ κ ω -
            interactionCutoff params Λ (nelsonReferenceCutoff params Λ K C₀ t) ω) ^ 2
          ∂(freeFieldMeasure params.mass params.mass_pos)) ^ j
        ≤ ((σ₀ * Real.exp (-2 * β * Real.sqrt (t + 2))) ^ 2) ^ j := by
    exact pow_le_pow_left₀ (by positivity) hL2' j
  calc
    (C * ↑j) ^ (4 * j) *
        (∫ ω,
            (interactionCutoff params Λ κ ω -
              interactionCutoff params Λ (nelsonReferenceCutoff params Λ K C₀ t) ω) ^ 2
            ∂(freeFieldMeasure params.mass params.mass_pos)) ^ j
      ≤ (C * ↑j) ^ (4 * j) * ((σ₀ * Real.exp (-2 * β * Real.sqrt (t + 2))) ^ 2) ^ j := by
          exact mul_le_mul_of_nonneg_left hpow_le (by positivity)
    _ = (C * ↑j) ^ (4 * j) * (σ₀ * Real.exp (-2 * β * Real.sqrt (t + 2))) ^ (2 * j) := by
          have hpow_eq :
              ((σ₀ * Real.exp (-2 * β * Real.sqrt (t + 2))) ^ 2) ^ j =
                (σ₀ * Real.exp (-2 * β * Real.sqrt (t + 2))) ^ (2 * j) := by
            rw [← pow_mul]
          rw [hpow_eq]

/-- **Sub-gap A: Double-exponential tail bound for the cutoff interaction.**

    For all t ≥ 0 and all UV cutoffs κ:
      P(V_{Λ,κ} < -t) ≤ A · exp(-B · exp(C · √t))
    where A, B, C > 0 depend on λ, |Λ|, m but NOT on κ.

    This is the core of Nelson's argument (Simon Theorem V.14). The proof uses:
    1. Covariance splitting: split φ_κ = φ_{κ₀} + ψ with κ₀ chosen from an
       additive-constant logarithmic covariance bound
    2. Wick lower bound: V_{κ₀} ≥ -6λc_{κ₀}²|Λ| ≥ -t (by choice of κ₀)
    3. Hence P(V_κ < -t-1) ≤ P(V_κ - V_{κ₀} < -1)
    4. Moment bound: E[(V_κ - V_{κ₀})^{2j}] ≤ (4j²)^{2j} ‖V_κ - V_{κ₀}‖₂^{2j}
       (Gaussian polynomial moment equivalence for 4th-chaos elements)
    5. L² bound: ‖V_κ - V_{κ₀}‖₂ ≤ ε(κ₀) with ε(κ₀) ~ κ₀^{-δ}
    6. Optimize j to get double-exponential tail decay. -/
theorem gap_interaction_double_exponential_tail_bound
    (params : Phi4Params) (Λ : Rectangle) :
    ∃ A B C : ℝ, 0 < A ∧ 0 < B ∧ 0 < C ∧ ∀ (κ : UVCutoff) (t : ℝ), 0 ≤ t →
      (freeFieldMeasure params.mass params.mass_pos)
        {ω : FieldConfig2D | interactionCutoff params Λ κ ω < -t} ≤
      ENNReal.ofReal (A * Real.exp (-B * Real.exp (C * Real.sqrt t))) := by
  obtain ⟨K, C₀, hK, hC₀, hcov⟩ := gap_regularizedPointCovariance_log_growth params
  obtain ⟨Cmom, σ₀, β, hCmom, hσ₀, hβ, hσ_small, hmoment⟩ :=
    gap_interactionCutoff_reference_shell_even_moment_bound params Λ K C₀
  exact
    interactionCutoff_double_exponential_tail_of_log_covariance_and_reference_shell_scale
      params Λ hK hC₀ hcov hCmom hσ₀ hβ hmoment hσ_small

/-- The improper integral ∫₀^∞ exp(pt - B·exp(C·√t)) dt is finite for all p, B, C > 0.
    Proof: for t ≥ T₀, B·exp(C·√t) ≥ (p+1)t, so the integrand ≤ exp(-t). -/
theorem integral_exp_linear_minus_double_exp_finite
    {p B C : ℝ} (hB : 0 < B) (hC : 0 < C) :
    IntegrableOn (fun t => Real.exp (p * t - B * Real.exp (C * Real.sqrt t)))
      (Set.Ioi 0) volume := by
  set T₀ := max 1 (24 * (p + 1) / (B * C ^ 4)) with hT₀_def
  have hT₀_pos : 0 < T₀ := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hBC4_pos : 0 < B * C ^ 4 := mul_pos hB (pow_pos hC 4)
  have hexp_quartic : ∀ t : ℝ, 0 ≤ t →
      C ^ 4 * t ^ 2 / 24 ≤ Real.exp (C * Real.sqrt t) := by
    intro t ht
    have hsqrt_nn : 0 ≤ C * Real.sqrt t := mul_nonneg (le_of_lt hC) (Real.sqrt_nonneg t)
    have h1 := Real.pow_div_factorial_le_exp (C * Real.sqrt t) hsqrt_nn 4
    have h2 : (C * Real.sqrt t) ^ 4 = C ^ 4 * t ^ 2 := by
      rw [mul_pow]; congr 1; rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt ht]
    rw [h2] at h1; norm_num [Nat.factorial] at h1; linarith
  have h_dom : ∀ t ≥ T₀, p * t - B * Real.exp (C * Real.sqrt t) ≤ -t := by
    intro t ht
    have ht_pos : 0 ≤ t := le_of_lt (lt_of_lt_of_le hT₀_pos ht)
    have ht_T₀ : t ≥ 24 * (p + 1) / (B * C ^ 4) := le_trans (le_max_right _ _) ht
    have h_coeff : (p + 1) * 24 ≤ B * C ^ 4 * t := by
      have := div_le_iff₀ hBC4_pos |>.mp ht_T₀; linarith
    have h_exp := hexp_quartic t ht_pos
    have h_B_exp : B * (C ^ 4 * t ^ 2 / 24) ≤ B * Real.exp (C * Real.sqrt t) :=
      mul_le_mul_of_nonneg_left h_exp (le_of_lt hB)
    nlinarith
  have hf_cont : Continuous (fun t : ℝ => Real.exp (p * t - B * Real.exp (C * Real.sqrt t))) :=
    by fun_prop
  have h_Ioi : IntegrableOn (fun t => Real.exp (p * t - B * Real.exp (C * Real.sqrt t)))
      (Set.Ioi T₀) volume := by
    apply Integrable.mono (exp_neg_integrableOn_Ioi T₀ one_pos)
      (hf_cont.aestronglyMeasurable.restrict)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (by linarith [h_dom t (Set.mem_Ioi.mp ht).le])
  have h_Ioc : IntegrableOn (fun t => Real.exp (p * t - B * Real.exp (C * Real.sqrt t)))
      (Set.Ioc 0 T₀) volume :=
    (hf_cont.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  rw [show Set.Ioi (0 : ℝ) = Set.Ioc 0 T₀ ∪ Set.Ioi T₀ from
    (Set.Ioc_union_Ioi_eq_Ioi (le_of_lt hT₀_pos)).symm]
  exact h_Ioc.union h_Ioi

/-- FTC: ∫₀^y p·exp(pt) dt = exp(py) - 1. -/
private theorem interval_integral_p_mul_exp (p y : ℝ) :
    ∫ t in (0 : ℝ)..y, p * Real.exp (p * t) = Real.exp (p * y) - 1 := by
  have hderiv : ∀ x ∈ Set.uIcc 0 y,
      HasDerivAt (fun t => Real.exp (p * t)) (p * Real.exp (p * x)) x := by
    intro x _
    exact ((by simpa using (hasDerivAt_id x).const_mul p :
      HasDerivAt (fun t => p * t) p x).exp.congr_deriv (by ring))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id'))).intervalIntegrable _ _)]
  simp [mul_zero]

/-- Pure-analysis lemma: if a random variable has double-exponential lower tail,
    then all negative exponential moments are finite.

    From the layer-cake identity:
      E[exp(-pX)] ≤ 1 + ∫₀^∞ p·exp(pt) · P(X < -t) dt
    and the double-exponential tail bound P(X < -t) ≤ A·exp(-B·exp(C·√t)):
      ∫₀^∞ p·exp(pt)·A·exp(-B·exp(C·√t)) dt < ∞
    because exp(C·√t) dominates pt for large t. -/
theorem neg_exp_moment_of_double_exponential_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X)
    {A B C_tail : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C_tail)
    (htail : ∀ t : ℝ, 0 ≤ t →
      μ {ω | X ω < -t} ≤ ENNReal.ofReal (A * Real.exp (-B * Real.exp (C_tail * Real.sqrt t))))
    (p : ℝ) (hp : 0 < p) :
    Integrable (fun ω => Real.exp (-(p * X ω))) μ ∧
    ∫ ω, Real.exp (-(p * X ω)) ∂μ ≤
      1 + p * A * ∫ t in Set.Ioi 0,
        Real.exp (p * t - B * Real.exp (C_tail * Real.sqrt t)) := by
  -- Abbreviations
  set g : ℝ → ℝ := fun t => p * Real.exp (p * t) with hg_def
  set f_tail : ℝ → ℝ := fun t =>
    p * A * Real.exp (p * t - B * Real.exp (C_tail * Real.sqrt t)) with hf_def
  -- FTC: ∫₀^{max(-x,0)} g = exp(p·max(-x,0)) - 1
  have hftc : ∀ ω : Ω, ∫ t in (0 : ℝ)..max (-X ω) 0, g t =
      Real.exp (p * max (-X ω) 0) - 1 :=
    fun ω => interval_integral_p_mul_exp p _
  have hI_nn : ∀ ω : Ω, 0 ≤ ∫ t in (0 : ℝ)..max (-X ω) 0, g t := fun ω => by
    rw [hftc]; linarith [Real.one_le_exp (mul_nonneg hp.le (le_max_right (-X ω) 0))]
  -- Layer-cake formula
  have hlc : ∫⁻ ω, ENNReal.ofReal (∫ t in (0 : ℝ)..max (-X ω) 0, g t) ∂μ =
      ∫⁻ t in Set.Ioi (0 : ℝ), μ {a | t < max (-X a) 0} * ENNReal.ofReal (g t) :=
    lintegral_comp_eq_lintegral_meas_lt_mul μ
      (by filter_upwards with ω; exact le_max_right _ _)
      ((hX.neg.max measurable_const).aemeasurable)
      (fun t _ => (continuous_const.mul (Real.continuous_exp.comp
        (continuous_const.mul continuous_id'))).intervalIntegrable _ _)
      (by filter_upwards with t; exact mul_nonneg hp.le (Real.exp_pos _).le)
  -- {max(-X,0) > t} = {X < -t} for t > 0
  have hset_eq : ∀ t : ℝ, 0 < t →
      μ {a : Ω | t < max (-X a) 0} = μ {a | X a < -t} := by
    intro t ht; congr 1; ext ω; simp only [Set.mem_setOf_eq]
    constructor
    · intro h; by_contra h_neg; push_neg at h_neg
      exact not_lt.mpr (max_le (by linarith) ht.le) h
    · intro h; exact lt_max_of_lt_left (by linarith)
  -- Tail integrand is IntegrableOn (Ioi 0)
  have hf_intOn : IntegrableOn f_tail (Set.Ioi 0) volume := by
    have := @integral_exp_linear_minus_double_exp_finite p B C_tail hB hC
    exact this.const_mul (p * A)
  -- *** Main lintegral bound ***
  -- ∫⁻ ofReal(exp(-pX)) ≤ 1 + ∫⁻_{t>0} ofReal(f_tail t)
  have h_lint_bound : ∫⁻ ω, ENNReal.ofReal (Real.exp (-(p * X ω))) ∂μ ≤
      1 + ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (f_tail t) := by
    calc ∫⁻ ω, ENNReal.ofReal (Real.exp (-(p * X ω))) ∂μ
        ≤ ∫⁻ ω, (1 + ENNReal.ofReal (∫ t in (0 : ℝ)..max (-X ω) 0, g t)) ∂μ := by
          apply lintegral_mono; intro ω; simp only
          rw [show (1 : ENNReal) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm,
              ← ENNReal.ofReal_add one_pos.le (hI_nn ω), hftc]
          apply ENNReal.ofReal_le_ofReal
          linarith [Real.exp_le_exp.2 (show -(p * X ω) ≤ p * max (-X ω) 0
            by nlinarith [le_max_left (-X ω) 0])]
      _ = 1 + ∫⁻ ω, ENNReal.ofReal (∫ t in (0 : ℝ)..max (-X ω) 0, g t) ∂μ := by
          rw [lintegral_add_left measurable_const]; simp [lintegral_const, measure_univ]
      _ = 1 + ∫⁻ t in Set.Ioi (0 : ℝ),
            μ {a | t < max (-X a) 0} * ENNReal.ofReal (g t) := by rw [hlc]
      _ = 1 + ∫⁻ t in Set.Ioi (0 : ℝ),
            μ {a | X a < -t} * ENNReal.ofReal (g t) := by
          congr 1; apply setLIntegral_congr_fun measurableSet_Ioi
          intro t ht; simp only [Set.mem_Ioi] at ht
          show μ {a | t < max (-X a) 0} * _ = μ {a | X a < -t} * _
          rw [hset_eq t ht]
      _ ≤ 1 + ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (f_tail t) := by
          apply add_le_add_right _ 1
          apply setLIntegral_mono (Measurable.ennreal_ofReal (by fun_prop))
          intro t ht
          have ht' := Set.mem_Ioi.mp ht
          calc μ {a | X a < -t} * ENNReal.ofReal (g t)
              ≤ ENNReal.ofReal (A * Real.exp (-B * Real.exp (C_tail * Real.sqrt t))) *
                ENNReal.ofReal (g t) :=
                mul_le_mul_left (htail t ht'.le) _
            _ = ENNReal.ofReal (A * Real.exp (-B * Real.exp (C_tail * Real.sqrt t)) * g t) :=
                (ENNReal.ofReal_mul (mul_nonneg hA.le (Real.exp_pos _).le)).symm
            _ = ENNReal.ofReal (f_tail t) := by
                congr 1; simp only [hg_def, hf_def]
                rw [show p * t - B * Real.exp (C_tail * Real.sqrt t) =
                  -B * Real.exp (C_tail * Real.sqrt t) + p * t from by ring, Real.exp_add]
                ring
  -- *** Convert to real integral ***
  -- The lintegral of ofReal(f_tail) equals ofReal(∫ f_tail) since f_tail ≥ 0 and integrable
  have h_lint_eq : ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (f_tail t) =
      ENNReal.ofReal (∫ t in Set.Ioi 0, f_tail t) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hf_intOn
      (by filter_upwards with t; exact mul_nonneg (mul_nonneg hp.le hA.le) (Real.exp_pos _).le)]
  -- The lintegral is finite
  have h_lint_ne_top : ∫⁻ ω, ENNReal.ofReal (Real.exp (-(p * X ω))) ∂μ ≠ ⊤ := by
    have h_rhs_ne_top : 1 + ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (f_tail t) ≠ ⊤ := by
      rw [h_lint_eq]
      exact ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.ofReal_ne_top⟩
    exact ne_top_of_le_ne_top h_rhs_ne_top h_lint_bound
  -- Integrability
  have h_integrable : Integrable (fun ω => Real.exp (-(p * X ω))) μ := by
    refine ⟨((hX.const_mul p).neg.exp).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    calc ∫⁻ a, ENNReal.ofReal ‖Real.exp (-(p * X a))‖ ∂μ
        = ∫⁻ a, ENNReal.ofReal (Real.exp (-(p * X a))) ∂μ := by
          congr 1; ext ω; rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      _ < ⊤ := h_lint_ne_top.lt_top
  refine ⟨h_integrable, ?_⟩
  -- Real integral bound
  have h_real : (∫ ω, Real.exp (-(p * X ω)) ∂μ : ℝ) =
      (∫⁻ ω, ENNReal.ofReal (Real.exp (-(p * X ω))) ∂μ).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (by filter_upwards with ω; exact (Real.exp_pos _).le)
      ((hX.const_mul p).neg.exp).aestronglyMeasurable]
  rw [h_real]
  have h_rhs_ne : 1 + ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (f_tail t) ≠ ⊤ := by
    rw [h_lint_eq]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.ofReal_ne_top⟩
  have h_rhs_val : (1 + ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (f_tail t)).toReal =
      1 + ∫ t in Set.Ioi 0, f_tail t := by
    rw [h_lint_eq, ENNReal.toReal_add ENNReal.one_ne_top ENNReal.ofReal_ne_top,
        ENNReal.toReal_one, ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ioi
          (fun t _ => mul_nonneg (mul_nonneg hp.le hA.le) (Real.exp_pos _).le))]
  rw [show 1 + p * A * ∫ t in Set.Ioi 0,
      Real.exp (p * t - B * Real.exp (C_tail * Real.sqrt t)) =
    1 + ∫ t in Set.Ioi 0, f_tail t from by
      simp only [hf_def]; rw [← integral_const_mul]]
  rw [← h_rhs_val]
  exact (ENNReal.toReal_le_toReal h_lint_ne_top h_rhs_ne).mpr h_lint_bound

/-- Bounded form of `neg_exp_moment_of_double_exponential_tail`: under a double-exponential
    lower tail bound, the negative exponential moment E[exp(-pX)] is bounded by some
    finite constant K. This decouples downstream uses from the specific layer-cake bound. -/
theorem neg_exp_moment_bounded_of_double_exponential_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X)
    {A B C_tail : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C_tail)
    (htail : ∀ t : ℝ, 0 ≤ t →
      μ {ω | X ω < -t} ≤ ENNReal.ofReal (A * Real.exp (-B * Real.exp (C_tail * Real.sqrt t))))
    (p : ℝ) (hp : 0 < p) :
    ∃ K : ℝ, 0 < K ∧
      Integrable (fun ω => Real.exp (-(p * X ω))) μ ∧
      ∫ ω, Real.exp (-(p * X ω)) ∂μ ≤ K := by
  obtain ⟨hint, hbound⟩ := neg_exp_moment_of_double_exponential_tail hX hA hB hC htail p hp
  refine ⟨1 + p * A * ∫ t in Set.Ioi 0,
    Real.exp (p * t - B * Real.exp (C_tail * Real.sqrt t)), ?_, hint, hbound⟩
  have hI := @integral_exp_linear_minus_double_exp_finite p B C_tail hB hC
  have : 0 ≤ p * A * ∫ t in Set.Ioi 0,
      Real.exp (p * t - B * Real.exp (C_tail * Real.sqrt t)) :=
    mul_nonneg (mul_nonneg hp.le hA.le)
      (setIntegral_nonneg measurableSet_Ioi (fun t _ => (Real.exp_pos _).le))
  linarith

theorem gap_exp_neg_interaction_uniform_bound (params : Phi4Params) (Λ : Rectangle) :
    ∀ p : ℝ, 0 < p →
      ∃ C : ℝ, 0 < C ∧ ∀ κ : UVCutoff,
        Integrable
          (fun ω : FieldConfig2D =>
            Real.exp (-(p * interactionCutoff params Λ κ ω)))
          (freeFieldMeasure params.mass params.mass_pos) ∧
        ∫ ω : FieldConfig2D,
          Real.exp (-(p * interactionCutoff params Λ κ ω))
          ∂(freeFieldMeasure params.mass params.mass_pos) ≤ C := by
  intro p hp
  -- Obtain double-exponential tail bound (uniform in κ)
  obtain ⟨A, B, C_tail, hA, hB, hC, htail⟩ :=
    gap_interaction_double_exponential_tail_bound params Λ
  -- The layer-cake integral is finite
  have hI := @integral_exp_linear_minus_double_exp_finite p B C_tail hB hC
  -- Set uniform bound
  set K := 1 + p * A * ∫ t in Set.Ioi 0,
    Real.exp (p * t - B * Real.exp (C_tail * Real.sqrt t))
  refine ⟨K, ?_, fun κ => ?_⟩
  · -- K > 0: K = 1 + (nonneg) ≥ 1 > 0
    have : 0 ≤ p * A * ∫ t in Set.Ioi 0,
        Real.exp (p * t - B * Real.exp (C_tail * Real.sqrt t)) :=
      mul_nonneg (mul_nonneg (le_of_lt hp) (le_of_lt hA))
        (setIntegral_nonneg measurableSet_Ioi (fun t _ => le_of_lt (Real.exp_pos _)))
    linarith
  · -- Apply neg_exp_moment to each cutoff
    have hX_meas : Measurable (interactionCutoff params Λ κ) :=
      (interactionCutoff_stronglyMeasurable params Λ κ).measurable
    exact neg_exp_moment_of_double_exponential_tail hX_meas hA hB hC
      (fun t ht => htail κ t ht) p hp

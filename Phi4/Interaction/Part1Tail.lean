/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.Interaction.Part1Core

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

/-- Level-set monotonicity:
    `{a ≤ |X(ω)|} = {a^k ≤ |X(ω)|^k}` for `a ≥ 0`, `k ≠ 0`. -/
theorem abs_pow_level_set_eq {Ω : Type*} (X : Ω → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (k : ℕ) (hk : k ≠ 0) :
    {ω | a ≤ |X ω|} = {ω | a ^ k ≤ |X ω| ^ k} := by
  ext ω
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hle
    exact pow_le_pow_left₀ ha hle k
  · intro hle
    exact le_of_pow_le_pow_left₀ hk (abs_nonneg _) hle

/-- Higher-moment Markov inequality in ENNReal form:
    `μ{|X| ≥ a} ≤ E[|X|^(2j)] / a^(2j)`, for `j > 0`, `a > 0`. -/
theorem higher_moment_markov_ennreal {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : Ω → ℝ} {j : ℕ} (hj : 0 < j)
    {a : ℝ} (ha : 0 < a)
    (hint : Integrable (fun ω => |X ω| ^ (2 * j)) μ) :
    μ {ω | a ≤ |X ω|} ≤
      ENNReal.ofReal ((∫ ω, |X ω| ^ (2 * j) ∂μ) / a ^ (2 * j)) := by
  have ha2j : (0 : ℝ) < a ^ (2 * j) := pow_pos ha _
  have hmark :
      a ^ (2 * j) * μ.real {ω | a ^ (2 * j) ≤ |X ω| ^ (2 * j)} ≤
        ∫ ω, |X ω| ^ (2 * j) ∂μ :=
    mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall (fun _ => by positivity)) hint _
  have hreal :
      μ.real {ω | a ≤ |X ω|} ≤
        (∫ ω, |X ω| ^ (2 * j) ∂μ) / a ^ (2 * j) := by
    rw [abs_pow_level_set_eq X a ha.le (2 * j) (by omega)]
    rw [le_div_iff₀ ha2j]
    linarith [mul_comm (a ^ (2 * j)) (μ.real {ω | a ^ (2 * j) ≤ |X ω| ^ (2 * j)})]
  have hrhs_nonneg : 0 ≤ (∫ ω, |X ω| ^ (2 * j) ∂μ) / a ^ (2 * j) :=
    div_nonneg (integral_nonneg (fun _ => by positivity)) (by positivity)
  exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _) hrhs_nonneg).mpr hreal

/-- Shifted-index cutoff-to-limit deviation bad-event bound from squared moments
    (Chebyshev):
    for `a > 0`,
    `μ{ a ≤ |interactionCutoff(κ_{n+1}) - interaction| }`
    is bounded by the squared-moment ratio
    `E[(interactionCutoff(κ_{n+1}) - interaction)^2] / a^2`. -/
theorem shifted_cutoff_interaction_deviation_bad_event_measure_le_of_sq_moment
    (params : Phi4Params) (Λ : Rectangle) (a : ℝ) (ha : 0 < a) (n : ℕ)
    (hInt :
      Integrable
        (fun ω : FieldConfig2D =>
          (interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω) ^ 2)
        (freeFieldMeasure params.mass params.mass_pos)) :
    (freeFieldMeasure params.mass params.mass_pos)
      {ω : FieldConfig2D |
        a ≤
          |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω -
            interaction params Λ ω|}
      ≤ ENNReal.ofReal
          ((∫ ω : FieldConfig2D,
              (interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)) /
            (a ^ 2)) := by
  let μ : Measure FieldConfig2D := freeFieldMeasure params.mass params.mass_pos
  let X : FieldConfig2D → ℝ := fun ω =>
    interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω
  letI : IsProbabilityMeasure μ := freeFieldMeasure_isProbability params.mass params.mass_pos
  have hIntAbs : Integrable (fun ω : FieldConfig2D => |X ω| ^ (2 * (1 : ℕ))) μ := by
    refine hInt.congr ?_
    filter_upwards with ω
    simp [X, pow_two]
  have hmarkov :
      μ {ω : FieldConfig2D | a ≤ |X ω|} ≤
        ENNReal.ofReal ((∫ ω : FieldConfig2D, |X ω| ^ (2 * (1 : ℕ)) ∂μ) / a ^ (2 * (1 : ℕ))) :=
    higher_moment_markov_ennreal (μ := μ) (X := X) (j := 1) (hj := by decide)
      (a := a) ha hIntAbs
  simpa [X, μ, pow_two, sq_abs] using hmarkov

/-- Shifted-index cutoff-to-limit deviation bad-event majorant from squared
    moment majorants:
    if `E[(interactionCutoff(κ_{n+1}) - interaction)^2] ≤ Mₙ`, then
    `μ{ a ≤ |interactionCutoff(κ_{n+1}) - interaction| } ≤ Mₙ / a^2`. -/
theorem shifted_cutoff_interaction_deviation_bad_event_measure_le_of_sq_moment_bound
    (params : Phi4Params) (Λ : Rectangle) (a : ℝ) (ha : 0 < a)
    (M : ℕ → ℝ)
    (hInt :
      ∀ n : ℕ,
        Integrable
          (fun ω : FieldConfig2D =>
            (interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hM :
      ∀ n : ℕ,
        ∫ ω : FieldConfig2D,
          (interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω) ^ 2
          ∂(freeFieldMeasure params.mass params.mass_pos) ≤ M n) :
    ∀ n : ℕ,
      (freeFieldMeasure params.mass params.mass_pos)
        {ω : FieldConfig2D |
          a ≤
            |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω -
              interaction params Λ ω|}
        ≤ ENNReal.ofReal ((M n) / (a ^ 2)) := by
  intro n
  have hbase :=
    shifted_cutoff_interaction_deviation_bad_event_measure_le_of_sq_moment
      (params := params) (Λ := Λ) (a := a) ha n (hInt n)
  have hdiv :
      (∫ ω : FieldConfig2D,
          (interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω) ^ 2
          ∂(freeFieldMeasure params.mass params.mass_pos)) / (a ^ 2)
        ≤ (M n) / (a ^ 2) := by
    exact div_le_div_of_nonneg_right (hM n) (sq_nonneg a)
  exact hbase.trans (ENNReal.ofReal_le_ofReal hdiv)

/-- Polynomial-decay majorants produce finite ENNReal sums.
    This is a reusable p-series bridge for bad-event summability arguments. -/
theorem tsum_ofReal_ne_top_of_polynomial_decay
    {f : ℕ → ℝ} {K : ℝ} {α : ℝ}
    (hα : 1 < α)
    (hf_nonneg : ∀ n, 0 ≤ f n)
    (hle : ∀ n, f n ≤ K * (↑(n + 1) : ℝ) ^ (-α)) :
    ∑' n, ENNReal.ofReal (f n) ≠ ⊤ := by
  have hs_rpow : Summable (fun n : ℕ => (n : ℝ) ^ (-α)) := by
    exact (Real.summable_nat_rpow).2 (by linarith)
  have hs_shift : Summable (fun n : ℕ => (↑(n + 1) : ℝ) ^ (-α)) := by
    simpa [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc] using
      (_root_.summable_nat_add_iff 1).2 hs_rpow
  have hs_major : Summable (fun n : ℕ => K * (↑(n + 1) : ℝ) ^ (-α)) :=
    hs_shift.mul_left K
  have hs_f : Summable f :=
    Summable.of_nonneg_of_le hf_nonneg hle hs_major
  exact hs_f.tsum_ofReal_ne_top

/-- Moment-decay to tail-summability bridge:
    if `E[|Xₙ|^(2j)] ≤ K * (n+1)^(-β)` with `β > 1`, then
    `∑ μ{|Xₙ| ≥ a}` is finite for every fixed `a > 0`. -/
theorem tail_summable_of_moment_polynomial_decay
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {j : ℕ} (hj : 0 < j)
    {a : ℝ} (ha : 0 < a)
    {K β : ℝ} (hK : 0 ≤ K) (hβ : 1 < β)
    (hint : ∀ n : ℕ, Integrable (fun ω : Ω => |X n ω| ^ (2 * j)) μ)
    (hmoment :
      ∀ n : ℕ, ∫ ω : Ω, |X n ω| ^ (2 * j) ∂μ ≤ K * (↑(n + 1) : ℝ) ^ (-β)) :
    (∑' n : ℕ, μ {ω : Ω | a ≤ |X n ω|}) ≠ ⊤ := by
  let ε : ℕ → ℝ≥0∞ := fun n =>
    ENNReal.ofReal ((K / (a ^ (2 * j))) * (↑(n + 1) : ℝ) ^ (-β))
  have hdom :
      ∀ n : ℕ, μ {ω : Ω | a ≤ |X n ω|} ≤ ε n := by
    intro n
    have hbase :=
      higher_moment_markov_ennreal (μ := μ) (X := X n) (j := j) hj (a := a) ha (hint n)
    have hdiv :
        (∫ ω : Ω, |X n ω| ^ (2 * j) ∂μ) / (a ^ (2 * j))
          ≤ (K / (a ^ (2 * j))) * (↑(n + 1) : ℝ) ^ (-β) := by
      calc
        (∫ ω : Ω, |X n ω| ^ (2 * j) ∂μ) / (a ^ (2 * j))
            ≤ (K * (↑(n + 1) : ℝ) ^ (-β)) / (a ^ (2 * j)) :=
              div_le_div_of_nonneg_right (hmoment n) (pow_nonneg (le_of_lt ha) _)
        _ = (K / (a ^ (2 * j))) * (↑(n + 1) : ℝ) ^ (-β) := by
              field_simp [pow_ne_zero _ ha.ne']
    exact (hbase.trans (ENNReal.ofReal_le_ofReal hdiv)).trans_eq (by simp [ε])
  have hεsum : (∑' n : ℕ, ε n) ≠ ⊤ := by
    change (∑' n : ℕ, ENNReal.ofReal ((K / (a ^ (2 * j))) * (↑(n + 1) : ℝ) ^ (-β))) ≠ ⊤
    exact tsum_ofReal_ne_top_of_polynomial_decay
      (hα := hβ)
      (hf_nonneg := fun n =>
        mul_nonneg
          (div_nonneg hK (pow_nonneg (le_of_lt ha) _))
          (by positivity))
      (hle := fun n => le_rfl)
  exact ne_top_of_le_ne_top hεsum (ENNReal.tsum_le_tsum hdom)

/-- Summable shifted cutoff-to-limit deviation tails from polynomial-decay
    squared-moment bounds.
    If `E[(interactionCutoff(κ_{n+1}) - interaction)^2]` decays like
    `(n+1)^(-β)` with `β > 1`, then the deviation bad-event probabilities
    `μ{ a ≤ |interactionCutoff(κ_{n+1}) - interaction| }` are summable. -/
theorem shifted_cutoff_interaction_deviation_bad_event_summable_of_sq_moment_polynomial_bound
    (params : Phi4Params) (Λ : Rectangle) (a : ℝ) (ha : 0 < a)
    (C β : ℝ) (hC : 0 ≤ C) (hβ : 1 < β)
    (hInt :
      ∀ n : ℕ,
        Integrable
          (fun ω : FieldConfig2D =>
            (interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hM :
      ∀ n : ℕ,
        ∫ ω : FieldConfig2D,
          (interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω) ^ 2
          ∂(freeFieldMeasure params.mass params.mass_pos)
        ≤ C * (↑(n + 1) : ℝ) ^ (-β)) :
    (∑' n : ℕ,
      (freeFieldMeasure params.mass params.mass_pos)
        {ω : FieldConfig2D |
          a ≤
            |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω -
              interaction params Λ ω|}) ≠ ⊤ := by
  let μ : Measure FieldConfig2D := freeFieldMeasure params.mass params.mass_pos
  let X : ℕ → FieldConfig2D → ℝ := fun n ω =>
    interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω
  letI : IsProbabilityMeasure μ := freeFieldMeasure_isProbability params.mass params.mass_pos
  have hintAbs : ∀ n : ℕ, Integrable (fun ω : FieldConfig2D => |X n ω| ^ (2 * (1 : ℕ))) μ := by
    intro n
    refine (hInt n).congr ?_
    filter_upwards with ω
    simp [X, pow_two]
  have hmomentAbs :
      ∀ n : ℕ, ∫ ω : FieldConfig2D, |X n ω| ^ (2 * (1 : ℕ)) ∂μ ≤
        C * (↑(n + 1) : ℝ) ^ (-β) := by
    intro n
    simpa [X, pow_two] using hM n
  simpa [μ, X] using
    (tail_summable_of_moment_polynomial_decay
      (μ := μ) (X := X) (j := 1) (hj := by decide)
      (a := a) ha (K := C) (β := β) hC hβ
      hintAbs hmomentAbs)

/-- Borel-Cantelli criterion for almost-sure convergence to `0`:
    if for every reciprocal threshold `1/(m+1)` the level-set events
    `{ω | 1/(m+1) ≤ |Xₙ ω|}` are summable in `n`, then `Xₙ → 0` a.e. -/
theorem ae_tendsto_zero_of_summable_level_sets_nat_inv
    (μ : Measure FieldConfig2D)
    (X : ℕ → FieldConfig2D → ℝ)
    (hsum :
      ∀ m : ℕ,
        (∑' n : ℕ, μ {ω : FieldConfig2D | (1 / (m + 1 : ℝ)) ≤ |X n ω|}) ≠ ∞) :
    ∀ᵐ ω ∂μ,
      Filter.Tendsto (fun n : ℕ => X n ω) Filter.atTop (nhds 0) := by
  have hsmall :
      ∀ m : ℕ,
        ∀ᵐ ω ∂μ, ∀ᶠ n in Filter.atTop, |X n ω| < (1 / (m + 1 : ℝ)) := by
    intro m
    have hnot :
        ∀ᵐ ω ∂μ,
          ∀ᶠ n in Filter.atTop,
            ω ∉ {ω : FieldConfig2D | (1 / (m + 1 : ℝ)) ≤ |X n ω|} :=
      MeasureTheory.ae_eventually_notMem
        (μ := μ)
        (s := fun n => {ω : FieldConfig2D | (1 / (m + 1 : ℝ)) ≤ |X n ω|})
        (hsum m)
    filter_upwards [hnot] with ω hω
    exact hω.mono (fun n hn => not_le.mp hn)
  have hall :
      ∀ᵐ ω ∂μ, ∀ m : ℕ, ∀ᶠ n in Filter.atTop, |X n ω| < (1 / (m + 1 : ℝ)) := by
    rw [ae_all_iff]
    exact hsmall
  filter_upwards [hall] with ω hω
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  rcases exists_nat_one_div_lt hε with ⟨m, hm⟩
  rcases Filter.eventually_atTop.1 (hω m) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hX : |X n ω| < (1 / (m + 1 : ℝ)) := hN n hn
  have hε' : |X n ω| < ε := lt_trans hX hm
  simpa [Real.dist_eq] using hε'

/-- Shifted canonical cutoff deviations converge to `0` almost surely from
    polynomial-decay squared-moment bounds. -/
theorem interactionCutoff_standardSeq_succ_tendsto_ae_of_sq_moment_polynomial_bound
    (params : Phi4Params) (Λ : Rectangle)
    (C β : ℝ) (hC : 0 ≤ C) (hβ : 1 < β)
    (hInt :
      ∀ n : ℕ,
        Integrable
          (fun ω : FieldConfig2D =>
            (interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hM :
      ∀ n : ℕ,
        ∫ ω : FieldConfig2D,
          (interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω) ^ 2
          ∂(freeFieldMeasure params.mass params.mass_pos)
        ≤ C * (↑(n + 1) : ℝ) ^ (-β)) :
    ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
      Filter.Tendsto
        (fun n : ℕ =>
          interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω)
        Filter.atTop
        (nhds 0) := by
  let μ : Measure FieldConfig2D := freeFieldMeasure params.mass params.mass_pos
  let X : ℕ → FieldConfig2D → ℝ := fun n ω =>
    interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω
  have hsum :
      ∀ m : ℕ,
        (∑' n : ℕ, μ {ω : FieldConfig2D | (1 / (m + 1 : ℝ)) ≤ |X n ω|}) ≠ ∞ := by
    intro m
    have hmpos : 0 < (1 / (m + 1 : ℝ)) := Nat.one_div_pos_of_nat
    simpa [μ, X] using
      shifted_cutoff_interaction_deviation_bad_event_summable_of_sq_moment_polynomial_bound
        (params := params) (Λ := Λ) (a := (1 / (m + 1 : ℝ))) hmpos
        (C := C) (β := β) hC hβ hInt hM
  simpa [μ, X] using
    ae_tendsto_zero_of_summable_level_sets_nat_inv (μ := μ) (X := X) hsum

/-- Construct `InteractionWeightModel` directly from:
    1) polynomial-decay squared-moment bounds for shifted cutoff deviations, and
    2) uniform shifted-cutoff real-integral exponential-moment bounds.
    This keeps the analytic inputs explicit while deriving the a.e. convergence
    needed by the Fatou `Lᵖ` route. -/
theorem interactionWeightModel_nonempty_of_sq_moment_polynomial_bound_and_uniform_integral_bound
    (params : Phi4Params)
    (C β : ℝ) (hC : 0 ≤ C) (hβ : 1 < β)
    (hInt :
      ∀ (Λ : Rectangle) (n : ℕ),
        Integrable
          (fun ω : FieldConfig2D =>
            (interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hM :
      ∀ (Λ : Rectangle) (n : ℕ),
        ∫ ω : FieldConfig2D,
          (interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω) ^ 2
          ∂(freeFieldMeasure params.mass params.mass_pos)
        ≤ C * (↑(n + 1) : ℝ) ^ (-β))
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (n : ℕ),
        AEStronglyMeasurable
          (fun ω : FieldConfig2D => interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)
          (freeFieldMeasure params.mass params.mass_pos))
    (hbound :
      ∀ (Λ : Rectangle) {p : ℝ≥0∞}, p ≠ ⊤ →
        ∃ D : ℝ,
          (∀ n : ℕ,
            Integrable
              (fun ω : FieldConfig2D =>
                Real.exp (-(p.toReal * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)))
              (freeFieldMeasure params.mass params.mass_pos)) ∧
          (∀ n : ℕ,
            ∫ ω : FieldConfig2D,
              Real.exp (-(p.toReal * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
              ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D)) :
    Nonempty (InteractionWeightModel params) := by
  have htend0 :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun n : ℕ =>
              interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω)
            Filter.atTop
            (nhds 0) := by
    intro Λ
    exact interactionCutoff_standardSeq_succ_tendsto_ae_of_sq_moment_polynomial_bound
      (params := params) (Λ := Λ) (C := C) (β := β) hC hβ (hInt Λ) (hM Λ)
  have htend :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun n : ℕ => interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)
            Filter.atTop
            (nhds (interaction params Λ ω)) := by
    intro Λ
    filter_upwards [htend0 Λ] with ω hω
    have hadd :
        Filter.Tendsto
          (fun n : ℕ =>
            (interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω) +
              interaction params Λ ω)
          Filter.atTop
          (nhds (interaction params Λ ω)) := by
      simpa [zero_add] using (hω.const_add (interaction params Λ ω))
    have heq :
        (fun n : ℕ =>
          (interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω) +
            interaction params Λ ω)
          =ᶠ[Filter.atTop]
        (fun n : ℕ => interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω) :=
      Filter.Eventually.of_forall (fun n => by
        simp [sub_eq_add_neg, add_comm])
    exact hadd.congr' heq
  exact interactionWeightModel_nonempty_of_standardSeq_succ_tendsto_ae_and_uniform_integral_bound
    (params := params) htend hcutoff_meas hbound

/-- Construct `InteractionWeightModel` directly from:
    1) polynomial-decay squared-moment bounds for shifted cutoff deviations, and
    2) per-exponent geometric shifted-cutoff real-integral bounds.
    This theorem converts geometric decay to the uniform-integral hypotheses
    required by
    `interactionWeightModel_nonempty_of_sq_moment_polynomial_bound_and_uniform_integral_bound`.
    Compatibility endpoint: prefer
    `interactionWeightModel_nonempty_of_sq_moment_polynomial_bound_and_geometric_exp_moment_bound`
    when assumptions are naturally stated for real exponents `q > 0`. -/
theorem interactionWeightModel_nonempty_of_sq_moment_polynomial_bound_and_geometric_integral_bound
    (params : Phi4Params)
    (C β : ℝ) (hC : 0 ≤ C) (hβ : 1 < β)
    (hInt :
      ∀ (Λ : Rectangle) (n : ℕ),
        Integrable
          (fun ω : FieldConfig2D =>
            (interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hM :
      ∀ (Λ : Rectangle) (n : ℕ),
        ∫ ω : FieldConfig2D,
          (interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω) ^ 2
          ∂(freeFieldMeasure params.mass params.mass_pos)
        ≤ C * (↑(n + 1) : ℝ) ^ (-β))
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (n : ℕ),
        AEStronglyMeasurable
          (fun ω : FieldConfig2D => interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)
          (freeFieldMeasure params.mass params.mass_pos))
    (hgeom :
      ∀ (Λ : Rectangle) {p : ℝ≥0∞}, p ≠ ⊤ →
        ∃ D r : ℝ,
          0 ≤ D ∧ 0 ≤ r ∧ r < 1 ∧
          (∀ n : ℕ,
            Integrable
              (fun ω : FieldConfig2D =>
                Real.exp (-(p.toReal * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)))
              (freeFieldMeasure params.mass params.mass_pos)) ∧
          (∀ n : ℕ,
            ∫ ω : FieldConfig2D,
              Real.exp (-(p.toReal * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
              ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D * r ^ n)) :
    Nonempty (InteractionWeightModel params) := by
  have htend :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun n : ℕ => interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)
            Filter.atTop
            (nhds (interaction params Λ ω)) := by
    intro Λ
    have htend0 :=
      interactionCutoff_standardSeq_succ_tendsto_ae_of_sq_moment_polynomial_bound
        (params := params) (Λ := Λ) (C := C) (β := β) hC hβ (hInt Λ) (hM Λ)
    filter_upwards [htend0] with ω hω
    have hadd :
        Filter.Tendsto
          (fun n : ℕ =>
            (interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω) +
              interaction params Λ ω)
          Filter.atTop
          (nhds (interaction params Λ ω)) := by
      simpa [zero_add] using (hω.const_add (interaction params Λ ω))
    have heq :
        (fun n : ℕ =>
          (interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω) +
            interaction params Λ ω)
          =ᶠ[Filter.atTop]
        (fun n : ℕ => interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω) :=
      Filter.Eventually.of_forall (fun n => by
        simp [sub_eq_add_neg, add_comm])
    exact hadd.congr' heq
  exact
    interactionWeightModel_nonempty_of_standardSeq_succ_tendsto_ae_and_geometric_integral_bound
      (params := params) htend hcutoff_meas hgeom

/-- Construct `InteractionWeightModel` directly from:
    1) polynomial-decay squared-moment bounds for shifted cutoff deviations, and
    2) per-exponent geometric shifted-cutoff real-parameter exponential-moment
    bounds for each `q > 0`.
    This keeps the Glimm-Jaffe 8.6.2 input shape explicit while avoiding
    geometric assumptions at `p = 0`. -/
theorem interactionWeightModel_nonempty_of_sq_moment_polynomial_bound_and_geometric_exp_moment_bound
    (params : Phi4Params)
    (C β : ℝ) (hC : 0 ≤ C) (hβ : 1 < β)
    (hInt :
      ∀ (Λ : Rectangle) (n : ℕ),
        Integrable
          (fun ω : FieldConfig2D =>
            (interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hM :
      ∀ (Λ : Rectangle) (n : ℕ),
        ∫ ω : FieldConfig2D,
          (interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω) ^ 2
          ∂(freeFieldMeasure params.mass params.mass_pos)
        ≤ C * (↑(n + 1) : ℝ) ^ (-β))
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (n : ℕ),
        AEStronglyMeasurable
          (fun ω : FieldConfig2D => interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)
          (freeFieldMeasure params.mass params.mass_pos))
    (hgeom :
      ∀ (Λ : Rectangle) (q : ℝ), 0 < q →
        ∃ D r : ℝ,
          0 ≤ D ∧ 0 ≤ r ∧ r < 1 ∧
          (∀ n : ℕ,
            Integrable
              (fun ω : FieldConfig2D =>
                Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)))
              (freeFieldMeasure params.mass params.mass_pos)) ∧
          (∀ n : ℕ,
            ∫ ω : FieldConfig2D,
              Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
              ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D * r ^ n)) :
    Nonempty (InteractionWeightModel params) := by
  refine interactionWeightModel_nonempty_of_sq_moment_polynomial_bound_and_uniform_integral_bound
    (params := params) (C := C) (β := β) hC hβ hInt hM hcutoff_meas ?_
  intro Λ p hpTop
  by_cases hp0 : p = 0
  · refine ⟨1, ?_, ?_⟩
    · intro n
      let μ : Measure FieldConfig2D := freeFieldMeasure params.mass params.mass_pos
      letI : IsProbabilityMeasure μ := freeFieldMeasure_isProbability params.mass params.mass_pos
      simpa [μ, hp0] using
        (integrable_const (1 : ℝ) : Integrable (fun _ : FieldConfig2D => (1 : ℝ)) μ)
    · intro n
      let μ : Measure FieldConfig2D := freeFieldMeasure params.mass params.mass_pos
      letI : IsProbabilityMeasure μ := freeFieldMeasure_isProbability params.mass params.mass_pos
      have hlin :
          ∫ ω : FieldConfig2D,
            Real.exp (-(p.toReal * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
            ∂μ = 1 := by
        simp [hp0, μ]
      simpa [μ] using hlin.le
  · have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hpTop
    rcases hgeom Λ p.toReal hq with ⟨D, r, hD, hr0, hr1, hIntExp, hMExp⟩
    exact uniform_integral_bound_of_standardSeq_succ_geometric_integral_bound
      (params := params) (Λ := Λ) (q := p.toReal)
      (hgeom := ⟨D, r, hD, hr0, hr1, hIntExp, hMExp⟩)

/-- Deterministic linear-in-index lower bounds on shifted cutoffs imply
    geometric shifted-cutoff exponential-moment bounds:
    if `a * n - b ≤ interactionCutoff(κ_{n+1})` pointwise with `a > 0`, then
    `E[exp(-(q * interactionCutoff(κ_{n+1})))] ≤ exp(q*b) * exp(-q*a)^n`
    for every `q > 0`. -/
theorem standardSeq_succ_geometric_exp_moment_bound_of_linear_lower_bound
    (params : Phi4Params) (Λ : Rectangle) (q a b : ℝ)
    (hq : 0 < q) (ha : 0 < a)
    (hcutoff_meas :
      ∀ n : ℕ,
        AEStronglyMeasurable
          (fun ω : FieldConfig2D => interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)
          (freeFieldMeasure params.mass params.mass_pos))
    (hlin :
      ∀ (n : ℕ) (ω : FieldConfig2D),
        a * (n : ℝ) - b ≤ interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω) :
    ∃ D r : ℝ,
      0 ≤ D ∧ 0 ≤ r ∧ r < 1 ∧
      (∀ n : ℕ,
        Integrable
          (fun ω : FieldConfig2D =>
            Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)))
          (freeFieldMeasure params.mass params.mass_pos)) ∧
      (∀ n : ℕ,
        ∫ ω : FieldConfig2D,
          Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
          ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D * r ^ n) := by
  let μ : Measure FieldConfig2D := freeFieldMeasure params.mass params.mass_pos
  let D : ℝ := Real.exp (q * b)
  let r : ℝ := Real.exp (-q * a)
  have hD : 0 ≤ D := by
    positivity
  have hr0 : 0 ≤ r := by
    positivity
  have hr1 : r < 1 := by
    have hneg : -q * a < 0 := by nlinarith [hq, ha]
    simpa [r] using (Real.exp_lt_one_iff.mpr hneg)
  have hle :
      ∀ n : ℕ, ∀ ω : FieldConfig2D,
        Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
          ≤ D * r ^ n := by
    intro n ω
    have harg :
        -(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω) ≤
          q * b + (n : ℝ) * (-q * a) := by
      nlinarith [hlin n ω]
    have hexp : Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
        ≤ Real.exp (q * b + (n : ℝ) * (-q * a)) := (Real.exp_le_exp).2 harg
    have hrepr : Real.exp (q * b + (n : ℝ) * (-q * a)) = D * r ^ n := by
      calc
        Real.exp (q * b + (n : ℝ) * (-q * a))
            = Real.exp (q * b) * Real.exp ((n : ℝ) * (-q * a)) := by
              rw [Real.exp_add]
        _ = Real.exp (q * b) * (Real.exp (-q * a)) ^ n := by
              rw [Real.exp_nat_mul]
        _ = D * r ^ n := by simp [D, r]
    exact hexp.trans_eq hrepr
  have hInt :
      ∀ n : ℕ,
        Integrable
          (fun ω : FieldConfig2D =>
            Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)))
          μ := by
    intro n
    have hAe :
        AEStronglyMeasurable
          (fun ω : FieldConfig2D =>
            Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)))
          μ := by
      simpa [μ, mul_assoc, mul_comm, mul_left_comm] using
        (Real.continuous_exp.comp_aestronglyMeasurable ((hcutoff_meas n).const_mul (-q)))
    have hIntConst : Integrable (fun _ : FieldConfig2D => D * r ^ n) μ :=
      integrable_const _
    refine Integrable.mono' hIntConst hAe ?_
    filter_upwards with ω
    have hnonneg_rhs : 0 ≤ D * r ^ n := mul_nonneg hD (pow_nonneg hr0 n)
    simpa [Real.norm_of_nonneg (Real.exp_nonneg _), Real.norm_of_nonneg hnonneg_rhs] using hle n ω
  refine ⟨D, r, hD, hr0, hr1, hInt, ?_⟩
  intro n
  have hle_ae :
      (fun ω : FieldConfig2D =>
        Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)))
        ≤ᵐ[μ] (fun _ : FieldConfig2D => D * r ^ n) :=
    Filter.Eventually.of_forall (hle n)
  have hIntConst : Integrable (fun _ : FieldConfig2D => D * r ^ n) μ := integrable_const _
  have hmono := integral_mono_ae (hInt n) hIntConst hle_ae
  letI : IsProbabilityMeasure μ := freeFieldMeasure_isProbability params.mass params.mass_pos
  have hconst : ∫ _ω : FieldConfig2D, D * r ^ n ∂μ = D * r ^ n := by simp [μ]
  exact hmono.trans (by simpa [hconst])

/-- Construct `InteractionWeightModel` from explicit real-parameterized a.e.
    UV convergence, cutoff measurability data, and deterministic linear
    shifted-cutoff lower bounds in the canonical index:
    `a * n - b ≤ interactionCutoff(κ_{n+1})` with `a > 0`.
    This yields geometric exponential-moment decay constructively. -/
theorem interactionWeightModel_nonempty_of_tendsto_ae_and_linear_lower_bound
    (params : Phi4Params)
    (hcutoff_tendsto_ae :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
            Filter.atTop
            (nhds (interaction params Λ ω)))
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        AEStronglyMeasurable (interactionCutoff params Λ κ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hlin :
      ∀ Λ : Rectangle, ∃ a b : ℝ, 0 < a ∧
        ∀ (n : ℕ) (ω : FieldConfig2D),
          a * (n : ℝ) - b ≤ interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω) :
    Nonempty (InteractionWeightModel params) := by
  refine interactionWeightModel_nonempty_of_tendsto_ae_and_geometric_exp_moment_bound
    (params := params) hcutoff_tendsto_ae hcutoff_meas ?_
  intro Λ q hq
  rcases hlin Λ with ⟨a, b, ha, hlinΛ⟩
  exact standardSeq_succ_geometric_exp_moment_bound_of_linear_lower_bound
    (params := params) (Λ := Λ) (q := q) (a := a) (b := b) hq ha
    (hcutoff_meas := fun n => by
      simpa using hcutoff_meas Λ (standardUVCutoffSeq (n + 1)))
    hlinΛ

/-- If shifted-index squared cutoff-to-limit moments converge to `0`, then for
    every fixed threshold `a > 0`, the corresponding shifted bad-event
    probabilities
    `μ{ a ≤ |interactionCutoff(κ_{n+1}) - interaction| }`
    converge to `0` (Chebyshev + squeeze). -/
theorem tendsto_shifted_cutoff_interaction_deviation_bad_event_measure_zero_of_sq_moment
    (params : Phi4Params) (Λ : Rectangle) (a : ℝ) (ha : 0 < a)
    (hInt :
      ∀ n : ℕ,
        Integrable
          (fun ω : FieldConfig2D =>
            (interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hSq_tendsto :
      Filter.Tendsto
        (fun n : ℕ =>
          ∫ ω : FieldConfig2D,
            (interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω) ^ 2
            ∂(freeFieldMeasure params.mass params.mass_pos))
        Filter.atTop
        (nhds 0)) :
    Filter.Tendsto
      (fun n : ℕ =>
        (freeFieldMeasure params.mass params.mass_pos)
          {ω : FieldConfig2D |
            a ≤
              |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω -
                interaction params Λ ω|})
      Filter.atTop
      (nhds 0) := by
  let μ : Measure FieldConfig2D := freeFieldMeasure params.mass params.mass_pos
  let E : ℕ → ℝ := fun n =>
    ∫ ω : FieldConfig2D,
      (interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω) ^ 2 ∂μ
  let b : ℕ → ENNReal := fun n =>
    ENNReal.ofReal (E n / (a ^ 2))
  have hle :
      ∀ n : ℕ,
        μ {ω : FieldConfig2D |
            a ≤
              |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω -
                interaction params Λ ω|}
          ≤ b n := by
    intro n
    simpa [μ, E, b] using
      shifted_cutoff_interaction_deviation_bad_event_measure_le_of_sq_moment
        (params := params) (Λ := Λ) (a := a) ha n (hInt n)
  have hb_tendsto : Filter.Tendsto b Filter.atTop (nhds 0) := by
    have hratio :
        Filter.Tendsto (fun n : ℕ => E n / (a ^ 2)) Filter.atTop (nhds 0) := by
      simpa [E] using hSq_tendsto.div_const (a ^ 2)
    have htmp :
        Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (E n / (a ^ 2)))
          Filter.atTop (nhds (ENNReal.ofReal 0)) :=
      (ENNReal.continuous_ofReal.tendsto 0).comp hratio
    simpa [b] using htmp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_const_nhds) hb_tendsto ?_ ?_
  · intro n
    exact bot_le
  · intro n
    exact hle n

/-- If the real-parameterized L² cutoff convergence hypothesis holds and the
    shifted cutoff-to-limit squared deviations are integrable, then for every
    fixed threshold `a > 0` the shifted bad-event probabilities
    `μ{ a ≤ |interactionCutoff(κ_{n+1}) - interaction| }` converge to `0`. -/
theorem tendsto_shifted_cutoff_interaction_deviation_bad_event_measure_zero_of_converges_L2
    (params : Phi4Params) (Λ : Rectangle) (a : ℝ) (ha : 0 < a)
    (hInt :
      ∀ n : ℕ,
        Integrable
          (fun ω : FieldConfig2D =>
            (interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_conv :
      Filter.Tendsto
        (fun (κ : ℝ) => if h : 0 < κ then
          ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
            ∂(freeFieldMeasure params.mass params.mass_pos)
          else 0)
        Filter.atTop
        (nhds 0)) :
    Filter.Tendsto
      (fun n : ℕ =>
        (freeFieldMeasure params.mass params.mass_pos)
          {ω : FieldConfig2D |
            a ≤
              |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω -
                interaction params Λ ω|})
      Filter.atTop
      (nhds 0) := by
  exact tendsto_shifted_cutoff_interaction_deviation_bad_event_measure_zero_of_sq_moment
    (params := params) (Λ := Λ) (a := a) ha hInt
    (shifted_cutoff_interaction_sq_moment_tendsto_zero_of_converges_L2
      (params := params) (Λ := Λ) hcutoff_conv)

/-- Shifted-index cutoff bad-event bound from exponential moments (Chernoff):
    for `θ > 0`,
    `μ{interactionCutoff(κ_{n+1}) < -B} ≤ exp(-θ B) * E[exp(-θ interactionCutoff(κ_{n+1}))]`.
    This is a reusable bridge from moment control to bad-event tails. -/
theorem shifted_cutoff_bad_event_measure_le_of_exponential_moment
    (params : Phi4Params) (Λ : Rectangle) (B θ : ℝ) (hθ : 0 < θ) (n : ℕ)
    (hInt :
      Integrable
        (fun ω : FieldConfig2D =>
          Real.exp ((-θ) * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
        (freeFieldMeasure params.mass params.mass_pos)) :
    (freeFieldMeasure params.mass params.mass_pos)
      {ω : FieldConfig2D |
        interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω < -B}
      ≤ ENNReal.ofReal
          (Real.exp (-θ * B) *
            ∫ ω : FieldConfig2D,
              Real.exp ((-θ) * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)
                ∂(freeFieldMeasure params.mass params.mass_pos)) := by
  let μ : Measure FieldConfig2D := freeFieldMeasure params.mass params.mass_pos
  let X : FieldConfig2D → ℝ :=
    fun ω => interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω
  letI : IsProbabilityMeasure μ := freeFieldMeasure_isProbability params.mass params.mass_pos
  have hchernoff :
      μ.real {ω : FieldConfig2D | X ω ≤ -B} ≤
        Real.exp (-(-θ) * (-B)) * ProbabilityTheory.mgf X μ (-θ) := by
    exact ProbabilityTheory.measure_le_le_exp_mul_mgf
      (μ := μ) (X := X) (ε := -B) (t := -θ) (ht := by linarith) hInt
  have hchernoff' :
      μ.real {ω : FieldConfig2D | X ω ≤ -B} ≤
        Real.exp (-θ * B) *
          ∫ ω : FieldConfig2D, Real.exp ((-θ) * X ω) ∂μ := by
    simpa [ProbabilityTheory.mgf, X, μ, mul_comm, mul_left_comm, mul_assoc] using hchernoff
  have hreal :
      (μ {ω : FieldConfig2D | X ω ≤ -B}).toReal ≤
        Real.exp (-θ * B) *
          ∫ ω : FieldConfig2D, Real.exp ((-θ) * X ω) ∂μ := by
    simpa [Measure.real, μ] using hchernoff'
  have hrhs_nonneg :
      0 ≤ Real.exp (-θ * B) *
        ∫ ω : FieldConfig2D, Real.exp ((-θ) * X ω) ∂μ := by
    refine mul_nonneg (Real.exp_nonneg _) ?_
    exact integral_nonneg (fun _ => Real.exp_nonneg _)
  have hle_le :
      μ {ω : FieldConfig2D | X ω ≤ -B} ≤
        ENNReal.ofReal
          (Real.exp (-θ * B) *
            ∫ ω : FieldConfig2D, Real.exp ((-θ) * X ω) ∂μ) := by
    exact (ENNReal.le_ofReal_iff_toReal_le (ha := measure_ne_top μ _) (hb := hrhs_nonneg)).2 hreal
  have hsubset :
      {ω : FieldConfig2D | X ω < -B} ⊆ {ω : FieldConfig2D | X ω ≤ -B} := by
    intro ω hω
    exact le_of_lt (by simpa using hω)
  exact (measure_mono hsubset).trans hle_le

/-- Shifted-index cutoff bad-event majorant from exponential moments:
    if `E[exp(-θ interactionCutoff(κ_{n+1}))] ≤ Mₙ`, then
    `μ{interactionCutoff(κ_{n+1}) < -B} ≤ exp(-θ B) * Mₙ`. -/
theorem shifted_cutoff_bad_event_measure_le_of_exponential_moment_bound
    (params : Phi4Params) (Λ : Rectangle) (B θ : ℝ) (hθ : 0 < θ)
    (M : ℕ → ℝ)
    (hInt :
      ∀ n : ℕ,
        Integrable
          (fun ω : FieldConfig2D =>
            Real.exp ((-θ) * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
          (freeFieldMeasure params.mass params.mass_pos))
    (hM :
      ∀ n : ℕ,
        ∫ ω : FieldConfig2D,
          Real.exp ((-θ) * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)
          ∂(freeFieldMeasure params.mass params.mass_pos) ≤ M n) :
    ∀ n : ℕ,
      (freeFieldMeasure params.mass params.mass_pos)
        {ω : FieldConfig2D |
          interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω < -B}
        ≤ ENNReal.ofReal (Real.exp (-θ * B) * M n) := by
  intro n
  have hbase :=
    shifted_cutoff_bad_event_measure_le_of_exponential_moment
      (params := params) (Λ := Λ) (B := B) (θ := θ) hθ n (hInt n)
  have hmul :
      Real.exp (-θ * B) *
          ∫ ω : FieldConfig2D,
            Real.exp ((-θ) * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)
              ∂(freeFieldMeasure params.mass params.mass_pos)
        ≤ Real.exp (-θ * B) * M n := by
    exact mul_le_mul_of_nonneg_left (hM n) (Real.exp_nonneg _)
  exact hbase.trans (ENNReal.ofReal_le_ofReal hmul)

/-- Shifted-index cutoff bad-event majorant from absolute exponential moments:
    if `E[exp(θ |interactionCutoff(κ_{n+1})|)] ≤ Mₙ`, then
    `μ{interactionCutoff(κ_{n+1}) < -B} ≤ exp(-θ B) * Mₙ`. -/
theorem shifted_cutoff_bad_event_measure_le_of_exponential_moment_abs_bound
    (params : Phi4Params) (Λ : Rectangle) (B θ : ℝ) (hθ : 0 < θ)
    [InteractionUVModel params]
    (M : ℕ → ℝ)
    (hIntAbs :
      ∀ n : ℕ,
        Integrable
          (fun ω : FieldConfig2D =>
            Real.exp (θ * |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω|))
          (freeFieldMeasure params.mass params.mass_pos))
    (hM :
      ∀ n : ℕ,
        ∫ ω : FieldConfig2D,
          Real.exp (θ * |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω|)
          ∂(freeFieldMeasure params.mass params.mass_pos) ≤ M n) :
    ∀ n : ℕ,
      (freeFieldMeasure params.mass params.mass_pos)
        {ω : FieldConfig2D |
          interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω < -B}
        ≤ ENNReal.ofReal (Real.exp (-θ * B) * M n) := by
  intro n
  let μ : Measure FieldConfig2D := freeFieldMeasure params.mass params.mass_pos
  let X : FieldConfig2D → ℝ :=
    fun ω => interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω
  have hXae : AEStronglyMeasurable X μ := by
    simpa [X, μ] using
      (interactionCutoff_in_L2 params Λ (standardUVCutoffSeq (n + 1))).aestronglyMeasurable
  have hAeExpNeg : AEStronglyMeasurable (fun ω => Real.exp ((-θ) * X ω)) μ := by
    exact Real.continuous_exp.comp_aestronglyMeasurable (hXae.const_mul (-θ))
  have hIntNeg : Integrable (fun ω => Real.exp ((-θ) * X ω)) μ := by
    refine Integrable.mono' (hIntAbs n) hAeExpNeg ?_
    filter_upwards with ω
    have hArg : (-θ) * X ω ≤ θ * |X ω| := by
      have hmul : θ * (-X ω) ≤ θ * |X ω| :=
        mul_le_mul_of_nonneg_left (neg_le_abs (X ω)) (le_of_lt hθ)
      nlinarith
    have hExp : Real.exp ((-θ) * X ω) ≤ Real.exp (θ * |X ω|) :=
      (Real.exp_le_exp).2 hArg
    simpa [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)] using hExp
  have hIntBound :
      ∫ ω : FieldConfig2D, Real.exp ((-θ) * X ω) ∂μ ≤ M n := by
    have hle_ae :
        (fun ω => Real.exp ((-θ) * X ω)) ≤ᵐ[μ]
          (fun ω => Real.exp (θ * |X ω|)) := by
      filter_upwards with ω
      exact (Real.exp_le_exp).2 (by
        have hmul : θ * (-X ω) ≤ θ * |X ω| :=
          mul_le_mul_of_nonneg_left (neg_le_abs (X ω)) (le_of_lt hθ)
        nlinarith)
    exact (integral_mono_ae hIntNeg (hIntAbs n) hle_ae).trans (hM n)
  have hbase :=
    shifted_cutoff_bad_event_measure_le_of_exponential_moment
      (params := params) (Λ := Λ) (B := B) (θ := θ) hθ n hIntNeg
  have hmul :
      Real.exp (-θ * B) *
          ∫ ω : FieldConfig2D, Real.exp ((-θ) * X ω) ∂μ
        ≤ Real.exp (-θ * B) * M n := by
    exact mul_le_mul_of_nonneg_left hIntBound (Real.exp_nonneg _)
  exact hbase.trans (by
    simpa [X, μ] using ENNReal.ofReal_le_ofReal hmul)

/-- Shifted-index geometric bad-event tails from geometric decay of exponential
    moments of the cutoff interaction sequence:
    if `E[exp(-θ interactionCutoff(κ_{n+1}))] ≤ D * r^n` with `r < 1`,
    then `μ{interactionCutoff(κ_{n+1}) < -B}` is bounded by a geometric tail. -/
theorem shifted_cutoff_bad_event_geometric_bound_of_exponential_moment_bound
    (params : Phi4Params) (Λ : Rectangle) (B θ D r : ℝ)
    (hθ : 0 < θ) (hD : 0 ≤ D) (hr0 : 0 ≤ r)
    (hInt :
      ∀ n : ℕ,
        Integrable
          (fun ω : FieldConfig2D =>
            Real.exp ((-θ) * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
          (freeFieldMeasure params.mass params.mass_pos))
    (hM :
      ∀ n : ℕ,
        ∫ ω : FieldConfig2D,
          Real.exp ((-θ) * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)
          ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D * r ^ n) :
    ∀ n : ℕ,
      (freeFieldMeasure params.mass params.mass_pos)
        {ω : FieldConfig2D |
          interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω < -B}
        ≤ ENNReal.ofReal (Real.exp (-θ * B) * D) * (ENNReal.ofReal r) ^ n := by
  intro n
  have hbase :=
    shifted_cutoff_bad_event_measure_le_of_exponential_moment_bound
      (params := params) (Λ := Λ) (B := B) (θ := θ) hθ
      (M := fun k => D * r ^ k) hInt hM n
  have hrepr :
      ENNReal.ofReal (Real.exp (-θ * B) * (D * r ^ n)) =
        ENNReal.ofReal (Real.exp (-θ * B) * D) * (ENNReal.ofReal r) ^ n := by
    have hA : 0 ≤ Real.exp (-θ * B) * D := mul_nonneg (Real.exp_nonneg _) hD
    calc
      ENNReal.ofReal (Real.exp (-θ * B) * (D * r ^ n))
          = ENNReal.ofReal ((Real.exp (-θ * B) * D) * r ^ n) := by ring_nf
      _ = ENNReal.ofReal (Real.exp (-θ * B) * D) * ENNReal.ofReal (r ^ n) := by
            rw [ENNReal.ofReal_mul hA]
      _ = ENNReal.ofReal (Real.exp (-θ * B) * D) * (ENNReal.ofReal r) ^ n := by
            rw [ENNReal.ofReal_pow hr0]
  have hrewrite :
      ENNReal.ofReal (Real.exp (-θ * B) * (D * r ^ n)) ≤
        ENNReal.ofReal (Real.exp (-θ * B) * D) * (ENNReal.ofReal r) ^ n := by
    exact hrepr.le
  exact hbase.trans hrewrite

/-- Shifted-index geometric bad-event tails from geometric decay of absolute
    exponential moments of the cutoff interaction sequence:
    if `E[exp(θ |interactionCutoff(κ_{n+1})|)] ≤ D * r^n`, then
    `μ{interactionCutoff(κ_{n+1}) < -B}` is bounded by a geometric tail. -/
theorem shifted_cutoff_bad_event_geometric_bound_of_exponential_moment_abs_bound
    (params : Phi4Params) (Λ : Rectangle) (B θ D r : ℝ)
    (hθ : 0 < θ) (hD : 0 ≤ D) (hr0 : 0 ≤ r)
    [InteractionUVModel params]
    (hIntAbs :
      ∀ n : ℕ,
        Integrable
          (fun ω : FieldConfig2D =>
            Real.exp (θ * |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω|))
          (freeFieldMeasure params.mass params.mass_pos))
    (hM :
      ∀ n : ℕ,
        ∫ ω : FieldConfig2D,
          Real.exp (θ * |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω|)
          ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D * r ^ n) :
    ∀ n : ℕ,
      (freeFieldMeasure params.mass params.mass_pos)
        {ω : FieldConfig2D |
          interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω < -B}
        ≤ ENNReal.ofReal (Real.exp (-θ * B) * D) * (ENNReal.ofReal r) ^ n := by
  intro n
  have hbase :=
    shifted_cutoff_bad_event_measure_le_of_exponential_moment_abs_bound
      (params := params) (Λ := Λ) (B := B) (θ := θ) hθ
      (M := fun k => D * r ^ k) hIntAbs hM n
  have hrepr :
      ENNReal.ofReal (Real.exp (-θ * B) * (D * r ^ n)) =
        ENNReal.ofReal (Real.exp (-θ * B) * D) * (ENNReal.ofReal r) ^ n := by
    have hA : 0 ≤ Real.exp (-θ * B) * D := mul_nonneg (Real.exp_nonneg _) hD
    calc
      ENNReal.ofReal (Real.exp (-θ * B) * (D * r ^ n))
          = ENNReal.ofReal ((Real.exp (-θ * B) * D) * r ^ n) := by ring_nf
      _ = ENNReal.ofReal (Real.exp (-θ * B) * D) * ENNReal.ofReal (r ^ n) := by
            rw [ENNReal.ofReal_mul hA]
      _ = ENNReal.ofReal (Real.exp (-θ * B) * D) * (ENNReal.ofReal r) ^ n := by
            rw [ENNReal.ofReal_pow hr0]
  exact hbase.trans (by simpa [hrepr] using hrepr.le)

/-- Global shifted-index geometric bad-event tails from per-volume geometric
    decay of shifted-index exponential moments of cutoff interactions.
    This packages the Chernoff + moment-decay bridge at the canonical threshold
    `B = 0`. -/
theorem
    shifted_cutoff_bad_event_geometric_bound_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
    (params : Phi4Params)
    (hmom :
      ∀ Λ : Rectangle, ∃ θ D r : ℝ,
        0 < θ ∧ 0 ≤ D ∧ 0 ≤ r ∧ r < 1 ∧
        (∀ n : ℕ,
          Integrable
            (fun ω : FieldConfig2D =>
              Real.exp ((-θ) * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
            (freeFieldMeasure params.mass params.mass_pos)) ∧
        (∀ n : ℕ,
          ∫ ω : FieldConfig2D,
            Real.exp ((-θ) * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)
            ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D * r ^ n)) :
    ∀ Λ : Rectangle, ∃ C r : ℝ≥0∞,
      C ≠ ⊤ ∧ r < 1 ∧
      (∀ n : ℕ,
        (freeFieldMeasure params.mass params.mass_pos)
          {ω : FieldConfig2D |
            interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω < 0} ≤ C * r ^ n) := by
  intro Λ
  rcases hmom Λ with ⟨θ, D, r, hθ, hD, hr0, hr1, hInt, hM⟩
  refine ⟨ENNReal.ofReal (Real.exp 0 * D), ENNReal.ofReal r, ?_, ?_, ?_⟩
  · simp
  · exact (ENNReal.ofReal_lt_one).2 hr1
  · intro n
    simpa [Real.exp_zero] using
      (shifted_cutoff_bad_event_geometric_bound_of_exponential_moment_bound
        (params := params) (Λ := Λ) (B := 0) (θ := θ) (D := D) (r := r)
        hθ hD hr0 hInt hM n)

/-- `Lᵖ` integrability from shifted-index summable bad sets with good-set
    cutoff lower bounds, given explicit measurability of `interaction` and
    explicit a.e. convergence of the canonical cutoff sequence. -/
theorem
    exp_interaction_Lp_of_cutoff_seq_shifted_bad_set_summable_of_aestronglyMeasurable_and_standardSeq_tendsto_ae
    (params : Phi4Params) (Λ : Rectangle)
    (hinteraction_meas :
      AEStronglyMeasurable (interaction params Λ)
        (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_tendsto_ae :
      ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
        Filter.Tendsto
          (fun n : ℕ => interactionCutoff params Λ (standardUVCutoffSeq n) ω)
          Filter.atTop
          (nhds (interaction params Λ ω)))
    (B : ℝ)
    (bad : ℕ → Set FieldConfig2D)
    (hbad_sum :
      (∑' n : ℕ,
        (freeFieldMeasure params.mass params.mass_pos) (bad n)) ≠ ∞)
    (hcutoff_good :
      ∀ n : ℕ, ∀ ω : FieldConfig2D, ω ∉ bad n →
        -B ≤ interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)
    {p : ℝ≥0∞} :
    MemLp (fun ω => Real.exp (-(interaction params Λ ω)))
      p (freeFieldMeasure params.mass params.mass_pos) := by
  have hcutoff_ev :
      ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
        ∀ᶠ n in Filter.atTop,
          -B ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω :=
    cutoff_seq_eventually_lower_bound_of_shifted_bad_set_summable
      params Λ B bad hbad_sum hcutoff_good
  exact
    exp_interaction_Lp_of_cutoff_seq_eventually_lower_bound_of_aestronglyMeasurable_and_standardSeq_tendsto_ae
      (params := params) (Λ := Λ)
      hinteraction_meas hcutoff_tendsto_ae (B := B) hcutoff_ev

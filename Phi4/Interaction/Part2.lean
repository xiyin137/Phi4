/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.Interaction.Part1Tail

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

/-- Shifted-index variant of
    `cutoff_seq_eventually_lower_bound_of_summable_bad_event_bound`:
    summable majorants on `{interactionCutoff(κ_{n+1}) < -B}` imply eventual
    almost-sure lower bounds for the canonical cutoff sequence. -/
theorem cutoff_seq_eventually_lower_bound_of_shifted_summable_bad_event_bound
    (params : Phi4Params) (Λ : Rectangle) (B : ℝ)
    (ε : ℕ → ℝ≥0∞)
    (hε_sum : (∑' n : ℕ, ε n) ≠ ∞)
    (hbad_le :
      ∀ n : ℕ,
        (freeFieldMeasure params.mass params.mass_pos)
          {ω : FieldConfig2D |
            interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω < -B} ≤ ε n) :
    ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
      ∀ᶠ n in Filter.atTop,
        -B ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω := by
  have hbad_sum :
      (∑' n : ℕ,
        (freeFieldMeasure params.mass params.mass_pos)
          {ω : FieldConfig2D |
            interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω < -B}) ≠ ∞ :=
    ne_top_of_le_ne_top hε_sum (ENNReal.tsum_le_tsum hbad_le)
  refine cutoff_seq_eventually_lower_bound_of_shifted_bad_set_summable
    (params := params) (Λ := Λ) (B := B)
    (bad := fun n => {ω : FieldConfig2D |
      interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω < -B})
    hbad_sum ?_
  intro n ω hω
  exact not_lt.mp hω

/-- Shifted-index geometric bad-event tails imply eventual almost-sure lower
    bounds for the canonical cutoff sequence. -/
theorem cutoff_seq_eventually_lower_bound_of_shifted_geometric_bad_event_bound
    (params : Phi4Params) (Λ : Rectangle) (B : ℝ)
    (C r : ℝ≥0∞) (hC : C ≠ ⊤) (hr : r < 1)
    (hbad_le :
      ∀ n : ℕ,
        (freeFieldMeasure params.mass params.mass_pos)
          {ω : FieldConfig2D |
            interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω < -B} ≤ C * r ^ n) :
    ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
      ∀ᶠ n in Filter.atTop,
        -B ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω := by
  have hgeom_lt : (∑' n : ℕ, r ^ n) < ∞ :=
    (tsum_geometric_lt_top).2 hr
  have hsum_lt : (∑' n : ℕ, C * r ^ n) < ∞ := by
    have hC_lt : C < ∞ := by exact lt_of_le_of_ne le_top hC
    rw [ENNReal.tsum_mul_left]
    exact ENNReal.mul_lt_top hC_lt hgeom_lt
  exact cutoff_seq_eventually_lower_bound_of_shifted_summable_bad_event_bound
    params Λ B (fun n => C * r ^ n) (ne_of_lt hsum_lt) hbad_le

/-- Eventual cutoff nonnegativity from geometric decay of shifted-index
    exponential moments of cutoff interactions on a fixed volume. -/
theorem cutoff_seq_eventually_nonneg_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
    (params : Phi4Params) (Λ : Rectangle)
    (hmom :
      ∃ θ D r : ℝ,
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
    ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
      ∀ᶠ n in Filter.atTop,
        0 ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω := by
  rcases hmom with ⟨θ, D, r, hθ, hD, hr0, hr1, hInt, hM⟩
  have hbad_le :
      ∀ n : ℕ,
        (freeFieldMeasure params.mass params.mass_pos)
          {ω : FieldConfig2D |
            interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω < 0}
          ≤ ENNReal.ofReal (Real.exp 0 * D) * (ENNReal.ofReal r) ^ n := by
    simpa [Real.exp_zero] using
      (shifted_cutoff_bad_event_geometric_bound_of_exponential_moment_bound
        (params := params) (Λ := Λ) (B := 0) (θ := θ) (D := D) (r := r)
        hθ hD hr0 hInt hM)
  have hcutoff_ev :
      ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
        ∀ᶠ n in Filter.atTop,
          -0 ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω :=
    cutoff_seq_eventually_lower_bound_of_shifted_geometric_bad_event_bound
      (params := params) (Λ := Λ) (B := 0)
      (C := ENNReal.ofReal (Real.exp 0 * D)) (r := ENNReal.ofReal r)
      (hC := by simp)
      (hr := (ENNReal.ofReal_lt_one).2 hr1)
      (by simpa using hbad_le)
  simpa using hcutoff_ev

/-- Almost-everywhere nonnegativity of the limiting interaction from geometric
    decay of shifted-index exponential moments of cutoff interactions, given
    explicit a.e. convergence of the canonical cutoff sequence. -/
theorem
    interaction_ae_nonneg_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound_of_standardSeq_tendsto_ae
    (params : Phi4Params) (Λ : Rectangle)
    (htend :
      ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
        Filter.Tendsto
          (fun n : ℕ => interactionCutoff params Λ (standardUVCutoffSeq n) ω)
          Filter.atTop
          (nhds (interaction params Λ ω)))
    (hmom :
      ∃ θ D r : ℝ,
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
    ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
      0 ≤ interaction params Λ ω := by
  have hcutoff_ev :=
    cutoff_seq_eventually_nonneg_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
      (params := params) (Λ := Λ) hmom
  have hcutoff_ev_neg :
      ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
        ∀ᶠ n in Filter.atTop,
          -0 ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω := by
    simpa using hcutoff_ev
  have hinteraction :
      ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
        -0 ≤ interaction params Λ ω :=
    interaction_ae_lower_bound_of_cutoff_seq_eventually_of_standardSeq_tendsto_ae
      (params := params) (Λ := Λ) (B := 0) htend hcutoff_ev_neg
  simpa using hinteraction

/-! ## Old route theorems removed

The following theorems were removed because they relied on mathematically
impossible hypotheses (geometric decay of absolute exponential moments for
4th-chaos random variables):

- `shifted_exponential_moment_geometric_bound_of_abs_at_theta`
- `exp_interaction_Lp_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound_of_aestronglyMeasurable_and_standardSeq_tendsto_ae`
- `exp_interaction_Lp_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_moment_geometric_bound`
- `exp_interaction_Lp_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_moment_abs_geometric_bound`

The correct endpoint is now in `AnalyticInputs.lean` via `hasExpInteractionLp_of_analytic_inputs`,
which uses Nelson's uniform *negative* exponential moment bound (Fatou route).
See `test/proofideas_nelson_bound.lean` for the proof strategy analysis. -/

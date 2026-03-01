/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.Interaction.Part2

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

/-- Construct `InteractionWeightModel` from geometric decay of shifted-index
    exponential moments of the cutoff interaction:
    `E[exp(-θ interactionCutoff(κ_{n+1}))] ≤ D * r^n` with `r < 1`. -/
theorem interactionWeightModel_nonempty_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
    (params : Phi4Params)
    [InteractionUVModel params]
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
    Nonempty (InteractionWeightModel params) := by
  exact
    interactionWeightModel_nonempty_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound_of_aestronglyMeasurable_and_standardSeq_tendsto_ae
      (params := params)
      (hinteraction_meas := fun Λ => (interaction_in_L2 params Λ).aestronglyMeasurable)
      (hcutoff_tendsto_ae := fun Λ => interactionCutoff_standardSeq_tendsto_ae params Λ)
      hmom

/-- Construct `InteractionWeightModel` from geometric decay of shifted-index
    absolute exponential moments of cutoff interactions:
    `E[exp(θ |interactionCutoff(κ_{n+1})|)] ≤ D * r^n` with `r < 1`. -/
theorem interactionWeightModel_nonempty_of_uv_cutoff_seq_shifted_exponential_moment_abs_geometric_bound
    (params : Phi4Params)
    [InteractionUVModel params]
    (hmomAbs :
      ∀ Λ : Rectangle, ∃ θ D r : ℝ,
        0 < θ ∧ 0 ≤ D ∧ 0 ≤ r ∧ r < 1 ∧
        (∀ n : ℕ,
          Integrable
            (fun ω : FieldConfig2D =>
              Real.exp (θ * |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω|))
            (freeFieldMeasure params.mass params.mass_pos)) ∧
        (∀ n : ℕ,
          ∫ ω : FieldConfig2D,
            Real.exp (θ * |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω|)
            ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D * r ^ n)) :
    Nonempty (InteractionWeightModel params) := by
  refine interactionWeightModel_nonempty_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
    (params := params) ?_
  intro Λ
  exact shifted_exponential_moment_geometric_bound_of_abs
    (params := params) (Λ := Λ) (hmomAbs Λ)

/-- Construct `InteractionWeightModel` from:
    1) square-integrability/measurability UV interaction data (used to
       instantiate `InteractionUVModel`), and
    2) geometric decay of shifted-index exponential moments of
       `interactionCutoff(κ_{n+1})` on every volume cutoff. -/
theorem
    interactionWeightModel_nonempty_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
    (params : Phi4Params)
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        AEStronglyMeasurable (interactionCutoff params Λ κ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_sq :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        Integrable (fun ω => (interactionCutoff params Λ κ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_conv :
      ∀ (Λ : Rectangle),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then
            ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)
            else 0)
          Filter.atTop
          (nhds 0))
    (hcutoff_ae :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
            Filter.atTop
            (nhds (interaction params Λ ω)))
    (hinteraction_meas :
      ∀ (Λ : Rectangle),
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hinteraction_sq :
      ∀ (Λ : Rectangle),
        Integrable (fun ω => (interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
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
    Nonempty (InteractionWeightModel params) := by
  refine interactionWeightModel_nonempty_of_data params ?_
  intro Λ p _hp
  exact exp_interaction_Lp_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
    (params := params) (Λ := Λ)
    hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
    hinteraction_meas hinteraction_sq (hmom Λ)

/-- Construct `InteractionWeightModel` from:
    1) square-integrability/measurability UV interaction data, and
    2) geometric decay of shifted-index absolute exponential moments of
       `interactionCutoff(κ_{n+1})` on every volume cutoff. -/
theorem
    interactionWeightModel_nonempty_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_moment_abs_geometric_bound
    (params : Phi4Params)
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        AEStronglyMeasurable (interactionCutoff params Λ κ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_sq :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        Integrable (fun ω => (interactionCutoff params Λ κ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_conv :
      ∀ (Λ : Rectangle),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then
            ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)
            else 0)
          Filter.atTop
          (nhds 0))
    (hcutoff_ae :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
            Filter.atTop
            (nhds (interaction params Λ ω)))
    (hinteraction_meas :
      ∀ (Λ : Rectangle),
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hinteraction_sq :
      ∀ (Λ : Rectangle),
        Integrable (fun ω => (interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hmomAbs :
      ∀ Λ : Rectangle, ∃ θ D r : ℝ,
        0 < θ ∧ 0 ≤ D ∧ 0 ≤ r ∧ r < 1 ∧
        (∀ n : ℕ,
          Integrable
            (fun ω : FieldConfig2D =>
              Real.exp (θ * |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω|))
            (freeFieldMeasure params.mass params.mass_pos)) ∧
        (∀ n : ℕ,
          ∫ ω : FieldConfig2D,
            Real.exp (θ * |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω|)
            ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D * r ^ n)) :
    Nonempty (InteractionWeightModel params) := by
  rcases interactionUVModel_nonempty_of_sq_integrable_data
      (params := params)
      hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
      hinteraction_meas hinteraction_sq with ⟨huv⟩
  letI : InteractionUVModel params := huv
  refine interactionWeightModel_nonempty_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
    (params := params)
    hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
    hinteraction_meas hinteraction_sq ?_
  intro Λ
  exact shifted_exponential_moment_geometric_bound_of_abs
    (params := params) (Λ := Λ) (hmomAbs Λ)

/-- Construct `InteractionWeightModel` from direct per-volume almost-everywhere
    lower bounds on the limiting interaction `interaction params Λ`. -/
theorem interactionWeightModel_nonempty_of_ae_lower_bounds
    (params : Phi4Params)
    [InteractionUVModel params]
    (hbound :
      ∀ Λ : Rectangle, ∃ B : ℝ,
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          -B ≤ interaction params Λ ω) :
    Nonempty (InteractionWeightModel params) := by
  refine interactionWeightModel_nonempty_of_data params ?_
  intro Λ p _hp
  rcases hbound Λ with ⟨B, hB⟩
  exact exp_interaction_Lp_of_ae_lower_bound
    (params := params) (Λ := Λ) (B := B) hB

/-- Construct `InteractionWeightModel` from direct per-volume almost-everywhere
    lower bounds on `interaction`, using explicit measurability inputs instead
    of `InteractionUVModel`. -/
theorem interactionWeightModel_nonempty_of_ae_lower_bounds_of_aestronglyMeasurable
    (params : Phi4Params)
    (hmeas :
      ∀ Λ : Rectangle,
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hbound :
      ∀ Λ : Rectangle, ∃ B : ℝ,
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          -B ≤ interaction params Λ ω) :
    Nonempty (InteractionWeightModel params) := by
  refine interactionWeightModel_nonempty_of_data params ?_
  intro Λ p _hp
  rcases hbound Λ with ⟨B, hB⟩
  exact exp_interaction_Lp_of_ae_lower_bound_of_aestronglyMeasurable
    (params := params) (Λ := Λ) (hmeas := hmeas Λ) (B := B) hB

/-- Construct `InteractionIntegrabilityModel` from:
    1. UV/L² interaction control (`InteractionUVModel`), and
    2. per-volume cutoff-sequence lower bounds (sufficient for
       Boltzmann-weight `Lᵖ` integrability). -/
theorem interactionIntegrabilityModel_nonempty_of_uv_cutoff_seq_lower_bounds
    (params : Phi4Params)
    [InteractionUVModel params]
    (hcutoff_ae :
      ∀ Λ : Rectangle, ∃ B : ℝ,
        ∀ n : ℕ,
          ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
            -B ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω) :
    Nonempty (InteractionIntegrabilityModel params) := by
  rcases interactionWeightModel_nonempty_of_cutoff_seq_lower_bounds
      (params := params) hcutoff_ae with ⟨hW⟩
  letI : InteractionWeightModel params := hW
  exact ⟨inferInstance⟩

/-- Construct `InteractionIntegrabilityModel` from:
    1. UV/L² interaction control (`InteractionUVModel`), and
    2. shifted cutoff-sequence lower bounds (`κ_{n+1}`), avoiding direct
       `n = 0` assumptions. -/
theorem interactionIntegrabilityModel_nonempty_of_uv_cutoff_seq_succ_lower_bounds
    (params : Phi4Params)
    [InteractionUVModel params]
    (hcutoff_ae :
      ∀ Λ : Rectangle, ∃ B : ℝ,
        ∀ n : ℕ,
          ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
            -B ≤ interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω) :
    Nonempty (InteractionIntegrabilityModel params) := by
  rcases interactionWeightModel_nonempty_of_cutoff_seq_succ_lower_bounds
      (params := params) hcutoff_ae with ⟨hW⟩
  letI : InteractionWeightModel params := hW
  exact ⟨inferInstance⟩

/-- Construct `InteractionIntegrabilityModel` from:
    1. UV/L² interaction control (`InteractionUVModel`), and
    2. per-volume cutoff-sequence pointwise lower bounds (`∀ ω`, `∀ n`). -/
theorem interactionIntegrabilityModel_nonempty_of_uv_cutoff_seq_pointwise_lower_bounds
    (params : Phi4Params)
    [InteractionUVModel params]
    (hcutoff :
      ∀ Λ : Rectangle, ∃ B : ℝ,
        ∀ n : ℕ, ∀ ω : FieldConfig2D,
          -B ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω) :
    Nonempty (InteractionIntegrabilityModel params) := by
  rcases interactionWeightModel_nonempty_of_cutoff_seq_pointwise_lower_bounds
      (params := params) hcutoff with ⟨hW⟩
  letI : InteractionWeightModel params := hW
  exact ⟨inferInstance⟩

/-- Construct `InteractionIntegrabilityModel` from:
    1. UV/L² interaction control (`InteractionUVModel`), and
    2. shifted cutoff-sequence pointwise lower bounds (`κ_{n+1}`, `∀ ω`, `∀ n`). -/
theorem interactionIntegrabilityModel_nonempty_of_uv_cutoff_seq_succ_pointwise_lower_bounds
    (params : Phi4Params)
    [InteractionUVModel params]
    (hcutoff :
      ∀ Λ : Rectangle, ∃ B : ℝ,
        ∀ n : ℕ, ∀ ω : FieldConfig2D,
          -B ≤ interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω) :
    Nonempty (InteractionIntegrabilityModel params) := by
  rcases interactionWeightModel_nonempty_of_cutoff_seq_succ_pointwise_lower_bounds
      (params := params) hcutoff with ⟨hW⟩
  letI : InteractionWeightModel params := hW
  exact ⟨inferInstance⟩

/-- Construct `InteractionIntegrabilityModel` from:
    1. UV/L² interaction control (`InteractionUVModel`), and
    2. per-volume summable bad sets with good-set cutoff lower bounds. -/
theorem interactionIntegrabilityModel_nonempty_of_uv_cutoff_seq_summable_bad_sets
    (params : Phi4Params)
    [InteractionUVModel params]
    (hbad :
      ∀ Λ : Rectangle, ∃ B : ℝ, ∃ bad : ℕ → Set FieldConfig2D,
        (∑' n : ℕ, (freeFieldMeasure params.mass params.mass_pos) (bad n)) ≠ ∞ ∧
        (∀ n : ℕ, ∀ ω : FieldConfig2D, ω ∉ bad n →
          -B ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω)) :
    Nonempty (InteractionIntegrabilityModel params) := by
  rcases interactionWeightModel_nonempty_of_cutoff_seq_summable_bad_sets
      (params := params) hbad with ⟨hW⟩
  letI : InteractionWeightModel params := hW
  exact ⟨inferInstance⟩

/-- Construct `InteractionIntegrabilityModel` from:
    1. UV/L² interaction control (`InteractionUVModel`), and
    2. per-volume shifted-index summable bad sets with good-set cutoff lower
       bounds. -/
theorem interactionIntegrabilityModel_nonempty_of_uv_cutoff_seq_shifted_summable_bad_sets
    (params : Phi4Params)
    [InteractionUVModel params]
    (hbad :
      ∀ Λ : Rectangle, ∃ B : ℝ, ∃ bad : ℕ → Set FieldConfig2D,
        (∑' n : ℕ, (freeFieldMeasure params.mass params.mass_pos) (bad n)) ≠ ∞ ∧
        (∀ n : ℕ, ∀ ω : FieldConfig2D, ω ∉ bad n →
          -B ≤ interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)) :
    Nonempty (InteractionIntegrabilityModel params) := by
  rcases interactionWeightModel_nonempty_of_cutoff_seq_shifted_summable_bad_sets
      (params := params) hbad with ⟨hW⟩
  letI : InteractionWeightModel params := hW
  exact ⟨inferInstance⟩

/-- Construct `InteractionIntegrabilityModel` from:
    1. UV/L² interaction control (`InteractionUVModel`), and
    2. Wick-level shifted-index summable bad sets that imply cutoff lower
       bounds outside bad sets. -/
theorem interactionIntegrabilityModel_nonempty_of_uv_cutoff_seq_shifted_summable_wick_bad_sets
    (params : Phi4Params)
    [InteractionUVModel params]
    (hwick_bad :
      ∀ Λ : Rectangle, ∃ B : ℝ, ∃ bad : ℕ → Set FieldConfig2D,
        (∑' n : ℕ, (freeFieldMeasure params.mass params.mass_pos) (bad n)) ≠ ∞ ∧
        MeasurableSet Λ.toSet ∧
        volume Λ.toSet ≠ ∞ ∧
        (∀ n : ℕ, ∀ ω : FieldConfig2D,
          IntegrableOn
            (fun x => wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x)
            Λ.toSet volume) ∧
        (∀ n : ℕ, ∀ ω : FieldConfig2D, ω ∉ bad n →
          ∀ x ∈ Λ.toSet,
            -B ≤ wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x)) :
    Nonempty (InteractionIntegrabilityModel params) := by
  rcases interactionWeightModel_nonempty_of_uv_cutoff_seq_shifted_summable_wick_bad_sets
      (params := params) hwick_bad with ⟨hW⟩
  letI : InteractionWeightModel params := hW
  exact ⟨inferInstance⟩

/-- Construct `InteractionIntegrabilityModel` from:
    1. UV/L² interaction control (`InteractionUVModel`), and
    2. Wick-level shifted-index geometric bad-set tails plus good-set
       lower bounds on `wickPower 4`. -/
theorem interactionIntegrabilityModel_nonempty_of_uv_cutoff_seq_shifted_geometric_wick_bad_sets
    (params : Phi4Params)
    [InteractionUVModel params]
    (hwick_bad :
      ∀ Λ : Rectangle, ∃ B : ℝ, ∃ bad : ℕ → Set FieldConfig2D, ∃ C r : ℝ≥0∞,
        C ≠ ⊤ ∧ r < 1 ∧
        (∀ n : ℕ,
          (freeFieldMeasure params.mass params.mass_pos) (bad n) ≤ C * r ^ n) ∧
        MeasurableSet Λ.toSet ∧
        volume Λ.toSet ≠ ∞ ∧
        (∀ n : ℕ, ∀ ω : FieldConfig2D,
          IntegrableOn
            (fun x => wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x)
            Λ.toSet volume) ∧
        (∀ n : ℕ, ∀ ω : FieldConfig2D, ω ∉ bad n →
          ∀ x ∈ Λ.toSet,
            -B ≤ wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x)) :
    Nonempty (InteractionIntegrabilityModel params) := by
  rcases interactionWeightModel_nonempty_of_uv_cutoff_seq_shifted_geometric_wick_bad_sets
      (params := params) hwick_bad with ⟨hW⟩
  letI : InteractionWeightModel params := hW
  exact ⟨inferInstance⟩

/-- Construct `InteractionIntegrabilityModel` from:
    1. UV/L² interaction control (`InteractionUVModel`), and
    2. Wick-level shifted-index exponential bad-set tails plus good-set
       lower bounds on `wickPower 4`. -/
theorem interactionIntegrabilityModel_nonempty_of_uv_cutoff_seq_shifted_exponential_wick_bad_sets
    (params : Phi4Params)
    [InteractionUVModel params]
    (hwick_bad :
      ∀ Λ : Rectangle, ∃ B : ℝ, ∃ bad : ℕ → Set FieldConfig2D, ∃ C : ℝ≥0∞,
        ∃ α : ℝ, C ≠ ⊤ ∧ 0 < α ∧
        (∀ n : ℕ,
          (freeFieldMeasure params.mass params.mass_pos) (bad n)
            ≤ C * (ENNReal.ofReal (Real.exp (-α))) ^ n) ∧
        MeasurableSet Λ.toSet ∧
        volume Λ.toSet ≠ ∞ ∧
        (∀ n : ℕ, ∀ ω : FieldConfig2D,
          IntegrableOn
            (fun x => wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x)
            Λ.toSet volume) ∧
        (∀ n : ℕ, ∀ ω : FieldConfig2D, ω ∉ bad n →
          ∀ x ∈ Λ.toSet,
            -B ≤ wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x)) :
    Nonempty (InteractionIntegrabilityModel params) := by
  rcases interactionWeightModel_nonempty_of_uv_cutoff_seq_shifted_exponential_wick_bad_sets
      (params := params) hwick_bad with ⟨hW⟩
  letI : InteractionWeightModel params := hW
  exact ⟨inferInstance⟩

/-- Construct `InteractionIntegrabilityModel` from:
    1. UV/L² interaction control (`InteractionUVModel`), and
    2. shifted-index summable tails of natural Wick sublevel bad events
       `{ω | ∃ x ∈ Λ, wickPower(κ_{n+1}) ω x < -B}`. -/
theorem interactionIntegrabilityModel_nonempty_of_uv_cutoff_seq_shifted_summable_wick_sublevel_bad_sets
    (params : Phi4Params)
    [InteractionUVModel params]
    (hwick_bad :
      ∀ Λ : Rectangle, ∃ B : ℝ,
        (∑' n : ℕ,
          (freeFieldMeasure params.mass params.mass_pos)
            {ω : FieldConfig2D |
              ∃ x ∈ Λ.toSet,
                wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x < -B}) ≠ ∞ ∧
        MeasurableSet Λ.toSet ∧
        volume Λ.toSet ≠ ∞ ∧
        (∀ n : ℕ, ∀ ω : FieldConfig2D,
          IntegrableOn
            (fun x => wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x)
            Λ.toSet volume)) :
    Nonempty (InteractionIntegrabilityModel params) := by
  rcases interactionWeightModel_nonempty_of_uv_cutoff_seq_shifted_summable_wick_sublevel_bad_sets
      (params := params) hwick_bad with ⟨hW⟩
  letI : InteractionWeightModel params := hW
  exact ⟨inferInstance⟩

/-- Construct `InteractionIntegrabilityModel` from:
    1. UV/L² interaction control (`InteractionUVModel`), and
    2. shifted-index geometric tails of natural Wick sublevel bad events
       `{ω | ∃ x ∈ Λ, wickPower(κ_{n+1}) ω x < -B}`. -/
theorem interactionIntegrabilityModel_nonempty_of_uv_cutoff_seq_shifted_geometric_wick_sublevel_bad_sets
    (params : Phi4Params)
    [InteractionUVModel params]
    (hwick_bad :
      ∀ Λ : Rectangle, ∃ B : ℝ, ∃ C r : ℝ≥0∞,
        C ≠ ⊤ ∧ r < 1 ∧
        (∀ n : ℕ,
          (freeFieldMeasure params.mass params.mass_pos)
            {ω : FieldConfig2D |
              ∃ x ∈ Λ.toSet,
                wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x < -B}
            ≤ C * r ^ n) ∧
        MeasurableSet Λ.toSet ∧
        volume Λ.toSet ≠ ∞ ∧
        (∀ n : ℕ, ∀ ω : FieldConfig2D,
          IntegrableOn
            (fun x => wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x)
            Λ.toSet volume)) :
    Nonempty (InteractionIntegrabilityModel params) := by
  rcases interactionWeightModel_nonempty_of_uv_cutoff_seq_shifted_geometric_wick_sublevel_bad_sets
      (params := params) hwick_bad with ⟨hW⟩
  letI : InteractionWeightModel params := hW
  exact ⟨inferInstance⟩

/-- Construct `InteractionIntegrabilityModel` from:
    1. UV/L² interaction control (`InteractionUVModel`), and
    2. shifted-index exponential tails of natural Wick sublevel bad events
       `{ω | ∃ x ∈ Λ, wickPower(κ_{n+1}) ω x < -B}`. -/
theorem interactionIntegrabilityModel_nonempty_of_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets
    (params : Phi4Params)
    [InteractionUVModel params]
    (hwick_bad :
      ∀ Λ : Rectangle, ∃ B : ℝ, ∃ C : ℝ≥0∞, ∃ α : ℝ,
        C ≠ ⊤ ∧ 0 < α ∧
        (∀ n : ℕ,
          (freeFieldMeasure params.mass params.mass_pos)
            {ω : FieldConfig2D |
              ∃ x ∈ Λ.toSet,
                wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x < -B}
            ≤ C * (ENNReal.ofReal (Real.exp (-α))) ^ n) ∧
        MeasurableSet Λ.toSet ∧
        volume Λ.toSet ≠ ∞ ∧
        (∀ n : ℕ, ∀ ω : FieldConfig2D,
          IntegrableOn
            (fun x => wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x)
            Λ.toSet volume)) :
    Nonempty (InteractionIntegrabilityModel params) := by
  rcases interactionWeightModel_nonempty_of_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets
      (params := params) hwick_bad with ⟨hW⟩
  letI : InteractionWeightModel params := hW
  exact ⟨inferInstance⟩

/-- Construct `InteractionIntegrabilityModel` from:
    1. square-integrability/measurability UV data (promoted to
       `InteractionUVModel`), and
    2. shifted-index exponential tails of natural Wick sublevel bad events
       `{ω | ∃ x ∈ Λ, wickPower(κ_{n+1}) ω x < -B}`. -/
theorem
    interactionIntegrabilityModel_nonempty_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets
    (params : Phi4Params)
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        AEStronglyMeasurable (interactionCutoff params Λ κ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_sq :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        Integrable (fun ω => (interactionCutoff params Λ κ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_conv :
      ∀ (Λ : Rectangle),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then
            ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)
            else 0)
          Filter.atTop
          (nhds 0))
    (hcutoff_ae :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
            Filter.atTop
            (nhds (interaction params Λ ω)))
    (hinteraction_meas :
      ∀ (Λ : Rectangle),
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hinteraction_sq :
      ∀ (Λ : Rectangle),
        Integrable (fun ω => (interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hwick_bad :
      ∀ Λ : Rectangle, ∃ B : ℝ, ∃ C : ℝ≥0∞, ∃ α : ℝ,
        C ≠ ⊤ ∧ 0 < α ∧
        (∀ n : ℕ,
          (freeFieldMeasure params.mass params.mass_pos)
            {ω : FieldConfig2D |
              ∃ x ∈ Λ.toSet,
                wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x < -B}
            ≤ C * (ENNReal.ofReal (Real.exp (-α))) ^ n) ∧
        MeasurableSet Λ.toSet ∧
        volume Λ.toSet ≠ ∞ ∧
        (∀ n : ℕ, ∀ ω : FieldConfig2D,
          IntegrableOn
            (fun x => wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x)
            Λ.toSet volume)) :
    Nonempty (InteractionIntegrabilityModel params) := by
  rcases interactionUVModel_nonempty_of_sq_integrable_data
      (params := params)
      hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
      hinteraction_meas hinteraction_sq with ⟨huv⟩
  letI : InteractionUVModel params := huv
  have hW :
      Nonempty (InteractionWeightModel params) :=
    interactionWeightModel_nonempty_of_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets
      (params := params) hwick_bad
  exact interactionIntegrabilityModel_nonempty_of_uv_weight_nonempty
    (params := params) ⟨huv⟩ hW

/-- Construct `InteractionIntegrabilityModel` from:
    1. UV/L² interaction control (`InteractionUVModel`), and
    2. per-volume eventually-in-`n` cutoff lower bounds (sufficient for
       Boltzmann-weight `Lᵖ` integrability). -/
theorem interactionIntegrabilityModel_nonempty_of_uv_cutoff_seq_eventually_lower_bounds
    (params : Phi4Params)
    [InteractionUVModel params]
    (hcutoff_ae :
      ∀ Λ : Rectangle, ∃ B : ℝ,
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          ∀ᶠ n in Filter.atTop,
            -B ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω) :
    Nonempty (InteractionIntegrabilityModel params) := by
  rcases interactionWeightModel_nonempty_of_cutoff_seq_eventually_lower_bounds
      (params := params) hcutoff_ae with ⟨hW⟩
  letI : InteractionWeightModel params := hW
  exact ⟨inferInstance⟩

/-- Construct `InteractionIntegrabilityModel` from:
    1. UV/L² interaction control (`InteractionUVModel`), and
    2. per-volume variable cutoff constants with eventual uniform control
       (`Bₙ ≤ B` eventually). -/
theorem interactionIntegrabilityModel_nonempty_of_uv_cutoff_seq_variable_lower_bounds
    (params : Phi4Params)
    [InteractionUVModel params]
    (hcutoff_ae :
      ∀ Λ : Rectangle, ∃ Bseq : ℕ → ℝ, ∃ B : ℝ,
        (∀ n : ℕ,
          ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
            -Bseq n ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω) ∧
        (∀ᶠ n in Filter.atTop, Bseq n ≤ B)) :
    Nonempty (InteractionIntegrabilityModel params) := by
  rcases interactionWeightModel_nonempty_of_cutoff_seq_variable_lower_bounds
      (params := params) hcutoff_ae with ⟨hW⟩
  letI : InteractionWeightModel params := hW
  exact ⟨inferInstance⟩

/-- Construct `InteractionIntegrabilityModel` from:
    1. UV/L² interaction control (`InteractionUVModel`), and
    2. per-volume summable bad-event tails for cutoff lower bounds. -/
theorem interactionIntegrabilityModel_nonempty_of_uv_cutoff_seq_summable_bad_event_measure
    (params : Phi4Params)
    [InteractionUVModel params]
    (hbad :
      ∀ Λ : Rectangle, ∃ B : ℝ,
        (∑' n : ℕ,
          (freeFieldMeasure params.mass params.mass_pos)
            {ω : FieldConfig2D |
              interactionCutoff params Λ (standardUVCutoffSeq n) ω < -B}) ≠ ∞) :
    Nonempty (InteractionIntegrabilityModel params) := by
  rcases interactionWeightModel_nonempty_of_cutoff_seq_summable_bad_event_measure
      (params := params) hbad with ⟨hW⟩
  letI : InteractionWeightModel params := hW
  exact ⟨inferInstance⟩

/-- Construct `InteractionIntegrabilityModel` from:
    1. UV/L² interaction control (`InteractionUVModel`), and
    2. per-volume shifted-index summable bad-event tails (`κ_{n+1}`). -/
theorem interactionIntegrabilityModel_nonempty_of_uv_cutoff_seq_shifted_summable_bad_event_measure
    (params : Phi4Params)
    [InteractionUVModel params]
    (hbad :
      ∀ Λ : Rectangle, ∃ B : ℝ,
        (∑' n : ℕ,
          (freeFieldMeasure params.mass params.mass_pos)
            {ω : FieldConfig2D |
              interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω < -B}) ≠ ∞) :
    Nonempty (InteractionIntegrabilityModel params) := by
  rcases interactionWeightModel_nonempty_of_cutoff_seq_shifted_summable_bad_event_measure
      (params := params) hbad with ⟨hW⟩
  letI : InteractionWeightModel params := hW
  exact ⟨inferInstance⟩

/-- Construct `InteractionIntegrabilityModel` from:
    1. UV/L² interaction control (`InteractionUVModel`), and
    2. per-volume summable majorants on cutoff bad-event probabilities. -/
theorem interactionIntegrabilityModel_nonempty_of_uv_cutoff_seq_summable_bad_event_bound
    (params : Phi4Params)
    [InteractionUVModel params]
    (hbad :
      ∀ Λ : Rectangle, ∃ B : ℝ, ∃ ε : ℕ → ℝ≥0∞,
        (∑' n : ℕ, ε n) ≠ ∞ ∧
        (∀ n : ℕ,
          (freeFieldMeasure params.mass params.mass_pos)
            {ω : FieldConfig2D |
              interactionCutoff params Λ (standardUVCutoffSeq n) ω < -B} ≤ ε n)) :
    Nonempty (InteractionIntegrabilityModel params) := by
  rcases interactionWeightModel_nonempty_of_cutoff_seq_summable_bad_event_bound
      (params := params) hbad with ⟨hW⟩
  letI : InteractionWeightModel params := hW
  exact ⟨inferInstance⟩

/-- Construct `InteractionIntegrabilityModel` from:
    1. UV/L² interaction control (`InteractionUVModel`), and
    2. per-volume shifted-index summable majorants on cutoff bad-event
       probabilities (`κ_{n+1}`). -/
theorem interactionIntegrabilityModel_nonempty_of_uv_cutoff_seq_shifted_summable_bad_event_bound
    (params : Phi4Params)
    [InteractionUVModel params]
    (hbad :
      ∀ Λ : Rectangle, ∃ B : ℝ, ∃ ε : ℕ → ℝ≥0∞,
        (∑' n : ℕ, ε n) ≠ ∞ ∧
        (∀ n : ℕ,
          (freeFieldMeasure params.mass params.mass_pos)
            {ω : FieldConfig2D |
              interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω < -B} ≤ ε n)) :
    Nonempty (InteractionIntegrabilityModel params) := by
  rcases interactionWeightModel_nonempty_of_cutoff_seq_shifted_summable_bad_event_bound
      (params := params) hbad with ⟨hW⟩
  letI : InteractionWeightModel params := hW
  exact ⟨inferInstance⟩

/-- Construct `InteractionIntegrabilityModel` from:
    1. UV/L² interaction control (`InteractionUVModel`), and
    2. per-volume geometric bad-event tail bounds (`μ badₙ ≤ C * rⁿ`, `r < 1`). -/
theorem interactionIntegrabilityModel_nonempty_of_uv_cutoff_seq_geometric_bad_event_bound
    (params : Phi4Params)
    [InteractionUVModel params]
    (hbad :
      ∀ Λ : Rectangle, ∃ B : ℝ, ∃ C r : ℝ≥0∞,
        C ≠ ⊤ ∧ r < 1 ∧
        (∀ n : ℕ,
          (freeFieldMeasure params.mass params.mass_pos)
            {ω : FieldConfig2D |
              interactionCutoff params Λ (standardUVCutoffSeq n) ω < -B} ≤ C * r ^ n)) :
    Nonempty (InteractionIntegrabilityModel params) := by
  rcases interactionWeightModel_nonempty_of_cutoff_seq_geometric_bad_event_bound
      (params := params) hbad with ⟨hW⟩
  letI : InteractionWeightModel params := hW
  exact ⟨inferInstance⟩

/-- Construct `InteractionIntegrabilityModel` from:
    1. UV/L² interaction control (`InteractionUVModel`), and
    2. per-volume shifted-index geometric bad-event tail bounds
       (`κ_{n+1}`). -/
theorem interactionIntegrabilityModel_nonempty_of_uv_cutoff_seq_shifted_geometric_bad_event_bound
    (params : Phi4Params)
    [InteractionUVModel params]
    (hbad :
      ∀ Λ : Rectangle, ∃ B : ℝ, ∃ C r : ℝ≥0∞,
        C ≠ ⊤ ∧ r < 1 ∧
        (∀ n : ℕ,
          (freeFieldMeasure params.mass params.mass_pos)
            {ω : FieldConfig2D |
              interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω < -B} ≤ C * r ^ n)) :
    Nonempty (InteractionIntegrabilityModel params) := by
  rcases interactionWeightModel_nonempty_of_cutoff_seq_shifted_geometric_bad_event_bound
      (params := params) hbad with ⟨hW⟩
  letI : InteractionWeightModel params := hW
  exact ⟨inferInstance⟩

/-- Construct `InteractionIntegrabilityModel` from:
    1. UV/L² interaction control (`InteractionUVModel`), and
    2. per-volume exponential bad-event tail bounds
       (`μ badₙ ≤ C * exp(-α n)`, `α > 0`). -/
theorem interactionIntegrabilityModel_nonempty_of_uv_cutoff_seq_exponential_bad_event_bound
    (params : Phi4Params)
    [InteractionUVModel params]
    (hbad :
      ∀ Λ : Rectangle, ∃ B : ℝ, ∃ C : ℝ≥0∞, ∃ α : ℝ,
        C ≠ ⊤ ∧ 0 < α ∧
        (∀ n : ℕ,
          (freeFieldMeasure params.mass params.mass_pos)
            {ω : FieldConfig2D |
              interactionCutoff params Λ (standardUVCutoffSeq n) ω < -B}
            ≤ C * (ENNReal.ofReal (Real.exp (-α))) ^ n)) :
    Nonempty (InteractionIntegrabilityModel params) := by
  rcases interactionWeightModel_nonempty_of_cutoff_seq_exponential_bad_event_bound
      (params := params) hbad with ⟨hW⟩
  letI : InteractionWeightModel params := hW
  exact ⟨inferInstance⟩

/-- Construct `InteractionIntegrabilityModel` from:
    1. UV/L² interaction control (`InteractionUVModel`), and
    2. per-volume shifted-index exponential bad-event tail bounds
       (`κ_{n+1}`). -/
theorem interactionIntegrabilityModel_nonempty_of_uv_cutoff_seq_shifted_exponential_bad_event_bound
    (params : Phi4Params)
    [InteractionUVModel params]
    (hbad :
      ∀ Λ : Rectangle, ∃ B : ℝ, ∃ C : ℝ≥0∞, ∃ α : ℝ,
        C ≠ ⊤ ∧ 0 < α ∧
        (∀ n : ℕ,
          (freeFieldMeasure params.mass params.mass_pos)
            {ω : FieldConfig2D |
              interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω < -B}
            ≤ C * (ENNReal.ofReal (Real.exp (-α))) ^ n)) :
    Nonempty (InteractionIntegrabilityModel params) := by
  rcases interactionWeightModel_nonempty_of_cutoff_seq_shifted_exponential_bad_event_bound
      (params := params) hbad with ⟨hW⟩
  letI : InteractionWeightModel params := hW
  exact ⟨inferInstance⟩

/-- Construct `InteractionIntegrabilityModel` from:
    1. UV/L² interaction control (`InteractionUVModel`), and
    2. geometric decay of shifted-index exponential moments of
       `interactionCutoff(κ_{n+1})`. -/
theorem interactionIntegrabilityModel_nonempty_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
    (params : Phi4Params)
    [InteractionUVModel params]
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
    Nonempty (InteractionIntegrabilityModel params) := by
  rcases interactionWeightModel_nonempty_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
      (params := params) hmom with ⟨hW⟩
  letI : InteractionWeightModel params := hW
  exact ⟨inferInstance⟩

/-- Construct `InteractionIntegrabilityModel` from:
    1. UV/L² interaction control (`InteractionUVModel`), and
    2. geometric decay of shifted-index absolute exponential moments of
       `interactionCutoff(κ_{n+1})`. -/
theorem interactionIntegrabilityModel_nonempty_of_uv_cutoff_seq_shifted_exponential_moment_abs_geometric_bound
    (params : Phi4Params)
    [InteractionUVModel params]
    (hmomAbs :
      ∀ Λ : Rectangle, ∃ θ D r : ℝ,
        0 < θ ∧ 0 ≤ D ∧ 0 ≤ r ∧ r < 1 ∧
        (∀ n : ℕ,
          Integrable
            (fun ω : FieldConfig2D =>
              Real.exp (θ * |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω|))
            (freeFieldMeasure params.mass params.mass_pos)) ∧
        (∀ n : ℕ,
          ∫ ω : FieldConfig2D,
            Real.exp (θ * |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω|)
            ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D * r ^ n)) :
    Nonempty (InteractionIntegrabilityModel params) := by
  rcases interactionWeightModel_nonempty_of_uv_cutoff_seq_shifted_exponential_moment_abs_geometric_bound
      (params := params) hmomAbs with ⟨hW⟩
  letI : InteractionWeightModel params := hW
  exact ⟨inferInstance⟩

/-- Construct `InteractionIntegrabilityModel` from:
    1. square-integrability/measurability UV data (promoted to `InteractionUVModel`),
    2. geometric decay of shifted-index exponential moments of
       `interactionCutoff(κ_{n+1})`. -/
theorem
    interactionIntegrabilityModel_nonempty_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
    (params : Phi4Params)
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        AEStronglyMeasurable (interactionCutoff params Λ κ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_sq :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        Integrable (fun ω => (interactionCutoff params Λ κ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_conv :
      ∀ (Λ : Rectangle),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then
            ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)
            else 0)
          Filter.atTop
          (nhds 0))
    (hcutoff_ae :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
            Filter.atTop
            (nhds (interaction params Λ ω)))
    (hinteraction_meas :
      ∀ (Λ : Rectangle),
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hinteraction_sq :
      ∀ (Λ : Rectangle),
        Integrable (fun ω => (interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
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
    Nonempty (InteractionIntegrabilityModel params) := by
  rcases interactionUVModel_nonempty_of_sq_integrable_data
      (params := params)
      hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
      hinteraction_meas hinteraction_sq with ⟨huv⟩
  letI : InteractionUVModel params := huv
  have hW :
      Nonempty (InteractionWeightModel params) :=
    interactionWeightModel_nonempty_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
      (params := params)
      hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
      hinteraction_meas hinteraction_sq hmom
  exact interactionIntegrabilityModel_nonempty_of_uv_weight_nonempty
    (params := params) ⟨huv⟩ hW

/-- Construct `InteractionIntegrabilityModel` from:
    1. square-integrability/measurability UV data (promoted to `InteractionUVModel`),
    2. geometric decay of shifted-index absolute exponential moments of
       `interactionCutoff(κ_{n+1})`. -/
theorem
    interactionIntegrabilityModel_nonempty_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_moment_abs_geometric_bound
    (params : Phi4Params)
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        AEStronglyMeasurable (interactionCutoff params Λ κ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_sq :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        Integrable (fun ω => (interactionCutoff params Λ κ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_conv :
      ∀ (Λ : Rectangle),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then
            ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)
            else 0)
          Filter.atTop
          (nhds 0))
    (hcutoff_ae :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
            Filter.atTop
            (nhds (interaction params Λ ω)))
    (hinteraction_meas :
      ∀ (Λ : Rectangle),
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hinteraction_sq :
      ∀ (Λ : Rectangle),
        Integrable (fun ω => (interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hmomAbs :
      ∀ Λ : Rectangle, ∃ θ D r : ℝ,
        0 < θ ∧ 0 ≤ D ∧ 0 ≤ r ∧ r < 1 ∧
        (∀ n : ℕ,
          Integrable
            (fun ω : FieldConfig2D =>
              Real.exp (θ * |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω|))
            (freeFieldMeasure params.mass params.mass_pos)) ∧
        (∀ n : ℕ,
          ∫ ω : FieldConfig2D,
            Real.exp (θ * |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω|)
            ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D * r ^ n)) :
    Nonempty (InteractionIntegrabilityModel params) := by
  rcases interactionUVModel_nonempty_of_sq_integrable_data
      (params := params)
      hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
      hinteraction_meas hinteraction_sq with ⟨huv⟩
  letI : InteractionUVModel params := huv
  have hW :
      Nonempty (InteractionWeightModel params) :=
    interactionWeightModel_nonempty_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_moment_abs_geometric_bound
      (params := params)
      hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
      hinteraction_meas hinteraction_sq hmomAbs
  exact interactionIntegrabilityModel_nonempty_of_uv_weight_nonempty
    (params := params) ⟨huv⟩ hW

/-- Construct `InteractionIntegrabilityModel` from:
    1. square-integrability/measurability UV data (promoted to
       `InteractionUVModel`),
    2. per-volume polynomial-decay shifted UV-difference squared moments in the
       graph-natural index form
       `E[(V_{n+1} - V)^2] ≤ C(Λ) * (n+2)^(-β)` (`β > 1`), and
    3. per-volume uniform shifted cutoff partition-function bounds
       `∫ exp(-q * V_{n+1}) ≤ D(Λ, q)`.

    This is the same hard-core WP1 assembly route as the theorem above, with
    only the index convention changed (`n+2` instead of `n+1`). -/
theorem
    interactionIntegrabilityModel_nonempty_of_sq_integrable_data_and_sq_moment_polynomial_bound_per_volume_and_uniform_partition_bound_of_succ_succ
    (params : Phi4Params)
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        AEStronglyMeasurable (interactionCutoff params Λ κ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_sq :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        Integrable (fun ω => (interactionCutoff params Λ κ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_conv :
      ∀ (Λ : Rectangle),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then
            ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)
            else 0)
          Filter.atTop
          (nhds 0))
    (hcutoff_ae :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
            Filter.atTop
            (nhds (interaction params Λ ω)))
    (hinteraction_meas :
      ∀ (Λ : Rectangle),
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hinteraction_sq :
      ∀ (Λ : Rectangle),
        Integrable (fun ω => (interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (β : ℝ) (hβ : 1 < β)
    (C : Rectangle → ℝ)
    (hC_nonneg : ∀ Λ : Rectangle, 0 ≤ C Λ)
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
        ≤ C Λ * (↑(n + 2) : ℝ) ^ (-β))
    (hpartition :
      ∀ (Λ : Rectangle) (q : ℝ), 0 < q →
        ∃ D : ℝ,
          (∀ n : ℕ,
            Integrable
              (fun ω : FieldConfig2D =>
                Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)))
              (freeFieldMeasure params.mass params.mass_pos)) ∧
          (∀ n : ℕ,
            ∫ ω : FieldConfig2D,
              Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
              ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D)) :
    Nonempty (InteractionIntegrabilityModel params) := by
  rcases interactionUVModel_nonempty_of_sq_integrable_data
      (params := params)
      hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
      hinteraction_meas hinteraction_sq with ⟨huv⟩
  have hW : Nonempty (InteractionWeightModel params) :=
    interactionWeightModel_nonempty_of_sq_moment_polynomial_bound_per_volume_and_uniform_partition_bound_of_succ_succ
      (params := params) (β := β) hβ (C := C) hC_nonneg hInt hM
      (hcutoff_meas := fun Λ n => by
        simpa using hcutoff_meas Λ (standardUVCutoffSeq (n + 1)))
      hpartition
  exact interactionIntegrabilityModel_nonempty_of_uv_weight_nonempty
    (params := params) ⟨huv⟩ hW

/-- Construct `InteractionIntegrabilityModel` from:
    1. square-integrability/measurability UV data (promoted to
       `InteractionUVModel`),
    2. per-volume polynomial-decay shifted UV-difference squared moments
       `E[(V_{n+1} - V)^2] ≤ C(Λ) * (n+1)^(-β)` (`β > 1`), and
    3. per-volume uniform shifted cutoff partition-function bounds
       `∫ exp(-q * V_{n+1}) ≤ D(Λ, q)`.

    This is the direct hard-core WP1 assembly route: quantitative UV
    convergence plus uniform cutoff partition control feeds the Fatou bridge to
    produce `InteractionWeightModel`, then combines with UV/L² control. -/
theorem
    interactionIntegrabilityModel_nonempty_of_sq_integrable_data_and_sq_moment_polynomial_bound_per_volume_and_uniform_partition_bound
    (params : Phi4Params)
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        AEStronglyMeasurable (interactionCutoff params Λ κ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_sq :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        Integrable (fun ω => (interactionCutoff params Λ κ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_conv :
      ∀ (Λ : Rectangle),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then
            ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)
            else 0)
          Filter.atTop
          (nhds 0))
    (hcutoff_ae :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
            Filter.atTop
            (nhds (interaction params Λ ω)))
    (hinteraction_meas :
      ∀ (Λ : Rectangle),
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hinteraction_sq :
      ∀ (Λ : Rectangle),
        Integrable (fun ω => (interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (β : ℝ) (hβ : 1 < β)
    (C : Rectangle → ℝ)
    (hC_nonneg : ∀ Λ : Rectangle, 0 ≤ C Λ)
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
        ≤ C Λ * (↑(n + 1) : ℝ) ^ (-β))
    (hpartition :
      ∀ (Λ : Rectangle) (q : ℝ), 0 < q →
        ∃ D : ℝ,
          (∀ n : ℕ,
            Integrable
              (fun ω : FieldConfig2D =>
                Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)))
              (freeFieldMeasure params.mass params.mass_pos)) ∧
          (∀ n : ℕ,
            ∫ ω : FieldConfig2D,
              Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
              ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D)) :
    Nonempty (InteractionIntegrabilityModel params) := by
  rcases interactionUVModel_nonempty_of_sq_integrable_data
      (params := params)
      hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
      hinteraction_meas hinteraction_sq with ⟨huv⟩
  have hW : Nonempty (InteractionWeightModel params) :=
    interactionWeightModel_nonempty_of_sq_moment_polynomial_bound_per_volume_and_uniform_partition_bound
      (params := params) (β := β) hβ (C := C) hC_nonneg hInt hM
      (hcutoff_meas := fun Λ n => by
        simpa using hcutoff_meas Λ (standardUVCutoffSeq (n + 1)))
      hpartition
  exact interactionIntegrabilityModel_nonempty_of_uv_weight_nonempty
    (params := params) ⟨huv⟩ hW

/-- Construct `InteractionIntegrabilityModel` from:
    1. square-integrability/measurability UV data (promoted to
       `InteractionUVModel`),
    2. a fixed higher even moment order `2j` (`j > 0`) with per-volume
       polynomial-decay shifted UV-difference bounds
       `E[|V_{n+1} - V|^(2j)] ≤ C(Λ) * (n+1)^(-β)` (`β > 1`), and
    3. per-volume uniform shifted cutoff partition-function bounds
       `∫ exp(-q * V_{n+1}) ≤ D(Λ, q)`.

    This is the higher-moment generalization of the squared-moment hard-core
    WP1 assembly route. -/
theorem
    interactionIntegrabilityModel_nonempty_of_sq_integrable_data_and_higher_moment_polynomial_bound_per_volume_and_uniform_partition_bound
    (params : Phi4Params)
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        AEStronglyMeasurable (interactionCutoff params Λ κ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_sq :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        Integrable (fun ω => (interactionCutoff params Λ κ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_conv :
      ∀ (Λ : Rectangle),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then
            ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)
            else 0)
          Filter.atTop
          (nhds 0))
    (hcutoff_ae :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
            Filter.atTop
            (nhds (interaction params Λ ω)))
    (hinteraction_meas :
      ∀ (Λ : Rectangle),
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hinteraction_sq :
      ∀ (Λ : Rectangle),
        Integrable (fun ω => (interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (j : ℕ) (hj : 0 < j)
    (β : ℝ) (hβ : 1 < β)
    (C : Rectangle → ℝ)
    (hC_nonneg : ∀ Λ : Rectangle, 0 ≤ C Λ)
    (hInt :
      ∀ (Λ : Rectangle) (n : ℕ),
        Integrable
          (fun ω : FieldConfig2D =>
            |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω| ^ (2 * j))
          (freeFieldMeasure params.mass params.mass_pos))
    (hM :
      ∀ (Λ : Rectangle) (n : ℕ),
        ∫ ω : FieldConfig2D,
          |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω| ^ (2 * j)
          ∂(freeFieldMeasure params.mass params.mass_pos)
        ≤ C Λ * (↑(n + 1) : ℝ) ^ (-β))
    (hpartition :
      ∀ (Λ : Rectangle) (q : ℝ), 0 < q →
        ∃ D : ℝ,
          (∀ n : ℕ,
            Integrable
              (fun ω : FieldConfig2D =>
                Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)))
              (freeFieldMeasure params.mass params.mass_pos)) ∧
          (∀ n : ℕ,
            ∫ ω : FieldConfig2D,
              Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
              ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D)) :
    Nonempty (InteractionIntegrabilityModel params) := by
  rcases interactionUVModel_nonempty_of_sq_integrable_data
      (params := params)
      hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
      hinteraction_meas hinteraction_sq with ⟨huv⟩
  have hW : Nonempty (InteractionWeightModel params) :=
    interactionWeightModel_nonempty_of_higher_moment_polynomial_bound_per_volume_and_uniform_partition_bound
      (params := params) (j := j) (hj := hj)
      (β := β) hβ (C := C) hC_nonneg hInt hM
      (hcutoff_meas := fun Λ n => by
        simpa using hcutoff_meas Λ (standardUVCutoffSeq (n + 1)))
      hpartition
  exact interactionIntegrabilityModel_nonempty_of_uv_weight_nonempty
    (params := params) ⟨huv⟩ hW

/-- Construct `InteractionIntegrabilityModel` from:
    1. square-integrability/measurability UV data (promoted to
       `InteractionUVModel`),
    2. a fixed higher even moment order `2j` (`j > 0`) with per-volume
       polynomial-decay shifted UV-difference bounds in the graph-natural index
       form `E[|V_{n+1} - V|^(2j)] ≤ C(Λ) * (n+2)^(-β)` (`β > 1`), and
    3. per-volume uniform shifted cutoff partition-function bounds
       `∫ exp(-q * V_{n+1}) ≤ D(Λ, q)`.

    This is the same higher-moment hard-core WP1 assembly route as the theorem
    above, with only the index convention changed (`n+2` instead of `n+1`). -/
theorem
    interactionIntegrabilityModel_nonempty_of_sq_integrable_data_and_higher_moment_polynomial_bound_per_volume_and_uniform_partition_bound_of_succ_succ
    (params : Phi4Params)
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        AEStronglyMeasurable (interactionCutoff params Λ κ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_sq :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        Integrable (fun ω => (interactionCutoff params Λ κ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_conv :
      ∀ (Λ : Rectangle),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then
            ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)
            else 0)
          Filter.atTop
          (nhds 0))
    (hcutoff_ae :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
            Filter.atTop
            (nhds (interaction params Λ ω)))
    (hinteraction_meas :
      ∀ (Λ : Rectangle),
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hinteraction_sq :
      ∀ (Λ : Rectangle),
        Integrable (fun ω => (interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (j : ℕ) (hj : 0 < j)
    (β : ℝ) (hβ : 1 < β)
    (C : Rectangle → ℝ)
    (hC_nonneg : ∀ Λ : Rectangle, 0 ≤ C Λ)
    (hInt :
      ∀ (Λ : Rectangle) (n : ℕ),
        Integrable
          (fun ω : FieldConfig2D =>
            |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω| ^ (2 * j))
          (freeFieldMeasure params.mass params.mass_pos))
    (hM :
      ∀ (Λ : Rectangle) (n : ℕ),
        ∫ ω : FieldConfig2D,
          |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω| ^ (2 * j)
          ∂(freeFieldMeasure params.mass params.mass_pos)
        ≤ C Λ * (↑(n + 2) : ℝ) ^ (-β))
    (hpartition :
      ∀ (Λ : Rectangle) (q : ℝ), 0 < q →
        ∃ D : ℝ,
          (∀ n : ℕ,
            Integrable
              (fun ω : FieldConfig2D =>
                Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)))
              (freeFieldMeasure params.mass params.mass_pos)) ∧
          (∀ n : ℕ,
            ∫ ω : FieldConfig2D,
              Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
              ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D)) :
    Nonempty (InteractionIntegrabilityModel params) := by
  rcases interactionUVModel_nonempty_of_sq_integrable_data
      (params := params)
      hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
      hinteraction_meas hinteraction_sq with ⟨huv⟩
  have hW : Nonempty (InteractionWeightModel params) :=
    interactionWeightModel_nonempty_of_higher_moment_polynomial_bound_per_volume_and_uniform_partition_bound_of_succ_succ
      (params := params) (j := j) (hj := hj) (β := β) hβ (C := C) hC_nonneg hInt hM
      (hcutoff_meas := fun Λ n => by
        simpa using hcutoff_meas Λ (standardUVCutoffSeq (n + 1)))
      hpartition
  exact interactionIntegrabilityModel_nonempty_of_uv_weight_nonempty
    (params := params) ⟨huv⟩ hW

/-- Construct `InteractionIntegrabilityModel` from:
    1. square-integrability/measurability UV data (promoted to
       `InteractionUVModel`),
    2. explicit real-parameterized a.e. UV convergence for cutoffs, and
    3. per-volume bad-set decomposition data consisting of:
       - linear lower bounds outside bad sets,
       - geometric second-moment bounds for shifted cutoff exponentials, and
       - ENNReal geometric bad-set tails.

    This theorem wires the new Cauchy/AM-GM bad-part infrastructure into the
    production integrability path without introducing interface wrappers. -/
theorem
    interactionIntegrabilityModel_nonempty_of_sq_integrable_data_and_linear_lower_bound_off_bad_sets_and_sq_exp_moment_geometric_and_bad_measure_geometric_ennreal
    (params : Phi4Params)
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        AEStronglyMeasurable (interactionCutoff params Λ κ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_sq :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        Integrable (fun ω => (interactionCutoff params Λ κ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_conv :
      ∀ (Λ : Rectangle),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then
            ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)
            else 0)
          Filter.atTop
          (nhds 0))
    (hcutoff_ae :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
            Filter.atTop
            (nhds (interaction params Λ ω)))
    (hinteraction_meas :
      ∀ (Λ : Rectangle),
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hinteraction_sq :
      ∀ (Λ : Rectangle),
        Integrable (fun ω => (interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hdecomp :
      ∀ (Λ : Rectangle) (q : ℝ), 0 < q →
        ∃ a b : ℝ, 0 < a ∧
          ∃ bad : ℕ → Set FieldConfig2D,
            (∀ n : ℕ, MeasurableSet (bad n)) ∧
            (∀ n : ℕ,
              Integrable
                (fun ω : FieldConfig2D =>
                  Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)))
                (freeFieldMeasure params.mass params.mass_pos)) ∧
            (∀ (n : ℕ) (ω : FieldConfig2D), ω ∉ bad n →
              a * (n : ℝ) - b ≤ interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω) ∧
            (∀ n : ℕ,
              MemLp
                (fun ω : FieldConfig2D =>
                  Real.exp ((-q) * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
                2
                (freeFieldMeasure params.mass params.mass_pos)) ∧
            ∃ D2 r2 : ℝ,
              0 ≤ D2 ∧ 0 ≤ r2 ∧ r2 < 1 ∧
              (∀ n : ℕ,
                ∫ ω : FieldConfig2D,
                  (Real.exp
                    ((-q) * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)) ^ (2 : ℝ)
                  ∂(freeFieldMeasure params.mass params.mass_pos)
                ≤ D2 * r2 ^ n) ∧
              ∃ Cb rb : ℝ≥0∞,
                Cb ≠ ⊤ ∧ rb < 1 ∧
                (∀ n : ℕ,
                  (freeFieldMeasure params.mass params.mass_pos) (bad n) ≤ Cb * rb ^ n)) :
    Nonempty (InteractionIntegrabilityModel params) := by
  rcases interactionUVModel_nonempty_of_sq_integrable_data
      (params := params)
      hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
      hinteraction_meas hinteraction_sq with ⟨huv⟩
  have hW : Nonempty (InteractionWeightModel params) := by
    refine interactionWeightModel_nonempty_of_tendsto_ae_and_geometric_exp_moment_bound
      (params := params) hcutoff_ae hcutoff_meas ?_
    intro Λ q hq
    rcases hdecomp Λ q hq with
      ⟨a, b, ha, bad, hbad_meas, hInt, hgood, hmem2, D2, r2, hD2, hr20, hr21, hMoment2,
        Cb, rb, hCb, hrb1, hbadMeasure⟩
    exact
      standardSeq_succ_geometric_exp_moment_bound_of_linear_lower_bound_off_bad_sets_and_sq_exp_moment_geometric_and_bad_measure_geometric_ennreal
        (params := params) (Λ := Λ) (q := q) (a := a) (b := b) hq ha
        bad hbad_meas hInt hgood hmem2
        D2 r2 hD2 hr20 hr21 hMoment2
        Cb rb hCb hrb1 hbadMeasure
  exact interactionIntegrabilityModel_nonempty_of_uv_weight_nonempty
    (params := params) ⟨huv⟩ hW

/-- Construct `InteractionIntegrabilityModel` from:
    1. square-integrable/measurable UV data,
    2. per-volume geometric shifted-cutoff exponential moments,
    3. linear threshold parameters `(a, b)` with effective ratio
       `exp(q * a) * r < 1`,
    4. geometric shifted-cutoff second moments for `exp(-q * interactionCutoff)`.

    The bad-set decomposition is built canonically using
    `bad n = toMeasurable {interactionCutoff(κ_{n+1}) < a*n - b}`, and the
    ENNReal geometric bad-tail bound is derived by the linear-threshold
    Chernoff bridge. -/
theorem
    interactionIntegrabilityModel_nonempty_of_sq_integrable_data_and_linear_threshold_geometric_exp_moment_and_sq_exp_moment_geometric
    (params : Phi4Params)
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        AEStronglyMeasurable (interactionCutoff params Λ κ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_sq :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        Integrable (fun ω => (interactionCutoff params Λ κ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_conv :
      ∀ (Λ : Rectangle),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then
            ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)
            else 0)
          Filter.atTop
          (nhds 0))
    (hcutoff_ae :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
            Filter.atTop
            (nhds (interaction params Λ ω)))
    (hinteraction_meas :
      ∀ (Λ : Rectangle),
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hinteraction_sq :
      ∀ (Λ : Rectangle),
        Integrable (fun ω => (interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcore :
      ∀ (Λ : Rectangle) (q : ℝ), 0 < q →
        ∃ a D r : ℝ,
          0 < a ∧ 0 ≤ D ∧ 0 ≤ r ∧ Real.exp (q * a) * r < 1 ∧
          (∀ n : ℕ,
            Integrable
              (fun ω : FieldConfig2D =>
                Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)))
              (freeFieldMeasure params.mass params.mass_pos)) ∧
          (∀ n : ℕ,
            ∫ ω : FieldConfig2D,
              Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
              ∂(freeFieldMeasure params.mass params.mass_pos)
            ≤ D * r ^ n) ∧
          (∀ n : ℕ,
            MemLp
              (fun ω : FieldConfig2D =>
                Real.exp ((-q) * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
              2
              (freeFieldMeasure params.mass params.mass_pos)) ∧
          ∃ D2 r2 : ℝ,
            0 ≤ D2 ∧ 0 ≤ r2 ∧ r2 < 1 ∧
            (∀ n : ℕ,
              ∫ ω : FieldConfig2D,
                (Real.exp
                  ((-q) * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)) ^ (2 : ℝ)
                ∂(freeFieldMeasure params.mass params.mass_pos)
              ≤ D2 * r2 ^ n)) :
    Nonempty (InteractionIntegrabilityModel params) := by
  refine
    interactionIntegrabilityModel_nonempty_of_sq_integrable_data_and_linear_lower_bound_off_bad_sets_and_sq_exp_moment_geometric_and_bad_measure_geometric_ennreal
      (params := params)
      hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
      hinteraction_meas hinteraction_sq ?_
  intro Λ q hq
  rcases hcore Λ q hq with
    ⟨a, D, r, ha, hD, hr0, hrr1, hInt, hM, hmem2, D2, r2, hD2, hr20, hr21, hMoment2⟩
  let b : ℝ := 0
  let μ : Measure FieldConfig2D := freeFieldMeasure params.mass params.mass_pos
  let bad : ℕ → Set FieldConfig2D := fun n =>
    toMeasurable μ
      {ω : FieldConfig2D |
        interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω < a * (n : ℝ) - b}
  rcases
      shifted_cutoff_bad_event_exists_ennreal_geometric_bound_of_exponential_moment_bound_linear_threshold
        (params := params) (Λ := Λ) (q := q) (a := a) (b := b) (D := D) (r := r)
        hq hD hr0 hrr1
        (hInt := fun n => by simpa [neg_mul] using hInt n)
        (hM := fun n => by simpa [neg_mul] using hM n) with
    ⟨Cb, rb, hCb, hrb1, hbadEvent⟩
  refine ⟨a, b, ha, bad, ?_, hInt, ?_, hmem2, D2, r2, hD2, hr20, hr21, hMoment2, Cb, rb, hCb, hrb1, ?_⟩
  · intro n
    exact measurableSet_toMeasurable μ _
  · intro n ω hω
    have hnot :
        ¬ interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω < a * (n : ℝ) - b := by
      intro hlt
      exact hω ((subset_toMeasurable μ _) hlt)
    exact not_lt.mp hnot
  · intro n
    calc
      (freeFieldMeasure params.mass params.mass_pos) (bad n)
          = (freeFieldMeasure params.mass params.mass_pos)
              {ω : FieldConfig2D |
                interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω < a * (n : ℝ) - b} := by
              simp [bad, μ, measure_toMeasurable]
      _ ≤ Cb * rb ^ n := hbadEvent n

/-- Construct `InteractionIntegrabilityModel` from:
    1. square-integrable/measurable UV data,
    2. per-volume geometric shifted-cutoff exponential moments at parameter `q`,
    3. geometric shifted-cutoff exponential moments at doubled parameter `2q`,
    4. linear thresholds `(a, b)` with effective ratio `exp(q * a) * r < 1`.

    The doubled-parameter moments are converted internally into the `MemLp`-2
    and second-moment decomposition data needed by the hard-core bad-set route. -/
theorem
    interactionIntegrabilityModel_nonempty_of_sq_integrable_data_and_linear_threshold_geometric_exp_moment_and_double_exp_moment_geometric
    (params : Phi4Params)
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        AEStronglyMeasurable (interactionCutoff params Λ κ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_sq :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        Integrable (fun ω => (interactionCutoff params Λ κ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_conv :
      ∀ (Λ : Rectangle),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then
            ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)
            else 0)
          Filter.atTop
          (nhds 0))
    (hcutoff_ae :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
            Filter.atTop
            (nhds (interaction params Λ ω)))
    (hinteraction_meas :
      ∀ (Λ : Rectangle),
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hinteraction_sq :
      ∀ (Λ : Rectangle),
        Integrable (fun ω => (interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcore :
      ∀ (Λ : Rectangle) (q : ℝ), 0 < q →
        ∃ a D r D2 r2 : ℝ,
          0 < a ∧ 0 ≤ D ∧ 0 ≤ r ∧ Real.exp (q * a) * r < 1 ∧
          0 ≤ D2 ∧ 0 ≤ r2 ∧ r2 < 1 ∧
          (∀ n : ℕ,
            Integrable
              (fun ω : FieldConfig2D =>
                Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)))
              (freeFieldMeasure params.mass params.mass_pos)) ∧
          (∀ n : ℕ,
            ∫ ω : FieldConfig2D,
              Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
              ∂(freeFieldMeasure params.mass params.mass_pos)
            ≤ D * r ^ n) ∧
          (∀ n : ℕ,
            Integrable
              (fun ω : FieldConfig2D =>
                Real.exp ((-(2 * q)) * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
              (freeFieldMeasure params.mass params.mass_pos)) ∧
          (∀ n : ℕ,
            ∫ ω : FieldConfig2D,
              Real.exp ((-(2 * q)) * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)
              ∂(freeFieldMeasure params.mass params.mass_pos)
            ≤ D2 * r2 ^ n)) :
    Nonempty (InteractionIntegrabilityModel params) := by
  refine
    interactionIntegrabilityModel_nonempty_of_sq_integrable_data_and_linear_lower_bound_off_bad_sets_and_sq_exp_moment_geometric_and_bad_measure_geometric_ennreal
      (params := params)
      hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
      hinteraction_meas hinteraction_sq ?_
  intro Λ q hq
  rcases hcore Λ q hq with
    ⟨a, D, r, D2, r2, ha, hD, hr0, hrr1, hD2, hr20, hr21, hInt, hM, hInt2, hMoment2raw⟩
  let b : ℝ := 0
  let μ : Measure FieldConfig2D := freeFieldMeasure params.mass params.mass_pos
  let bad : ℕ → Set FieldConfig2D := fun n =>
    toMeasurable μ
      {ω : FieldConfig2D |
        interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω < a * (n : ℝ) - b}
  rcases
      standardSeq_succ_sq_exp_moment_data_of_double_exponential_moment_geometric_bound
        (params := params) (Λ := Λ) (q := q)
        (hcutoff_meas := fun n => by
          simpa using hcutoff_meas Λ (standardUVCutoffSeq (n + 1)))
        hInt2 D2 r2 hMoment2raw with
    ⟨hmem2, hMoment2⟩
  rcases
      shifted_cutoff_bad_event_exists_ennreal_geometric_bound_of_exponential_moment_bound_linear_threshold
        (params := params) (Λ := Λ) (q := q) (a := a) (b := b) (D := D) (r := r)
        hq hD hr0 hrr1
        (hInt := fun n => by simpa [neg_mul] using hInt n)
        (hM := fun n => by simpa [neg_mul] using hM n) with
    ⟨Cb, rb, hCb, hrb1, hbadEvent⟩
  refine
    ⟨a, b, ha, bad, ?_, hInt, ?_, hmem2, D2, r2, hD2, hr20, hr21, hMoment2, Cb, rb, hCb, hrb1, ?_⟩
  · intro n
    exact measurableSet_toMeasurable μ _
  · intro n ω hω
    have hnot :
        ¬ interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω < a * (n : ℝ) - b := by
      intro hlt
      exact hω ((subset_toMeasurable μ _) hlt)
    exact not_lt.mp hnot
  · intro n
    calc
      (freeFieldMeasure params.mass params.mass_pos) (bad n)
          = (freeFieldMeasure params.mass params.mass_pos)
              {ω : FieldConfig2D |
                interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω < a * (n : ℝ) - b} := by
              simp [bad, μ, measure_toMeasurable]
      _ ≤ Cb * rb ^ n := hbadEvent n

/-- Weakened doubled-moment linear-threshold constructor:
    same route as
    `interactionIntegrabilityModel_nonempty_of_sq_integrable_data_and_linear_threshold_geometric_exp_moment_and_double_exp_moment_geometric`,
    but without explicitly requiring per-`n` integrability of
    `exp(-q * interactionCutoff(κ_{n+1}))`.

    Integrability is derived internally from `MemLp(·, 2)` over the probability
    free-field measure. -/
theorem
    interactionIntegrabilityModel_nonempty_of_sq_integrable_data_and_linear_threshold_geometric_exp_moment_and_double_exp_moment_geometric_of_moment_bounds
    (params : Phi4Params)
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        AEStronglyMeasurable (interactionCutoff params Λ κ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_sq :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        Integrable (fun ω => (interactionCutoff params Λ κ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_conv :
      ∀ (Λ : Rectangle),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then
            ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)
            else 0)
          Filter.atTop
          (nhds 0))
    (hcutoff_ae :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
            Filter.atTop
            (nhds (interaction params Λ ω)))
    (hinteraction_meas :
      ∀ (Λ : Rectangle),
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hinteraction_sq :
      ∀ (Λ : Rectangle),
        Integrable (fun ω => (interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcore :
      ∀ (Λ : Rectangle) (q : ℝ), 0 < q →
        ∃ a D r D2 r2 : ℝ,
          0 < a ∧ 0 ≤ D ∧ 0 ≤ r ∧ Real.exp (q * a) * r < 1 ∧
          0 ≤ D2 ∧ 0 ≤ r2 ∧ r2 < 1 ∧
          (∀ n : ℕ,
            ∫ ω : FieldConfig2D,
              Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
              ∂(freeFieldMeasure params.mass params.mass_pos)
            ≤ D * r ^ n) ∧
          (∀ n : ℕ,
            Integrable
              (fun ω : FieldConfig2D =>
                Real.exp ((-(2 * q)) * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
              (freeFieldMeasure params.mass params.mass_pos)) ∧
          (∀ n : ℕ,
            ∫ ω : FieldConfig2D,
              Real.exp ((-(2 * q)) * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)
              ∂(freeFieldMeasure params.mass params.mass_pos)
            ≤ D2 * r2 ^ n)) :
    Nonempty (InteractionIntegrabilityModel params) := by
  refine
    interactionIntegrabilityModel_nonempty_of_sq_integrable_data_and_linear_threshold_geometric_exp_moment_and_double_exp_moment_geometric
      (params := params)
      hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
      hinteraction_meas hinteraction_sq ?_
  intro Λ q hq
  rcases hcore Λ q hq with
    ⟨a, D, r, D2, r2, ha, hD, hr0, hrr1, hD2, hr20, hr21, hM, hInt2, hMoment2raw⟩
  rcases
      standardSeq_succ_sq_exp_moment_data_of_double_exponential_moment_geometric_bound
        (params := params) (Λ := Λ) (q := q)
        (hcutoff_meas := fun n => by
          simpa using hcutoff_meas Λ (standardUVCutoffSeq (n + 1)))
        hInt2 D2 r2 hMoment2raw with
    ⟨hmem2, _hMoment2⟩
  let μ : Measure FieldConfig2D := freeFieldMeasure params.mass params.mass_pos
  letI : IsProbabilityMeasure μ := freeFieldMeasure_isProbability params.mass params.mass_pos
  have hInt :
      ∀ n : ℕ,
        Integrable
          (fun ω : FieldConfig2D =>
            Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
          )
          (freeFieldMeasure params.mass params.mass_pos) := by
    intro n
    simpa [neg_mul] using (hmem2 n).integrable (by norm_num)
  exact ⟨a, D, r, D2, r2, ha, hD, hr0, hrr1, hD2, hr20, hr21, hInt, hM, hInt2, hMoment2raw⟩

/-- Mixed signed/absolute doubled-moment linear-threshold constructor:
    same route as
    `interactionIntegrabilityModel_nonempty_of_sq_integrable_data_and_linear_threshold_geometric_exp_moment_and_double_exp_moment_geometric_of_moment_bounds`,
    but the doubled-parameter branch is accepted in absolute form
    `exp((2q) * |interactionCutoff|)`.

    The `2q` absolute moments are converted internally to signed `2q` moments
    using `shifted_exponential_moment_geometric_bound_of_abs_at_theta`. -/
theorem
    interactionIntegrabilityModel_nonempty_of_sq_integrable_data_and_linear_threshold_geometric_exp_moment_and_double_exp_moment_abs_geometric_of_moment_bounds
    (params : Phi4Params)
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        AEStronglyMeasurable (interactionCutoff params Λ κ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_sq :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        Integrable (fun ω => (interactionCutoff params Λ κ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_conv :
      ∀ (Λ : Rectangle),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then
            ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)
            else 0)
          Filter.atTop
          (nhds 0))
    (hcutoff_ae :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
            Filter.atTop
            (nhds (interaction params Λ ω)))
    (hinteraction_meas :
      ∀ (Λ : Rectangle),
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hinteraction_sq :
      ∀ (Λ : Rectangle),
        Integrable (fun ω => (interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcore :
      ∀ (Λ : Rectangle) (q : ℝ), 0 < q →
        ∃ a D r D2 r2 : ℝ,
          0 < a ∧ 0 ≤ D ∧ 0 ≤ r ∧ Real.exp (q * a) * r < 1 ∧
          0 ≤ D2 ∧ 0 ≤ r2 ∧ r2 < 1 ∧
          (∀ n : ℕ,
            ∫ ω : FieldConfig2D,
              Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
              ∂(freeFieldMeasure params.mass params.mass_pos)
            ≤ D * r ^ n) ∧
          (∀ n : ℕ,
            Integrable
              (fun ω : FieldConfig2D =>
                Real.exp ((2 * q) * |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω|))
              (freeFieldMeasure params.mass params.mass_pos)) ∧
          (∀ n : ℕ,
            ∫ ω : FieldConfig2D,
              Real.exp ((2 * q) * |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω|)
              ∂(freeFieldMeasure params.mass params.mass_pos)
            ≤ D2 * r2 ^ n)) :
    Nonempty (InteractionIntegrabilityModel params) := by
  rcases interactionUVModel_nonempty_of_sq_integrable_data
      (params := params)
      hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
      hinteraction_meas hinteraction_sq with ⟨huv⟩
  letI : InteractionUVModel params := huv
  refine
    interactionIntegrabilityModel_nonempty_of_sq_integrable_data_and_linear_threshold_geometric_exp_moment_and_double_exp_moment_geometric_of_moment_bounds
      (params := params)
      hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
      hinteraction_meas hinteraction_sq ?_
  intro Λ q hq
  rcases hcore Λ q hq with
    ⟨a, D, r, D2, r2, ha, hD, hr0, hrr1, hD2, hr20, hr21, hM, hIntAbs2, hMAbs2⟩
  rcases
      shifted_exponential_moment_geometric_bound_of_abs_at_theta
        (params := params) (Λ := Λ) (θ := 2 * q) (D := D2) (r := r2)
        (show 0 < 2 * q by nlinarith [hq])
        hIntAbs2 hMAbs2 with
    ⟨hInt2, hMoment2raw⟩
  exact ⟨a, D, r, D2, r2, ha, hD, hr0, hrr1, hD2, hr20, hr21, hM, hInt2, hMoment2raw⟩

/-- Construct `InteractionIntegrabilityModel` from:
    1. square-integrability/measurability UV data (promoted to `InteractionUVModel`),
    2. deterministic linear shifted-cutoff lower bounds
       `a * n - b ≤ interactionCutoff(κ_{n+1})` (with `a > 0`), which are used
       to construct `InteractionWeightModel` via geometric moment control. -/
theorem interactionIntegrabilityModel_nonempty_of_sq_integrable_data_and_linear_lower_bound
    (params : Phi4Params)
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        AEStronglyMeasurable (interactionCutoff params Λ κ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_sq :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        Integrable (fun ω => (interactionCutoff params Λ κ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_conv :
      ∀ (Λ : Rectangle),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then
            ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)
            else 0)
          Filter.atTop
          (nhds 0))
    (hcutoff_ae :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
            Filter.atTop
            (nhds (interaction params Λ ω)))
    (hinteraction_meas :
      ∀ (Λ : Rectangle),
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hinteraction_sq :
      ∀ (Λ : Rectangle),
        Integrable (fun ω => (interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hlin :
      ∀ Λ : Rectangle, ∃ a b : ℝ, 0 < a ∧
        ∀ (n : ℕ) (ω : FieldConfig2D),
          a * (n : ℝ) - b ≤ interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω) :
    Nonempty (InteractionIntegrabilityModel params) := by
  rcases interactionUVModel_nonempty_of_sq_integrable_data
      (params := params)
      hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
      hinteraction_meas hinteraction_sq with ⟨huv⟩
  have hW : Nonempty (InteractionWeightModel params) :=
    interactionWeightModel_nonempty_of_tendsto_ae_and_linear_lower_bound
      (params := params) hcutoff_ae hcutoff_meas hlin
  exact interactionIntegrabilityModel_nonempty_of_uv_weight_nonempty
    (params := params) ⟨huv⟩ hW

/-- Construct `InteractionIntegrabilityModel` from:
    1. UV/L² interaction control (`InteractionUVModel`), and
    2. direct per-volume almost-everywhere lower bounds on the limiting
       interaction `interaction params Λ`. -/
theorem interactionIntegrabilityModel_nonempty_of_uv_ae_lower_bounds
    (params : Phi4Params)
    [InteractionUVModel params]
    (hbound :
      ∀ Λ : Rectangle, ∃ B : ℝ,
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          -B ≤ interaction params Λ ω) :
    Nonempty (InteractionIntegrabilityModel params) := by
  rcases interactionWeightModel_nonempty_of_ae_lower_bounds
      (params := params) hbound with ⟨hW⟩
  letI : InteractionWeightModel params := hW
  exact ⟨inferInstance⟩

/-- **Theorem 8.6.2 (Glimm-Jaffe)**: e^{-V_Λ} ∈ Lᵖ(dφ_C) for all p < ∞.
    This is the key estimate for existence of the finite-volume measure in d=2.

    More precisely:
      ∫ exp(-p V_Λ) dφ_C ≤ const × exp(const × (N(f) + 1))
    where N(f) depends on the coupling and volume.

    The proof combines:
    - Semiboundedness of :φ⁴:_κ (Proposition 8.6.3)
    - Gaussian measure of the "bad set" where :φ⁴: is very negative
- The fact that this bad set has exponentially small measure -/
theorem exp_interaction_Lp (params : Phi4Params) (Λ : Rectangle)
    [InteractionWeightModel params]
    {p : ℝ≥0∞} (hp : p ≠ ⊤) :
    MemLp (fun ω => Real.exp (-(interaction params Λ ω)))
      p (freeFieldMeasure params.mass params.mass_pos) := by
  exact InteractionWeightModel.exp_interaction_Lp
    (params := params) Λ hp

/-- Positivity of the partition function: Z_Λ = ∫ e^{-V_Λ} dφ_C > 0. -/
theorem partition_function_pos (params : Phi4Params)
    [InteractionWeightModel params]
    (Λ : Rectangle) :
    0 < ∫ ω, Real.exp (-(interaction params Λ ω))
        ∂(freeFieldMeasure params.mass params.mass_pos) := by
  letI : IsProbabilityMeasure (freeFieldMeasure params.mass params.mass_pos) :=
    freeFieldMeasure_isProbability params.mass params.mass_pos
  have hLp : MemLp (fun ω => Real.exp (-(interaction params Λ ω)))
      (1 : ℝ≥0∞) (freeFieldMeasure params.mass params.mass_pos) :=
    exp_interaction_Lp params Λ (p := (1 : ℝ≥0∞)) (by norm_num)
  have hIntExp : Integrable (fun ω => Real.exp (-(interaction params Λ ω)))
      (freeFieldMeasure params.mass params.mass_pos) :=
    (memLp_one_iff_integrable.mp hLp)
  simpa using (integral_exp_pos (μ := freeFieldMeasure params.mass params.mass_pos)
    (f := fun ω => -(interaction params Λ ω)) hIntExp)

/-- Finiteness of the partition function: Z_Λ < ∞ (i.e. the exponential is integrable). -/
theorem partition_function_integrable (params : Phi4Params)
    [InteractionWeightModel params]
    (Λ : Rectangle) :
    Integrable (fun ω => Real.exp (-(interaction params Λ ω)))
        (freeFieldMeasure params.mass params.mass_pos) := by
  have hLp : MemLp (fun ω => Real.exp (-(interaction params Λ ω)))
      (1 : ℝ≥0∞) (freeFieldMeasure params.mass params.mass_pos) :=
    exp_interaction_Lp params Λ (p := (1 : ℝ≥0∞)) (by norm_num)
  exact (memLp_one_iff_integrable.mp hLp)

/-- `partition_function_pos` from an explicit witness of
    `InteractionWeightModel`, avoiding direct typeclass assumptions
    at theorem-call sites. -/
theorem partition_function_pos_of_nonempty_interactionWeightModel
    (params : Phi4Params) (Λ : Rectangle)
    (hW : Nonempty (InteractionWeightModel params)) :
    0 < ∫ ω, Real.exp (-(interaction params Λ ω))
        ∂(freeFieldMeasure params.mass params.mass_pos) := by
  rcases hW with ⟨hWinst⟩
  letI : InteractionWeightModel params := hWinst
  exact partition_function_pos params Λ

/-- `partition_function_integrable` from an explicit witness of
    `InteractionWeightModel`, avoiding direct typeclass assumptions
    at theorem-call sites. -/
theorem partition_function_integrable_of_nonempty_interactionWeightModel
    (params : Phi4Params) (Λ : Rectangle)
    (hW : Nonempty (InteractionWeightModel params)) :
    Integrable (fun ω => Real.exp (-(interaction params Λ ω)))
        (freeFieldMeasure params.mass params.mass_pos) := by
  rcases hW with ⟨hWinst⟩
  letI : InteractionWeightModel params := hWinst
  exact partition_function_integrable params Λ

/-- Concrete partition-function positivity from geometric decay of shifted
    exponential moments of cutoff interactions. This discharges
    `InteractionWeightModel` via proved interaction bridges. -/
theorem partition_function_pos_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
    (params : Phi4Params)
    [InteractionUVModel params]
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
            ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D * r ^ n))
    (Λ : Rectangle) :
    0 < ∫ ω, Real.exp (-(interaction params Λ ω))
        ∂(freeFieldMeasure params.mass params.mass_pos) := by
  have hW :
      Nonempty (InteractionWeightModel params) :=
    interactionWeightModel_nonempty_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
      (params := params) hmom
  exact partition_function_pos_of_nonempty_interactionWeightModel
    (params := params) (Λ := Λ) hW

/-- Concrete partition-function integrability from geometric decay of shifted
    exponential moments of cutoff interactions. This discharges
    `InteractionWeightModel` via proved interaction bridges. -/
theorem partition_function_integrable_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
    (params : Phi4Params)
    [InteractionUVModel params]
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
            ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D * r ^ n))
    (Λ : Rectangle) :
    Integrable (fun ω => Real.exp (-(interaction params Λ ω)))
      (freeFieldMeasure params.mass params.mass_pos) := by
  have hW :
      Nonempty (InteractionWeightModel params) :=
    interactionWeightModel_nonempty_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
      (params := params) hmom
  exact partition_function_integrable_of_nonempty_interactionWeightModel
    (params := params) (Λ := Λ) hW

/-- Concrete partition-function positivity from explicit real-parameterized a.e.
    UV convergence, cutoff measurability, and deterministic linear shifted
    lower bounds `a * n - b ≤ interactionCutoff(κ_{n+1})` (`a > 0`). -/
theorem partition_function_pos_of_tendsto_ae_and_linear_lower_bound
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
          a * (n : ℝ) - b ≤ interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)
    (Λ : Rectangle) :
    0 < ∫ ω, Real.exp (-(interaction params Λ ω))
        ∂(freeFieldMeasure params.mass params.mass_pos) := by
  have hW :
      Nonempty (InteractionWeightModel params) :=
    interactionWeightModel_nonempty_of_tendsto_ae_and_linear_lower_bound
      (params := params) hcutoff_tendsto_ae hcutoff_meas hlin
  exact partition_function_pos_of_nonempty_interactionWeightModel
    (params := params) (Λ := Λ) hW

/-- Concrete partition-function integrability from explicit real-parameterized
    a.e. UV convergence, cutoff measurability, and deterministic linear shifted
    lower bounds `a * n - b ≤ interactionCutoff(κ_{n+1})` (`a > 0`). -/
theorem partition_function_integrable_of_tendsto_ae_and_linear_lower_bound
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
          a * (n : ℝ) - b ≤ interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)
    (Λ : Rectangle) :
    Integrable (fun ω => Real.exp (-(interaction params Λ ω)))
      (freeFieldMeasure params.mass params.mass_pos) := by
  have hW :
      Nonempty (InteractionWeightModel params) :=
    interactionWeightModel_nonempty_of_tendsto_ae_and_linear_lower_bound
      (params := params) hcutoff_tendsto_ae hcutoff_meas hlin
  exact partition_function_integrable_of_nonempty_interactionWeightModel
    (params := params) (Λ := Λ) hW

/-- Concrete partition-function positivity from:
    1) square-integrable/measurable UV interaction data, and
    2) shifted-cutoff geometric exponential-moment decay.
    This avoids a direct `[InteractionUVModel params]` assumption by building the
    required interaction integrability/weight interfaces constructively. -/
theorem
    partition_function_pos_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
    (params : Phi4Params)
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        AEStronglyMeasurable (interactionCutoff params Λ κ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_sq :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        Integrable (fun ω => (interactionCutoff params Λ κ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_conv :
      ∀ (Λ : Rectangle),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then
            ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)
            else 0)
          Filter.atTop
          (nhds 0))
    (hcutoff_ae :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
            Filter.atTop
            (nhds (interaction params Λ ω)))
    (hinteraction_meas :
      ∀ (Λ : Rectangle),
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hinteraction_sq :
      ∀ (Λ : Rectangle),
        Integrable (fun ω => (interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
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
            ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D * r ^ n))
    (Λ : Rectangle) :
    0 < ∫ ω, Real.exp (-(interaction params Λ ω))
        ∂(freeFieldMeasure params.mass params.mass_pos) := by
  have hW :
      Nonempty (InteractionWeightModel params) :=
    interactionWeightModel_nonempty_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
      (params := params)
      hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
      hinteraction_meas hinteraction_sq hmom
  exact partition_function_pos_of_nonempty_interactionWeightModel
    (params := params) (Λ := Λ) hW

/-- Concrete partition-function integrability from:
    1) square-integrable/measurable UV interaction data, and
    2) shifted-cutoff geometric exponential-moment decay.
    This avoids a direct `[InteractionUVModel params]` assumption by building the
    required interaction integrability/weight interfaces constructively. -/
theorem
    partition_function_integrable_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
    (params : Phi4Params)
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        AEStronglyMeasurable (interactionCutoff params Λ κ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_sq :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        Integrable (fun ω => (interactionCutoff params Λ κ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_conv :
      ∀ (Λ : Rectangle),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then
            ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)
            else 0)
          Filter.atTop
          (nhds 0))
    (hcutoff_ae :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
            Filter.atTop
            (nhds (interaction params Λ ω)))
    (hinteraction_meas :
      ∀ (Λ : Rectangle),
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hinteraction_sq :
      ∀ (Λ : Rectangle),
        Integrable (fun ω => (interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
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
            ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D * r ^ n))
    (Λ : Rectangle) :
    Integrable (fun ω => Real.exp (-(interaction params Λ ω)))
      (freeFieldMeasure params.mass params.mass_pos) := by
  have hW :
      Nonempty (InteractionWeightModel params) :=
    interactionWeightModel_nonempty_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
      (params := params)
      hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
      hinteraction_meas hinteraction_sq hmom
  exact partition_function_integrable_of_nonempty_interactionWeightModel
    (params := params) (Λ := Λ) hW

/-- Concrete partition-function positivity from:
    1) square-integrable/measurable UV interaction data,
    2) per-volume bad-set decomposition data with linear lower bounds off bad
       sets, geometric second-moment control, and ENNReal geometric bad-set
       tails.
    This is the ENNReal-tail bad-set hard-core WP1 route to partition-function
    positivity. -/
theorem
    partition_function_pos_of_sq_integrable_data_and_linear_lower_bound_off_bad_sets_and_sq_exp_moment_geometric_and_bad_measure_geometric_ennreal
    (params : Phi4Params)
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        AEStronglyMeasurable (interactionCutoff params Λ κ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_sq :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        Integrable (fun ω => (interactionCutoff params Λ κ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_conv :
      ∀ (Λ : Rectangle),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then
            ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)
            else 0)
          Filter.atTop
          (nhds 0))
    (hcutoff_ae :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
            Filter.atTop
            (nhds (interaction params Λ ω)))
    (hinteraction_meas :
      ∀ (Λ : Rectangle),
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hinteraction_sq :
      ∀ (Λ : Rectangle),
        Integrable (fun ω => (interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hdecomp :
      ∀ (Λ : Rectangle) (q : ℝ), 0 < q →
        ∃ a b : ℝ, 0 < a ∧
          ∃ bad : ℕ → Set FieldConfig2D,
            (∀ n : ℕ, MeasurableSet (bad n)) ∧
            (∀ n : ℕ,
              Integrable
                (fun ω : FieldConfig2D =>
                  Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)))
                (freeFieldMeasure params.mass params.mass_pos)) ∧
            (∀ (n : ℕ) (ω : FieldConfig2D), ω ∉ bad n →
              a * (n : ℝ) - b ≤ interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω) ∧
            (∀ n : ℕ,
              MemLp
                (fun ω : FieldConfig2D =>
                  Real.exp ((-q) * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
                2
                (freeFieldMeasure params.mass params.mass_pos)) ∧
            ∃ D2 r2 : ℝ,
              0 ≤ D2 ∧ 0 ≤ r2 ∧ r2 < 1 ∧
              (∀ n : ℕ,
                ∫ ω : FieldConfig2D,
                  (Real.exp
                    ((-q) * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)) ^ (2 : ℝ)
                  ∂(freeFieldMeasure params.mass params.mass_pos)
                ≤ D2 * r2 ^ n) ∧
              ∃ Cb rb : ℝ≥0∞,
                Cb ≠ ⊤ ∧ rb < 1 ∧
                (∀ n : ℕ,
                  (freeFieldMeasure params.mass params.mass_pos) (bad n) ≤ Cb * rb ^ n))
    (Λ : Rectangle) :
    0 < ∫ ω, Real.exp (-(interaction params Λ ω))
        ∂(freeFieldMeasure params.mass params.mass_pos) := by
  have hI :
      Nonempty (InteractionIntegrabilityModel params) :=
    interactionIntegrabilityModel_nonempty_of_sq_integrable_data_and_linear_lower_bound_off_bad_sets_and_sq_exp_moment_geometric_and_bad_measure_geometric_ennreal
      (params := params)
      hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
      hinteraction_meas hinteraction_sq hdecomp
  have hW :
      Nonempty (InteractionWeightModel params) :=
    interactionWeightModel_nonempty_of_integrability_nonempty
      (params := params) hI
  exact partition_function_pos_of_nonempty_interactionWeightModel
    (params := params) (Λ := Λ) hW

/-- Concrete partition-function integrability from:
    1) square-integrable/measurable UV interaction data,
    2) per-volume bad-set decomposition data with linear lower bounds off bad
       sets, geometric second-moment control, and ENNReal geometric bad-set
       tails.
    This is the ENNReal-tail bad-set hard-core WP1 route to partition-function
    integrability. -/
theorem
    partition_function_integrable_of_sq_integrable_data_and_linear_lower_bound_off_bad_sets_and_sq_exp_moment_geometric_and_bad_measure_geometric_ennreal
    (params : Phi4Params)
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        AEStronglyMeasurable (interactionCutoff params Λ κ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_sq :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        Integrable (fun ω => (interactionCutoff params Λ κ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_conv :
      ∀ (Λ : Rectangle),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then
            ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)
            else 0)
          Filter.atTop
          (nhds 0))
    (hcutoff_ae :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
            Filter.atTop
            (nhds (interaction params Λ ω)))
    (hinteraction_meas :
      ∀ (Λ : Rectangle),
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hinteraction_sq :
      ∀ (Λ : Rectangle),
        Integrable (fun ω => (interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hdecomp :
      ∀ (Λ : Rectangle) (q : ℝ), 0 < q →
        ∃ a b : ℝ, 0 < a ∧
          ∃ bad : ℕ → Set FieldConfig2D,
            (∀ n : ℕ, MeasurableSet (bad n)) ∧
            (∀ n : ℕ,
              Integrable
                (fun ω : FieldConfig2D =>
                  Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)))
                (freeFieldMeasure params.mass params.mass_pos)) ∧
            (∀ (n : ℕ) (ω : FieldConfig2D), ω ∉ bad n →
              a * (n : ℝ) - b ≤ interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω) ∧
            (∀ n : ℕ,
              MemLp
                (fun ω : FieldConfig2D =>
                  Real.exp ((-q) * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
                2
                (freeFieldMeasure params.mass params.mass_pos)) ∧
            ∃ D2 r2 : ℝ,
              0 ≤ D2 ∧ 0 ≤ r2 ∧ r2 < 1 ∧
              (∀ n : ℕ,
                ∫ ω : FieldConfig2D,
                  (Real.exp
                    ((-q) * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)) ^ (2 : ℝ)
                  ∂(freeFieldMeasure params.mass params.mass_pos)
                ≤ D2 * r2 ^ n) ∧
              ∃ Cb rb : ℝ≥0∞,
                Cb ≠ ⊤ ∧ rb < 1 ∧
                (∀ n : ℕ,
                  (freeFieldMeasure params.mass params.mass_pos) (bad n) ≤ Cb * rb ^ n))
    (Λ : Rectangle) :
    Integrable (fun ω => Real.exp (-(interaction params Λ ω)))
      (freeFieldMeasure params.mass params.mass_pos) := by
  have hI :
      Nonempty (InteractionIntegrabilityModel params) :=
    interactionIntegrabilityModel_nonempty_of_sq_integrable_data_and_linear_lower_bound_off_bad_sets_and_sq_exp_moment_geometric_and_bad_measure_geometric_ennreal
      (params := params)
      hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
      hinteraction_meas hinteraction_sq hdecomp
  have hW :
      Nonempty (InteractionWeightModel params) :=
    interactionWeightModel_nonempty_of_integrability_nonempty
      (params := params) hI
  exact partition_function_integrable_of_nonempty_interactionWeightModel
    (params := params) (Λ := Λ) hW

/-- Concrete partition-function positivity from:
    1) square-integrable/measurable UV interaction data,
    2) per-volume polynomial-decay squared-moment shifted UV-difference bounds,
    3) per-volume uniform shifted-cutoff partition-function bounds.
    This is the hard-core WP1 per-volume route to partition-function positivity. -/
theorem
    partition_function_pos_of_sq_integrable_data_and_sq_moment_polynomial_bound_per_volume_and_uniform_partition_bound
    (params : Phi4Params)
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        AEStronglyMeasurable (interactionCutoff params Λ κ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_sq :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        Integrable (fun ω => (interactionCutoff params Λ κ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_conv :
      ∀ (Λ : Rectangle),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then
            ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)
            else 0)
          Filter.atTop
          (nhds 0))
    (hcutoff_ae :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
            Filter.atTop
            (nhds (interaction params Λ ω)))
    (hinteraction_meas :
      ∀ (Λ : Rectangle),
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hinteraction_sq :
      ∀ (Λ : Rectangle),
        Integrable (fun ω => (interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (betaMom : ℝ) (hbetaMom : 1 < betaMom)
    (C : Rectangle → ℝ)
    (hC_nonneg : ∀ Λ : Rectangle, 0 ≤ C Λ)
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
        ≤ C Λ * (↑(n + 1) : ℝ) ^ (-betaMom))
    (hpartition :
      ∀ (Λ : Rectangle) (q : ℝ), 0 < q →
        ∃ D : ℝ,
          (∀ n : ℕ,
            Integrable
              (fun ω : FieldConfig2D =>
                Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)))
              (freeFieldMeasure params.mass params.mass_pos)) ∧
          (∀ n : ℕ,
            ∫ ω : FieldConfig2D,
              Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
              ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D))
    (Λ : Rectangle) :
    0 < ∫ ω, Real.exp (-(interaction params Λ ω))
        ∂(freeFieldMeasure params.mass params.mass_pos) := by
  have hI :
      Nonempty (InteractionIntegrabilityModel params) :=
    interactionIntegrabilityModel_nonempty_of_sq_integrable_data_and_sq_moment_polynomial_bound_per_volume_and_uniform_partition_bound
      (params := params)
      hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
      hinteraction_meas hinteraction_sq
      betaMom hbetaMom C hC_nonneg hInt hM hpartition
  have hW :
      Nonempty (InteractionWeightModel params) :=
    interactionWeightModel_nonempty_of_integrability_nonempty
      (params := params) hI
  exact partition_function_pos_of_nonempty_interactionWeightModel
    (params := params) (Λ := Λ) hW

/-- Concrete partition-function integrability from:
    1) square-integrable/measurable UV interaction data,
    2) per-volume polynomial-decay squared-moment shifted UV-difference bounds,
    3) per-volume uniform shifted-cutoff partition-function bounds.
    This is the hard-core WP1 per-volume route to partition-function
    integrability. -/
theorem
    partition_function_integrable_of_sq_integrable_data_and_sq_moment_polynomial_bound_per_volume_and_uniform_partition_bound
    (params : Phi4Params)
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        AEStronglyMeasurable (interactionCutoff params Λ κ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_sq :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        Integrable (fun ω => (interactionCutoff params Λ κ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_conv :
      ∀ (Λ : Rectangle),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then
            ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)
            else 0)
          Filter.atTop
          (nhds 0))
    (hcutoff_ae :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
            Filter.atTop
            (nhds (interaction params Λ ω)))
    (hinteraction_meas :
      ∀ (Λ : Rectangle),
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hinteraction_sq :
      ∀ (Λ : Rectangle),
        Integrable (fun ω => (interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (betaMom : ℝ) (hbetaMom : 1 < betaMom)
    (C : Rectangle → ℝ)
    (hC_nonneg : ∀ Λ : Rectangle, 0 ≤ C Λ)
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
        ≤ C Λ * (↑(n + 1) : ℝ) ^ (-betaMom))
    (hpartition :
      ∀ (Λ : Rectangle) (q : ℝ), 0 < q →
        ∃ D : ℝ,
          (∀ n : ℕ,
            Integrable
              (fun ω : FieldConfig2D =>
                Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)))
              (freeFieldMeasure params.mass params.mass_pos)) ∧
          (∀ n : ℕ,
            ∫ ω : FieldConfig2D,
              Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
              ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D))
    (Λ : Rectangle) :
    Integrable (fun ω => Real.exp (-(interaction params Λ ω)))
      (freeFieldMeasure params.mass params.mass_pos) := by
  have hI :
      Nonempty (InteractionIntegrabilityModel params) :=
    interactionIntegrabilityModel_nonempty_of_sq_integrable_data_and_sq_moment_polynomial_bound_per_volume_and_uniform_partition_bound
      (params := params)
      hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
      hinteraction_meas hinteraction_sq
      betaMom hbetaMom C hC_nonneg hInt hM hpartition
  have hW :
      Nonempty (InteractionWeightModel params) :=
    interactionWeightModel_nonempty_of_integrability_nonempty
      (params := params) hI
  exact partition_function_integrable_of_nonempty_interactionWeightModel
    (params := params) (Λ := Λ) hW

/-- Concrete partition-function positivity from:
    1) square-integrable/measurable UV interaction data,
    2) fixed higher even moment order `2j` (`j > 0`) with per-volume
       polynomial-decay shifted UV-difference bounds,
    3) per-volume uniform shifted-cutoff partition-function bounds. -/
theorem
    partition_function_pos_of_sq_integrable_data_and_higher_moment_polynomial_bound_per_volume_and_uniform_partition_bound
    (params : Phi4Params)
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        AEStronglyMeasurable (interactionCutoff params Λ κ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_sq :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        Integrable (fun ω => (interactionCutoff params Λ κ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_conv :
      ∀ (Λ : Rectangle),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then
            ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)
            else 0)
          Filter.atTop
          (nhds 0))
    (hcutoff_ae :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
            Filter.atTop
            (nhds (interaction params Λ ω)))
    (hinteraction_meas :
      ∀ (Λ : Rectangle),
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hinteraction_sq :
      ∀ (Λ : Rectangle),
        Integrable (fun ω => (interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (j : ℕ) (hj : 0 < j)
    (betaMom : ℝ) (hbetaMom : 1 < betaMom)
    (C : Rectangle → ℝ)
    (hC_nonneg : ∀ Λ : Rectangle, 0 ≤ C Λ)
    (hInt :
      ∀ (Λ : Rectangle) (n : ℕ),
        Integrable
          (fun ω : FieldConfig2D =>
            |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω| ^ (2 * j))
          (freeFieldMeasure params.mass params.mass_pos))
    (hM :
      ∀ (Λ : Rectangle) (n : ℕ),
        ∫ ω : FieldConfig2D,
          |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω| ^ (2 * j)
          ∂(freeFieldMeasure params.mass params.mass_pos)
        ≤ C Λ * (↑(n + 1) : ℝ) ^ (-betaMom))
    (hpartition :
      ∀ (Λ : Rectangle) (q : ℝ), 0 < q →
        ∃ D : ℝ,
          (∀ n : ℕ,
            Integrable
              (fun ω : FieldConfig2D =>
                Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)))
              (freeFieldMeasure params.mass params.mass_pos)) ∧
          (∀ n : ℕ,
            ∫ ω : FieldConfig2D,
              Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
              ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D))
    (Λ : Rectangle) :
    0 < ∫ ω, Real.exp (-(interaction params Λ ω))
        ∂(freeFieldMeasure params.mass params.mass_pos) := by
  have hI :
      Nonempty (InteractionIntegrabilityModel params) :=
    interactionIntegrabilityModel_nonempty_of_sq_integrable_data_and_higher_moment_polynomial_bound_per_volume_and_uniform_partition_bound
      (params := params)
      hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
      hinteraction_meas hinteraction_sq
      j hj betaMom hbetaMom C hC_nonneg hInt hM hpartition
  have hW :
      Nonempty (InteractionWeightModel params) :=
    interactionWeightModel_nonempty_of_integrability_nonempty
      (params := params) hI
  exact partition_function_pos_of_nonempty_interactionWeightModel
    (params := params) (Λ := Λ) hW

/-- Concrete partition-function integrability from:
    1) square-integrable/measurable UV interaction data,
    2) fixed higher even moment order `2j` (`j > 0`) with per-volume
       polynomial-decay shifted UV-difference bounds,
    3) per-volume uniform shifted-cutoff partition-function bounds. -/
theorem
    partition_function_integrable_of_sq_integrable_data_and_higher_moment_polynomial_bound_per_volume_and_uniform_partition_bound
    (params : Phi4Params)
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        AEStronglyMeasurable (interactionCutoff params Λ κ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_sq :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        Integrable (fun ω => (interactionCutoff params Λ κ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_conv :
      ∀ (Λ : Rectangle),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then
            ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)
            else 0)
          Filter.atTop
          (nhds 0))
    (hcutoff_ae :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
            Filter.atTop
            (nhds (interaction params Λ ω)))
    (hinteraction_meas :
      ∀ (Λ : Rectangle),
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hinteraction_sq :
      ∀ (Λ : Rectangle),
        Integrable (fun ω => (interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (j : ℕ) (hj : 0 < j)
    (betaMom : ℝ) (hbetaMom : 1 < betaMom)
    (C : Rectangle → ℝ)
    (hC_nonneg : ∀ Λ : Rectangle, 0 ≤ C Λ)
    (hInt :
      ∀ (Λ : Rectangle) (n : ℕ),
        Integrable
          (fun ω : FieldConfig2D =>
            |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω| ^ (2 * j))
          (freeFieldMeasure params.mass params.mass_pos))
    (hM :
      ∀ (Λ : Rectangle) (n : ℕ),
        ∫ ω : FieldConfig2D,
          |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω| ^ (2 * j)
          ∂(freeFieldMeasure params.mass params.mass_pos)
        ≤ C Λ * (↑(n + 1) : ℝ) ^ (-betaMom))
    (hpartition :
      ∀ (Λ : Rectangle) (q : ℝ), 0 < q →
        ∃ D : ℝ,
          (∀ n : ℕ,
            Integrable
              (fun ω : FieldConfig2D =>
                Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)))
              (freeFieldMeasure params.mass params.mass_pos)) ∧
          (∀ n : ℕ,
            ∫ ω : FieldConfig2D,
              Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
              ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D))
    (Λ : Rectangle) :
    Integrable (fun ω => Real.exp (-(interaction params Λ ω)))
      (freeFieldMeasure params.mass params.mass_pos) := by
  have hI :
      Nonempty (InteractionIntegrabilityModel params) :=
    interactionIntegrabilityModel_nonempty_of_sq_integrable_data_and_higher_moment_polynomial_bound_per_volume_and_uniform_partition_bound
      (params := params)
      hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
      hinteraction_meas hinteraction_sq
      j hj betaMom hbetaMom C hC_nonneg hInt hM hpartition
  have hW :
      Nonempty (InteractionWeightModel params) :=
    interactionWeightModel_nonempty_of_integrability_nonempty
      (params := params) hI
  exact partition_function_integrable_of_nonempty_interactionWeightModel
    (params := params) (Λ := Λ) hW

/-- Concrete partition-function positivity from:
    1) square-integrable/measurable UV interaction data,
    2) per-volume polynomial-decay squared-moment shifted UV-difference bounds
       with graph-natural decay rate `(n+2)^(-β)`,
    3) per-volume uniform shifted-cutoff partition-function bounds. -/
theorem
    partition_function_pos_of_sq_integrable_data_and_sq_moment_polynomial_bound_per_volume_and_uniform_partition_bound_of_succ_succ
    (params : Phi4Params)
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        AEStronglyMeasurable (interactionCutoff params Λ κ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_sq :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        Integrable (fun ω => (interactionCutoff params Λ κ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_conv :
      ∀ (Λ : Rectangle),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then
            ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)
            else 0)
          Filter.atTop
          (nhds 0))
    (hcutoff_ae :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
            Filter.atTop
            (nhds (interaction params Λ ω)))
    (hinteraction_meas :
      ∀ (Λ : Rectangle),
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hinteraction_sq :
      ∀ (Λ : Rectangle),
        Integrable (fun ω => (interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (betaMom : ℝ) (hbetaMom : 1 < betaMom)
    (C : Rectangle → ℝ)
    (hC_nonneg : ∀ Λ : Rectangle, 0 ≤ C Λ)
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
        ≤ C Λ * (↑(n + 2) : ℝ) ^ (-betaMom))
    (hpartition :
      ∀ (Λ : Rectangle) (q : ℝ), 0 < q →
        ∃ D : ℝ,
          (∀ n : ℕ,
            Integrable
              (fun ω : FieldConfig2D =>
                Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)))
              (freeFieldMeasure params.mass params.mass_pos)) ∧
          (∀ n : ℕ,
            ∫ ω : FieldConfig2D,
              Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
              ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D))
    (Λ : Rectangle) :
    0 < ∫ ω, Real.exp (-(interaction params Λ ω))
        ∂(freeFieldMeasure params.mass params.mass_pos) := by
  have hI :
      Nonempty (InteractionIntegrabilityModel params) :=
    interactionIntegrabilityModel_nonempty_of_sq_integrable_data_and_sq_moment_polynomial_bound_per_volume_and_uniform_partition_bound_of_succ_succ
      (params := params)
      hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
      hinteraction_meas hinteraction_sq
      betaMom hbetaMom C hC_nonneg hInt hM hpartition
  have hW :
      Nonempty (InteractionWeightModel params) :=
    interactionWeightModel_nonempty_of_integrability_nonempty
      (params := params) hI
  exact partition_function_pos_of_nonempty_interactionWeightModel
    (params := params) (Λ := Λ) hW

/-- Concrete partition-function integrability from:
    1) square-integrable/measurable UV interaction data,
    2) per-volume polynomial-decay squared-moment shifted UV-difference bounds
       with graph-natural decay rate `(n+2)^(-β)`,
    3) per-volume uniform shifted-cutoff partition-function bounds. -/
theorem
    partition_function_integrable_of_sq_integrable_data_and_sq_moment_polynomial_bound_per_volume_and_uniform_partition_bound_of_succ_succ
    (params : Phi4Params)
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        AEStronglyMeasurable (interactionCutoff params Λ κ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_sq :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        Integrable (fun ω => (interactionCutoff params Λ κ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_conv :
      ∀ (Λ : Rectangle),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then
            ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)
            else 0)
          Filter.atTop
          (nhds 0))
    (hcutoff_ae :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
            Filter.atTop
            (nhds (interaction params Λ ω)))
    (hinteraction_meas :
      ∀ (Λ : Rectangle),
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hinteraction_sq :
      ∀ (Λ : Rectangle),
        Integrable (fun ω => (interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (betaMom : ℝ) (hbetaMom : 1 < betaMom)
    (C : Rectangle → ℝ)
    (hC_nonneg : ∀ Λ : Rectangle, 0 ≤ C Λ)
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
        ≤ C Λ * (↑(n + 2) : ℝ) ^ (-betaMom))
    (hpartition :
      ∀ (Λ : Rectangle) (q : ℝ), 0 < q →
        ∃ D : ℝ,
          (∀ n : ℕ,
            Integrable
              (fun ω : FieldConfig2D =>
                Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)))
              (freeFieldMeasure params.mass params.mass_pos)) ∧
          (∀ n : ℕ,
            ∫ ω : FieldConfig2D,
              Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
              ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D))
    (Λ : Rectangle) :
    Integrable (fun ω => Real.exp (-(interaction params Λ ω)))
      (freeFieldMeasure params.mass params.mass_pos) := by
  have hI :
      Nonempty (InteractionIntegrabilityModel params) :=
    interactionIntegrabilityModel_nonempty_of_sq_integrable_data_and_sq_moment_polynomial_bound_per_volume_and_uniform_partition_bound_of_succ_succ
      (params := params)
      hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
      hinteraction_meas hinteraction_sq
      betaMom hbetaMom C hC_nonneg hInt hM hpartition
  have hW :
      Nonempty (InteractionWeightModel params) :=
    interactionWeightModel_nonempty_of_integrability_nonempty
      (params := params) hI
  exact partition_function_integrable_of_nonempty_interactionWeightModel
    (params := params) (Λ := Λ) hW

/-- Concrete partition-function positivity from:
    1) square-integrable/measurable UV interaction data,
    2) fixed higher even moment order `2j` (`j > 0`) with per-volume
       polynomial-decay shifted UV-difference bounds and graph-natural decay
       rate `(n+2)^(-β)`,
    3) per-volume uniform shifted-cutoff partition-function bounds. -/
theorem
    partition_function_pos_of_sq_integrable_data_and_higher_moment_polynomial_bound_per_volume_and_uniform_partition_bound_of_succ_succ
    (params : Phi4Params)
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        AEStronglyMeasurable (interactionCutoff params Λ κ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_sq :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        Integrable (fun ω => (interactionCutoff params Λ κ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_conv :
      ∀ (Λ : Rectangle),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then
            ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)
            else 0)
          Filter.atTop
          (nhds 0))
    (hcutoff_ae :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
            Filter.atTop
            (nhds (interaction params Λ ω)))
    (hinteraction_meas :
      ∀ (Λ : Rectangle),
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hinteraction_sq :
      ∀ (Λ : Rectangle),
        Integrable (fun ω => (interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (j : ℕ) (hj : 0 < j)
    (betaMom : ℝ) (hbetaMom : 1 < betaMom)
    (C : Rectangle → ℝ)
    (hC_nonneg : ∀ Λ : Rectangle, 0 ≤ C Λ)
    (hInt :
      ∀ (Λ : Rectangle) (n : ℕ),
        Integrable
          (fun ω : FieldConfig2D =>
            |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω| ^ (2 * j))
          (freeFieldMeasure params.mass params.mass_pos))
    (hM :
      ∀ (Λ : Rectangle) (n : ℕ),
        ∫ ω : FieldConfig2D,
          |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω| ^ (2 * j)
          ∂(freeFieldMeasure params.mass params.mass_pos)
        ≤ C Λ * (↑(n + 2) : ℝ) ^ (-betaMom))
    (hpartition :
      ∀ (Λ : Rectangle) (q : ℝ), 0 < q →
        ∃ D : ℝ,
          (∀ n : ℕ,
            Integrable
              (fun ω : FieldConfig2D =>
                Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)))
              (freeFieldMeasure params.mass params.mass_pos)) ∧
          (∀ n : ℕ,
            ∫ ω : FieldConfig2D,
              Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
              ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D))
    (Λ : Rectangle) :
    0 < ∫ ω, Real.exp (-(interaction params Λ ω))
        ∂(freeFieldMeasure params.mass params.mass_pos) := by
  have hI :
      Nonempty (InteractionIntegrabilityModel params) :=
    interactionIntegrabilityModel_nonempty_of_sq_integrable_data_and_higher_moment_polynomial_bound_per_volume_and_uniform_partition_bound_of_succ_succ
      (params := params)
      hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
      hinteraction_meas hinteraction_sq
      j hj betaMom hbetaMom C hC_nonneg hInt hM hpartition
  have hW :
      Nonempty (InteractionWeightModel params) :=
    interactionWeightModel_nonempty_of_integrability_nonempty
      (params := params) hI
  exact partition_function_pos_of_nonempty_interactionWeightModel
    (params := params) (Λ := Λ) hW

/-- Concrete partition-function integrability from:
    1) square-integrable/measurable UV interaction data,
    2) fixed higher even moment order `2j` (`j > 0`) with per-volume
       polynomial-decay shifted UV-difference bounds and graph-natural decay
       rate `(n+2)^(-β)`,
    3) per-volume uniform shifted-cutoff partition-function bounds. -/
theorem
    partition_function_integrable_of_sq_integrable_data_and_higher_moment_polynomial_bound_per_volume_and_uniform_partition_bound_of_succ_succ
    (params : Phi4Params)
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        AEStronglyMeasurable (interactionCutoff params Λ κ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_sq :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        Integrable (fun ω => (interactionCutoff params Λ κ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_conv :
      ∀ (Λ : Rectangle),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then
            ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)
            else 0)
          Filter.atTop
          (nhds 0))
    (hcutoff_ae :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
            Filter.atTop
            (nhds (interaction params Λ ω)))
    (hinteraction_meas :
      ∀ (Λ : Rectangle),
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hinteraction_sq :
      ∀ (Λ : Rectangle),
        Integrable (fun ω => (interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (j : ℕ) (hj : 0 < j)
    (betaMom : ℝ) (hbetaMom : 1 < betaMom)
    (C : Rectangle → ℝ)
    (hC_nonneg : ∀ Λ : Rectangle, 0 ≤ C Λ)
    (hInt :
      ∀ (Λ : Rectangle) (n : ℕ),
        Integrable
          (fun ω : FieldConfig2D =>
            |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω| ^ (2 * j))
          (freeFieldMeasure params.mass params.mass_pos))
    (hM :
      ∀ (Λ : Rectangle) (n : ℕ),
        ∫ ω : FieldConfig2D,
          |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω| ^ (2 * j)
          ∂(freeFieldMeasure params.mass params.mass_pos)
        ≤ C Λ * (↑(n + 2) : ℝ) ^ (-betaMom))
    (hpartition :
      ∀ (Λ : Rectangle) (q : ℝ), 0 < q →
        ∃ D : ℝ,
          (∀ n : ℕ,
            Integrable
              (fun ω : FieldConfig2D =>
                Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)))
              (freeFieldMeasure params.mass params.mass_pos)) ∧
          (∀ n : ℕ,
            ∫ ω : FieldConfig2D,
              Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
              ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D))
    (Λ : Rectangle) :
    Integrable (fun ω => Real.exp (-(interaction params Λ ω)))
      (freeFieldMeasure params.mass params.mass_pos) := by
  have hI :
      Nonempty (InteractionIntegrabilityModel params) :=
    interactionIntegrabilityModel_nonempty_of_sq_integrable_data_and_higher_moment_polynomial_bound_per_volume_and_uniform_partition_bound_of_succ_succ
      (params := params)
      hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
      hinteraction_meas hinteraction_sq
      j hj betaMom hbetaMom C hC_nonneg hInt hM hpartition
  have hW :
      Nonempty (InteractionWeightModel params) :=
    interactionWeightModel_nonempty_of_integrability_nonempty
      (params := params) hI
  exact partition_function_integrable_of_nonempty_interactionWeightModel
    (params := params) (Λ := Λ) hW

/-- Concrete partition-function positivity from:
    shifted-index exponential tails of natural Wick sublevel bad events
    `{ω | ∃ x ∈ Λ, wickPower(κ_{n+1}) ω x < -B}`.
    This discharges `InteractionWeightModel` via proved interaction bridges. -/
theorem
    partition_function_pos_of_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets
    (params : Phi4Params)
    [InteractionUVModel params]
    (hwick_bad :
      ∀ Λ : Rectangle, ∃ B : ℝ, ∃ C : ℝ≥0∞, ∃ α : ℝ,
        C ≠ ⊤ ∧ 0 < α ∧
        (∀ n : ℕ,
          (freeFieldMeasure params.mass params.mass_pos)
            {ω : FieldConfig2D |
              ∃ x ∈ Λ.toSet,
                wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x < -B}
            ≤ C * (ENNReal.ofReal (Real.exp (-α))) ^ n) ∧
        MeasurableSet Λ.toSet ∧
        volume Λ.toSet ≠ ∞ ∧
        (∀ n : ℕ, ∀ ω : FieldConfig2D,
          IntegrableOn
            (fun x => wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x)
            Λ.toSet volume))
    (Λ : Rectangle) :
    0 < ∫ ω, Real.exp (-(interaction params Λ ω))
        ∂(freeFieldMeasure params.mass params.mass_pos) := by
  have hW :
      Nonempty (InteractionWeightModel params) :=
    interactionWeightModel_nonempty_of_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets
      (params := params) hwick_bad
  exact partition_function_pos_of_nonempty_interactionWeightModel
    (params := params) (Λ := Λ) hW

/-- Concrete partition-function integrability from:
    shifted-index exponential tails of natural Wick sublevel bad events
    `{ω | ∃ x ∈ Λ, wickPower(κ_{n+1}) ω x < -B}`.
    This discharges `InteractionWeightModel` via proved interaction bridges. -/
theorem
    partition_function_integrable_of_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets
    (params : Phi4Params)
    [InteractionUVModel params]
    (hwick_bad :
      ∀ Λ : Rectangle, ∃ B : ℝ, ∃ C : ℝ≥0∞, ∃ α : ℝ,
        C ≠ ⊤ ∧ 0 < α ∧
        (∀ n : ℕ,
          (freeFieldMeasure params.mass params.mass_pos)
            {ω : FieldConfig2D |
              ∃ x ∈ Λ.toSet,
                wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x < -B}
            ≤ C * (ENNReal.ofReal (Real.exp (-α))) ^ n) ∧
        MeasurableSet Λ.toSet ∧
        volume Λ.toSet ≠ ∞ ∧
        (∀ n : ℕ, ∀ ω : FieldConfig2D,
          IntegrableOn
            (fun x => wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x)
            Λ.toSet volume))
    (Λ : Rectangle) :
    Integrable (fun ω => Real.exp (-(interaction params Λ ω)))
      (freeFieldMeasure params.mass params.mass_pos) := by
  have hW :
      Nonempty (InteractionWeightModel params) :=
    interactionWeightModel_nonempty_of_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets
      (params := params) hwick_bad
  exact partition_function_integrable_of_nonempty_interactionWeightModel
    (params := params) (Λ := Λ) hW

/-- Concrete partition-function positivity from:
    1) square-integrable/measurable UV interaction data, and
    2) shifted-index exponential tails of natural Wick sublevel bad events
       `{ω | ∃ x ∈ Λ, wickPower(κ_{n+1}) ω x < -B}`. -/
theorem
    partition_function_pos_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets
    (params : Phi4Params)
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        AEStronglyMeasurable (interactionCutoff params Λ κ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_sq :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        Integrable (fun ω => (interactionCutoff params Λ κ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_conv :
      ∀ (Λ : Rectangle),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then
            ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)
            else 0)
          Filter.atTop
          (nhds 0))
    (hcutoff_ae :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
            Filter.atTop
            (nhds (interaction params Λ ω)))
    (hinteraction_meas :
      ∀ (Λ : Rectangle),
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hinteraction_sq :
      ∀ (Λ : Rectangle),
        Integrable (fun ω => (interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hwick_bad :
      ∀ Λ : Rectangle, ∃ B : ℝ, ∃ C : ℝ≥0∞, ∃ α : ℝ,
        C ≠ ⊤ ∧ 0 < α ∧
        (∀ n : ℕ,
          (freeFieldMeasure params.mass params.mass_pos)
            {ω : FieldConfig2D |
              ∃ x ∈ Λ.toSet,
                wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x < -B}
            ≤ C * (ENNReal.ofReal (Real.exp (-α))) ^ n) ∧
        MeasurableSet Λ.toSet ∧
        volume Λ.toSet ≠ ∞ ∧
        (∀ n : ℕ, ∀ ω : FieldConfig2D,
          IntegrableOn
            (fun x => wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x)
            Λ.toSet volume))
    (Λ : Rectangle) :
    0 < ∫ ω, Real.exp (-(interaction params Λ ω))
        ∂(freeFieldMeasure params.mass params.mass_pos) := by
  have hW :
      Nonempty (InteractionWeightModel params) :=
    interactionWeightModel_nonempty_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets
      (params := params)
      hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
      hinteraction_meas hinteraction_sq hwick_bad
  exact partition_function_pos_of_nonempty_interactionWeightModel
    (params := params) (Λ := Λ) hW

/-- Concrete partition-function integrability from:
    1) square-integrable/measurable UV interaction data, and
    2) shifted-index exponential tails of natural Wick sublevel bad events
       `{ω | ∃ x ∈ Λ, wickPower(κ_{n+1}) ω x < -B}`. -/
theorem
    partition_function_integrable_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets
    (params : Phi4Params)
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        AEStronglyMeasurable (interactionCutoff params Λ κ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_sq :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        Integrable (fun ω => (interactionCutoff params Λ κ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_conv :
      ∀ (Λ : Rectangle),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then
            ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)
            else 0)
          Filter.atTop
          (nhds 0))
    (hcutoff_ae :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
            Filter.atTop
            (nhds (interaction params Λ ω)))
    (hinteraction_meas :
      ∀ (Λ : Rectangle),
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hinteraction_sq :
      ∀ (Λ : Rectangle),
        Integrable (fun ω => (interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hwick_bad :
      ∀ Λ : Rectangle, ∃ B : ℝ, ∃ C : ℝ≥0∞, ∃ α : ℝ,
        C ≠ ⊤ ∧ 0 < α ∧
        (∀ n : ℕ,
          (freeFieldMeasure params.mass params.mass_pos)
            {ω : FieldConfig2D |
              ∃ x ∈ Λ.toSet,
                wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x < -B}
            ≤ C * (ENNReal.ofReal (Real.exp (-α))) ^ n) ∧
        MeasurableSet Λ.toSet ∧
        volume Λ.toSet ≠ ∞ ∧
        (∀ n : ℕ, ∀ ω : FieldConfig2D,
          IntegrableOn
            (fun x => wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x)
            Λ.toSet volume))
    (Λ : Rectangle) :
    Integrable (fun ω => Real.exp (-(interaction params Λ ω)))
      (freeFieldMeasure params.mass params.mass_pos) := by
  have hW :
      Nonempty (InteractionWeightModel params) :=
    interactionWeightModel_nonempty_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets
      (params := params)
      hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
      hinteraction_meas hinteraction_sq hwick_bad
  exact partition_function_integrable_of_nonempty_interactionWeightModel
    (params := params) (Λ := Λ) hW

end

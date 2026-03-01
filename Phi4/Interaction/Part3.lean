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

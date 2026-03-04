/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.Interaction.Part2

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

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

/-
  NOTE:
  Thin `[InteractionUVModel params]` forwarding wrappers into
  `interactionWeightModel_nonempty_of_*` were removed to limit route bloat.
  Canonical path: construct `InteractionWeightModel` via an assumption-explicit
  theorem, then lift with `interactionIntegrabilityModel_nonempty_of_uv_weight_nonempty`.
-/

/-- Core square-data composition: once UV data is promoted to
    `InteractionUVModel` and a constructive `InteractionWeightModel` endpoint is
    available, obtain `InteractionIntegrabilityModel` without route wrappers. -/
theorem interactionIntegrabilityModel_nonempty_from_sq_integrable_data_and_weight
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
    (hW : Nonempty (InteractionWeightModel params)) :
    Nonempty (InteractionIntegrabilityModel params) := by
  rcases interactionUVModel_nonempty_of_sq_integrable_data
      (params := params)
      hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
      hinteraction_meas hinteraction_sq with ⟨huv⟩
  exact interactionIntegrabilityModel_nonempty_of_uv_weight_nonempty
    (params := params) ⟨huv⟩ hW

/-- Construct `InteractionIntegrabilityModel` from:
    1. square-integrability/measurability UV data (promoted to
       `InteractionUVModel`), and
    2. shifted-index exponential tails of natural Wick sublevel bad events
       `{ω | ∃ x ∈ Λ, wickPower(κ_{n+1}) ω x < -B}`. -/
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
  refine interactionIntegrabilityModel_nonempty_from_sq_integrable_data_and_weight
    (params := params)
    hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
    hinteraction_meas hinteraction_sq ?_
  exact
    interactionWeightModel_nonempty_of_sq_moment_polynomial_bound_per_volume_and_uniform_partition_bound_of_succ_succ
      (params := params) (β := β) hβ (C := C) hC_nonneg hInt hM
      (hcutoff_meas := fun Λ n => by
        exact interactionCutoff_standardSeq_succ_aestronglyMeasurable
          (params := params) hcutoff_meas Λ n)
      hpartition

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
  refine interactionIntegrabilityModel_nonempty_from_sq_integrable_data_and_weight
    (params := params)
    hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
    hinteraction_meas hinteraction_sq ?_
  exact
    interactionWeightModel_nonempty_of_sq_moment_polynomial_bound_per_volume_and_uniform_partition_bound
      (params := params) (β := β) hβ (C := C) hC_nonneg hInt hM
      (hcutoff_meas := fun Λ n => by
        exact interactionCutoff_standardSeq_succ_aestronglyMeasurable
          (params := params) hcutoff_meas Λ n)
      hpartition

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
  refine interactionIntegrabilityModel_nonempty_from_sq_integrable_data_and_weight
    (params := params)
    hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
    hinteraction_meas hinteraction_sq ?_
  exact
    interactionWeightModel_nonempty_of_higher_moment_polynomial_bound_per_volume_and_uniform_partition_bound
      (params := params) (j := j) (hj := hj)
      (β := β) hβ (C := C) hC_nonneg hInt hM
      (hcutoff_meas := fun Λ n => by
        exact interactionCutoff_standardSeq_succ_aestronglyMeasurable
          (params := params) hcutoff_meas Λ n)
      hpartition

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
  refine interactionIntegrabilityModel_nonempty_from_sq_integrable_data_and_weight
    (params := params)
    hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
    hinteraction_meas hinteraction_sq ?_
  exact
    interactionWeightModel_nonempty_of_higher_moment_polynomial_bound_per_volume_and_uniform_partition_bound_of_succ_succ
      (params := params) (j := j) (hj := hj) (β := β) hβ (C := C) hC_nonneg hInt hM
      (hcutoff_meas := fun Λ n => by
        exact interactionCutoff_standardSeq_succ_aestronglyMeasurable
          (params := params) hcutoff_meas Λ n)
      hpartition

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
  refine interactionIntegrabilityModel_nonempty_from_sq_integrable_data_and_weight
    (params := params)
    hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
    hinteraction_meas hinteraction_sq ?_
  refine interactionWeightModel_nonempty_of_standardSeq_succ_tendsto_ae_and_geometric_exp_moment_bound
    (params := params) ?_ ?_ ?_
  · intro Λ
    exact interactionCutoff_standardSeq_succ_tendsto_ae_of_tendsto_ae
      (params := params) (Λ := Λ) (hcutoff_ae Λ)
  · intro Λ n
    exact interactionCutoff_standardSeq_succ_aestronglyMeasurable
      (params := params) hcutoff_meas Λ n
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
          exact interactionCutoff_standardSeq_succ_aestronglyMeasurable
            (params := params) hcutoff_meas Λ n)
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
          exact interactionCutoff_standardSeq_succ_aestronglyMeasurable
            (params := params) hcutoff_meas Λ n)
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

/-- Core L^p integrability endpoint from `InteractionWeightModel`. -/
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

end

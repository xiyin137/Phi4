/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.Interaction.Part1

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

/-- `Lᵖ` integrability from shifted-index summable bad sets with good-set
    cutoff lower bounds. -/
theorem exp_interaction_Lp_of_cutoff_seq_shifted_bad_set_summable
    (params : Phi4Params) (Λ : Rectangle)
    [InteractionUVModel params]
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
  exact
    exp_interaction_Lp_of_cutoff_seq_shifted_bad_set_summable_of_aestronglyMeasurable_and_standardSeq_tendsto_ae
      (params := params) (Λ := Λ)
      ((interaction_in_L2 params Λ).aestronglyMeasurable)
      (interactionCutoff_standardSeq_tendsto_ae params Λ)
      (B := B) (bad := bad) hbad_sum hcutoff_good

/-- `Lᵖ` integrability from Wick-level shifted-index summable bad sets:
    outside each bad set one has a pointwise lower bound on `wickPower 4`,
    which induces the required cutoff lower bound. -/
theorem exp_interaction_Lp_of_cutoff_seq_shifted_summable_wick_bad_sets
    (params : Phi4Params) (Λ : Rectangle)
    [InteractionUVModel params]
    (B : ℝ)
    (bad : ℕ → Set FieldConfig2D)
    (hbad_sum :
      (∑' n : ℕ,
        (freeFieldMeasure params.mass params.mass_pos) (bad n)) ≠ ∞)
    (hΛ_meas : MeasurableSet Λ.toSet)
    (hΛ_finite : volume Λ.toSet ≠ ∞)
    (hwick_int :
      ∀ n : ℕ, ∀ ω : FieldConfig2D,
        IntegrableOn
          (fun x => wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x)
          Λ.toSet volume)
    (hgood :
      ∀ n : ℕ, ∀ ω : FieldConfig2D, ω ∉ bad n →
        ∀ x ∈ Λ.toSet,
          -B ≤ wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x)
    {p : ℝ≥0∞} :
    MemLp (fun ω => Real.exp (-(interaction params Λ ω)))
      p (freeFieldMeasure params.mass params.mass_pos) := by
  rcases interactionCutoff_pointwise_lower_bounds_of_standardSeq_succ_wick_bad_sets
      (params := params) (Λ := Λ) (B := B) (bad := bad)
      hΛ_meas hΛ_finite hwick_int hgood with ⟨Bcut, hcut⟩
  exact exp_interaction_Lp_of_cutoff_seq_shifted_bad_set_summable
    (params := params) (Λ := Λ) (B := Bcut) (bad := bad) hbad_sum hcut

/-- `Lᵖ` integrability from Wick-level shifted-index geometric bad-set tails
    (`μ(bad n) ≤ C * r^n`, `r < 1`) plus good-set lower bounds on `wickPower 4`. -/
theorem exp_interaction_Lp_of_cutoff_seq_shifted_geometric_wick_bad_sets
    (params : Phi4Params) (Λ : Rectangle)
    [InteractionUVModel params]
    (B : ℝ)
    (bad : ℕ → Set FieldConfig2D)
    (C r : ℝ≥0∞) (hC : C ≠ ⊤) (hr : r < 1)
    (hbad_le :
      ∀ n : ℕ,
        (freeFieldMeasure params.mass params.mass_pos) (bad n) ≤ C * r ^ n)
    (hΛ_meas : MeasurableSet Λ.toSet)
    (hΛ_finite : volume Λ.toSet ≠ ∞)
    (hwick_int :
      ∀ n : ℕ, ∀ ω : FieldConfig2D,
        IntegrableOn
          (fun x => wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x)
          Λ.toSet volume)
    (hgood :
      ∀ n : ℕ, ∀ ω : FieldConfig2D, ω ∉ bad n →
        ∀ x ∈ Λ.toSet,
          -B ≤ wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x)
    {p : ℝ≥0∞} :
    MemLp (fun ω => Real.exp (-(interaction params Λ ω)))
      p (freeFieldMeasure params.mass params.mass_pos) := by
  have hgeom_lt : (∑' n : ℕ, r ^ n) < ∞ :=
    (tsum_geometric_lt_top).2 hr
  have hsum_lt : (∑' n : ℕ, C * r ^ n) < ∞ := by
    have hC_lt : C < ∞ := by exact lt_of_le_of_ne le_top hC
    rw [ENNReal.tsum_mul_left]
    exact ENNReal.mul_lt_top hC_lt hgeom_lt
  have hbad_sum :
      (∑' n : ℕ, (freeFieldMeasure params.mass params.mass_pos) (bad n)) ≠ ∞ :=
    ne_top_of_le_ne_top (ne_of_lt hsum_lt) (ENNReal.tsum_le_tsum hbad_le)
  exact exp_interaction_Lp_of_cutoff_seq_shifted_summable_wick_bad_sets
    (params := params) (Λ := Λ) (B := B) (bad := bad) hbad_sum
    hΛ_meas hΛ_finite hwick_int hgood

/-- `Lᵖ` integrability from Wick-level shifted-index exponential bad-set tails
    (`μ(bad n) ≤ C * exp(-α n)`, `α > 0`) plus good-set lower bounds on
    `wickPower 4`. -/
theorem exp_interaction_Lp_of_cutoff_seq_shifted_exponential_wick_bad_sets
    (params : Phi4Params) (Λ : Rectangle)
    [InteractionUVModel params]
    (B : ℝ)
    (bad : ℕ → Set FieldConfig2D)
    (C : ℝ≥0∞) (α : ℝ) (hC : C ≠ ⊤) (hα : 0 < α)
    (hbad_le :
      ∀ n : ℕ,
        (freeFieldMeasure params.mass params.mass_pos) (bad n)
          ≤ C * (ENNReal.ofReal (Real.exp (-α))) ^ n)
    (hΛ_meas : MeasurableSet Λ.toSet)
    (hΛ_finite : volume Λ.toSet ≠ ∞)
    (hwick_int :
      ∀ n : ℕ, ∀ ω : FieldConfig2D,
        IntegrableOn
          (fun x => wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x)
          Λ.toSet volume)
    (hgood :
      ∀ n : ℕ, ∀ ω : FieldConfig2D, ω ∉ bad n →
        ∀ x ∈ Λ.toSet,
          -B ≤ wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x)
    {p : ℝ≥0∞} :
    MemLp (fun ω => Real.exp (-(interaction params Λ ω)))
      p (freeFieldMeasure params.mass params.mass_pos) := by
  have hr : ENNReal.ofReal (Real.exp (-α)) < 1 := by
    refine (ENNReal.ofReal_lt_one).2 ?_
    have hneg : -α < 0 := by linarith
    exact Real.exp_lt_one_iff.mpr hneg
  exact exp_interaction_Lp_of_cutoff_seq_shifted_geometric_wick_bad_sets
    (params := params) (Λ := Λ) (B := B) (bad := bad)
    (C := C) (r := ENNReal.ofReal (Real.exp (-α))) hC hr hbad_le
    hΛ_meas hΛ_finite hwick_int hgood

/-- `Lᵖ` integrability from shifted-index summable tails of the natural Wick
    sublevel bad events
    `{ω | ∃ x ∈ Λ, wickPower(κ_{n+1}) ω x < -B}`. -/
theorem exp_interaction_Lp_of_cutoff_seq_shifted_summable_wick_sublevel_bad_sets
    (params : Phi4Params) (Λ : Rectangle)
    [InteractionUVModel params]
    (B : ℝ)
    (hbad_sum :
      (∑' n : ℕ,
        (freeFieldMeasure params.mass params.mass_pos)
          {ω : FieldConfig2D |
            ∃ x ∈ Λ.toSet,
              wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x < -B}) ≠ ∞)
    (hΛ_meas : MeasurableSet Λ.toSet)
    (hΛ_finite : volume Λ.toSet ≠ ∞)
    (hwick_int :
      ∀ n : ℕ, ∀ ω : FieldConfig2D,
        IntegrableOn
          (fun x => wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x)
          Λ.toSet volume)
    {p : ℝ≥0∞} :
    MemLp (fun ω => Real.exp (-(interaction params Λ ω)))
      p (freeFieldMeasure params.mass params.mass_pos) := by
  let bad : ℕ → Set FieldConfig2D := fun n =>
    {ω : FieldConfig2D |
      ∃ x ∈ Λ.toSet,
        wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x < -B}
  have hbad_sum' :
      (∑' n : ℕ, (freeFieldMeasure params.mass params.mass_pos) (bad n)) ≠ ∞ := by
    simpa [bad] using hbad_sum
  have hgood :
      ∀ n : ℕ, ∀ ω : FieldConfig2D, ω ∉ bad n →
        ∀ x ∈ Λ.toSet,
          -B ≤ wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x := by
    intro n ω hω x hx
    by_contra hlt
    have hlt' :
        wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x < -B :=
      lt_of_not_ge hlt
    exact hω ⟨x, hx, hlt'⟩
  exact exp_interaction_Lp_of_cutoff_seq_shifted_summable_wick_bad_sets
    (params := params) (Λ := Λ) (B := B) (bad := bad)
    hbad_sum' hΛ_meas hΛ_finite hwick_int hgood

/-- `Lᵖ` integrability from shifted-index geometric tails of the natural Wick
    sublevel bad events
    `{ω | ∃ x ∈ Λ, wickPower(κ_{n+1}) ω x < -B}`. -/
theorem exp_interaction_Lp_of_cutoff_seq_shifted_geometric_wick_sublevel_bad_sets
    (params : Phi4Params) (Λ : Rectangle)
    [InteractionUVModel params]
    (B : ℝ)
    (C r : ℝ≥0∞) (hC : C ≠ ⊤) (hr : r < 1)
    (hbad_le :
      ∀ n : ℕ,
        (freeFieldMeasure params.mass params.mass_pos)
          {ω : FieldConfig2D |
            ∃ x ∈ Λ.toSet,
              wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x < -B}
          ≤ C * r ^ n)
    (hΛ_meas : MeasurableSet Λ.toSet)
    (hΛ_finite : volume Λ.toSet ≠ ∞)
    (hwick_int :
      ∀ n : ℕ, ∀ ω : FieldConfig2D,
        IntegrableOn
          (fun x => wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x)
          Λ.toSet volume)
    {p : ℝ≥0∞} :
    MemLp (fun ω => Real.exp (-(interaction params Λ ω)))
      p (freeFieldMeasure params.mass params.mass_pos) := by
  let bad : ℕ → Set FieldConfig2D := fun n =>
    {ω : FieldConfig2D |
      ∃ x ∈ Λ.toSet,
        wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x < -B}
  have hbad_le' :
      ∀ n : ℕ,
        (freeFieldMeasure params.mass params.mass_pos) (bad n) ≤ C * r ^ n := by
    intro n
    simpa [bad] using hbad_le n
  have hgood :
      ∀ n : ℕ, ∀ ω : FieldConfig2D, ω ∉ bad n →
        ∀ x ∈ Λ.toSet,
          -B ≤ wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x := by
    intro n ω hω x hx
    by_contra hlt
    have hlt' :
        wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x < -B :=
      lt_of_not_ge hlt
    exact hω ⟨x, hx, hlt'⟩
  exact exp_interaction_Lp_of_cutoff_seq_shifted_geometric_wick_bad_sets
    (params := params) (Λ := Λ) (B := B) (bad := bad)
    (C := C) (r := r) hC hr hbad_le' hΛ_meas hΛ_finite hwick_int hgood

/-- `Lᵖ` integrability from shifted-index exponential tails of the natural
    Wick sublevel bad events
    `{ω | ∃ x ∈ Λ, wickPower(κ_{n+1}) ω x < -B}`. -/
theorem exp_interaction_Lp_of_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets
    (params : Phi4Params) (Λ : Rectangle)
    [InteractionUVModel params]
    (B : ℝ)
    (C : ℝ≥0∞) (α : ℝ) (hC : C ≠ ⊤) (hα : 0 < α)
    (hbad_le :
      ∀ n : ℕ,
        (freeFieldMeasure params.mass params.mass_pos)
          {ω : FieldConfig2D |
            ∃ x ∈ Λ.toSet,
              wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x < -B}
          ≤ C * (ENNReal.ofReal (Real.exp (-α))) ^ n)
    (hΛ_meas : MeasurableSet Λ.toSet)
    (hΛ_finite : volume Λ.toSet ≠ ∞)
    (hwick_int :
      ∀ n : ℕ, ∀ ω : FieldConfig2D,
        IntegrableOn
          (fun x => wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x)
          Λ.toSet volume)
    {p : ℝ≥0∞} :
    MemLp (fun ω => Real.exp (-(interaction params Λ ω)))
      p (freeFieldMeasure params.mass params.mass_pos) := by
  let bad : ℕ → Set FieldConfig2D := fun n =>
    {ω : FieldConfig2D |
      ∃ x ∈ Λ.toSet,
        wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x < -B}
  have hbad_le' :
      ∀ n : ℕ,
        (freeFieldMeasure params.mass params.mass_pos) (bad n) ≤
          C * (ENNReal.ofReal (Real.exp (-α))) ^ n := by
    intro n
    simpa [bad] using hbad_le n
  have hgood :
      ∀ n : ℕ, ∀ ω : FieldConfig2D, ω ∉ bad n →
        ∀ x ∈ Λ.toSet,
          -B ≤ wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x := by
    intro n ω hω x hx
    by_contra hlt
    have hlt' :
        wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x < -B :=
      lt_of_not_ge hlt
    exact hω ⟨x, hx, hlt'⟩
  exact exp_interaction_Lp_of_cutoff_seq_shifted_exponential_wick_bad_sets
    (params := params) (Λ := Λ) (B := B) (bad := bad)
    (C := C) (α := α) hC hα hbad_le' hΛ_meas hΛ_finite hwick_int hgood

/-- `Lᵖ` integrability of the Boltzmann weight from summable bad sets and
    good-set cutoff lower bounds. -/
theorem exp_interaction_Lp_of_cutoff_seq_bad_set_summable
    (params : Phi4Params) (Λ : Rectangle)
    [InteractionUVModel params]
    (B : ℝ)
    (bad : ℕ → Set FieldConfig2D)
    (hbad_sum :
      (∑' n : ℕ,
        (freeFieldMeasure params.mass params.mass_pos) (bad n)) ≠ ∞)
    (hcutoff_good :
      ∀ n : ℕ, ∀ ω : FieldConfig2D, ω ∉ bad n →
        -B ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω)
    {p : ℝ≥0∞} :
    MemLp (fun ω => Real.exp (-(interaction params Λ ω)))
      p (freeFieldMeasure params.mass params.mass_pos) := by
  have hcutoff_ev :
      ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
        ∀ᶠ n in Filter.atTop,
          -B ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω :=
    cutoff_seq_eventually_lower_bound_of_bad_set_summable
      params Λ B bad hbad_sum hcutoff_good
  exact exp_interaction_Lp_of_cutoff_seq_eventually_lower_bound
    (params := params) (Λ := Λ) (B := B) hcutoff_ev

/-- If bad-event measures are controlled by a sequence with finite total mass,
    then the cutoff sequence is eventually bounded below almost surely. -/
theorem cutoff_seq_eventually_lower_bound_of_summable_bad_event_bound
    (params : Phi4Params) (Λ : Rectangle) (B : ℝ)
    (ε : ℕ → ℝ≥0∞)
    (hε_sum : (∑' n : ℕ, ε n) ≠ ∞)
    (hbad_le :
      ∀ n : ℕ,
        (freeFieldMeasure params.mass params.mass_pos)
          {ω : FieldConfig2D |
            interactionCutoff params Λ (standardUVCutoffSeq n) ω < -B} ≤ ε n) :
    ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
      ∀ᶠ n in Filter.atTop,
        -B ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω := by
  have hbad_sum :
      (∑' n : ℕ,
        (freeFieldMeasure params.mass params.mass_pos)
          {ω : FieldConfig2D |
            interactionCutoff params Λ (standardUVCutoffSeq n) ω < -B}) ≠ ∞ :=
    ne_top_of_le_ne_top hε_sum (ENNReal.tsum_le_tsum hbad_le)
  exact cutoff_seq_eventually_lower_bound_of_summable_bad_event_measure params Λ B hbad_sum

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
  exact cutoff_seq_eventually_lower_bound_of_shifted_summable_bad_event_measure
    params Λ B hbad_sum

/-- `Lᵖ` integrability of the Boltzmann weight from a summable majorant on
    cutoff bad-event probabilities. -/
theorem exp_interaction_Lp_of_cutoff_seq_summable_bad_event_bound
    (params : Phi4Params) (Λ : Rectangle)
    [InteractionUVModel params]
    (B : ℝ)
    (ε : ℕ → ℝ≥0∞)
    (hε_sum : (∑' n : ℕ, ε n) ≠ ∞)
    (hbad_le :
      ∀ n : ℕ,
        (freeFieldMeasure params.mass params.mass_pos)
          {ω : FieldConfig2D |
            interactionCutoff params Λ (standardUVCutoffSeq n) ω < -B} ≤ ε n)
    {p : ℝ≥0∞} :
    MemLp (fun ω => Real.exp (-(interaction params Λ ω)))
      p (freeFieldMeasure params.mass params.mass_pos) := by
  have hcutoff_ev :
      ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
        ∀ᶠ n in Filter.atTop,
          -B ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω :=
    cutoff_seq_eventually_lower_bound_of_summable_bad_event_bound
      params Λ B ε hε_sum hbad_le
  exact exp_interaction_Lp_of_cutoff_seq_eventually_lower_bound
    (params := params) (Λ := Λ) (B := B) hcutoff_ev

/-- Shifted-index `Lᵖ` integrability from a summable majorant on
    `{interactionCutoff(κ_{n+1}) < -B}` probabilities. -/
theorem exp_interaction_Lp_of_cutoff_seq_shifted_summable_bad_event_bound
    (params : Phi4Params) (Λ : Rectangle)
    [InteractionUVModel params]
    (B : ℝ)
    (ε : ℕ → ℝ≥0∞)
    (hε_sum : (∑' n : ℕ, ε n) ≠ ∞)
    (hbad_le :
      ∀ n : ℕ,
        (freeFieldMeasure params.mass params.mass_pos)
          {ω : FieldConfig2D |
            interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω < -B} ≤ ε n)
    {p : ℝ≥0∞} :
    MemLp (fun ω => Real.exp (-(interaction params Λ ω)))
      p (freeFieldMeasure params.mass params.mass_pos) := by
  have hcutoff_ev :
      ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
        ∀ᶠ n in Filter.atTop,
          -B ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω :=
    cutoff_seq_eventually_lower_bound_of_shifted_summable_bad_event_bound
      params Λ B ε hε_sum hbad_le
  exact exp_interaction_Lp_of_cutoff_seq_eventually_lower_bound
    (params := params) (Λ := Λ) (B := B) hcutoff_ev

/-- Geometric bad-event tails imply eventual almost-sure lower bounds for the
    cutoff sequence. -/
theorem cutoff_seq_eventually_lower_bound_of_geometric_bad_event_bound
    (params : Phi4Params) (Λ : Rectangle) (B : ℝ)
    (C r : ℝ≥0∞) (hC : C ≠ ⊤) (hr : r < 1)
    (hbad_le :
      ∀ n : ℕ,
        (freeFieldMeasure params.mass params.mass_pos)
          {ω : FieldConfig2D |
            interactionCutoff params Λ (standardUVCutoffSeq n) ω < -B} ≤ C * r ^ n) :
    ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
      ∀ᶠ n in Filter.atTop,
        -B ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω := by
  have hgeom_lt : (∑' n : ℕ, r ^ n) < ∞ :=
    (tsum_geometric_lt_top).2 hr
  have hsum_lt : (∑' n : ℕ, C * r ^ n) < ∞ := by
    have hC_lt : C < ∞ := by exact lt_of_le_of_ne le_top hC
    rw [ENNReal.tsum_mul_left]
    exact ENNReal.mul_lt_top hC_lt hgeom_lt
  exact cutoff_seq_eventually_lower_bound_of_summable_bad_event_bound
    params Λ B (fun n => C * r ^ n) (ne_of_lt hsum_lt) hbad_le

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

/-- `Lᵖ` integrability of the Boltzmann weight from geometric bad-event tails
    for cutoff lower bounds. -/
theorem exp_interaction_Lp_of_cutoff_seq_geometric_bad_event_bound
    (params : Phi4Params) (Λ : Rectangle)
    [InteractionUVModel params]
    (B : ℝ)
    (C r : ℝ≥0∞) (hC : C ≠ ⊤) (hr : r < 1)
    (hbad_le :
      ∀ n : ℕ,
        (freeFieldMeasure params.mass params.mass_pos)
          {ω : FieldConfig2D |
            interactionCutoff params Λ (standardUVCutoffSeq n) ω < -B} ≤ C * r ^ n)
    {p : ℝ≥0∞} :
    MemLp (fun ω => Real.exp (-(interaction params Λ ω)))
      p (freeFieldMeasure params.mass params.mass_pos) := by
  have hcutoff_ev :
      ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
        ∀ᶠ n in Filter.atTop,
          -B ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω :=
    cutoff_seq_eventually_lower_bound_of_geometric_bad_event_bound
      params Λ B C r hC hr hbad_le
  exact exp_interaction_Lp_of_cutoff_seq_eventually_lower_bound
    (params := params) (Λ := Λ) (B := B) hcutoff_ev

/-- Shifted-index `Lᵖ` integrability from geometric bad-event tails on
    `{interactionCutoff(κ_{n+1}) < -B}`. -/
theorem exp_interaction_Lp_of_cutoff_seq_shifted_geometric_bad_event_bound
    (params : Phi4Params) (Λ : Rectangle)
    [InteractionUVModel params]
    (B : ℝ)
    (C r : ℝ≥0∞) (hC : C ≠ ⊤) (hr : r < 1)
    (hbad_le :
      ∀ n : ℕ,
        (freeFieldMeasure params.mass params.mass_pos)
          {ω : FieldConfig2D |
            interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω < -B} ≤ C * r ^ n)
    {p : ℝ≥0∞} :
    MemLp (fun ω => Real.exp (-(interaction params Λ ω)))
      p (freeFieldMeasure params.mass params.mass_pos) := by
  have hcutoff_ev :
      ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
        ∀ᶠ n in Filter.atTop,
          -B ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω :=
    cutoff_seq_eventually_lower_bound_of_shifted_geometric_bad_event_bound
      params Λ B C r hC hr hbad_le
  exact exp_interaction_Lp_of_cutoff_seq_eventually_lower_bound
    (params := params) (Λ := Λ) (B := B) hcutoff_ev

/-- Exponential bad-event tails (`μ badₙ ≤ C * exp(-α n)` with `α > 0`)
    imply eventual almost-sure lower bounds for the cutoff sequence. -/
theorem cutoff_seq_eventually_lower_bound_of_exponential_bad_event_bound
    (params : Phi4Params) (Λ : Rectangle) (B : ℝ)
    (C : ℝ≥0∞) (α : ℝ) (hC : C ≠ ⊤) (hα : 0 < α)
    (hbad_le :
      ∀ n : ℕ,
        (freeFieldMeasure params.mass params.mass_pos)
          {ω : FieldConfig2D |
            interactionCutoff params Λ (standardUVCutoffSeq n) ω < -B}
          ≤ C * (ENNReal.ofReal (Real.exp (-α))) ^ n) :
    ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
      ∀ᶠ n in Filter.atTop,
        -B ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω := by
  have hr : ENNReal.ofReal (Real.exp (-α)) < 1 := by
    refine (ENNReal.ofReal_lt_one).2 ?_
    have hneg : -α < 0 := by linarith
    exact Real.exp_lt_one_iff.mpr hneg
  exact cutoff_seq_eventually_lower_bound_of_geometric_bad_event_bound
    params Λ B C (ENNReal.ofReal (Real.exp (-α))) hC hr hbad_le

/-- Shifted-index exponential bad-event tails imply eventual almost-sure lower
    bounds for the canonical cutoff sequence. -/
theorem cutoff_seq_eventually_lower_bound_of_shifted_exponential_bad_event_bound
    (params : Phi4Params) (Λ : Rectangle) (B : ℝ)
    (C : ℝ≥0∞) (α : ℝ) (hC : C ≠ ⊤) (hα : 0 < α)
    (hbad_le :
      ∀ n : ℕ,
        (freeFieldMeasure params.mass params.mass_pos)
          {ω : FieldConfig2D |
            interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω < -B}
          ≤ C * (ENNReal.ofReal (Real.exp (-α))) ^ n) :
    ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
      ∀ᶠ n in Filter.atTop,
        -B ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω := by
  have hr : ENNReal.ofReal (Real.exp (-α)) < 1 := by
    refine (ENNReal.ofReal_lt_one).2 ?_
    have hneg : -α < 0 := by linarith
    exact Real.exp_lt_one_iff.mpr hneg
  exact cutoff_seq_eventually_lower_bound_of_shifted_geometric_bad_event_bound
    params Λ B C (ENNReal.ofReal (Real.exp (-α))) hC hr hbad_le

/-- `Lᵖ` integrability of the Boltzmann weight from exponential bad-event tails
    for cutoff lower bounds. -/
theorem exp_interaction_Lp_of_cutoff_seq_exponential_bad_event_bound
    (params : Phi4Params) (Λ : Rectangle)
    [InteractionUVModel params]
    (B : ℝ)
    (C : ℝ≥0∞) (α : ℝ) (hC : C ≠ ⊤) (hα : 0 < α)
    (hbad_le :
      ∀ n : ℕ,
        (freeFieldMeasure params.mass params.mass_pos)
          {ω : FieldConfig2D |
            interactionCutoff params Λ (standardUVCutoffSeq n) ω < -B}
          ≤ C * (ENNReal.ofReal (Real.exp (-α))) ^ n)
    {p : ℝ≥0∞} :
    MemLp (fun ω => Real.exp (-(interaction params Λ ω)))
      p (freeFieldMeasure params.mass params.mass_pos) := by
  have hcutoff_ev :
      ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
        ∀ᶠ n in Filter.atTop,
          -B ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω :=
    cutoff_seq_eventually_lower_bound_of_exponential_bad_event_bound
      params Λ B C α hC hα hbad_le
  exact exp_interaction_Lp_of_cutoff_seq_eventually_lower_bound
    (params := params) (Λ := Λ) (B := B) hcutoff_ev

/-- Shifted-index `Lᵖ` integrability from exponential bad-event tails on
    `{interactionCutoff(κ_{n+1}) < -B}`. -/
theorem exp_interaction_Lp_of_cutoff_seq_shifted_exponential_bad_event_bound
    (params : Phi4Params) (Λ : Rectangle)
    [InteractionUVModel params]
    (B : ℝ)
    (C : ℝ≥0∞) (α : ℝ) (hC : C ≠ ⊤) (hα : 0 < α)
    (hbad_le :
      ∀ n : ℕ,
        (freeFieldMeasure params.mass params.mass_pos)
          {ω : FieldConfig2D |
            interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω < -B}
          ≤ C * (ENNReal.ofReal (Real.exp (-α))) ^ n)
    {p : ℝ≥0∞} :
    MemLp (fun ω => Real.exp (-(interaction params Λ ω)))
      p (freeFieldMeasure params.mass params.mass_pos) := by
  have hcutoff_ev :
      ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
        ∀ᶠ n in Filter.atTop,
          -B ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω :=
    cutoff_seq_eventually_lower_bound_of_shifted_exponential_bad_event_bound
      params Λ B C α hC hα hbad_le
  exact exp_interaction_Lp_of_cutoff_seq_eventually_lower_bound
    (params := params) (Λ := Λ) (B := B) hcutoff_ev

/-- If per-cutoff lower bounds use a varying constant `Bₙ`, and `Bₙ ≤ B`
    eventually, then the cutoff sequence is eventually bounded below by `-B`
    almost surely. -/
theorem cutoff_seq_eventually_uniform_lower_bound_of_pointwise_bounds
    (params : Phi4Params) (Λ : Rectangle)
    (Bseq : ℕ → ℝ) (B : ℝ)
    (hcutoff_ae :
      ∀ n : ℕ,
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          -Bseq n ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω)
    (hB : ∀ᶠ n in Filter.atTop, Bseq n ≤ B) :
    ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
      ∀ᶠ n in Filter.atTop,
        -B ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω := by
  have hall :
      ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
        ∀ n : ℕ, -Bseq n ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω := by
    rw [eventually_countable_forall]
    intro n
    exact hcutoff_ae n
  filter_upwards [hall] with ω hω
  exact hB.mono (fun n hn => by
    have hωn : -Bseq n ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω := hω n
    linarith)

/-- `Lᵖ` integrability of the Boltzmann weight from variable per-cutoff
    lower bounds `-Bₙ`, provided `Bₙ` is eventually bounded above by a fixed `B`. -/
theorem exp_interaction_Lp_of_cutoff_seq_variable_lower_bounds
    (params : Phi4Params) (Λ : Rectangle)
    [InteractionUVModel params]
    (Bseq : ℕ → ℝ) (B : ℝ)
    (hcutoff_ae :
      ∀ n : ℕ,
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          -Bseq n ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω)
    (hB : ∀ᶠ n in Filter.atTop, Bseq n ≤ B)
    {p : ℝ≥0∞} :
    MemLp (fun ω => Real.exp (-(interaction params Λ ω)))
      p (freeFieldMeasure params.mass params.mass_pos) := by
  have hcutoff_ev :
      ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
        ∀ᶠ n in Filter.atTop,
          -B ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω :=
    cutoff_seq_eventually_uniform_lower_bound_of_pointwise_bounds
      params Λ Bseq B hcutoff_ae hB
  exact exp_interaction_Lp_of_cutoff_seq_eventually_lower_bound
    (params := params) (Λ := Λ) (B := B) hcutoff_ev

/-- Construct `InteractionWeightModel` from per-volume cutoff-sequence
    almost-everywhere lower bounds. -/
theorem interactionWeightModel_nonempty_of_cutoff_seq_lower_bounds
    (params : Phi4Params)
    [InteractionUVModel params]
    (hcutoff_ae :
      ∀ Λ : Rectangle, ∃ B : ℝ,
        ∀ n : ℕ,
          ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
            -B ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω) :
    Nonempty (InteractionWeightModel params) := by
  refine interactionWeightModel_nonempty_of_data params ?_
  intro Λ p _hp
  rcases hcutoff_ae Λ with ⟨B, hB⟩
  exact exp_interaction_Lp_of_cutoff_seq_lower_bounds
    (params := params) (Λ := Λ) (B := B) hB

/-- Construct `InteractionWeightModel` from per-volume shifted cutoff-sequence
    lower bounds (`κ_{n+1}`), avoiding direct `n = 0` obligations. -/
theorem interactionWeightModel_nonempty_of_cutoff_seq_succ_lower_bounds
    (params : Phi4Params)
    [InteractionUVModel params]
    (hcutoff_ae :
      ∀ Λ : Rectangle, ∃ B : ℝ,
        ∀ n : ℕ,
          ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
            -B ≤ interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω) :
    Nonempty (InteractionWeightModel params) := by
  refine interactionWeightModel_nonempty_of_data params ?_
  intro Λ p _hp
  rcases hcutoff_ae Λ with ⟨B, hB⟩
  exact exp_interaction_Lp_of_cutoff_seq_succ_lower_bounds
    (params := params) (Λ := Λ) (B := B) hB

/-- Construct `InteractionWeightModel` from per-volume cutoff-sequence
    pointwise lower bounds (`∀ ω`, `∀ n`). -/
theorem interactionWeightModel_nonempty_of_cutoff_seq_pointwise_lower_bounds
    (params : Phi4Params)
    [InteractionUVModel params]
    (hcutoff :
      ∀ Λ : Rectangle, ∃ B : ℝ,
        ∀ n : ℕ, ∀ ω : FieldConfig2D,
          -B ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω) :
    Nonempty (InteractionWeightModel params) := by
  refine interactionWeightModel_nonempty_of_cutoff_seq_lower_bounds
    (params := params) ?_
  intro Λ
  rcases hcutoff Λ with ⟨B, hB⟩
  refine ⟨B, ?_⟩
  intro n
  exact Filter.Eventually.of_forall (fun ω => hB n ω)

/-- Construct `InteractionWeightModel` from per-volume shifted cutoff-sequence
    pointwise lower bounds (`κ_{n+1}`, `∀ ω`, `∀ n`). -/
theorem interactionWeightModel_nonempty_of_cutoff_seq_succ_pointwise_lower_bounds
    (params : Phi4Params)
    [InteractionUVModel params]
    (hcutoff :
      ∀ Λ : Rectangle, ∃ B : ℝ,
        ∀ n : ℕ, ∀ ω : FieldConfig2D,
          -B ≤ interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω) :
    Nonempty (InteractionWeightModel params) := by
  refine interactionWeightModel_nonempty_of_cutoff_seq_succ_lower_bounds
    (params := params) ?_
  intro Λ
  rcases hcutoff Λ with ⟨B, hB⟩
  refine ⟨B, ?_⟩
  intro n
  exact Filter.Eventually.of_forall (fun ω => hB n ω)

/-- Construct `InteractionWeightModel` from per-volume summable bad sets with
    good-set cutoff lower bounds. -/
theorem interactionWeightModel_nonempty_of_cutoff_seq_summable_bad_sets
    (params : Phi4Params)
    [InteractionUVModel params]
    (hbad :
      ∀ Λ : Rectangle, ∃ B : ℝ, ∃ bad : ℕ → Set FieldConfig2D,
        (∑' n : ℕ, (freeFieldMeasure params.mass params.mass_pos) (bad n)) ≠ ∞ ∧
        (∀ n : ℕ, ∀ ω : FieldConfig2D, ω ∉ bad n →
          -B ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω)) :
    Nonempty (InteractionWeightModel params) := by
  refine interactionWeightModel_nonempty_of_data params ?_
  intro Λ p _hp
  rcases hbad Λ with ⟨B, bad, hsum, hgood⟩
  exact exp_interaction_Lp_of_cutoff_seq_bad_set_summable
    (params := params) (Λ := Λ) (B := B) (bad := bad) hsum hgood

/-- Construct `InteractionWeightModel` from per-volume shifted-index summable
    bad sets with good-set cutoff lower bounds. -/
theorem interactionWeightModel_nonempty_of_cutoff_seq_shifted_summable_bad_sets
    (params : Phi4Params)
    [InteractionUVModel params]
    (hbad :
      ∀ Λ : Rectangle, ∃ B : ℝ, ∃ bad : ℕ → Set FieldConfig2D,
        (∑' n : ℕ, (freeFieldMeasure params.mass params.mass_pos) (bad n)) ≠ ∞ ∧
        (∀ n : ℕ, ∀ ω : FieldConfig2D, ω ∉ bad n →
          -B ≤ interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)) :
    Nonempty (InteractionWeightModel params) := by
  refine interactionWeightModel_nonempty_of_data params ?_
  intro Λ p _hp
  rcases hbad Λ with ⟨B, bad, hsum, hgood⟩
  exact exp_interaction_Lp_of_cutoff_seq_shifted_bad_set_summable
    (params := params) (Λ := Λ) (B := B) (bad := bad) hsum hgood

/-- Construct `InteractionWeightModel` from Wick-level shifted-index summable
    bad sets: if outside `bad n` one has a uniform pointwise lower bound for
    `wickPower 4` at cutoff `κ_{n+1}`, then the induced cutoff-interaction lower
    bound feeds the shifted summable-bad-set `exp_interaction_Lp` pipeline. -/
theorem interactionWeightModel_nonempty_of_uv_cutoff_seq_shifted_summable_wick_bad_sets
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
    Nonempty (InteractionWeightModel params) := by
  refine interactionWeightModel_nonempty_of_cutoff_seq_shifted_summable_bad_sets
    (params := params) ?_
  intro Λ
  rcases hwick_bad Λ with
    ⟨B, bad, hsum, hΛ_meas, hΛ_finite, hwick_int, hgood⟩
  rcases interactionCutoff_pointwise_lower_bounds_of_standardSeq_succ_wick_bad_sets
      (params := params) (Λ := Λ) (B := B) (bad := bad)
      hΛ_meas hΛ_finite hwick_int hgood with ⟨Bcut, hcut⟩
  refine ⟨Bcut, bad, hsum, ?_⟩
  intro n ω hω
  exact hcut n ω hω

/-- Construct `InteractionWeightModel` from Wick-level shifted-index geometric
    bad-set tails together with good-set lower bounds on `wickPower 4`.
    This packages the common case `μ(bad n) ≤ C * r^n` (`r < 1`) into the
    summable-bad-set Wick bridge. -/
theorem interactionWeightModel_nonempty_of_uv_cutoff_seq_shifted_geometric_wick_bad_sets
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
    Nonempty (InteractionWeightModel params) := by
  refine interactionWeightModel_nonempty_of_uv_cutoff_seq_shifted_summable_wick_bad_sets
    (params := params) ?_
  intro Λ
  rcases hwick_bad Λ with
    ⟨B, bad, C, r, hC, hr, hbad_le, hΛ_meas, hΛ_finite, hwick_int, hgood⟩
  have hgeom_lt : (∑' n : ℕ, r ^ n) < ∞ :=
    (tsum_geometric_lt_top).2 hr
  have hsum_lt : (∑' n : ℕ, C * r ^ n) < ∞ := by
    have hC_lt : C < ∞ := by exact lt_of_le_of_ne le_top hC
    rw [ENNReal.tsum_mul_left]
    exact ENNReal.mul_lt_top hC_lt hgeom_lt
  have hsum :
      (∑' n : ℕ, (freeFieldMeasure params.mass params.mass_pos) (bad n)) ≠ ∞ :=
    ne_top_of_le_ne_top (ne_of_lt hsum_lt) (ENNReal.tsum_le_tsum hbad_le)
  exact ⟨B, bad, hsum, hΛ_meas, hΛ_finite, hwick_int, hgood⟩

/-- Construct `InteractionWeightModel` from Wick-level shifted-index
    exponential bad-set tails and good-set lower bounds on `wickPower 4`.
    This packages `μ(bad n) ≤ C * exp(-α n)` (`α > 0`) into the geometric
    Wick bad-set bridge. -/
theorem interactionWeightModel_nonempty_of_uv_cutoff_seq_shifted_exponential_wick_bad_sets
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
    Nonempty (InteractionWeightModel params) := by
  refine interactionWeightModel_nonempty_of_uv_cutoff_seq_shifted_geometric_wick_bad_sets
    (params := params) ?_
  intro Λ
  rcases hwick_bad Λ with
    ⟨B, bad, C, α, hC, hα, hbad_le, hΛ_meas, hΛ_finite, hwick_int, hgood⟩
  have hr : ENNReal.ofReal (Real.exp (-α)) < 1 := by
    refine (ENNReal.ofReal_lt_one).2 ?_
    have hneg : -α < 0 := by linarith
    exact Real.exp_lt_one_iff.mpr hneg
  refine ⟨B, bad, C, ENNReal.ofReal (Real.exp (-α)), hC, hr, hbad_le,
    hΛ_meas, hΛ_finite, hwick_int, hgood⟩

/-- Construct `InteractionWeightModel` from shifted-index summable tails of
    natural Wick sublevel bad events
    `{ω | ∃ x ∈ Λ, wickPower(κ_{n+1}) ω x < -B}`. -/
theorem interactionWeightModel_nonempty_of_uv_cutoff_seq_shifted_summable_wick_sublevel_bad_sets
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
    Nonempty (InteractionWeightModel params) := by
  refine interactionWeightModel_nonempty_of_data params ?_
  intro Λ p _hp
  rcases hwick_bad Λ with ⟨B, hbad_sum, hΛ_meas, hΛ_finite, hwick_int⟩
  exact exp_interaction_Lp_of_cutoff_seq_shifted_summable_wick_sublevel_bad_sets
    (params := params) (Λ := Λ) (B := B)
    hbad_sum hΛ_meas hΛ_finite hwick_int

/-- Construct `InteractionWeightModel` from shifted-index geometric tails of
    natural Wick sublevel bad events
    `{ω | ∃ x ∈ Λ, wickPower(κ_{n+1}) ω x < -B}`. -/
theorem interactionWeightModel_nonempty_of_uv_cutoff_seq_shifted_geometric_wick_sublevel_bad_sets
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
    Nonempty (InteractionWeightModel params) := by
  refine interactionWeightModel_nonempty_of_data params ?_
  intro Λ p _hp
  rcases hwick_bad Λ with ⟨B, C, r, hC, hr, hbad_le, hΛ_meas, hΛ_finite, hwick_int⟩
  exact exp_interaction_Lp_of_cutoff_seq_shifted_geometric_wick_sublevel_bad_sets
    (params := params) (Λ := Λ) (B := B) (C := C) (r := r)
    hC hr hbad_le hΛ_meas hΛ_finite hwick_int

/-- Construct `InteractionWeightModel` from shifted-index exponential tails of
    natural Wick sublevel bad events
    `{ω | ∃ x ∈ Λ, wickPower(κ_{n+1}) ω x < -B}`, given explicit measurability
    of `interaction` and explicit canonical-sequence a.e. convergence data. -/
theorem
    interactionWeightModel_nonempty_of_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets_of_aestronglyMeasurable_and_standardSeq_tendsto_ae
    (params : Phi4Params)
    (hinteraction_meas :
      ∀ Λ : Rectangle,
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_tendsto_ae :
      ∀ Λ : Rectangle,
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun n : ℕ => interactionCutoff params Λ (standardUVCutoffSeq n) ω)
            Filter.atTop
            (nhds (interaction params Λ ω)))
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
    Nonempty (InteractionWeightModel params) := by
  refine interactionWeightModel_nonempty_of_data params ?_
  intro Λ p _hp
  rcases hwick_bad Λ with
    ⟨B, C, α, hC, hα, hbad_le, hΛ_meas, hΛ_finite, hwick_int⟩
  let bad : ℕ → Set FieldConfig2D := fun n =>
    {ω : FieldConfig2D |
      ∃ x ∈ Λ.toSet,
        wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x < -B}
  have hbad_le' :
      ∀ n : ℕ,
        (freeFieldMeasure params.mass params.mass_pos) (bad n) ≤
          C * (ENNReal.ofReal (Real.exp (-α))) ^ n := by
    intro n
    simpa [bad] using hbad_le n
  have hgood :
      ∀ n : ℕ, ∀ ω : FieldConfig2D, ω ∉ bad n →
        ∀ x ∈ Λ.toSet,
          -B ≤ wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x := by
    intro n ω hω x hx
    by_contra hlt
    have hlt' :
        wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x < -B :=
      lt_of_not_ge hlt
    exact hω ⟨x, hx, hlt'⟩
  rcases interactionCutoff_pointwise_lower_bounds_of_standardSeq_succ_wick_bad_sets
      (params := params) (Λ := Λ) (B := B) (bad := bad)
      hΛ_meas hΛ_finite hwick_int hgood with ⟨Bcut, hcut⟩
  have hr : ENNReal.ofReal (Real.exp (-α)) < 1 := by
    refine (ENNReal.ofReal_lt_one).2 ?_
    have hneg : -α < 0 := by linarith
    exact Real.exp_lt_one_iff.mpr hneg
  have hgeom_lt : (∑' n : ℕ, (ENNReal.ofReal (Real.exp (-α))) ^ n) < ∞ :=
    (tsum_geometric_lt_top).2 hr
  have hsum_lt : (∑' n : ℕ, C * (ENNReal.ofReal (Real.exp (-α))) ^ n) < ∞ := by
    have hC_lt : C < ∞ := by exact lt_of_le_of_ne le_top hC
    rw [ENNReal.tsum_mul_left]
    exact ENNReal.mul_lt_top hC_lt hgeom_lt
  have hbad_sum :
      (∑' n : ℕ, (freeFieldMeasure params.mass params.mass_pos) (bad n)) ≠ ∞ :=
    ne_top_of_le_ne_top (ne_of_lt hsum_lt) (ENNReal.tsum_le_tsum hbad_le')
  exact
    exp_interaction_Lp_of_cutoff_seq_shifted_bad_set_summable_of_aestronglyMeasurable_and_standardSeq_tendsto_ae
      (params := params) (Λ := Λ)
      (hinteraction_meas Λ) (hcutoff_tendsto_ae Λ)
      (B := Bcut) (bad := bad) hbad_sum hcut

/-- Construct `InteractionWeightModel` from shifted-index exponential tails of
    natural Wick sublevel bad events
    `{ω | ∃ x ∈ Λ, wickPower(κ_{n+1}) ω x < -B}`. -/
theorem interactionWeightModel_nonempty_of_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets
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
    Nonempty (InteractionWeightModel params) := by
  exact
    interactionWeightModel_nonempty_of_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets_of_aestronglyMeasurable_and_standardSeq_tendsto_ae
      (params := params)
      (hinteraction_meas := fun Λ => (interaction_in_L2 params Λ).aestronglyMeasurable)
      (hcutoff_tendsto_ae := fun Λ => interactionCutoff_standardSeq_tendsto_ae params Λ)
      hwick_bad

/-- Construct `InteractionWeightModel` from:
    1) square-integrability/measurability UV data (used to instantiate
       `InteractionUVModel`), and
    2) shifted-index exponential tails of natural Wick sublevel bad events
       `{ω | ∃ x ∈ Λ, wickPower(κ_{n+1}) ω x < -B}`. -/
theorem
    interactionWeightModel_nonempty_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets
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
    Nonempty (InteractionWeightModel params) := by
  rcases interactionUVModel_nonempty_of_sq_integrable_data
      (params := params)
      hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
      hinteraction_meas hinteraction_sq with ⟨huv⟩
  letI : InteractionUVModel params := huv
  exact interactionWeightModel_nonempty_of_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets
    (params := params) hwick_bad

/-- Construct `InteractionWeightModel` from per-volume eventually-in-`n`
    cutoff-sequence almost-everywhere lower bounds, using explicit
    measurability of `interaction` and explicit a.e. convergence of the
    canonical cutoff sequence. -/
theorem
    interactionWeightModel_nonempty_of_cutoff_seq_eventually_lower_bounds_of_aestronglyMeasurable_and_standardSeq_tendsto_ae
    (params : Phi4Params)
    (hinteraction_meas :
      ∀ Λ : Rectangle,
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_tendsto_ae :
      ∀ Λ : Rectangle,
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun n : ℕ => interactionCutoff params Λ (standardUVCutoffSeq n) ω)
            Filter.atTop
            (nhds (interaction params Λ ω)))
    (hcutoff_ae :
      ∀ Λ : Rectangle, ∃ B : ℝ,
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          ∀ᶠ n in Filter.atTop,
            -B ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω) :
    Nonempty (InteractionWeightModel params) := by
  refine interactionWeightModel_nonempty_of_data params ?_
  intro Λ p _hp
  rcases hcutoff_ae Λ with ⟨B, hB⟩
  exact
    exp_interaction_Lp_of_cutoff_seq_eventually_lower_bound_of_aestronglyMeasurable_and_standardSeq_tendsto_ae
      (params := params) (Λ := Λ)
      (hinteraction_meas Λ) (hcutoff_tendsto_ae Λ) (B := B) hB

/-- Construct `InteractionWeightModel` from per-volume eventually-in-`n`
    cutoff-sequence almost-everywhere lower bounds. -/
theorem interactionWeightModel_nonempty_of_cutoff_seq_eventually_lower_bounds
    (params : Phi4Params)
    [InteractionUVModel params]
    (hcutoff_ae :
      ∀ Λ : Rectangle, ∃ B : ℝ,
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          ∀ᶠ n in Filter.atTop,
            -B ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω) :
    Nonempty (InteractionWeightModel params) := by
  refine
    interactionWeightModel_nonempty_of_cutoff_seq_eventually_lower_bounds_of_aestronglyMeasurable_and_standardSeq_tendsto_ae
      (params := params)
      (hinteraction_meas := fun Λ => (interaction_in_L2 params Λ).aestronglyMeasurable)
      (hcutoff_tendsto_ae := fun Λ => interactionCutoff_standardSeq_tendsto_ae params Λ)
      hcutoff_ae

/-- Construct `InteractionWeightModel` from per-volume variable cutoff constants
    `Bₙ`, assuming eventual uniform control `Bₙ ≤ B`. -/
theorem interactionWeightModel_nonempty_of_cutoff_seq_variable_lower_bounds
    (params : Phi4Params)
    [InteractionUVModel params]
    (hcutoff_ae :
      ∀ Λ : Rectangle, ∃ Bseq : ℕ → ℝ, ∃ B : ℝ,
        (∀ n : ℕ,
          ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
            -Bseq n ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω) ∧
        (∀ᶠ n in Filter.atTop, Bseq n ≤ B)) :
    Nonempty (InteractionWeightModel params) := by
  refine interactionWeightModel_nonempty_of_data params ?_
  intro Λ p _hp
  rcases hcutoff_ae Λ with ⟨Bseq, B, hseq, hB⟩
  exact exp_interaction_Lp_of_cutoff_seq_variable_lower_bounds
    (params := params) (Λ := Λ) (Bseq := Bseq) (B := B) hseq hB

/-- Construct `InteractionWeightModel` from per-volume summable bad-event tails
    for cutoff lower bounds. -/
theorem interactionWeightModel_nonempty_of_cutoff_seq_summable_bad_event_measure
    (params : Phi4Params)
    [InteractionUVModel params]
    (hbad :
      ∀ Λ : Rectangle, ∃ B : ℝ,
        (∑' n : ℕ,
          (freeFieldMeasure params.mass params.mass_pos)
            {ω : FieldConfig2D |
              interactionCutoff params Λ (standardUVCutoffSeq n) ω < -B}) ≠ ∞) :
    Nonempty (InteractionWeightModel params) := by
  refine interactionWeightModel_nonempty_of_data params ?_
  intro Λ p _hp
  rcases hbad Λ with ⟨B, hB⟩
  exact exp_interaction_Lp_of_cutoff_seq_summable_bad_event_measure
    (params := params) (Λ := Λ) (B := B) hB

/-- Construct `InteractionWeightModel` from per-volume shifted-index summable
    bad-event tails (`κ_{n+1}`). -/
theorem interactionWeightModel_nonempty_of_cutoff_seq_shifted_summable_bad_event_measure
    (params : Phi4Params)
    [InteractionUVModel params]
    (hbad :
      ∀ Λ : Rectangle, ∃ B : ℝ,
        (∑' n : ℕ,
          (freeFieldMeasure params.mass params.mass_pos)
            {ω : FieldConfig2D |
              interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω < -B}) ≠ ∞) :
    Nonempty (InteractionWeightModel params) := by
  refine interactionWeightModel_nonempty_of_data params ?_
  intro Λ p _hp
  rcases hbad Λ with ⟨B, hB⟩
  exact exp_interaction_Lp_of_cutoff_seq_shifted_summable_bad_event_measure
    (params := params) (Λ := Λ) (B := B) hB

/-- Construct `InteractionWeightModel` from per-volume summable majorants on
    cutoff bad-event probabilities. -/
theorem interactionWeightModel_nonempty_of_cutoff_seq_summable_bad_event_bound
    (params : Phi4Params)
    [InteractionUVModel params]
    (hbad :
      ∀ Λ : Rectangle, ∃ B : ℝ, ∃ ε : ℕ → ℝ≥0∞,
        (∑' n : ℕ, ε n) ≠ ∞ ∧
        (∀ n : ℕ,
          (freeFieldMeasure params.mass params.mass_pos)
            {ω : FieldConfig2D |
              interactionCutoff params Λ (standardUVCutoffSeq n) ω < -B} ≤ ε n)) :
    Nonempty (InteractionWeightModel params) := by
  refine interactionWeightModel_nonempty_of_data params ?_
  intro Λ p _hp
  rcases hbad Λ with ⟨B, ε, hε, hB⟩
  exact exp_interaction_Lp_of_cutoff_seq_summable_bad_event_bound
    (params := params) (Λ := Λ) (B := B) (ε := ε) hε hB

/-- Construct `InteractionWeightModel` from per-volume shifted-index summable
    majorants on cutoff bad-event probabilities (`κ_{n+1}`). -/
theorem interactionWeightModel_nonempty_of_cutoff_seq_shifted_summable_bad_event_bound
    (params : Phi4Params)
    [InteractionUVModel params]
    (hbad :
      ∀ Λ : Rectangle, ∃ B : ℝ, ∃ ε : ℕ → ℝ≥0∞,
        (∑' n : ℕ, ε n) ≠ ∞ ∧
        (∀ n : ℕ,
          (freeFieldMeasure params.mass params.mass_pos)
            {ω : FieldConfig2D |
              interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω < -B} ≤ ε n)) :
    Nonempty (InteractionWeightModel params) := by
  refine interactionWeightModel_nonempty_of_data params ?_
  intro Λ p _hp
  rcases hbad Λ with ⟨B, ε, hε, hB⟩
  exact exp_interaction_Lp_of_cutoff_seq_shifted_summable_bad_event_bound
    (params := params) (Λ := Λ) (B := B) (ε := ε) hε hB

/-- Construct `InteractionWeightModel` from per-volume geometric bad-event tail
    bounds (`μ badₙ ≤ C * rⁿ`, `r < 1`). -/
theorem interactionWeightModel_nonempty_of_cutoff_seq_geometric_bad_event_bound
    (params : Phi4Params)
    [InteractionUVModel params]
    (hbad :
      ∀ Λ : Rectangle, ∃ B : ℝ, ∃ C r : ℝ≥0∞,
        C ≠ ⊤ ∧ r < 1 ∧
        (∀ n : ℕ,
          (freeFieldMeasure params.mass params.mass_pos)
            {ω : FieldConfig2D |
              interactionCutoff params Λ (standardUVCutoffSeq n) ω < -B} ≤ C * r ^ n)) :
    Nonempty (InteractionWeightModel params) := by
  refine interactionWeightModel_nonempty_of_data params ?_
  intro Λ p _hp
  rcases hbad Λ with ⟨B, C, r, hC, hr, hB⟩
  exact exp_interaction_Lp_of_cutoff_seq_geometric_bad_event_bound
    (params := params) (Λ := Λ) (B := B) (C := C) (r := r) hC hr hB

/-- Construct `InteractionWeightModel` from per-volume shifted-index geometric
    bad-event tail bounds (`κ_{n+1}`). -/
theorem interactionWeightModel_nonempty_of_cutoff_seq_shifted_geometric_bad_event_bound
    (params : Phi4Params)
    [InteractionUVModel params]
    (hbad :
      ∀ Λ : Rectangle, ∃ B : ℝ, ∃ C r : ℝ≥0∞,
        C ≠ ⊤ ∧ r < 1 ∧
        (∀ n : ℕ,
          (freeFieldMeasure params.mass params.mass_pos)
            {ω : FieldConfig2D |
              interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω < -B} ≤ C * r ^ n)) :
    Nonempty (InteractionWeightModel params) := by
  refine interactionWeightModel_nonempty_of_data params ?_
  intro Λ p _hp
  rcases hbad Λ with ⟨B, C, r, hC, hr, hB⟩
  exact exp_interaction_Lp_of_cutoff_seq_shifted_geometric_bad_event_bound
    (params := params) (Λ := Λ) (B := B) (C := C) (r := r) hC hr hB

/-- Construct `InteractionWeightModel` from per-volume exponential bad-event
    tail bounds (`μ badₙ ≤ C * exp(-α n)`, `α > 0`). -/
theorem interactionWeightModel_nonempty_of_cutoff_seq_exponential_bad_event_bound
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
    Nonempty (InteractionWeightModel params) := by
  refine interactionWeightModel_nonempty_of_data params ?_
  intro Λ p _hp
  rcases hbad Λ with ⟨B, C, α, hC, hα, hB⟩
  exact exp_interaction_Lp_of_cutoff_seq_exponential_bad_event_bound
    (params := params) (Λ := Λ) (B := B) (C := C) (α := α) hC hα hB

/-- Construct `InteractionWeightModel` from per-volume shifted-index
    exponential bad-event tail bounds (`κ_{n+1}`). -/
theorem interactionWeightModel_nonempty_of_cutoff_seq_shifted_exponential_bad_event_bound
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
    Nonempty (InteractionWeightModel params) := by
  refine interactionWeightModel_nonempty_of_data params ?_
  intro Λ p _hp
  rcases hbad Λ with ⟨B, C, α, hC, hα, hB⟩
  exact exp_interaction_Lp_of_cutoff_seq_shifted_exponential_bad_event_bound
    (params := params) (Λ := Λ) (B := B) (C := C) (α := α) hC hα hB

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

/-- Almost-everywhere nonnegativity of the limiting interaction from geometric
    decay of shifted-index exponential moments of cutoff interactions. -/
theorem interaction_ae_nonneg_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
    (params : Phi4Params) (Λ : Rectangle)
    [InteractionUVModel params]
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
  exact
    interaction_ae_nonneg_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound_of_standardSeq_tendsto_ae
      (params := params) (Λ := Λ)
      (interactionCutoff_standardSeq_tendsto_ae params Λ) hmom

/-- Globalized nonnegativity transfer: shifted-index exponential-moment
    geometric decay implies almost-everywhere nonnegativity of the limiting
    interaction on every volume cutoff `Λ`, given explicit canonical-sequence
    a.e. convergence data. -/
theorem
    interaction_ae_nonneg_all_rectangles_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound_of_standardSeq_tendsto_ae
    (params : Phi4Params)
    (hcutoff_tendsto_ae :
      ∀ Λ : Rectangle,
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun n : ℕ => interactionCutoff params Λ (standardUVCutoffSeq n) ω)
            Filter.atTop
            (nhds (interaction params Λ ω)))
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
    ∀ Λ : Rectangle,
      ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
        0 ≤ interaction params Λ ω := by
  intro Λ
  exact
    interaction_ae_nonneg_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound_of_standardSeq_tendsto_ae
      (params := params) (Λ := Λ) (hcutoff_tendsto_ae Λ) (hmom Λ)

/-- Globalized nonnegativity transfer: shifted-index exponential-moment
    geometric decay implies almost-everywhere nonnegativity of the limiting
    interaction on every volume cutoff `Λ`. -/
theorem interaction_ae_nonneg_all_rectangles_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
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
    ∀ Λ : Rectangle,
      ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
        0 ≤ interaction params Λ ω := by
  exact
    interaction_ae_nonneg_all_rectangles_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound_of_standardSeq_tendsto_ae
      (params := params)
      (hcutoff_tendsto_ae := fun Λ => interactionCutoff_standardSeq_tendsto_ae params Λ)
      hmom

/-- Square-data nonnegativity transfer on a fixed volume cutoff:
    shifted-index geometric exponential-moment decay implies almost-everywhere
    nonnegativity of the limiting interaction, with `InteractionUVModel`
    instantiated constructively from square-integrability/measurability data. -/
theorem interaction_ae_nonneg_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
    (params : Phi4Params) (Λ : Rectangle)
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
  rcases interactionUVModel_nonempty_of_sq_integrable_data
      (params := params)
      hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
      hinteraction_meas hinteraction_sq with ⟨huv⟩
  letI : InteractionUVModel params := huv
  exact interaction_ae_nonneg_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
    (params := params) (Λ := Λ) hmom

/-- Convert shifted-index geometric bounds on absolute exponential moments
    `E[exp(θ |interactionCutoff(κ_{n+1})|)]` into shifted-index geometric
    bounds on signed moments `E[exp(-θ interactionCutoff(κ_{n+1}))]`. -/
theorem shifted_exponential_moment_geometric_bound_of_abs
    (params : Phi4Params) (Λ : Rectangle)
    [InteractionUVModel params]
    (hmomAbs :
      ∃ θ D r : ℝ,
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
          ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D * r ^ n) := by
  rcases hmomAbs with ⟨θ, D, r, hθ, hD, hr0, hr1, hIntAbs, hMAbs⟩
  have hIntNeg :
      ∀ n : ℕ,
        Integrable
          (fun ω : FieldConfig2D =>
            Real.exp ((-θ) * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
          (freeFieldMeasure params.mass params.mass_pos) := by
    intro n
    let μ : Measure FieldConfig2D := freeFieldMeasure params.mass params.mass_pos
    let X : FieldConfig2D → ℝ :=
      fun ω => interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω
    have hXae : AEStronglyMeasurable X μ := by
      simpa [X, μ] using
        (interactionCutoff_in_L2 params Λ (standardUVCutoffSeq (n + 1))).aestronglyMeasurable
    have hAeExpNeg : AEStronglyMeasurable (fun ω => Real.exp ((-θ) * X ω)) μ := by
      exact Real.continuous_exp.comp_aestronglyMeasurable (hXae.const_mul (-θ))
    refine Integrable.mono' (hIntAbs n) hAeExpNeg ?_
    filter_upwards with ω
    have hArg : (-θ) * X ω ≤ θ * |X ω| := by
      have hmul : θ * (-X ω) ≤ θ * |X ω| :=
        mul_le_mul_of_nonneg_left (neg_le_abs (X ω)) (le_of_lt hθ)
      nlinarith
    have hExp : Real.exp ((-θ) * X ω) ≤ Real.exp (θ * |X ω|) :=
      (Real.exp_le_exp).2 hArg
    simpa [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)] using hExp
  refine ⟨θ, D, r, hθ, hD, hr0, hr1, hIntNeg, ?_⟩
  intro n
  let μ : Measure FieldConfig2D := freeFieldMeasure params.mass params.mass_pos
  let X : FieldConfig2D → ℝ :=
    fun ω => interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω
  have hle_ae :
      (fun ω => Real.exp ((-θ) * X ω)) ≤ᵐ[μ] (fun ω => Real.exp (θ * |X ω|)) := by
    filter_upwards with ω
    exact (Real.exp_le_exp).2 (by
      have hmul : θ * (-X ω) ≤ θ * |X ω| :=
        mul_le_mul_of_nonneg_left (neg_le_abs (X ω)) (le_of_lt hθ)
      nlinarith)
  have hIntBound :
      ∫ ω : FieldConfig2D, Real.exp ((-θ) * X ω) ∂μ ≤
        ∫ ω : FieldConfig2D, Real.exp (θ * |X ω|) ∂μ :=
    integral_mono_ae (hIntNeg n) (hIntAbs n) hle_ae
  exact hIntBound.trans (by simpa [X, μ] using hMAbs n)

/-- `Lᵖ` integrability from geometric decay of shifted-index exponential moments
    of the cutoff interaction, given explicit measurability of `interaction`
    and explicit a.e. convergence of the canonical cutoff sequence. -/
theorem
    exp_interaction_Lp_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound_of_aestronglyMeasurable_and_standardSeq_tendsto_ae
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
            ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D * r ^ n))
    {p : ℝ≥0∞} :
    MemLp (fun ω => Real.exp (-(interaction params Λ ω)))
      p (freeFieldMeasure params.mass params.mass_pos) := by
  have hbound :
      ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
        -0 ≤ interaction params Λ ω := by
    simpa using
      (interaction_ae_nonneg_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound_of_standardSeq_tendsto_ae
        (params := params) (Λ := Λ) hcutoff_tendsto_ae hmom)
  exact exp_interaction_Lp_of_ae_lower_bound_of_aestronglyMeasurable
    (params := params) (Λ := Λ)
    hinteraction_meas (B := 0) hbound

/-- `Lᵖ` integrability from geometric decay of shifted-index exponential moments
    of the cutoff interaction:
    `E[exp(-θ interactionCutoff(κ_{n+1}))] ≤ D * r^n` with `r < 1`. -/
theorem exp_interaction_Lp_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
    (params : Phi4Params) (Λ : Rectangle)
    [InteractionUVModel params]
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
            ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D * r ^ n))
    {p : ℝ≥0∞} :
    MemLp (fun ω => Real.exp (-(interaction params Λ ω)))
      p (freeFieldMeasure params.mass params.mass_pos) := by
  exact
    exp_interaction_Lp_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound_of_aestronglyMeasurable_and_standardSeq_tendsto_ae
      (params := params) (Λ := Λ)
      ((interaction_in_L2 params Λ).aestronglyMeasurable)
      (interactionCutoff_standardSeq_tendsto_ae params Λ)
      hmom

/-- `Lᵖ` integrability from geometric decay of shifted-index absolute
    exponential moments of cutoff interactions:
    `E[exp(θ |interactionCutoff(κ_{n+1})|)] ≤ D * r^n` with `r < 1`. -/
theorem exp_interaction_Lp_of_uv_cutoff_seq_shifted_exponential_moment_abs_geometric_bound
    (params : Phi4Params) (Λ : Rectangle)
    [InteractionUVModel params]
    (hmomAbs :
      ∃ θ D r : ℝ,
        0 < θ ∧ 0 ≤ D ∧ 0 ≤ r ∧ r < 1 ∧
        (∀ n : ℕ,
          Integrable
            (fun ω : FieldConfig2D =>
              Real.exp (θ * |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω|))
            (freeFieldMeasure params.mass params.mass_pos)) ∧
        (∀ n : ℕ,
          ∫ ω : FieldConfig2D,
            Real.exp (θ * |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω|)
            ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D * r ^ n))
    {p : ℝ≥0∞} :
    MemLp (fun ω => Real.exp (-(interaction params Λ ω)))
      p (freeFieldMeasure params.mass params.mass_pos) := by
  exact exp_interaction_Lp_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
    (params := params) (Λ := Λ)
    (hmom := shifted_exponential_moment_geometric_bound_of_abs
      (params := params) (Λ := Λ) hmomAbs)

/-- `Lᵖ` integrability endpoint from:
    1. square-integrability/measurability UV data, and
    2. geometric decay of shifted-index exponential moments of the cutoff
    interaction on the target volume `Λ`. -/
theorem exp_interaction_Lp_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
    (params : Phi4Params) (Λ : Rectangle)
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
            ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D * r ^ n))
    {p : ℝ≥0∞} :
    MemLp (fun ω => Real.exp (-(interaction params Λ ω)))
      p (freeFieldMeasure params.mass params.mass_pos) := by
  have hbound :
      ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
        -0 ≤ interaction params Λ ω := by
    simpa using
      (interaction_ae_nonneg_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
        (params := params) (Λ := Λ)
        hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
        hinteraction_meas hinteraction_sq hmom)
  exact exp_interaction_Lp_of_ae_lower_bound_of_aestronglyMeasurable
    (params := params) (Λ := Λ)
    (hinteraction_meas Λ) (B := 0) hbound

/-- `Lᵖ` integrability endpoint from:
    1. square-integrability/measurability UV data, and
    2. geometric decay of shifted-index absolute exponential moments of cutoff
       interactions on the target volume `Λ`. -/
theorem
    exp_interaction_Lp_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_moment_abs_geometric_bound
    (params : Phi4Params) (Λ : Rectangle)
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
      ∃ θ D r : ℝ,
        0 < θ ∧ 0 ≤ D ∧ 0 ≤ r ∧ r < 1 ∧
        (∀ n : ℕ,
          Integrable
            (fun ω : FieldConfig2D =>
              Real.exp (θ * |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω|))
            (freeFieldMeasure params.mass params.mass_pos)) ∧
        (∀ n : ℕ,
          ∫ ω : FieldConfig2D,
            Real.exp (θ * |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω|)
            ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D * r ^ n))
    {p : ℝ≥0∞} :
    MemLp (fun ω => Real.exp (-(interaction params Λ ω)))
      p (freeFieldMeasure params.mass params.mass_pos) := by
  rcases interactionUVModel_nonempty_of_sq_integrable_data
      (params := params)
      hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
      hinteraction_meas hinteraction_sq with ⟨huv⟩
  letI : InteractionUVModel params := huv
  exact exp_interaction_Lp_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
    (params := params) (Λ := Λ)
    hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
    hinteraction_meas hinteraction_sq
    (shifted_exponential_moment_geometric_bound_of_abs
      (params := params) (Λ := Λ) hmomAbs)

/-- Construct `InteractionWeightModel` from geometric decay of shifted-index
    exponential moments of the cutoff interaction:
    `E[exp(-θ interactionCutoff(κ_{n+1}))] ≤ D * r^n` with `r < 1`,
    given explicit measurability of `interaction` and explicit a.e.
    convergence of the canonical cutoff sequence. -/
theorem
    interactionWeightModel_nonempty_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound_of_aestronglyMeasurable_and_standardSeq_tendsto_ae
    (params : Phi4Params)
    (hinteraction_meas :
      ∀ Λ : Rectangle,
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_tendsto_ae :
      ∀ Λ : Rectangle,
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun n : ℕ => interactionCutoff params Λ (standardUVCutoffSeq n) ω)
            Filter.atTop
            (nhds (interaction params Λ ω)))
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
  exact
    exp_interaction_Lp_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound_of_aestronglyMeasurable_and_standardSeq_tendsto_ae
      (params := params) (Λ := Λ)
      (hinteraction_meas Λ) (hcutoff_tendsto_ae Λ) (hmom Λ)

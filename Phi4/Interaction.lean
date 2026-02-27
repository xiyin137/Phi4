/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Order.Filter.AtTopBot.Basic
import Phi4.WickProduct

/-!
# The φ⁴ Interaction Term

The quartic interaction is
  V_Λ = λ ∫_Λ :φ(x)⁴:_C dx
where Λ is a bounded volume cutoff region. The central result of this file is that
e^{-V_Λ} ∈ Lᵖ(dφ_C) for all p < ∞ in d=2 (Theorem 8.6.2 of Glimm-Jaffe).

This is the key estimate that makes the d=2 theory work: the logarithmic divergence
of c_κ(x) ~ (2π)⁻¹ ln κ in d=2 is "just barely" controlled by the quartic Wick ordering.
(In d=3, the divergence is worse and additional renormalization is needed.)

## Main definitions

* `interactionCutoff` — V_{Λ,κ} = λ ∫_Λ :φ_κ(x)⁴: dx (both UV and volume cutoff)
* `interaction` — V_Λ = lim_{κ→∞} V_{Λ,κ} (UV limit, volume cutoff remains)

## Main results

* `interaction_in_L2` — V_Λ ∈ L²(dφ_C)
* `exp_interaction_Lp` — e^{-V_Λ} ∈ Lᵖ(dφ_C) for all p < ∞
* `wick_fourth_semibounded` — Lower bound on :φ_κ⁴: in terms of (ln κ)²

## References

* [Glimm-Jaffe] Sections 8.5-8.6, Theorem 8.6.2
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

/-! ## UV-regularized interaction -/

/-- The UV-regularized interaction with volume cutoff:
    V_{Λ,κ} = λ ∫_Λ :φ_κ(x)⁴:_C dx.
    Here φ_κ = δ_κ * φ is the UV-smoothed field and :·⁴: is Wick-ordered.
    The integral is over the rectangle Λ with respect to Lebesgue measure on ℝ². -/
def interactionCutoff (params : Phi4Params) (Λ : Rectangle) (κ : UVCutoff)
    (ω : FieldConfig2D) : ℝ :=
  params.coupling * ∫ x in Λ.toSet, wickPower 4 params.mass κ ω x

/-- Canonical sequence of UV cutoffs `κ_n = n+1`. -/
def standardUVCutoffSeq (n : ℕ) : UVCutoff :=
  ⟨n + 1, by exact_mod_cast Nat.succ_pos n⟩

/-- The interaction V_Λ = lim_{κ→∞} V_{Λ,κ} (UV limit with fixed volume cutoff).
    The limit exists in L² by Theorem 8.5.3. -/
def interaction (params : Phi4Params) (Λ : Rectangle) (ω : FieldConfig2D) : ℝ :=
  Filter.limsup (fun n : ℕ => interactionCutoff params Λ (standardUVCutoffSeq n) ω) Filter.atTop

/-! ## Semiboundedness of the Wick-ordered quartic

Although :φ⁴: = φ⁴ - 6cφ² + 3c² is not pointwise bounded below (the Wick subtractions
destroy the positivity of φ⁴), it is "almost" bounded below: the set where it is very
negative has exponentially small Gaussian measure. -/

/-- Semiboundedness of the UV-regularized quartic Wick product.
    :φ_κ(x)⁴:_C ≥ -6c_κ(x)² ≥ -const × (ln κ)² for d=2.
    (Proposition 8.6.3 of Glimm-Jaffe)

    For fixed `κ`, the witness constant is uniform in the field configuration and point. -/
theorem wick_fourth_semibounded (mass : ℝ) (_hmass : 0 < mass) (κ : UVCutoff)
    (hκ : 1 < κ.κ) :
    ∃ C : ℝ, ∀ (ω : FieldConfig2D) (x : Spacetime2D),
      -C * (Real.log κ.κ) ^ 2 ≤ wickPower 4 mass κ ω x := by
  let c : ℝ := regularizedPointCovariance mass κ
  have hlog_ne : Real.log κ.κ ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one κ.hκ
    exact ne_of_gt hκ
  have hlog_sq_ne : (Real.log κ.κ) ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 hlog_ne
  let C : ℝ := 6 * c ^ 2 / (Real.log κ.κ) ^ 2
  refine ⟨C, ?_⟩
  intro ω x
  have hbase : -6 * c ^ 2 ≤ wickPower 4 mass κ ω x := by
    simp only [wickPower, wickMonomial_four, c]
    nlinarith [sq_nonneg (rawFieldEval mass κ ω x ^ 2 - 3 * regularizedPointCovariance mass κ)]
  have hleft : -C * (Real.log κ.κ) ^ 2 = -6 * c ^ 2 := by
    have h1 : C * (Real.log κ.κ) ^ 2 = 6 * c ^ 2 := by
      unfold C
      field_simp [hlog_sq_ne]
    linarith
  calc
    -C * (Real.log κ.κ) ^ 2 = -6 * c ^ 2 := hleft
    _ ≤ wickPower 4 mass κ ω x := hbase

/-- More precisely: :φ_κ(x)⁴: = (φ_κ² - 3c_κ)² - 6c_κ² ≥ -6c_κ².
    Proof: completing the square, φ⁴ - 6cφ² + 3c² = (φ² - 3c)² - 6c² ≥ -6c². -/
theorem wick_fourth_lower_bound_explicit (mass : ℝ) (_hmass : 0 < mass) (κ : UVCutoff)
    (ω : FieldConfig2D) (x : Spacetime2D) :
    -6 * (regularizedPointCovariance mass κ) ^ 2 ≤ wickPower 4 mass κ ω x := by
  simp only [wickPower, wickMonomial_four]
  nlinarith [sq_nonneg (rawFieldEval mass κ ω x ^ 2 - 3 * regularizedPointCovariance mass κ)]

/-! ## Abstract interaction-integrability interface -/

/-- Analytic interaction estimates used by finite-volume construction. This
    packages the substantial Chapter 8 bounds as explicit assumptions. -/
class InteractionIntegrabilityModel (params : Phi4Params) where
  interactionCutoff_in_L2 :
    ∀ (Λ : Rectangle) (κ : UVCutoff),
      MemLp (interactionCutoff params Λ κ) 2
        (freeFieldMeasure params.mass params.mass_pos)
  interactionCutoff_converges_L2 :
    ∀ (Λ : Rectangle),
      Filter.Tendsto
        (fun (κ : ℝ) => if h : 0 < κ then
          ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
            ∂(freeFieldMeasure params.mass params.mass_pos)
          else 0)
        Filter.atTop
        (nhds 0)
  /-- Almost-everywhere pointwise UV convergence toward `interaction`. -/
  interactionCutoff_tendsto_ae :
    ∀ (Λ : Rectangle),
      ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
          Filter.atTop
          (nhds (interaction params Λ ω))
  interaction_in_L2 :
    ∀ (Λ : Rectangle),
      MemLp (interaction params Λ) 2
        (freeFieldMeasure params.mass params.mass_pos)
  exp_interaction_Lp :
    ∀ (Λ : Rectangle) {p : ℝ≥0∞}, p ≠ ⊤ →
      MemLp (fun ω => Real.exp (-(interaction params Λ ω)))
        p (freeFieldMeasure params.mass params.mass_pos)

/-- UV/L² interaction input: cutoff moments, UV convergence, and L² control of
    the limiting interaction. -/
class InteractionUVModel (params : Phi4Params) where
  interactionCutoff_in_L2 :
    ∀ (Λ : Rectangle) (κ : UVCutoff),
      MemLp (interactionCutoff params Λ κ) 2
        (freeFieldMeasure params.mass params.mass_pos)
  interactionCutoff_converges_L2 :
    ∀ (Λ : Rectangle),
      Filter.Tendsto
        (fun (κ : ℝ) => if h : 0 < κ then
          ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
            ∂(freeFieldMeasure params.mass params.mass_pos)
          else 0)
        Filter.atTop
        (nhds 0)
  interactionCutoff_tendsto_ae :
    ∀ (Λ : Rectangle),
      ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
          Filter.atTop
          (nhds (interaction params Λ ω))
  interaction_in_L2 :
    ∀ (Λ : Rectangle),
      MemLp (interaction params Λ) 2
        (freeFieldMeasure params.mass params.mass_pos)

/-- Any full interaction-integrability model provides the UV/L² subinterface. -/
instance (priority := 100) interactionUVModel_of_integrability
    (params : Phi4Params)
    [InteractionIntegrabilityModel params] :
    InteractionUVModel params where
  interactionCutoff_in_L2 :=
    InteractionIntegrabilityModel.interactionCutoff_in_L2 (params := params)
  interactionCutoff_converges_L2 :=
    InteractionIntegrabilityModel.interactionCutoff_converges_L2 (params := params)
  interactionCutoff_tendsto_ae :=
    InteractionIntegrabilityModel.interactionCutoff_tendsto_ae (params := params)
  interaction_in_L2 :=
    InteractionIntegrabilityModel.interaction_in_L2 (params := params)

/-- Minimal interaction input used by finite-volume measure normalization and
    moment integrability: integrability of the Boltzmann weight `exp(-V_Λ)` in
    every finite `Lᵖ`. -/
class InteractionWeightModel (params : Phi4Params) where
  exp_interaction_Lp :
    ∀ (Λ : Rectangle) {p : ℝ≥0∞}, p ≠ ⊤ →
      MemLp (fun ω => Real.exp (-(interaction params Λ ω)))
        p (freeFieldMeasure params.mass params.mass_pos)

/-- Construct `InteractionUVModel` from explicit UV/L² interaction data. -/
theorem interactionUVModel_nonempty_of_data (params : Phi4Params)
    (hcutoff_in_L2 :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        MemLp (interactionCutoff params Λ κ) 2
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
    (hinteraction_L2 :
      ∀ (Λ : Rectangle),
        MemLp (interaction params Λ) 2
          (freeFieldMeasure params.mass params.mass_pos)) :
    Nonempty (InteractionUVModel params) := by
  exact ⟨{
    interactionCutoff_in_L2 := hcutoff_in_L2
    interactionCutoff_converges_L2 := hcutoff_conv
    interactionCutoff_tendsto_ae := hcutoff_ae
    interaction_in_L2 := hinteraction_L2
  }⟩

/-- Construct `InteractionWeightModel` from explicit Boltzmann-weight
    `Lᵖ` integrability data. -/
theorem interactionWeightModel_nonempty_of_data (params : Phi4Params)
    (hexp :
      ∀ (Λ : Rectangle) {p : ℝ≥0∞}, p ≠ ⊤ →
        MemLp (fun ω => Real.exp (-(interaction params Λ ω)))
          p (freeFieldMeasure params.mass params.mass_pos)) :
    Nonempty (InteractionWeightModel params) := by
  exact ⟨{ exp_interaction_Lp := hexp }⟩

/-- Construct `InteractionIntegrabilityModel` from explicit UV/L² and
    Boltzmann-weight `Lᵖ` data. -/
theorem interactionIntegrabilityModel_nonempty_of_data (params : Phi4Params)
    (hcutoff_in_L2 :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        MemLp (interactionCutoff params Λ κ) 2
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
    (hinteraction_L2 :
      ∀ (Λ : Rectangle),
        MemLp (interaction params Λ) 2
          (freeFieldMeasure params.mass params.mass_pos))
    (hexp :
      ∀ (Λ : Rectangle) {p : ℝ≥0∞}, p ≠ ⊤ →
        MemLp (fun ω => Real.exp (-(interaction params Λ ω)))
          p (freeFieldMeasure params.mass params.mass_pos)) :
    Nonempty (InteractionIntegrabilityModel params) := by
  exact ⟨{
    interactionCutoff_in_L2 := hcutoff_in_L2
    interactionCutoff_converges_L2 := hcutoff_conv
    interactionCutoff_tendsto_ae := hcutoff_ae
    interaction_in_L2 := hinteraction_L2
    exp_interaction_Lp := hexp
  }⟩

/-- Any full interaction-integrability model provides the weight-integrability
    subinterface. -/
instance (priority := 100) interactionWeightModel_of_integrability
    (params : Phi4Params)
    [InteractionIntegrabilityModel params] :
    InteractionWeightModel params where
  exp_interaction_Lp := InteractionIntegrabilityModel.exp_interaction_Lp (params := params)

/-- The combined UV/L² and weight-integrability subinterfaces reconstruct the
    original interaction-integrability interface. -/
instance (priority := 100) interactionIntegrabilityModel_of_uv_weight
    (params : Phi4Params)
    [InteractionUVModel params]
    [InteractionWeightModel params] :
    InteractionIntegrabilityModel params where
  interactionCutoff_in_L2 := InteractionUVModel.interactionCutoff_in_L2 (params := params)
  interactionCutoff_converges_L2 :=
    InteractionUVModel.interactionCutoff_converges_L2 (params := params)
  interactionCutoff_tendsto_ae :=
    InteractionUVModel.interactionCutoff_tendsto_ae (params := params)
  interaction_in_L2 := InteractionUVModel.interaction_in_L2 (params := params)
  exp_interaction_Lp := InteractionWeightModel.exp_interaction_Lp (params := params)

/-! ## The interaction is in Lᵖ -/

/-- The UV-regularized interaction V_{Λ,κ} is in L²(dφ_C).
    This follows from the localized Feynman graph bounds (Theorem 8.5.3).
    The bound is uniform in κ. -/
theorem interactionCutoff_in_L2 (params : Phi4Params) (Λ : Rectangle)
    [InteractionUVModel params]
    (κ : UVCutoff) :
    MemLp (interactionCutoff params Λ κ) 2 (freeFieldMeasure params.mass params.mass_pos) := by
  exact InteractionUVModel.interactionCutoff_in_L2
    (params := params) Λ κ

/-- Convergence of V_{Λ,κ} → V_Λ in L² as κ → ∞.
    The limit is taken in the L²(dφ_C) norm:
      ‖V_{Λ,κ} - V_Λ‖_{L²(dφ_C)} → 0 as κ → ∞. -/
theorem interactionCutoff_converges_L2 (params : Phi4Params)
    [InteractionUVModel params]
    (Λ : Rectangle) :
    Filter.Tendsto
      (fun (κ : ℝ) => if h : 0 < κ then
        ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
          ∂(freeFieldMeasure params.mass params.mass_pos)
        else 0)
      Filter.atTop
      (nhds 0) := by
  exact InteractionUVModel.interactionCutoff_converges_L2
    (params := params) Λ

/-- Almost-everywhere pointwise UV convergence `V_{Λ,κ} → V_Λ`. -/
theorem interactionCutoff_tendsto_ae (params : Phi4Params)
    [InteractionUVModel params]
    (Λ : Rectangle) :
    ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
      Filter.Tendsto
        (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
        Filter.atTop
        (nhds (interaction params Λ ω)) := by
  exact InteractionUVModel.interactionCutoff_tendsto_ae
    (params := params) Λ

/-- The interaction V_Λ is in L²(dφ_C). -/
theorem interaction_in_L2 (params : Phi4Params)
    [InteractionUVModel params]
    (Λ : Rectangle) :
    MemLp (interaction params Λ) 2 (freeFieldMeasure params.mass params.mass_pos) := by
  exact InteractionUVModel.interaction_in_L2
    (params := params) Λ

/-- Pointwise lower bound transfer from all UV-cutoff interactions
    along the canonical sequence to the limiting interaction
    `interaction = limsup_n interactionCutoff κ_n`. -/
theorem interaction_lower_bound_of_cutoff_seq (params : Phi4Params) (Λ : Rectangle) (B : ℝ)
    (hcutoff :
      ∀ (n : ℕ) (ω : FieldConfig2D),
        -B ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω)
    (hbounded :
      ∀ ω : FieldConfig2D,
        Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
          (fun n : ℕ => interactionCutoff params Λ (standardUVCutoffSeq n) ω)) :
    ∀ ω : FieldConfig2D, -B ≤ interaction params Λ ω := by
  intro ω
  change -B ≤
    Filter.limsup
      (fun n : ℕ => interactionCutoff params Λ (standardUVCutoffSeq n) ω)
      Filter.atTop
  have hfreq :
      ∃ᶠ n in Filter.atTop,
        -B ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω :=
    Filter.Frequently.of_forall (fun n => hcutoff n ω)
  exact Filter.le_limsup_of_frequently_le hfreq (hbounded ω)

/-- Almost-everywhere lower bound transfer from countably many UV-cutoff
    lower bounds (uniform in cutoff index) to the limiting interaction. -/
theorem interaction_ae_lower_bound_of_cutoff_seq
    (params : Phi4Params) (Λ : Rectangle) (B : ℝ)
    [InteractionUVModel params]
    (hcutoff_ae :
      ∀ n : ℕ,
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          -B ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω) :
    ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
      -B ≤ interaction params Λ ω := by
  have hall :
      ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
        ∀ n : ℕ, -B ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω := by
    rw [eventually_countable_forall]
    intro n
    exact hcutoff_ae n
  have htend :
      ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
          Filter.atTop
          (nhds (interaction params Λ ω)) :=
    interactionCutoff_tendsto_ae params Λ
  filter_upwards [hall, htend] with ω hω hωt
  have hnat' : Filter.Tendsto ((Nat.cast : ℕ → ℝ) ∘ fun a : ℕ => a + 1) Filter.atTop Filter.atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp (Filter.tendsto_add_atTop_nat 1)
  have hseq_raw :
      Filter.Tendsto
        (fun n : ℕ =>
          if h : 0 < ((Nat.cast : ℕ → ℝ) ((fun a : ℕ => a + 1) n)) then
            interactionCutoff params Λ ⟨(Nat.cast : ℕ → ℝ) ((fun a : ℕ => a + 1) n), h⟩ ω
          else 0)
        Filter.atTop
        (nhds (interaction params Λ ω)) :=
    hωt.comp hnat'
  have hseq_eq :
      (fun n : ℕ =>
        if h : 0 < ((Nat.cast : ℕ → ℝ) ((fun a : ℕ => a + 1) n)) then
          interactionCutoff params Λ ⟨(Nat.cast : ℕ → ℝ) ((fun a : ℕ => a + 1) n), h⟩ ω
        else 0) =ᶠ[Filter.atTop]
      (fun n : ℕ => interactionCutoff params Λ (standardUVCutoffSeq n) ω) := by
    exact Filter.Eventually.of_forall (fun n => by
      have hn : 0 < (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos n
      simp [standardUVCutoffSeq, hn])
  have hseq :
      Filter.Tendsto
        (fun n : ℕ => interactionCutoff params Λ (standardUVCutoffSeq n) ω)
        Filter.atTop
        (nhds (interaction params Λ ω)) :=
    hseq_raw.congr' hseq_eq
  have hcutoff_mem :
      ∀ᶠ n in Filter.atTop,
        interactionCutoff params Λ (standardUVCutoffSeq n) ω ∈ Set.Ici (-B) :=
    Filter.Eventually.of_forall (fun n => hω n)
  exact isClosed_Ici.mem_of_tendsto hseq hcutoff_mem

/-! ## The exponential of the interaction is in Lᵖ

This is the central estimate of the chapter (Theorem 8.6.2 of Glimm-Jaffe).
The proof has two main steps:
1. Semiboundedness: :P(φ_κ):_C ≥ -const × (ln κ)^{deg P/2}
2. Gaussian tail estimates: P(|:φ_κ: < threshold|) ≤ exp(-const × κ^δ)
-/

/-- On a finite measure space, an almost-everywhere lower bound on `V`
    implies `exp(-V) ∈ Lᵖ` for every exponent `p`.
    This is the measure-theoretic bridge used in the φ⁴ interaction-integrability
    chain once semiboundedness/tail estimates provide the lower bound. -/
theorem memLp_exp_neg_of_ae_lower_bound
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (V : α → ℝ) (hV_meas : AEStronglyMeasurable V μ)
    (B : ℝ) (hV_lower : ∀ᵐ x ∂μ, -B ≤ V x)
    {p : ℝ≥0∞} :
    MemLp (fun x => Real.exp (-(V x))) p μ := by
  have hExp_meas : AEStronglyMeasurable (fun x => Real.exp (-(V x))) μ := by
    exact ((hV_meas.aemeasurable.neg).exp).aestronglyMeasurable
  have hbound : ∀ᵐ x ∂μ, ‖Real.exp (-(V x))‖ ≤ Real.exp B := by
    filter_upwards [hV_lower] with x hx
    have hle : -(V x) ≤ B := by linarith
    have hexp_le : Real.exp (-(V x)) ≤ Real.exp B := Real.exp_le_exp.mpr hle
    have hnonneg : 0 ≤ Real.exp (-(V x)) := le_of_lt (Real.exp_pos _)
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hexp_le
  exact MemLp.of_bound hExp_meas (Real.exp B) hbound

/-- If the interaction has an almost-everywhere lower bound under the free field
    measure, then its Boltzmann weight is in every finite `Lᵖ`.
    This isolates the final measure-theoretic step from the hard Chapter 8
    semiboundedness/tail estimates that produce the lower bound. -/
theorem exp_interaction_Lp_of_ae_lower_bound (params : Phi4Params) (Λ : Rectangle)
    [InteractionUVModel params]
    (B : ℝ)
    (hbound : ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
      -B ≤ interaction params Λ ω)
    {p : ℝ≥0∞} :
    MemLp (fun ω => Real.exp (-(interaction params Λ ω)))
      p (freeFieldMeasure params.mass params.mass_pos) := by
  have hmeas :
      AEStronglyMeasurable (interaction params Λ)
        (freeFieldMeasure params.mass params.mass_pos) :=
    (interaction_in_L2 params Λ).aestronglyMeasurable
  exact memLp_exp_neg_of_ae_lower_bound
    (μ := freeFieldMeasure params.mass params.mass_pos)
    (V := interaction params Λ) hmeas B hbound

/-- `Lᵖ` integrability of the Boltzmann weight from countably many
    cutoff-level almost-everywhere lower bounds along the canonical UV sequence. -/
theorem exp_interaction_Lp_of_cutoff_seq_lower_bounds
    (params : Phi4Params) (Λ : Rectangle)
    [InteractionUVModel params]
    (B : ℝ)
    (hcutoff_ae :
      ∀ n : ℕ,
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          -B ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω)
    {p : ℝ≥0∞} :
    MemLp (fun ω => Real.exp (-(interaction params Λ ω)))
      p (freeFieldMeasure params.mass params.mass_pos) := by
  refine exp_interaction_Lp_of_ae_lower_bound (params := params) (Λ := Λ)
    (B := B) ?_
  exact interaction_ae_lower_bound_of_cutoff_seq params Λ B hcutoff_ae

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

end

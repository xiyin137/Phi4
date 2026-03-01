/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.PSeries
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

/-- Bridge from pointwise Wick lower bounds to a lower bound on the cutoff
    interaction integral over a fixed volume. -/
theorem interactionCutoff_lower_bound_of_wick_lower_bound
    (params : Phi4Params) (Λ : Rectangle) (κ : UVCutoff) (ω : FieldConfig2D)
    (B : ℝ)
    (hΛ_meas : MeasurableSet Λ.toSet)
    (hΛ_finite : volume Λ.toSet ≠ ∞)
    (hwick_int :
      IntegrableOn (fun x => wickPower 4 params.mass κ ω x) Λ.toSet volume)
    (hlower : ∀ x ∈ Λ.toSet, -B ≤ wickPower 4 params.mass κ ω x) :
    params.coupling * ∫ _ in Λ.toSet, (-B : ℝ) ≤
      interactionCutoff params Λ κ ω := by
  have hconst_int : IntegrableOn (fun _ : Spacetime2D => (-B : ℝ)) Λ.toSet volume :=
    integrableOn_const hΛ_finite
  have hint_le :
      ∫ x in Λ.toSet, (-B : ℝ) ∂volume ≤
        ∫ x in Λ.toSet, wickPower 4 params.mass κ ω x ∂volume := by
    exact setIntegral_mono_on hconst_int hwick_int hΛ_meas hlower
  have hmul :
      params.coupling * (∫ x in Λ.toSet, (-B : ℝ) ∂volume) ≤
        params.coupling * (∫ x in Λ.toSet, wickPower 4 params.mass κ ω x ∂volume) :=
    mul_le_mul_of_nonneg_left hint_le params.coupling_pos.le
  simpa [interactionCutoff] using hmul

/-- Semibounded Wick quartic implies a cutoff-interaction lower bound for each
    UV cutoff scale `κ > 1`, provided integrability on the finite volume. -/
theorem interactionCutoff_lower_bound_of_wick_semibounded
    (params : Phi4Params) (Λ : Rectangle) (κ : UVCutoff)
    (hκ : 1 < κ.κ)
    (hΛ_meas : MeasurableSet Λ.toSet)
    (hΛ_finite : volume Λ.toSet ≠ ∞)
    (hwick_int :
      ∀ ω : FieldConfig2D,
        IntegrableOn (fun x => wickPower 4 params.mass κ ω x) Λ.toSet volume) :
    ∃ C : ℝ, ∀ ω : FieldConfig2D,
      params.coupling *
          ∫ _ in Λ.toSet, (-(C * (Real.log κ.κ) ^ 2) : ℝ) ≤
        interactionCutoff params Λ κ ω := by
  rcases wick_fourth_semibounded params.mass params.mass_pos κ hκ with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro ω
  refine interactionCutoff_lower_bound_of_wick_lower_bound
    (params := params) (Λ := Λ) (κ := κ) (ω := ω)
    (B := C * (Real.log κ.κ) ^ 2)
    hΛ_meas hΛ_finite (hwick_int ω) ?_
  intro x hx
  simpa [neg_mul] using hC ω x

/-- Along the shifted canonical UV sequence `κ_{n+1} = n + 2`, semibounded Wick
    control yields pointwise lower bounds for `interactionCutoff`. -/
theorem interactionCutoff_pointwise_lower_bounds_of_standardSeq_succ_wick_semibounded
    (params : Phi4Params) (Λ : Rectangle)
    (hΛ_meas : MeasurableSet Λ.toSet)
    (hΛ_finite : volume Λ.toSet ≠ ∞)
    (hwick_int :
      ∀ n : ℕ, ∀ ω : FieldConfig2D,
        IntegrableOn
          (fun x => wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x)
          Λ.toSet volume) :
    ∀ n : ℕ, ∃ B : ℝ, ∀ ω : FieldConfig2D,
      -B ≤ interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω := by
  intro n
  have hκ : 1 < (standardUVCutoffSeq (n + 1)).κ := by
    simpa [standardUVCutoffSeq] using
      (show (0 : ℝ) < (n : ℝ) + 1 from by positivity)
  rcases interactionCutoff_lower_bound_of_wick_semibounded
      (params := params) (Λ := Λ) (κ := standardUVCutoffSeq (n + 1))
      hκ hΛ_meas hΛ_finite (hwick_int n) with ⟨C, hC⟩
  refine ⟨-(params.coupling *
      ∫ x in Λ.toSet, (-(C * (Real.log (standardUVCutoffSeq (n + 1)).κ) ^ 2) : ℝ)), ?_⟩
  intro ω
  simpa using hC ω

/-- Good-set variant of `interactionCutoff_lower_bound_of_wick_lower_bound`:
    if a pointwise Wick lower bound holds outside a bad set, then the induced
    cutoff-interaction lower bound also holds outside that bad set. -/
theorem interactionCutoff_lower_bound_of_wick_lower_bound_on_good_set
    (params : Phi4Params) (Λ : Rectangle) (κ : UVCutoff)
    (bad : Set FieldConfig2D) (B : ℝ)
    (hΛ_meas : MeasurableSet Λ.toSet)
    (hΛ_finite : volume Λ.toSet ≠ ∞)
    (hwick_int :
      ∀ ω : FieldConfig2D,
        IntegrableOn (fun x => wickPower 4 params.mass κ ω x) Λ.toSet volume)
    (hgood :
      ∀ ω : FieldConfig2D, ω ∉ bad →
        ∀ x ∈ Λ.toSet, -B ≤ wickPower 4 params.mass κ ω x) :
    ∀ ω : FieldConfig2D, ω ∉ bad →
      params.coupling * ∫ _ in Λ.toSet, (-(B : ℝ)) ≤
        interactionCutoff params Λ κ ω := by
  intro ω hω
  exact interactionCutoff_lower_bound_of_wick_lower_bound
    (params := params) (Λ := Λ) (κ := κ) (ω := ω) (B := B)
    hΛ_meas hΛ_finite (hwick_int ω) (hgood ω hω)

/-- Shifted canonical-sequence cutoff lower bounds from Wick lower bounds on
    good sets: outside each bad set `bad n`, one gets a uniform-in-`n` lower
    bound on `interactionCutoff` with explicit constant depending on `Λ` and `B`. -/
theorem interactionCutoff_pointwise_lower_bounds_of_standardSeq_succ_wick_bad_sets
    (params : Phi4Params) (Λ : Rectangle) (B : ℝ)
    (bad : ℕ → Set FieldConfig2D)
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
          -B ≤ wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x) :
    ∃ Bcut : ℝ, ∀ n : ℕ, ∀ ω : FieldConfig2D, ω ∉ bad n →
      -Bcut ≤ interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω := by
  refine ⟨-(params.coupling * ∫ x in Λ.toSet, (-(B : ℝ))), ?_⟩
  intro n ω hω
  have hcut :
      params.coupling * ∫ x in Λ.toSet, (-(B : ℝ)) ≤
        interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω := by
    exact interactionCutoff_lower_bound_of_wick_lower_bound_on_good_set
      (params := params) (Λ := Λ) (κ := standardUVCutoffSeq (n + 1))
      (bad := bad n) (B := B) hΛ_meas hΛ_finite (hwick_int n) (hgood n) ω hω
  simpa using hcut

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

/-- Build cutoff `L²` control from a square-integrability hypothesis. -/
theorem interactionCutoff_memLp_two_of_sq_integrable
    (params : Phi4Params) (Λ : Rectangle) (κ : UVCutoff)
    (hmeas :
      AEStronglyMeasurable (interactionCutoff params Λ κ)
        (freeFieldMeasure params.mass params.mass_pos))
    (hsq :
      Integrable (fun ω => (interactionCutoff params Λ κ ω) ^ 2)
        (freeFieldMeasure params.mass params.mass_pos)) :
    MemLp (interactionCutoff params Λ κ) 2
      (freeFieldMeasure params.mass params.mass_pos) := by
  exact (memLp_two_iff_integrable_sq hmeas).2 hsq

/-- Build limiting-interaction `L²` control from a square-integrability
    hypothesis. -/
theorem interaction_memLp_two_of_sq_integrable
    (params : Phi4Params) (Λ : Rectangle)
    (hmeas :
      AEStronglyMeasurable (interaction params Λ)
        (freeFieldMeasure params.mass params.mass_pos))
    (hsq :
      Integrable (fun ω => (interaction params Λ ω) ^ 2)
        (freeFieldMeasure params.mass params.mass_pos)) :
    MemLp (interaction params Λ) 2
      (freeFieldMeasure params.mass params.mass_pos) := by
  exact (memLp_two_iff_integrable_sq hmeas).2 hsq

/-- Construct `InteractionUVModel` from:
    1) cutoff-square integrability + measurability,
    2) UV `L²` convergence data,
    3) cutoff a.e. UV convergence,
    4) limiting-interaction square integrability + measurability. -/
theorem interactionUVModel_nonempty_of_sq_integrable_data
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
          (freeFieldMeasure params.mass params.mass_pos)) :
    Nonempty (InteractionUVModel params) := by
  refine interactionUVModel_nonempty_of_data params ?_ hcutoff_conv hcutoff_ae ?_
  · intro Λ κ
    exact interactionCutoff_memLp_two_of_sq_integrable
      (params := params) (Λ := Λ) (κ := κ)
      (hcutoff_meas Λ κ) (hcutoff_sq Λ κ)
  · intro Λ
    exact interaction_memLp_two_of_sq_integrable
      (params := params) (Λ := Λ)
      (hinteraction_meas Λ) (hinteraction_sq Λ)

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

/-- Any nonempty full interaction-integrability witness yields a nonempty
    UV/L² subinterface witness. -/
theorem interactionUVModel_nonempty_of_integrability_nonempty
    (params : Phi4Params)
    (hint : Nonempty (InteractionIntegrabilityModel params)) :
    Nonempty (InteractionUVModel params) := by
  rcases hint with ⟨hintInst⟩
  letI : InteractionIntegrabilityModel params := hintInst
  exact ⟨inferInstance⟩

/-- Any nonempty full interaction-integrability witness yields a nonempty
    weight-integrability subinterface witness. -/
theorem interactionWeightModel_nonempty_of_integrability_nonempty
    (params : Phi4Params)
    (hint : Nonempty (InteractionIntegrabilityModel params)) :
    Nonempty (InteractionWeightModel params) := by
  rcases hint with ⟨hintInst⟩
  letI : InteractionIntegrabilityModel params := hintInst
  exact ⟨inferInstance⟩

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

/-- Combine nonempty UV/L² and weight-integrability witnesses into a nonempty
    full interaction-integrability witness. -/
theorem interactionIntegrabilityModel_nonempty_of_uv_weight_nonempty
    (params : Phi4Params)
    (huv : Nonempty (InteractionUVModel params))
    (hweight : Nonempty (InteractionWeightModel params)) :
    Nonempty (InteractionIntegrabilityModel params) := by
  rcases huv with ⟨huvInst⟩
  rcases hweight with ⟨hweightInst⟩
  letI : InteractionUVModel params := huvInst
  letI : InteractionWeightModel params := hweightInst
  exact ⟨inferInstance⟩

/-- Construct `InteractionIntegrabilityModel` from square-integrability UV
    data plus explicit Boltzmann-weight `Lᵖ` data. -/
theorem interactionIntegrabilityModel_nonempty_of_sq_integrable_data
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
    (hexp :
      ∀ (Λ : Rectangle) {p : ℝ≥0∞}, p ≠ ⊤ →
        MemLp (fun ω => Real.exp (-(interaction params Λ ω)))
          p (freeFieldMeasure params.mass params.mass_pos)) :
    Nonempty (InteractionIntegrabilityModel params) := by
  rcases interactionUVModel_nonempty_of_sq_integrable_data
      (params := params)
      hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
      hinteraction_meas hinteraction_sq with ⟨huv⟩
  rcases interactionWeightModel_nonempty_of_data (params := params) hexp with ⟨hweight⟩
  exact interactionIntegrabilityModel_nonempty_of_uv_weight_nonempty
    (params := params) ⟨huv⟩ ⟨hweight⟩

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

/-- Almost-everywhere convergence of the canonical cutoff sequence
    `κ_n = n + 1` to the limiting interaction, from explicit real-parameterized
    a.e. UV convergence data. -/
theorem interactionCutoff_standardSeq_tendsto_ae_of_tendsto_ae
    (params : Phi4Params) (Λ : Rectangle)
    (htend :
      ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
          Filter.atTop
          (nhds (interaction params Λ ω))) :
    ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
      Filter.Tendsto
        (fun n : ℕ => interactionCutoff params Λ (standardUVCutoffSeq n) ω)
        Filter.atTop
        (nhds (interaction params Λ ω)) := by
  filter_upwards [htend] with ω hωt
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
  exact hseq_raw.congr' hseq_eq

/-- Almost-everywhere convergence of the canonical cutoff sequence
    `κ_n = n + 1` to the limiting interaction. -/
theorem interactionCutoff_standardSeq_tendsto_ae
    (params : Phi4Params) (Λ : Rectangle)
    [InteractionUVModel params] :
    ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
      Filter.Tendsto
        (fun n : ℕ => interactionCutoff params Λ (standardUVCutoffSeq n) ω)
        Filter.atTop
        (nhds (interaction params Λ ω)) := by
  exact interactionCutoff_standardSeq_tendsto_ae_of_tendsto_ae
    (params := params) (Λ := Λ) (interactionCutoff_tendsto_ae params Λ)

/-- Shifted canonical-sequence (`κ_{n+1}`) specialization of the explicit
    real-parameterized a.e. UV convergence data. -/
theorem interactionCutoff_standardSeq_succ_tendsto_ae_of_tendsto_ae
    (params : Phi4Params) (Λ : Rectangle)
    (htend :
      ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
          Filter.atTop
          (nhds (interaction params Λ ω))) :
    ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
      Filter.Tendsto
        (fun n : ℕ => interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)
        Filter.atTop
        (nhds (interaction params Λ ω)) := by
  have hstd :
      ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
        Filter.Tendsto
          (fun n : ℕ => interactionCutoff params Λ (standardUVCutoffSeq n) ω)
          Filter.atTop
          (nhds (interaction params Λ ω)) :=
    interactionCutoff_standardSeq_tendsto_ae_of_tendsto_ae
      (params := params) (Λ := Λ) htend
  filter_upwards [hstd] with ω hω
  exact hω.comp (Filter.tendsto_add_atTop_nat 1)

/-- Shifted canonical-sequence (`κ_{n+1}`) specialization of L² cutoff
    convergence:
    if the real-parameterized L² convergence hypothesis holds, then the shifted
    canonical sequence satisfies
    `∫ (interactionCutoff(κ_{n+1}) - interaction)^2 → 0`. -/
theorem shifted_cutoff_interaction_sq_moment_tendsto_zero_of_converges_L2
    (params : Phi4Params) (Λ : Rectangle)
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
        ∫ ω, (interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω) ^ 2
          ∂(freeFieldMeasure params.mass params.mass_pos))
      Filter.atTop
      (nhds 0) := by
  let μ : Measure FieldConfig2D := freeFieldMeasure params.mass params.mass_pos
  have hnat' :
      Filter.Tendsto ((Nat.cast : ℕ → ℝ) ∘ fun a : ℕ => a + 2) Filter.atTop Filter.atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp (Filter.tendsto_add_atTop_nat 2)
  have hseq_raw :
      Filter.Tendsto
        (fun n : ℕ =>
          if h : 0 < ((Nat.cast : ℕ → ℝ) ((fun a : ℕ => a + 2) n)) then
            ∫ ω, (interactionCutoff params Λ
              ⟨(Nat.cast : ℕ → ℝ) ((fun a : ℕ => a + 2) n), h⟩ ω - interaction params Λ ω) ^ 2 ∂μ
          else 0)
        Filter.atTop
        (nhds 0) :=
    hcutoff_conv.comp hnat'
  have hseq_eq :
      (fun n : ℕ =>
        if h : 0 < ((Nat.cast : ℕ → ℝ) ((fun a : ℕ => a + 2) n)) then
          ∫ ω, (interactionCutoff params Λ
            ⟨(Nat.cast : ℕ → ℝ) ((fun a : ℕ => a + 2) n), h⟩ ω - interaction params Λ ω) ^ 2 ∂μ
        else 0) =ᶠ[Filter.atTop]
      (fun n : ℕ =>
        ∫ ω, (interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω) ^ 2 ∂μ) := by
    exact Filter.Eventually.of_forall (fun n => by
      have hn : 0 < ((Nat.cast : ℕ → ℝ) ((fun a : ℕ => a + 2) n)) := by
        exact_mod_cast Nat.succ_pos (n + 1)
      have hn2 : 0 < (↑n + 2 : ℝ) := by simpa using hn
      have hκ : (↑n + 2 : ℝ) = (↑n + 1 + 1 : ℝ) := by ring
      have hn3 : 0 < (↑n + 1 + 1 : ℝ) := by nlinarith [hn2, hκ]
      simp [standardUVCutoffSeq, μ, hκ, hn3])
  exact hseq_raw.congr' hseq_eq

/-- Fatou bridge for shifted canonical UV cutoffs:
    if `interactionCutoff(κ_{n+1})` converges almost everywhere to `interaction`
    and the nonnegative sequence `exp(-q·interactionCutoff(κ_{n+1}))` has a
    uniform `lintegral` bound, then `exp(-q·interaction)` is integrable. -/
theorem integrable_exp_neg_mul_interaction_of_standardSeq_succ_tendsto_ae_of_uniform_lintegral_bound
    (params : Phi4Params) (Λ : Rectangle) (q : ℝ)
    (htend :
      ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
        Filter.Tendsto
          (fun n : ℕ => interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)
          Filter.atTop
          (nhds (interaction params Λ ω)))
    (hcutoff_meas :
      ∀ n : ℕ,
        AEStronglyMeasurable
          (fun ω : FieldConfig2D => interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)
          (freeFieldMeasure params.mass params.mass_pos))
    (hbound :
      ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
        ∀ n : ℕ,
          ∫⁻ ω,
              ENNReal.ofReal
                (Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)))
            ∂(freeFieldMeasure params.mass params.mass_pos) ≤ C) :
    Integrable
      (fun ω : FieldConfig2D => Real.exp (-(q * interaction params Λ ω)))
      (freeFieldMeasure params.mass params.mass_pos) := by
  let μ : Measure FieldConfig2D := freeFieldMeasure params.mass params.mass_pos
  rcases hbound with ⟨C, hC_top, hC_bound⟩
  let g : ℕ → FieldConfig2D → ℝ :=
    fun n ω => Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
  let gLim : FieldConfig2D → ℝ :=
    fun ω => Real.exp (-(q * interaction params Λ ω))
  let F : ℕ → FieldConfig2D → ℝ≥0∞ := fun n ω => ENNReal.ofReal (g n ω)

  have hg_meas : ∀ n : ℕ, AEStronglyMeasurable (g n) μ := by
    intro n
    have htmp :
        AEMeasurable
          (fun ω : FieldConfig2D =>
            -(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)) μ := by
      simpa [μ, neg_mul] using (((hcutoff_meas n).aemeasurable.const_mul q).neg)
    exact htmp.exp.aestronglyMeasurable

  have hF_meas : ∀ n : ℕ, AEMeasurable (F n) μ := by
    intro n
    exact (hg_meas n).aemeasurable.ennreal_ofReal

  have hg_tendsto :
      ∀ᵐ ω ∂μ, Filter.Tendsto (fun n : ℕ => g n ω) Filter.atTop (nhds (gLim ω)) := by
    have hcont : Continuous fun x : ℝ => Real.exp (-(q * x)) := by
      continuity
    filter_upwards [htend] with ω hω
    exact (hcont.tendsto _).comp hω

  have hgLim_meas : AEStronglyMeasurable gLim μ :=
    aestronglyMeasurable_of_tendsto_ae Filter.atTop hg_meas hg_tendsto

  have hF_liminf_ae :
      ∀ᵐ ω ∂μ, Filter.liminf (fun n : ℕ => F n ω) Filter.atTop = ENNReal.ofReal (gLim ω) := by
    filter_upwards [hg_tendsto] with ω hω
    have hωF :
        Filter.Tendsto (fun n : ℕ => F n ω) Filter.atTop (nhds (ENNReal.ofReal (gLim ω))) := by
      exact (ENNReal.continuous_ofReal.tendsto _).comp hω
    simpa [F, gLim] using hωF.liminf_eq

  have hF_liminf_ae_eq :
      (fun ω => Filter.liminf (fun n : ℕ => F n ω) Filter.atTop) =ᵐ[μ]
        (fun ω => ENNReal.ofReal (gLim ω)) := by
    filter_upwards [hF_liminf_ae] with ω hω
    exact hω

  have hlintegral_liminf_le :
      ∫⁻ ω, ENNReal.ofReal (gLim ω) ∂μ ≤
        Filter.liminf (fun n : ℕ => ∫⁻ ω, F n ω ∂μ) Filter.atTop := by
    calc
      ∫⁻ ω, ENNReal.ofReal (gLim ω) ∂μ
          = ∫⁻ ω, Filter.liminf (fun n : ℕ => F n ω) Filter.atTop ∂μ := by
            exact lintegral_congr_ae hF_liminf_ae_eq.symm
      _ ≤ Filter.liminf (fun n : ℕ => ∫⁻ ω, F n ω ∂μ) Filter.atTop :=
            MeasureTheory.lintegral_liminf_le' hF_meas

  have hliminf_le_C :
      Filter.liminf (fun n : ℕ => ∫⁻ ω, F n ω ∂μ) Filter.atTop ≤ C := by
    have hbound_ev :
        ∀ᶠ n in Filter.atTop, (fun n : ℕ => ∫⁻ ω, F n ω ∂μ) n ≤ (fun _ : ℕ => C) n :=
      Filter.Eventually.of_forall (fun n => by
        simpa [F, g, μ] using hC_bound n)
    have hliminf_const :
        Filter.liminf (fun _ : ℕ => C) Filter.atTop = C := by
      simpa using
        (Filter.Tendsto.liminf_eq (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => C) Filter.atTop (nhds C)))
    exact (Filter.liminf_le_liminf hbound_ev).trans_eq hliminf_const

  have hlintegral_ne_top :
      ∫⁻ ω, ENNReal.ofReal (gLim ω) ∂μ ≠ ⊤ := by
    have hC_lt_top : C < ⊤ := lt_top_iff_ne_top.mpr hC_top
    exact (lt_of_le_of_lt (hlintegral_liminf_le.trans hliminf_le_C) hC_lt_top).ne

  have hgLim_nonneg : 0 ≤ᵐ[μ] gLim := by
    filter_upwards [] with ω
    exact Real.exp_nonneg _

  exact (lintegral_ofReal_ne_top_iff_integrable hgLim_meas hgLim_nonneg).1 hlintegral_ne_top

/-- Finite nonzero-`p` `Lᵖ` bridge from shifted-cutoff uniform exponential
    moments: if one has the shifted a.e. cutoff convergence and a uniform
    `lintegral` bound on `exp(-(p.toReal) * interactionCutoff(κ_{n+1}))`,
    then `exp(-interaction)` belongs to `Lᵖ`. -/
theorem memLp_exp_neg_interaction_of_standardSeq_succ_tendsto_ae_of_uniform_lintegral_bound
    (params : Phi4Params) (Λ : Rectangle)
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpTop : p ≠ ⊤)
    (htend :
      ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
        Filter.Tendsto
          (fun n : ℕ => interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)
          Filter.atTop
          (nhds (interaction params Λ ω)))
    (hcutoff_meas :
      ∀ n : ℕ,
        AEStronglyMeasurable
          (fun ω : FieldConfig2D => interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)
          (freeFieldMeasure params.mass params.mass_pos))
    (hbound :
      ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
        ∀ n : ℕ,
          ∫⁻ ω,
              ENNReal.ofReal
                (Real.exp (-(p.toReal * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)))
            ∂(freeFieldMeasure params.mass params.mass_pos) ≤ C) :
    MemLp (fun ω : FieldConfig2D => Real.exp (-(interaction params Λ ω)))
      p (freeFieldMeasure params.mass params.mass_pos) := by
  let μ : Measure FieldConfig2D := freeFieldMeasure params.mass params.mass_pos
  let f : FieldConfig2D → ℝ := fun ω => Real.exp (-(interaction params Λ ω))

  have hIntMul : Integrable
      (fun ω : FieldConfig2D => Real.exp (-(p.toReal * interaction params Λ ω))) μ :=
    integrable_exp_neg_mul_interaction_of_standardSeq_succ_tendsto_ae_of_uniform_lintegral_bound
      (params := params) (Λ := Λ) (q := p.toReal)
      htend hcutoff_meas hbound

  have hinter_meas : AEStronglyMeasurable (interaction params Λ) μ :=
    aestronglyMeasurable_of_tendsto_ae Filter.atTop hcutoff_meas htend
  have hf_meas : AEStronglyMeasurable f μ := by
    exact (hinter_meas.aemeasurable.neg.exp).aestronglyMeasurable

  have hnorm_rpow_int : Integrable (fun ω : FieldConfig2D => ‖f ω‖ ^ p.toReal) μ := by
    refine hIntMul.congr ?_
    filter_upwards [] with ω
    have hpos : 0 < Real.exp (-(interaction params Λ ω)) := Real.exp_pos _
    calc
      Real.exp (-(p.toReal * interaction params Λ ω))
          = Real.exp (p.toReal * (-(interaction params Λ ω))) := by ring
      _ = (Real.exp (-(interaction params Λ ω))) ^ p.toReal := by
        rw [Real.rpow_def_of_pos hpos, Real.log_exp, mul_comm]
      _ = ‖f ω‖ ^ p.toReal := by
        simp [f, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hpos)]

  exact (integrable_norm_rpow_iff hf_meas hp0 hpTop).1 hnorm_rpow_int

/-- Convert shifted-cutoff uniform real-integral bounds into the ENNReal
    `lintegral` bound format used by the Fatou bridge. -/
theorem uniform_lintegral_bound_of_standardSeq_succ_uniform_integral_bound
    (params : Phi4Params) (Λ : Rectangle) (q : ℝ)
    (hbound :
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
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ n : ℕ,
        ∫⁻ ω,
            ENNReal.ofReal
              (Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)))
          ∂(freeFieldMeasure params.mass params.mass_pos) ≤ C := by
  rcases hbound with ⟨D, hInt, hD⟩
  refine ⟨ENNReal.ofReal D, by simp, ?_⟩
  intro n
  let μ : Measure FieldConfig2D := freeFieldMeasure params.mass params.mass_pos
  have hnonneg :
      0 ≤ᵐ[μ]
        (fun ω : FieldConfig2D =>
          Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))) :=
    Filter.Eventually.of_forall (fun _ => Real.exp_nonneg _)
  have hlin_eq :
      ∫⁻ ω,
          ENNReal.ofReal
            (Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)))
        ∂μ =
      ENNReal.ofReal
        (∫ ω : FieldConfig2D,
          Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)) ∂μ) := by
    exact (ofReal_integral_eq_lintegral_ofReal (hInt n) hnonneg).symm
  calc
    ∫⁻ ω,
        ENNReal.ofReal
          (Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)))
      ∂(freeFieldMeasure params.mass params.mass_pos)
      = ENNReal.ofReal
          (∫ ω : FieldConfig2D,
            Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
            ∂(freeFieldMeasure params.mass params.mass_pos)) := by
            simpa [μ] using hlin_eq
    _ ≤ ENNReal.ofReal D := ENNReal.ofReal_le_ofReal (hD n)

/-- Finite nonzero-`p` `Lᵖ` bridge from shifted-cutoff uniform real-integral
    exponential-moment bounds. -/
theorem memLp_exp_neg_interaction_of_standardSeq_succ_tendsto_ae_of_uniform_integral_bound
    (params : Phi4Params) (Λ : Rectangle)
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpTop : p ≠ ⊤)
    (htend :
      ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
        Filter.Tendsto
          (fun n : ℕ => interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)
          Filter.atTop
          (nhds (interaction params Λ ω)))
    (hcutoff_meas :
      ∀ n : ℕ,
        AEStronglyMeasurable
          (fun ω : FieldConfig2D => interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)
          (freeFieldMeasure params.mass params.mass_pos))
    (hbound :
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
    MemLp (fun ω : FieldConfig2D => Real.exp (-(interaction params Λ ω)))
      p (freeFieldMeasure params.mass params.mass_pos) := by
  rcases uniform_lintegral_bound_of_standardSeq_succ_uniform_integral_bound
      (params := params) (Λ := Λ) (q := p.toReal) hbound with ⟨C, hCtop, hCbound⟩
  exact memLp_exp_neg_interaction_of_standardSeq_succ_tendsto_ae_of_uniform_lintegral_bound
    (params := params) (Λ := Λ) (hp0 := hp0) (hpTop := hpTop)
    htend hcutoff_meas ⟨C, hCtop, hCbound⟩

/-- Construct `InteractionWeightModel` from shifted-cutoff a.e. convergence and
    uniform shifted-cutoff exponential moments for every finite exponent.
    This is an assumption-explicit Fatou/`Lᵖ` packaging route that does not
    require `InteractionUVModel` as an input. -/
theorem interactionWeightModel_nonempty_of_standardSeq_succ_tendsto_ae_and_uniform_lintegral_bound
    (params : Phi4Params)
    (htend :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun n : ℕ => interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)
            Filter.atTop
            (nhds (interaction params Λ ω)))
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (n : ℕ),
        AEStronglyMeasurable
          (fun ω : FieldConfig2D => interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)
          (freeFieldMeasure params.mass params.mass_pos))
    (hbound :
      ∀ (Λ : Rectangle) {p : ℝ≥0∞}, p ≠ ⊤ →
        ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
          ∀ n : ℕ,
            ∫⁻ ω,
                ENNReal.ofReal
                  (Real.exp (-(p.toReal * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)))
              ∂(freeFieldMeasure params.mass params.mass_pos) ≤ C) :
    Nonempty (InteractionWeightModel params) := by
  refine interactionWeightModel_nonempty_of_data (params := params) ?_
  intro Λ p hpTop
  by_cases hp0 : p = 0
  · rw [hp0]
    rw [memLp_zero_iff_aestronglyMeasurable]
    have hmeas_cut : ∀ n : ℕ,
        AEStronglyMeasurable
          (fun ω : FieldConfig2D => interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)
          (freeFieldMeasure params.mass params.mass_pos) :=
      hcutoff_meas Λ
    have hmeas_lim : AEStronglyMeasurable (interaction params Λ)
        (freeFieldMeasure params.mass params.mass_pos) :=
      aestronglyMeasurable_of_tendsto_ae Filter.atTop hmeas_cut (htend Λ)
    exact (hmeas_lim.aemeasurable.neg.exp).aestronglyMeasurable
  · exact memLp_exp_neg_interaction_of_standardSeq_succ_tendsto_ae_of_uniform_lintegral_bound
      (params := params) (Λ := Λ) (hp0 := hp0) (hpTop := hpTop)
      (htend Λ) (hcutoff_meas Λ) (hbound Λ hpTop)

/-- Construct `InteractionWeightModel` from shifted-cutoff a.e. convergence and
    uniform shifted-cutoff real-integral exponential-moment bounds for every
    finite exponent. This is the real-integral variant of the Fatou route and
    matches constructive Theorem 8.6.2-style hypotheses. -/
theorem interactionWeightModel_nonempty_of_standardSeq_succ_tendsto_ae_and_uniform_integral_bound
    (params : Phi4Params)
    (htend :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun n : ℕ => interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)
            Filter.atTop
            (nhds (interaction params Λ ω)))
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
  refine interactionWeightModel_nonempty_of_data (params := params) ?_
  intro Λ p hpTop
  by_cases hp0 : p = 0
  · rw [hp0]
    rw [memLp_zero_iff_aestronglyMeasurable]
    have hmeas_cut : ∀ n : ℕ,
        AEStronglyMeasurable
          (fun ω : FieldConfig2D => interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)
          (freeFieldMeasure params.mass params.mass_pos) :=
      hcutoff_meas Λ
    have hmeas_lim : AEStronglyMeasurable (interaction params Λ)
        (freeFieldMeasure params.mass params.mass_pos) :=
      aestronglyMeasurable_of_tendsto_ae Filter.atTop hmeas_cut (htend Λ)
    exact (hmeas_lim.aemeasurable.neg.exp).aestronglyMeasurable
  · exact memLp_exp_neg_interaction_of_standardSeq_succ_tendsto_ae_of_uniform_integral_bound
      (params := params) (Λ := Λ) (hp0 := hp0) (hpTop := hpTop)
      (htend Λ) (hcutoff_meas Λ) (hbound Λ hpTop)

/-- Convert geometric shifted-cutoff real-integral bounds
    `∫ exp(-(q)*V_{n+1}) ≤ D * r^n` with `0 ≤ r < 1` to uniform
    shifted-cutoff real-integral bounds `∫ exp(-(q)*V_{n+1}) ≤ D`. -/
theorem uniform_integral_bound_of_standardSeq_succ_geometric_integral_bound
    (params : Phi4Params) (Λ : Rectangle) (q : ℝ)
    (hgeom :
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
    ∃ D : ℝ,
      (∀ n : ℕ,
        Integrable
          (fun ω : FieldConfig2D =>
            Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)))
          (freeFieldMeasure params.mass params.mass_pos)) ∧
      (∀ n : ℕ,
        ∫ ω : FieldConfig2D,
          Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
          ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D) := by
  rcases hgeom with ⟨D, r, hD, hr0, hr1, hInt, hM⟩
  refine ⟨D, hInt, ?_⟩
  intro n
  have hrpow_le : r ^ n ≤ 1 := by
    exact pow_le_one₀ hr0 (le_of_lt hr1)
  have hDr_le_D : D * r ^ n ≤ D := by
    calc
      D * r ^ n ≤ D * 1 := mul_le_mul_of_nonneg_left hrpow_le hD
      _ = D := by ring
  exact (hM n).trans hDr_le_D

/-- Construct `InteractionWeightModel` from shifted-cutoff a.e. convergence and
    per-exponent geometric shifted-cutoff exponential-moment bounds
    `∫ exp(-(p.toReal)*V_{n+1}) ≤ D * r^n` with `0 ≤ r < 1`.
    This theorem converts geometric decay to the uniform real-integral bounds
    required by the preceding Fatou-based constructor. -/
theorem interactionWeightModel_nonempty_of_standardSeq_succ_tendsto_ae_and_geometric_integral_bound
    (params : Phi4Params)
    (htend :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun n : ℕ => interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)
            Filter.atTop
            (nhds (interaction params Λ ω)))
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
  refine interactionWeightModel_nonempty_of_standardSeq_succ_tendsto_ae_and_uniform_integral_bound
    (params := params) htend hcutoff_meas ?_
  intro Λ p hpTop
  exact uniform_integral_bound_of_standardSeq_succ_geometric_integral_bound
    (params := params) (Λ := Λ) (q := p.toReal) (hgeom := hgeom Λ hpTop)

/-- Construct `InteractionWeightModel` from explicit real-parameterized a.e.
    UV convergence, cutoff measurability data, and per-exponent uniform
    shifted-cutoff integral bounds. This theorem bridges real-parameter UV data
    to the shifted canonical-sequence Fatou route without using class bundles. -/
theorem interactionWeightModel_nonempty_of_tendsto_ae_and_uniform_integral_bound
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
  refine interactionWeightModel_nonempty_of_standardSeq_succ_tendsto_ae_and_uniform_integral_bound
    (params := params) ?_ ?_ hbound
  · intro Λ
    exact interactionCutoff_standardSeq_succ_tendsto_ae_of_tendsto_ae
      (params := params) (Λ := Λ) (hcutoff_tendsto_ae Λ)
  · intro Λ n
    simpa using hcutoff_meas Λ (standardUVCutoffSeq (n + 1))

/-- Construct `InteractionWeightModel` from explicit real-parameterized a.e.
    UV convergence, cutoff measurability data, and per-exponent geometric
    shifted-cutoff integral bounds. This theorem bridges real-parameter UV data
    to the shifted canonical-sequence geometric/Fatou route without class bundles. -/
theorem interactionWeightModel_nonempty_of_tendsto_ae_and_geometric_integral_bound
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
  refine interactionWeightModel_nonempty_of_standardSeq_succ_tendsto_ae_and_geometric_integral_bound
    (params := params) ?_ ?_ hgeom
  · intro Λ
    exact interactionCutoff_standardSeq_succ_tendsto_ae_of_tendsto_ae
      (params := params) (Λ := Λ) (hcutoff_tendsto_ae Λ)
  · intro Λ n
    simpa using hcutoff_meas Λ (standardUVCutoffSeq (n + 1))

/-- If the canonical cutoff sequence is eventually bounded below almost surely,
    and one has explicit almost-everywhere convergence of that sequence to the
    limiting interaction, then the limit inherits the same lower bound.
    This is the assumption-minimal transfer lemma used by downstream
    `exp(-interaction)` integrability bridges. -/
theorem interaction_ae_lower_bound_of_cutoff_seq_eventually_of_standardSeq_tendsto_ae
    (params : Phi4Params) (Λ : Rectangle) (B : ℝ)
    (htend :
      ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
        Filter.Tendsto
          (fun n : ℕ => interactionCutoff params Λ (standardUVCutoffSeq n) ω)
          Filter.atTop
          (nhds (interaction params Λ ω)))
    (hcutoff_ae :
      ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
        ∀ᶠ n in Filter.atTop,
          -B ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω) :
    ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
      -B ≤ interaction params Λ ω := by
  filter_upwards [hcutoff_ae, htend] with ω hω hωt
  have hcutoff_mem :
      ∀ᶠ n in Filter.atTop,
        interactionCutoff params Λ (standardUVCutoffSeq n) ω ∈ Set.Ici (-B) :=
    hω
  exact isClosed_Ici.mem_of_tendsto hωt hcutoff_mem

/-- If the canonical cutoff sequence is eventually bounded below almost surely,
    then the limiting interaction inherits the same almost-everywhere lower bound. -/
theorem interaction_ae_lower_bound_of_cutoff_seq_eventually
    (params : Phi4Params) (Λ : Rectangle) (B : ℝ)
    [InteractionUVModel params]
    (hcutoff_ae :
      ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
        ∀ᶠ n in Filter.atTop,
          -B ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω) :
    ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
      -B ≤ interaction params Λ ω := by
  exact interaction_ae_lower_bound_of_cutoff_seq_eventually_of_standardSeq_tendsto_ae
    (params := params) (Λ := Λ) (B := B)
    (interactionCutoff_standardSeq_tendsto_ae params Λ)
    hcutoff_ae

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
  have hevent :
      ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
        ∀ᶠ n in Filter.atTop,
          -B ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω :=
    hall.mono (fun ω hω => Filter.Eventually.of_forall hω)
  exact interaction_ae_lower_bound_of_cutoff_seq_eventually params Λ B hevent

/-- Shifted-sequence transfer: if `-B` bounds all cutoff interactions along
    `κ_{n+1}`, then the unshifted canonical sequence is eventually bounded below
    by `-B` almost surely. This isolates the common `n = 0` bookkeeping step. -/
theorem cutoff_seq_eventually_lower_bound_of_succ
    (params : Phi4Params) (Λ : Rectangle) (B : ℝ)
    (hcutoff_ae :
      ∀ n : ℕ,
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          -B ≤ interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω) :
    ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
      ∀ᶠ n in Filter.atTop,
        -B ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω := by
  have hall :
      ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
        ∀ n : ℕ, -B ≤ interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω := by
    rw [eventually_countable_forall]
    intro n
    exact hcutoff_ae n
  filter_upwards [hall] with ω hω
  refine Filter.eventually_atTop.2 ?_
  refine ⟨1, ?_⟩
  intro n hn
  cases n with
  | zero =>
      exact (False.elim (Nat.not_succ_le_zero 0 hn))
  | succ m =>
      simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hω m

/-- Shifted-sequence lower bounds (`κ_{n+1}`) imply an almost-everywhere lower
    bound on the limiting interaction. -/
theorem interaction_ae_lower_bound_of_cutoff_seq_succ
    (params : Phi4Params) (Λ : Rectangle) (B : ℝ)
    [InteractionUVModel params]
    (hcutoff_ae :
      ∀ n : ℕ,
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          -B ≤ interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω) :
    ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
      -B ≤ interaction params Λ ω := by
  have hcutoff_ev :
      ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
        ∀ᶠ n in Filter.atTop,
          -B ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω :=
    cutoff_seq_eventually_lower_bound_of_succ params Λ B hcutoff_ae
  exact interaction_ae_lower_bound_of_cutoff_seq_eventually params Λ B hcutoff_ev

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

/-- Measurable-version of `exp_interaction_Lp_of_ae_lower_bound`:
    if one provides measurability of `interaction params Λ` directly, no
    `InteractionUVModel` assumption is needed for the `Lᵖ` conclusion. -/
theorem exp_interaction_Lp_of_ae_lower_bound_of_aestronglyMeasurable
    (params : Phi4Params) (Λ : Rectangle)
    (hmeas :
      AEStronglyMeasurable (interaction params Λ)
        (freeFieldMeasure params.mass params.mass_pos))
    (B : ℝ)
    (hbound : ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
      -B ≤ interaction params Λ ω)
    {p : ℝ≥0∞} :
    MemLp (fun ω => Real.exp (-(interaction params Λ ω)))
      p (freeFieldMeasure params.mass params.mass_pos) := by
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

/-- `Lᵖ` integrability of the Boltzmann weight from an eventually-in-`n`
    almost-everywhere lower bound on the canonical cutoff sequence, using
    explicit measurability of `interaction` and explicit a.e. convergence of
    the canonical cutoff sequence. -/
theorem
    exp_interaction_Lp_of_cutoff_seq_eventually_lower_bound_of_aestronglyMeasurable_and_standardSeq_tendsto_ae
    (params : Phi4Params) (Λ : Rectangle)
    (hmeas :
      AEStronglyMeasurable (interaction params Λ)
        (freeFieldMeasure params.mass params.mass_pos))
    (htend :
      ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
        Filter.Tendsto
          (fun n : ℕ => interactionCutoff params Λ (standardUVCutoffSeq n) ω)
          Filter.atTop
          (nhds (interaction params Λ ω)))
    (B : ℝ)
    (hcutoff_ae :
      ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
        ∀ᶠ n in Filter.atTop,
          -B ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω)
    {p : ℝ≥0∞} :
    MemLp (fun ω => Real.exp (-(interaction params Λ ω)))
      p (freeFieldMeasure params.mass params.mass_pos) := by
  have hbound :
      ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
        -B ≤ interaction params Λ ω :=
    interaction_ae_lower_bound_of_cutoff_seq_eventually_of_standardSeq_tendsto_ae
      (params := params) (Λ := Λ) (B := B) htend hcutoff_ae
  exact exp_interaction_Lp_of_ae_lower_bound_of_aestronglyMeasurable
    (params := params) (Λ := Λ) hmeas B hbound

/-- `Lᵖ` integrability of the Boltzmann weight from an eventually-in-`n`
    almost-everywhere lower bound on the canonical cutoff sequence. -/
theorem exp_interaction_Lp_of_cutoff_seq_eventually_lower_bound
    (params : Phi4Params) (Λ : Rectangle)
    [InteractionUVModel params]
    (B : ℝ)
    (hcutoff_ae :
      ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
        ∀ᶠ n in Filter.atTop,
          -B ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω)
    {p : ℝ≥0∞} :
    MemLp (fun ω => Real.exp (-(interaction params Λ ω)))
      p (freeFieldMeasure params.mass params.mass_pos) := by
  refine
    exp_interaction_Lp_of_cutoff_seq_eventually_lower_bound_of_aestronglyMeasurable_and_standardSeq_tendsto_ae
      (params := params) (Λ := Λ)
      ((interaction_in_L2 params Λ).aestronglyMeasurable)
      (interactionCutoff_standardSeq_tendsto_ae params Λ)
      (B := B) hcutoff_ae

/-- `Lᵖ` integrability of the Boltzmann weight from shifted canonical
    cutoff-sequence lower bounds (`κ_{n+1}`). -/
theorem exp_interaction_Lp_of_cutoff_seq_succ_lower_bounds
    (params : Phi4Params) (Λ : Rectangle)
    [InteractionUVModel params]
    (B : ℝ)
    (hcutoff_ae :
      ∀ n : ℕ,
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          -B ≤ interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)
    {p : ℝ≥0∞} :
    MemLp (fun ω => Real.exp (-(interaction params Λ ω)))
      p (freeFieldMeasure params.mass params.mass_pos) := by
  refine exp_interaction_Lp_of_ae_lower_bound (params := params) (Λ := Λ)
    (B := B) ?_
  exact interaction_ae_lower_bound_of_cutoff_seq_succ params Λ B hcutoff_ae

/-- Shift eventually-at-top bounds from `n + 1` back to the canonical index `n`.
    This is the index bookkeeping bridge used when analytic estimates are only
    available for UV scales `κ > 1`. -/
theorem eventually_atTop_of_eventually_atTop_succ {P : ℕ → Prop}
    (h : ∀ᶠ n in Filter.atTop, P (n + 1)) :
    ∀ᶠ n in Filter.atTop, P n := by
  rcases Filter.eventually_atTop.1 h with ⟨N, hN⟩
  refine Filter.eventually_atTop.2 ?_
  refine ⟨N + 1, ?_⟩
  intro n hn
  cases n with
  | zero =>
      exact (False.elim (Nat.not_succ_le_zero N hn))
  | succ m =>
      have hm : N ≤ m := by
        exact Nat.succ_le_succ_iff.mp hn
      exact hN m hm

/-- If cutoff lower bounds can fail only on a summable family of bad sets,
    then the cutoff sequence is eventually bounded below almost surely. -/
theorem cutoff_seq_eventually_lower_bound_of_bad_set_summable
    (params : Phi4Params) (Λ : Rectangle) (B : ℝ)
    (bad : ℕ → Set FieldConfig2D)
    (hbad_sum :
      (∑' n : ℕ,
        (freeFieldMeasure params.mass params.mass_pos) (bad n)) ≠ ∞)
    (hcutoff_good :
      ∀ n : ℕ, ∀ ω : FieldConfig2D, ω ∉ bad n →
        -B ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω) :
    ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
      ∀ᶠ n in Filter.atTop,
        -B ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω := by
  have hnotbad :
      ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
        ∀ᶠ n in Filter.atTop, ω ∉ bad n :=
    MeasureTheory.ae_eventually_notMem
      (μ := freeFieldMeasure params.mass params.mass_pos) hbad_sum
  filter_upwards [hnotbad] with ω hω
  exact hω.mono (fun n hn => hcutoff_good n ω hn)

/-- If the bad-event probabilities for a fixed lower bound `-B` are summable,
    then the cutoff sequence is eventually bounded below by `-B` almost surely. -/
theorem cutoff_seq_eventually_lower_bound_of_summable_bad_event_measure
    (params : Phi4Params) (Λ : Rectangle) (B : ℝ)
    (hbad_sum :
      (∑' n : ℕ,
        (freeFieldMeasure params.mass params.mass_pos)
          {ω : FieldConfig2D |
            interactionCutoff params Λ (standardUVCutoffSeq n) ω < -B}) ≠ ∞) :
    ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
      ∀ᶠ n in Filter.atTop,
        -B ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω := by
  refine cutoff_seq_eventually_lower_bound_of_bad_set_summable
    (params := params) (Λ := Λ) (B := B)
    (bad := fun n => {ω : FieldConfig2D |
      interactionCutoff params Λ (standardUVCutoffSeq n) ω < -B})
    hbad_sum ?_
  intro n ω hω
  exact not_lt.mp hω

/-- Shifted-index Borel-Cantelli transfer:
    if lower bounds along `κ_{n+1}` fail only on a summable bad-set family,
    then the canonical cutoff sequence is eventually bounded below almost surely. -/
theorem cutoff_seq_eventually_lower_bound_of_shifted_bad_set_summable
    (params : Phi4Params) (Λ : Rectangle) (B : ℝ)
    (bad : ℕ → Set FieldConfig2D)
    (hbad_sum :
      (∑' n : ℕ,
        (freeFieldMeasure params.mass params.mass_pos) (bad n)) ≠ ∞)
    (hcutoff_good :
      ∀ n : ℕ, ∀ ω : FieldConfig2D, ω ∉ bad n →
        -B ≤ interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω) :
    ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
      ∀ᶠ n in Filter.atTop,
        -B ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω := by
  have hnotbad :
      ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
        ∀ᶠ n in Filter.atTop, ω ∉ bad n :=
    MeasureTheory.ae_eventually_notMem
      (μ := freeFieldMeasure params.mass params.mass_pos) hbad_sum
  filter_upwards [hnotbad] with ω hω
  have hsucc :
      ∀ᶠ n in Filter.atTop,
        -B ≤ interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω :=
    hω.mono (fun n hn => hcutoff_good n ω hn)
  exact eventually_atTop_of_eventually_atTop_succ hsucc

/-- Shifted-index specialization of summable bad-event tails:
    if events `{interactionCutoff(κ_{n+1}) < -B}` are summable, then the
    canonical sequence is eventually bounded below almost surely. -/
theorem cutoff_seq_eventually_lower_bound_of_shifted_summable_bad_event_measure
    (params : Phi4Params) (Λ : Rectangle) (B : ℝ)
    (hbad_sum :
      (∑' n : ℕ,
        (freeFieldMeasure params.mass params.mass_pos)
          {ω : FieldConfig2D |
            interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω < -B}) ≠ ∞) :
    ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
      ∀ᶠ n in Filter.atTop,
        -B ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω := by
  refine cutoff_seq_eventually_lower_bound_of_shifted_bad_set_summable
    (params := params) (Λ := Λ) (B := B)
    (bad := fun n => {ω : FieldConfig2D |
      interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω < -B})
    hbad_sum ?_
  intro n ω hω
  exact not_lt.mp hω

/-- Summable bad-event tails for cutoff lower bounds imply an almost-everywhere
    lower bound on the limiting interaction. -/
theorem interaction_ae_lower_bound_of_cutoff_seq_summable_bad_event_measure
    (params : Phi4Params) (Λ : Rectangle) (B : ℝ)
    [InteractionUVModel params]
    (hbad_sum :
      (∑' n : ℕ,
        (freeFieldMeasure params.mass params.mass_pos)
          {ω : FieldConfig2D |
            interactionCutoff params Λ (standardUVCutoffSeq n) ω < -B}) ≠ ∞) :
    ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
      -B ≤ interaction params Λ ω := by
  have hcutoff_ev :
      ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
        ∀ᶠ n in Filter.atTop,
          -B ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω :=
    cutoff_seq_eventually_lower_bound_of_summable_bad_event_measure params Λ B hbad_sum
  exact interaction_ae_lower_bound_of_cutoff_seq_eventually params Λ B hcutoff_ev

/-- Shifted-index summable bad-event tails imply an almost-everywhere lower
    bound on the limiting interaction. -/
theorem interaction_ae_lower_bound_of_cutoff_seq_shifted_summable_bad_event_measure
    (params : Phi4Params) (Λ : Rectangle) (B : ℝ)
    [InteractionUVModel params]
    (hbad_sum :
      (∑' n : ℕ,
        (freeFieldMeasure params.mass params.mass_pos)
          {ω : FieldConfig2D |
            interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω < -B}) ≠ ∞) :
    ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
      -B ≤ interaction params Λ ω := by
  have hcutoff_ev :
      ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
        ∀ᶠ n in Filter.atTop,
          -B ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω :=
    cutoff_seq_eventually_lower_bound_of_shifted_summable_bad_event_measure
      params Λ B hbad_sum
  exact interaction_ae_lower_bound_of_cutoff_seq_eventually params Λ B hcutoff_ev

/-- Shifted-index summable bad sets with good-set lower bounds imply an
    almost-everywhere lower bound on the limiting interaction. -/
theorem interaction_ae_lower_bound_of_cutoff_seq_shifted_bad_set_summable
    (params : Phi4Params) (Λ : Rectangle) (B : ℝ)
    [InteractionUVModel params]
    (bad : ℕ → Set FieldConfig2D)
    (hbad_sum :
      (∑' n : ℕ,
        (freeFieldMeasure params.mass params.mass_pos) (bad n)) ≠ ∞)
    (hcutoff_good :
      ∀ n : ℕ, ∀ ω : FieldConfig2D, ω ∉ bad n →
        -B ≤ interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω) :
    ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
      -B ≤ interaction params Λ ω := by
  have hcutoff_ev :
      ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
        ∀ᶠ n in Filter.atTop,
          -B ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω :=
    cutoff_seq_eventually_lower_bound_of_shifted_bad_set_summable
      params Λ B bad hbad_sum hcutoff_good
  exact interaction_ae_lower_bound_of_cutoff_seq_eventually params Λ B hcutoff_ev

/-- Summable bad sets with good-set cutoff lower bounds imply an
    almost-everywhere lower bound on the limiting interaction. -/
theorem interaction_ae_lower_bound_of_cutoff_seq_bad_set_summable
    (params : Phi4Params) (Λ : Rectangle) (B : ℝ)
    [InteractionUVModel params]
    (bad : ℕ → Set FieldConfig2D)
    (hbad_sum :
      (∑' n : ℕ,
        (freeFieldMeasure params.mass params.mass_pos) (bad n)) ≠ ∞)
    (hcutoff_good :
      ∀ n : ℕ, ∀ ω : FieldConfig2D, ω ∉ bad n →
        -B ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω) :
    ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
      -B ≤ interaction params Λ ω := by
  have hcutoff_ev :
      ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
        ∀ᶠ n in Filter.atTop,
          -B ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω :=
    cutoff_seq_eventually_lower_bound_of_bad_set_summable
      params Λ B bad hbad_sum hcutoff_good
  exact interaction_ae_lower_bound_of_cutoff_seq_eventually params Λ B hcutoff_ev

/-- `Lᵖ` integrability of the Boltzmann weight from summable bad-event tails
    for cutoff lower bounds. -/
theorem exp_interaction_Lp_of_cutoff_seq_summable_bad_event_measure
    (params : Phi4Params) (Λ : Rectangle)
    [InteractionUVModel params]
    (B : ℝ)
    (hbad_sum :
      (∑' n : ℕ,
        (freeFieldMeasure params.mass params.mass_pos)
          {ω : FieldConfig2D |
            interactionCutoff params Λ (standardUVCutoffSeq n) ω < -B}) ≠ ∞)
    {p : ℝ≥0∞} :
    MemLp (fun ω => Real.exp (-(interaction params Λ ω)))
      p (freeFieldMeasure params.mass params.mass_pos) := by
  have hcutoff_ev :
      ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
        ∀ᶠ n in Filter.atTop,
          -B ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω :=
    cutoff_seq_eventually_lower_bound_of_summable_bad_event_measure params Λ B hbad_sum
  exact exp_interaction_Lp_of_cutoff_seq_eventually_lower_bound
    (params := params) (Λ := Λ) (B := B) hcutoff_ev

/-- `Lᵖ` integrability from shifted-index summable bad-event tails
    (`κ_{n+1}` events). -/
theorem exp_interaction_Lp_of_cutoff_seq_shifted_summable_bad_event_measure
    (params : Phi4Params) (Λ : Rectangle)
    [InteractionUVModel params]
    (B : ℝ)
    (hbad_sum :
      (∑' n : ℕ,
        (freeFieldMeasure params.mass params.mass_pos)
          {ω : FieldConfig2D |
            interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω < -B}) ≠ ∞)
    {p : ℝ≥0∞} :
    MemLp (fun ω => Real.exp (-(interaction params Λ ω)))
      p (freeFieldMeasure params.mass params.mass_pos) := by
  have hcutoff_ev :
      ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
        ∀ᶠ n in Filter.atTop,
          -B ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω :=
    cutoff_seq_eventually_lower_bound_of_shifted_summable_bad_event_measure
      params Λ B hbad_sum
  exact exp_interaction_Lp_of_cutoff_seq_eventually_lower_bound
    (params := params) (Λ := Λ) (B := B) hcutoff_ev


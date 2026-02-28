/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.Function.L2Space
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
    `κ_n = n + 1` to the limiting interaction. -/
theorem interactionCutoff_standardSeq_tendsto_ae
    (params : Phi4Params) (Λ : Rectangle)
    [InteractionUVModel params] :
    ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
      Filter.Tendsto
        (fun n : ℕ => interactionCutoff params Λ (standardUVCutoffSeq n) ω)
        Filter.atTop
        (nhds (interaction params Λ ω)) := by
  have htend :
      ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
          Filter.atTop
          (nhds (interaction params Λ ω)) :=
    interactionCutoff_tendsto_ae params Λ
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
  have htend := interactionCutoff_standardSeq_tendsto_ae params Λ
  filter_upwards [hcutoff_ae, htend] with ω hω hωt
  have hcutoff_mem :
      ∀ᶠ n in Filter.atTop,
        interactionCutoff params Λ (standardUVCutoffSeq n) ω ∈ Set.Ici (-B) :=
    hω
  exact isClosed_Ici.mem_of_tendsto hωt hcutoff_mem

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
  refine exp_interaction_Lp_of_ae_lower_bound (params := params) (Λ := Λ)
    (B := B) ?_
  exact interaction_ae_lower_bound_of_cutoff_seq_eventually params Λ B hcutoff_ae

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
  have hcutoff_ev :
      ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
        ∀ᶠ n in Filter.atTop,
          -B ≤ interactionCutoff params Λ (standardUVCutoffSeq n) ω :=
    cutoff_seq_eventually_lower_bound_of_shifted_bad_set_summable
      params Λ B bad hbad_sum hcutoff_good
  exact exp_interaction_Lp_of_cutoff_seq_eventually_lower_bound
    (params := params) (Λ := Λ) (B := B) hcutoff_ev

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
  refine interactionWeightModel_nonempty_of_data params ?_
  intro Λ p _hp
  rcases hwick_bad Λ with
    ⟨B, C, α, hC, hα, hbad_le, hΛ_meas, hΛ_finite, hwick_int⟩
  exact exp_interaction_Lp_of_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets
    (params := params) (Λ := Λ) (B := B) (C := C) (α := α)
    hC hα hbad_le hΛ_meas hΛ_finite hwick_int

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
  refine interactionWeightModel_nonempty_of_data params ?_
  intro Λ p _hp
  rcases hcutoff_ae Λ with ⟨B, hB⟩
  exact exp_interaction_Lp_of_cutoff_seq_eventually_lower_bound
    (params := params) (Λ := Λ) (B := B) hB

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
    interaction_ae_lower_bound_of_cutoff_seq_eventually
      (params := params) (Λ := Λ) (B := 0) hcutoff_ev_neg
  simpa using hinteraction

/-- Construct `InteractionWeightModel` from geometric decay of shifted-index
    exponential moments of the cutoff interaction:
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
  have hbound :
      ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
        -0 ≤ interaction params Λ ω := by
    simpa using
      (interaction_ae_nonneg_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
        (params := params) (Λ := Λ) hmom)
  simpa using
    (exp_interaction_Lp_of_ae_lower_bound
      (params := params) (Λ := Λ) (B := 0) hbound : MemLp
        (fun ω => Real.exp (-(interaction params Λ ω)))
        p (freeFieldMeasure params.mass params.mass_pos))

/-- `Lᵖ` integrability endpoint from:
    1. square-integrability/measurability UV data (used to instantiate
       `InteractionUVModel`), and
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
  rcases interactionUVModel_nonempty_of_sq_integrable_data
      (params := params)
      hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
      hinteraction_meas hinteraction_sq with ⟨huv⟩
  letI : InteractionUVModel params := huv
  exact exp_interaction_Lp_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
    (params := params) (Λ := Λ) hmom

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
  refine interactionWeightModel_nonempty_of_cutoff_seq_shifted_geometric_bad_event_bound
    (params := params) ?_
  intro Λ
  rcases
      shifted_cutoff_bad_event_geometric_bound_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
        (params := params) hmom Λ with ⟨C, r, hC, hr, hbad⟩
  refine ⟨0, C, r, hC, hr, ?_⟩
  simpa using hbad

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
  exact interactionIntegrabilityModel_nonempty_of_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets
    (params := params) hwick_bad

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
  exact interactionIntegrabilityModel_nonempty_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
    (params := params) hmom

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
  have hInt :
      Nonempty (InteractionIntegrabilityModel params) :=
    interactionIntegrabilityModel_nonempty_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
      (params := params)
      hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
      hinteraction_meas hinteraction_sq hmom
  have hW :
      Nonempty (InteractionWeightModel params) :=
    interactionWeightModel_nonempty_of_integrability_nonempty
      (params := params) hInt
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
  have hInt :
      Nonempty (InteractionIntegrabilityModel params) :=
    interactionIntegrabilityModel_nonempty_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
      (params := params)
      hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
      hinteraction_meas hinteraction_sq hmom
  have hW :
      Nonempty (InteractionWeightModel params) :=
    interactionWeightModel_nonempty_of_integrability_nonempty
      (params := params) hInt
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
  rcases interactionUVModel_nonempty_of_sq_integrable_data
      (params := params)
      hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
      hinteraction_meas hinteraction_sq with ⟨huv⟩
  letI : InteractionUVModel params := huv
  exact partition_function_pos_of_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets
    (params := params) hwick_bad Λ

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
  rcases interactionUVModel_nonempty_of_sq_integrable_data
      (params := params)
      hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
      hinteraction_meas hinteraction_sq with ⟨huv⟩
  letI : InteractionUVModel params := huv
  exact partition_function_integrable_of_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets
    (params := params) hwick_bad Λ

end

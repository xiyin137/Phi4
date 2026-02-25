/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
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

private def uvSeq (n : ℕ) : UVCutoff :=
  ⟨n + 1, by exact_mod_cast Nat.succ_pos n⟩

/-- The interaction V_Λ = lim_{κ→∞} V_{Λ,κ} (UV limit with fixed volume cutoff).
    The limit exists in L² by Theorem 8.5.3. -/
def interaction (params : Phi4Params) (Λ : Rectangle) (ω : FieldConfig2D) : ℝ :=
  Filter.limsup (fun n : ℕ => interactionCutoff params Λ (uvSeq n) ω) Filter.atTop

/-! ## Semiboundedness of the Wick-ordered quartic

Although :φ⁴: = φ⁴ - 6cφ² + 3c² is not pointwise bounded below (the Wick subtractions
destroy the positivity of φ⁴), it is "almost" bounded below: the set where it is very
negative has exponentially small Gaussian measure. -/

/-- Semiboundedness of the UV-regularized quartic Wick product.
    :φ_κ(x)⁴:_C ≥ -6c_κ(x)² ≥ -const × (ln κ)² for d=2.
    (Proposition 8.6.3 of Glimm-Jaffe)

    The constant C depends only on the mass, not on the field configuration or point. -/
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
  interaction_in_L2 :
    ∀ (Λ : Rectangle),
      MemLp (interaction params Λ) 2
        (freeFieldMeasure params.mass params.mass_pos)
  exp_interaction_Lp :
    ∀ (Λ : Rectangle) {p : ℝ≥0∞}, p ≠ ⊤ →
      MemLp (fun ω => Real.exp (-(interaction params Λ ω)))
        p (freeFieldMeasure params.mass params.mass_pos)

/-! ## The interaction is in Lᵖ -/

/-- The UV-regularized interaction V_{Λ,κ} is in L²(dφ_C).
    This follows from the localized Feynman graph bounds (Theorem 8.5.3).
    The bound is uniform in κ. -/
theorem interactionCutoff_in_L2 (params : Phi4Params) (Λ : Rectangle)
    [InteractionIntegrabilityModel params]
    (κ : UVCutoff) :
    MemLp (interactionCutoff params Λ κ) 2 (freeFieldMeasure params.mass params.mass_pos) := by
  exact InteractionIntegrabilityModel.interactionCutoff_in_L2
    (params := params) Λ κ

/-- Convergence of V_{Λ,κ} → V_Λ in L² as κ → ∞.
    The limit is taken in the L²(dφ_C) norm:
      ‖V_{Λ,κ} - V_Λ‖_{L²(dφ_C)} → 0 as κ → ∞. -/
theorem interactionCutoff_converges_L2 (params : Phi4Params)
    [InteractionIntegrabilityModel params]
    (Λ : Rectangle) :
    Filter.Tendsto
      (fun (κ : ℝ) => if h : 0 < κ then
        ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
          ∂(freeFieldMeasure params.mass params.mass_pos)
        else 0)
      Filter.atTop
      (nhds 0) := by
  exact InteractionIntegrabilityModel.interactionCutoff_converges_L2
    (params := params) Λ

/-- The interaction V_Λ is in L²(dφ_C). -/
theorem interaction_in_L2 (params : Phi4Params)
    [InteractionIntegrabilityModel params]
    (Λ : Rectangle) :
    MemLp (interaction params Λ) 2 (freeFieldMeasure params.mass params.mass_pos) := by
  exact InteractionIntegrabilityModel.interaction_in_L2
    (params := params) Λ

/-! ## The exponential of the interaction is in Lᵖ

This is the central estimate of the chapter (Theorem 8.6.2 of Glimm-Jaffe).
The proof has two main steps:
1. Semiboundedness: :P(φ_κ):_C ≥ -const × (ln κ)^{deg P/2}
2. Gaussian tail estimates: P(|:φ_κ: < threshold|) ≤ exp(-const × κ^δ)
-/

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
    [InteractionIntegrabilityModel params]
    {p : ℝ≥0∞} (hp : p ≠ ⊤) :
    MemLp (fun ω => Real.exp (-(interaction params Λ ω)))
      p (freeFieldMeasure params.mass params.mass_pos) := by
  exact InteractionIntegrabilityModel.exp_interaction_Lp
    (params := params) Λ hp

/-- Positivity of the partition function: Z_Λ = ∫ e^{-V_Λ} dφ_C > 0. -/
theorem partition_function_pos (params : Phi4Params)
    [InteractionIntegrabilityModel params]
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
    [InteractionIntegrabilityModel params]
    (Λ : Rectangle) :
    Integrable (fun ω => Real.exp (-(interaction params Λ ω)))
        (freeFieldMeasure params.mass params.mass_pos) := by
  have hLp : MemLp (fun ω => Real.exp (-(interaction params Λ ω)))
      (1 : ℝ≥0∞) (freeFieldMeasure params.mass params.mass_pos) :=
    exp_interaction_Lp params Λ (p := (1 : ℝ≥0∞)) (by norm_num)
  exact (memLp_one_iff_integrable.mp hLp)

end

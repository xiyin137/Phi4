/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.Interaction.Part3

/-!
# Analytic Inputs for the Interaction Integrability

This file provides the analytic estimates that feed into the Part2/Part3 machinery to
close `gap_hasExpInteractionLp`. The main results are:

1. **Measurability** of `interactionCutoff` and `interaction` as functions of ω
2. **L² integrability** of `interactionCutoff` (from Gaussian moment bounds)
3. **L² convergence** of the UV cutoff to the limiting interaction
4. **Exponential moment bounds** (Nelson hypercontractivity estimates)

## Strategy

The measurability chain uses:
- `configuration_eval_measurable` from gaussian-field (ω ↦ ω(f) is measurable)
- `stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable` (joint measurability)
- `StronglyMeasurable.integral_prod_right` (parametric integral measurability)

The L² bounds use Gaussian moment computations:
- E[:φ_κ⁴:²] = 24 c_κ⁴ + 36 c_κ⁴ + 9 c_κ⁴ = ... (Wick theorem for eighth moment)
- These are finite for each κ since c_κ < ∞

## References

* [Glimm-Jaffe] Sections 8.5-8.6
* Nelson's hypercontractivity [Nelson 1973]
-/

noncomputable section

open MeasureTheory GaussianField
open scoped ENNReal NNReal

/-! ## Frontier: UV mollifier continuity in spacetime

The UV mollifier δ_{κ,x} varies continuously in x in the Schwartz topology.
This is because translation is a continuous operation on S(ℝ²). -/

/-- The UV mollifier is continuous as a function of the spacetime point in the
    Schwartz topology: x ↦ uvMollifier κ x is continuous as Spacetime2D → TestFun2D.
    This holds because translation is continuous in the Schwartz topology. -/
theorem gap_uvMollifier_continuous (κ : UVCutoff) :
    Continuous (fun x : Spacetime2D => uvMollifier κ x) := by
  sorry

/-! ## Measurability of field evaluations and Wick products -/

/-- The raw field evaluation is strongly measurable in ω for each fixed spacetime point. -/
theorem rawFieldEval_stronglyMeasurable (mass : ℝ) (κ : UVCutoff) (x : Spacetime2D) :
    @StronglyMeasurable FieldConfig2D ℝ _ instMeasurableSpaceConfiguration
      (fun ω => rawFieldEval mass κ ω x) :=
  (continuous_id.stronglyMeasurable).comp_measurable
    (configuration_eval_measurable (uvMollifier κ x))

/-- Wick power is strongly measurable in ω for each fixed spacetime point. -/
theorem wickPower_stronglyMeasurable (n : ℕ) (mass : ℝ) (κ : UVCutoff) (x : Spacetime2D) :
    @StronglyMeasurable FieldConfig2D ℝ _ instMeasurableSpaceConfiguration
      (fun ω => wickPower n mass κ ω x) := by
  unfold wickPower rawFieldEval
  exact (wickMonomial_continuous n (regularizedPointCovariance mass κ)).stronglyMeasurable.comp_measurable
    (configuration_eval_measurable (uvMollifier κ x))

/-- The raw field evaluation is continuous in x for each fixed ω.
    This follows from continuity of the UV mollifier and continuity of ω. -/
theorem rawFieldEval_continuous_in_x (mass : ℝ) (κ : UVCutoff) (ω : FieldConfig2D) :
    Continuous (fun x : Spacetime2D => rawFieldEval mass κ ω x) := by
  unfold rawFieldEval
  exact ω.continuous.comp (gap_uvMollifier_continuous κ)

/-- Wick power is continuous in x for each fixed ω. -/
theorem wickPower_continuous_in_x (n : ℕ) (mass : ℝ) (κ : UVCutoff) (ω : FieldConfig2D) :
    Continuous (fun x : Spacetime2D => wickPower n mass κ ω x) := by
  unfold wickPower rawFieldEval
  exact (wickMonomial_continuous n _).comp (ω.continuous.comp (gap_uvMollifier_continuous κ))

/-- Joint strong measurability of the Wick power on FieldConfig2D × Spacetime2D.
    Uses the Carathéodory condition: measurable in ω for each x, continuous in x for each ω.
    Requires SecondCountableTopology on Spacetime2D (which holds for ℝ²). -/
theorem wickPower_stronglyMeasurable_uncurry (n : ℕ) (mass : ℝ) (κ : UVCutoff) :
    @StronglyMeasurable (FieldConfig2D × Spacetime2D) ℝ _
      (instMeasurableSpaceConfiguration.prod inferInstance)
      (Function.uncurry (fun ω x => wickPower n mass κ ω x)) := by
  -- Use stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
  -- with ι = Spacetime2D, α = FieldConfig2D, u x ω = wickPower n mass κ ω x
  -- giving uncurry u : Spacetime2D × FieldConfig2D → ℝ, then swap
  letI : MeasurableSpace FieldConfig2D := instMeasurableSpaceConfiguration
  have hjoint :=
    @stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
      FieldConfig2D ℝ Spacetime2D
      _ _ _ _ _ _ _ instMeasurableSpaceConfiguration
      (fun x ω => wickPower n mass κ ω x)
      (fun ω => wickPower_continuous_in_x n mass κ ω)
      (fun x => wickPower_stronglyMeasurable n mass κ x)
  -- hjoint : StronglyMeasurable (uncurry (fun x ω => ...)) on (Spacetime2D × FieldConfig2D)
  -- Swap to get (FieldConfig2D × Spacetime2D)
  convert hjoint.comp_measurable measurable_swap using 1

/-! ## Measurability of the interaction -/

/-- The UV-cutoff interaction is strongly measurable as a function of ω. -/
theorem interactionCutoff_stronglyMeasurable (params : Phi4Params) (Λ : Rectangle) (κ : UVCutoff) :
    @StronglyMeasurable FieldConfig2D ℝ _ instMeasurableSpaceConfiguration
      (interactionCutoff params Λ κ) := by
  unfold interactionCutoff
  -- params.coupling * ∫ x in Λ.toSet, wickPower 4 params.mass κ ω x
  apply StronglyMeasurable.const_mul
  -- Need: ω ↦ ∫ x in Λ.toSet, wickPower 4 mass κ ω x is strongly measurable
  -- Use StronglyMeasurable.integral_prod_right with the joint measurability
  -- The set integral ∫ x in S, f x = ∫ x, S.indicator f x
  show StronglyMeasurable fun ω =>
    ∫ x in Λ.toSet, wickPower 4 params.mass κ ω x
  -- Rewrite set integral as full integral with indicator
  have h_eq : (fun ω => ∫ x in Λ.toSet, wickPower 4 params.mass κ ω x) =
      (fun ω => ∫ x, Λ.toSet.indicator (fun x => wickPower 4 params.mass κ ω x) x) := by
    ext ω; rw [integral_indicator Λ.toSet_measurableSet]
  rw [h_eq]
  -- Now use StronglyMeasurable.integral_prod_right
  -- We need StronglyMeasurable (uncurry (fun ω x => indicator ...)) on (FieldConfig2D × Spacetime2D)
  apply StronglyMeasurable.integral_prod_right
  -- Need: StronglyMeasurable (fun (ω, x) => Λ.toSet.indicator (wickPower 4 mass κ ω ·) x)
  -- This is StronglyMeasurable (fun (ω, x) => indicator Λ.toSet (wickPower 4 mass κ ω ·) x)
  -- = StronglyMeasurable of indicator of a jointly measurable function over a measurable set
  apply StronglyMeasurable.indicator
  · -- The function (ω, x) ↦ wickPower 4 mass κ ω x is jointly strongly measurable
    exact wickPower_stronglyMeasurable_uncurry 4 params.mass κ
  · -- {(ω, x) | x ∈ Λ.toSet} is measurable in the product
    exact Λ.toSet_measurableSet.preimage measurable_snd

/-- The UV-cutoff interaction is AEStronglyMeasurable under the free field measure. -/
theorem interactionCutoff_aestronglyMeasurable (params : Phi4Params) (Λ : Rectangle)
    (κ : UVCutoff) :
    AEStronglyMeasurable (interactionCutoff params Λ κ)
      (freeFieldMeasure params.mass params.mass_pos) :=
  (interactionCutoff_stronglyMeasurable params Λ κ).aestronglyMeasurable

/-! ## L² integrability of the cutoff interaction

The cutoff interaction V_{Λ,κ} = λ ∫_Λ :φ_κ(x)⁴: dx is a quadratic form in the
Gaussian field pairings ω(δ_{κ,x}). For fixed κ, all moments are finite because:
- Each ω(δ_{κ,x}) is Gaussian with variance c_κ
- :φ_κ(x)⁴: is a polynomial in ω(δ_{κ,x})
- Polynomials of Gaussians have all moments finite
- The integral over Λ (bounded region) preserves integrability
-/

/-- The cutoff interaction is square-integrable under the free field measure.
    This is a consequence of the Gaussian structure: V_{Λ,κ} is an integral
    of polynomials of Gaussian random variables over a bounded region. -/
theorem gap_interactionCutoff_sq_integrable (params : Phi4Params) (Λ : Rectangle)
    (κ : UVCutoff) :
    Integrable (fun ω => (interactionCutoff params Λ κ ω) ^ 2)
      (freeFieldMeasure params.mass params.mass_pos) := by
  sorry

/-- The cutoff interaction is in L² under the free field measure. -/
theorem interactionCutoff_memLp_two (params : Phi4Params) (Λ : Rectangle)
    (κ : UVCutoff) :
    MemLp (interactionCutoff params Λ κ) 2
      (freeFieldMeasure params.mass params.mass_pos) :=
  (memLp_two_iff_integrable_sq
    (interactionCutoff_aestronglyMeasurable params Λ κ)).2
    (gap_interactionCutoff_sq_integrable params Λ κ)

/-! ## UV convergence -/

/-- L² convergence of the cutoff interaction to the limiting interaction. -/
theorem gap_interactionCutoff_L2_convergence (params : Phi4Params) (Λ : Rectangle) :
    Filter.Tendsto
      (fun (κ : ℝ) => if h : 0 < κ then
        ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
          ∂(freeFieldMeasure params.mass params.mass_pos)
        else 0)
      Filter.atTop
      (nhds 0) := by
  sorry

/-- A.e. convergence of the cutoff interaction to the limiting interaction. -/
theorem gap_interactionCutoff_ae_convergence (params : Phi4Params) (Λ : Rectangle) :
    ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
      Filter.Tendsto
        (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
        Filter.atTop
        (nhds (interaction params Λ ω)) := by
  sorry

/-- Measurability of the limiting interaction. -/
theorem gap_interaction_aestronglyMeasurable (params : Phi4Params) (Λ : Rectangle) :
    AEStronglyMeasurable (interaction params Λ)
      (freeFieldMeasure params.mass params.mass_pos) := by
  sorry

/-- Square integrability of the limiting interaction. -/
theorem gap_interaction_sq_integrable (params : Phi4Params) (Λ : Rectangle) :
    Integrable (fun ω => (interaction params Λ ω) ^ 2)
      (freeFieldMeasure params.mass params.mass_pos) := by
  sorry

/-! ## Nelson hypercontractivity estimate

The key analytic estimate: geometric decay of shifted-index exponential moments
E[exp(θ |V_{Λ,κ_{n+1}}|)] ≤ D · r^n for some θ > 0, D > 0, 0 ≤ r < 1.

This follows from Nelson's hypercontractivity inequality for Wiener chaos:
for X in the n-th chaos, ‖X‖_p ≤ (p-1)^{n/2} ‖X‖_2.
Applied to :φ⁴: (4th chaos), this gives exponential moment control. -/

/-- Nelson estimate: geometric decay of shifted-index absolute exponential moments
    of the cutoff interaction. This is the Chapter 8 core analytic input. -/
theorem gap_exponential_moment_geometric_bound (params : Phi4Params) (Λ : Rectangle) :
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
          ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D * r ^ n) := by
  sorry

/-! ## Closing gap_hasExpInteractionLp

We now wire the analytic inputs through the Part2/Part3 endpoint theorems to close
the main WP1 blocker. -/

/-- The Chapter 8 interaction integrability core: exp(-V_Λ) ∈ Lᵖ for all p < ∞.
    Proved by combining the analytic inputs through the Fatou/Borel-Cantelli
    infrastructure in Part2/Part3. -/
theorem hasExpInteractionLp_of_analytic_inputs (params : Phi4Params) :
    HasExpInteractionLp params := by
  intro Λ _ _
  exact
    exp_interaction_Lp_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_moment_abs_geometric_bound
      (params := params) (Λ := Λ)
      (hcutoff_meas := fun Λ κ => interactionCutoff_aestronglyMeasurable params Λ κ)
      (hcutoff_sq := fun Λ κ => gap_interactionCutoff_sq_integrable params Λ κ)
      (hcutoff_conv := fun Λ => gap_interactionCutoff_L2_convergence params Λ)
      (hcutoff_ae := fun Λ => gap_interactionCutoff_ae_convergence params Λ)
      (hinteraction_meas := fun Λ => gap_interaction_aestronglyMeasurable params Λ)
      (hinteraction_sq := fun Λ => gap_interaction_sq_integrable params Λ)
      (hmomAbs := gap_exponential_moment_geometric_bound params Λ)

end

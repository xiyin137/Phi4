/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.Interaction.Part3
import Mathlib.Analysis.Convex.Integral

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

open MeasureTheory GaussianField Filter
open scoped ENNReal NNReal

/-! ## Frontier: UV mollifier continuity in spacetime

The UV mollifier δ_{κ,x} varies continuously in x in the Schwartz topology.
This is because translation is a continuous operation on S(ℝ²). -/

/-- The ContDiffBump underlying the UV mollifier. -/
private def uvBump (κ : UVCutoff) (x : Spacetime2D) : ContDiffBump x :=
  ⟨(2 * κ.κ)⁻¹, κ.κ⁻¹, inv_pos.mpr (mul_pos two_pos κ.hκ),
   by rw [inv_lt_inv₀ (mul_pos two_pos κ.hκ) κ.hκ]; linarith [κ.hκ]⟩

/-- The iterated derivative of the base mollifier vanishes outside the support ball. -/
private lemma iteratedFDeriv_uvMollifier_zero_outside (κ : UVCutoff) (n : ℕ)
    (z : Spacetime2D) (hz : ‖z‖ > κ.κ⁻¹) :
    iteratedFDeriv ℝ n (⇑(uvMollifier κ 0)) z = 0 := by
  apply image_eq_zero_of_notMem_tsupport; intro hmem
  have : z ∈ Metric.closedBall (0 : Spacetime2D) κ.κ⁻¹ :=
    (tsupport_iteratedFDeriv_subset (𝕜 := ℝ) n).trans (by
      rw [show (⇑(uvMollifier κ 0) : Spacetime2D → ℝ) = ⇑(uvBump κ 0) from rfl]
      exact (uvBump κ 0).tsupport_eq.le) hmem
  rw [Metric.mem_closedBall, dist_zero_right] at this; linarith

/-- Translation identity for the iterated derivative of the UV mollifier. -/
private lemma iteratedFDeriv_uvMollifier_translate (κ : UVCutoff) (n : ℕ) (a y : Spacetime2D) :
    iteratedFDeriv ℝ n (⇑(uvMollifier κ a)) y =
    iteratedFDeriv ℝ n (⇑(uvMollifier κ 0)) (y - a) := by
  show iteratedFDeriv ℝ n (uvMollifier κ a).toFun y =
    iteratedFDeriv ℝ n (uvMollifier κ 0).toFun (y - a)
  have : (uvMollifier κ a).toFun = fun z => (uvMollifier κ 0).toFun (z - a) := by
    ext z; show (uvMollifier κ a) z = (uvMollifier κ 0) (z - a)
    simp [uvMollifier, ContDiffBump.toFun, sub_eq_add_neg]
  rw [this, iteratedFDeriv_comp_sub]

/-- The iterated derivative of a difference of Schwartz maps equals the difference
    of iterated derivatives. -/
private lemma iteratedFDeriv_sub_schwartz (f g : SchwartzMap Spacetime2D ℝ)
    (n : ℕ) (y : Spacetime2D) :
    iteratedFDeriv ℝ n (⇑(f - g)) y =
    iteratedFDeriv ℝ n (⇑f) y - iteratedFDeriv ℝ n (⇑g) y := by
  show iteratedFDeriv ℝ n (f - g).toFun y =
    iteratedFDeriv ℝ n f.toFun y - iteratedFDeriv ℝ n g.toFun y
  have hfeq : (f - g).toFun = fun z => f.toFun z + (-g.toFun z) := by
    ext z; show f z - g z = f z + (-(g z)); ring
  rw [hfeq, iteratedFDeriv_add_apply'
    (f.smooth'.of_le (by exact_mod_cast le_top)).contDiffAt
    (g.smooth'.of_le (by exact_mod_cast le_top)).contDiffAt.neg]
  have : (fun x => -g.toFun x) = -g.toFun := by ext; simp
  rw [this, iteratedFDeriv_neg_apply]; abel

/-- The UV mollifier is continuous as a function of the spacetime point in the
    Schwartz topology: x ↦ uvMollifier κ x is continuous as Spacetime2D → TestFun2D.
    This holds because translation is continuous in the Schwartz topology. -/
theorem gap_uvMollifier_continuous (κ : UVCutoff) :
    Continuous (fun x : Spacetime2D => uvMollifier κ x) := by
  rw [continuous_iff_continuousAt]; intro x₀
  rw [ContinuousAt, (schwartz_withSeminorms ℝ Spacetime2D ℝ).tendsto_nhds]
  intro ⟨k, n⟩ ε hε
  simp only [SchwartzMap.schwartzSeminormFamily_apply]
  set R := κ.κ⁻¹
  have hR_pos : 0 < R := inv_pos.mpr κ.hκ
  -- The base iterated derivative is uniformly continuous (compactly supported + smooth)
  have hD_uc : UniformContinuous
      (iteratedFDeriv ℝ n (⇑(uvMollifier κ 0) : Spacetime2D → ℝ)) := by
    apply HasCompactSupport.uniformContinuous_of_continuous
    · rw [show (⇑(uvMollifier κ 0) : Spacetime2D → ℝ) = ⇑(uvBump κ 0) from rfl]
      exact (uvBump κ 0).hasCompactSupport.iteratedFDeriv n
    · exact ((uvMollifier κ 0).smooth').continuous_iteratedFDeriv (by exact_mod_cast le_top)
  -- Bound: on the support region, ‖y‖ ≤ ‖x₀‖ + R + 1
  have hbase_nn : 0 ≤ ‖x₀‖ + R + 1 := by linarith [norm_nonneg x₀]
  set B := (‖x₀‖ + R + 1) ^ k
  have hB_nn : 0 ≤ B := pow_nonneg hbase_nn k
  set ε' := ε / (B + 1)
  have hε'_pos : 0 < ε' := div_pos hε (by linarith)
  -- From uniform continuity, get δ₁ controlling the derivative difference
  obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := (Metric.uniformContinuous_iff.mp hD_uc) ε' hε'_pos
  rw [Metric.eventually_nhds_iff]
  refine ⟨min δ₁ 1, lt_min hδ₁_pos one_pos, fun x hx => ?_⟩
  have hx1 : dist x x₀ < 1 := lt_of_lt_of_le hx (min_le_right _ _)
  have hxδ₁ : dist x x₀ < δ₁ := lt_of_lt_of_le hx (min_le_left _ _)
  -- Bound the Schwartz seminorm by B * ε' using seminorm_le_bound, then show B * ε' < ε
  apply lt_of_le_of_lt
    (SchwartzMap.seminorm_le_bound ℝ k n _ (mul_nonneg hB_nn (le_of_lt hε'_pos)) _)
  · calc B * ε' = ε * B / (B + 1) := by ring
      _ < ε * (B + 1) / (B + 1) := div_lt_div_of_pos_right
          (mul_lt_mul_of_pos_left (by linarith) hε) (by linarith)
      _ = ε := by field_simp
  · -- Pointwise bound: ‖y‖^k * ‖iteratedFDeriv ℝ n (uvMol x - uvMol x₀) y‖ ≤ B * ε'
    intro y
    rw [iteratedFDeriv_sub_schwartz,
        iteratedFDeriv_uvMollifier_translate κ n x y,
        iteratedFDeriv_uvMollifier_translate κ n x₀ y]
    by_cases hy : dist y x₀ ≤ R + 1
    · -- y in support region: ‖y‖ bounded, use uniform continuity
      have hy_norm : ‖y‖ ≤ ‖x₀‖ + R + 1 := by
        have h := norm_add_le (y - x₀) x₀; rw [sub_add_cancel] at h
        linarith [show ‖y - x₀‖ ≤ R + 1 from by rwa [← dist_eq_norm]]
      have hD_close : ‖iteratedFDeriv ℝ n (⇑(uvMollifier κ 0)) (y - x) -
          iteratedFDeriv ℝ n (⇑(uvMollifier κ 0)) (y - x₀)‖ < ε' := by
        rw [← dist_eq_norm]; apply hδ₁
        rw [dist_eq_norm, show (y - x) - (y - x₀) = x₀ - x from by abel, norm_sub_rev]
        exact dist_eq_norm x x₀ ▸ hxδ₁
      calc ‖y‖ ^ k * ‖iteratedFDeriv ℝ n (⇑(uvMollifier κ 0)) (y - x) -
              iteratedFDeriv ℝ n (⇑(uvMollifier κ 0)) (y - x₀)‖
          ≤ B * ‖iteratedFDeriv ℝ n (⇑(uvMollifier κ 0)) (y - x) -
              iteratedFDeriv ℝ n (⇑(uvMollifier κ 0)) (y - x₀)‖ :=
            mul_le_mul_of_nonneg_right
              (pow_le_pow_left₀ (norm_nonneg _) hy_norm k) (norm_nonneg _)
        _ ≤ B * ε' := mul_le_mul_of_nonneg_left (le_of_lt hD_close) hB_nn
    · -- y outside support region: both D values vanish
      push_neg at hy
      have hy_x : ‖y - x‖ > R := by
        calc R < dist y x₀ - dist x x₀ := by linarith
          _ ≤ dist y x := by linarith [dist_triangle y x x₀]
          _ = ‖y - x‖ := dist_eq_norm y x
      have hy_x₀ : ‖y - x₀‖ > R := by rw [← dist_eq_norm]; linarith
      rw [iteratedFDeriv_uvMollifier_zero_outside κ n _ hy_x,
          iteratedFDeriv_uvMollifier_zero_outside κ n _ hy_x₀,
          sub_self, norm_zero, mul_zero]
      exact mul_nonneg hB_nn (le_of_lt hε'_pos)

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

The proof uses:
1. wickPower_memLp: for each x, the Wick power is in L^p(dμ) for all finite p
2. Cauchy-Schwarz: (∫_Λ f dx)² ≤ vol(Λ) * ∫_Λ f² dx
3. Fubini-Tonelli: E[∫_Λ f² dx] = ∫_Λ E[f²] dx for f² ≥ 0
4. Translation invariance: E[:φ_κ(x)⁴:²] is constant in x
-/

/-- For each fixed spacetime point, the square of the Wick power is integrable
    under the free field measure. Immediate from `wickPower_memLp` with p = 2. -/
theorem wickPower_sq_integrable (mass : ℝ) (hmass : 0 < mass) (κ : UVCutoff)
    (x : Spacetime2D) :
    Integrable (fun ω => (wickPower 4 mass κ ω x) ^ 2)
      (freeFieldMeasure mass hmass) :=
  (wickPower_memLp 4 mass hmass κ x (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).integrable_sq

/-- Cauchy-Schwarz for set integrals over a finite-measure set:
    (∫ x in S, f x)² ≤ (μ S).toReal * ∫ x in S, f x ^ 2.
    This is Jensen's inequality for the convex function (·)². -/
theorem sq_setIntegral_le_volume_mul_setIntegral_sq {f : Spacetime2D → ℝ}
    (S : Set Spacetime2D) (_hS : MeasurableSet S)
    (hfint : Integrable f (MeasureTheory.volume.restrict S))
    (hf2int : Integrable (fun x => f x ^ 2) (MeasureTheory.volume.restrict S))
    (hvol : MeasureTheory.volume S ≠ ⊤) :
    (∫ x in S, f x) ^ 2 ≤
      (MeasureTheory.volume S).toReal * ∫ x in S, f x ^ 2 := by
  -- If vol(S) = 0, both sides are 0
  by_cases hvol0 : MeasureTheory.volume S = 0
  · have hrestr : MeasureTheory.volume.restrict S = 0 :=
      MeasureTheory.Measure.restrict_eq_zero.mpr hvol0
    simp [hrestr]
  -- vol(S) > 0: use Jensen's inequality for (·)²
  have hconv : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2) :=
    Even.convexOn_pow ⟨1, rfl⟩
  have hjensen := ConvexOn.map_set_average_le hconv
    (continuous_pow 2 |>.continuousOn) isClosed_univ
    hvol0 hvol (by simp) hfint hf2int
  -- hjensen : (⨍ x in S, f x) ^ 2 ≤ ⨍ x in S, f x ^ 2
  rw [MeasureTheory.setAverage_eq, MeasureTheory.setAverage_eq] at hjensen
  simp only [smul_eq_mul, MeasureTheory.Measure.real] at hjensen
  rw [mul_pow] at hjensen
  -- hjensen : V⁻¹ ^ 2 * (∫_S f) ^ 2 ≤ V⁻¹ * ∫_S f²  where V = (volume S).toReal
  have hVpos : 0 < (MeasureTheory.volume S).toReal := ENNReal.toReal_pos hvol0 hvol
  -- Multiply both sides by V² to clear denominators
  have h1 := mul_le_mul_of_nonneg_left hjensen
    (sq_nonneg (MeasureTheory.volume S).toReal)
  set V := (MeasureTheory.volume S).toReal with hV_def
  have hVne : V ≠ 0 := hVpos.ne'
  have hVinv_pos : 0 < V⁻¹ := inv_pos.mpr hVpos
  -- hjensen: V⁻¹ ^ 2 * (∫ f)² ≤ V⁻¹ * ∫ f²
  -- Rewrite V⁻¹ ^ 2 = V⁻¹ * V⁻¹ and reassociate
  rw [sq, mul_assoc] at hjensen
  -- hjensen: V⁻¹ * (V⁻¹ * (∫ f)²) ≤ V⁻¹ * ∫ f²
  -- Cancel V⁻¹ from both sides (V⁻¹ > 0)
  have h1 := le_of_mul_le_mul_left hjensen hVinv_pos
  -- h1: V⁻¹ * (∫ f)² ≤ ∫ f²
  -- Multiply both sides by V (> 0)
  have h2 := mul_le_mul_of_nonneg_left h1 hVpos.le
  -- h2: V * (V⁻¹ * (∫ f)²) ≤ V * ∫ f²
  rw [← mul_assoc, mul_inv_cancel₀ hVne, one_mul] at h2
  -- h2: (∫ f)² ≤ V * ∫ f²
  exact h2

/-- Moment recursion: E[(ω f)^{n+2}] = (n+1) · Cov(f,f) · E[(ω f)^n].
    Re-derived from `wick_recursive` (the public Gaussian field API). -/
private theorem moment_recursion_ai (mass : ℝ) (hmass : 0 < mass) (f : TestFun2D) (n : ℕ) :
    ∫ ω : FieldConfig2D, (ω f) ^ (n + 2) ∂(freeFieldMeasure mass hmass) =
    (↑(n + 1) : ℝ) * GaussianField.covariance (freeCovarianceCLM mass hmass) f f *
      ∫ ω : FieldConfig2D, (ω f) ^ n ∂(freeFieldMeasure mass hmass) := by
  set T := freeCovarianceCLM mass hmass; set c := GaussianField.covariance T f f
  simp_rw [show ∀ ω : FieldConfig2D, (ω f) ^ (n + 2) = ω f * ∏ i : Fin (n + 1),
    ω ((fun _ : Fin (n + 1) => f) i) from fun ω => by
      rw [show (∏ i : Fin (n + 1), ω ((fun _ : Fin (n + 1) => f) i)) = (ω f) ^ (n + 1) from
        Fin.prod_const (n + 1) (ω f)]; ring]
  change ∫ ω, ω f * ∏ i, ω ((fun _ => f) i) ∂(measure T) = _
  rw [wick_recursive T n f (fun _ => f)]
  simp_rw [show @inner ℝ ell2' _ (T f) (T f) = c from rfl, Fin.prod_const]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  change _ = (↑(n + 1) : ℝ) * c * ∫ ω : Configuration TestFun2D, (ω f) ^ n ∂(measure T)
  push_cast; ring

/-- Powers of Gaussian pairings are integrable (from `product_integrable`). -/
private theorem power_integrable_ai (mass : ℝ) (hmass : 0 < mass) (f : TestFun2D) (n : ℕ) :
    Integrable (fun ω : FieldConfig2D => (ω f) ^ n) (freeFieldMeasure mass hmass) := by
  set T := freeCovarianceCLM mass hmass
  simp_rw [show ∀ ω : FieldConfig2D, (ω f) ^ n = ∏ i : Fin n, ω ((fun _ => f) i) from
    fun ω => (Fin.prod_const n (ω f)).symm]
  change Integrable (fun ω => ∏ i : Fin n, ω ((fun _ => f) i)) (measure T)
  exact product_integrable T n (fun _ => f)

/-- The L² expectation E[(wickPower 4 mass κ · y)²] is uniformly bounded on compact sets.
    The proof computes the integral explicitly as a polynomial in σ²(y) = Cov(δ_{κ,y}, δ_{κ,y})
    using the Gaussian moment recursion, then uses continuity of σ²(y) (from
    gap_uvMollifier_continuous) to bound the polynomial on the compact set. -/
theorem wickPower_sq_expectation_bounded_on_compact (mass : ℝ) (hmass : 0 < mass)
    (κ : UVCutoff) (K : Set Spacetime2D) (hK : IsCompact K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y ∈ K,
      ∫ ω, (wickPower 4 mass κ ω y) ^ 2
        ∂(freeFieldMeasure mass hmass) ≤ M := by
  set T := freeCovarianceCLM mass hmass
  set μ := freeFieldMeasure mass hmass
  set c₀ := regularizedPointCovariance mass κ
  set covFun : Spacetime2D → ℝ := fun y =>
    GaussianField.covariance T (uvMollifier κ y) (uvMollifier κ y)
  -- The polynomial Q(t) = 105t⁴ - 180c₀t³ + 126c₀²t² - 36c₀³t + 9c₀⁴
  -- equals E[(He₄(X;c₀))²] when X ~ N(0,t)
  set Q : ℝ → ℝ := fun t => 105 * t ^ 4 - 180 * c₀ * t ^ 3 + 126 * c₀ ^ 2 * t ^ 2 -
    36 * c₀ ^ 3 * t + 9 * c₀ ^ 4
  -- The integral equals Q(covFun(y)) by explicit Gaussian moment computation
  have hintegral_eq : ∀ y, ∫ ω, (wickPower 4 mass κ ω y) ^ 2 ∂μ = Q (covFun y) := by
    intro y
    set f := uvMollifier κ y
    show ∫ ω, (wickMonomial 4 c₀ (ω f)) ^ 2 ∂μ = Q (covFun y)
    simp only [wickMonomial_four]
    simp_rw [show ∀ ω : FieldConfig2D,
      ((ω f) ^ 4 - 6 * c₀ * (ω f) ^ 2 + 3 * c₀ ^ 2) ^ 2 =
      (ω f) ^ 8 + ((-12) * c₀ * (ω f) ^ 6 + (42 * c₀ ^ 2 * (ω f) ^ 4 +
      ((-36) * c₀ ^ 3 * (ω f) ^ 2 + 9 * c₀ ^ 4))) from fun ω => by ring]
    have hi8 : Integrable (fun ω : FieldConfig2D => (ω f) ^ 8) μ :=
      power_integrable_ai mass hmass f 8
    have hi6 : Integrable (fun ω : FieldConfig2D => (ω f) ^ 6) μ :=
      power_integrable_ai mass hmass f 6
    have hi4 : Integrable (fun ω : FieldConfig2D => (ω f) ^ 4) μ :=
      power_integrable_ai mass hmass f 4
    have hi2 : Integrable (fun ω : FieldConfig2D => (ω f) ^ 2) μ :=
      power_integrable_ai mass hmass f 2
    -- Split integral into sum (use exact/have instead of rw to handle Pi.add matching)
    have s1 : ∫ ω, ((ω f) ^ 8 + (-12 * c₀ * (ω f) ^ 6 + (42 * c₀ ^ 2 * (ω f) ^ 4 +
      (-36 * c₀ ^ 3 * (ω f) ^ 2 + 9 * c₀ ^ 4)))) ∂μ =
      ∫ ω, (ω f) ^ 8 ∂μ + ∫ ω, (-12 * c₀ * (ω f) ^ 6 + (42 * c₀ ^ 2 * (ω f) ^ 4 +
      (-36 * c₀ ^ 3 * (ω f) ^ 2 + 9 * c₀ ^ 4))) ∂μ :=
      integral_add hi8 ((hi6.const_mul _).add ((hi4.const_mul _).add
        ((hi2.const_mul _).add (integrable_const _))))
    have s2 : ∫ ω, (-12 * c₀ * (ω f) ^ 6 + (42 * c₀ ^ 2 * (ω f) ^ 4 +
      (-36 * c₀ ^ 3 * (ω f) ^ 2 + 9 * c₀ ^ 4))) ∂μ =
      ∫ ω, (-12 * c₀ * (ω f) ^ 6) ∂μ + ∫ ω, (42 * c₀ ^ 2 * (ω f) ^ 4 +
      (-36 * c₀ ^ 3 * (ω f) ^ 2 + 9 * c₀ ^ 4)) ∂μ :=
      integral_add (hi6.const_mul _) ((hi4.const_mul _).add
        ((hi2.const_mul _).add (integrable_const _)))
    have s3 : ∫ ω, (42 * c₀ ^ 2 * (ω f) ^ 4 +
      (-36 * c₀ ^ 3 * (ω f) ^ 2 + 9 * c₀ ^ 4)) ∂μ =
      ∫ ω, (42 * c₀ ^ 2 * (ω f) ^ 4) ∂μ +
      ∫ ω, (-36 * c₀ ^ 3 * (ω f) ^ 2 + 9 * c₀ ^ 4) ∂μ :=
      integral_add (hi4.const_mul _) ((hi2.const_mul _).add (integrable_const _))
    have s4 : ∫ ω, (-36 * c₀ ^ 3 * (ω f) ^ 2 + 9 * c₀ ^ 4) ∂μ =
      ∫ ω, (-36 * c₀ ^ 3 * (ω f) ^ 2) ∂μ + ∫ _, 9 * c₀ ^ 4 ∂μ :=
      integral_add (hi2.const_mul _) (integrable_const _)
    rw [s1, s2, s3, s4,
        integral_const_mul, integral_const_mul, integral_const_mul, integral_const]
    -- Gaussian even moments: E[X²]=σ², E[X⁴]=3σ⁴, E[X⁶]=15σ⁶, E[X⁸]=105σ⁸
    have h2 : ∫ ω : FieldConfig2D, (ω f) ^ 2 ∂μ = covFun y := by
      simp_rw [show ∀ ω : FieldConfig2D, (ω f) ^ 2 = ω f * ω f from fun ω => sq (ω f)]
      exact cross_moment_eq_covariance T f f
    have h4 : ∫ ω : FieldConfig2D, (ω f) ^ 4 ∂μ = 3 * (covFun y) ^ 2 := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, moment_recursion_ai mass hmass f 2, h2]
      push_cast; ring
    have h6 : ∫ ω : FieldConfig2D, (ω f) ^ 6 ∂μ = 15 * (covFun y) ^ 3 := by
      rw [show (6 : ℕ) = 4 + 2 from rfl, moment_recursion_ai mass hmass f 4, h4]
      push_cast; ring
    have h8 : ∫ ω : FieldConfig2D, (ω f) ^ 8 ∂μ = 105 * (covFun y) ^ 4 := by
      rw [show (8 : ℕ) = 6 + 2 from rfl, moment_recursion_ai mass hmass f 6, h6]
      push_cast; ring
    rw [h8, h6, h4, h2]; simp [Measure.real, measure_univ]; ring
  -- The integral is nonneg (integral of a square)
  have hintegral_nonneg : ∀ y, 0 ≤ ∫ ω, (wickPower 4 mass κ ω y) ^ 2 ∂μ :=
    fun y => integral_nonneg (fun ω => sq_nonneg _)
  -- covFun is continuous (gap_uvMollifier_continuous + T CLM + inner continuous)
  have hcov_cont : Continuous covFun := by
    have h1 := gap_uvMollifier_continuous κ
    have h2 : Continuous (fun y => T (uvMollifier κ y)) := T.continuous.comp h1
    exact continuous_inner.comp (h2.prodMk h2)
  -- Q ∘ covFun is continuous
  have hF_cont : Continuous (fun y => Q (covFun y)) :=
    (by continuity : Continuous Q).comp hcov_cont
  -- On compact K, Q(covFun(y)) is bounded above
  by_cases hKne : K.Nonempty
  · obtain ⟨y₀, hy₀, hmax⟩ := hK.exists_isMaxOn hKne hF_cont.continuousOn
    refine ⟨Q (covFun y₀), ?_, fun y hy => ?_⟩
    · rw [← hintegral_eq]; exact hintegral_nonneg y₀
    · rw [hintegral_eq]; exact hmax hy
  · exact ⟨0, le_rfl, fun y hy => absurd hy
      (Set.not_nonempty_iff_eq_empty.mp hKne ▸ Set.notMem_empty y)⟩

/-- The function (ω, x) ↦ (wickPower 4 mass κ ω x)² is integrable on the product
    of the free field measure with Lebesgue measure restricted to Λ.
    Uses Fubini's criterion (integrable_prod_iff'): integrable in ω for each y,
    and the ω-integral is integrable in y over Λ. -/
theorem wickPower_sq_integrable_prod (params : Phi4Params) (Λ : Rectangle)
    (κ : UVCutoff) :
    Integrable
      (fun p : FieldConfig2D × Spacetime2D =>
        (wickPower 4 params.mass κ p.1 p.2) ^ 2)
      ((freeFieldMeasure params.mass params.mass_pos).prod
        (MeasureTheory.volume.restrict Λ.toSet)) := by
  let μ := freeFieldMeasure params.mass params.mass_pos
  let ν := MeasureTheory.volume.restrict Λ.toSet
  letI : IsProbabilityMeasure μ := freeFieldMeasure_isProbability params.mass params.mass_pos
  -- Joint AEStronglyMeasurable for wickPower² on the product
  have hmeas : AEStronglyMeasurable
      (fun p : FieldConfig2D × Spacetime2D => (wickPower 4 params.mass κ p.1 p.2) ^ 2)
      (μ.prod ν) := by
    exact ((wickPower_stronglyMeasurable_uncurry 4 params.mass κ).pow 2).aestronglyMeasurable
  rw [MeasureTheory.integrable_prod_iff' hmeas]
  constructor
  · -- (1) For a.e. y ∂ν, ω ↦ wickPower(ω,y)² is integrable ∂μ
    -- This follows from wickPower_sq_integrable for every y
    filter_upwards with y
    exact wickPower_sq_integrable params.mass params.mass_pos κ y
  · -- (2) y ↦ ∫ ‖wickPower(ω,y)²‖ dμ(ω) is integrable ∂ν
    -- Since (wickPower ω y)² ≥ 0, ‖·‖ = id, so this is y ↦ ∫ (wickPower ω y)² dμ
    -- The function is bounded on compact Λ (uniform L² bound) and ν is finite
    obtain ⟨M, hMnn, hM⟩ := wickPower_sq_expectation_bounded_on_compact
      params.mass params.mass_pos κ Λ.toSet Λ.toSet_isCompact
    -- Show the norm simplifies since squares are nonneg
    have hnorm_eq : (fun y => ∫ ω, ‖(wickPower 4 params.mass κ ω y) ^ 2‖ ∂μ) =
        (fun y => ∫ ω, (wickPower 4 params.mass κ ω y) ^ 2 ∂μ) := by
      ext y; congr 1; ext ω; exact Real.norm_of_nonneg (sq_nonneg _)
    rw [hnorm_eq]
    -- Measurability of the partial integral
    have hsm : AEStronglyMeasurable
        (fun y => ∫ ω, (wickPower 4 params.mass κ ω y) ^ 2 ∂μ) ν :=
      (StronglyMeasurable.integral_prod_left
        ((wickPower_stronglyMeasurable_uncurry 4 params.mass κ).pow 2)).aestronglyMeasurable
    -- ν is a finite measure (Λ compact)
    have hν_fin : ν Set.univ < ⊤ := by
      rw [MeasureTheory.Measure.restrict_apply_univ]
      exact Λ.toSet_isCompact.measure_lt_top
    -- Use Integrable.mono with constant function M (integrable on finite measure)
    haveI : IsFiniteMeasure ν := ⟨hν_fin⟩
    have hconst : Integrable (fun _ : Spacetime2D => M) ν := integrable_const M
    apply hconst.mono hsm
    -- a.e. bound: on ν = vol.restrict Λ, a.e. y ∈ Λ.toSet
    filter_upwards [MeasureTheory.ae_restrict_mem Λ.toSet_measurableSet] with y hy
    rw [Real.norm_of_nonneg (integral_nonneg (fun ω => sq_nonneg _)),
        Real.norm_of_nonneg hMnn]
    exact hM y hy

/-- The cutoff interaction is square-integrable under the free field measure.
    This is a consequence of the Gaussian structure: V_{Λ,κ} is an integral
    of polynomials of Gaussian random variables over a bounded region. -/
theorem gap_interactionCutoff_sq_integrable (params : Phi4Params) (Λ : Rectangle)
    (κ : UVCutoff) :
    Integrable (fun ω => (interactionCutoff params Λ κ ω) ^ 2)
      (freeFieldMeasure params.mass params.mass_pos) := by
  -- interactionCutoff ω = coupling * ∫_Λ wickPower 4 mass κ ω x dx
  -- (interactionCutoff ω)² = coupling² * (∫_Λ w dx)²
  -- By Cauchy-Schwarz: (∫_Λ w dx)² ≤ vol(Λ) * ∫_Λ w² dx
  -- So it suffices to show ω ↦ ∫_Λ w² dx is integrable (Fubini)
  let μ := freeFieldMeasure params.mass params.mass_pos
  let ν := MeasureTheory.volume.restrict Λ.toSet
  unfold interactionCutoff
  -- (coupling * ∫_Λ w dx)² = coupling² * (∫_Λ w dx)²
  have h_eq : (fun ω => (params.coupling * ∫ x in Λ.toSet, wickPower 4 params.mass κ ω x) ^ 2) =
      (fun ω => params.coupling ^ 2 * (∫ x in Λ.toSet, wickPower 4 params.mass κ ω x) ^ 2) := by
    ext ω; ring
  rw [h_eq]
  apply Integrable.const_mul
  -- Need: ω ↦ (∫_Λ w dx)² is integrable ∂μ
  -- By Fubini (wickPower_sq_integrable_prod): (ω,x) ↦ w² is integrable on μ × ν
  -- By integral_prod_left: ω ↦ ∫ w² dν is integrable ∂μ
  -- By Cauchy-Schwarz: (∫_Λ w dx)² ≤ vol(Λ) * ∫_Λ w² dx, so ‖(∫_Λ w)²‖ ≤ ‖vol * ∫ w²‖
  have hprod := wickPower_sq_integrable_prod params Λ κ
  have hfub : Integrable (fun ω => ∫ x, (wickPower 4 params.mass κ ω x) ^ 2 ∂ν) μ :=
    hprod.integral_prod_left
  -- The dominating function is vol(Λ) * ∫ w² dν, which is integrable
  have hdom : Integrable (fun ω => (MeasureTheory.volume Λ.toSet).toReal *
      ∫ x, (wickPower 4 params.mass κ ω x) ^ 2 ∂ν) μ := hfub.const_mul _
  apply hdom.mono
  · -- AEStronglyMeasurable for (∫_Λ w)²
    -- The spatial integral is strongly measurable (same as interactionCutoff proof)
    have hmeas_int : @StronglyMeasurable FieldConfig2D ℝ _ instMeasurableSpaceConfiguration
        (fun ω => ∫ x in Λ.toSet, wickPower 4 params.mass κ ω x) := by
      show StronglyMeasurable fun ω => ∫ x in Λ.toSet, wickPower 4 params.mass κ ω x
      have h_eq : (fun ω => ∫ x in Λ.toSet, wickPower 4 params.mass κ ω x) =
          (fun ω => ∫ x, Λ.toSet.indicator (fun x => wickPower 4 params.mass κ ω x) x) := by
        ext ω; rw [integral_indicator Λ.toSet_measurableSet]
      rw [h_eq]
      apply StronglyMeasurable.integral_prod_right
      apply StronglyMeasurable.indicator
      · exact wickPower_stronglyMeasurable_uncurry 4 params.mass κ
      · exact Λ.toSet_measurableSet.preimage measurable_snd
    exact (StronglyMeasurable.pow hmeas_int 2).aestronglyMeasurable
  · -- Pointwise bound: ‖(∫_Λ w)²‖ ≤ ‖vol * ∫ w²‖ a.e.
    filter_upwards with ω
    -- LHS: ‖(∫_Λ w)²‖ = (∫_Λ w)² (since squares are nonneg)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    -- RHS: ‖vol * ∫ w²‖ = vol * ∫ w² (both nonneg)
    rw [Real.norm_of_nonneg (mul_nonneg ENNReal.toReal_nonneg
      (integral_nonneg (fun x => sq_nonneg _)))]
    -- Now: (∫_Λ w)² ≤ vol * ∫_Λ w² by Cauchy-Schwarz
    -- Convert ∫ ... ∂ν to ∫ ... in Λ.toSet
    change (∫ x in Λ.toSet, wickPower 4 params.mass κ ω x) ^ 2 ≤
      (MeasureTheory.volume Λ.toSet).toReal *
      ∫ x in Λ.toSet, wickPower 4 params.mass κ ω x ^ 2
    -- Apply Cauchy-Schwarz (Jensen)
    apply sq_setIntegral_le_volume_mul_setIntegral_sq
    · exact Λ.toSet_measurableSet
    · -- wickPower is integrable on Λ (continuous on compact, hence integrable)
      exact (wickPower_continuous_in_x 4 params.mass κ ω).continuousOn.integrableOn_compact
        Λ.toSet_isCompact
    · -- wickPower² is integrable on Λ
      exact ((wickPower_continuous_in_x 4 params.mass κ ω).pow 2).continuousOn.integrableOn_compact
        Λ.toSet_isCompact
    · exact Λ.toSet_volume_ne_top

/-- The cutoff interaction is in L² under the free field measure. -/
theorem interactionCutoff_memLp_two (params : Phi4Params) (Λ : Rectangle)
    (κ : UVCutoff) :
    MemLp (interactionCutoff params Λ κ) 2
      (freeFieldMeasure params.mass params.mass_pos) :=
  (memLp_two_iff_integrable_sq
    (interactionCutoff_aestronglyMeasurable params Λ κ)).2
    (gap_interactionCutoff_sq_integrable params Λ κ)

/-! ## UV convergence -/

/-- Sequence-level a.e. convergence: V_{κ_n} → V a.e. along the canonical cutoff
    sequence `standardUVCutoffSeq n = ⟨n+1, ...⟩`.

    This is the natural first target: the Fatou bridge only needs discrete
    convergence, and `interaction` is defined as `Filter.limsup` of the sequence,
    so convergence holds whenever the limsup equals the limit.

    Strategy: Since `interaction` = `Filter.limsup` of `interactionCutoff(κ_n)`,
    convergence of the full sequence holds iff limsup = liminf a.e. The natural
    route is to show the Wick-ordered cutoff interactions are eventually monotone
    (after UV renormalization), so limsup = liminf = lim. Note: L² convergence
    only gives a.e. convergence along a *subsequence*, not the full sequence. -/
theorem gap_interactionCutoff_standardSeq_ae_convergence
    (params : Phi4Params) (Λ : Rectangle) :
    ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
      Filter.Tendsto
        (fun n : ℕ => interactionCutoff params Λ (standardUVCutoffSeq n) ω)
        Filter.atTop
        (nhds (interaction params Λ ω)) := by
  sorry

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

/-- A.e. convergence of the cutoff interaction to the limiting interaction
    (continuous-parameter version). Stronger than sequence-level, not needed
    for the main WP1 endpoint. -/
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
  -- interaction = Filter.limsup of interactionCutoff (standardUVCutoffSeq n)
  -- Each cutoff is StronglyMeasurable → Measurable
  -- Measurable.limsup → interaction is Measurable → AEStronglyMeasurable
  unfold interaction
  apply Measurable.aestronglyMeasurable
  apply Measurable.limsup
  intro n
  exact (interactionCutoff_stronglyMeasurable params Λ (standardUVCutoffSeq n)).measurable

/-- Square integrability of the limiting interaction.
    Strategy: from L² convergence (Vκ → V in L²), the limit V ∈ L² by completeness.
    Concretely: V² ≤ 2(V - Vκ)² + 2Vκ² pointwise, so ∫V² ≤ 2∫(V-Vκ)² + 2∫Vκ² < ∞. -/
theorem gap_interaction_sq_integrable (params : Phi4Params) (Λ : Rectangle) :
    Integrable (fun ω => (interaction params Λ ω) ^ 2)
      (freeFieldMeasure params.mass params.mass_pos) := by
  sorry

/-! ## Nelson's uniform exponential moment bound (Simon Theorem V.14)

The core analytic estimate: for any p > 0, the *negative* exponential moments
E[exp(-p V_{Λ,κ})] are bounded uniformly in the UV cutoff κ.

**Statement-level corrections:**
1. The original statement (`gap_exponential_moment_geometric_bound`) asked for geometric
   decay E[exp(θ|V|)] ≤ D·rⁿ with r < 1. This is mathematically impossible: under a
   probability measure, exp(θ|V|) ≥ 1 always. See `test/proofideas_interaction_next_steps.lean`.
2. The intermediate statement (`gap_exp_interaction_uniform_bound` with |V|) asked for
   E[exp(p|V_κ|)] ≤ C uniformly. This is also false: V_κ is in the 4th Wiener chaos,
   so tails decay like exp(-c√t), making E[exp(p|V_κ|)] = ∞ for any p > 0.

The correct statement uses *negative* exponential moments E[exp(-pV_κ)]. The key insight
is that V_κ = λ∫:φ⁴:dx is NOT symmetric: :φ⁴:_{c_κ} ≥ -6c_κ² pointwise (bounded below),
but unbounded above (heavily right-skewed). So exp(-pV_κ) ≤ exp(6pλc_κ²|Λ|) is finite
for each κ, and Nelson's more sophisticated argument (using hypercontractivity + covariance
splitting) shows the bound is uniform in κ.

Reference: Simon, "The P(φ)₂ Euclidean Field Theory", Theorem V.14;
Glimm-Jaffe, "Quantum Physics", Chapter 8.6. -/

/-- Uniform bound on negative exponential moments of the cutoff interaction:
    for any p > 0, E[exp(-p V_{Λ,κ})] ≤ C(Λ,p) uniformly in κ.

    This is Nelson's bound — the Chapter 8 core analytic input for stability.
    The proof uses Nelson hypercontractivity + covariance-splitting to show that
    the right-skewed distribution of V_κ suppresses exp(-pV_κ) uniformly. -/
theorem gap_exp_neg_interaction_uniform_bound (params : Phi4Params) (Λ : Rectangle) :
    ∀ p : ℝ, 0 < p →
      ∃ C : ℝ, 0 < C ∧ ∀ κ : UVCutoff,
        Integrable
          (fun ω : FieldConfig2D =>
            Real.exp (-(p * interactionCutoff params Λ κ ω)))
          (freeFieldMeasure params.mass params.mass_pos) ∧
        ∫ ω : FieldConfig2D,
          Real.exp (-(p * interactionCutoff params Λ κ ω))
          ∂(freeFieldMeasure params.mass params.mass_pos) ≤ C := by
  sorry

/-! ## Closing gap_hasExpInteractionLp

The WP1 endpoint `HasExpInteractionLp` (i.e., exp(-V_Λ) ∈ Lᵖ for all finite p)
is proved by Fatou's lemma applied to the cutoff approximations:

1. From `gap_interactionCutoff_ae_convergence`: V_{Λ,κ} → V_Λ a.e., hence
   exp(-p V_{Λ,κ}) → exp(-p V_Λ) a.e. (continuity of exp).
2. From `gap_exp_neg_interaction_uniform_bound`: E[exp(-p V_{Λ,κ})] ≤ C
   uniformly in κ (Nelson's bound).
3. Fatou: ∫⁻ exp(-pV_Λ) ≤ liminf ∫⁻ exp(-pV_{Λ,κ_n}) ≤ C < ⊤.
4. AEStronglyMeasurable + finite eLpNorm → MemLp.

This route bypasses Part2/Part3 entirely and needs only two analytic inputs:
`gap_interactionCutoff_ae_convergence` and `gap_exp_neg_interaction_uniform_bound`. -/

/-- The Chapter 8 interaction integrability core: exp(-V_Λ) ∈ Lᵖ for all p < ∞.
    Proved by Fatou's lemma: Nelson's uniform negative exponential moment bounds
    on the cutoff interactions plus a.e. convergence give MemLp for the limit. -/
theorem hasExpInteractionLp_of_analytic_inputs (params : Phi4Params) :
    HasExpInteractionLp params := by
  intro Λ (p : ℝ≥0∞) hp_ne_top
  set μ := freeFieldMeasure params.mass params.mass_pos
  -- Case p = 0: MemLp f 0 μ ↔ AEStronglyMeasurable f μ
  by_cases hp0 : p = 0
  · rw [hp0, memLp_zero_iff_aestronglyMeasurable]
    exact ((gap_interaction_aestronglyMeasurable params Λ).aemeasurable.neg.exp).aestronglyMeasurable
  -- Case 0 < p < ⊤: use the Fatou bridge from Part1Core
  have hp_toReal_pos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_ne_top
  -- a.e. convergence along standardUVCutoffSeq(n), then shift to (n+1)
  have hae_discrete :
      ∀ᵐ ω ∂μ, Filter.Tendsto
        (fun n : ℕ => interactionCutoff params Λ (standardUVCutoffSeq n) ω)
        Filter.atTop (nhds (interaction params Λ ω)) :=
    gap_interactionCutoff_standardSeq_ae_convergence params Λ
  have hae_shifted :
      ∀ᵐ ω ∂μ, Filter.Tendsto
        (fun n : ℕ => interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)
        Filter.atTop (nhds (interaction params Λ ω)) := by
    filter_upwards [hae_discrete] with ω hω
    exact hω.comp (Filter.tendsto_add_atTop_nat 1)
  -- Cutoff measurability for the shifted sequence
  have hcutoff_meas : ∀ n : ℕ,
      AEStronglyMeasurable
        (fun ω : FieldConfig2D => interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)
        μ := by
    intro n
    exact (interactionCutoff_stronglyMeasurable params Λ (standardUVCutoffSeq (n + 1))).aestronglyMeasurable
  -- Uniform lintegral bound from gap_exp_neg_interaction_uniform_bound (Nelson's bound)
  have hbound :
      ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
        ∀ n : ℕ,
          ∫⁻ ω,
              ENNReal.ofReal
                (Real.exp (-(p.toReal * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)))
            ∂μ ≤ C := by
    obtain ⟨D, hD_pos, hD_bound⟩ :=
      gap_exp_neg_interaction_uniform_bound params Λ p.toReal hp_toReal_pos
    apply uniform_lintegral_bound_of_standardSeq_succ_uniform_integral_bound params Λ p.toReal
    exact ⟨D, fun n => (hD_bound (standardUVCutoffSeq (n + 1))).1,
           fun n => (hD_bound (standardUVCutoffSeq (n + 1))).2⟩
  -- Apply the Fatou bridge
  exact memLp_exp_neg_interaction_of_standardSeq_succ_tendsto_ae_of_uniform_lintegral_bound
    params Λ hp0 hp_ne_top hae_shifted hcutoff_meas hbound

end

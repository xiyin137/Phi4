/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.Interaction.Part3
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Topology.Algebra.InfiniteSum.Real

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

/-- Under a probability measure, ∫|f| ≤ √(∫ f²) (Jensen / Cauchy-Schwarz). -/
private theorem integral_abs_le_sqrt_integral_sq {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Integrable f μ) (hf2 : Integrable (fun ω => f ω ^ 2) μ) :
    ∫ ω, |f ω| ∂μ ≤ Real.sqrt (∫ ω, f ω ^ 2 ∂μ) := by
  have h_abs_int := hf.abs
  have h_jensen : (∫ ω, |f ω| ∂μ) ^ 2 ≤ ∫ ω, |f ω| ^ 2 ∂μ := by
    have hconv : ConvexOn ℝ (Set.Ici (0:ℝ)) (fun x : ℝ => x ^ 2) := convexOn_pow 2
    have hcont : ContinuousOn (fun x : ℝ => x ^ 2) (Set.Ici (0:ℝ)) :=
      (continuous_pow 2).continuousOn
    have hclosed : IsClosed (Set.Ici (0:ℝ)) := isClosed_Ici
    have hae : ∀ᵐ x ∂μ, (fun ω => |f ω|) x ∈ Set.Ici (0:ℝ) := by
      filter_upwards with x; exact Set.mem_Ici.mpr (abs_nonneg _)
    have hcomp : Integrable ((fun x : ℝ => x ^ 2) ∘ (fun ω => |f ω|)) μ := by
      show Integrable (fun ω => |f ω| ^ 2) μ
      convert hf2 using 1; ext ω; exact sq_abs (f ω)
    exact hconv.map_integral_le hcont hclosed hae h_abs_int hcomp
  rw [show ∫ ω, |f ω| ^ 2 ∂μ = ∫ ω, f ω ^ 2 ∂μ from by
    congr 1; ext ω; exact sq_abs (f ω)] at h_jensen
  exact Real.le_sqrt_of_sq_le h_jensen

/-- Hölder bridge for the shell `A`-term: `L⁴ × L⁴ → L²` on products.
This is the right reusable norm-level statement after
`wickPower_four_step_decomposition`; the shell estimate for the nonlinear part
reduces to separate `L⁴` bounds on the raw increment and the cubic polynomial
factor. -/
private theorem lpNorm_mul_le_lpNorm_four_mul_four
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ}
    (hf : MemLp f 4 μ) (hg : MemLp g 4 μ) :
    lpNorm (fun x => f x * g x) 2 μ ≤ lpNorm f 4 μ * lpNorm g 4 μ := by
  haveI : ENNReal.HolderTriple (4 : ℝ≥0∞) 4 2 := by
    simpa [show (4 : ℝ≥0∞) = 2 * (2 : ℝ≥0∞) by norm_num] using
      (holderTriple_double (2 : ℝ≥0∞))
  have h_e : eLpNorm (fun x => f x * g x) 2 μ ≤ eLpNorm f 4 μ * eLpNorm g 4 μ := by
    have hmul : ∀ x, ‖(fun x1 x2 => x1 * x2) (f x) (g x)‖ ≤ (1 : ℝ) * ‖f x‖ * ‖g x‖ := by
      intro x
      calc
        ‖(fun x1 x2 => x1 * x2) (f x) (g x)‖ ≤ ‖f x‖ * ‖g x‖ := norm_mul_le (f x) (g x)
        _ = (1 : ℝ) * ‖f x‖ * ‖g x‖ := by ring
    simpa using
      (eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm (μ := μ)
        (p := (4 : ℝ≥0∞)) (q := (4 : ℝ≥0∞)) (r := (2 : ℝ≥0∞))
        hf.1 hg.1 (· * ·) 1 (.of_forall hmul))
  have hfg : MemLp (fun x => f x * g x) (2 : ℝ≥0∞) μ := by
    simpa using (hg.mul' hf)
  rw [← MeasureTheory.toReal_eLpNorm hfg.aestronglyMeasurable]
  rw [← MeasureTheory.toReal_eLpNorm hf.aestronglyMeasurable]
  rw [← MeasureTheory.toReal_eLpNorm hg.aestronglyMeasurable]
  have h_toReal :=
    ENNReal.toReal_mono (ENNReal.mul_ne_top hf.eLpNorm_lt_top.ne hg.eLpNorm_lt_top.ne) h_e
  simpa [ENNReal.toReal_mul] using h_toReal

/-- Exact `L⁴` norm of the raw shell increment. This converts the fourth-moment
identity from `WickProduct` into the norm-level statement needed by the shell
`A`-term estimate. -/
private theorem rawFieldEval_sub_lpNorm_four_eq
    (mass : ℝ) (hmass : 0 < mass) (κ₁ κ₂ : UVCutoff) (x : Spacetime2D) :
    lpNorm (fun ω : FieldConfig2D => rawFieldEval mass κ₂ ω x - rawFieldEval mass κ₁ ω x)
      4 (freeFieldMeasure mass hmass)
    = (3 * (GaussianField.covariance (freeCovarianceCLM mass hmass)
        (uvMollifier κ₂ x - uvMollifier κ₁ x)
        (uvMollifier κ₂ x - uvMollifier κ₁ x)) ^ 2) ^ ((1 : ℝ) / 4) := by
  let μ := freeFieldMeasure mass hmass
  let Δ : FieldConfig2D → ℝ := fun ω => rawFieldEval mass κ₂ ω x - rawFieldEval mass κ₁ ω x
  have hmem : MemLp Δ 4 μ := by
    simpa [Δ, rawFieldEval_sub] using
      (GaussianField.pairing_memLp (freeCovarianceCLM mass hmass)
        (uvMollifier κ₂ x - uvMollifier κ₁ x) (4 : ℝ≥0))
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) ENNReal.ofNat_ne_top
    hmem.aestronglyMeasurable]
  norm_num
  have habs4 : ∀ z : ℝ, |z| ^ 4 = z ^ 4 := by
    intro z
    calc
      |z| ^ 4 = (|z| ^ 2) ^ 2 := by ring
      _ = (z ^ 2) ^ 2 := by rw [sq_abs]
      _ = z ^ 4 := by ring
  have habs : ∫ ω : FieldConfig2D, |Δ ω| ^ 4 ∂μ = ∫ ω : FieldConfig2D, (Δ ω) ^ 4 ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards with ω
    exact habs4 (Δ ω)
  rw [habs]
  have hfour := rawFieldEval_sub_fourth_expectation mass hmass κ₁ κ₂ x
  exact congrArg (fun t : ℝ => t ^ ((1 : ℝ) / 4)) hfour

/-- Exact `L⁴` norm of a single regularized raw field in terms of its covariance.
This is the basic Gaussian moment formula needed to make the cubic-factor bound
quantitative. -/
private theorem rawFieldEval_lpNorm_four_eq
    (mass : ℝ) (hmass : 0 < mass) (κ : UVCutoff) (x : Spacetime2D) :
    lpNorm (fun ω : FieldConfig2D => rawFieldEval mass κ ω x)
      4 (freeFieldMeasure mass hmass)
    = (3 * (GaussianField.covariance (freeCovarianceCLM mass hmass)
        (uvMollifier κ x) (uvMollifier κ x)) ^ 2) ^ ((1 : ℝ) / 4) := by
  let μ := freeFieldMeasure mass hmass
  let X : FieldConfig2D → ℝ := fun ω => rawFieldEval mass κ ω x
  let f : TestFun2D := uvMollifier κ x
  let σ : ℝ := GaussianField.covariance (freeCovarianceCLM mass hmass) f f
  have hX_4 : MemLp X 4 μ := by
    simpa [X, f] using
      (GaussianField.pairing_memLp (freeCovarianceCLM mass hmass) f (4 : ℝ≥0))
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) ENNReal.ofNat_ne_top
    hX_4.aestronglyMeasurable]
  norm_num
  have habs4 : ∀ z : ℝ, |z| ^ 4 = z ^ 4 := by
    intro z
    calc
      |z| ^ 4 = (|z| ^ 2) ^ 2 := by ring
      _ = (z ^ 2) ^ 2 := by rw [sq_abs]
      _ = z ^ 4 := by ring
  have habs : ∫ ω : FieldConfig2D, |X ω| ^ 4 ∂μ = ∫ ω : FieldConfig2D, (X ω) ^ 4 ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards with ω
    exact habs4 (X ω)
  rw [habs]
  have h2 : ∫ ω : FieldConfig2D, (ω f) ^ 2 ∂μ = σ := by
    simp_rw [show ∀ ω : FieldConfig2D, (ω f) ^ 2 = ω f * ω f from fun ω => sq (ω f)]
    simpa [GaussianField.covariance, σ] using
      cross_moment_eq_covariance (freeCovarianceCLM mass hmass) f f
  have h4 : ∫ ω : FieldConfig2D, (ω f) ^ 4 ∂μ = 3 * σ ^ 2 := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, moment_recursion_ai mass hmass f 2, h2]
    simp [σ]
    ring
  simpa [X, f, σ] using congrArg (fun t : ℝ => t ^ ((1 : ℝ) / 4)) h4

/-- Exact `L⁴` norm of the cubic absolute-value factor `|X|^3` for a Gaussian
raw field `X = rawFieldEval mass κ · x`. This packages the twelfth Gaussian
moment into the norm form needed by `cubic_factor_lpNorm_four_le`. -/
private theorem rawFieldEval_abs_cube_lpNorm_four_eq
    (mass : ℝ) (hmass : 0 < mass) (κ : UVCutoff) (x : Spacetime2D) :
    lpNorm (fun ω : FieldConfig2D => |rawFieldEval mass κ ω x| ^ (3 : ℝ))
      4 (freeFieldMeasure mass hmass)
    = (10395 * (GaussianField.covariance (freeCovarianceCLM mass hmass)
        (uvMollifier κ x) (uvMollifier κ x)) ^ 6) ^ ((1 : ℝ) / 4) := by
  let μ := freeFieldMeasure mass hmass
  let X : FieldConfig2D → ℝ := fun ω => rawFieldEval mass κ ω x
  let f : TestFun2D := uvMollifier κ x
  let σ : ℝ := GaussianField.covariance (freeCovarianceCLM mass hmass) f f
  have hX_12 : MemLp X 12 μ := by
    simpa [X, f] using
      (GaussianField.pairing_memLp (freeCovarianceCLM mass hmass) f (12 : ℝ≥0))
  have hcube' : MemLp (fun ω => |X ω| ^ (3 : ℝ)) ((12 : ℝ≥0∞) / 3) μ := by
    simpa [Real.norm_eq_abs] using hX_12.norm_rpow_div (3 : ℝ≥0∞)
  have hdiv12 : ((12 : ℝ≥0∞) / 3) = 4 := by
    change (((12 : NNReal) : ENNReal) / ((3 : NNReal) : ENNReal)) = ((4 : NNReal) : ENNReal)
    rw [← ENNReal.coe_div (p := (12 : NNReal)) (r := (3 : NNReal)) (by norm_num)]
    norm_num
  have hcube : MemLp (fun ω => |X ω| ^ (3 : ℝ)) 4 μ := by
    simpa [hdiv12] using hcube'
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) ENNReal.ofNat_ne_top
    hcube.aestronglyMeasurable]
  norm_num
  have hpow12 : ∀ z : ℝ, (|z| ^ (3 : ℕ)) ^ (4 : ℕ) = z ^ 12 := by
    intro z
    have hsq : |z| ^ 2 = z ^ 2 := by simp
    calc
      (|z| ^ (3 : ℕ)) ^ (4 : ℕ) = |z| ^ (12 : ℕ) := by
        rw [← pow_mul]
      _ = (|z| ^ 2) ^ 6 := by
        rw [show (12 : ℕ) = 2 * 6 by norm_num, pow_mul]
      _ = (z ^ 2) ^ 6 := by rw [hsq]
      _ = z ^ 12 := by
        rw [show (12 : ℕ) = 2 * 6 by norm_num, pow_mul]
  have habs : ∫ ω : FieldConfig2D, (|X ω| ^ (3 : ℕ)) ^ (4 : ℕ) ∂μ =
      ∫ ω : FieldConfig2D, (X ω) ^ 12 ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards with ω
    exact hpow12 (X ω)
  have habs_pow :
      (∫ ω : FieldConfig2D, (|X ω| ^ (3 : ℕ)) ^ (4 : ℕ) ∂μ) ^ ((1 : ℝ) / 4) =
      (∫ ω : FieldConfig2D, (X ω) ^ 12 ∂μ) ^ ((1 : ℝ) / 4) := by
    exact congrArg (fun t : ℝ => t ^ ((1 : ℝ) / 4)) habs
  have h2 : ∫ ω : FieldConfig2D, (ω f) ^ 2 ∂μ = σ := by
    simp_rw [show ∀ ω : FieldConfig2D, (ω f) ^ 2 = ω f * ω f from fun ω => sq (ω f)]
    simpa [GaussianField.covariance, σ] using
      cross_moment_eq_covariance (freeCovarianceCLM mass hmass) f f
  have h4 : ∫ ω : FieldConfig2D, (ω f) ^ 4 ∂μ = 3 * σ ^ 2 := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, moment_recursion_ai mass hmass f 2, h2]
    simp [σ]
    ring
  have h6 : ∫ ω : FieldConfig2D, (ω f) ^ 6 ∂μ = 15 * σ ^ 3 := by
    rw [show (6 : ℕ) = 4 + 2 from rfl, moment_recursion_ai mass hmass f 4, h4]
    simp [σ]
    ring
  have h8 : ∫ ω : FieldConfig2D, (ω f) ^ 8 ∂μ = 105 * σ ^ 4 := by
    rw [show (8 : ℕ) = 6 + 2 from rfl, moment_recursion_ai mass hmass f 6, h6]
    simp [σ]
    ring
  have h10 : ∫ ω : FieldConfig2D, (ω f) ^ 10 ∂μ = 945 * σ ^ 5 := by
    rw [show (10 : ℕ) = 8 + 2 from rfl, moment_recursion_ai mass hmass f 8, h8]
    simp [σ]
    ring
  have h12 : ∫ ω : FieldConfig2D, (ω f) ^ 12 ∂μ = 10395 * σ ^ 6 := by
    rw [show (12 : ℕ) = 10 + 2 from rfl, moment_recursion_ai mass hmass f 10, h10]
    simp [σ]
    ring
  have hX12 : ∫ ω : FieldConfig2D, (X ω) ^ 12 ∂μ = 10395 * σ ^ 6 := by
    simpa [X, f] using h12
  calc
    (∫ x : FieldConfig2D, (|X x| ^ (3 : ℕ)) ^ (4 : ℕ) ∂μ) ^ ((1 : ℝ) / 4) =
        (∫ ω : FieldConfig2D, (X ω) ^ 12 ∂μ) ^ ((1 : ℝ) / 4) := habs_pow
    _ = (10395 * σ ^ 6) ^ ((1 : ℝ) / 4) := by rw [hX12]
    _ = (10395 * (GaussianField.covariance (freeCovarianceCLM mass hmass) f f) ^ 6) ^
          ((1 : ℝ) / 4) := by simp [σ]
    _ = (10395 * (GaussianField.covariance (freeCovarianceCLM mass hmass)
          (uvMollifier κ x) (uvMollifier κ x)) ^ 6) ^ ((1 : ℝ) / 4) := by
          simp [f]

/-- Nonnegative mixed cubic terms are controlled by pure cubes.
This is the algebraic inequality behind the `L⁴` bound for the cubic factor in
`wickPower_four_step_decomposition`. -/
private theorem mixed_cubic_le_four_cubes (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3 ≤ 4 * (a ^ 3 + b ^ 3) := by
  nlinarith [ha, hb, sq_nonneg (a - b)]

/-- Pointwise domination of the cubic factor from
`wickPower_four_step_decomposition` by pure cubic and linear terms in the raw
fields. This avoids estimating the mixed monomials separately. -/
private theorem cubic_factor_pointwise_bound
    (x y c : ℝ) :
    |x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3 - 6 * c * (x + y)|
      ≤ 4 * (|x| ^ 3 + |y| ^ 3) + 6 * |c| * (|x| + |y|) := by
  have htri :
      |x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3 - 6 * c * (x + y)|
        ≤ |x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3| + |6 * c * (x + y)| := by
    simpa [sub_eq_add_neg] using
      (abs_add_le (x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3) (- (6 * c * (x + y))))
  have hpoly1 :
      |x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3|
        ≤ |x| ^ 3 + |x ^ 2 * y| + |x * y ^ 2| + |y| ^ 3 := by
    calc
      |x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3|
          = |(x ^ 3 + x ^ 2 * y) + (x * y ^ 2 + y ^ 3)| := by ring_nf
      _ ≤ |x ^ 3 + x ^ 2 * y| + |x * y ^ 2 + y ^ 3| := abs_add_le _ _
      _ ≤ (|x ^ 3| + |x ^ 2 * y|) + (|x * y ^ 2| + |y ^ 3|) := by
            gcongr <;> exact abs_add_le _ _
      _ = |x| ^ 3 + |x ^ 2 * y| + |x * y ^ 2| + |y| ^ 3 := by
            simp [abs_mul, abs_pow, add_assoc, add_left_comm, add_comm]
  have hpoly2 :
      |x| ^ 3 + |x ^ 2 * y| + |x * y ^ 2| + |y| ^ 3
        ≤ 4 * (|x| ^ 3 + |y| ^ 3) := by
    have hxy1 : |x ^ 2 * y| = |x| ^ 2 * |y| := by simp [abs_mul, abs_pow]
    have hxy2 : |x * y ^ 2| = |x| * |y| ^ 2 := by simp [abs_mul, abs_pow]
    rw [hxy1, hxy2]
    exact mixed_cubic_le_four_cubes |x| |y| (abs_nonneg _) (abs_nonneg _)
  have hlin : |6 * c * (x + y)| ≤ 6 * |c| * (|x| + |y|) := by
    calc
      |6 * c * (x + y)| = 6 * |c| * |x + y| := by
        simp [abs_mul, mul_left_comm, mul_comm]
      _ ≤ 6 * |c| * (|x| + |y|) := by
        gcongr
        exact abs_add_le _ _
  exact le_trans htri (by linarith [hpoly1.trans hpoly2, hlin])

/-- `L⁴` bound for the cubic factor in `wickPower_four_step_decomposition`.
This reduces the nonlinear shell term to raw-field `L¹²` and `L⁴` control,
which is available from Gaussian moments. -/
private theorem cubic_factor_lpNorm_four_le
    (mass : ℝ) (hmass : 0 < mass) (κ₁ κ₂ : UVCutoff) (x : Spacetime2D) :
    let μ := freeFieldMeasure mass hmass
    let X₁ : FieldConfig2D → ℝ := fun ω => rawFieldEval mass κ₁ ω x
    let X₂ : FieldConfig2D → ℝ := fun ω => rawFieldEval mass κ₂ ω x
    let c := regularizedPointCovariance mass κ₁
    let P : FieldConfig2D → ℝ := fun ω =>
      (X₂ ω) ^ 3 + (X₂ ω) ^ 2 * X₁ ω + X₂ ω * (X₁ ω) ^ 2 + (X₁ ω) ^ 3
        - 6 * c * (X₂ ω + X₁ ω)
    lpNorm P 4 μ ≤
      4 * (lpNorm (fun ω => |X₂ ω| ^ (3 : ℝ)) 4 μ + lpNorm (fun ω => |X₁ ω| ^ (3 : ℝ)) 4 μ) +
      6 * |c| * (lpNorm (fun ω => |X₂ ω|) 4 μ + lpNorm (fun ω => |X₁ ω|) 4 μ) := by
  dsimp
  let μ := freeFieldMeasure mass hmass
  let X₁ : FieldConfig2D → ℝ := fun ω => rawFieldEval mass κ₁ ω x
  let X₂ : FieldConfig2D → ℝ := fun ω => rawFieldEval mass κ₂ ω x
  let c := regularizedPointCovariance mass κ₁
  let P : FieldConfig2D → ℝ := fun ω =>
    (X₂ ω) ^ 3 + (X₂ ω) ^ 2 * X₁ ω + X₂ ω * (X₁ ω) ^ 2 + (X₁ ω) ^ 3
      - 6 * c * (X₂ ω + X₁ ω)
  let Q1 : FieldConfig2D → ℝ := fun ω =>
    4 * (|X₂ ω| ^ (3 : ℝ) + |X₁ ω| ^ (3 : ℝ))
  let Q2 : FieldConfig2D → ℝ := fun ω =>
    6 * |c| * (|X₂ ω| + |X₁ ω|)
  have hX1_12 : MemLp X₁ 12 μ := by
    simpa [X₁] using
      (GaussianField.pairing_memLp (freeCovarianceCLM mass hmass)
        (uvMollifier κ₁ x) (12 : ℝ≥0))
  have hX2_12 : MemLp X₂ 12 μ := by
    simpa [X₂] using
      (GaussianField.pairing_memLp (freeCovarianceCLM mass hmass)
        (uvMollifier κ₂ x) (12 : ℝ≥0))
  have hX1_4 : MemLp X₁ 4 μ := by
    simpa [X₁] using
      (GaussianField.pairing_memLp (freeCovarianceCLM mass hmass)
        (uvMollifier κ₁ x) (4 : ℝ≥0))
  have hX2_4 : MemLp X₂ 4 μ := by
    simpa [X₂] using
      (GaussianField.pairing_memLp (freeCovarianceCLM mass hmass)
        (uvMollifier κ₂ x) (4 : ℝ≥0))
  have hX1_cube' : MemLp (fun ω => |X₁ ω| ^ (3 : ℝ)) ((12 : ℝ≥0∞) / 3) μ := by
    simpa [Real.norm_eq_abs] using hX1_12.norm_rpow_div (3 : ℝ≥0∞)
  have hX2_cube' : MemLp (fun ω => |X₂ ω| ^ (3 : ℝ)) ((12 : ℝ≥0∞) / 3) μ := by
    simpa [Real.norm_eq_abs] using hX2_12.norm_rpow_div (3 : ℝ≥0∞)
  have hdiv12 : ((12 : ℝ≥0∞) / 3) = 4 := by
    change (((12 : NNReal) : ENNReal) / ((3 : NNReal) : ENNReal)) = ((4 : NNReal) : ENNReal)
    rw [← ENNReal.coe_div (p := (12 : NNReal)) (r := (3 : NNReal)) (by norm_num)]
    norm_num
  have hX1_cube : MemLp (fun ω => |X₁ ω| ^ (3 : ℝ)) 4 μ := by
    simpa [hdiv12] using hX1_cube'
  have hX2_cube : MemLp (fun ω => |X₂ ω| ^ (3 : ℝ)) 4 μ := by
    simpa [hdiv12] using hX2_cube'
  have hX1_abs' : MemLp (fun ω => |X₁ ω|) ((4 : ℝ≥0∞) / 1) μ := by
    simpa [Real.norm_eq_abs] using hX1_4.norm_rpow_div (1 : ℝ≥0∞)
  have hX2_abs' : MemLp (fun ω => |X₂ ω|) ((4 : ℝ≥0∞) / 1) μ := by
    simpa [Real.norm_eq_abs] using hX2_4.norm_rpow_div (1 : ℝ≥0∞)
  have hX1_abs : MemLp (fun ω => |X₁ ω|) 4 μ := by
    simpa using hX1_abs'
  have hX2_abs : MemLp (fun ω => |X₂ ω|) 4 μ := by
    simpa using hX2_abs'
  have hQ1_mem : MemLp Q1 4 μ := by
    simpa [Q1] using (hX2_cube.add hX1_cube).const_mul 4
  have hQ2_mem : MemLp Q2 4 μ := by
    simpa [Q2] using (hX2_abs.add hX1_abs).const_mul (6 * |c|)
  have hmono : lpNorm P 4 μ ≤ lpNorm (fun ω => Q1 ω + Q2 ω) 4 μ := by
    apply lpNorm_mono_real (g := fun ω => Q1 ω + Q2 ω)
    · exact hQ1_mem.add hQ2_mem
    · intro ω
      have hω := cubic_factor_pointwise_bound (X₂ ω) (X₁ ω) c
      simpa [P, Q1, Q2] using hω
  have hsum : lpNorm (fun ω => Q1 ω + Q2 ω) 4 μ ≤ lpNorm Q1 4 μ + lpNorm Q2 4 μ :=
    lpNorm_add_le hQ1_mem (g := Q2) (by norm_num : (1 : ℝ≥0∞) ≤ 4)
  have hQ1 : lpNorm Q1 4 μ =
      4 * lpNorm (fun ω => |X₂ ω| ^ (3 : ℝ) + |X₁ ω| ^ (3 : ℝ)) 4 μ := by
    simpa [Q1, Pi.smul_apply] using
      lpNorm_const_smul (4 : ℝ)
        (fun ω => |X₂ ω| ^ (3 : ℝ) + |X₁ ω| ^ (3 : ℝ)) μ (p := (4 : ℝ≥0∞))
  have hQ2 : lpNorm Q2 4 μ =
      (6 * |c|) * lpNorm (fun ω => |X₂ ω| + |X₁ ω|) 4 μ := by
    simpa [Q2, Pi.smul_apply] using
      lpNorm_const_smul (6 * |c| : ℝ) (fun ω => |X₂ ω| + |X₁ ω|) μ (p := (4 : ℝ≥0∞))
  have hcube_sum :
      lpNorm (fun ω => |X₂ ω| ^ (3 : ℝ) + |X₁ ω| ^ (3 : ℝ)) 4 μ ≤
        lpNorm (fun ω => |X₂ ω| ^ (3 : ℝ)) 4 μ + lpNorm (fun ω => |X₁ ω| ^ (3 : ℝ)) 4 μ :=
    lpNorm_add_le hX2_cube (g := fun ω => |X₁ ω| ^ (3 : ℝ)) (by norm_num : (1 : ℝ≥0∞) ≤ 4)
  have habs_sum :
      lpNorm (fun ω => |X₂ ω| + |X₁ ω|) 4 μ ≤
        lpNorm (fun ω => |X₂ ω|) 4 μ + lpNorm (fun ω => |X₁ ω|) 4 μ :=
    lpNorm_add_le hX2_abs (g := fun ω => |X₁ ω|) (by norm_num : (1 : ℝ≥0∞) ≤ 4)
  calc
    lpNorm P 4 μ ≤ lpNorm (fun ω => Q1 ω + Q2 ω) 4 μ := hmono
    _ ≤ lpNorm Q1 4 μ + lpNorm Q2 4 μ := hsum
    _ = 4 * lpNorm (fun ω => |X₂ ω| ^ (3 : ℝ) + |X₁ ω| ^ (3 : ℝ)) 4 μ +
          (6 * |c|) * lpNorm (fun ω => |X₂ ω| + |X₁ ω|) 4 μ := by
          rw [hQ1, hQ2]
    _ ≤ 4 * (lpNorm (fun ω => |X₂ ω| ^ (3 : ℝ)) 4 μ +
          lpNorm (fun ω => |X₁ ω| ^ (3 : ℝ)) 4 μ) +
          6 * |c| * (lpNorm (fun ω => |X₂ ω|) 4 μ +
            lpNorm (fun ω => |X₁ ω|) 4 μ) := by
          have h1 := mul_le_mul_of_nonneg_left hcube_sum (by positivity : 0 ≤ (4 : ℝ))
          have h2 := mul_le_mul_of_nonneg_left habs_sum (by positivity : 0 ≤ 6 * |c|)
          linarith

/-- Explicit covariance-form version of `cubic_factor_lpNorm_four_le`.
This packages the raw-field `L⁴` / `L¹²` norms into Gaussian moment formulas, so
the remaining work in the shell estimate is genuinely on the covariance side. -/
private theorem cubic_factor_lpNorm_four_le_covariance
    (mass : ℝ) (hmass : 0 < mass) (κ₁ κ₂ : UVCutoff) (x : Spacetime2D) :
    let μ := freeFieldMeasure mass hmass
    let X₁ : FieldConfig2D → ℝ := fun ω => rawFieldEval mass κ₁ ω x
    let X₂ : FieldConfig2D → ℝ := fun ω => rawFieldEval mass κ₂ ω x
    let c := regularizedPointCovariance mass κ₁
    let P : FieldConfig2D → ℝ := fun ω =>
      (X₂ ω) ^ 3 + (X₂ ω) ^ 2 * X₁ ω + X₂ ω * (X₁ ω) ^ 2 + (X₁ ω) ^ 3
        - 6 * c * (X₂ ω + X₁ ω)
    let σ₁ := GaussianField.covariance (freeCovarianceCLM mass hmass)
      (uvMollifier κ₁ x) (uvMollifier κ₁ x)
    let σ₂ := GaussianField.covariance (freeCovarianceCLM mass hmass)
      (uvMollifier κ₂ x) (uvMollifier κ₂ x)
    lpNorm P 4 μ ≤
      4 * ((10395 * σ₂ ^ 6) ^ ((1 : ℝ) / 4) + (10395 * σ₁ ^ 6) ^ ((1 : ℝ) / 4)) +
      6 * |c| * ((3 * σ₂ ^ 2) ^ ((1 : ℝ) / 4) + (3 * σ₁ ^ 2) ^ ((1 : ℝ) / 4)) := by
  let μ := freeFieldMeasure mass hmass
  let X₁ : FieldConfig2D → ℝ := fun ω => rawFieldEval mass κ₁ ω x
  let X₂ : FieldConfig2D → ℝ := fun ω => rawFieldEval mass κ₂ ω x
  let c := regularizedPointCovariance mass κ₁
  let P : FieldConfig2D → ℝ := fun ω =>
    (X₂ ω) ^ 3 + (X₂ ω) ^ 2 * X₁ ω + X₂ ω * (X₁ ω) ^ 2 + (X₁ ω) ^ 3
      - 6 * c * (X₂ ω + X₁ ω)
  let σ₁ := GaussianField.covariance (freeCovarianceCLM mass hmass)
    (uvMollifier κ₁ x) (uvMollifier κ₁ x)
  let σ₂ := GaussianField.covariance (freeCovarianceCLM mass hmass)
    (uvMollifier κ₂ x) (uvMollifier κ₂ x)
  have hbase :
      lpNorm P 4 μ ≤
        4 * (lpNorm (fun ω => |X₂ ω| ^ (3 : ℝ)) 4 μ +
          lpNorm (fun ω => |X₁ ω| ^ (3 : ℝ)) 4 μ) +
          6 * |c| * (lpNorm (fun ω => |X₂ ω|) 4 μ +
            lpNorm (fun ω => |X₁ ω|) 4 μ) := by
    simpa [μ, X₁, X₂, c, P] using cubic_factor_lpNorm_four_le mass hmass κ₁ κ₂ x
  have hcube₂ :
      lpNorm (fun ω => |X₂ ω| ^ (3 : ℝ)) 4 μ = (10395 * σ₂ ^ 6) ^ ((1 : ℝ) / 4) := by
    simpa [X₂, σ₂] using rawFieldEval_abs_cube_lpNorm_four_eq mass hmass κ₂ x
  have hcube₁ :
      lpNorm (fun ω => |X₁ ω| ^ (3 : ℝ)) 4 μ = (10395 * σ₁ ^ 6) ^ ((1 : ℝ) / 4) := by
    simpa [X₁, σ₁] using rawFieldEval_abs_cube_lpNorm_four_eq mass hmass κ₁ x
  have habs₂ :
      lpNorm (fun ω => |X₂ ω|) 4 μ = (3 * σ₂ ^ 2) ^ ((1 : ℝ) / 4) := by
    rw [lpNorm_fun_abs
      ((rawFieldEval_stronglyMeasurable mass κ₂ x).aestronglyMeasurable) (p := (4 : ℝ≥0∞))]
    simpa [X₂, σ₂] using rawFieldEval_lpNorm_four_eq mass hmass κ₂ x
  have habs₁ :
      lpNorm (fun ω => |X₁ ω|) 4 μ = (3 * σ₁ ^ 2) ^ ((1 : ℝ) / 4) := by
    rw [lpNorm_fun_abs
      ((rawFieldEval_stronglyMeasurable mass κ₁ x).aestronglyMeasurable) (p := (4 : ℝ≥0∞))]
    simpa [X₁, σ₁] using rawFieldEval_lpNorm_four_eq mass hmass κ₁ x
  calc
    lpNorm P 4 μ ≤
        4 * (lpNorm (fun ω => |X₂ ω| ^ (3 : ℝ)) 4 μ +
          lpNorm (fun ω => |X₁ ω| ^ (3 : ℝ)) 4 μ) +
          6 * |c| * (lpNorm (fun ω => |X₂ ω|) 4 μ +
            lpNorm (fun ω => |X₁ ω|) 4 μ) := hbase
    _ = 4 * ((10395 * σ₂ ^ 6) ^ ((1 : ℝ) / 4) + (10395 * σ₁ ^ 6) ^ ((1 : ℝ) / 4)) +
          6 * |c| * ((3 * σ₂ ^ 2) ^ ((1 : ℝ) / 4) + (3 * σ₁ ^ 2) ^ ((1 : ℝ) / 4)) := by
          rw [hcube₂, hcube₁, habs₂, habs₁]

/-- Norm-level bound for the nonlinear `A`-term in the quartic step
decomposition. After this theorem, the shell estimate for the nonlinear part is
reduced entirely to covariance quantities. -/
private theorem wickPower_four_step_A_term_lpNorm_two_le_covariance
    (mass : ℝ) (hmass : 0 < mass) (κ₁ κ₂ : UVCutoff) (x : Spacetime2D) :
    let μ := freeFieldMeasure mass hmass
    let X₁ : FieldConfig2D → ℝ := fun ω => rawFieldEval mass κ₁ ω x
    let X₂ : FieldConfig2D → ℝ := fun ω => rawFieldEval mass κ₂ ω x
    let Δ : FieldConfig2D → ℝ := fun ω => X₂ ω - X₁ ω
    let c := regularizedPointCovariance mass κ₁
    let P : FieldConfig2D → ℝ := fun ω =>
      (X₂ ω) ^ 3 + (X₂ ω) ^ 2 * X₁ ω + X₂ ω * (X₁ ω) ^ 2 + (X₁ ω) ^ 3
        - 6 * c * (X₂ ω + X₁ ω)
    let σ₁ := GaussianField.covariance (freeCovarianceCLM mass hmass)
      (uvMollifier κ₁ x) (uvMollifier κ₁ x)
    let σ₂ := GaussianField.covariance (freeCovarianceCLM mass hmass)
      (uvMollifier κ₂ x) (uvMollifier κ₂ x)
    let δσ := GaussianField.covariance (freeCovarianceCLM mass hmass)
      (uvMollifier κ₂ x - uvMollifier κ₁ x)
      (uvMollifier κ₂ x - uvMollifier κ₁ x)
    lpNorm (fun ω => Δ ω * P ω) 2 μ ≤
      (3 * δσ ^ 2) ^ ((1 : ℝ) / 4) *
        (4 * ((10395 * σ₂ ^ 6) ^ ((1 : ℝ) / 4) + (10395 * σ₁ ^ 6) ^ ((1 : ℝ) / 4)) +
          6 * |c| * ((3 * σ₂ ^ 2) ^ ((1 : ℝ) / 4) + (3 * σ₁ ^ 2) ^ ((1 : ℝ) / 4))) := by
  let μ := freeFieldMeasure mass hmass
  let X₁ : FieldConfig2D → ℝ := fun ω => rawFieldEval mass κ₁ ω x
  let X₂ : FieldConfig2D → ℝ := fun ω => rawFieldEval mass κ₂ ω x
  let Δ : FieldConfig2D → ℝ := fun ω => X₂ ω - X₁ ω
  let c := regularizedPointCovariance mass κ₁
  let P : FieldConfig2D → ℝ := fun ω =>
    (X₂ ω) ^ 3 + (X₂ ω) ^ 2 * X₁ ω + X₂ ω * (X₁ ω) ^ 2 + (X₁ ω) ^ 3
      - 6 * c * (X₂ ω + X₁ ω)
  let σ₁ := GaussianField.covariance (freeCovarianceCLM mass hmass)
    (uvMollifier κ₁ x) (uvMollifier κ₁ x)
  let σ₂ := GaussianField.covariance (freeCovarianceCLM mass hmass)
    (uvMollifier κ₂ x) (uvMollifier κ₂ x)
  let δσ := GaussianField.covariance (freeCovarianceCLM mass hmass)
    (uvMollifier κ₂ x - uvMollifier κ₁ x)
    (uvMollifier κ₂ x - uvMollifier κ₁ x)
  let Q1 : FieldConfig2D → ℝ := fun ω =>
    4 * (|X₂ ω| ^ (3 : ℝ) + |X₁ ω| ^ (3 : ℝ))
  let Q2 : FieldConfig2D → ℝ := fun ω =>
    6 * |c| * (|X₂ ω| + |X₁ ω|)
  let Q : FieldConfig2D → ℝ := fun ω => Q1 ω + Q2 ω
  have hΔ4 : MemLp Δ 4 μ := by
    simpa [Δ, X₁, X₂, rawFieldEval_sub] using
      (GaussianField.pairing_memLp (freeCovarianceCLM mass hmass)
        (uvMollifier κ₂ x - uvMollifier κ₁ x) (4 : ℝ≥0))
  have hX1_cube : MemLp (fun ω => |X₁ ω| ^ (3 : ℝ)) 4 μ := by
    let f : TestFun2D := uvMollifier κ₁ x
    have hX1_12 : MemLp X₁ 12 μ := by
      simpa [X₁, f] using
        (GaussianField.pairing_memLp (freeCovarianceCLM mass hmass) f (12 : ℝ≥0))
    have hcube' : MemLp (fun ω => |X₁ ω| ^ (3 : ℝ)) ((12 : ℝ≥0∞) / 3) μ := by
      simpa [Real.norm_eq_abs] using hX1_12.norm_rpow_div (3 : ℝ≥0∞)
    have hdiv12 : ((12 : ℝ≥0∞) / 3) = 4 := by
      change (((12 : NNReal) : ENNReal) / ((3 : NNReal) : ENNReal)) = ((4 : NNReal) : ENNReal)
      rw [← ENNReal.coe_div (p := (12 : NNReal)) (r := (3 : NNReal)) (by norm_num)]
      norm_num
    simpa [hdiv12] using hcube'
  have hX2_cube : MemLp (fun ω => |X₂ ω| ^ (3 : ℝ)) 4 μ := by
    let f : TestFun2D := uvMollifier κ₂ x
    have hX2_12 : MemLp X₂ 12 μ := by
      simpa [X₂, f] using
        (GaussianField.pairing_memLp (freeCovarianceCLM mass hmass) f (12 : ℝ≥0))
    have hcube' : MemLp (fun ω => |X₂ ω| ^ (3 : ℝ)) ((12 : ℝ≥0∞) / 3) μ := by
      simpa [Real.norm_eq_abs] using hX2_12.norm_rpow_div (3 : ℝ≥0∞)
    have hdiv12 : ((12 : ℝ≥0∞) / 3) = 4 := by
      change (((12 : NNReal) : ENNReal) / ((3 : NNReal) : ENNReal)) = ((4 : NNReal) : ENNReal)
      rw [← ENNReal.coe_div (p := (12 : NNReal)) (r := (3 : NNReal)) (by norm_num)]
      norm_num
    simpa [hdiv12] using hcube'
  have hX1_abs : MemLp (fun ω => |X₁ ω|) 4 μ := by
    simpa [X₁, Real.norm_eq_abs] using
      (GaussianField.pairing_memLp (freeCovarianceCLM mass hmass) (uvMollifier κ₁ x) (4 : ℝ≥0)).abs
  have hX2_abs : MemLp (fun ω => |X₂ ω|) 4 μ := by
    simpa [X₂, Real.norm_eq_abs] using
      (GaussianField.pairing_memLp (freeCovarianceCLM mass hmass) (uvMollifier κ₂ x) (4 : ℝ≥0)).abs
  have hQ1_mem : MemLp Q1 4 μ := by
    simpa [Q1] using (hX2_cube.add hX1_cube).const_mul 4
  have hQ2_mem : MemLp Q2 4 μ := by
    simpa [Q2] using (hX2_abs.add hX1_abs).const_mul (6 * |c|)
  have hQ_mem : MemLp Q 4 μ := by
    exact hQ1_mem.add hQ2_mem
  have hP_meas : AEStronglyMeasurable P μ := by
    let h1 := rawFieldEval_stronglyMeasurable mass κ₁ x
    let h2 := rawFieldEval_stronglyMeasurable mass κ₂ x
    have hP_eq :
        P =
          (fun ω =>
            X₂ ω * (X₁ ω) ^ 2 + (X₁ ω * (X₂ ω) ^ 2 + ((X₁ ω) ^ 3 + (X₂ ω) ^ 3)) -
              6 * c * (X₂ ω + X₁ ω)) := by
      funext ω
      simp [P, add_left_comm, add_comm, mul_left_comm, mul_comm]
    have hpoly :
        StronglyMeasurable
          (fun ω =>
            X₂ ω * (X₁ ω) ^ 2 + (X₁ ω * (X₂ ω) ^ 2 + ((X₁ ω) ^ 3 + (X₂ ω) ^ 3))) := by
      exact (h2.mul (h1.pow 2)).add ((h1.mul (h2.pow 2)).add ((h1.pow 3).add (h2.pow 3)))
    rw [hP_eq]
    exact (hpoly.sub ((h2.add h1).const_mul (6 * c))).aestronglyMeasurable
  have hP_mem : MemLp P 4 μ := by
    refine MemLp.of_le_mul (c := 1) hQ_mem hP_meas ?_
    refine Filter.Eventually.of_forall ?_
    intro ω
    have hω := cubic_factor_pointwise_bound (X₂ ω) (X₁ ω) c
    have hQ_nonneg : 0 ≤ Q ω := by
      unfold Q Q1 Q2
      positivity
    have hω' : ‖P ω‖ ≤ 1 * ‖Q ω‖ := by
      have hQ_norm : ‖Q ω‖ = Q ω := by
        simp [Real.norm_eq_abs, abs_of_nonneg hQ_nonneg]
      calc
        ‖P ω‖ = |P ω| := by simp [Real.norm_eq_abs]
        _ ≤ Q ω := by simpa [P, Q, Q1, Q2] using hω
        _ = ‖Q ω‖ := by rw [hQ_norm]
        _ = 1 * ‖Q ω‖ := by ring
    exact hω'
  have hprod : lpNorm (fun ω => Δ ω * P ω) 2 μ ≤ lpNorm Δ 4 μ * lpNorm P 4 μ :=
    lpNorm_mul_le_lpNorm_four_mul_four hΔ4 hP_mem
  have hP_bound :
      lpNorm P 4 μ ≤
        4 * ((10395 * σ₂ ^ 6) ^ ((1 : ℝ) / 4) + (10395 * σ₁ ^ 6) ^ ((1 : ℝ) / 4)) +
          6 * |c| * ((3 * σ₂ ^ 2) ^ ((1 : ℝ) / 4) + (3 * σ₁ ^ 2) ^ ((1 : ℝ) / 4)) := by
    simpa [μ, X₁, X₂, c, P, σ₁, σ₂] using
      cubic_factor_lpNorm_four_le_covariance mass hmass κ₁ κ₂ x
  have hΔ_eq :
      lpNorm Δ 4 μ = (3 * δσ ^ 2) ^ ((1 : ℝ) / 4) := by
    simpa [μ, Δ, X₁, X₂, δσ] using rawFieldEval_sub_lpNorm_four_eq mass hmass κ₁ κ₂ x
  calc
    lpNorm (fun ω => Δ ω * P ω) 2 μ ≤ lpNorm Δ 4 μ * lpNorm P 4 μ := hprod
    _ ≤ lpNorm Δ 4 μ *
        (4 * ((10395 * σ₂ ^ 6) ^ ((1 : ℝ) / 4) + (10395 * σ₁ ^ 6) ^ ((1 : ℝ) / 4)) +
          6 * |c| * ((3 * σ₂ ^ 2) ^ ((1 : ℝ) / 4) + (3 * σ₁ ^ 2) ^ ((1 : ℝ) / 4))) := by
          exact mul_le_mul_of_nonneg_left hP_bound MeasureTheory.lpNorm_nonneg
    _ = (3 * δσ ^ 2) ^ ((1 : ℝ) / 4) *
        (4 * ((10395 * σ₂ ^ 6) ^ ((1 : ℝ) / 4) + (10395 * σ₁ ^ 6) ^ ((1 : ℝ) / 4)) +
          6 * |c| * ((3 * σ₂ ^ 2) ^ ((1 : ℝ) / 4) + (3 * σ₁ ^ 2) ^ ((1 : ℝ) / 4))) := by
          rw [hΔ_eq]

/-- Exact `L²` norm of the quadratic re-Wick factor against a Gaussian raw field.
This isolates the linear renormalization term in the quartic shell increment. -/
private theorem rawFieldEval_rewick_two_lpNorm_two_eq
    (mass : ℝ) (hmass : 0 < mass) (κ : UVCutoff) (x : Spacetime2D) (c : ℝ) :
    lpNorm (fun ω : FieldConfig2D => wickMonomial 2 c (rawFieldEval mass κ ω x))
      2 (freeFieldMeasure mass hmass)
    = (3 * (GaussianField.covariance (freeCovarianceCLM mass hmass)
        (uvMollifier κ x) (uvMollifier κ x)) ^ 2
        - 2 * c * GaussianField.covariance (freeCovarianceCLM mass hmass)
            (uvMollifier κ x) (uvMollifier κ x)
        + c ^ 2) ^ ((1 : ℝ) / 2) := by
  let μ := freeFieldMeasure mass hmass
  let X : FieldConfig2D → ℝ := fun ω => rawFieldEval mass κ ω x
  let f : TestFun2D := uvMollifier κ x
  let σ : ℝ := GaussianField.covariance (freeCovarianceCLM mass hmass) f f
  have hmeas :
      AEStronglyMeasurable (fun ω : FieldConfig2D => wickMonomial 2 c (X ω)) μ := by
    exact ((wickMonomial_continuous 2 c).stronglyMeasurable.comp_measurable
      (rawFieldEval_stronglyMeasurable mass κ x).measurable).aestronglyMeasurable
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) ENNReal.ofNat_ne_top hmeas]
  norm_num
  have h2 : ∫ ω : FieldConfig2D, (ω f) ^ 2 ∂μ = σ := by
    simp_rw [show ∀ ω : FieldConfig2D, (ω f) ^ 2 = ω f * ω f from fun ω => sq (ω f)]
    simpa [GaussianField.covariance, σ] using
      cross_moment_eq_covariance (freeCovarianceCLM mass hmass) f f
  have h4 : ∫ ω : FieldConfig2D, (ω f) ^ 4 ∂μ = 3 * σ ^ 2 := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, moment_recursion_ai mass hmass f 2, h2]
    simp [σ]
    ring
  have hi4 : Integrable (fun ω : FieldConfig2D => (ω f) ^ 4) μ :=
    power_integrable_ai mass hmass f 4
  have hi2 : Integrable (fun ω : FieldConfig2D => (ω f) ^ 2) μ :=
    power_integrable_ai mass hmass f 2
  have hpoly :
      ∀ ω : FieldConfig2D,
        (X ω ^ 2 - c) ^ 2 = (ω f) ^ 4 - 2 * c * (ω f) ^ 2 + c ^ 2 := by
    intro ω
    change ((ω f) ^ 2 - c) ^ 2 = (ω f) ^ 4 - 2 * c * (ω f) ^ 2 + c ^ 2
    ring
  simp_rw [hpoly]
  have s1 :
      ∫ ω : FieldConfig2D, ((ω f) ^ 4 - 2 * c * (ω f) ^ 2 + c ^ 2) ∂μ =
        ∫ ω : FieldConfig2D, ((ω f) ^ 4 - 2 * c * (ω f) ^ 2) ∂μ +
        ∫ _ : FieldConfig2D, c ^ 2 ∂μ :=
    integral_add (hi4.sub (hi2.const_mul _)) (integrable_const _)
  have s2 :
      ∫ ω : FieldConfig2D, ((ω f) ^ 4 - 2 * c * (ω f) ^ 2) ∂μ =
        ∫ ω : FieldConfig2D, (ω f) ^ 4 ∂μ -
        ∫ ω : FieldConfig2D, (2 * c * (ω f) ^ 2) ∂μ :=
    integral_sub hi4 (hi2.const_mul _)
  rw [s1, s2, integral_const_mul, integral_const, h4, h2]
  have hμ : μ.real Set.univ = 1 := by
    simp [μ, Measure.real, measure_univ]
  simp [hμ, σ, f]

/-- Covariance-form `L²` norm of the linear re-Wick correction term in the
quartic shell increment. -/
private theorem wickPower_four_step_B_term_lpNorm_two_eq_covariance
    (mass : ℝ) (hmass : 0 < mass) (κ₁ κ₂ : UVCutoff) (x : Spacetime2D) :
    let μ := freeFieldMeasure mass hmass
    let c := regularizedPointCovariance mass κ₁
    let σ₂ := GaussianField.covariance (freeCovarianceCLM mass hmass)
      (uvMollifier κ₂ x) (uvMollifier κ₂ x)
    let δc := regularizedPointCovariance mass κ₂ - regularizedPointCovariance mass κ₁
    lpNorm (fun ω : FieldConfig2D =>
      6 * δc * wickMonomial 2 c (rawFieldEval mass κ₂ ω x)) 2 μ
    = |6 * δc| * (3 * σ₂ ^ 2 - 2 * c * σ₂ + c ^ 2) ^ ((1 : ℝ) / 2) := by
  let μ := freeFieldMeasure mass hmass
  let c := regularizedPointCovariance mass κ₁
  let σ₂ := GaussianField.covariance (freeCovarianceCLM mass hmass)
    (uvMollifier κ₂ x) (uvMollifier κ₂ x)
  let δc := regularizedPointCovariance mass κ₂ - regularizedPointCovariance mass κ₁
  dsimp [μ, c, σ₂, δc]
  let h : FieldConfig2D → ℝ := fun ω =>
    rawFieldEval mass κ₂ ω x ^ 2 - regularizedPointCovariance mass κ₁
  have hscale :
      lpNorm
          ((6 * (regularizedPointCovariance mass κ₂ - regularizedPointCovariance mass κ₁)) • h)
          2 (freeFieldMeasure mass hmass)
        =
          ‖(6 * (regularizedPointCovariance mass κ₂ - regularizedPointCovariance mass κ₁) : ℝ)‖₊ *
            lpNorm h 2 (freeFieldMeasure mass hmass) :=
    MeasureTheory.lpNorm_const_smul _ _ _
  have hrewick :
      lpNorm h 2 (freeFieldMeasure mass hmass)
        =
          (3 * (GaussianField.covariance (freeCovarianceCLM mass hmass)
              (uvMollifier κ₂ x) (uvMollifier κ₂ x)) ^ 2
            - 2 * regularizedPointCovariance mass κ₁ *
                GaussianField.covariance (freeCovarianceCLM mass hmass)
                  (uvMollifier κ₂ x) (uvMollifier κ₂ x)
            + regularizedPointCovariance mass κ₁ ^ 2) ^ ((1 : ℝ) / 2) := by
    simpa [h, wickMonomial_two] using
      rawFieldEval_rewick_two_lpNorm_two_eq mass hmass κ₂ x (regularizedPointCovariance mass κ₁)
  calc
    lpNorm
        (fun ω : FieldConfig2D =>
          6 * (regularizedPointCovariance mass κ₂ - regularizedPointCovariance mass κ₁) *
            wickMonomial 2 (regularizedPointCovariance mass κ₁) (rawFieldEval mass κ₂ ω x))
        2 (freeFieldMeasure mass hmass)
      =
        lpNorm
          ((6 * (regularizedPointCovariance mass κ₂ - regularizedPointCovariance mass κ₁)) • h)
          2 (freeFieldMeasure mass hmass) := by
            congr 1
            ext ω
            simp [h, smul_eq_mul, wickMonomial_two]
    _ =
        ‖(6 * (regularizedPointCovariance mass κ₂ - regularizedPointCovariance mass κ₁) : ℝ)‖₊ *
          lpNorm h 2 (freeFieldMeasure mass hmass) := hscale
    _ =
        |6 * (regularizedPointCovariance mass κ₂ - regularizedPointCovariance mass κ₁)| *
          (3 * (GaussianField.covariance (freeCovarianceCLM mass hmass)
              (uvMollifier κ₂ x) (uvMollifier κ₂ x)) ^ 2
            - 2 * regularizedPointCovariance mass κ₁ *
                GaussianField.covariance (freeCovarianceCLM mass hmass)
                  (uvMollifier κ₂ x) (uvMollifier κ₂ x)
            + regularizedPointCovariance mass κ₁ ^ 2) ^ ((1 : ℝ) / 2) := by
              rw [hrewick]
              simp [Real.norm_eq_abs]

/-- Covariance-form `L²` norm of the constant re-Wick correction term in the
  quartic shell increment. -/
private theorem wickPower_four_step_C_term_lpNorm_two_eq_covariance
    (mass : ℝ) (hmass : 0 < mass) (κ₁ κ₂ : UVCutoff) :
    let μ := freeFieldMeasure mass hmass
    let δc := regularizedPointCovariance mass κ₂ - regularizedPointCovariance mass κ₁
    lpNorm (fun _ : FieldConfig2D => 3 * δc ^ 2) 2 μ = |3 * δc ^ 2| := by
  let μ := freeFieldMeasure mass hmass
  let δc := regularizedPointCovariance mass κ₂ - regularizedPointCovariance mass κ₁
  dsimp [μ, δc]
  rw [MeasureTheory.lpNorm_const' (μ := freeFieldMeasure mass hmass) (p := 2)
    (hp₀ := by positivity) (hp := by simp)
    (c := (3 * (regularizedPointCovariance mass κ₂ - regularizedPointCovariance mass κ₁) ^ 2 : ℝ))]
  simp [Real.norm_eq_abs]

/-- Pointwise-in-`x` `L²` bound for one quartic Wick-power step. After this
the only remaining obstruction in the shell increment proof is to bound the
covariance expressions uniformly/integrably in `x`. -/
private theorem wickPower_four_step_lpNorm_two_le_covariance
    (mass : ℝ) (hmass : 0 < mass) (κ₁ κ₂ : UVCutoff) (x : Spacetime2D) :
    let μ := freeFieldMeasure mass hmass
    let c := regularizedPointCovariance mass κ₁
    let σ₁ := GaussianField.covariance (freeCovarianceCLM mass hmass)
      (uvMollifier κ₁ x) (uvMollifier κ₁ x)
    let σ₂ := GaussianField.covariance (freeCovarianceCLM mass hmass)
      (uvMollifier κ₂ x) (uvMollifier κ₂ x)
    let δσ := GaussianField.covariance (freeCovarianceCLM mass hmass)
      (uvMollifier κ₂ x - uvMollifier κ₁ x)
      (uvMollifier κ₂ x - uvMollifier κ₁ x)
    let δc := regularizedPointCovariance mass κ₂ - regularizedPointCovariance mass κ₁
    lpNorm (fun ω : FieldConfig2D => wickPower 4 mass κ₂ ω x - wickPower 4 mass κ₁ ω x) 2 μ
      ≤
        (3 * δσ ^ 2) ^ ((1 : ℝ) / 4) *
          (4 * ((10395 * σ₂ ^ 6) ^ ((1 : ℝ) / 4) + (10395 * σ₁ ^ 6) ^ ((1 : ℝ) / 4)) +
            6 * |c| * ((3 * σ₂ ^ 2) ^ ((1 : ℝ) / 4) + (3 * σ₁ ^ 2) ^ ((1 : ℝ) / 4)))
        + |6 * δc| * (3 * σ₂ ^ 2 - 2 * c * σ₂ + c ^ 2) ^ ((1 : ℝ) / 2)
        + |3 * δc ^ 2| := by
  let μ := freeFieldMeasure mass hmass
  let c := regularizedPointCovariance mass κ₁
  let σ₁ := GaussianField.covariance (freeCovarianceCLM mass hmass)
    (uvMollifier κ₁ x) (uvMollifier κ₁ x)
  let σ₂ := GaussianField.covariance (freeCovarianceCLM mass hmass)
    (uvMollifier κ₂ x) (uvMollifier κ₂ x)
  let δσ := GaussianField.covariance (freeCovarianceCLM mass hmass)
    (uvMollifier κ₂ x - uvMollifier κ₁ x)
    (uvMollifier κ₂ x - uvMollifier κ₁ x)
  let δc := regularizedPointCovariance mass κ₂ - regularizedPointCovariance mass κ₁
  let A : FieldConfig2D → ℝ := fun ω =>
    (rawFieldEval mass κ₂ ω x - rawFieldEval mass κ₁ ω x) *
      ((rawFieldEval mass κ₂ ω x) ^ 3 +
       (rawFieldEval mass κ₂ ω x) ^ 2 * rawFieldEval mass κ₁ ω x +
       rawFieldEval mass κ₂ ω x * (rawFieldEval mass κ₁ ω x) ^ 2 +
       (rawFieldEval mass κ₁ ω x) ^ 3 -
       6 * c * (rawFieldEval mass κ₂ ω x + rawFieldEval mass κ₁ ω x))
  let B : FieldConfig2D → ℝ := fun ω =>
    6 * δc * wickMonomial 2 c (rawFieldEval mass κ₂ ω x)
  let C : FieldConfig2D → ℝ := fun _ => 3 * δc ^ 2
  let h : FieldConfig2D → ℝ := fun ω => rawFieldEval mass κ₂ ω x ^ 2 - c
  have hconst_mem : MemLp C 2 μ := by
    simpa [C] using
      (memLp_const_iff (μ := μ) (p := (2 : ℝ≥0∞)) (c := (3 * δc ^ 2 : ℝ))
        (by norm_num) (by norm_num)).2
        (by simp)
  have hh_mem : MemLp h 2 μ := by
    have hX4 : MemLp (fun ω : FieldConfig2D => rawFieldEval mass κ₂ ω x) 4 μ := by
      simpa using
        (GaussianField.pairing_memLp (freeCovarianceCLM mass hmass) (uvMollifier κ₂ x) (4 : ℝ≥0))
    have hXsq_abs : MemLp (fun ω : FieldConfig2D => |rawFieldEval mass κ₂ ω x| ^ (2 : ℝ)) 2 μ := by
      have htmp : MemLp (fun ω : FieldConfig2D => ‖rawFieldEval mass κ₂ ω x‖ ^ (2 : ℝ))
          ((4 : ℝ≥0∞) / 2) μ := by
        simpa [Real.norm_eq_abs] using hX4.norm_rpow_div (2 : ℝ≥0∞)
      have hdiv : ((4 : ℝ≥0∞) / 2) = 2 := by
        change (((4 : NNReal) : ENNReal) / ((2 : NNReal) : ENNReal)) = ((2 : NNReal) : ENNReal)
        rw [← ENNReal.coe_div (p := (4 : NNReal)) (r := (2 : NNReal)) (by norm_num)]
        norm_num
      simpa [hdiv] using htmp
    have hXsq : MemLp (fun ω : FieldConfig2D => rawFieldEval mass κ₂ ω x ^ 2) 2 μ := by
      refine hXsq_abs.congr_norm
        ((rawFieldEval_stronglyMeasurable mass κ₂ x).pow 2).aestronglyMeasurable ?_
      filter_upwards with ω
      rw [show |rawFieldEval mass κ₂ ω x| ^ (2 : ℝ) = rawFieldEval mass κ₂ ω x ^ 2 by
        rw [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast, sq_abs]]
    have hc_mem : MemLp (fun _ : FieldConfig2D => c) 2 μ := by
      simpa using
        (memLp_const_iff (μ := μ) (p := (2 : ℝ≥0∞)) (c := c) (by norm_num) (by norm_num)).2
          (by simp)
    simpa [h] using hXsq.sub hc_mem
  have hB_mem : MemLp B 2 μ := by
    simpa [B, h, wickMonomial_two, smul_eq_mul] using hh_mem.const_mul (6 * δc)
  have hCB_mem : MemLp (fun ω => C ω - B ω) 2 μ := hconst_mem.sub hB_mem
  have hdecomp :
      (fun ω : FieldConfig2D => wickPower 4 mass κ₂ ω x - wickPower 4 mass κ₁ ω x) =
        (fun ω => (C ω - B ω) + A ω) := by
    funext ω
    rw [wickPower_four_step_decomposition mass κ₁ κ₂ ω x]
    simp [A, B, C, c, δc]
    ring
  calc
    lpNorm (fun ω : FieldConfig2D => wickPower 4 mass κ₂ ω x - wickPower 4 mass κ₁ ω x) 2 μ
      = lpNorm (fun ω => (C ω - B ω) + A ω) 2 μ := by rw [hdecomp]
    _ ≤ lpNorm (fun ω => C ω - B ω) 2 μ + lpNorm A 2 μ := by
          exact lpNorm_add_le hCB_mem (g := A) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    _ ≤ (lpNorm C 2 μ + lpNorm B 2 μ) + lpNorm A 2 μ := by
          gcongr
          exact lpNorm_sub_le hconst_mem (g := B) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    _ ≤ (lpNorm C 2 μ
          + |6 * δc| * (3 * σ₂ ^ 2 - 2 * c * σ₂ + c ^ 2) ^ ((1 : ℝ) / 2))
          + lpNorm A 2 μ := by
            gcongr
            exact le_of_eq <| by simpa [μ, c, σ₂, δc, B] using
              wickPower_four_step_B_term_lpNorm_two_eq_covariance mass hmass κ₁ κ₂ x
    _ ≤ (lpNorm C 2 μ
          + |6 * δc| * (3 * σ₂ ^ 2 - 2 * c * σ₂ + c ^ 2) ^ ((1 : ℝ) / 2))
          + ((3 * δσ ^ 2) ^ ((1 : ℝ) / 4) *
            (4 * ((10395 * σ₂ ^ 6) ^ ((1 : ℝ) / 4) + (10395 * σ₁ ^ 6) ^ ((1 : ℝ) / 4)) +
              6 * |c| * ((3 * σ₂ ^ 2) ^ ((1 : ℝ) / 4) + (3 * σ₁ ^ 2) ^ ((1 : ℝ) / 4)))) := by
            gcongr
            simpa [μ, c, σ₁, σ₂, δσ, A] using
              wickPower_four_step_A_term_lpNorm_two_le_covariance mass hmass κ₁ κ₂ x
    _ = |3 * δc ^ 2|
          + |6 * δc| * (3 * σ₂ ^ 2 - 2 * c * σ₂ + c ^ 2) ^ ((1 : ℝ) / 2)
          + ((3 * δσ ^ 2) ^ ((1 : ℝ) / 4) *
            (4 * ((10395 * σ₂ ^ 6) ^ ((1 : ℝ) / 4) + (10395 * σ₁ ^ 6) ^ ((1 : ℝ) / 4)) +
              6 * |c| * ((3 * σ₂ ^ 2) ^ ((1 : ℝ) / 4) + (3 * σ₁ ^ 2) ^ ((1 : ℝ) / 4)))) := by
            rw [wickPower_four_step_C_term_lpNorm_two_eq_covariance mass hmass κ₁ κ₂]
    _ = (3 * δσ ^ 2) ^ ((1 : ℝ) / 4) *
          (4 * ((10395 * σ₂ ^ 6) ^ ((1 : ℝ) / 4) + (10395 * σ₁ ^ 6) ^ ((1 : ℝ) / 4)) +
            6 * |c| * ((3 * σ₂ ^ 2) ^ ((1 : ℝ) / 4) + (3 * σ₁ ^ 2) ^ ((1 : ℝ) / 4)))
        + |6 * δc| * (3 * σ₂ ^ 2 - 2 * c * σ₂ + c ^ 2) ^ ((1 : ℝ) / 2)
        + |3 * δc ^ 2| := by ring

/-- The square of the Wick-step difference is integrable on the product of the
free field measure with Lebesgue measure restricted to `Λ`. This is a purely
functional-analytic bridge: the pointwise inequality `(a - b)^2 ≤ 2(a^2 + b^2)`
reduces integrability to the already-proved product-square integrability of the
individual cutoff Wick powers. -/
private theorem wickPower_step_sq_integrable_prod (params : Phi4Params) (Λ : Rectangle)
    (κ₁ κ₂ : UVCutoff) :
    Integrable
      (fun p : FieldConfig2D × Spacetime2D =>
        (wickPower 4 params.mass κ₂ p.1 p.2 - wickPower 4 params.mass κ₁ p.1 p.2) ^ 2)
      ((freeFieldMeasure params.mass params.mass_pos).prod
        (MeasureTheory.volume.restrict Λ.toSet)) := by
  let μ := freeFieldMeasure params.mass params.mass_pos
  let ν := MeasureTheory.volume.restrict Λ.toSet
  have hmeas : AEStronglyMeasurable
      (fun p : FieldConfig2D × Spacetime2D =>
        (wickPower 4 params.mass κ₂ p.1 p.2 - wickPower 4 params.mass κ₁ p.1 p.2) ^ 2)
      (μ.prod ν) := by
    exact (((wickPower_stronglyMeasurable_uncurry 4 params.mass κ₂).sub
      (wickPower_stronglyMeasurable_uncurry 4 params.mass κ₁)).pow 2).aestronglyMeasurable
  have hκ₂ := wickPower_sq_integrable_prod params Λ κ₂
  have hκ₁ := wickPower_sq_integrable_prod params Λ κ₁
  have hsum : Integrable
      (fun p : FieldConfig2D × Spacetime2D =>
        (wickPower 4 params.mass κ₂ p.1 p.2) ^ 2 +
          (wickPower 4 params.mass κ₁ p.1 p.2) ^ 2)
      (μ.prod ν) := hκ₂.add hκ₁
  have hdom : Integrable
      (fun p : FieldConfig2D × Spacetime2D =>
        2 * ((wickPower 4 params.mass κ₂ p.1 p.2) ^ 2 +
          (wickPower 4 params.mass κ₁ p.1 p.2) ^ 2))
      (μ.prod ν) := hsum.const_mul 2
  apply hdom.mono hmeas
  filter_upwards with p
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  rw [Real.norm_of_nonneg (by positivity)]
  nlinarith [sq_nonneg
    (wickPower 4 params.mass κ₂ p.1 p.2 + wickPower 4 params.mass κ₁ p.1 p.2)]

/-- Spatial bridge from the pointwise Wick-step square to the cutoff interaction
increment. This isolates the remaining shell-rate theorem to a covariance bound
under the spatial integral: all Fubini and Cauchy-Schwarz bookkeeping is done
here. -/
private theorem interactionCutoff_sub_sq_le_spatialIntegral
    (params : Phi4Params) (Λ : Rectangle) (κ₁ κ₂ : UVCutoff) :
    ∫ ω : FieldConfig2D,
      (interactionCutoff params Λ κ₂ ω - interactionCutoff params Λ κ₁ ω) ^ 2
        ∂(freeFieldMeasure params.mass params.mass_pos)
      ≤ params.coupling ^ 2 * (MeasureTheory.volume Λ.toSet).toReal *
          ∫ x in Λ.toSet,
            ∫ ω : FieldConfig2D,
              (wickPower 4 params.mass κ₂ ω x - wickPower 4 params.mass κ₁ ω x) ^ 2
                ∂(freeFieldMeasure params.mass params.mass_pos) := by
  let μ := freeFieldMeasure params.mass params.mass_pos
  let ν := MeasureTheory.volume.restrict Λ.toSet
  let d : FieldConfig2D → Spacetime2D → ℝ := fun ω x =>
    wickPower 4 params.mass κ₂ ω x - wickPower 4 params.mass κ₁ ω x
  have hprod : Integrable (fun p : FieldConfig2D × Spacetime2D => (d p.1 p.2) ^ 2) (μ.prod ν) := by
    simpa [μ, ν, d] using wickPower_step_sq_integrable_prod params Λ κ₁ κ₂
  have hdint : Integrable (fun ω => ∫ x, (d ω x) ^ 2 ∂ν) μ :=
    hprod.integral_prod_left
  have hdom :
      Integrable (fun ω => (params.coupling ^ 2 * (MeasureTheory.volume Λ.toSet).toReal) *
        ∫ x, (d ω x) ^ 2 ∂ν) μ := hdint.const_mul _
  have hnonneg :
      0 ≤ᵐ[μ] fun ω : FieldConfig2D =>
        (interactionCutoff params Λ κ₂ ω - interactionCutoff params Λ κ₁ ω) ^ 2 :=
    Filter.Eventually.of_forall fun _ => sq_nonneg _
  have hpoint :
      ∀ᵐ ω ∂μ,
        (interactionCutoff params Λ κ₂ ω - interactionCutoff params Λ κ₁ ω) ^ 2 ≤
          (params.coupling ^ 2 * (MeasureTheory.volume Λ.toSet).toReal) *
            ∫ x, (d ω x) ^ 2 ∂ν := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    have hκ₂_int : Integrable (fun x => wickPower 4 params.mass κ₂ ω x) ν :=
      (wickPower_continuous_in_x 4 params.mass κ₂ ω).continuousOn.integrableOn_compact
        Λ.toSet_isCompact
    have hκ₁_int : Integrable (fun x => wickPower 4 params.mass κ₁ ω x) ν :=
      (wickPower_continuous_in_x 4 params.mass κ₁ ω).continuousOn.integrableOn_compact
        Λ.toSet_isCompact
    have hd_int : Integrable (fun x => d ω x) ν := hκ₂_int.sub hκ₁_int
    have hd_sq_int : Integrable (fun x => (d ω x) ^ 2) ν := by
      exact (((wickPower_continuous_in_x 4 params.mass κ₂ ω).sub
        (wickPower_continuous_in_x 4 params.mass κ₁ ω)).pow 2).continuousOn.integrableOn_compact
        Λ.toSet_isCompact
    have hsub :
        interactionCutoff params Λ κ₂ ω - interactionCutoff params Λ κ₁ ω =
          params.coupling * ∫ x in Λ.toSet, d ω x := by
      unfold interactionCutoff
      rw [← mul_sub_left_distrib]
      congr 1
      rw [integral_sub hκ₂_int hκ₁_int]
    calc
      (interactionCutoff params Λ κ₂ ω - interactionCutoff params Λ κ₁ ω) ^ 2
        = params.coupling ^ 2 * (∫ x in Λ.toSet, d ω x) ^ 2 := by
            rw [hsub, mul_pow]
      _ ≤ params.coupling ^ 2 *
            ((MeasureTheory.volume Λ.toSet).toReal * ∫ x in Λ.toSet, (d ω x) ^ 2) := by
            gcongr
            exact sq_setIntegral_le_volume_mul_setIntegral_sq
              Λ.toSet Λ.toSet_measurableSet hd_int hd_sq_int Λ.toSet_volume_ne_top
      _ = (params.coupling ^ 2 * (MeasureTheory.volume Λ.toSet).toReal) *
            ∫ x, (d ω x) ^ 2 ∂ν := by
            rw [mul_assoc]
  have hle := integral_mono_of_nonneg hnonneg hdom hpoint
  calc
    ∫ ω : FieldConfig2D,
        (interactionCutoff params Λ κ₂ ω - interactionCutoff params Λ κ₁ ω) ^ 2 ∂μ
      ≤ ∫ ω : FieldConfig2D,
          (params.coupling ^ 2 * (MeasureTheory.volume Λ.toSet).toReal) *
            ∫ x, (d ω x) ^ 2 ∂ν ∂μ := hle
    _ = (params.coupling ^ 2 * (MeasureTheory.volume Λ.toSet).toReal) *
          ∫ ω : FieldConfig2D, ∫ x, (d ω x) ^ 2 ∂ν ∂μ := by
          rw [integral_const_mul]
    _ = (params.coupling ^ 2 * (MeasureTheory.volume Λ.toSet).toReal) *
          ∫ x, ∫ ω : FieldConfig2D, (d ω x) ^ 2 ∂μ ∂ν := by
          congr 1
          exact MeasureTheory.integral_integral_swap hprod
    _ = params.coupling ^ 2 * (MeasureTheory.volume Λ.toSet).toReal *
          ∫ x in Λ.toSet,
            ∫ ω : FieldConfig2D,
              (wickPower 4 params.mass κ₂ ω x - wickPower 4 params.mass κ₁ ω x) ^ 2 ∂μ := by
          rfl

/-- Pointwise square-expectation bound for a quartic Wick-power step. This is
the square-integral version of `wickPower_four_step_lpNorm_two_le_covariance`,
stated in the exact form needed under the spatial integral for the shell-rate
theorem. -/
private theorem wickPower_four_step_sq_expectation_le_covariance
    (mass : ℝ) (hmass : 0 < mass) (κ₁ κ₂ : UVCutoff) (x : Spacetime2D) :
    let μ := freeFieldMeasure mass hmass
    let c := regularizedPointCovariance mass κ₁
    let σ₁ := GaussianField.covariance (freeCovarianceCLM mass hmass)
      (uvMollifier κ₁ x) (uvMollifier κ₁ x)
    let σ₂ := GaussianField.covariance (freeCovarianceCLM mass hmass)
      (uvMollifier κ₂ x) (uvMollifier κ₂ x)
    let δσ := GaussianField.covariance (freeCovarianceCLM mass hmass)
      (uvMollifier κ₂ x - uvMollifier κ₁ x)
      (uvMollifier κ₂ x - uvMollifier κ₁ x)
    let δc := regularizedPointCovariance mass κ₂ - regularizedPointCovariance mass κ₁
    let B :=
      (3 * δσ ^ 2) ^ ((1 : ℝ) / 4) *
        (4 * ((10395 * σ₂ ^ 6) ^ ((1 : ℝ) / 4) + (10395 * σ₁ ^ 6) ^ ((1 : ℝ) / 4)) +
          6 * |c| * ((3 * σ₂ ^ 2) ^ ((1 : ℝ) / 4) + (3 * σ₁ ^ 2) ^ ((1 : ℝ) / 4)))
      + |6 * δc| * (3 * σ₂ ^ 2 - 2 * c * σ₂ + c ^ 2) ^ ((1 : ℝ) / 2)
      + |3 * δc ^ 2|
    ∫ ω : FieldConfig2D,
      (wickPower 4 mass κ₂ ω x - wickPower 4 mass κ₁ ω x) ^ 2 ∂μ ≤ B ^ 2 := by
  let μ := freeFieldMeasure mass hmass
  let c := regularizedPointCovariance mass κ₁
  let σ₁ := GaussianField.covariance (freeCovarianceCLM mass hmass)
    (uvMollifier κ₁ x) (uvMollifier κ₁ x)
  let σ₂ := GaussianField.covariance (freeCovarianceCLM mass hmass)
    (uvMollifier κ₂ x) (uvMollifier κ₂ x)
  let δσ := GaussianField.covariance (freeCovarianceCLM mass hmass)
    (uvMollifier κ₂ x - uvMollifier κ₁ x)
    (uvMollifier κ₂ x - uvMollifier κ₁ x)
  let δc := regularizedPointCovariance mass κ₂ - regularizedPointCovariance mass κ₁
  let h : FieldConfig2D → ℝ := fun ω =>
    wickPower 4 mass κ₂ ω x - wickPower 4 mass κ₁ ω x
  let B :=
    (3 * δσ ^ 2) ^ ((1 : ℝ) / 4) *
      (4 * ((10395 * σ₂ ^ 6) ^ ((1 : ℝ) / 4) + (10395 * σ₁ ^ 6) ^ ((1 : ℝ) / 4)) +
        6 * |c| * ((3 * σ₂ ^ 2) ^ ((1 : ℝ) / 4) + (3 * σ₁ ^ 2) ^ ((1 : ℝ) / 4)))
    + |6 * δc| * (3 * σ₂ ^ 2 - 2 * c * σ₂ + c ^ 2) ^ ((1 : ℝ) / 2)
    + |3 * δc ^ 2|
  have hκ₂_mem : MemLp (fun ω : FieldConfig2D => wickPower 4 mass κ₂ ω x) 2 μ := by
    simpa [μ] using
      (wickPower_memLp 4 mass hmass κ₂ x (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
  have hκ₁_mem : MemLp (fun ω : FieldConfig2D => wickPower 4 mass κ₁ ω x) 2 μ := by
    simpa [μ] using
      (wickPower_memLp 4 mass hmass κ₁ x (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
  have hh_mem : MemLp h 2 μ := by
    simpa [h] using hκ₂_mem.sub hκ₁_mem
  have h_lp_sq :
      lpNorm h 2 μ ^ 2 = ∫ ω : FieldConfig2D, (h ω) ^ 2 ∂μ := by
    rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) ENNReal.ofNat_ne_top
      hh_mem.aestronglyMeasurable]
    norm_num
    have h_nonneg_int : 0 ≤ ∫ ω : FieldConfig2D, (h ω) ^ 2 ∂μ :=
      integral_nonneg fun _ => sq_nonneg _
    rw [show ((∫ ω : FieldConfig2D, (h ω) ^ 2 ∂μ) ^ ((1 : ℝ) / 2)) = 
      Real.sqrt (∫ ω : FieldConfig2D, (h ω) ^ 2 ∂μ) by
        rw [Real.sqrt_eq_rpow]]
    rw [Real.sq_sqrt h_nonneg_int]
  have hB_nonneg : 0 ≤ B := by
    have hrewick_nonneg : 0 ≤ (3 * σ₂ ^ 2 - 2 * c * σ₂ + c ^ 2) ^ ((1 : ℝ) / 2) := by
      rw [← rawFieldEval_rewick_two_lpNorm_two_eq mass hmass κ₂ x c]
      exact MeasureTheory.lpNorm_nonneg
    positivity
  have h_lp : lpNorm h 2 μ ≤ B := by
    simpa [μ, c, σ₁, σ₂, δσ, δc, h, B] using
      wickPower_four_step_lpNorm_two_le_covariance mass hmass κ₁ κ₂ x
  have h_lp_nonneg : 0 ≤ lpNorm h 2 μ := MeasureTheory.lpNorm_nonneg
  have hsq : lpNorm h 2 μ ^ 2 ≤ B ^ 2 := by
    nlinarith [h_lp, h_lp_nonneg, hB_nonneg]
  calc
    ∫ ω : FieldConfig2D, (wickPower 4 mass κ₂ ω x - wickPower 4 mass κ₁ ω x) ^ 2 ∂μ
      = lpNorm h 2 μ ^ 2 := h_lp_sq.symm
    _ ≤ B ^ 2 := hsq

/-- Honest frontier for the discrete shell branch: after the algebraic and
Gaussian-moment reductions above, the remaining mathematics is to show that the
spatially integrated quartic shell step decays at the target rate.

For the current CLM-based Gaussian measure, this requires either a direct
covariance estimate for the CLM covariance or a successful bridge to the
flat-space kernel in `gap_covariance_eq_kernel`. -/
theorem gap_wickPower_standardSeq_spatial_sq_rate
    (params : Phi4Params) (Λ : Rectangle) :
    ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ,
      params.coupling ^ 2 * (MeasureTheory.volume Λ.toSet).toReal *
          ∫ x in Λ.toSet,
            ∫ ω : FieldConfig2D,
              (wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x -
                wickPower 4 params.mass (standardUVCutoffSeq n) ω x) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)
        ≤ D ^ 2 * (Real.log (n + 2)) ^ 2 / (n + 1) ^ 3 := by
  sorry

/-- The L² increment rate for the cutoff interaction along the canonical UV
    cutoff sequence.

    This theorem is now reduced to the explicit discrete shell estimate
    `gap_wickPower_standardSeq_spatial_sq_rate`. For the current CLM-based
    Gaussian measure, the remaining missing mathematics is a covariance-shell
    decay bound for the spatially integrated quartic Wick-power step.

    If the foundational bridge `gap_covariance_eq_kernel` is resolved, the
    expected flat-space heuristic is that the covariance increment on the shell
    `κ_n -> κ_{n+1}` gains the rate `log(n+2) / (n+1)^(3/2)`. -/
theorem gap_interactionCutoff_standardSeq_L2_increment_rate
    (params : Phi4Params) (Λ : Rectangle) :
    ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ,
      ∫ ω : FieldConfig2D,
        (interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω -
         interactionCutoff params Λ (standardUVCutoffSeq n) ω) ^ 2
        ∂(freeFieldMeasure params.mass params.mass_pos)
      ≤ D ^ 2 * (Real.log (n + 2)) ^ 2 / (n + 1) ^ 3 := by
  let μ := freeFieldMeasure params.mass params.mass_pos
  have h_reduction :
      ∀ n : ℕ,
        ∫ ω : FieldConfig2D,
            (interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω -
              interactionCutoff params Λ (standardUVCutoffSeq n) ω) ^ 2 ∂μ
          ≤ params.coupling ^ 2 * (MeasureTheory.volume Λ.toSet).toReal *
              ∫ x in Λ.toSet,
                ∫ ω : FieldConfig2D,
                  (wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x -
                    wickPower 4 params.mass (standardUVCutoffSeq n) ω x) ^ 2 ∂μ := by
    intro n
    simpa [μ] using
      interactionCutoff_sub_sq_le_spatialIntegral params Λ
        (standardUVCutoffSeq n) (standardUVCutoffSeq (n + 1))
  obtain ⟨D, hD, h_shell⟩ := gap_wickPower_standardSeq_spatial_sq_rate params Λ
  refine ⟨D, hD, ?_⟩
  intro n
  calc
    ∫ ω : FieldConfig2D,
        (interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω -
          interactionCutoff params Λ (standardUVCutoffSeq n) ω) ^ 2 ∂μ
      ≤ params.coupling ^ 2 * (MeasureTheory.volume Λ.toSet).toReal *
          ∫ x in Λ.toSet,
            ∫ ω : FieldConfig2D,
              (wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x -
                wickPower 4 params.mass (standardUVCutoffSeq n) ω x) ^ 2 ∂μ := h_reduction n
    _ ≤ D ^ 2 * (Real.log (n + 2)) ^ 2 / (n + 1) ^ 3 := h_shell n

/-- The model upper bound `sqrt(D² log²(n+2) / (n+1)^3)` is summable. -/
private theorem summable_sqrt_log_sq_div_cube (D : ℝ) (hD : 0 < D) :
    Summable (fun n : ℕ =>
      Real.sqrt (D ^ 2 * (Real.log (↑n + 2)) ^ 2 / (↑n + 1) ^ 3)) := by
  have h_rpow_summable : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-(5 / 4 : ℝ))) := by
    have h_key : (fun n : ℕ => ((n : ℝ) + 1) ^ (-(5 / 4 : ℝ))) =
        (fun n : ℕ => ((n : ℝ) ^ (-((5 : ℝ) / 4)))) ∘ Nat.succ := by
      ext n
      simp [Nat.cast_succ]
    rw [h_key]
    refine Summable.comp_injective ?_ Nat.succ_injective
    convert Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 5 / 4) using 1
    ext n
    rw [Real.rpow_neg (Nat.cast_nonneg n)]
  have h_upper_summable : Summable (fun n : ℕ =>
      (4 * (2 : ℝ) ^ ((1 : ℝ) / 4) * D) * ((n : ℝ) + 1) ^ (-(5 / 4 : ℝ))) :=
    h_rpow_summable.mul_left (4 * (2 : ℝ) ^ ((1 : ℝ) / 4) * D)
  refine Summable.of_nonneg_of_le (fun n => Real.sqrt_nonneg _) ?_ h_upper_summable
  intro n
  have hn1 : 0 < (n : ℝ) + 1 := by positivity
  have hn2 : 0 < (n : ℝ) + 2 := by positivity
  have hlog1 : Real.log ((n : ℝ) + 2) ≤ 4 * ((n : ℝ) + 2) ^ ((1 : ℝ) / 4) := by
    have hlog := Real.log_le_rpow_div hn2.le (by norm_num : (0 : ℝ) < 1 / 4)
    linarith
  have hlog2 : ((n : ℝ) + 2) ^ ((1 : ℝ) / 4) ≤
      (2 : ℝ) ^ ((1 : ℝ) / 4) * ((n : ℝ) + 1) ^ ((1 : ℝ) / 4) := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (le_of_lt hn1)]
    exact Real.rpow_le_rpow hn2.le (by linarith) (by norm_num)
  have hlog3 : Real.log ((n : ℝ) + 2) ≤
      4 * (2 : ℝ) ^ ((1 : ℝ) / 4) * ((n : ℝ) + 1) ^ ((1 : ℝ) / 4) := by
    linarith [mul_le_mul_of_nonneg_left hlog2 (by norm_num : (0 : ℝ) ≤ 4)]
  have hlog_nonneg : 0 ≤ Real.log ((n : ℝ) + 2) := by
    exact Real.log_nonneg (by linarith)
  have hlog3_nonneg : 0 ≤ 4 * (2 : ℝ) ^ ((1 : ℝ) / 4) * ((n : ℝ) + 1) ^ ((1 : ℝ) / 4) := by
    positivity
  have hlog4 : Real.log ((n : ℝ) + 2) ^ 2 ≤
      (4 * (2 : ℝ) ^ ((1 : ℝ) / 4) * ((n : ℝ) + 1) ^ ((1 : ℝ) / 4)) ^ 2 :=
    by nlinarith
  have hlog5 : (4 * (2 : ℝ) ^ ((1 : ℝ) / 4) * ((n : ℝ) + 1) ^ ((1 : ℝ) / 4)) ^ 2 =
      16 * Real.sqrt 2 * ((n : ℝ) + 1) ^ ((1 : ℝ) / 2) := by
    have h_two : ((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 = Real.sqrt 2 := by
      rw [Real.sqrt_eq_rpow, sq, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      norm_num
    have h_one : (((n : ℝ) + 1) ^ ((1 : ℝ) / 4)) ^ 2 = ((n : ℝ) + 1) ^ ((1 : ℝ) / 2) := by
      rw [sq, ← Real.rpow_add hn1]
      norm_num
    rw [mul_pow, mul_pow, h_two, h_one]
    norm_num
  have hlog_sq_bound : Real.log ((n : ℝ) + 2) ^ 2 ≤
      16 * Real.sqrt 2 * ((n : ℝ) + 1) ^ ((1 : ℝ) / 2) := by
    exact hlog4.trans_eq hlog5
  have htarget_nonneg : 0 ≤
      (4 * (2 : ℝ) ^ ((1 : ℝ) / 4) * D) * ((n : ℝ) + 1) ^ (-(5 / 4 : ℝ)) := by
    positivity
  have hsq : D ^ 2 * (Real.log (↑n + 2)) ^ 2 / (↑n + 1) ^ 3 ≤
      ((4 * (2 : ℝ) ^ ((1 : ℝ) / 4) * D) * ((n : ℝ) + 1) ^ (-(5 / 4 : ℝ))) ^ 2 := by
    have h_div : ((n : ℝ) + 1) ^ ((1 : ℝ) / 2) / ((n : ℝ) + 1) ^ 3 =
        ((n : ℝ) + 1) ^ (-(5 / 2 : ℝ)) := by
      rw [← Real.rpow_sub_natCast' hn1.le (by norm_num : (1 : ℝ) / 2 - 3 ≠ 0)]
      norm_num
    have h_const_sq : (4 * (2 : ℝ) ^ ((1 : ℝ) / 4) * D) ^ 2 =
        16 * Real.sqrt 2 * D ^ 2 := by
      rw [mul_pow, mul_pow]
      have h_two : ((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 = Real.sqrt 2 := by
        rw [Real.sqrt_eq_rpow, sq, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        norm_num
      rw [h_two]
      ring
    have h_rpow_sq : (((n : ℝ) + 1) ^ (-(5 / 4 : ℝ))) ^ 2 =
        ((n : ℝ) + 1) ^ (-(5 / 2 : ℝ)) := by
      rw [sq, ← Real.rpow_add hn1]
      norm_num
    calc
      D ^ 2 * (Real.log (↑n + 2)) ^ 2 / (↑n + 1) ^ 3
          ≤ D ^ 2 * (16 * Real.sqrt 2 * ((n : ℝ) + 1) ^ ((1 : ℝ) / 2)) / (↑n + 1) ^ 3 := by
              exact div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_left hlog_sq_bound (by positivity))
                (by positivity)
      _ = D ^ 2 * (16 * Real.sqrt 2) * (((n : ℝ) + 1) ^ ((1 : ℝ) / 2) / ((n : ℝ) + 1) ^ 3) := by
            ring
      _ = D ^ 2 * (16 * Real.sqrt 2) * ((n : ℝ) + 1) ^ (-(5 / 2 : ℝ)) := by
            rw [h_div]
      _ = (16 * Real.sqrt 2 * D ^ 2) * ((n : ℝ) + 1) ^ (-(5 / 2 : ℝ)) := by
            ring
      _ = (4 * (2 : ℝ) ^ ((1 : ℝ) / 4) * D) ^ 2 * (((n : ℝ) + 1) ^ (-(5 / 4 : ℝ))) ^ 2 := by
            rw [h_const_sq, h_rpow_sq]
      _ = ((4 * (2 : ℝ) ^ ((1 : ℝ) / 4) * D) * ((n : ℝ) + 1) ^ (-(5 / 4 : ℝ))) ^ 2 := by
            ring_nf
  exact (Real.sqrt_le_iff).2 ⟨htarget_nonneg, hsq⟩

/-- The L¹ increments of the cutoff interaction along the canonical UV cutoff
    sequence are summable: Σ_n E[|V_{κ_{n+1}} - V_{κ_n}|] < ∞.

    This is the key analytical estimate for a.e. convergence. It follows from
    the L² increment rate bound (`gap_interactionCutoff_standardSeq_L2_increment_rate`)
    via Cauchy-Schwarz: E[|X|] ≤ ‖X‖₂ under a probability measure.

    Reference: Simon, "P(φ)₂", Chapter II (Theorem II.11). -/
theorem gap_interactionCutoff_standardSeq_summable_L1_increments
    (params : Phi4Params) (Λ : Rectangle) :
    Summable (fun n : ℕ =>
      ∫ ω : FieldConfig2D,
        |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω -
         interactionCutoff params Λ (standardUVCutoffSeq n) ω|
        ∂(freeFieldMeasure params.mass params.mass_pos)) := by
  set μ := freeFieldMeasure params.mass params.mass_pos
  -- Get the L² rate bound
  obtain ⟨D, hD, h_L2_rate⟩ :=
    gap_interactionCutoff_standardSeq_L2_increment_rate params Λ
  -- Each cutoff is L², hence differences are integrable
  have hf_int : ∀ n, Integrable
      (fun ω => interactionCutoff params Λ (standardUVCutoffSeq n) ω) μ :=
    fun n => (interactionCutoff_memLp_two params Λ
      (standardUVCutoffSeq n)).integrable one_le_two
  have hdiff_int : ∀ n, Integrable (fun ω =>
      interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω -
      interactionCutoff params Λ (standardUVCutoffSeq n) ω) μ :=
    fun n => (hf_int (n + 1)).sub (hf_int n)
  -- Each L¹ increment ≤ √(L² rate bound)
  have hdiff_sq_int : ∀ n, Integrable (fun ω =>
      (interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω -
       interactionCutoff params Λ (standardUVCutoffSeq n) ω) ^ 2) μ :=
    fun n => ((interactionCutoff_memLp_two params Λ
      (standardUVCutoffSeq (n + 1))).sub
      (interactionCutoff_memLp_two params Λ
        (standardUVCutoffSeq n))).integrable_norm_rpow
      (by simp) (by simp) |>.congr
      (by filter_upwards with ω
          simp [Real.norm_eq_abs, ENNReal.toReal_ofNat])
  have h_bound : ∀ n, ∫ ω,
      |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω -
       interactionCutoff params Λ (standardUVCutoffSeq n) ω| ∂μ ≤
      Real.sqrt (D ^ 2 * (Real.log (↑n + 2)) ^ 2 / (↑n + 1) ^ 3) := by
    intro n
    calc ∫ ω, |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω -
           interactionCutoff params Λ (standardUVCutoffSeq n) ω| ∂μ
        ≤ Real.sqrt (∫ ω, (interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω -
            interactionCutoff params Λ (standardUVCutoffSeq n) ω) ^ 2 ∂μ) :=
          integral_abs_le_sqrt_integral_sq (hdiff_int n) (hdiff_sq_int n)
      _ ≤ Real.sqrt (D ^ 2 * (Real.log (↑n + 2)) ^ 2 / (↑n + 1) ^ 3) :=
          Real.sqrt_le_sqrt (h_L2_rate n)
  -- The bound sequence is summable
  refine Summable.of_nonneg_of_le
    (fun n => integral_nonneg (fun ω => abs_nonneg _)) h_bound ?_
  -- Σ √(D²·log²(n+2)/(n+1)³) = Σ D·log(n+2)/(n+1)^{3/2} is summable
  exact summable_sqrt_log_sq_div_cube D hD

/-- Sequence-level a.e. convergence: V_{κ_n} → V a.e. along the canonical cutoff
    sequence `standardUVCutoffSeq n = ⟨n+1, ...⟩`.

    This is the natural first target: the Fatou bridge only needs discrete
    convergence, and `interaction` is defined as `Filter.limsup` of the sequence,
    so convergence holds whenever the limsup equals the limit.

    Strategy: From the summability of L¹ increments
    (`gap_interactionCutoff_standardSeq_summable_L1_increments`), we get
    E[Σ_n |V_{n+1} - V_n|] < ∞ by Tonelli/MCT, hence Σ_n |V_{n+1} - V_n| < ∞
    a.e. This gives absolute convergence of the telescoping series, so V_n
    converges a.e. The limit equals `interaction` (= limsup) by
    `Filter.Tendsto.limsup_eq`. -/
theorem gap_interactionCutoff_standardSeq_ae_convergence
    (params : Phi4Params) (Λ : Rectangle) :
    ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
      Filter.Tendsto
        (fun n : ℕ => interactionCutoff params Λ (standardUVCutoffSeq n) ω)
        Filter.atTop
        (nhds (interaction params Λ ω)) := by
  set μ := freeFieldMeasure params.mass params.mass_pos
  set f : ℕ → FieldConfig2D → ℝ := fun n ω =>
    interactionCutoff params Λ (standardUVCutoffSeq n) ω
  have h_summable := gap_interactionCutoff_standardSeq_summable_L1_increments params Λ
  -- Step 1: from summable L¹ increments, derive a.e. pointwise absolute summability
  -- by MCT/Tonelli: E[∑|Δ_n|] = ∑E[|Δ_n|] < ∞ ⟹ ∑|Δ_n(ω)| < ∞ a.e.
  have hf_meas : ∀ n, Measurable (f n) := fun n =>
    (interactionCutoff_stronglyMeasurable params Λ (standardUVCutoffSeq n)).measurable
  have h_ae_abs_summable : ∀ᵐ ω ∂μ,
      Summable (fun n => |f (n + 1) ω - f n ω|) := by
    -- Use lintegral_tsum + ae_lt_top
    have hdiff_meas : ∀ n, Measurable (fun ω => (‖f (n + 1) ω - f n ω‖₊ : ℝ≥0∞)) :=
      fun n => ((hf_meas (n + 1)).sub (hf_meas n)).nnnorm.coe_nnreal_ennreal
    have h_lintegral_eq : ∫⁻ ω, ∑' n, (‖f (n + 1) ω - f n ω‖₊ : ℝ≥0∞) ∂μ =
        ∑' n, ∫⁻ ω, (‖f (n + 1) ω - f n ω‖₊ : ℝ≥0∞) ∂μ :=
      lintegral_tsum (fun n => (hdiff_meas n).aemeasurable)
    -- Each f_n is L², hence integrable; differences are integrable
    have hf_integrable : ∀ n, Integrable (f n) μ :=
      fun n => (interactionCutoff_memLp_two params Λ (standardUVCutoffSeq n)).integrable one_le_two
    have hdiff_integrable : ∀ n, Integrable (fun ω => f (n + 1) ω - f n ω) μ :=
      fun n => (hf_integrable (n + 1)).sub (hf_integrable n)
    have h_tsum_ne_top : ∑' n, ∫⁻ ω, (‖f (n + 1) ω - f n ω‖₊ : ℝ≥0∞) ∂μ ≠ ⊤ := by
      -- Convert each lintegral to ENNReal.ofReal (∫ ‖Δ_n‖ dμ) via lintegral_coe_eq_integral
      have h_eq : ∀ n, ∫⁻ ω, (‖f (n + 1) ω - f n ω‖₊ : ℝ≥0∞) ∂μ =
          ENNReal.ofReal (∫ ω, ‖f (n + 1) ω - f n ω‖ ∂μ) :=
        fun n => lintegral_coe_eq_integral _ ((hdiff_integrable n).norm)
      simp_rw [h_eq]
      -- ∑' n, ENNReal.ofReal (∫ ‖Δ_n‖ dμ) ≠ ⊤
      have h_nn : ∀ n, 0 ≤ ∫ ω, ‖f (n + 1) ω - f n ω‖ ∂μ :=
        fun n => integral_nonneg (fun ω => norm_nonneg _)
      simp_rw [ENNReal.ofReal_eq_coe_nnreal (h_nn _)]
      rw [ENNReal.tsum_coe_ne_top_iff_summable]
      refine NNReal.summable_coe.1 ?_
      simp only [NNReal.coe_mk]
      simp_rw [Real.norm_eq_abs]
      exact h_summable
    have h_lintegral_ne_top : ∫⁻ ω, ∑' n, (‖f (n + 1) ω - f n ω‖₊ : ℝ≥0∞) ∂μ ≠ ⊤ :=
      h_lintegral_eq ▸ h_tsum_ne_top
    have h_ae_lt_top : ∀ᵐ ω ∂μ, ∑' n, (‖f (n + 1) ω - f n ω‖₊ : ℝ≥0∞) < ⊤ :=
      ae_lt_top (Measurable.ennreal_tsum hdiff_meas) h_lintegral_ne_top
    filter_upwards [h_ae_lt_top] with ω hω
    have hω' : ∑' n, (‖f (n + 1) ω - f n ω‖₊ : ℝ≥0∞) ≠ ⊤ := ne_of_lt hω
    rw [ENNReal.tsum_coe_ne_top_iff_summable] at hω'
    have h_nnnorm_summable := NNReal.summable_coe.2 hω'
    simp only [coe_nnnorm, Real.norm_eq_abs] at h_nnnorm_summable
    exact h_nnnorm_summable
  -- Step 2: for a.e. ω with absolutely summable differences, the sequence converges
  filter_upwards [h_ae_abs_summable] with ω h_abs_sum
  -- Cauchy from summable dist
  have h_summable_dist : Summable (fun n => dist (f n ω) (f n.succ ω)) := by
    refine h_abs_sum.congr (fun n => ?_)
    rw [Real.dist_eq, abs_sub_comm]
  have h_cauchy : CauchySeq (fun n => f n ω) :=
    cauchySeq_of_summable_dist h_summable_dist
  -- Complete → convergent
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete h_cauchy
  -- The limit equals the limsup (= interaction)
  have hL_eq : interaction params Λ ω = L := by
    unfold interaction
    exact hL.limsup_eq
  rw [hL_eq]
  exact hL

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

/-- If the successive `L²` norms of `f_{n+1} - f_n` are summable and `f_n → g`
    a.e., then `g ∈ L²`. This is the structural bridge needed for the discrete
    UV-cutoff route. -/
private theorem memLp_two_of_tendsto_ae_of_summable_lpNorm_sub
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : ℕ → α → ℝ} {g : α → ℝ}
    (hf : ∀ n, MemLp (f n) 2 μ)
    (h_lim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (nhds (g x)))
    {d : ℕ → ℝ} (hd_sum : Summable d)
    (h_step : ∀ n, lpNorm (fun x => f (n + 1) x - f n x) 2 μ ≤ d n) :
    MemLp g 2 μ := by
  let F : ℕ → α →₂[μ] ℝ := fun n => (hf n).toLp (f n)
  have hdist : ∀ n, dist (F n) (F (n + 1)) ≤ d n := by
    intro n
    rw [dist_comm, dist_eq_norm]
    have hsub_mem : MemLp (fun x => f (n + 1) x - f n x) 2 μ := (hf (n + 1)).sub (hf n)
    have hsub_eq_toLp : (Lp.memLp (F (n + 1) - F n)).toLp (fun x => (F (n + 1) - F n) x) =
        hsub_mem.toLp (fun x => f (n + 1) x - f n x) := by
      apply (MemLp.toLp_eq_toLp_iff (Lp.memLp (F (n + 1) - F n)) hsub_mem).2
      filter_upwards [Lp.coeFn_sub (F (n + 1)) (F n), (hf (n + 1)).coeFn_toLp,
        (hf n).coeFn_toLp] with x hx h1 h0
      calc
        (F (n + 1) - F n) x = F (n + 1) x - F n x := by simpa using hx
        _ = f (n + 1) x - f n x := by rw [h1, h0]
    have hsub_eq : F (n + 1) - F n = hsub_mem.toLp (fun x => f (n + 1) x - f n x) := by
      simpa using (Lp.toLp_coeFn (F (n + 1) - F n) (Lp.memLp (F (n + 1) - F n))).symm.trans
        hsub_eq_toLp
    rw [hsub_eq, Lp.norm_toLp, MeasureTheory.toReal_eLpNorm hsub_mem.aestronglyMeasurable]
    exact h_step n
  have h_cauchy : CauchySeq F :=
    cauchySeq_of_dist_le_of_summable d hdist hd_sum
  obtain ⟨G, hG⟩ := cauchySeq_tendsto_of_complete h_cauchy
  have h_meas_in_measure : TendstoInMeasure μ (fun n => F n) atTop G :=
    tendstoInMeasure_of_tendsto_Lp hG
  have hFn_in_measure : TendstoInMeasure μ f atTop G := by
    exact h_meas_in_measure.congr_left (fun n => (hf n).coeFn_toLp)
  have hg_in_measure : TendstoInMeasure μ f atTop g :=
    tendstoInMeasure_of_tendsto_ae (fun n => (hf n).aestronglyMeasurable) h_lim
  have h_ae : (G : α → ℝ) =ᵐ[μ] g := tendstoInMeasure_ae_unique hFn_in_measure hg_in_measure
  exact MemLp.ae_eq h_ae (Lp.memLp G)

/-- Convert the shellwise `L²` increment rate into a bound on the real-valued
    `lpNorm` of the successive cutoff differences. -/
private theorem interactionCutoff_standardSeq_lpNorm_sub_le
    (params : Phi4Params) (Λ : Rectangle) {D : ℝ}
    (h_rate : ∀ n : ℕ,
      ∫ ω : FieldConfig2D,
        (interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω -
         interactionCutoff params Λ (standardUVCutoffSeq n) ω) ^ 2
        ∂(freeFieldMeasure params.mass params.mass_pos)
      ≤ D ^ 2 * (Real.log (n + 2)) ^ 2 / (n + 1) ^ 3) :
    ∀ n : ℕ,
      lpNorm
        (fun ω : FieldConfig2D =>
          interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω -
          interactionCutoff params Λ (standardUVCutoffSeq n) ω)
        2 (freeFieldMeasure params.mass params.mass_pos)
      ≤ Real.sqrt (D ^ 2 * (Real.log (n + 2)) ^ 2 / (n + 1) ^ 3) := by
  intro n
  have hdiff_mem : MemLp
      (fun ω : FieldConfig2D =>
        interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω -
        interactionCutoff params Λ (standardUVCutoffSeq n) ω)
      2 (freeFieldMeasure params.mass params.mass_pos) :=
    ((interactionCutoff_memLp_two params Λ (standardUVCutoffSeq (n + 1))).sub
      (interactionCutoff_memLp_two params Λ (standardUVCutoffSeq n)))
  rw [lpNorm_eq_integral_norm_rpow_toReal two_ne_zero ENNReal.ofNat_ne_top
    hdiff_mem.aestronglyMeasurable]
  have h_sq :
      ∫ ω : FieldConfig2D,
          ‖interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω -
            interactionCutoff params Λ (standardUVCutoffSeq n) ω‖ ^ (2 : ℝ)
        ∂(freeFieldMeasure params.mass params.mass_pos)
      ≤ D ^ 2 * (Real.log (n + 2)) ^ 2 / (n + 1) ^ 3 := by
    simpa [sq_abs] using h_rate n
  have h_nonneg : 0 ≤
      ∫ ω : FieldConfig2D,
          ‖interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω -
            interactionCutoff params Λ (standardUVCutoffSeq n) ω‖ ^ (2 : ℝ)
        ∂(freeFieldMeasure params.mass params.mass_pos) := by
    exact integral_nonneg (fun _ => by positivity)
  have := Real.rpow_le_rpow h_nonneg h_sq (by norm_num : 0 ≤ (1 / 2 : ℝ))
  simpa [Real.sqrt_eq_rpow, one_div] using this

/-- Square integrability of the limiting interaction.
    Strategy: from L² convergence (Vκ → V in L²), the limit V ∈ L² by completeness.
    Concretely: V² ≤ 2(V - Vκ)² + 2Vκ² pointwise, so ∫V² ≤ 2∫(V-Vκ)² + 2∫Vκ² < ∞. -/
theorem gap_interaction_sq_integrable (params : Phi4Params) (Λ : Rectangle) :
    Integrable (fun ω => (interaction params Λ ω) ^ 2)
      (freeFieldMeasure params.mass params.mass_pos) := by
  obtain ⟨D, hD, h_rate⟩ := gap_interactionCutoff_standardSeq_L2_increment_rate params Λ
  have h_mem : MemLp (interaction params Λ) 2 (freeFieldMeasure params.mass params.mass_pos) := by
    apply memLp_two_of_tendsto_ae_of_summable_lpNorm_sub
      (hf := fun n => interactionCutoff_memLp_two params Λ (standardUVCutoffSeq n))
      (h_lim := gap_interactionCutoff_standardSeq_ae_convergence params Λ)
      (hd_sum := summable_sqrt_log_sq_div_cube D hD)
    intro n
    exact interactionCutoff_standardSeq_lpNorm_sub_le params Λ h_rate n
  exact (memLp_two_iff_integrable_sq (gap_interaction_aestronglyMeasurable params Λ)).1 h_mem

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

/-- Markov's inequality at even moment order: for a measurable real-valued
function `Y` and `j ≥ 1`, `P(|Y| > 1)` is bounded by the `2j`-th moment. -/
theorem markov_even_moment
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y : Ω → ℝ} (j : ℕ)
    (hint : Integrable (fun ω => |Y ω| ^ (2 * j)) μ) :
    μ {ω | 1 < |Y ω|} ≤ ENNReal.ofReal (∫ ω, |Y ω| ^ (2 * j) ∂μ) := by
  have hsub : {ω | 1 < |Y ω|} ⊆ {ω | (1 : ℝ) ≤ |Y ω| ^ (2 * j)} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    exact one_le_pow₀ (le_of_lt hω)
  calc
    μ {ω | 1 < |Y ω|}
      ≤ μ {ω | (1 : ℝ) ≤ |Y ω| ^ (2 * j)} := measure_mono hsub
    _ ≤ ENNReal.ofReal (∫ ω, |Y ω| ^ (2 * j) ∂μ) :=
        hint.measure_le_integral
          (ae_of_all _ (fun ω => pow_nonneg (abs_nonneg _) _))
          (fun ω hω => hω)

/-- `4 - log 16` is positive, since `16 < exp 4`. This is the decay exponent
appearing in the Markov optimization step. -/
private theorem four_sub_log_sixteen_pos : 0 < 4 - Real.log 16 := by
  have : Real.log 16 < 4 := by
    rw [show (4 : ℝ) = Real.log (Real.exp 4) from (Real.log_exp 4).symm]
    exact Real.log_lt_log (by positivity) (by
      calc (16 : ℝ) = 2 ^ 4 := by norm_num
        _ < Real.exp 1 ^ 4 :=
          pow_lt_pow_left₀ Real.exp_one_gt_two (by norm_num) (by norm_num)
        _ = Real.exp 4 := by rw [← Real.exp_nat_mul]; norm_num)
  linarith

/-- Markov optimization: when the even moments satisfy the hypercontractive-type
growth `((C j)^4 * ε^2)^j`, one can choose an optimal integer moment order
producing a double-exponential decay scale `exp(-c / sqrt ε)`. -/
theorem markov_optimization_exists_j
    (C : ℝ) (hC : 0 < C) (ε : ℝ) (hε : 0 < ε)
    (hε_small : ε ≤ 1 / (Real.exp 1 * C) ^ 2) :
    ∃ (c : ℝ) (j : ℕ), 0 < c ∧ 0 < j ∧
      (C * ↑j) ^ (4 * j) * ε ^ (2 * j) ≤ Real.exp (-(c / Real.sqrt ε)) := by
  set e₁ := Real.exp 1
  set β := 4 - Real.log 16
  set j_real := 1 / (e₁ * C * Real.sqrt ε)
  set j := Nat.ceil j_real
  set c := β / (e₁ * C)
  refine ⟨c, j, ?_, ?_, ?_⟩
  · exact div_pos four_sub_log_sixteen_pos (mul_pos (Real.exp_pos 1) hC)
  ·
    have hj_real_pos : 0 < j_real :=
      div_pos one_pos (mul_pos (mul_pos (Real.exp_pos 1) hC) (Real.sqrt_pos.mpr hε))
    exact Nat.ceil_pos.mpr hj_real_pos
  ·
    have he₁_pos : 0 < e₁ := Real.exp_pos 1
    have hsqrt_pos : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
    have heC_pos : 0 < e₁ * C := mul_pos he₁_pos hC
    have hj_real_pos : 0 < j_real :=
      div_pos one_pos (mul_pos heC_pos hsqrt_pos)
    have hj_real_ge_one : 1 ≤ j_real := by
      rw [one_le_div (mul_pos heC_pos hsqrt_pos)]
      have hsq_le : Real.sqrt ε ≤ 1 / (e₁ * C) := by
        rw [Real.sqrt_le_left]
        · rwa [div_pow, one_pow]
        · exact div_nonneg (by norm_num) (le_of_lt heC_pos)
      calc e₁ * C * Real.sqrt ε
          ≤ e₁ * C * (1 / (e₁ * C)) :=
            mul_le_mul_of_nonneg_left hsq_le (le_of_lt heC_pos)
        _ = 1 := by field_simp
    have hj_le : (j : ℝ) ≤ 2 * j_real := by
      have : (j : ℝ) ≤ j_real + 1 :=
        le_of_lt (Nat.ceil_lt_add_one (le_of_lt hj_real_pos))
      linarith
    have hj_ge : j_real ≤ (j : ℝ) := Nat.le_ceil j_real
    have hCj_le : C * (j : ℝ) ≤ 2 / (e₁ * Real.sqrt ε) := by
      calc C * (j : ℝ) ≤ C * (2 * j_real) :=
              mul_le_mul_of_nonneg_left hj_le (le_of_lt hC)
        _ = 2 * (C / (e₁ * C * Real.sqrt ε)) := by ring
        _ = 2 / (e₁ * Real.sqrt ε) := by
            congr 1
            field_simp
    have hbase_le : (C * (j : ℝ)) ^ 4 * ε ^ 2 ≤ 16 / e₁ ^ 4 := by
      have h1 : (C * (j : ℝ)) ^ 4 ≤ (2 / (e₁ * Real.sqrt ε)) ^ 4 :=
        pow_le_pow_left₀ (by positivity) hCj_le 4
      have hsq : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt (le_of_lt hε)
      have h2 : (2 / (e₁ * Real.sqrt ε)) ^ 4 * ε ^ 2 = 16 / e₁ ^ 4 := by
        have he₁_ne : e₁ ≠ 0 := ne_of_gt he₁_pos
        have hsqrt_ne : Real.sqrt ε ≠ 0 := ne_of_gt hsqrt_pos
        field_simp
        rw [show (Real.sqrt ε) ^ 4 = ((Real.sqrt ε) ^ 2) ^ 2 from by ring, hsq]
        ring
      linarith [mul_le_mul_of_nonneg_right h1 (sq_nonneg ε)]
    have hrewrite : (C * (j : ℝ)) ^ (4 * j) * ε ^ (2 * j) =
        ((C * (j : ℝ)) ^ 4 * ε ^ 2) ^ (j : ℕ) := by
      rw [mul_pow, pow_mul, pow_mul, pow_mul]
      ring
    rw [hrewrite]
    have hbase_nonneg : 0 ≤ (C * (j : ℝ)) ^ 4 * ε ^ 2 := by positivity
    have hpow_le : ((C * (j : ℝ)) ^ 4 * ε ^ 2) ^ j ≤ (16 / e₁ ^ 4) ^ j :=
      pow_le_pow_left₀ hbase_nonneg hbase_le j
    have hlog_ratio : Real.log (16 / e₁ ^ 4) = Real.log 16 - 4 := by
      rw [Real.log_div (by positivity : (16 : ℝ) ≠ 0) (by positivity : e₁ ^ 4 ≠ 0)]
      congr 1
      rw [Real.log_pow, Real.log_exp]
      norm_num
    have hratio_pos : 0 < 16 / e₁ ^ 4 := by positivity
    have hratio_eq : 16 / e₁ ^ 4 = Real.exp (-β) := by
      rw [← Real.exp_log hratio_pos, hlog_ratio]
      congr 1
      ring
    have hpow_eq : (16 / e₁ ^ 4) ^ j = Real.exp (-(β * (j : ℝ))) := by
      rw [hratio_eq, ← Real.exp_nat_mul, mul_comm]
      congr 1
      ring
    have hβj_ge : β * j_real ≤ β * (j : ℝ) :=
      mul_le_mul_of_nonneg_left hj_ge (le_of_lt four_sub_log_sixteen_pos)
    have hβj_real_eq : β * j_real = c / Real.sqrt ε := by
      simp only [c, j_real]
      field_simp
    have hexp_le : Real.exp (-(β * (j : ℝ))) ≤ Real.exp (-(c / Real.sqrt ε)) := by
      apply Real.exp_le_exp_of_le
      linarith
    linarith [hpow_le, hpow_eq, hexp_le]

/-- Markov's inequality with optimized moment order turns hypercontractive even
moment growth into a double-exponential tail bound. -/
theorem markov_hypercontractive_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y : Ω → ℝ} {C σ : ℝ} (hC : 0 < C) (hσ : 0 < σ)
    (hmoment : ∀ j : ℕ, 0 < j →
      Integrable (fun ω => |Y ω| ^ (2 * j)) μ ∧
      ∫ ω, |Y ω| ^ (2 * j) ∂μ ≤ (C * ↑j) ^ (4 * j) * σ ^ (2 * j))
    (hσ_small : σ ≤ 1 / (Real.exp 1 * C) ^ 2) :
    ∃ c : ℝ, 0 < c ∧
      μ {ω | 1 < |Y ω|} ≤ ENNReal.ofReal (Real.exp (-(c / Real.sqrt σ))) := by
  obtain ⟨c, j, hc, hj, hopt⟩ := markov_optimization_exists_j C hC σ hσ hσ_small
  obtain ⟨hint, hmom⟩ := hmoment j hj
  refine ⟨c, hc, ?_⟩
  calc
    μ {ω | 1 < |Y ω|}
      ≤ ENNReal.ofReal (∫ ω, |Y ω| ^ (2 * j) ∂μ) := markov_even_moment j hint
    _ ≤ ENNReal.ofReal ((C * ↑j) ^ (4 * j) * σ ^ (2 * j)) :=
        ENNReal.ofReal_le_ofReal hmom
    _ ≤ ENNReal.ofReal (Real.exp (-(c / Real.sqrt σ))) :=
        ENNReal.ofReal_le_ofReal hopt

/-- **Sub-gap A: Double-exponential tail bound for the cutoff interaction.**

    For all t ≥ 0 and all UV cutoffs κ:
      P(V_{Λ,κ} < -t) ≤ A · exp(-B · exp(C · √t))
    where A, B, C > 0 depend on λ, |Λ|, m but NOT on κ.

    This is the core of Nelson's argument (Simon Theorem V.14). The proof uses:
    1. Covariance splitting: split φ_κ = φ_{κ₀} + ψ with κ₀ = exp(K√t)
    2. Wick lower bound: V_{κ₀} ≥ -6λc_{κ₀}²|Λ| ≥ -t (by choice of κ₀)
    3. Hence P(V_κ < -t-1) ≤ P(V_κ - V_{κ₀} < -1)
    4. Moment bound: E[(V_κ - V_{κ₀})^{2j}] ≤ (4j²)^{2j} ‖V_κ - V_{κ₀}‖₂^{2j}
       (Gaussian polynomial moment equivalence for 4th-chaos elements)
    5. L² bound: ‖V_κ - V_{κ₀}‖₂ ≤ ε(κ₀) with ε(κ₀) ~ κ₀^{-δ}
    6. Optimize j to get double-exponential tail decay. -/
theorem gap_interaction_double_exponential_tail_bound
    (params : Phi4Params) (Λ : Rectangle) :
    ∃ A B C : ℝ, 0 < A ∧ 0 < B ∧ 0 < C ∧ ∀ (κ : UVCutoff) (t : ℝ), 0 ≤ t →
      (freeFieldMeasure params.mass params.mass_pos)
        {ω : FieldConfig2D | interactionCutoff params Λ κ ω < -t} ≤
      ENNReal.ofReal (A * Real.exp (-B * Real.exp (C * Real.sqrt t))) := by
  sorry

/-- The improper integral ∫₀^∞ exp(pt - B·exp(C·√t)) dt is finite for all p, B, C > 0.
    Proof: for t ≥ T₀, B·exp(C·√t) ≥ (p+1)t, so the integrand ≤ exp(-t). -/
theorem integral_exp_linear_minus_double_exp_finite
    {p B C : ℝ} (hB : 0 < B) (hC : 0 < C) :
    IntegrableOn (fun t => Real.exp (p * t - B * Real.exp (C * Real.sqrt t)))
      (Set.Ioi 0) volume := by
  set T₀ := max 1 (24 * (p + 1) / (B * C ^ 4)) with hT₀_def
  have hT₀_pos : 0 < T₀ := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hBC4_pos : 0 < B * C ^ 4 := mul_pos hB (pow_pos hC 4)
  have hexp_quartic : ∀ t : ℝ, 0 ≤ t →
      C ^ 4 * t ^ 2 / 24 ≤ Real.exp (C * Real.sqrt t) := by
    intro t ht
    have hsqrt_nn : 0 ≤ C * Real.sqrt t := mul_nonneg (le_of_lt hC) (Real.sqrt_nonneg t)
    have h1 := Real.pow_div_factorial_le_exp (C * Real.sqrt t) hsqrt_nn 4
    have h2 : (C * Real.sqrt t) ^ 4 = C ^ 4 * t ^ 2 := by
      rw [mul_pow]; congr 1; rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt ht]
    rw [h2] at h1; norm_num [Nat.factorial] at h1; linarith
  have h_dom : ∀ t ≥ T₀, p * t - B * Real.exp (C * Real.sqrt t) ≤ -t := by
    intro t ht
    have ht_pos : 0 ≤ t := le_of_lt (lt_of_lt_of_le hT₀_pos ht)
    have ht_T₀ : t ≥ 24 * (p + 1) / (B * C ^ 4) := le_trans (le_max_right _ _) ht
    have h_coeff : (p + 1) * 24 ≤ B * C ^ 4 * t := by
      have := div_le_iff₀ hBC4_pos |>.mp ht_T₀; linarith
    have h_exp := hexp_quartic t ht_pos
    have h_B_exp : B * (C ^ 4 * t ^ 2 / 24) ≤ B * Real.exp (C * Real.sqrt t) :=
      mul_le_mul_of_nonneg_left h_exp (le_of_lt hB)
    nlinarith
  have hf_cont : Continuous (fun t : ℝ => Real.exp (p * t - B * Real.exp (C * Real.sqrt t))) :=
    by fun_prop
  have h_Ioi : IntegrableOn (fun t => Real.exp (p * t - B * Real.exp (C * Real.sqrt t)))
      (Set.Ioi T₀) volume := by
    apply Integrable.mono (exp_neg_integrableOn_Ioi T₀ one_pos)
      (hf_cont.aestronglyMeasurable.restrict)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (by linarith [h_dom t (Set.mem_Ioi.mp ht).le])
  have h_Ioc : IntegrableOn (fun t => Real.exp (p * t - B * Real.exp (C * Real.sqrt t)))
      (Set.Ioc 0 T₀) volume :=
    (hf_cont.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  rw [show Set.Ioi (0 : ℝ) = Set.Ioc 0 T₀ ∪ Set.Ioi T₀ from
    (Set.Ioc_union_Ioi_eq_Ioi (le_of_lt hT₀_pos)).symm]
  exact h_Ioc.union h_Ioi

/-- FTC: ∫₀^y p·exp(pt) dt = exp(py) - 1. -/
private theorem interval_integral_p_mul_exp (p y : ℝ) :
    ∫ t in (0 : ℝ)..y, p * Real.exp (p * t) = Real.exp (p * y) - 1 := by
  have hderiv : ∀ x ∈ Set.uIcc 0 y,
      HasDerivAt (fun t => Real.exp (p * t)) (p * Real.exp (p * x)) x := by
    intro x _
    exact ((by simpa using (hasDerivAt_id x).const_mul p :
      HasDerivAt (fun t => p * t) p x).exp.congr_deriv (by ring))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id'))).intervalIntegrable _ _)]
  simp [mul_zero]

/-- Pure-analysis lemma: if a random variable has double-exponential lower tail,
    then all negative exponential moments are finite.

    From the layer-cake identity:
      E[exp(-pX)] ≤ 1 + ∫₀^∞ p·exp(pt) · P(X < -t) dt
    and the double-exponential tail bound P(X < -t) ≤ A·exp(-B·exp(C·√t)):
      ∫₀^∞ p·exp(pt)·A·exp(-B·exp(C·√t)) dt < ∞
    because exp(C·√t) dominates pt for large t. -/
theorem neg_exp_moment_of_double_exponential_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X)
    {A B C_tail : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C_tail)
    (htail : ∀ t : ℝ, 0 ≤ t →
      μ {ω | X ω < -t} ≤ ENNReal.ofReal (A * Real.exp (-B * Real.exp (C_tail * Real.sqrt t))))
    (p : ℝ) (hp : 0 < p) :
    Integrable (fun ω => Real.exp (-(p * X ω))) μ ∧
    ∫ ω, Real.exp (-(p * X ω)) ∂μ ≤
      1 + p * A * ∫ t in Set.Ioi 0,
        Real.exp (p * t - B * Real.exp (C_tail * Real.sqrt t)) := by
  -- Abbreviations
  set g : ℝ → ℝ := fun t => p * Real.exp (p * t) with hg_def
  set f_tail : ℝ → ℝ := fun t =>
    p * A * Real.exp (p * t - B * Real.exp (C_tail * Real.sqrt t)) with hf_def
  -- FTC: ∫₀^{max(-x,0)} g = exp(p·max(-x,0)) - 1
  have hftc : ∀ ω : Ω, ∫ t in (0 : ℝ)..max (-X ω) 0, g t =
      Real.exp (p * max (-X ω) 0) - 1 :=
    fun ω => interval_integral_p_mul_exp p _
  have hI_nn : ∀ ω : Ω, 0 ≤ ∫ t in (0 : ℝ)..max (-X ω) 0, g t := fun ω => by
    rw [hftc]; linarith [Real.one_le_exp (mul_nonneg hp.le (le_max_right (-X ω) 0))]
  -- Layer-cake formula
  have hlc : ∫⁻ ω, ENNReal.ofReal (∫ t in (0 : ℝ)..max (-X ω) 0, g t) ∂μ =
      ∫⁻ t in Set.Ioi (0 : ℝ), μ {a | t < max (-X a) 0} * ENNReal.ofReal (g t) :=
    lintegral_comp_eq_lintegral_meas_lt_mul μ
      (by filter_upwards with ω; exact le_max_right _ _)
      ((hX.neg.max measurable_const).aemeasurable)
      (fun t _ => (continuous_const.mul (Real.continuous_exp.comp
        (continuous_const.mul continuous_id'))).intervalIntegrable _ _)
      (by filter_upwards with t; exact mul_nonneg hp.le (Real.exp_pos _).le)
  -- {max(-X,0) > t} = {X < -t} for t > 0
  have hset_eq : ∀ t : ℝ, 0 < t →
      μ {a : Ω | t < max (-X a) 0} = μ {a | X a < -t} := by
    intro t ht; congr 1; ext ω; simp only [Set.mem_setOf_eq]
    constructor
    · intro h; by_contra h_neg; push_neg at h_neg
      exact not_lt.mpr (max_le (by linarith) ht.le) h
    · intro h; exact lt_max_of_lt_left (by linarith)
  -- Tail integrand is IntegrableOn (Ioi 0)
  have hf_intOn : IntegrableOn f_tail (Set.Ioi 0) volume := by
    have := @integral_exp_linear_minus_double_exp_finite p B C_tail hB hC
    exact this.const_mul (p * A)
  -- *** Main lintegral bound ***
  -- ∫⁻ ofReal(exp(-pX)) ≤ 1 + ∫⁻_{t>0} ofReal(f_tail t)
  have h_lint_bound : ∫⁻ ω, ENNReal.ofReal (Real.exp (-(p * X ω))) ∂μ ≤
      1 + ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (f_tail t) := by
    calc ∫⁻ ω, ENNReal.ofReal (Real.exp (-(p * X ω))) ∂μ
        ≤ ∫⁻ ω, (1 + ENNReal.ofReal (∫ t in (0 : ℝ)..max (-X ω) 0, g t)) ∂μ := by
          apply lintegral_mono; intro ω; simp only
          rw [show (1 : ENNReal) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm,
              ← ENNReal.ofReal_add one_pos.le (hI_nn ω), hftc]
          apply ENNReal.ofReal_le_ofReal
          linarith [Real.exp_le_exp.2 (show -(p * X ω) ≤ p * max (-X ω) 0
            by nlinarith [le_max_left (-X ω) 0])]
      _ = 1 + ∫⁻ ω, ENNReal.ofReal (∫ t in (0 : ℝ)..max (-X ω) 0, g t) ∂μ := by
          rw [lintegral_add_left measurable_const]; simp [lintegral_const, measure_univ]
      _ = 1 + ∫⁻ t in Set.Ioi (0 : ℝ),
            μ {a | t < max (-X a) 0} * ENNReal.ofReal (g t) := by rw [hlc]
      _ = 1 + ∫⁻ t in Set.Ioi (0 : ℝ),
            μ {a | X a < -t} * ENNReal.ofReal (g t) := by
          congr 1; apply setLIntegral_congr_fun measurableSet_Ioi
          intro t ht; simp only [Set.mem_Ioi] at ht
          show μ {a | t < max (-X a) 0} * _ = μ {a | X a < -t} * _
          rw [hset_eq t ht]
      _ ≤ 1 + ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (f_tail t) := by
          apply add_le_add_right _ 1
          apply setLIntegral_mono (Measurable.ennreal_ofReal (by fun_prop))
          intro t ht
          have ht' := Set.mem_Ioi.mp ht
          calc μ {a | X a < -t} * ENNReal.ofReal (g t)
              ≤ ENNReal.ofReal (A * Real.exp (-B * Real.exp (C_tail * Real.sqrt t))) *
                ENNReal.ofReal (g t) :=
                mul_le_mul_left (htail t ht'.le) _
            _ = ENNReal.ofReal (A * Real.exp (-B * Real.exp (C_tail * Real.sqrt t)) * g t) :=
                (ENNReal.ofReal_mul (mul_nonneg hA.le (Real.exp_pos _).le)).symm
            _ = ENNReal.ofReal (f_tail t) := by
                congr 1; simp only [hg_def, hf_def]
                rw [show p * t - B * Real.exp (C_tail * Real.sqrt t) =
                  -B * Real.exp (C_tail * Real.sqrt t) + p * t from by ring, Real.exp_add]
                ring
  -- *** Convert to real integral ***
  -- The lintegral of ofReal(f_tail) equals ofReal(∫ f_tail) since f_tail ≥ 0 and integrable
  have h_lint_eq : ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (f_tail t) =
      ENNReal.ofReal (∫ t in Set.Ioi 0, f_tail t) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hf_intOn
      (by filter_upwards with t; exact mul_nonneg (mul_nonneg hp.le hA.le) (Real.exp_pos _).le)]
  -- The lintegral is finite
  have h_lint_ne_top : ∫⁻ ω, ENNReal.ofReal (Real.exp (-(p * X ω))) ∂μ ≠ ⊤ := by
    have h_rhs_ne_top : 1 + ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (f_tail t) ≠ ⊤ := by
      rw [h_lint_eq]
      exact ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.ofReal_ne_top⟩
    exact ne_top_of_le_ne_top h_rhs_ne_top h_lint_bound
  -- Integrability
  have h_integrable : Integrable (fun ω => Real.exp (-(p * X ω))) μ := by
    refine ⟨((hX.const_mul p).neg.exp).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    calc ∫⁻ a, ENNReal.ofReal ‖Real.exp (-(p * X a))‖ ∂μ
        = ∫⁻ a, ENNReal.ofReal (Real.exp (-(p * X a))) ∂μ := by
          congr 1; ext ω; rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      _ < ⊤ := h_lint_ne_top.lt_top
  refine ⟨h_integrable, ?_⟩
  -- Real integral bound
  have h_real : (∫ ω, Real.exp (-(p * X ω)) ∂μ : ℝ) =
      (∫⁻ ω, ENNReal.ofReal (Real.exp (-(p * X ω))) ∂μ).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (by filter_upwards with ω; exact (Real.exp_pos _).le)
      ((hX.const_mul p).neg.exp).aestronglyMeasurable]
  rw [h_real]
  have h_rhs_ne : 1 + ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (f_tail t) ≠ ⊤ := by
    rw [h_lint_eq]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.ofReal_ne_top⟩
  have h_rhs_val : (1 + ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (f_tail t)).toReal =
      1 + ∫ t in Set.Ioi 0, f_tail t := by
    rw [h_lint_eq, ENNReal.toReal_add ENNReal.one_ne_top ENNReal.ofReal_ne_top,
        ENNReal.toReal_one, ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ioi
          (fun t _ => mul_nonneg (mul_nonneg hp.le hA.le) (Real.exp_pos _).le))]
  rw [show 1 + p * A * ∫ t in Set.Ioi 0,
      Real.exp (p * t - B * Real.exp (C_tail * Real.sqrt t)) =
    1 + ∫ t in Set.Ioi 0, f_tail t from by
      simp only [hf_def]; rw [← integral_const_mul]]
  rw [← h_rhs_val]
  exact (ENNReal.toReal_le_toReal h_lint_ne_top h_rhs_ne).mpr h_lint_bound

/-- Bounded form of `neg_exp_moment_of_double_exponential_tail`: under a double-exponential
    lower tail bound, the negative exponential moment E[exp(-pX)] is bounded by some
    finite constant K. This decouples downstream uses from the specific layer-cake bound. -/
theorem neg_exp_moment_bounded_of_double_exponential_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X)
    {A B C_tail : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C_tail)
    (htail : ∀ t : ℝ, 0 ≤ t →
      μ {ω | X ω < -t} ≤ ENNReal.ofReal (A * Real.exp (-B * Real.exp (C_tail * Real.sqrt t))))
    (p : ℝ) (hp : 0 < p) :
    ∃ K : ℝ, 0 < K ∧
      Integrable (fun ω => Real.exp (-(p * X ω))) μ ∧
      ∫ ω, Real.exp (-(p * X ω)) ∂μ ≤ K := by
  obtain ⟨hint, hbound⟩ := neg_exp_moment_of_double_exponential_tail hX hA hB hC htail p hp
  refine ⟨1 + p * A * ∫ t in Set.Ioi 0,
    Real.exp (p * t - B * Real.exp (C_tail * Real.sqrt t)), ?_, hint, hbound⟩
  have hI := @integral_exp_linear_minus_double_exp_finite p B C_tail hB hC
  have : 0 ≤ p * A * ∫ t in Set.Ioi 0,
      Real.exp (p * t - B * Real.exp (C_tail * Real.sqrt t)) :=
    mul_nonneg (mul_nonneg hp.le hA.le)
      (setIntegral_nonneg measurableSet_Ioi (fun t _ => (Real.exp_pos _).le))
  linarith

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
  intro p hp
  -- Obtain double-exponential tail bound (uniform in κ)
  obtain ⟨A, B, C_tail, hA, hB, hC, htail⟩ :=
    gap_interaction_double_exponential_tail_bound params Λ
  -- The layer-cake integral is finite
  have hI := @integral_exp_linear_minus_double_exp_finite p B C_tail hB hC
  -- Set uniform bound
  set K := 1 + p * A * ∫ t in Set.Ioi 0,
    Real.exp (p * t - B * Real.exp (C_tail * Real.sqrt t))
  refine ⟨K, ?_, fun κ => ?_⟩
  · -- K > 0: K = 1 + (nonneg) ≥ 1 > 0
    have : 0 ≤ p * A * ∫ t in Set.Ioi 0,
        Real.exp (p * t - B * Real.exp (C_tail * Real.sqrt t)) :=
      mul_nonneg (mul_nonneg (le_of_lt hp) (le_of_lt hA))
        (setIntegral_nonneg measurableSet_Ioi (fun t _ => le_of_lt (Real.exp_pos _)))
    linarith
  · -- Apply neg_exp_moment to each cutoff
    have hX_meas : Measurable (interactionCutoff params Λ κ) :=
      (interactionCutoff_stronglyMeasurable params Λ κ).measurable
    exact neg_exp_moment_of_double_exponential_tail hX_meas hA hB hC
      (fun t ht => htail κ t ht) p hp

/-! ## Closing gap_hasExpInteractionLp

The WP1 endpoint `HasExpInteractionLp` (i.e., exp(-V_Λ) ∈ Lᵖ for all finite p)
is proved by Fatou's lemma applied to the cutoff approximations:

1. From `gap_interactionCutoff_standardSeq_ae_convergence`:
   V_{Λ,κ_n} → V_Λ a.e. along the canonical sequence, hence
   exp(-p V_{Λ,κ_n}) → exp(-p V_Λ) a.e. (continuity of exp).
2. From `gap_exp_neg_interaction_uniform_bound`: E[exp(-p V_{Λ,κ})] ≤ C
   uniformly in κ (Nelson's bound).
3. Fatou: ∫⁻ exp(-pV_Λ) ≤ liminf ∫⁻ exp(-pV_{Λ,κ_n}) ≤ C < ⊤.
4. AEStronglyMeasurable + finite eLpNorm → MemLp.

This route bypasses Part2/Part3 entirely and needs only two analytic inputs:
`gap_interactionCutoff_standardSeq_ae_convergence` and
`gap_exp_neg_interaction_uniform_bound`. -/

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

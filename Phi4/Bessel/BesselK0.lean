/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.Bessel.BesselK1

/-!
# Modified Bessel Function K₀

The modified Bessel function K₀(z) is defined via the integral representation
  K₀(z) = ∫₀^∞ exp(-z cosh(t)) dt

This is the Green's function kernel for the 2D massive scalar field:
  C(x,y) = (2π)⁻¹ K₀(m|x-y|)

## Main definitions

* `besselK0` - K₀(z) = ∫₀^∞ exp(-z cosh(t)) dt

## Main results

* `besselK0_pos` - K₀(z) > 0 for z > 0
* `besselK0_integrand_integrableOn` - integrability of the K₀ integrand
* `schwingerIntegral2D_eq_besselK0` - ∫₀^∞ (1/t) exp(-m²t - r²/(4t)) dt = 2K₀(mr)

## References

* Abramowitz-Stegun, Chapter 9
* [Glimm-Jaffe] Section 7.1 (the free covariance in d=2)
-/

open MeasureTheory Set Filter Asymptotics Real

noncomputable section

/-- The modified Bessel function K₀(z) via cosh integral representation.
    K₀(z) = ∫₀^∞ exp(-z cosh(t)) dt
    This is well-defined and positive for z > 0. -/
def besselK0 (z : ℝ) : ℝ :=
  ∫ t : ℝ in Ici 0, exp (-z * cosh t)

/-- The integrand for K₀ is integrable on [0,∞) for z > 0.
    Proof: For t ≥ 0, cosh(t) ≥ 1 + t²/2, so exp(-z cosh t) ≤ exp(-z) exp(-zt²/2).
    The Gaussian exp(-zt²/2) is integrable on [0,∞). -/
lemma besselK0_integrand_integrableOn (z : ℝ) (hz : 0 < z) :
    IntegrableOn (fun t => exp (-z * cosh t)) (Ici 0) volume := by
  set f : ℝ → ℝ := fun t => exp (-z * cosh t) with hf_def
  have hf_cont : Continuous f :=
    continuous_exp.comp (continuous_const.mul continuous_cosh)
  -- Split [0, ∞) = [0, 1] ∪ [1, ∞)
  have h_union : Ici (0 : ℝ) = Icc 0 1 ∪ Ici 1 := by
    ext x; simp only [mem_Ici, mem_union, mem_Icc]
    constructor
    · intro hx
      by_cases h : x ≤ 1
      · left; exact ⟨hx, h⟩
      · right; linarith
    · intro h; cases h with | inl h => exact h.1 | inr h => linarith
  rw [h_union]
  apply IntegrableOn.union
  -- On [0, 1]: continuous on compact → integrable
  · exact hf_cont.continuousOn.integrableOn_compact isCompact_Icc
  -- On [1, ∞): exp(-z cosh t) is O(exp(-t)) which is integrable
  · have h_int_Ioi : IntegrableOn f (Ioi 0) volume := by
      apply integrable_of_isBigO_exp_neg (b := 1) one_pos hf_cont.continuousOn
      rw [isBigO_iff]; use 1
      -- Show exp(-z cosh t) / exp(-t) → 0 as t → ∞
      have h_ratio_tendsto : Tendsto (fun t => f t / exp (-t)) atTop (nhds 0) := by
        have h_eq : ∀ t, f t / exp (-t) = exp (t - z * cosh t) := by
          intro t; simp only [f]; field_simp; rw [← exp_add]; ring_nf
        simp_rw [h_eq]
        apply tendsto_exp_atBot.comp
        -- Show t - z * cosh t → -∞
        -- Key: cosh t ≥ exp(t)/2, so z * cosh t ≥ z * exp(t)/2, so t - z*cosh(t) ≤ t - z*exp(t)/2 → -∞
        have hexp_inf : Tendsto (fun t : ℝ => z * exp t / 2) atTop atTop := by
          apply Tendsto.atTop_div_const (by linarith : (0 : ℝ) < 2)
          exact Tendsto.const_mul_atTop hz tendsto_exp_atTop
        have h_ratio : Tendsto (fun t : ℝ => t / exp t) atTop (nhds 0) := by
          have h := tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
          simp only [pow_one] at h
          convert h using 1; ext t; rw [exp_neg, div_eq_mul_inv]
        have h_scaled : Tendsto (fun t : ℝ => 2 / z * (t / exp t)) atTop (nhds (2 / z * 0)) :=
          h_ratio.const_mul (2 / z)
        simp only [mul_zero] at h_scaled
        have h_shifted : Tendsto (fun t : ℝ => 2 / z * (t / exp t) - 1) atTop (nhds (-1)) := by
          convert h_scaled.sub_const 1 using 1; simp
        have h_prod : Tendsto (fun t : ℝ => (z * exp t / 2) * (2 / z * (t / exp t) - 1))
            atTop atBot := Tendsto.atTop_mul_neg (by norm_num : (-1 : ℝ) < 0) hexp_inf h_shifted
        exact tendsto_atBot_mono (fun t => by
          have h_cosh_ge : cosh t ≥ exp t / 2 := by
            rw [cosh_eq]; have : exp (-t) ≥ 0 := exp_nonneg _; linarith
          calc t - z * cosh t ≤ t - z * (exp t / 2) := by
                linarith [mul_le_mul_of_nonneg_left h_cosh_ge hz.le]
            _ = _ := by field_simp) h_prod
      -- From ratio → 0, get eventually |f(t)| ≤ |exp(-t)|
      have h_eventually_le : ∀ᶠ t in atTop, f t ≤ exp (-1 * t) := by
        have h1 : ∀ᶠ t in atTop, |f t / exp (-t)| < 1 := by
          have := Metric.tendsto_nhds.mp h_ratio_tendsto 1 one_pos
          filter_upwards [this] with t ht
          simp only [Real.dist_eq, sub_zero] at ht; exact ht
        filter_upwards [h1] with t ht
        have hgt : 0 < exp (-t) := exp_pos _
        rw [abs_lt] at ht
        have : f t < exp (-t) := (div_lt_one hgt).mp ht.2
        simp only [neg_mul, one_mul]; linarith
      filter_upwards [h_eventually_le] with t ht
      rw [Real.norm_of_nonneg (exp_nonneg _), Real.norm_of_nonneg (exp_nonneg _)]
      simp only [one_mul]; exact ht
    apply h_int_Ioi.mono _ le_rfl
    intro x hx; simp only [mem_Ici] at hx; simp only [mem_Ioi]; linarith

/-- K₀(z) is positive for z > 0.
    The integrand exp(-z cosh t) is strictly positive and integrable, so the integral is positive. -/
lemma besselK0_pos (z : ℝ) (hz : 0 < z) : 0 < besselK0 z := by
  unfold besselK0
  set f : ℝ → ℝ := fun t => exp (-z * cosh t) with hf_def
  have hf_nonneg : ∀ t, 0 ≤ f t := fun t => exp_nonneg _
  have hf_pos : ∀ t, 0 < f t := fun t => exp_pos _
  have hf_int := besselK0_integrand_integrableOn z hz
  have h_support : Function.support f ∩ Ici 0 = Ici 0 := by
    ext t; simp only [Function.mem_support, mem_inter_iff, mem_Ici, ne_eq]
    exact ⟨fun ⟨_, ht⟩ => ht, fun ht => ⟨(hf_pos t).ne', ht⟩⟩
  have h_meas_pos : 0 < volume (Function.support f ∩ Ici 0) := by
    rw [h_support, Real.volume_Ici]; exact ENNReal.zero_lt_top
  rw [MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae
      (Eventually.of_forall hf_nonneg) hf_int]
  exact h_meas_pos

/-- The K₁ integrand is integrable on [0,∞) for z > 0.
    Extracted as a standalone lemma for use in comparisons. -/
lemma besselK1_integrand_integrableOn (z : ℝ) (hz : 0 < z) :
    IntegrableOn (fun t => exp (-z * cosh t) * cosh t) (Ici 0) volume := by
  -- K₁ integrand = K₀ integrand × cosh t. We use the same split strategy.
  set f : ℝ → ℝ := fun t => exp (-z * cosh t) * cosh t with hf_def
  have hf_cont : Continuous f := by
    apply Continuous.mul
    · exact continuous_exp.comp (continuous_const.mul continuous_cosh)
    · exact continuous_cosh
  have h_union : Ici (0 : ℝ) = Icc 0 1 ∪ Ici 1 := by
    ext x; simp only [mem_Ici, mem_union, mem_Icc]
    constructor
    · intro hx
      by_cases h : x ≤ 1
      · left; exact ⟨hx, h⟩
      · right; linarith
    · intro h; cases h with | inl h => exact h.1 | inr h => linarith
  rw [h_union]
  apply IntegrableOn.union
  · exact hf_cont.continuousOn.integrableOn_compact isCompact_Icc
  · -- On [1, ∞): use comparison with K₀ integrand times cosh bound
    have h_int_Ioi : IntegrableOn f (Ioi 0) volume := by
      apply integrable_of_isBigO_exp_neg (b := 1) one_pos hf_cont.continuousOn
      rw [isBigO_iff]; use 1
      have h_ratio_tendsto : Tendsto (fun t => f t / exp (-t)) atTop (nhds 0) := by
        have h_eq : ∀ t, f t / exp (-t) = cosh t * exp (t - z * cosh t) := by
          intro t; simp only [f]; field_simp; rw [mul_comm, ← exp_add]; ring_nf
        simp_rw [h_eq]
        -- cosh(t) * exp(t - z*cosh(t)) ≤ exp(2t - z*exp(t)/2) → 0
        have hbound : ∀ t, 0 ≤ t →
            cosh t * exp (t - z * cosh t) ≤ exp (2 * t - z * exp t / 2) := by
          intro t ht
          have h_cosh_le : cosh t ≤ exp t := by
            rw [cosh_eq]; have : exp (-t) ≤ exp t := exp_le_exp.mpr (by linarith); linarith
          have h_cosh_ge : cosh t ≥ exp t / 2 := by
            rw [cosh_eq]; have : exp (-t) ≥ 0 := exp_nonneg _; linarith
          calc cosh t * exp (t - z * cosh t)
              ≤ exp t * exp (t - z * cosh t) :=
                mul_le_mul_of_nonneg_right h_cosh_le (exp_nonneg _)
            _ ≤ exp t * exp (t - z * (exp t / 2)) := by
                apply mul_le_mul_of_nonneg_left _ (exp_nonneg _)
                apply exp_le_exp.mpr; linarith [mul_le_mul_of_nonneg_left h_cosh_ge hz.le]
            _ = exp (2 * t - z * exp t / 2) := by rw [← exp_add]; ring_nf
        have hexp_inf : Tendsto (fun t : ℝ => z * exp t / 2) atTop atTop := by
          apply Tendsto.atTop_div_const (by linarith : (0 : ℝ) < 2)
          exact Tendsto.const_mul_atTop hz tendsto_exp_atTop
        have h_ratio : Tendsto (fun t : ℝ => t / exp t) atTop (nhds 0) := by
          have h := tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
          simp only [pow_one] at h
          convert h using 1; ext t; rw [exp_neg, div_eq_mul_inv]
        have h_scaled : Tendsto (fun t : ℝ => 4 / z * (t / exp t)) atTop (nhds 0) := by
          convert h_ratio.const_mul (4 / z) using 1; simp [mul_zero]
        have h_shifted : Tendsto (fun t : ℝ => 4 / z * (t / exp t) - 1) atTop (nhds (-1)) := by
          convert h_scaled.sub_const 1 using 1; simp
        have h_prod : Tendsto (fun t : ℝ => (z * exp t / 2) * (4 / z * (t / exp t) - 1))
            atTop atBot := Tendsto.atTop_mul_neg (by norm_num : (-1 : ℝ) < 0) hexp_inf h_shifted
        have h_exp_to_zero : Tendsto (fun t => exp (2 * t - z * exp t / 2)) atTop (nhds 0) := by
          apply tendsto_exp_atBot.comp
          exact tendsto_atBot_mono (fun t => by
            calc 2 * t - z * exp t / 2
                ≤ (z * exp t / 2) * (4 / z * (t / exp t) - 1) := by field_simp; nlinarith [sq_nonneg 2]
              _ = _ := rfl) h_prod
        have hpos : ∀ t, 0 ≤ cosh t * exp (t - z * cosh t) :=
          fun t => mul_nonneg (cosh_pos t).le (exp_nonneg _)
        refine squeeze_zero' (Eventually.of_forall hpos) ?_ h_exp_to_zero
        filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
        exact hbound t ht
      have h_eventually_le : ∀ᶠ t in atTop, f t ≤ exp (-1 * t) := by
        have h1 : ∀ᶠ t in atTop, |f t / exp (-t)| < 1 := by
          have := Metric.tendsto_nhds.mp h_ratio_tendsto 1 one_pos
          filter_upwards [this] with t ht
          simp only [Real.dist_eq, sub_zero] at ht; exact ht
        filter_upwards [h1] with t ht
        have hgt : 0 < exp (-t) := exp_pos _
        rw [abs_lt] at ht
        have : f t < exp (-t) := (div_lt_one hgt).mp ht.2
        simp only [neg_mul, one_mul]; linarith
      filter_upwards [h_eventually_le] with t ht
      rw [Real.norm_of_nonneg (by apply mul_nonneg (exp_nonneg _) (cosh_pos t).le),
          Real.norm_of_nonneg (exp_nonneg _)]
      simp only [one_mul]; exact ht
    apply h_int_Ioi.mono _ le_rfl
    intro x hx; simp only [mem_Ici] at hx; simp only [mem_Ioi]; linarith

/-- K₀ is bounded by K₁: K₀(z) ≤ K₁(z) for z > 0.
    Proof: exp(-z cosh t) ≤ exp(-z cosh t) * cosh t since cosh t ≥ 1. -/
lemma besselK0_le_besselK1 (z : ℝ) (hz : 0 < z) : besselK0 z ≤ besselK1 z := by
  unfold besselK0 besselK1
  exact setIntegral_mono
    (hf := besselK0_integrand_integrableOn z hz)
    (hg := besselK1_integrand_integrableOn z hz)
    (fun t => le_mul_of_one_le_right (exp_nonneg _) (one_le_cosh t))

/-- The 2D Schwinger integral identity:
    ∫₀^∞ (1/t) exp(-m²t - r²/(4t)) dt = 2K₀(mr)

    This connects the heat kernel representation of the 2D Green's function
    to the Bessel function K₀. The proof uses the substitution t = (r/(2m)) exp(u).

    Combined with the definition of freeCovKernel, this gives:
    C(x,y) = (4π)⁻¹ · 2K₀(m|x-y|) = (2π)⁻¹ K₀(m|x-y|). -/
lemma schwingerIntegral2D_eq_besselK0 (m r : ℝ) (hm : 0 < m) (hr : 0 < r) :
    ∫ t in Ioi 0, (1 / t) * exp (-m^2 * t - r^2 / (4 * t)) =
    2 * besselK0 (m * r) := by
  let z := m * r
  have hz : 0 < z := mul_pos hm hr
  have h_symm : ∫ u : ℝ, exp (-z * cosh u) = 2 * besselK0 z := by
    have h_abs :
        ∫ u : ℝ, (fun t : ℝ => exp (-z * cosh t)) |u| =
        2 * ∫ u in Ioi (0 : ℝ), exp (-z * cosh u) := by
      simpa using (integral_comp_abs (f := fun t : ℝ => exp (-z * cosh t)))
    have h_even :
        (fun u : ℝ => exp (-z * cosh u)) =
        fun u => (fun t : ℝ => exp (-z * cosh t)) |u| := by
      funext u
      simp [cosh_abs]
    have h_even_int :
        ∫ u : ℝ, exp (-z * cosh u) =
        ∫ u : ℝ, (fun t : ℝ => exp (-z * cosh t)) |u| := by
      exact congrArg (fun f : ℝ → ℝ => ∫ u : ℝ, f u) h_even
    calc
      ∫ u : ℝ, exp (-z * cosh u)
          = ∫ u : ℝ, (fun t : ℝ => exp (-z * cosh t)) |u| := h_even_int
      _ = 2 * ∫ u in Ioi (0 : ℝ), exp (-z * cosh u) := h_abs
      _ = 2 * besselK0 z := by
            congr 1
            have hIoi_Ici :
                ∫ u in Ioi (0 : ℝ), exp (-z * cosh u) =
                ∫ u in Ici (0 : ℝ), exp (-z * cosh u) :=
              setIntegral_congr_set Ioi_ae_eq_Ici
            rw [hIoi_Ici, besselK0]

  let c := r / (2 * m)
  have hc : 0 < c := by
    dsimp [c]
    positivity

  let g : ℝ → ℝ := fun t => (1 / t) * exp (-m^2 * t - r^2 / (4 * t))

  have h_transform : ∀ u : ℝ,
      (c * exp u) * g (c * exp u) = exp (-z * cosh u) := by
    intro u
    have ht : c * exp u ≠ 0 := by positivity
    have h_sum :
        m^2 * (c * exp u) + r^2 / (4 * (c * exp u)) = z * cosh u := by
      dsimp [c, z]
      have he : exp u * exp (-u) = 1 := by
        rw [exp_neg]
        exact mul_inv_cancel₀ (exp_pos u).ne'
      field_simp
      rw [cosh_eq]
      ring_nf
      rw [he]
      ring
    calc
      (c * exp u) * g (c * exp u)
          = exp (-(m^2 * (c * exp u)) - r^2 / (4 * (c * exp u))) := by
              dsimp [g]
              field_simp [ht]
      _ = exp (-(m^2 * (c * exp u) + r^2 / (4 * (c * exp u)))) := by
              congr 1
              ring
      _ = exp (-(z * cosh u)) := by
              rw [h_sum]
      _ = exp (-z * cosh u) := by
              congr 1
              ring

  have h_cov : ∫ t in Ioi 0, g t = ∫ u, (c * exp u) * g (c * exp u) := by
    let φ := fun u => c * exp u
    have hφ_mono : StrictMono φ := by
      intro a b hab
      exact mul_lt_mul_of_pos_left (exp_lt_exp.mpr hab) hc
    have hφ_surj : φ '' Set.univ = Ioi 0 := by
      ext t
      simp only [Set.mem_image, Set.mem_univ, true_and, mem_Ioi, φ]
      constructor
      · rintro ⟨u, rfl⟩
        exact mul_pos hc (exp_pos u)
      · intro ht
        use Real.log (t / c)
        rw [exp_log (by positivity : t / c > 0)]
        field_simp
    have hφ_deriv : ∀ u ∈ Set.univ, HasDerivWithinAt φ (c * exp u) Set.univ u := by
      intro u _
      exact ((hasDerivAt_exp u).const_mul c).hasDerivWithinAt
    calc
      ∫ t in Ioi 0, g t = ∫ t in φ '' Set.univ, g t := by
        rw [hφ_surj]
      _ = ∫ u in Set.univ, (c * exp u) • g (φ u) :=
        integral_image_eq_integral_deriv_smul_of_monotoneOn MeasurableSet.univ
          hφ_deriv (hφ_mono.monotone.monotoneOn Set.univ) g
      _ = ∫ u, (c * exp u) * g (c * exp u) := by
        rw [setIntegral_univ]
        simp only [smul_eq_mul, φ]

  rw [h_cov]
  have h_eq :
      ∫ u, (c * exp u) * g (c * exp u) = ∫ u : ℝ, exp (-z * cosh u) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with u
    exact h_transform u
  rw [h_eq, h_symm]

/-- K₀ is continuous on (0, ∞).
    Proof: dominated convergence. For z near z₀ > 0, the integrand is bounded by
    exp(-z₀/2 · cosh t) which is integrable. -/
lemma besselK0_continuousOn : ContinuousOn besselK0 (Ioi 0) := by
  rw [isOpen_Ioi.continuousOn_iff]
  intro z₀ hz₀
  -- We show ContinuousAt besselK0 z₀ for z₀ > 0
  simp only [mem_Ioi] at hz₀
  -- Rewrite besselK0 as a full integral with indicator
  have h_eq : besselK0 = fun z => ∫ t, (Ici (0 : ℝ)).indicator (fun t => exp (-z * cosh t)) t := by
    ext z; simp only [besselK0, ← integral_indicator measurableSet_Ici]
  rw [h_eq]
  -- Set up F and bound for continuousAt_of_dominated
  set F : ℝ → ℝ → ℝ := fun z t => (Ici (0 : ℝ)).indicator (fun t => exp (-z * cosh t)) t
  set ε := z₀ / 2 with hε_def
  have hε_pos : 0 < ε := by linarith
  set bound : ℝ → ℝ := (Ici (0 : ℝ)).indicator (fun t => exp (-ε * cosh t))
  -- Apply continuousAt_of_dominated
  apply continuousAt_of_dominated (F := F) (bound := bound)
  · -- hF_meas: ∀ᶠ x in 𝓝 z₀, AEStronglyMeasurable (F x) μ
    apply Eventually.of_forall
    intro z
    apply AEStronglyMeasurable.indicator _ measurableSet_Ici
    exact (continuous_exp.comp (continuous_const.neg.mul continuous_cosh)).aestronglyMeasurable
  · -- h_bound: ∀ᶠ x in 𝓝 z₀, ∀ᵐ a, ‖F x a‖ ≤ bound a
    -- For z > ε = z₀/2, we have exp(-z * cosh t) ≤ exp(-ε * cosh t)
    rw [Filter.eventually_iff_exists_mem]
    refine ⟨Ioi ε, Ioi_mem_nhds (by linarith : ε < z₀), ?_⟩
    intro z hz_mem
    apply Eventually.of_forall
    intro t
    simp only [F, bound]
    by_cases ht : t ∈ Ici (0 : ℝ)
    · rw [indicator_of_mem ht, indicator_of_mem ht]
      rw [Real.norm_of_nonneg (exp_nonneg _)]
      apply exp_le_exp.mpr
      have hz_gt : ε < z := mem_Ioi.mp hz_mem
      nlinarith [cosh_pos t]
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]
      simp [norm_zero]
  · -- bound_integrable: Integrable bound μ
    exact (besselK0_integrand_integrableOn ε hε_pos).integrable_indicator measurableSet_Ici
  · -- h_cont: ∀ᵐ a, ContinuousAt (fun x => F x a) z₀
    apply Eventually.of_forall
    intro t
    simp only [F]
    by_cases ht : t ∈ Ici (0 : ℝ)
    · simp only [Set.indicator_of_mem ht]
      simp only [show ∀ x : ℝ, -x * cosh t = -(x * cosh t) from fun x => neg_mul x (cosh t)]
      exact (continuous_exp.comp ((continuous_id'.mul continuous_const).neg)).continuousAt
    · simp only [Set.indicator_of_notMem ht]
      exact continuousAt_const

/-- K₀ is monotone decreasing for z > 0.
    Proof: for z₁ ≤ z₂, the integrand exp(-z₂ cosh t) ≤ exp(-z₁ cosh t) pointwise. -/
lemma besselK0_antitone : AntitoneOn besselK0 (Ioi 0) := by
  intro z₁ hz₁ z₂ hz₂ h12
  unfold besselK0
  apply setIntegral_mono (besselK0_integrand_integrableOn z₂ (mem_Ioi.mp hz₂))
    (besselK0_integrand_integrableOn z₁ (mem_Ioi.mp hz₁))
  intro t
  apply exp_le_exp.mpr
  nlinarith [cosh_pos t]

end

/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.InfiniteVolumeLimit.Part3

/-!
# Regularity of the φ⁴₂ Theory

This file establishes regularity properties of the infinite-volume φ⁴₂ theory,
culminating in the bound on the generating functional that gives OS axiom E1
(regularity / linear growth).

The main results are:
1. Wick powers :φʲ: exist in infinite volume (convergence of UV limit)
2. Integration by parts identity in infinite volume (Euclidean equation of motion)
3. The generating functional bound: |S{f}| ≤ exp(c · N'(f)) (OS1)

The key technique is integration by parts, which relates the n-point functions
to (n±1)-point functions via the equation of motion. Combined with the
finite-volume estimates of Chapter 8, this gives uniform bounds that pass
to the infinite volume limit.

## References

* [Glimm-Jaffe] Chapter 12, especially Sections 12.1-12.5
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

/-! ## Abstract regularity interfaces -/

/-- Input for existence of infinite-volume Wick powers. -/
class WickPowersModel (params : Phi4Params)
    [InfiniteVolumeMeasureModel params] where
  wick_powers_infinite_volume :
    ∀ (j : ℕ) {p : ℝ≥0∞}, p ≠ ⊤ →
      ∃ (W : ℕ → FieldConfig2D → Spacetime2D → ℝ),
        ∀ x : Spacetime2D, MemLp (fun ω => W j ω x) p (infiniteVolumeMeasure params)

/-! ## Integration by parts in infinite volume -/

/-- The Wick cubic smeared against a test function: ∫ :φ(x)³: f(x) dx
    evaluated in the infinite-volume measure.
    This arises from the functional derivative of V = λ∫:φ⁴:dx. -/
def wickCubicSmeared (params : Phi4Params) (f : TestFun2D)
    (ω : FieldConfig2D) : ℝ :=
  Filter.limsup
    (fun n : ℕ => ∫ x, wickPower 3 params.mass (standardUVCutoffSeq n) ω x * f x)
    Filter.atTop

/-- If the canonical UV-smearing sequence converges pointwise, then
    `wickCubicSmeared` agrees with that ordinary limit. -/
theorem wickCubicSmeared_eq_lim_of_convergent
    (params : Phi4Params) (f : TestFun2D) (ω : FieldConfig2D) (V : ℝ)
    (hconv :
      Filter.Tendsto
        (fun n : ℕ => ∫ x, wickPower 3 params.mass (standardUVCutoffSeq n) ω x * f x)
        Filter.atTop
        (nhds V)) :
    wickCubicSmeared params f ω = V := by
  unfold wickCubicSmeared
  simpa using hconv.limsup_eq

/-- Regularity/IBP inputs for the infinite-volume φ⁴₂ theory beyond Wick-power
    existence. -/
class RegularityModel (params : Phi4Params)
    [InfiniteVolumeMeasureModel params] where
  /-- Almost-everywhere pointwise convergence of the UV-regularized Wick-cubic
      smearings to `wickCubicSmeared`. -/
  wickCubicSmeared_tendsto_ae :
    ∀ (f : TestFun2D),
      ∀ᵐ ω ∂(infiniteVolumeMeasure params),
        Filter.Tendsto
          (fun n : ℕ => ∫ x, wickPower 3 params.mass (standardUVCutoffSeq n) ω x * f x)
          Filter.atTop
          (nhds (wickCubicSmeared params f ω))
  euclidean_equation_of_motion :
    ∀ (f g : TestFun2D),
      ∫ ω, ω f * ω g ∂(infiniteVolumeMeasure params) =
        GaussianField.covariance (freeCovarianceCLM params.mass params.mass_pos) f g -
        params.coupling *
          ∫ ω, wickCubicSmeared params f ω * ω g ∂(infiniteVolumeMeasure params)
  generating_functional_bound :
    ∃ c : ℝ, ∀ f : TestFun2D,
      |∫ ω, Real.exp (ω f) ∂(infiniteVolumeMeasure params)| ≤
        Real.exp (c * SchwartzMap.seminorm ℝ 2 2 f)
  nonlocal_phi4_bound :
    ∀ (g : TestFun2D), ∃ C₁ C₂ : ℝ, ∀ (Λ : Rectangle),
      |generatingFunctional params Λ g| ≤
        Real.exp (C₁ * Λ.area + C₂)
  generating_functional_bound_uniform :
    ∀ (f : TestFun2D),
      ∃ c : ℝ, ∀ Λ : Rectangle,
        |generatingFunctional params Λ f| ≤ Real.exp (c * SchwartzMap.seminorm ℝ 2 2 f)

/-! ## Generating functional bound (OS1) -/

/-- Norm functional for the generating functional bound.
    In the current interface this is taken to be a fixed Schwartz seminorm
    controlling the growth estimate. -/
def normFunctional (g : TestFun2D) : ℝ :=
  SchwartzMap.seminorm ℝ 2 2 g

/-! ## Exhaustion reduction lemmas for OS1 -/

/-- Finite-volume generating functional along the standard rectangle exhaustion. -/
def generatingFunctionalOnExhaustion (params : Phi4Params) (f : TestFun2D) (n : ℕ) : ℝ :=
  generatingFunctional params (exhaustingRectangles (n + 1) (Nat.succ_pos n)) f

@[simp] theorem generatingFunctionalOnExhaustion_eq (params : Phi4Params)
    (f : TestFun2D) (n : ℕ) :
    generatingFunctionalOnExhaustion params f n =
      generatingFunctional params (exhaustingRectangles (n + 1) (Nat.succ_pos n)) f := rfl

/-- Finite-volume diagonal moments from a finite-volume generating-functional
    exponential bound at fixed constant `c`. -/
theorem finiteVolume_diagonal_moment_bound_of_generating_bound
    (params : Phi4Params) [InteractionWeightModel params]
    (c : ℝ)
    (hbound : ∀ (g : TestFun2D) (Λ : Rectangle),
      |generatingFunctional params Λ g| ≤ Real.exp (c * normFunctional g))
    (Λ : Rectangle) (f : TestFun2D) (n : ℕ) :
    |schwingerN params Λ n (fun _ => f)| ≤
      (Nat.factorial n : ℝ) *
        (Real.exp (c * normFunctional f) + Real.exp (c * normFunctional (-f))) := by
  have hmoment :=
    schwingerN_const_abs_le_factorial_mul_generatingFunctional_pair
      params Λ f n
  have hgf_nonneg : 0 ≤ generatingFunctional params Λ f :=
    generatingFunctional_nonneg params Λ f
  have hgneg_nonneg : 0 ≤ generatingFunctional params Λ (-f) :=
    generatingFunctional_nonneg params Λ (-f)
  have hgf_le : generatingFunctional params Λ f ≤ Real.exp (c * normFunctional f) := by
    simpa [abs_of_nonneg hgf_nonneg] using hbound f Λ
  have hgneg_le : generatingFunctional params Λ (-f) ≤ Real.exp (c * normFunctional (-f)) := by
    simpa [abs_of_nonneg hgneg_nonneg] using hbound (-f) Λ
  have hsum_le :
      generatingFunctional params Λ f + generatingFunctional params Λ (-f) ≤
        Real.exp (c * normFunctional f) + Real.exp (c * normFunctional (-f)) :=
    add_le_add hgf_le hgneg_le
  have hfac_nonneg : 0 ≤ (Nat.factorial n : ℝ) := by positivity
  exact hmoment.trans (mul_le_mul_of_nonneg_left hsum_le hfac_nonneg)

/-- Uniform-in-volume finite-volume mixed `n`-point moments from a pointwise-in-`f`
    generating-functional exponential estimate. The resulting `c` depends on the
    finite family `f : Fin n → TestFun2D`, but is uniform in `Λ`. -/
theorem finiteVolume_mixed_moment_bound_of_uniform_generating_bound
    (params : Phi4Params) [InteractionWeightModel params]
    (huniform : ∀ h : TestFun2D, ∃ c : ℝ, ∀ Λ : Rectangle,
      |generatingFunctional params Λ h| ≤ Real.exp (c * normFunctional h))
    (n : ℕ) (hn : 0 < n) (f : Fin n → TestFun2D) :
    ∃ c : ℝ, ∀ Λ : Rectangle,
      |schwingerN params Λ n f| ≤
        ∑ i : Fin n, (Nat.factorial n : ℝ) *
          (Real.exp (c * normFunctional (f i)) +
            Real.exp (c * normFunctional (-(f i)))) := by
  classical
  have hpos :
      ∀ i : Fin n, ∃ c : ℝ, ∀ Λ : Rectangle,
        |generatingFunctional params Λ (f i)| ≤ Real.exp (c * normFunctional (f i)) := by
    intro i
    exact huniform (f i)
  choose cpos hcpos using hpos
  have hneg :
      ∀ i : Fin n, ∃ c : ℝ, ∀ Λ : Rectangle,
        |generatingFunctional params Λ (-(f i))| ≤ Real.exp (c * normFunctional (-(f i))) := by
    intro i
    exact huniform (-(f i))
  choose cneg hcneg using hneg
  let c : ℝ := ∑ i : Fin n, (|cpos i| + |cneg i|)
  refine ⟨c, ?_⟩
  intro Λ
  have hmixed :=
    schwingerN_abs_le_sum_factorial_mul_generatingFunctional_pair
      params Λ n hn f
  have hfac_nonneg : 0 ≤ (Nat.factorial n : ℝ) := by positivity
  have hsumBound :
      (∑ i : Fin n, (Nat.factorial n : ℝ) *
          (generatingFunctional params Λ (f i) + generatingFunctional params Λ (-(f i)))) ≤
        ∑ i : Fin n, (Nat.factorial n : ℝ) *
          (Real.exp (c * normFunctional (f i)) +
            Real.exp (c * normFunctional (-(f i)))) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    have hnonneg_f : 0 ≤ generatingFunctional params Λ (f i) :=
      generatingFunctional_nonneg params Λ (f i)
    have hnonneg_negf : 0 ≤ generatingFunctional params Λ (-(f i)) :=
      generatingFunctional_nonneg params Λ (-(f i))
    have hci_le_abs : cpos i ≤ |cpos i| := le_abs_self (cpos i)
    have hnegci_le_abs : cneg i ≤ |cneg i| := le_abs_self (cneg i)
    have habs_le_pair : |cpos i| ≤ |cpos i| + |cneg i| := by
      have hnonneg : 0 ≤ |cneg i| := abs_nonneg (cneg i)
      linarith
    have hnegabs_le_pair : |cneg i| ≤ |cpos i| + |cneg i| := by
      have hnonneg : 0 ≤ |cpos i| := abs_nonneg (cpos i)
      linarith
    have hpair_le_c : |cpos i| + |cneg i| ≤ c := by
      dsimp [c]
      have hpair_le_c' :
          |cpos i| + |cneg i| ≤
            ∑ j ∈ (Finset.univ : Finset (Fin n)), (|cpos j| + |cneg j|) := by
        exact Finset.single_le_sum
          (s := (Finset.univ : Finset (Fin n)))
          (f := fun j : Fin n => |cpos j| + |cneg j|)
          (fun j hj => by positivity)
          (by simp)
      simpa using hpair_le_c'
    have hci_le_c : cpos i ≤ c := hci_le_abs.trans (habs_le_pair.trans hpair_le_c)
    have hnegci_le_c : cneg i ≤ c := hnegci_le_abs.trans (hnegabs_le_pair.trans hpair_le_c)
    have hnorm_f_nonneg : 0 ≤ normFunctional (f i) := by
      unfold normFunctional
      positivity
    have hnorm_negf_nonneg : 0 ≤ normFunctional (-(f i)) := by
      unfold normFunctional
      positivity
    have hgf_le_ci :
        generatingFunctional params Λ (f i) ≤ Real.exp (cpos i * normFunctional (f i)) := by
      simpa [abs_of_nonneg hnonneg_f] using hcpos i Λ
    have hnegf_le_ci :
        generatingFunctional params Λ (-(f i)) ≤
          Real.exp (cneg i * normFunctional (-(f i))) := by
      simpa [abs_of_nonneg hnonneg_negf] using hcneg i Λ
    have hexp_mono_f :
        Real.exp (cpos i * normFunctional (f i)) ≤
          Real.exp (c * normFunctional (f i)) := by
      refine Real.exp_le_exp.mpr ?_
      exact mul_le_mul_of_nonneg_right hci_le_c hnorm_f_nonneg
    have hexp_mono_negf :
        Real.exp (cneg i * normFunctional (-(f i))) ≤
          Real.exp (c * normFunctional (-(f i))) := by
      refine Real.exp_le_exp.mpr ?_
      exact mul_le_mul_of_nonneg_right hnegci_le_c hnorm_negf_nonneg
    have hgf_le :
        generatingFunctional params Λ (f i) ≤ Real.exp (c * normFunctional (f i)) :=
      hgf_le_ci.trans hexp_mono_f
    have hnegf_le :
        generatingFunctional params Λ (-(f i)) ≤
          Real.exp (c * normFunctional (-(f i))) :=
      hnegf_le_ci.trans hexp_mono_negf
    have hpair_le :
        generatingFunctional params Λ (f i) + generatingFunctional params Λ (-(f i)) ≤
          Real.exp (c * normFunctional (f i)) +
            Real.exp (c * normFunctional (-(f i))) :=
      add_le_add hgf_le hnegf_le
    exact mul_le_mul_of_nonneg_left hpair_le hfac_nonneg
  exact hmixed.trans hsumBound

private theorem abs_limit_le_of_abs_bound {u : ℕ → ℝ} {x B : ℝ}
    (hu : Filter.Tendsto u Filter.atTop (nhds x))
    (hbound : ∀ n, |u n| ≤ B) :
    |x| ≤ B := by
  have huabs : Filter.Tendsto (fun n => |u n|) Filter.atTop (nhds |x|) := by
    simpa [Real.norm_eq_abs] using hu.norm
  have hB : Filter.Tendsto (fun _ : ℕ => B) Filter.atTop (nhds B) :=
    tendsto_const_nhds
  exact le_of_tendsto_of_tendsto huabs hB
    (Filter.Eventually.of_forall hbound)

/-- Restrict a global finite-volume generating-functional exponential bound
    to the standard exhausting sequence. -/
theorem generatingFunctionalOnExhaustion_bound_of_global_uniform
    (params : Phi4Params)
    (hglobal : ∃ c : ℝ, ∀ (f : TestFun2D) (Λ : Rectangle),
      |generatingFunctional params Λ f| ≤ Real.exp (c * normFunctional f)) :
    ∃ c : ℝ, ∀ (f : TestFun2D) (n : ℕ),
      |generatingFunctionalOnExhaustion params f n| ≤
        Real.exp (c * normFunctional f) := by
  rcases hglobal with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro f n
  simpa [generatingFunctionalOnExhaustion] using
    hc f (exhaustingRectangles (n + 1) (Nat.succ_pos n))

/-- Infinite-volume mixed `n`-point Schwinger bound from pointwise-in-`f`
    uniform finite-volume generating-functional control. -/
theorem infiniteVolumeSchwinger_mixed_bound_of_uniform_generating_bound
    (params : Phi4Params) [InteractionWeightModel params]
    [SchwingerLimitModel params]
    (huniform : ∀ h : TestFun2D, ∃ c : ℝ, ∀ Λ : Rectangle,
      |generatingFunctional params Λ h| ≤ Real.exp (c * normFunctional h))
    (n : ℕ) (hn : 0 < n) (f : Fin n → TestFun2D) :
    ∃ c : ℝ,
      |infiniteVolumeSchwinger params n f| ≤
        ∑ i : Fin n, (Nat.factorial n : ℝ) *
          (Real.exp (c * normFunctional (f i)) +
            Real.exp (c * normFunctional (-(f i)))) := by
  rcases finiteVolume_mixed_moment_bound_of_uniform_generating_bound
      params huniform n hn f with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  let C : ℝ :=
    ∑ i : Fin n, (Nat.factorial n : ℝ) *
      (Real.exp (c * normFunctional (f i)) +
        Real.exp (c * normFunctional (-(f i))))
  have hraw :
      Filter.Tendsto
        (fun m : ℕ => if h : 0 < m then schwingerN params (exhaustingRectangles m h) n f else 0)
        Filter.atTop
        (nhds (infiniteVolumeSchwinger params n f)) :=
    SchwingerLimitModel.infiniteVolumeSchwinger_tendsto
      (params := params) n f
  have hlim :
      Filter.Tendsto
        (fun k : ℕ => schwingerN params (exhaustingRectangles (k + 1) (Nat.succ_pos k)) n f)
        Filter.atTop
        (nhds (infiniteVolumeSchwinger params n f)) := by
    have hcomp := hraw.comp (Filter.tendsto_add_atTop_nat 1)
    simpa using hcomp
  have hbound : ∀ k : ℕ,
      |schwingerN params (exhaustingRectangles (k + 1) (Nat.succ_pos k)) n f| ≤ C := by
    intro k
    simpa [C] using hc (exhaustingRectangles (k + 1) (Nat.succ_pos k))
  simpa [C] using abs_limit_le_of_abs_bound hlim hbound

/-- If the generating functional along exhaustion converges to the infinite-volume
    generating functional and satisfies a global exponential bound, then OS1 follows. -/
theorem generating_functional_bound_of_exhaustion_limit
    (params : Phi4Params)
    [InfiniteVolumeMeasureModel params]
    (hlim : ∀ f : TestFun2D,
      Filter.Tendsto (generatingFunctionalOnExhaustion params f) Filter.atTop
        (nhds (∫ ω, Real.exp (ω f) ∂(infiniteVolumeMeasure params))))
    (hbound : ∃ c : ℝ, ∀ (f : TestFun2D) (n : ℕ),
      |generatingFunctionalOnExhaustion params f n| ≤
        Real.exp (c * normFunctional f)) :
    ∃ c : ℝ, ∀ f : TestFun2D,
      |∫ ω, Real.exp (ω f) ∂(infiniteVolumeMeasure params)| ≤
        Real.exp (c * normFunctional f) := by
  rcases hbound with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro f
  exact abs_limit_le_of_abs_bound (hlim f) (fun n => hc f n)

/-- Honest frontier: generating-functional bound (OS1 / E0') from
    explicit exhaustion convergence and finite-volume uniform bounds. -/
theorem gap_generating_functional_bound (params : Phi4Params) :
    [InfiniteVolumeMeasureModel params] →
    (hlim : ∀ f : TestFun2D,
      Filter.Tendsto (generatingFunctionalOnExhaustion params f) Filter.atTop
        (nhds (∫ ω, Real.exp (ω f) ∂(infiniteVolumeMeasure params)))) →
    (hglobal : ∃ c : ℝ, ∀ (f : TestFun2D) (Λ : Rectangle),
      |generatingFunctional params Λ f| ≤ Real.exp (c * normFunctional f)) →
    ∃ c : ℝ, ∀ f : TestFun2D,
      |∫ ω, Real.exp (ω f) ∂(infiniteVolumeMeasure params)| ≤
        Real.exp (c * normFunctional f) := by
  intro hmeas hlim hglobal
  exact generating_functional_bound_of_exhaustion_limit params hlim
    (generatingFunctionalOnExhaustion_bound_of_global_uniform params hglobal)

/-! ## Uniformity in volume -/

/-- Honest frontier: uniform-in-volume generating-functional bound (GJ §12.4)
    from explicit pointwise-in-`f` finite-volume data. -/
theorem gap_generating_functional_bound_uniform (params : Phi4Params)
    (huniform : ∀ f : TestFun2D, ∃ c : ℝ, ∀ Λ : Rectangle,
      |generatingFunctional params Λ f| ≤ Real.exp (c * normFunctional f))
    (f : TestFun2D) :
    ∃ c : ℝ, ∀ Λ : Rectangle,
      |generatingFunctional params Λ f| ≤ Real.exp (c * normFunctional f) := by
  exact huniform f

/-! ## Nonlocal φ⁴ bounds -/

/-- Honest frontier: nonlocal φ⁴ bounds (GJ §12.3) from explicit
    pointwise-in-`f` uniform finite-volume bounds. -/
theorem gap_nonlocal_phi4_bound (params : Phi4Params) :
    (huniform : ∀ f : TestFun2D, ∃ c : ℝ, ∀ Λ : Rectangle,
      |generatingFunctional params Λ f| ≤ Real.exp (c * normFunctional f)) →
    ∀ (g : TestFun2D), ∃ C₁ C₂ : ℝ, ∀ (Λ : Rectangle),
      |generatingFunctional params Λ g| ≤
        Real.exp (C₁ * Λ.area + C₂) := by
  intro huniform g
  rcases gap_generating_functional_bound_uniform params huniform g with ⟨c, hc⟩
  refine ⟨0, c * normFunctional g, ?_⟩
  intro Λ
  simpa [zero_mul] using hc Λ

end

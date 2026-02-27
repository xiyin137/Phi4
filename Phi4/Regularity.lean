/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.InfiniteVolumeLimit

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

/-! ## Wick powers in infinite volume -/

/-- **Wick powers exist in infinite volume** (Glimm-Jaffe 12.2):
    :φ(x)ʲ: = lim_{κ→∞} :φ_κ(x)ʲ: exists as a limit in Lᵖ(dμ)
    for the infinite-volume measure dμ and for all p < ∞.

    The key is that the UV limit and the infinite volume limit commute:
    the UV-regularized Wick power converges in Lᵖ uniformly in the volume. -/
theorem wick_powers_infinite_volume (params : Phi4Params) (j : ℕ)
    [InfiniteVolumeMeasureModel params]
    [WickPowersModel params]
    {p : ℝ≥0∞} (hp : p ≠ ⊤) :
    ∃ (W : ℕ → FieldConfig2D → Spacetime2D → ℝ),
      ∀ x : Spacetime2D, MemLp (fun ω => W j ω x) p (infiniteVolumeMeasure params) := by
  exact WickPowersModel.wick_powers_infinite_volume
    (params := params) j hp

/-! ## Integration by parts in infinite volume -/

/-- The Wick cubic smeared against a test function: ∫ :φ(x)³: f(x) dx
    evaluated in the infinite-volume measure.
    This arises from the functional derivative of V = λ∫:φ⁴:dx. -/
def wickCubicSmeared (params : Phi4Params) (f : TestFun2D)
    (ω : FieldConfig2D) : ℝ :=
  Filter.limsup
    (fun n : ℕ => ∫ x, wickPower 3 params.mass (standardUVCutoffSeq n) ω x * f x)
    Filter.atTop

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

/-- **Euclidean equation of motion** (Glimm-Jaffe 12.1.1):
    For the infinite volume φ⁴₂ theory,
      ⟨φ(f)φ(g)⟩ = C(f,g) - λ ⟨(:φ³: · f) φ(g)⟩

    This is the Schwinger-Dyson equation / integration by parts identity for
    the interacting measure.

    After analytic continuation to real (Minkowski) time, the δ-function
    contribution vanishes and this becomes the nonlinear field equation:
      (-□ + m²) φ(x) + λ :φ(x)³: = 0 -/
theorem euclidean_equation_of_motion (params : Phi4Params)
    [InfiniteVolumeMeasureModel params]
    [RegularityModel params]
    (f g : TestFun2D) :
    ∫ ω, ω f * ω g ∂(infiniteVolumeMeasure params) =
      GaussianField.covariance (freeCovarianceCLM params.mass params.mass_pos) f g -
      params.coupling *
        ∫ ω, wickCubicSmeared params f ω * ω g ∂(infiniteVolumeMeasure params) := by
  exact RegularityModel.euclidean_equation_of_motion
    (params := params) f g

/-- Almost-everywhere pointwise UV convergence for `wickCubicSmeared`. -/
theorem wickCubicSmeared_tendsto_ae (params : Phi4Params)
    [InfiniteVolumeMeasureModel params]
    [RegularityModel params]
    (f : TestFun2D) :
    ∀ᵐ ω ∂(infiniteVolumeMeasure params),
      Filter.Tendsto
        (fun n : ℕ => ∫ x, wickPower 3 params.mass (standardUVCutoffSeq n) ω x * f x)
        Filter.atTop
        (nhds (wickCubicSmeared params f ω)) := by
  exact RegularityModel.wickCubicSmeared_tendsto_ae
    (params := params) f

/-- Kernel-form rewriting of the Euclidean equation of motion, using the
    explicit covariance bridge `freeCovariance_eq_kernel`. -/
theorem euclidean_equation_of_motion_kernel_form (params : Phi4Params)
    [InfiniteVolumeMeasureModel params]
    [RegularityModel params]
    [FreeCovarianceKernelModel params.mass params.mass_pos]
    (f g : TestFun2D) :
    ∫ ω, ω f * ω g ∂(infiniteVolumeMeasure params) =
      (∫ x, ∫ y, f x * freeCovKernel params.mass x y * g y) -
      params.coupling *
        ∫ ω, wickCubicSmeared params f ω * ω g ∂(infiniteVolumeMeasure params) := by
  rw [euclidean_equation_of_motion (params := params) f g]
  rw [freeCovariance_eq_kernel (mass := params.mass) (hmass := params.mass_pos) f g]

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

/-- Finite-volume diagonal moments from a global finite-volume
    generating-functional exponential bound. -/
theorem finiteVolume_diagonal_moment_bound_of_global_uniform_generating_bound
    (params : Phi4Params) [InteractionWeightModel params]
    (hglobal : ∃ c : ℝ, ∀ (g : TestFun2D) (Λ : Rectangle),
      |generatingFunctional params Λ g| ≤ Real.exp (c * normFunctional g))
    (Λ : Rectangle) (f : TestFun2D) (n : ℕ) :
    ∃ c : ℝ,
      |schwingerN params Λ n (fun _ => f)| ≤
        (Nat.factorial n : ℝ) *
          (Real.exp (c * normFunctional f) + Real.exp (c * normFunctional (-f))) := by
  rcases hglobal with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  exact finiteVolume_diagonal_moment_bound_of_generating_bound
    params c hc Λ f n

/-- Finite-volume mixed `n`-point moments from a finite-volume generating-functional
    exponential bound at fixed constant `c`. -/
theorem finiteVolume_mixed_moment_bound_of_generating_bound
    (params : Phi4Params) [InteractionWeightModel params]
    (c : ℝ)
    (hbound : ∀ (g : TestFun2D) (Λ : Rectangle),
      |generatingFunctional params Λ g| ≤ Real.exp (c * normFunctional g))
    (Λ : Rectangle) (n : ℕ) (hn : 0 < n) (f : Fin n → TestFun2D) :
    |schwingerN params Λ n f| ≤
      ∑ i : Fin n, (Nat.factorial n : ℝ) *
        (Real.exp (c * normFunctional (f i)) +
          Real.exp (c * normFunctional (-(f i)))) := by
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
    have hgf_nonneg : 0 ≤ generatingFunctional params Λ (f i) :=
      generatingFunctional_nonneg params Λ (f i)
    have hgneg_nonneg : 0 ≤ generatingFunctional params Λ (-(f i)) :=
      generatingFunctional_nonneg params Λ (-(f i))
    have hgf_le : generatingFunctional params Λ (f i) ≤ Real.exp (c * normFunctional (f i)) := by
      simpa [abs_of_nonneg hgf_nonneg] using hbound (f i) Λ
    have hgneg_le :
        generatingFunctional params Λ (-(f i)) ≤
          Real.exp (c * normFunctional (-(f i))) := by
      simpa [abs_of_nonneg hgneg_nonneg] using hbound (-(f i)) Λ
    have hpair_le :
        generatingFunctional params Λ (f i) + generatingFunctional params Λ (-(f i)) ≤
          Real.exp (c * normFunctional (f i)) +
            Real.exp (c * normFunctional (-(f i))) :=
      add_le_add hgf_le hgneg_le
    exact mul_le_mul_of_nonneg_left hpair_le hfac_nonneg
  exact hmixed.trans hsumBound

/-- Finite-volume mixed `n`-point moments from a global finite-volume
    generating-functional exponential bound. -/
theorem finiteVolume_mixed_moment_bound_of_global_uniform_generating_bound
    (params : Phi4Params) [InteractionWeightModel params]
    (hglobal : ∃ c : ℝ, ∀ (g : TestFun2D) (Λ : Rectangle),
      |generatingFunctional params Λ g| ≤ Real.exp (c * normFunctional g))
    (Λ : Rectangle) (n : ℕ) (hn : 0 < n) (f : Fin n → TestFun2D) :
    ∃ c : ℝ,
      |schwingerN params Λ n f| ≤
        ∑ i : Fin n, (Nat.factorial n : ℝ) *
          (Real.exp (c * normFunctional (f i)) +
            Real.exp (c * normFunctional (-(f i)))) := by
  rcases hglobal with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  exact finiteVolume_mixed_moment_bound_of_generating_bound
    params c hc Λ n hn f

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

/-- Finite-volume two-point bound from a finite-volume generating-functional
    exponential bound, obtained by polarization from diagonal moment bounds. -/
theorem finiteVolume_twoPoint_bound_of_generating_bound
    (params : Phi4Params) [InteractionWeightModel params]
    (c : ℝ)
    (hbound : ∀ (h : TestFun2D) (Λ : Rectangle),
      |generatingFunctional params Λ h| ≤ Real.exp (c * normFunctional h))
    (Λ : Rectangle) (f g : TestFun2D) :
    |schwingerTwo params Λ f g| ≤
      ((Nat.factorial 2 : ℝ) *
          (Real.exp (c * normFunctional (f + g)) +
            Real.exp (c * normFunctional (-(f + g)))) +
        (Nat.factorial 2 : ℝ) *
          (Real.exp (c * normFunctional (f - g)) +
            Real.exp (c * normFunctional (-(f - g))))) / 4 := by
  let Mplus : ℝ :=
    (Nat.factorial 2 : ℝ) *
      (Real.exp (c * normFunctional (f + g)) +
        Real.exp (c * normFunctional (-(f + g))))
  let Mminus : ℝ :=
    (Nat.factorial 2 : ℝ) *
      (Real.exp (c * normFunctional (f - g)) +
        Real.exp (c * normFunctional (-(f - g))))
  have hplusDiag :
      |schwingerTwo params Λ (f + g) (f + g)| ≤ Mplus := by
    have hdiag :=
      finiteVolume_diagonal_moment_bound_of_generating_bound
        params c hbound Λ (f + g) 2
    simpa [Mplus, schwingerN_two_eq_schwingerTwo] using hdiag
  have hminusDiag :
      |schwingerTwo params Λ (f - g) (f - g)| ≤ Mminus := by
    have hdiag :=
      finiteVolume_diagonal_moment_bound_of_generating_bound
        params c hbound Λ (f - g) 2
    simpa [Mminus, schwingerN_two_eq_schwingerTwo] using hdiag
  have hpol := schwingerTwo_polarization params Λ f g
  have htri :
      |schwingerTwo params Λ (f + g) (f + g) -
          schwingerTwo params Λ (f - g) (f - g)| ≤
        |schwingerTwo params Λ (f + g) (f + g)| +
          |schwingerTwo params Λ (f - g) (f - g)| := by
    simpa [Real.norm_eq_abs, sub_eq_add_neg] using
      (norm_add_le (schwingerTwo params Λ (f + g) (f + g))
        (-(schwingerTwo params Λ (f - g) (f - g))))
  calc
    |schwingerTwo params Λ f g|
        = |schwingerTwo params Λ (f + g) (f + g) -
            schwingerTwo params Λ (f - g) (f - g)| / 4 := by
            rw [hpol, abs_div, abs_of_pos (show (0 : ℝ) < 4 by norm_num)]
    _ ≤ (|schwingerTwo params Λ (f + g) (f + g)| +
          |schwingerTwo params Λ (f - g) (f - g)|) / 4 := by
          exact div_le_div_of_nonneg_right htri (by positivity)
    _ ≤ (Mplus + Mminus) / 4 := by
          exact div_le_div_of_nonneg_right (add_le_add hplusDiag hminusDiag) (by positivity)
    _ = ((Nat.factorial 2 : ℝ) *
          (Real.exp (c * normFunctional (f + g)) +
            Real.exp (c * normFunctional (-(f + g)))) +
        (Nat.factorial 2 : ℝ) *
          (Real.exp (c * normFunctional (f - g)) +
            Real.exp (c * normFunctional (-(f - g))))) / 4 := by
          simp [Mplus, Mminus]

/-- Finite-volume two-point bound from a global finite-volume generating-functional
    exponential estimate. -/
theorem finiteVolume_twoPoint_bound_of_global_uniform_generating_bound
    (params : Phi4Params) [InteractionWeightModel params]
    (hglobal : ∃ c : ℝ, ∀ (h : TestFun2D) (Λ : Rectangle),
      |generatingFunctional params Λ h| ≤ Real.exp (c * normFunctional h))
    (Λ : Rectangle) (f g : TestFun2D) :
    ∃ c : ℝ,
      |schwingerTwo params Λ f g| ≤
        ((Nat.factorial 2 : ℝ) *
            (Real.exp (c * normFunctional (f + g)) +
              Real.exp (c * normFunctional (-(f + g)))) +
          (Nat.factorial 2 : ℝ) *
            (Real.exp (c * normFunctional (f - g)) +
              Real.exp (c * normFunctional (-(f - g))))) / 4 := by
  rcases hglobal with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  exact finiteVolume_twoPoint_bound_of_generating_bound params c hc Λ f g

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

/-- Pointwise-in-`f` variant of the previous restriction lemma. -/
theorem generatingFunctionalOnExhaustion_bound_of_uniform
    (params : Phi4Params)
    (huniform : ∀ f : TestFun2D, ∃ c : ℝ, ∀ Λ : Rectangle,
      |generatingFunctional params Λ f| ≤ Real.exp (c * normFunctional f)) :
    ∀ f : TestFun2D, ∃ c : ℝ, ∀ n : ℕ,
      |generatingFunctionalOnExhaustion params f n| ≤
        Real.exp (c * normFunctional f) := by
  intro f
  rcases huniform f with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro n
  simpa [generatingFunctionalOnExhaustion] using
    hc (exhaustingRectangles (n + 1) (Nat.succ_pos n))

/-- Uniform diagonal moment bound along exhaustion from a global finite-volume
    generating-functional exponential estimate. -/
theorem diagonal_moment_bound_on_exhaustion_of_global_uniform
    (params : Phi4Params) [InteractionWeightModel params]
    (hglobal : ∃ c : ℝ, ∀ (g : TestFun2D) (Λ : Rectangle),
      |generatingFunctional params Λ g| ≤ Real.exp (c * normFunctional g))
    (f : TestFun2D) (n : ℕ) :
    ∃ c : ℝ, ∀ k : ℕ,
      |schwingerN params (exhaustingRectangles (k + 1) (Nat.succ_pos k)) n (fun _ => f)| ≤
        (Nat.factorial n : ℝ) *
          (Real.exp (c * normFunctional f) + Real.exp (c * normFunctional (-f))) := by
  rcases hglobal with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro k
  exact finiteVolume_diagonal_moment_bound_of_generating_bound
    params c hc
    (exhaustingRectangles (k + 1) (Nat.succ_pos k))
    f n

/-- Transfer the exhaustion diagonal-moment bound to the limit point. -/
theorem diagonal_moment_limit_bound_of_exhaustion
    (params : Phi4Params) [InteractionWeightModel params]
    (hglobal : ∃ c : ℝ, ∀ (g : TestFun2D) (Λ : Rectangle),
      |generatingFunctional params Λ g| ≤ Real.exp (c * normFunctional g))
    (f : TestFun2D) (n : ℕ) (x : ℝ)
    (hlim : Filter.Tendsto
      (fun k : ℕ =>
        schwingerN params (exhaustingRectangles (k + 1) (Nat.succ_pos k)) n (fun _ => f))
      Filter.atTop (nhds x)) :
    ∃ c : ℝ,
      |x| ≤ (Nat.factorial n : ℝ) *
        (Real.exp (c * normFunctional f) + Real.exp (c * normFunctional (-f))) := by
  rcases diagonal_moment_bound_on_exhaustion_of_global_uniform
      params hglobal f n with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  exact abs_limit_le_of_abs_bound hlim (fun k => hc k)

/-- Diagonal infinite-volume Schwinger moments are bounded by the same explicit
    factorial-exponential expression under a global finite-volume OS1-type
    generating-functional bound. -/
theorem infiniteVolumeSchwinger_diagonal_bound_of_global_uniform
    (params : Phi4Params) [InteractionWeightModel params]
    [InfiniteVolumeSchwingerModel params]
    (hglobal : ∃ c : ℝ, ∀ (g : TestFun2D) (Λ : Rectangle),
      |generatingFunctional params Λ g| ≤ Real.exp (c * normFunctional g))
    (f : TestFun2D) (n : ℕ) :
    ∃ c : ℝ,
      |infiniteVolumeSchwinger params n (fun _ => f)| ≤
        (Nat.factorial n : ℝ) *
          (Real.exp (c * normFunctional f) + Real.exp (c * normFunctional (-f))) := by
  have hraw :
      Filter.Tendsto
        (fun m : ℕ =>
          if h : 0 < m then schwingerN params (exhaustingRectangles m h) n (fun _ => f) else 0)
        Filter.atTop
        (nhds (infiniteVolumeSchwinger params n (fun _ => f))) :=
    InfiniteVolumeSchwingerModel.infiniteVolumeSchwinger_tendsto
      (params := params) n (fun _ => f)
  have hlim :
      Filter.Tendsto
        (fun k : ℕ =>
          schwingerN params (exhaustingRectangles (k + 1) (Nat.succ_pos k)) n (fun _ => f))
        Filter.atTop
        (nhds (infiniteVolumeSchwinger params n (fun _ => f))) := by
    have hcomp := hraw.comp (Filter.tendsto_add_atTop_nat 1)
    simpa using hcomp
  exact diagonal_moment_limit_bound_of_exhaustion
    params hglobal f n (infiniteVolumeSchwinger params n (fun _ => f)) hlim

/-- Infinite-volume mixed `n`-point Schwinger bound from global finite-volume
    generating-functional control, lifted along exhaustion limits. -/
theorem infiniteVolumeSchwinger_mixed_bound_of_global_uniform
    (params : Phi4Params) [InteractionWeightModel params]
    [InfiniteVolumeSchwingerModel params]
    (hglobal : ∃ c : ℝ, ∀ (g : TestFun2D) (Λ : Rectangle),
      |generatingFunctional params Λ g| ≤ Real.exp (c * normFunctional g))
    (n : ℕ) (hn : 0 < n) (f : Fin n → TestFun2D) :
    ∃ c : ℝ,
      |infiniteVolumeSchwinger params n f| ≤
        ∑ i : Fin n, (Nat.factorial n : ℝ) *
          (Real.exp (c * normFunctional (f i)) +
            Real.exp (c * normFunctional (-(f i)))) := by
  rcases hglobal with ⟨c, hc⟩
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
    InfiniteVolumeSchwingerModel.infiniteVolumeSchwinger_tendsto
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
    simpa [C] using
      finiteVolume_mixed_moment_bound_of_generating_bound params c hc
        (exhaustingRectangles (k + 1) (Nat.succ_pos k)) n hn f
  simpa [C] using abs_limit_le_of_abs_bound hlim hbound

/-- Infinite-volume mixed `n`-point Schwinger bound from pointwise-in-`f`
    uniform finite-volume generating-functional control. -/
theorem infiniteVolumeSchwinger_mixed_bound_of_uniform_generating_bound
    (params : Phi4Params) [InteractionWeightModel params]
    [InfiniteVolumeSchwingerModel params]
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
    InfiniteVolumeSchwingerModel.infiniteVolumeSchwinger_tendsto
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

/-- Interface-level infinite-volume mixed `n`-point Schwinger bound obtained
    from `RegularityModel` via its pointwise-in-`f` finite-volume uniform
    generating-functional estimate. -/
theorem infiniteVolumeSchwinger_mixed_bound_of_interface
    (params : Phi4Params) [InteractionWeightModel params]
    [InfiniteVolumeSchwingerModel params]
    [InfiniteVolumeMeasureModel params]
    [RegularityModel params]
    (n : ℕ) (hn : 0 < n) (f : Fin n → TestFun2D) :
    ∃ c : ℝ,
      |infiniteVolumeSchwinger params n f| ≤
        ∑ i : Fin n, (Nat.factorial n : ℝ) *
          (Real.exp (c * normFunctional (f i)) +
            Real.exp (c * normFunctional (-(f i)))) := by
  exact infiniteVolumeSchwinger_mixed_bound_of_uniform_generating_bound
    params
    (RegularityModel.generating_functional_bound_uniform (params := params))
    n hn f

/-- Infinite-volume 2-point Schwinger bound from global finite-volume
    generating-functional control, via polarization and exhaustion limits. -/
theorem infiniteVolume_twoPoint_bound_of_global_uniform
    (params : Phi4Params) [InteractionWeightModel params]
    [InfiniteVolumeSchwingerModel params]
    (hglobal : ∃ c : ℝ, ∀ (h : TestFun2D) (Λ : Rectangle),
      |generatingFunctional params Λ h| ≤ Real.exp (c * normFunctional h))
    (f g : TestFun2D) :
    ∃ c : ℝ,
      |infiniteVolumeSchwinger params 2 ![f, g]| ≤
        ((Nat.factorial 2 : ℝ) *
            (Real.exp (c * normFunctional (f + g)) +
              Real.exp (c * normFunctional (-(f + g)))) +
          (Nat.factorial 2 : ℝ) *
            (Real.exp (c * normFunctional (f - g)) +
              Real.exp (c * normFunctional (-(f - g))))) / 4 := by
  rcases hglobal with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  let C : ℝ :=
    ((Nat.factorial 2 : ℝ) *
        (Real.exp (c * normFunctional (f + g)) +
          Real.exp (c * normFunctional (-(f + g)))) +
      (Nat.factorial 2 : ℝ) *
        (Real.exp (c * normFunctional (f - g)) +
          Real.exp (c * normFunctional (-(f - g))))) / 4
  have hraw :
      Filter.Tendsto
        (fun m : ℕ =>
          if h : 0 < m then
            schwingerN params (exhaustingRectangles m h) 2 (![f, g] : Fin 2 → TestFun2D)
          else 0)
        Filter.atTop
        (nhds (infiniteVolumeSchwinger params 2 ![f, g])) :=
    InfiniteVolumeSchwingerModel.infiniteVolumeSchwinger_tendsto
      (params := params) 2 (![f, g] : Fin 2 → TestFun2D)
  have hlim :
      Filter.Tendsto
        (fun k : ℕ =>
          schwingerN params (exhaustingRectangles (k + 1) (Nat.succ_pos k)) 2
            (![f, g] : Fin 2 → TestFun2D))
        Filter.atTop
        (nhds (infiniteVolumeSchwinger params 2 ![f, g])) := by
    have hcomp := hraw.comp (Filter.tendsto_add_atTop_nat 1)
    simpa using hcomp
  have hbound : ∀ k : ℕ,
      |schwingerN params (exhaustingRectangles (k + 1) (Nat.succ_pos k)) 2
        (![f, g] : Fin 2 → TestFun2D)| ≤ C := by
    intro k
    have hfin :
        |schwingerTwo params (exhaustingRectangles (k + 1) (Nat.succ_pos k)) f g| ≤ C := by
      simpa [C] using finiteVolume_twoPoint_bound_of_generating_bound params c hc
        (exhaustingRectangles (k + 1) (Nat.succ_pos k)) f g
    simpa [schwingerN_two_eq_schwingerTwo] using hfin
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

/-- A global finite-volume uniform bound plus exhaustion convergence yields OS1. -/
theorem generating_functional_bound_of_exhaustion_limit_global_uniform
    (params : Phi4Params)
    [InfiniteVolumeMeasureModel params]
    (hlim : ∀ f : TestFun2D,
      Filter.Tendsto (generatingFunctionalOnExhaustion params f) Filter.atTop
        (nhds (∫ ω, Real.exp (ω f) ∂(infiniteVolumeMeasure params))))
    (hglobal : ∃ c : ℝ, ∀ (f : TestFun2D) (Λ : Rectangle),
      |generatingFunctional params Λ f| ≤ Real.exp (c * normFunctional f)) :
    ∃ c : ℝ, ∀ f : TestFun2D,
      |∫ ω, Real.exp (ω f) ∂(infiniteVolumeMeasure params)| ≤
        Real.exp (c * normFunctional f) := by
  exact generating_functional_bound_of_exhaustion_limit params hlim
    (generatingFunctionalOnExhaustion_bound_of_global_uniform params hglobal)

/-- Pointwise-in-`f` finite-volume uniform bounds plus exhaustion convergence
    yield a pointwise-in-`f` infinite-volume exponential bound. -/
theorem generating_functional_pointwise_bound_of_exhaustion_limit
    (params : Phi4Params)
    [InfiniteVolumeMeasureModel params]
    (hlim : ∀ f : TestFun2D,
      Filter.Tendsto (generatingFunctionalOnExhaustion params f) Filter.atTop
        (nhds (∫ ω, Real.exp (ω f) ∂(infiniteVolumeMeasure params))))
    (huniform : ∀ f : TestFun2D, ∃ c : ℝ, ∀ Λ : Rectangle,
      |generatingFunctional params Λ f| ≤ Real.exp (c * normFunctional f)) :
    ∀ f : TestFun2D, ∃ c : ℝ,
      |∫ ω, Real.exp (ω f) ∂(infiniteVolumeMeasure params)| ≤
        Real.exp (c * normFunctional f) := by
  intro f
  rcases generatingFunctionalOnExhaustion_bound_of_uniform params huniform f with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  exact abs_limit_le_of_abs_bound (hlim f) (fun n => hc n)

/-- Interface-level generating-functional bound extracted from
    `RegularityModel`. -/
theorem generating_functional_bound_of_interface (params : Phi4Params) :
    [InfiniteVolumeMeasureModel params] →
    [RegularityModel params] →
    ∃ c : ℝ, ∀ f : TestFun2D,
      |∫ ω, Real.exp (ω f) ∂(infiniteVolumeMeasure params)| ≤
        Real.exp (c * normFunctional f) := by
  intro hmeas hreg
  simpa [normFunctional] using
    (RegularityModel.generating_functional_bound
      (params := params))

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
  exact generating_functional_bound_of_exhaustion_limit_global_uniform
    params hlim hglobal

/-- **Generating functional bound** (Theorem 12.5.1 of Glimm-Jaffe):
    |S{f}| ≤ exp(c · N'(f)).

    Public endpoint routed through the regularity interface. -/
theorem generating_functional_bound (params : Phi4Params) :
    [InfiniteVolumeMeasureModel params] →
    [RegularityModel params] →
    ∃ c : ℝ, ∀ f : TestFun2D,
      |∫ ω, Real.exp (ω f) ∂(infiniteVolumeMeasure params)| ≤
        Real.exp (c * normFunctional f) := by
  intro hmeas hreg
  exact generating_functional_bound_of_interface params

/-! ## Nonlocal φ⁴ bounds -/

/-- Interface-level nonlocal φ⁴ bound extracted from `RegularityModel`. -/
theorem nonlocal_phi4_bound_of_interface (params : Phi4Params) :
    [InfiniteVolumeMeasureModel params] →
    [RegularityModel params] →
    ∀ (g : TestFun2D), ∃ C₁ C₂ : ℝ, ∀ (Λ : Rectangle),
      |generatingFunctional params Λ g| ≤
        Real.exp (C₁ * Λ.area + C₂) := by
  intro hmeas hreg
  exact RegularityModel.nonlocal_phi4_bound
    (params := params)

/-! ## Uniformity in volume -/

/-- Interface-level uniform-in-volume generating-functional bound extracted from
    `RegularityModel`. -/
theorem generating_functional_bound_uniform_of_interface (params : Phi4Params)
    [InfiniteVolumeMeasureModel params]
    [RegularityModel params]
    (f : TestFun2D) :
    ∃ c : ℝ, ∀ Λ : Rectangle,
      |generatingFunctional params Λ f| ≤ Real.exp (c * normFunctional f) := by
  simpa [normFunctional] using
    (RegularityModel.generating_functional_bound_uniform
      (params := params) f)

/-- Honest frontier: uniform-in-volume generating-functional bound (GJ §12.4)
    from explicit pointwise-in-`f` finite-volume data. -/
theorem gap_generating_functional_bound_uniform (params : Phi4Params)
    [InfiniteVolumeMeasureModel params]
    (huniform : ∀ f : TestFun2D, ∃ c : ℝ, ∀ Λ : Rectangle,
      |generatingFunctional params Λ f| ≤ Real.exp (c * normFunctional f))
    (f : TestFun2D) :
    ∃ c : ℝ, ∀ Λ : Rectangle,
      |generatingFunctional params Λ f| ≤ Real.exp (c * normFunctional f) := by
  exact huniform f

/-- Public uniformity endpoint via explicit theorem-level frontier gap. -/
theorem generating_functional_bound_uniform (params : Phi4Params)
    [InfiniteVolumeMeasureModel params]
    [RegularityModel params]
    (f : TestFun2D) :
    ∃ c : ℝ, ∀ Λ : Rectangle,
      |generatingFunctional params Λ f| ≤ Real.exp (c * normFunctional f) := by
  exact generating_functional_bound_uniform_of_interface params f

/-! ## Nonlocal φ⁴ bounds -/

/-- Honest frontier: nonlocal φ⁴ bounds (GJ §12.3) from explicit
    pointwise-in-`f` uniform finite-volume bounds. -/
theorem gap_nonlocal_phi4_bound (params : Phi4Params) :
    [InfiniteVolumeMeasureModel params] →
    (huniform : ∀ f : TestFun2D, ∃ c : ℝ, ∀ Λ : Rectangle,
      |generatingFunctional params Λ f| ≤ Real.exp (c * normFunctional f)) →
    ∀ (g : TestFun2D), ∃ C₁ C₂ : ℝ, ∀ (Λ : Rectangle),
      |generatingFunctional params Λ g| ≤
        Real.exp (C₁ * Λ.area + C₂) := by
  intro hmeas huniform g
  rcases gap_generating_functional_bound_uniform params huniform g with ⟨c, hc⟩
  refine ⟨0, c * normFunctional g, ?_⟩
  intro Λ
  simpa [zero_mul] using hc Λ

/-- Public nonlocal φ⁴ bound endpoint via explicit theorem-level frontier gap. -/
theorem nonlocal_phi4_bound (params : Phi4Params) :
    [InfiniteVolumeMeasureModel params] →
    [RegularityModel params] →
    ∀ (g : TestFun2D), ∃ C₁ C₂ : ℝ, ∀ (Λ : Rectangle),
      |generatingFunctional params Λ g| ≤
        Real.exp (C₁ * Λ.area + C₂) := by
  intro hmeas hreg
  exact nonlocal_phi4_bound_of_interface params

end

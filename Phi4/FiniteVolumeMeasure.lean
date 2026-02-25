/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.Interaction

/-!
# Finite Volume φ⁴₂ Measure

The finite-volume interacting measure is
  dμ_Λ = Z_Λ⁻¹ exp(-V_Λ) dφ_C
where V_Λ = λ ∫_Λ :φ⁴: dx is the interaction and Z_Λ = ∫ exp(-V_Λ) dφ_C is the
partition function. By Theorem 8.6.2, this is a well-defined probability measure.

The Schwinger functions (correlation functions) are
  S_n^Λ(f₁,...,fₙ) = ∫ φ(f₁)⋯φ(fₙ) dμ_Λ

## Main definitions

* `finiteVolumeMeasure` — dμ_Λ = Z_Λ⁻¹ e^{-V_Λ} dφ_C
* `partitionFunction` — Z_Λ = ∫ e^{-V_Λ} dφ_C
* `schwingerTwo` — 2-point Schwinger function S₂^Λ(f,g) = ⟨φ(f)φ(g)⟩_Λ

## References

* [Glimm-Jaffe] Sections 8.6, 11.2
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

/-! ## Partition function -/

/-- The partition function Z_Λ = ∫ exp(-V_Λ) dφ_C.
    By Theorem 8.6.2, this is finite and positive. -/
def partitionFunction (params : Phi4Params) (Λ : Rectangle) : ℝ :=
  ∫ ω, Real.exp (-(interaction params Λ ω)) ∂(freeFieldMeasure params.mass params.mass_pos)

/-! ## Finite volume measure -/

/-- The finite-volume interacting measure:
    dμ_Λ = Z_Λ⁻¹ exp(-V_Λ) dφ_C.
    This is a probability measure on S'(ℝ²). -/
def finiteVolumeMeasure (params : Phi4Params) (Λ : Rectangle) :
    @Measure FieldConfig2D GaussianField.instMeasurableSpaceConfiguration :=
  ENNReal.ofReal (partitionFunction params Λ)⁻¹ •
    (freeFieldMeasure params.mass params.mass_pos).withDensity
      (fun ω => ENNReal.ofReal (Real.exp (-(interaction params Λ ω))))

/-- The finite-volume measure is a probability measure. -/
theorem finiteVolumeMeasure_isProbability (params : Phi4Params) (Λ : Rectangle) :
    IsProbabilityMeasure (finiteVolumeMeasure params Λ) := by
  refine ⟨?_⟩
  have hZpos : 0 < partitionFunction params Λ := by
    simpa [partitionFunction] using partition_function_pos params Λ
  have hInt : Integrable (fun ω => Real.exp (-(interaction params Λ ω)))
      (freeFieldMeasure params.mass params.mass_pos) :=
    partition_function_integrable params Λ
  have h_nonneg :
      0 ≤ᵐ[freeFieldMeasure params.mass params.mass_pos]
        (fun ω => Real.exp (-(interaction params Λ ω))) :=
    Filter.Eventually.of_forall (fun _ => Real.exp_nonneg _)
  have hlin :
      ∫⁻ ω,
        ENNReal.ofReal (Real.exp (-(interaction params Λ ω)))
          ∂(freeFieldMeasure params.mass params.mass_pos) =
      ENNReal.ofReal (partitionFunction params Λ) := by
    rw [partitionFunction]
    exact (ofReal_integral_eq_lintegral_ofReal hInt h_nonneg).symm
  calc
    finiteVolumeMeasure params Λ Set.univ
        = ENNReal.ofReal (partitionFunction params Λ)⁻¹ *
            (freeFieldMeasure params.mass params.mass_pos).withDensity
              (fun ω => ENNReal.ofReal (Real.exp (-(interaction params Λ ω)))) Set.univ := by
          simp [finiteVolumeMeasure]
    _ = ENNReal.ofReal (partitionFunction params Λ)⁻¹ *
          ∫⁻ ω,
            ENNReal.ofReal (Real.exp (-(interaction params Λ ω)))
              ∂(freeFieldMeasure params.mass params.mass_pos) := by
          rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    _ = ENNReal.ofReal (partitionFunction params Λ)⁻¹ * ENNReal.ofReal (partitionFunction params Λ) := by
          rw [hlin]
    _ = 1 := by
          rw [ENNReal.ofReal_inv_of_pos hZpos]
          have hne0 : ENNReal.ofReal (partitionFunction params Λ) ≠ 0 := by
            intro hz0
            have hz_nonpos : partitionFunction params Λ ≤ 0 :=
              (ENNReal.ofReal_eq_zero.mp hz0)
            linarith
          have hneTop : ENNReal.ofReal (partitionFunction params Λ) ≠ ⊤ := by
            simp
          exact ENNReal.inv_mul_cancel hne0 hneTop

/-! ## Schwinger functions (correlation functions) -/

/-- The 2-point Schwinger function in finite volume:
    S₂^Λ(f, g) = ∫ ω(f) · ω(g) dμ_Λ(ω) = ⟨φ(f)φ(g)⟩_Λ. -/
def schwingerTwo (params : Phi4Params) (Λ : Rectangle)
    (f g : TestFun2D) : ℝ :=
  ∫ ω, ω f * ω g ∂(finiteVolumeMeasure params Λ)

/-- The n-point Schwinger function in finite volume:
    S_n^Λ(f₁,...,fₙ) = ∫ ω(f₁)⋯ω(fₙ) dμ_Λ(ω). -/
def schwingerN (params : Phi4Params) (Λ : Rectangle) (n : ℕ)
    (f : Fin n → TestFun2D) : ℝ :=
  ∫ ω, (∏ i, ω (f i)) ∂(finiteVolumeMeasure params Λ)

/-- The generating functional (Laplace transform) in finite volume:
    S_Λ{g} = ∫ exp(⟨ω, g⟩) dμ_Λ(ω) for real test functions g. -/
def generatingFunctional (params : Phi4Params) (Λ : Rectangle)
    (g : TestFun2D) : ℝ :=
  ∫ ω, Real.exp (ω g) ∂(finiteVolumeMeasure params Λ)

/-! ## Basic properties -/

/-- Symmetry of the 2-point function: S₂(f,g) = S₂(g,f). -/
theorem schwingerTwo_symm (params : Phi4Params) (Λ : Rectangle)
    (f g : TestFun2D) :
    schwingerTwo params Λ f g = schwingerTwo params Λ g f := by
  simp only [schwingerTwo, mul_comm]

/-- The n-point Schwinger function is symmetric under permutations.
    Proof: the product ∏ᵢ ω(f(σ(i))) = ∏ᵢ ω(f(i)) by `Equiv.prod_comp`. -/
theorem schwingerN_perm (params : Phi4Params) (Λ : Rectangle) (n : ℕ)
    (f : Fin n → TestFun2D) (σ : Equiv.Perm (Fin n)) :
    schwingerN params Λ n (f ∘ σ) = schwingerN params Λ n f := by
  simp only [schwingerN, Function.comp]
  congr 1; funext ω
  exact Equiv.prod_comp σ (fun i => ω (f i))

private lemma phi4_holderTriple_double (p : ℝ≥0∞) :
    ENNReal.HolderTriple (2 * p) (2 * p) p where
  inv_add_inv_eq_inv := by
    have h2_ne_zero : (2 : ℝ≥0∞) ≠ 0 := two_ne_zero
    have h2_ne_top : (2 : ℝ≥0∞) ≠ ⊤ := ENNReal.ofNat_ne_top
    calc
      (2 * p)⁻¹ + (2 * p)⁻¹
          = 2 * (2 * p)⁻¹ := (two_mul _).symm
      _ = 2 * (2⁻¹ * p⁻¹) := by
            congr 1
            exact ENNReal.mul_inv (Or.inl h2_ne_zero) (Or.inl h2_ne_top)
      _ = (2 * 2⁻¹) * p⁻¹ := by rw [mul_assoc]
      _ = 1 * p⁻¹ := by rw [ENNReal.mul_inv_cancel h2_ne_zero h2_ne_top]
      _ = p⁻¹ := one_mul _

private theorem freeField_product_memLp
    (mass : ℝ) (hmass : 0 < mass) :
    ∀ (n : ℕ) (f : Fin n → TestFun2D) (p : ℝ≥0),
      MemLp (fun ω : FieldConfig2D => ∏ i, ω (f i)) (↑p) (freeFieldMeasure mass hmass) := by
  intro n
  induction n with
  | zero =>
      intro f p
      simp
      exact memLp_const 1
  | succ n ih =>
      intro f p
      simp_rw [Fin.prod_univ_succ]
      set T := freeCovarianceCLM mass hmass
      haveI : ENNReal.HolderTriple (↑(2 * p)) (↑(2 * p)) (↑p) := by
        rw [ENNReal.coe_mul]
        exact phi4_holderTriple_double (↑p)
      have hf0 : MemLp (fun ω : FieldConfig2D => ω (f 0)) (↑(2 * p))
          (freeFieldMeasure mass hmass) :=
        GaussianField.pairing_memLp T (f 0) (2 * p)
      have htail : MemLp (fun ω : FieldConfig2D => ∏ i : Fin n, ω (f (Fin.succ i)))
          (↑(2 * p)) (freeFieldMeasure mass hmass) :=
        ih (fun i => f (Fin.succ i)) (2 * p)
      exact htail.mul' hf0

private theorem finiteVolume_product_integrable
    (params : Phi4Params) (Λ : Rectangle) (n : ℕ) (f : Fin n → TestFun2D) :
    Integrable (fun ω : FieldConfig2D => ∏ i, ω (f i)) (finiteVolumeMeasure params Λ) := by
  set μ := freeFieldMeasure params.mass params.mass_pos
  set w : FieldConfig2D → ℝ := fun ω => Real.exp (-(interaction params Λ ω))
  set d : FieldConfig2D → ℝ≥0∞ := fun ω => ENNReal.ofReal (w ω)

  have hwInt : Integrable w μ := by
    simpa [w, μ] using partition_function_integrable params Λ
  have hwMeas : AEMeasurable w μ := hwInt.aestronglyMeasurable.aemeasurable
  have hdMeas : AEMeasurable d μ := by
    simpa [d] using hwMeas.ennreal_ofReal
  have hdLtTop : ∀ᵐ ω ∂μ, d ω < ⊤ := by
    filter_upwards with ω
    simp [d]

  have hprodL2 : MemLp (fun ω : FieldConfig2D => ∏ i, ω (f i)) (2 : ℝ≥0∞) μ := by
    simpa [μ] using freeField_product_memLp params.mass params.mass_pos n f (2 : ℝ≥0)
  have hwL2 : MemLp w (2 : ℝ≥0∞) μ := by
    simpa [w, μ] using (exp_interaction_Lp params Λ (p := (2 : ℝ≥0∞)) (by norm_num))

  have hmulInt : Integrable (fun ω : FieldConfig2D => w ω * ∏ i, ω (f i)) μ := by
    have hmulInt' : Integrable ((fun ω : FieldConfig2D => ∏ i, ω (f i)) * w) μ :=
      hprodL2.integrable_mul hwL2
    refine hmulInt'.congr ?_
    filter_upwards with ω
    simp [mul_comm]

  have hsmulInt : Integrable (fun ω : FieldConfig2D => (d ω).toReal • (∏ i, ω (f i))) μ := by
    refine hmulInt.congr ?_
    filter_upwards with ω
    simp [d, w, Real.exp_nonneg, smul_eq_mul]

  have hwd : Integrable (fun ω : FieldConfig2D => ∏ i, ω (f i)) (μ.withDensity d) :=
    (integrable_withDensity_iff_integrable_smul₀' hdMeas hdLtTop).2 hsmulInt

  have hZpos : 0 < partitionFunction params Λ := by
    simpa [partitionFunction] using partition_function_pos params Λ
  have hscale_ne_top : ENNReal.ofReal (partitionFunction params Λ)⁻¹ ≠ ⊤ := by
    simpa [ENNReal.inv_ne_top] using (ENNReal.ofReal_ne_zero.2 hZpos)

  have hscaled : Integrable (fun ω : FieldConfig2D => ∏ i, ω (f i))
      (ENNReal.ofReal (partitionFunction params Λ)⁻¹ • (μ.withDensity d)) :=
    hwd.smul_measure hscale_ne_top
  simpa [finiteVolumeMeasure, μ, d] using hscaled

/-- The Schwinger functions are multilinear in each argument.
    Proof: ω is linear (WeakDual), so the product splits at index i,
    and the integral distributes by linearity. -/
theorem schwingerN_multilinear (params : Phi4Params) (Λ : Rectangle) (n : ℕ)
    (f g : Fin n → TestFun2D) (c : ℝ) (i : Fin n) :
    schwingerN params Λ n (Function.update f i (c • f i + g i)) =
      c * schwingerN params Λ n f +
        schwingerN params Λ n (Function.update f i (g i)) := by
  simp only [schwingerN]
  -- Step 1: Pointwise identity for the integrands
  have h_pw : ∀ ω : FieldConfig2D,
      (∏ j, ω ((Function.update f i (c • f i + g i)) j)) =
        c * (∏ j, ω (f j)) + (∏ j, ω ((Function.update f i (g i)) j)) := by
    intro ω
    -- Extract the i-th factor from each product
    set P := (∏ j ∈ Finset.univ.erase i, ω (f j)) with hP_def
    have hi := Finset.mem_univ i
    have h1 : (∏ j, ω ((Function.update f i (c • f i + g i)) j)) =
        ω (c • f i + g i) * P := by
      rw [← Finset.mul_prod_erase _ _ hi, Function.update_self]
      congr 1
      exact Finset.prod_congr rfl fun j hj =>
        by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    have h2 : (∏ j, ω (f j)) = ω (f i) * P :=
      (Finset.mul_prod_erase _ _ hi).symm
    have h3 : (∏ j, ω ((Function.update f i (g i)) j)) = ω (g i) * P := by
      rw [← Finset.mul_prod_erase _ _ hi, Function.update_self]
      congr 1
      exact Finset.prod_congr rfl fun j hj =>
        by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    rw [h1, h2, h3, map_add, map_smul, smul_eq_mul]
    ring
  -- Step 2: Rewrite the integrand using pointwise identity
  have h_eq : (fun ω : FieldConfig2D =>
      ∏ j, ω ((Function.update f i (c • f i + g i)) j)) =
      fun ω => c * ∏ j, ω (f j) + ∏ j, ω ((Function.update f i (g i)) j) :=
    funext h_pw
  simp only [h_eq]
  -- Step 3: Use integral linearity
  have h_int1 : Integrable (fun ω : FieldConfig2D => c * ∏ j, ω (f j))
      (finiteVolumeMeasure params Λ) :=
    (finiteVolume_product_integrable params Λ n f).const_mul c
  have h_int2 : Integrable (fun ω : FieldConfig2D =>
      ∏ j, ω (Function.update f i (g i) j))
      (finiteVolumeMeasure params Λ) :=
    finiteVolume_product_integrable params Λ n (Function.update f i (g i))
  rw [integral_add h_int1 h_int2, integral_const_mul]

/-- The 2-point function is bounded by the free field 2-point function
    (for the φ⁴ interaction with λ > 0). This is a consequence of the
    Lebowitz inequality. -/
theorem schwingerTwo_le_free (params : Phi4Params) (Λ : Rectangle)
    (f g : TestFun2D) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) :
    schwingerTwo params Λ f g ≤
      ∫ ω, ω f * ω g ∂(freeFieldMeasure params.mass params.mass_pos) := by
  sorry

end

/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.Interaction.Part3

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
open scoped ProbabilityTheory

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
theorem finiteVolumeMeasure_isProbability (params : Phi4Params)
    [InteractionWeightModel params]
    (Λ : Rectangle) :
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

/-- `finiteVolumeMeasure_isProbability` from an explicit witness of
    `InteractionWeightModel`, avoiding direct typeclass assumptions
    at theorem-call sites. -/
theorem finiteVolumeMeasure_isProbability_of_nonempty_interactionWeightModel
    (params : Phi4Params) (Λ : Rectangle)
    (hW : Nonempty (InteractionWeightModel params)) :
    IsProbabilityMeasure (finiteVolumeMeasure params Λ) := by
  rcases hW with ⟨hWinst⟩
  letI : InteractionWeightModel params := hWinst
  exact finiteVolumeMeasure_isProbability params Λ

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

/-- Zeroth Schwinger function normalization in finite volume:
    `S_0^Λ = 1` for any choice of the unique `Fin 0 → TestFun2D`. -/
theorem schwingerN_zero (params : Phi4Params)
    [InteractionWeightModel params]
    (Λ : Rectangle) (f : Fin 0 → TestFun2D) :
    schwingerN params Λ 0 f = 1 := by
  have hprob : IsProbabilityMeasure (finiteVolumeMeasure params Λ) :=
    finiteVolumeMeasure_isProbability params Λ
  letI : IsProbabilityMeasure (finiteVolumeMeasure params Λ) := hprob
  calc
    schwingerN params Λ 0 f
        = ∫ ω : FieldConfig2D, (1 : ℝ) ∂(finiteVolumeMeasure params Λ) := by
          simp [schwingerN]
    _ = 1 := by
          rw [integral_const]
          simp

/-- The 2-point Schwinger function as the `n = 2` case of `schwingerN`. -/
theorem schwingerN_two_eq_schwingerTwo (params : Phi4Params) (Λ : Rectangle)
    (f : Fin 2 → TestFun2D) :
    schwingerN params Λ 2 f = schwingerTwo params Λ (f 0) (f 1) := by
  simp [schwingerN, schwingerTwo, Fin.prod_univ_two]

/-- Connected (truncated) finite-volume 2-point function:
    `S₂^Λ(f,g) - S₁^Λ(f)S₁^Λ(g)`. -/
def connectedSchwingerTwo (params : Phi4Params) (Λ : Rectangle)
    (f g : TestFun2D) : ℝ :=
  schwingerTwo params Λ f g -
    schwingerN params Λ 1 ![f] * schwingerN params Λ 1 ![g]

@[simp] theorem connectedSchwingerTwo_eq (params : Phi4Params) (Λ : Rectangle)
    (f g : TestFun2D) :
    connectedSchwingerTwo params Λ f g =
      schwingerTwo params Λ f g -
        schwingerN params Λ 1 ![f] * schwingerN params Λ 1 ![g] := rfl

/-- The generating functional (Laplace transform) in finite volume:
    S_Λ{g} = ∫ exp(⟨ω, g⟩) dμ_Λ(ω) for real test functions g. -/
def generatingFunctional (params : Phi4Params) (Λ : Rectangle)
    (g : TestFun2D) : ℝ :=
  ∫ ω, Real.exp (ω g) ∂(finiteVolumeMeasure params Λ)

theorem generatingFunctional_nonneg (params : Phi4Params) (Λ : Rectangle)
    (g : TestFun2D) :
    0 ≤ generatingFunctional params Λ g := by
  unfold generatingFunctional
  exact integral_nonneg_of_ae (Filter.Eventually.of_forall (fun ω => Real.exp_nonneg (ω g)))

/-! ## Basic properties -/

/-- Symmetry of the 2-point function: S₂(f,g) = S₂(g,f). -/
theorem schwingerTwo_symm (params : Phi4Params) (Λ : Rectangle)
    (f g : TestFun2D) :
    schwingerTwo params Λ f g = schwingerTwo params Λ g f := by
  simp only [schwingerTwo, mul_comm]

/-- Symmetry of connected 2-point function in finite volume. -/
theorem connectedSchwingerTwo_symm (params : Phi4Params) (Λ : Rectangle)
    (f g : TestFun2D) :
    connectedSchwingerTwo params Λ f g = connectedSchwingerTwo params Λ g f := by
  unfold connectedSchwingerTwo
  rw [schwingerTwo_symm, mul_comm]

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
    (params : Phi4Params) [InteractionWeightModel params]
    (Λ : Rectangle) (n : ℕ) (f : Fin n → TestFun2D) :
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
    simp [hZpos]

  have hscaled : Integrable (fun ω : FieldConfig2D => ∏ i, ω (f i))
      (ENNReal.ofReal (partitionFunction params Λ)⁻¹ • (μ.withDensity d)) :=
    hwd.smul_measure hscale_ne_top
  simpa [finiteVolumeMeasure, μ, d] using hscaled

private theorem finiteVolume_pairing_exp_integrable
    (params : Phi4Params) [InteractionWeightModel params]
    (Λ : Rectangle) (f : TestFun2D) (t : ℝ) :
    Integrable (fun ω : FieldConfig2D => Real.exp (t * ω f))
      (finiteVolumeMeasure params Λ) := by
  set μ := freeFieldMeasure params.mass params.mass_pos
  set w : FieldConfig2D → ℝ := fun ω => Real.exp (-(interaction params Λ ω))
  set d : FieldConfig2D → ℝ≥0∞ := fun ω => ENNReal.ofReal (w ω)
  set X : FieldConfig2D → ℝ := fun ω => Real.exp (t * ω f)

  have hwInt : Integrable w μ := by
    simpa [w, μ] using partition_function_integrable params Λ
  have hwMeas : AEMeasurable w μ := hwInt.aestronglyMeasurable.aemeasurable
  have hdMeas : AEMeasurable d μ := by
    simpa [d] using hwMeas.ennreal_ofReal
  have hdLtTop : ∀ᵐ ω ∂μ, d ω < ⊤ := by
    filter_upwards with ω
    simp [d]

  have hXL2 : MemLp X (2 : ℝ≥0∞) μ := by
    have hXInt : Integrable X μ := by
      simpa [X, μ] using freeField_pairing_exp_integrable params.mass params.mass_pos f t
    have hX2Int : Integrable (fun ω : FieldConfig2D => (X ω) ^ 2) μ := by
      have h2t :
          Integrable (fun ω : FieldConfig2D => Real.exp ((2 * t) * ω f)) μ := by
        simpa [μ] using freeField_pairing_exp_integrable params.mass params.mass_pos f (2 * t)
      refine h2t.congr ?_
      filter_upwards with ω
      calc
        Real.exp ((2 * t) * ω f)
            = Real.exp (t * ω f + t * ω f) := by ring_nf
        _ = Real.exp (t * ω f) * Real.exp (t * ω f) := by
              rw [Real.exp_add]
        _ = (X ω) ^ 2 := by
              simp [X, pow_two]
    exact (memLp_two_iff_integrable_sq hXInt.aestronglyMeasurable).2 hX2Int
  have hwL2 : MemLp w (2 : ℝ≥0∞) μ := by
    simpa [w, μ] using (exp_interaction_Lp params Λ (p := (2 : ℝ≥0∞)) (by norm_num))

  have hmulInt : Integrable (fun ω : FieldConfig2D => X ω * w ω) μ :=
    hXL2.integrable_mul hwL2
  have hsmulInt : Integrable (fun ω : FieldConfig2D => (d ω).toReal • X ω) μ := by
    refine hmulInt.congr ?_
    filter_upwards with ω
    simp [d, w, X, Real.exp_nonneg, smul_eq_mul, mul_comm]

  have hwd : Integrable X (μ.withDensity d) :=
    (integrable_withDensity_iff_integrable_smul₀' hdMeas hdLtTop).2 hsmulInt

  have hZpos : 0 < partitionFunction params Λ := by
    simpa [partitionFunction] using partition_function_pos params Λ
  have hscale_ne_top : ENNReal.ofReal (partitionFunction params Λ)⁻¹ ≠ ⊤ := by
    simp [hZpos]

  have hscaled : Integrable X
      (ENNReal.ofReal (partitionFunction params Λ)⁻¹ • (μ.withDensity d)) :=
    hwd.smul_measure hscale_ne_top
  simpa [finiteVolumeMeasure, μ, d, X] using hscaled

private theorem abs_pow_le_factorial_mul_exp_abs (x : ℝ) (n : ℕ) :
    |x| ^ n ≤ (Nat.factorial n : ℝ) * Real.exp |x| := by
  have h0 : 0 ≤ |x| := abs_nonneg x
  have hpow : |x| ^ n / (Nat.factorial n : ℝ) ≤ Real.exp |x| :=
    Real.pow_div_factorial_le_exp (x := |x|) h0 n
  have hfac_pos : 0 < (Nat.factorial n : ℝ) :=
    Nat.cast_pos.mpr (Nat.factorial_pos n)
  have hmul : |x| ^ n ≤ Real.exp |x| * (Nat.factorial n : ℝ) :=
    (div_le_iff₀ hfac_pos).1 hpow
  simpa [mul_comm] using hmul

private theorem abs_pow_le_factorial_mul_exp_add_exp_neg (x : ℝ) (n : ℕ) :
    |x| ^ n ≤ (Nat.factorial n : ℝ) * (Real.exp x + Real.exp (-x)) := by
  calc
    |x| ^ n ≤ (Nat.factorial n : ℝ) * Real.exp |x| := abs_pow_le_factorial_mul_exp_abs x n
    _ ≤ (Nat.factorial n : ℝ) * (Real.exp x + Real.exp (-x)) := by
      exact mul_le_mul_of_nonneg_left (Real.exp_abs_le x) (by positivity)

private theorem abs_prod_le_sum_abs_pow {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) :
    |∏ i, x i| ≤ ∑ i, |(x i) ^ n| := by
  have hw : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ (1 : ℝ) := by
    intro i hi
    positivity
  have hwpos : 0 < ∑ i ∈ (Finset.univ : Finset (Fin n)), (1 : ℝ) := by
    simp [hn]
  have hz : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ (|x i| : ℝ) := by
    intro i hi
    positivity
  have hgeom :=
    Real.geom_mean_le_arith_mean (s := (Finset.univ : Finset (Fin n)))
      (w := fun _ => (1 : ℝ)) (z := fun i => (|x i| : ℝ))
      hw hwpos hz
  have hgeom' : (∏ i, |x i|) ^ ((n : ℝ)⁻¹) ≤ (∑ i, |x i|) / n := by
    simpa [Finset.sum_const, Fintype.card_fin, div_eq_mul_inv] using hgeom
  have hprod_nonneg : 0 ≤ ∏ i, |x i| := by
    exact Finset.prod_nonneg (by intro i hi; positivity)
  have hmean_nonneg : 0 ≤ (∑ i, |x i|) / n := by
    positivity
  have hn_real_pos : (0 : ℝ) < n := by
    exact_mod_cast hn
  have hprod_le_meanpow :
      ∏ i, |x i| ≤ ((∑ i, |x i|) / n) ^ (n : ℝ) := by
    exact (Real.rpow_inv_le_iff_of_pos hprod_nonneg hmean_nonneg hn_real_pos).1 hgeom'
  have hwnonneg : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ ((n : ℝ)⁻¹) := by
    intro i hi
    positivity
  have hwsum : ∑ i ∈ (Finset.univ : Finset (Fin n)), ((n : ℝ)⁻¹) = 1 := by
    have hn0 : (n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hn)
    simp [Finset.sum_const, Fintype.card_fin, hn0]
  have hpowmean :=
    Real.pow_arith_mean_le_arith_mean_pow
      (s := (Finset.univ : Finset (Fin n)))
      (w := fun _ => ((n : ℝ)⁻¹))
      (z := fun i => (|x i| : ℝ))
      hwnonneg hwsum hz n
  have hmeanpow_le :
      ((∑ i, |x i|) / n) ^ (n : ℝ) ≤ (∑ i, |x i| ^ n) / n := by
    simpa [Real.rpow_natCast, div_eq_mul_inv, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
      using hpowmean
  have hsum_nonneg : 0 ≤ ∑ i, |x i| ^ n := by
    exact Finset.sum_nonneg (by intro i hi; positivity)
  have hn_one : (1 : ℝ) ≤ n := by
    exact_mod_cast (Nat.succ_le_of_lt hn)
  have hdiv_le : (∑ i, |x i| ^ n) / n ≤ ∑ i, |x i| ^ n := by
    exact div_le_self hsum_nonneg hn_one
  have habs : |∏ i, x i| = ∏ i, |x i| := by
    simpa using (Finset.abs_prod (s := (Finset.univ : Finset (Fin n))) (f := x))
  calc
    |∏ i, x i| = ∏ i, |x i| := habs
    _ ≤ ((∑ i, |x i|) / n) ^ (n : ℝ) := hprod_le_meanpow
    _ ≤ (∑ i, |x i| ^ n) / n := hmeanpow_le
    _ ≤ ∑ i, |x i| ^ n := hdiv_le
    _ = ∑ i, |(x i) ^ n| := by simp [abs_pow]

/-- Absolute `n`-th moment of a single field pairing under the finite-volume
    interacting measure is controlled by the same factorial-generating-functional
    expression as in the diagonal Schwinger estimate. -/
theorem finiteVolume_pairing_abs_moment_le_factorial_mul_generatingFunctional_pair
    (params : Phi4Params) [InteractionWeightModel params]
    (Λ : Rectangle) (f : TestFun2D) (n : ℕ) :
    ∫ ω, |(ω f) ^ n| ∂(finiteVolumeMeasure params Λ) ≤
      (Nat.factorial n : ℝ) *
        (generatingFunctional params Λ f + generatingFunctional params Λ (-f)) := by
  set μ : Measure FieldConfig2D := finiteVolumeMeasure params Λ
  have hExp : Integrable (fun ω : FieldConfig2D => Real.exp (ω f)) μ := by
    simpa [μ] using finiteVolume_pairing_exp_integrable params Λ f 1
  have hExpNeg : Integrable (fun ω : FieldConfig2D => Real.exp (-(ω f))) μ := by
    simpa [μ] using finiteVolume_pairing_exp_integrable params Λ f (-1)
  have hpowInt : Integrable (fun ω : FieldConfig2D => (ω f) ^ n) μ := by
    have hprod := finiteVolume_product_integrable params Λ n (fun _ => f)
    refine hprod.congr ?_
    filter_upwards with ω
    simp
  have hnormInt : Integrable (fun ω : FieldConfig2D => |(ω f) ^ n|) μ := hpowInt.norm
  have hsumInt : Integrable (fun ω : FieldConfig2D => Real.exp (ω f) + Real.exp (-(ω f))) μ :=
    hExp.add hExpNeg
  have hrhsInt :
      Integrable (fun ω : FieldConfig2D =>
        (Nat.factorial n : ℝ) * (Real.exp (ω f) + Real.exp (-(ω f)))) μ :=
    hsumInt.const_mul (Nat.factorial n : ℝ)
  have hpoint :
      ∀ ω : FieldConfig2D,
        |(ω f) ^ n| ≤ (Nat.factorial n : ℝ) * (Real.exp (ω f) + Real.exp (-(ω f))) := by
    intro ω
    have hbase := abs_pow_le_factorial_mul_exp_add_exp_neg (ω f) n
    simpa [abs_pow] using hbase
  have hmono :
      ∫ ω, |(ω f) ^ n| ∂μ ≤
        ∫ ω, (Nat.factorial n : ℝ) * (Real.exp (ω f) + Real.exp (-(ω f))) ∂μ :=
    integral_mono_ae hnormInt hrhsInt (Filter.Eventually.of_forall hpoint)
  have hrhs_eval :
      ∫ ω, (Nat.factorial n : ℝ) * (Real.exp (ω f) + Real.exp (-(ω f))) ∂μ =
        (Nat.factorial n : ℝ) *
          (generatingFunctional params Λ f + generatingFunctional params Λ (-f)) := by
    calc
      ∫ ω, (Nat.factorial n : ℝ) * (Real.exp (ω f) + Real.exp (-(ω f))) ∂μ
          = (Nat.factorial n : ℝ) * ∫ ω, (Real.exp (ω f) + Real.exp (-(ω f))) ∂μ := by
              rw [integral_const_mul]
      _ = (Nat.factorial n : ℝ) *
            ((∫ ω, Real.exp (ω f) ∂μ) + (∫ ω, Real.exp (-(ω f)) ∂μ)) := by
            rw [integral_add hExp hExpNeg]
      _ = (Nat.factorial n : ℝ) *
            (generatingFunctional params Λ f + generatingFunctional params Λ (-f)) := by
            simp [μ, generatingFunctional]
  exact hmono.trans_eq hrhs_eval

/-- Diagonal finite-volume Schwinger moments are controlled by two generating
    functionals at `f` and `-f`:
    `|S_n^Λ(f,…,f)| ≤ n! (S_Λ{f} + S_Λ{-f})`.

    The hypotheses provide integrability of the two exponential observables
    under the finite-volume interacting measure. -/
theorem schwingerN_const_abs_le_factorial_mul_generatingFunctional_pair
    (params : Phi4Params) [InteractionWeightModel params]
    (Λ : Rectangle) (f : TestFun2D) (n : ℕ) :
    |schwingerN params Λ n (fun _ => f)| ≤
      (Nat.factorial n : ℝ) *
        (generatingFunctional params Λ f + generatingFunctional params Λ (-f)) := by
  set μ : Measure FieldConfig2D := finiteVolumeMeasure params Λ
  have hExp : Integrable (fun ω : FieldConfig2D => Real.exp (ω f)) μ := by
    simpa [μ] using finiteVolume_pairing_exp_integrable params Λ f 1
  have hExpNeg : Integrable (fun ω : FieldConfig2D => Real.exp (-(ω f))) μ := by
    simpa [μ] using finiteVolume_pairing_exp_integrable params Λ f (-1)
  have hpowInt : Integrable (fun ω : FieldConfig2D => (ω f) ^ n) μ := by
    have hprod := finiteVolume_product_integrable params Λ n (fun _ => f)
    refine hprod.congr ?_
    filter_upwards with ω
    simp
  have hnormInt : Integrable (fun ω : FieldConfig2D => |(ω f) ^ n|) μ := hpowInt.norm
  have hsumInt : Integrable (fun ω : FieldConfig2D => Real.exp (ω f) + Real.exp (-(ω f))) μ :=
    hExp.add hExpNeg
  have hrhsInt :
      Integrable (fun ω : FieldConfig2D =>
        (Nat.factorial n : ℝ) * (Real.exp (ω f) + Real.exp (-(ω f)))) μ :=
    hsumInt.const_mul (Nat.factorial n : ℝ)
  have hpoint :
      ∀ ω : FieldConfig2D,
        |(ω f) ^ n| ≤ (Nat.factorial n : ℝ) * (Real.exp (ω f) + Real.exp (-(ω f))) := by
    intro ω
    have hbase := abs_pow_le_factorial_mul_exp_add_exp_neg (ω f) n
    simpa [abs_pow] using hbase
  have hmono :
      ∫ ω, |(ω f) ^ n| ∂μ ≤
        ∫ ω, (Nat.factorial n : ℝ) * (Real.exp (ω f) + Real.exp (-(ω f))) ∂μ :=
    integral_mono_ae hnormInt hrhsInt (Filter.Eventually.of_forall hpoint)
  have hnorm :
      |∫ ω, (ω f) ^ n ∂μ| ≤ ∫ ω, |(ω f) ^ n| ∂μ := by
    simpa [Real.norm_eq_abs] using
      (norm_integral_le_integral_norm (f := fun ω : FieldConfig2D => (ω f) ^ n))
  have hrhs_eval :
      ∫ ω, (Nat.factorial n : ℝ) * (Real.exp (ω f) + Real.exp (-(ω f))) ∂μ =
        (Nat.factorial n : ℝ) *
          (generatingFunctional params Λ f + generatingFunctional params Λ (-f)) := by
    calc
      ∫ ω, (Nat.factorial n : ℝ) * (Real.exp (ω f) + Real.exp (-(ω f))) ∂μ
          = (Nat.factorial n : ℝ) * ∫ ω, (Real.exp (ω f) + Real.exp (-(ω f))) ∂μ := by
              rw [integral_const_mul]
      _ = (Nat.factorial n : ℝ) *
            ((∫ ω, Real.exp (ω f) ∂μ) + (∫ ω, Real.exp (-(ω f)) ∂μ)) := by
            rw [integral_add hExp hExpNeg]
      _ = (Nat.factorial n : ℝ) *
            (generatingFunctional params Λ f + generatingFunctional params Λ (-f)) := by
            simp [μ, generatingFunctional]
  have hsch : schwingerN params Λ n (fun _ => f) = ∫ ω, (ω f) ^ n ∂μ := by
    simp [schwingerN, μ]
  calc
    |schwingerN params Λ n (fun _ => f)|
        = |∫ ω, (ω f) ^ n ∂μ| := by rw [hsch]
    _ ≤ ∫ ω, |(ω f) ^ n| ∂μ := hnorm
    _ ≤ ∫ ω, (Nat.factorial n : ℝ) * (Real.exp (ω f) + Real.exp (-(ω f))) ∂μ := hmono
    _ = (Nat.factorial n : ℝ) *
          (generatingFunctional params Λ f + generatingFunctional params Λ (-f)) := hrhs_eval

/-- Mixed finite-volume `n`-point Schwinger function bound from diagonal
    absolute-moment control:
    `|S_n^Λ(f₁,…,fₙ)|` is bounded by the sum of diagonal factorial-generating
    bounds for each individual argument. -/
theorem schwingerN_abs_le_sum_factorial_mul_generatingFunctional_pair
    (params : Phi4Params) [InteractionWeightModel params]
    (Λ : Rectangle) (n : ℕ) (hn : 0 < n) (f : Fin n → TestFun2D) :
    |schwingerN params Λ n f| ≤
      ∑ i : Fin n, (Nat.factorial n : ℝ) *
        (generatingFunctional params Λ (f i) + generatingFunctional params Λ (-(f i))) := by
  set μ : Measure FieldConfig2D := finiteVolumeMeasure params Λ
  have hprodInt : Integrable (fun ω : FieldConfig2D => ∏ i, ω (f i)) μ :=
    finiteVolume_product_integrable params Λ n f
  have hpowInt : ∀ i : Fin n, Integrable (fun ω : FieldConfig2D => (ω (f i)) ^ n) μ := by
    intro i
    have hprod := finiteVolume_product_integrable params Λ n (fun _ => f i)
    refine hprod.congr ?_
    filter_upwards with ω
    simp
  have hsumInt :
      Integrable (fun ω : FieldConfig2D => ∑ i : Fin n, |(ω (f i)) ^ n|) μ := by
    have hsumInt' :
        Integrable
          (fun ω : FieldConfig2D =>
            ∑ i ∈ (Finset.univ : Finset (Fin n)), |(ω (f i)) ^ n|) μ := by
      exact MeasureTheory.integrable_finset_sum (s := (Finset.univ : Finset (Fin n)))
        (fun i hi => (hpowInt i).norm)
    simpa using hsumInt'
  have hpoint :
      ∀ ω : FieldConfig2D, |∏ i, ω (f i)| ≤ ∑ i : Fin n, |(ω (f i)) ^ n| := by
    intro ω
    simpa using abs_prod_le_sum_abs_pow hn (fun i : Fin n => ω (f i))
  have hmono :
      ∫ ω, |∏ i, ω (f i)| ∂μ ≤
        ∫ ω, ∑ i : Fin n, |(ω (f i)) ^ n| ∂μ :=
    integral_mono_ae hprodInt.norm hsumInt (Filter.Eventually.of_forall hpoint)
  have hsumEval :
      ∫ ω, ∑ i : Fin n, |(ω (f i)) ^ n| ∂μ =
        ∑ i : Fin n, ∫ ω, |(ω (f i)) ^ n| ∂μ := by
    simpa using (MeasureTheory.integral_finset_sum
      (μ := μ) (s := (Finset.univ : Finset (Fin n)))
      (f := fun i : Fin n => fun ω : FieldConfig2D => |(ω (f i)) ^ n|)
      (fun i hi => (hpowInt i).norm))
  have htermBound :
      ∀ i : Fin n,
        ∫ ω, |(ω (f i)) ^ n| ∂μ ≤
          (Nat.factorial n : ℝ) *
            (generatingFunctional params Λ (f i) +
              generatingFunctional params Λ (-(f i))) := by
    intro i
    simpa [μ] using
      finiteVolume_pairing_abs_moment_le_factorial_mul_generatingFunctional_pair
        params Λ (f i) n
  have hsumBound :
      (∑ i : Fin n, ∫ ω, |(ω (f i)) ^ n| ∂μ) ≤
        ∑ i : Fin n, (Nat.factorial n : ℝ) *
          (generatingFunctional params Λ (f i) + generatingFunctional params Λ (-(f i))) :=
    Finset.sum_le_sum (fun i hi => htermBound i)
  have hnorm :
      |∫ ω, ∏ i, ω (f i) ∂μ| ≤ ∫ ω, |∏ i, ω (f i)| ∂μ := by
    simpa [Real.norm_eq_abs, Finset.abs_prod] using
      (norm_integral_le_integral_norm (f := fun ω : FieldConfig2D => ∏ i, ω (f i)))
  have hsch : schwingerN params Λ n f = ∫ ω, ∏ i, ω (f i) ∂μ := by
    simp [schwingerN, μ]
  calc
    |schwingerN params Λ n f| = |∫ ω, ∏ i, ω (f i) ∂μ| := by rw [hsch]
    _ ≤ ∫ ω, |∏ i, ω (f i)| ∂μ := hnorm
    _ ≤ ∫ ω, ∑ i : Fin n, |(ω (f i)) ^ n| ∂μ := hmono
    _ = ∑ i : Fin n, ∫ ω, |(ω (f i)) ^ n| ∂μ := hsumEval
    _ ≤ ∑ i : Fin n, (Nat.factorial n : ℝ) *
          (generatingFunctional params Λ (f i) + generatingFunctional params Λ (-(f i))) :=
        hsumBound

/-- Single-field observable is `L²` under the finite-volume interacting measure. -/
theorem finiteVolume_pairing_memLp_two (params : Phi4Params)
    [InteractionWeightModel params]
    (Λ : Rectangle) (f : TestFun2D) :
    MemLp (fun ω : FieldConfig2D => ω f) (2 : ℝ≥0∞)
      (finiteVolumeMeasure params Λ) := by
  set μ : Measure FieldConfig2D := finiteVolumeMeasure params Λ
  have hIntSq : Integrable (fun ω : FieldConfig2D => (ω f) ^ 2) μ := by
    have hprod := finiteVolume_product_integrable params Λ 2 ![f, f]
    refine hprod.congr ?_
    filter_upwards with ω
    simp [Fin.prod_univ_two, pow_two]
  have hAEMeas :
      AEStronglyMeasurable (fun ω : FieldConfig2D => ω f) μ := by
    exact (GaussianField.configuration_eval_measurable f).aestronglyMeasurable
  exact (memLp_two_iff_integrable_sq hAEMeas).2 hIntSq

/-- Polarization identity for the finite-volume 2-point function. -/
theorem schwingerTwo_polarization (params : Phi4Params)
    [InteractionWeightModel params]
    (Λ : Rectangle) (f g : TestFun2D) :
    schwingerTwo params Λ f g =
      (schwingerTwo params Λ (f + g) (f + g) -
        schwingerTwo params Λ (f - g) (f - g)) / 4 := by
  set μ : Measure FieldConfig2D := finiteVolumeMeasure params Λ
  have hplusInt : Integrable (fun ω : FieldConfig2D => (ω (f + g)) ^ 2) μ := by
    have hLp := finiteVolume_pairing_memLp_two params Λ (f + g)
    simpa [μ] using hLp.integrable_sq
  have hminusInt : Integrable (fun ω : FieldConfig2D => (ω (f - g)) ^ 2) μ := by
    have hLp := finiteVolume_pairing_memLp_two params Λ (f - g)
    simpa [μ] using hLp.integrable_sq
  have hmain :
      4 * schwingerTwo params Λ f g =
        ∫ ω, (ω (f + g)) ^ 2 ∂μ - ∫ ω, (ω (f - g)) ^ 2 ∂μ := by
    calc
      4 * schwingerTwo params Λ f g
          = ∫ ω, 4 * (ω f * ω g) ∂μ := by
              rw [schwingerTwo, integral_const_mul]
      _ = ∫ ω, ((ω (f + g)) ^ 2 - (ω (f - g)) ^ 2) ∂μ := by
            congr 1
            funext ω
            rw [map_add, map_sub]
            ring
      _ = ∫ ω, (ω (f + g)) ^ 2 ∂μ - ∫ ω, (ω (f - g)) ^ 2 ∂μ := by
            rw [integral_sub hplusInt hminusInt]
  have hplus :
      schwingerTwo params Λ (f + g) (f + g) =
        ∫ ω, (ω (f + g)) ^ 2 ∂μ := by
    simp [schwingerTwo, μ, pow_two]
  have hminus :
      schwingerTwo params Λ (f - g) (f - g) =
        ∫ ω, (ω (f - g)) ^ 2 ∂μ := by
    simp [schwingerTwo, μ, pow_two]
  apply (eq_div_iff (show (4 : ℝ) ≠ 0 by norm_num)).2
  calc
    schwingerTwo params Λ f g * 4 = 4 * schwingerTwo params Λ f g := by ring
    _ = ∫ ω, (ω (f + g)) ^ 2 ∂μ - ∫ ω, (ω (f - g)) ^ 2 ∂μ := hmain
    _ = schwingerTwo params Λ (f + g) (f + g) -
          schwingerTwo params Λ (f - g) (f - g) := by
          rw [hplus, hminus]

/-- Diagonal connected 2-point positivity (variance form) in finite volume. -/
theorem connectedSchwingerTwo_self_nonneg (params : Phi4Params)
    [InteractionWeightModel params]
    (Λ : Rectangle) (f : TestFun2D) :
    0 ≤ connectedSchwingerTwo params Λ f f := by
  let μ : Measure FieldConfig2D := finiteVolumeMeasure params Λ
  have hprob : IsProbabilityMeasure μ := by
    simpa [μ] using finiteVolumeMeasure_isProbability params Λ
  letI : IsProbabilityMeasure μ := hprob
  let X : FieldConfig2D → ℝ := fun ω => ω f
  have hX : MemLp X 2 μ := by
    simpa [μ, X] using finiteVolume_pairing_memLp_two params Λ f
  have hcov_eq :
      cov[X, X; μ] = connectedSchwingerTwo params Λ f f := by
    have hcov_sub : cov[X, X; μ] = μ[X * X] - μ[X] * μ[X] :=
      ProbabilityTheory.covariance_eq_sub hX hX
    simpa [μ, X, connectedSchwingerTwo, schwingerTwo, schwingerN, Fin.prod_univ_one]
      using hcov_sub
  have hcov_nonneg : 0 ≤ cov[X, X; μ] := by
    rw [ProbabilityTheory.covariance_self hX.aemeasurable]
    exact ProbabilityTheory.variance_nonneg X μ
  exact hcov_eq ▸ hcov_nonneg

/-- The Schwinger functions are multilinear in each argument.
    Proof: ω is linear (WeakDual), so the product splits at index i,
    and the integral distributes by linearity. -/
theorem schwingerN_multilinear (params : Phi4Params) (Λ : Rectangle) (n : ℕ)
    [InteractionWeightModel params]
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

/-- Additivity of the one-point Schwinger functional. -/
theorem schwingerOne_add (params : Phi4Params)
    [InteractionWeightModel params]
    (Λ : Rectangle) (f g : TestFun2D) :
    schwingerN params Λ 1 ![f + g] =
      schwingerN params Λ 1 ![f] + schwingerN params Λ 1 ![g] := by
  let F : Fin 1 → TestFun2D := ![f]
  let G : Fin 1 → TestFun2D := Function.update F 0 g
  have hlin := schwingerN_multilinear params Λ 1 F G 1 0
  have hleft : Function.update F 0 (1 • F 0 + G 0) = ![f + g] := by
    ext i
    fin_cases i
    simp [F, G]
  have hright : Function.update F 0 (G 0) = ![g] := by
    ext i
    fin_cases i
    simp [F, G]
  simpa [hleft, hright, F] using hlin

/-- Scalar linearity of the one-point Schwinger functional. -/
theorem schwingerOne_smul (params : Phi4Params)
    [InteractionWeightModel params]
    (Λ : Rectangle) (c : ℝ) (f : TestFun2D) :
    schwingerN params Λ 1 ![c • f] = c * schwingerN params Λ 1 ![f] := by
  let F : Fin 1 → TestFun2D := ![f]
  let G : Fin 1 → TestFun2D := Function.update F 0 0
  have hlin := schwingerN_multilinear params Λ 1 F G c 0
  have hleft : Function.update F 0 (c • F 0 + G 0) = ![c • f] := by
    ext i
    fin_cases i
    simp [F, G]
  have hright : Function.update F 0 (G 0) = ![(0 : TestFun2D)] := by
    ext i
    fin_cases i
    simp [F, G]
  have hzero : schwingerN params Λ 1 ![(0 : TestFun2D)] = 0 := by
    simp [schwingerN]
  calc
    schwingerN params Λ 1 ![c • f]
        = c * schwingerN params Λ 1 F + schwingerN params Λ 1 ![(0 : TestFun2D)] := by
            simpa [hleft, hright] using hlin
    _ = c * schwingerN params Λ 1 F := by simp [hzero]
    _ = c * schwingerN params Λ 1 ![f] := by simp [F]

/-- The one-point Schwinger functional as a linear map. -/
def schwingerOneLinear (params : Phi4Params)
    [InteractionWeightModel params]
    (Λ : Rectangle) : TestFun2D →ₗ[ℝ] ℝ where
  toFun f := schwingerN params Λ 1 ![f]
  map_add' := by
    intro f g
    exact schwingerOne_add params Λ f g
  map_smul' := by
    intro c f
    exact schwingerOne_smul params Λ c f

/-- Additivity in the first argument of the finite-volume two-point function. -/
theorem schwingerTwo_add_left (params : Phi4Params)
    [InteractionWeightModel params]
    (Λ : Rectangle) (f₁ f₂ g : TestFun2D) :
    schwingerTwo params Λ (f₁ + f₂) g =
      schwingerTwo params Λ f₁ g + schwingerTwo params Λ f₂ g := by
  let F : Fin 2 → TestFun2D := ![f₁, g]
  let G : Fin 2 → TestFun2D := Function.update F 0 f₂
  have hlin := schwingerN_multilinear params Λ 2 F G 1 0
  have hleft : Function.update F 0 (1 • F 0 + G 0) = ![f₁ + f₂, g] := by
    ext i
    fin_cases i <;> simp [F, G]
  have hright : Function.update F 0 (G 0) = ![f₂, g] := by
    ext i
    fin_cases i <;> simp [F, G]
  have hlin' :
      schwingerN params Λ 2 (![f₁ + f₂, g] : Fin 2 → TestFun2D) =
        1 * schwingerN params Λ 2 F + schwingerN params Λ 2 (![f₂, g] : Fin 2 → TestFun2D) := by
    simpa [hleft, hright] using hlin
  have hF : schwingerN params Λ 2 F = schwingerTwo params Λ f₁ g := by
    simpa [F] using schwingerN_two_eq_schwingerTwo params Λ F
  have h2 : schwingerN params Λ 2 (![f₂, g] : Fin 2 → TestFun2D) = schwingerTwo params Λ f₂ g := by
    simpa using schwingerN_two_eq_schwingerTwo params Λ (![f₂, g] : Fin 2 → TestFun2D)
  calc
    schwingerTwo params Λ (f₁ + f₂) g
        = schwingerN params Λ 2 (![f₁ + f₂, g] : Fin 2 → TestFun2D) := by
            exact (schwingerN_two_eq_schwingerTwo params Λ
              (![f₁ + f₂, g] : Fin 2 → TestFun2D)).symm
    _ = 1 * schwingerN params Λ 2 F + schwingerN params Λ 2 (![f₂, g] : Fin 2 → TestFun2D) := hlin'
    _ = schwingerN params Λ 2 F + schwingerN params Λ 2 (![f₂, g] : Fin 2 → TestFun2D) := by simp
    _ = schwingerTwo params Λ f₁ g + schwingerTwo params Λ f₂ g := by simp [hF, h2]

/-- Scalar linearity in the first argument of the finite-volume two-point function. -/
theorem schwingerTwo_smul_left (params : Phi4Params)
    [InteractionWeightModel params]
    (Λ : Rectangle) (c : ℝ) (f g : TestFun2D) :
    schwingerTwo params Λ (c • f) g = c * schwingerTwo params Λ f g := by
  let F : Fin 2 → TestFun2D := ![f, g]
  let G : Fin 2 → TestFun2D := Function.update F 0 0
  have hlin := schwingerN_multilinear params Λ 2 F G c 0
  have hleft : Function.update F 0 (c • F 0 + G 0) = ![c • f, g] := by
    ext i
    fin_cases i <;> simp [F, G]
  have hright : Function.update F 0 (G 0) = ![(0 : TestFun2D), g] := by
    ext i
    fin_cases i <;> simp [F, G]
  have hlin' :
      schwingerN params Λ 2 (![c • f, g] : Fin 2 → TestFun2D) =
        c * schwingerN params Λ 2 F +
          schwingerN params Λ 2 (![(0 : TestFun2D), g] : Fin 2 → TestFun2D) := by
    simpa [hleft, hright] using hlin
  have hF : schwingerN params Λ 2 F = schwingerTwo params Λ f g := by
    simpa [F] using schwingerN_two_eq_schwingerTwo params Λ F
  have hzero : schwingerN params Λ 2 (![(0 : TestFun2D), g] : Fin 2 → TestFun2D) = 0 := by
    simp [schwingerN]
  calc
    schwingerTwo params Λ (c • f) g
        = schwingerN params Λ 2 (![c • f, g] : Fin 2 → TestFun2D) := by
            exact (schwingerN_two_eq_schwingerTwo params Λ
              (![c • f, g] : Fin 2 → TestFun2D)).symm
    _ = c * schwingerN params Λ 2 F +
          schwingerN params Λ 2 (![(0 : TestFun2D), g] : Fin 2 → TestFun2D) := hlin'
    _ = c * schwingerN params Λ 2 F := by simp [hzero]
    _ = c * schwingerTwo params Λ f g := by simp [hF]

/-- Additivity in the second argument of the finite-volume two-point function. -/
theorem schwingerTwo_add_right (params : Phi4Params)
    [InteractionWeightModel params]
    (Λ : Rectangle) (f g₁ g₂ : TestFun2D) :
    schwingerTwo params Λ f (g₁ + g₂) =
      schwingerTwo params Λ f g₁ + schwingerTwo params Λ f g₂ := by
  calc
    schwingerTwo params Λ f (g₁ + g₂)
        = schwingerTwo params Λ (g₁ + g₂) f := schwingerTwo_symm params Λ f (g₁ + g₂)
    _ = schwingerTwo params Λ g₁ f + schwingerTwo params Λ g₂ f :=
          schwingerTwo_add_left params Λ g₁ g₂ f
    _ = schwingerTwo params Λ f g₁ + schwingerTwo params Λ f g₂ := by
          rw [schwingerTwo_symm params Λ g₁ f, schwingerTwo_symm params Λ g₂ f]

/-- Scalar linearity in the second argument of the finite-volume two-point function. -/
theorem schwingerTwo_smul_right (params : Phi4Params)
    [InteractionWeightModel params]
    (Λ : Rectangle) (c : ℝ) (f g : TestFun2D) :
    schwingerTwo params Λ f (c • g) = c * schwingerTwo params Λ f g := by
  calc
    schwingerTwo params Λ f (c • g)
        = schwingerTwo params Λ (c • g) f := schwingerTwo_symm params Λ f (c • g)
    _ = c * schwingerTwo params Λ g f := schwingerTwo_smul_left params Λ c g f
    _ = c * schwingerTwo params Λ f g := by rw [schwingerTwo_symm params Λ g f]

/-- The finite-volume two-point function packaged as a bilinear map. -/
def schwingerTwoBilinear (params : Phi4Params)
    [InteractionWeightModel params]
    (Λ : Rectangle) :
    TestFun2D →ₗ[ℝ] TestFun2D →ₗ[ℝ] ℝ where
  toFun f :=
    { toFun := fun g => schwingerTwo params Λ f g
      map_add' := by
        intro g₁ g₂
        exact schwingerTwo_add_right params Λ f g₁ g₂
      map_smul' := by
        intro c g
        exact schwingerTwo_smul_right params Λ c f g }
  map_add' := by
    intro f₁ f₂
    ext g
    exact schwingerTwo_add_left params Λ f₁ f₂ g
  map_smul' := by
    intro c f
    ext g
    exact schwingerTwo_smul_left params Λ c f g

/-- The connected finite-volume two-point function packaged as a bilinear map. -/
def connectedSchwingerTwoBilinear (params : Phi4Params)
    [InteractionWeightModel params]
    (Λ : Rectangle) :
    TestFun2D →ₗ[ℝ] TestFun2D →ₗ[ℝ] ℝ where
  toFun f :=
    { toFun := fun g => connectedSchwingerTwo params Λ f g
      map_add' := by
        intro g₁ g₂
        unfold connectedSchwingerTwo
        rw [schwingerTwo_add_right, schwingerOne_add params Λ g₁ g₂]
        ring_nf
      map_smul' := by
        intro c g
        unfold connectedSchwingerTwo
        rw [schwingerTwo_smul_right, schwingerOne_smul params Λ c g]
        simp [smul_eq_mul]
        ring_nf }
  map_add' := by
    intro f₁ f₂
    ext g
    simp [connectedSchwingerTwo, schwingerTwo_add_left, schwingerOne_add]
    ring_nf
  map_smul' := by
    intro c f
    ext g
    simp [connectedSchwingerTwo, schwingerTwo_smul_left, schwingerOne_smul, smul_eq_mul]
    ring_nf

/-- Symmetry of the connected two-point bilinear form. -/
theorem connectedSchwingerTwoBilinear_symm (params : Phi4Params)
    [InteractionWeightModel params]
    (Λ : Rectangle) (f g : TestFun2D) :
    connectedSchwingerTwoBilinear params Λ f g =
      connectedSchwingerTwoBilinear params Λ g f := by
  simpa [connectedSchwingerTwoBilinear] using
    connectedSchwingerTwo_symm params Λ f g

/-- Diagonal nonnegativity of the connected two-point bilinear form. -/
theorem connectedSchwingerTwoBilinear_self_nonneg (params : Phi4Params)
    [InteractionWeightModel params]
    (Λ : Rectangle) (f : TestFun2D) :
    0 ≤ connectedSchwingerTwoBilinear params Λ f f := by
  simpa [connectedSchwingerTwoBilinear] using
    connectedSchwingerTwo_self_nonneg params Λ f

/-- Positive-semidefinite quadratic form statement for finite families:
    the connected two-point kernel is nonnegative on real finite linear combinations. -/
theorem connectedSchwingerTwo_quadratic_nonneg
    (params : Phi4Params)
    [InteractionWeightModel params]
    (Λ : Rectangle)
    {ι : Type*} (s : Finset ι)
    (f : ι → TestFun2D) (c : ι → ℝ) :
    0 ≤ Finset.sum s (fun i =>
      c i * Finset.sum s (fun j => c j * connectedSchwingerTwo params Λ (f j) (f i))) := by
  let B := connectedSchwingerTwoBilinear params Λ
  let v : TestFun2D := Finset.sum s (fun i => c i • f i)
  have hvv :
      B v v =
        Finset.sum s (fun i => c i * Finset.sum s (fun j => c j * B (f j) (f i))) := by
    simp [B, v, Finset.sum_apply]
  have hnonneg : 0 ≤ B v v :=
    connectedSchwingerTwoBilinear_self_nonneg params Λ v
  rw [hvv] at hnonneg
  simpa [B] using hnonneg

/-- Standard-index-order version of `connectedSchwingerTwo_quadratic_nonneg`. -/
theorem connectedSchwingerTwo_quadratic_nonneg_standard
    (params : Phi4Params)
    [InteractionWeightModel params]
    (Λ : Rectangle)
    {ι : Type*} (s : Finset ι)
    (f : ι → TestFun2D) (c : ι → ℝ) :
    0 ≤ Finset.sum s (fun i => Finset.sum s (fun j =>
      c i * c j * connectedSchwingerTwo params Λ (f i) (f j))) := by
  have hbase := connectedSchwingerTwo_quadratic_nonneg params Λ s f c
  have hEq :
      Finset.sum s (fun i =>
        c i * Finset.sum s (fun j => c j * connectedSchwingerTwo params Λ (f j) (f i)))
      =
      Finset.sum s (fun i => Finset.sum s (fun j =>
        c i * c j * connectedSchwingerTwo params Λ (f i) (f j))) := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [connectedSchwingerTwo_symm params Λ (f j) (f i)]
    ring
  rw [hEq] at hbase
  exact hbase

/-- Two-point absolute-value bound from quadratic positivity:
    `|Cᶜ(f,g)| ≤ (Cᶜ(f,f) + Cᶜ(g,g)) / 2`. -/
theorem connectedSchwingerTwo_abs_le_half_diag_sum
    (params : Phi4Params)
    [InteractionWeightModel params]
    (Λ : Rectangle)
    (f g : TestFun2D) :
    |connectedSchwingerTwo params Λ f g| ≤
      (connectedSchwingerTwo params Λ f f + connectedSchwingerTwo params Λ g g) / 2 := by
  let B := connectedSchwingerTwoBilinear params Λ
  have hplus : 0 ≤ B (f + g) (f + g) :=
    connectedSchwingerTwoBilinear_self_nonneg params Λ (f + g)
  have hminus : 0 ≤ B (f - g) (f - g) :=
    connectedSchwingerTwoBilinear_self_nonneg params Λ (f - g)
  have hsym : B f g = B g f :=
    connectedSchwingerTwoBilinear_symm params Λ f g
  have hplus_expand : B (f + g) (f + g) = B f f + B f g + B g f + B g g := by
    calc
      B (f + g) (f + g) = (B f + B g) (f + g) := by
        simpa using congrArg (fun L : TestFun2D →ₗ[ℝ] ℝ => L (f + g)) (B.map_add f g)
      _ = B f (f + g) + B g (f + g) := by rfl
      _ = (B f f + B f g) + (B g f + B g g) := by
        rw [(B f).map_add f g, (B g).map_add f g]
      _ = B f f + B f g + B g f + B g g := by ring
  have hminus_expand : B (f - g) (f - g) = B f f - B f g - B g f + B g g := by
    calc
      B (f - g) (f - g) = (B f - B g) (f - g) := by
        simpa using congrArg (fun L : TestFun2D →ₗ[ℝ] ℝ => L (f - g)) (B.map_sub f g)
      _ = B f (f - g) - B g (f - g) := by rfl
      _ = (B f f - B f g) - (B g f - B g g) := by
        rw [(B f).map_sub f g, (B g).map_sub f g]
      _ = B f f - B f g - B g f + B g g := by ring
  have hplus' : 0 ≤ B f f + 2 * B f g + B g g := by
    rw [hplus_expand] at hplus
    rw [hsym] at hplus
    linarith
  have hminus' : 0 ≤ B f f - 2 * B f g + B g g := by
    rw [hminus_expand] at hminus
    rw [hsym] at hminus
    linarith
  have hupper : B f g ≤ (B f f + B g g) / 2 := by
    linarith
  have habs : |B f g| ≤ (B f f + B g g) / 2 := by
    exact abs_le.mpr ⟨by linarith, hupper⟩
  simpa [B] using habs

/-! ### Cauchy-Schwarz-type consequences -/

/-- Cauchy-Schwarz inequality for the connected finite-volume two-point form:
    `(Cᶜ(f,g))² ≤ Cᶜ(f,f) Cᶜ(g,g)`. -/
theorem connectedSchwingerTwo_sq_le_mul_diag
    (params : Phi4Params)
    [InteractionWeightModel params]
    (Λ : Rectangle)
    (f g : TestFun2D) :
    (connectedSchwingerTwo params Λ f g) ^ 2 ≤
      connectedSchwingerTwo params Λ f f * connectedSchwingerTwo params Λ g g := by
  let B := connectedSchwingerTwoBilinear params Λ
  have hsym : B f g = B g f :=
    connectedSchwingerTwoBilinear_symm params Λ f g
  have hff : 0 ≤ B f f :=
    connectedSchwingerTwoBilinear_self_nonneg params Λ f
  have hgg : 0 ≤ B g g :=
    connectedSchwingerTwoBilinear_self_nonneg params Λ g
  have hquad_poly (t : ℝ) :
      0 ≤ B f f + (2 * t) * B f g + t ^ 2 * B g g := by
    have hquad : 0 ≤ B (f + t • g) (f + t • g) :=
      connectedSchwingerTwoBilinear_self_nonneg params Λ (f + t • g)
    have hexp :
        B (f + t • g) (f + t • g) = B f f + t * B g f + t * (B f g + t * B g g) := by
      simp [map_add, map_smul, add_assoc]
    rw [hexp, hsym.symm] at hquad
    nlinarith [hquad]
  have hcs : (B f g) ^ 2 ≤ B f f * B g g := by
    by_cases hgg0 : B g g = 0
    · have hfg0 : B f g = 0 := by
        by_contra hfg0
        let t0 : ℝ := -((B f f + 1) / (2 * B f g))
        have hdenom : 2 * B f g ≠ 0 := by
          intro h
          apply hfg0
          linarith
        have hq0 : 0 ≤ B f f + (2 * t0) * B f g + t0 ^ 2 * B g g := hquad_poly t0
        have ht : (2 * t0) * B f g = -(B f f + 1) := by
          dsimp [t0]
          field_simp [hdenom]
        have ht2 : t0 ^ 2 * B g g = 0 := by
          simp [hgg0]
        linarith [hq0, ht, ht2]
      rw [hfg0, hgg0]
      nlinarith
    · have hgg_pos : 0 < B g g := lt_of_le_of_ne hgg (by simpa [eq_comm] using hgg0)
      let t0 : ℝ := -(B f g) / (B g g)
      have hq0 : 0 ≤ B f f + (2 * t0) * B f g + t0 ^ 2 * B g g := hquad_poly t0
      have hcalc : (2 * t0) * B f g + t0 ^ 2 * B g g = -((B f g) ^ 2 / (B g g)) := by
        dsimp [t0]
        field_simp [hgg0]
        ring
      have hstep : 0 ≤ B f f - (B f g) ^ 2 / (B g g) := by
        linarith [hq0, hcalc]
      have hmul_nonneg : 0 ≤ (B f f - (B f g) ^ 2 / (B g g)) * (B g g) := by
        exact mul_nonneg hstep (le_of_lt hgg_pos)
      have hmul_nonneg' : 0 ≤ B f f * B g g - (B f g) ^ 2 := by
        have hcalc2 :
            (B f f - (B f g) ^ 2 / (B g g)) * (B g g) = B f f * B g g - (B f g) ^ 2 := by
          field_simp [hgg0]
        linarith [hmul_nonneg, hcalc2]
      linarith [hmul_nonneg']
  simpa [B] using hcs

/-- Geometric-mean bound from finite-volume connected two-point Cauchy-Schwarz:
    `|Cᶜ_Λ(f,g)| ≤ √(Cᶜ_Λ(f,f) Cᶜ_Λ(g,g))`. -/
theorem connectedSchwingerTwo_abs_le_sqrt_diag_mul
    (params : Phi4Params)
    [InteractionWeightModel params]
    (Λ : Rectangle)
    (f g : TestFun2D) :
    |connectedSchwingerTwo params Λ f g| ≤
      Real.sqrt (connectedSchwingerTwo params Λ f f * connectedSchwingerTwo params Λ g g) := by
  let x : ℝ := connectedSchwingerTwo params Λ f g
  let y : ℝ := connectedSchwingerTwo params Λ f f * connectedSchwingerTwo params Λ g g
  have hx2 : x ^ 2 ≤ y := by
    simpa [x, y] using connectedSchwingerTwo_sq_le_mul_diag params Λ f g
  have hy_nonneg : 0 ≤ y := by
    have hff : 0 ≤ connectedSchwingerTwo params Λ f f := connectedSchwingerTwo_self_nonneg params Λ f
    have hgg : 0 ≤ connectedSchwingerTwo params Λ g g := connectedSchwingerTwo_self_nonneg params Λ g
    exact mul_nonneg hff hgg
  have hxy_sq : (|x|) ^ 2 ≤ (Real.sqrt y) ^ 2 := by
    have h1 : |x| ^ 2 ≤ y := by
      simpa [sq_abs] using hx2
    have h2 : y = (Real.sqrt y) ^ 2 := by
      symm
      exact Real.sq_sqrt hy_nonneg
    linarith
  have hxy_abs : |(|x|)| ≤ |Real.sqrt y| := (sq_le_sq).1 hxy_sq
  have hxy : |x| ≤ Real.sqrt y := by
    simpa [abs_abs, abs_of_nonneg (Real.sqrt_nonneg y)] using hxy_abs
  simpa [x, y] using hxy

/-! ## Finite-volume comparison interface -/

/-- Comparison input controlling interacting two-point functions by the free Gaussian
    two-point function. This packages the nontrivial domination estimate proved via
    correlation-inequality/random-walk methods (e.g. Gaussian upper bounds in the
    even φ⁴ setting) as an explicit assumption for downstream development. -/
class FiniteVolumeComparisonModel (params : Phi4Params) where
  schwingerTwo_le_free : ∀ (Λ : Rectangle)
      (f g : TestFun2D)
      (_hf : ∀ x, 0 ≤ f x) (_hg : ∀ x, 0 ≤ g x),
      schwingerTwo params Λ f g ≤
        ∫ ω, ω f * ω g ∂(freeFieldMeasure params.mass params.mass_pos)

/-- The 2-point function is bounded by the free field 2-point function
    (for the φ⁴ interaction with λ > 0). This is a consequence of the
    Gaussian-domination / comparison inequalities for even φ⁴ models
    (e.g. GJ 21.5, Proposition 21.5.1 and related bounds). -/
theorem schwingerTwo_le_free (params : Phi4Params) (Λ : Rectangle)
    [FiniteVolumeComparisonModel params]
    (f g : TestFun2D) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) :
    schwingerTwo params Λ f g ≤
      ∫ ω, ω f * ω g ∂(freeFieldMeasure params.mass params.mass_pos) := by
  exact FiniteVolumeComparisonModel.schwingerTwo_le_free
    (params := params) Λ f g hf hg

end

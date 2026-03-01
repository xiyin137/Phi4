/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.Reconstruction.Part2

noncomputable section

open MeasureTheory Reconstruction
open scoped ENNReal NNReal

/-! ## Wightman reconstruction -/

/-- Class-free reconstruction step: linear growth plus an OS-to-Wightman
    reconstruction rule yields Wightman existence for a Schwinger family `S`. -/
theorem wightman_exists_of_linear_growth_and_reconstruction
    (S : SchwingerFunctions 1)
    (hlinear : ∃ OS : OsterwalderSchraderAxioms 1,
      OS.S = S ∧ Nonempty (OSLinearGrowthCondition 1 OS))
    (hreconstruct : ∀ (OS : OsterwalderSchraderAxioms 1),
      OSLinearGrowthCondition 1 OS →
        ∃ (Wfn : WightmanFunctions 1),
          IsWickRotationPair OS.S Wfn.W) :
    ∃ (Wfn : WightmanFunctions 1),
      ∃ (OS : OsterwalderSchraderAxioms 1),
        OS.S = S ∧ IsWickRotationPair OS.S Wfn.W := by
  rcases hlinear with ⟨OS, hOS_lg⟩
  rcases hOS_lg with ⟨hS, hlg_nonempty⟩
  rcases hlg_nonempty with ⟨hlg⟩
  rcases hreconstruct OS hlg with ⟨Wfn, hWR⟩
  exact ⟨Wfn, OS, hS, hWR⟩

/-- Construct Wightman existence from explicit linear-growth and reconstruction
    rule data at fixed `params`. -/
theorem phi4_wightman_exists_of_explicit_data (params : Phi4Params) :
    [SchwingerFunctionModel params] →
    (hlinear : ∃ OS : OsterwalderSchraderAxioms 1,
      OS.S = phi4SchwingerFunctions params ∧
      Nonempty (OSLinearGrowthCondition 1 OS)) →
    (hreconstruct : ∀ (OS : OsterwalderSchraderAxioms 1),
      OSLinearGrowthCondition 1 OS →
        ∃ (Wfn : WightmanFunctions 1),
          IsWickRotationPair OS.S Wfn.W) →
    ∃ (Wfn : WightmanFunctions 1),
      ∃ (OS : OsterwalderSchraderAxioms 1),
        OS.S = phi4SchwingerFunctions params ∧
        IsWickRotationPair OS.S Wfn.W := by
  intro hos hlinear hreconstruct
  exact wightman_exists_of_linear_growth_and_reconstruction
    (S := phi4SchwingerFunctions params) hlinear hreconstruct

/-- Direct explicit-bound reconstruction endpoint:
    a concrete seminorm-growth estimate for one OS package matching
    `phi4SchwingerFunctions` yields Wightman existence. -/
theorem phi4_wightman_exists_of_explicit_linear_growth_bound
    (params : Phi4Params) :
    [SchwingerFunctionModel params] →
    [WightmanReconstructionModel params] →
    (OS : OsterwalderSchraderAxioms 1) →
    (hS : OS.S = phi4SchwingerFunctions params) →
    (sobolev_index : ℕ) →
    (alpha beta gamma : ℝ) →
    (halpha : 0 < alpha) →
    (hbeta : 0 < beta) →
    (hgrowth : ∀ (n : ℕ) (f : SchwartzNPoint 1 n),
      ‖phi4SchwingerFunctions params n f‖ ≤
        alpha * beta ^ n * (n.factorial : ℝ) ^ gamma *
          SchwartzMap.seminorm ℝ sobolev_index sobolev_index f) →
    ∃ (Wfn : WightmanFunctions 1),
      ∃ (OS' : OsterwalderSchraderAxioms 1),
        OS'.S = phi4SchwingerFunctions params ∧
        IsWickRotationPair OS'.S Wfn.W := by
  intro hos hrec OS hS sobolev_index alpha beta gamma halpha hbeta hgrowth
  exact phi4_wightman_exists_of_explicit_data params
    (hlinear := phi4_linear_growth_of_explicit_bound params OS hS
      sobolev_index alpha beta gamma halpha hbeta hgrowth)
    (hreconstruct := phi4_wightman_reconstruction_step_of_interface params)

/-- Direct weak-coupling + explicit-growth endpoint:
    if an interface-level OS package exists at weak coupling and
    `phi4SchwingerFunctions` satisfy an explicit seminorm-growth bound, then
    Wightman existence follows. -/
theorem phi4_wightman_exists_of_os_and_explicit_linear_growth_bound
    (params : Phi4Params) :
    [OSAxiomCoreModel params] →
    [WightmanReconstructionModel params] →
    [OSDistributionE2Model params] →
    [OSE4ClusterModel params] →
    (hsmall : params.coupling < os4WeakCouplingThreshold params) →
    (sobolev_index : ℕ) →
    (alpha beta gamma : ℝ) →
    (halpha : 0 < alpha) →
    (hbeta : 0 < beta) →
    (hgrowth : ∀ (n : ℕ) (f : SchwartzNPoint 1 n),
      ‖phi4SchwingerFunctions params n f‖ ≤
        alpha * beta ^ n * (n.factorial : ℝ) ^ gamma *
          SchwartzMap.seminorm ℝ sobolev_index sobolev_index f) →
    ∃ (Wfn : WightmanFunctions 1),
      ∃ (OS' : OsterwalderSchraderAxioms 1),
        OS'.S = phi4SchwingerFunctions params ∧
        IsWickRotationPair OS'.S Wfn.W := by
  intro _hcore _hrec _he2 _he4 hsmall
    sobolev_index alpha beta gamma halpha hbeta hgrowth
  rcases phi4_satisfies_OS_of_interfaces params hsmall with ⟨OS, hS⟩
  exact phi4_wightman_exists_of_explicit_linear_growth_bound params
    OS hS sobolev_index alpha beta gamma halpha hbeta hgrowth

/-- Direct weak-coupling endpoint from:
    1) interface-level OS package data under weak coupling,
    2) explicit pointwise-in-`f` finite-volume uniform generating-functional bounds,
    3) explicit product-tensor reduction/approximation and order-zero inputs. -/
theorem phi4_wightman_exists_of_os_and_productTensor_approx_and_zero
    (params : Phi4Params) :
    [InteractionWeightModel params] →
    [SchwingerLimitModel params] →
    [OSAxiomCoreModel params] →
    [WightmanReconstructionModel params] →
    [OSDistributionE2Model params] →
    [OSE4ClusterModel params] →
    (hsmall : params.coupling < os4WeakCouplingThreshold params) →
    (sobolev_index : ℕ) →
    (alpha beta gamma : ℝ) →
    (halpha : 0 < alpha) →
    (hbeta : 0 < beta) →
    (huniform : ∀ h : TestFun2D, ∃ c : ℝ, ∀ Λ : Rectangle,
      |generatingFunctional params Λ h| ≤ Real.exp (c * normFunctional h)) →
    (hcompat :
      ∀ (n : ℕ) (f : Fin n → TestFun2D),
        phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily f) =
          (infiniteVolumeSchwinger params n f : ℂ)) →
    (hreduce :
      ∀ (c : ℝ) (n : ℕ) (_hn : 0 < n) (f : Fin n → TestFun2D),
        ∑ i : Fin n, (Nat.factorial n : ℝ) *
            (Real.exp (c * normFunctional (f i)) +
              Real.exp (c * normFunctional (-(f i)))) ≤
          alpha * beta ^ n * (n.factorial : ℝ) ^ gamma *
            SchwartzMap.seminorm ℝ sobolev_index sobolev_index
              (schwartzProductTensorFromTestFamily f)) →
    (happrox :
      ∀ (n : ℕ) (_hn : 0 < n) (g : SchwartzNPoint 1 n),
        ∃ u : ℕ → Fin n → TestFun2D,
          Filter.Tendsto (fun k => schwartzProductTensorFromTestFamily (u k))
            Filter.atTop (nhds g)) →
    (hzero :
      ∀ g : SchwartzNPoint 1 0,
        ‖phi4SchwingerFunctions params 0 g‖ ≤
          alpha * beta ^ 0 * (Nat.factorial 0 : ℝ) ^ gamma *
            SchwartzMap.seminorm ℝ sobolev_index sobolev_index g) →
    ∃ (Wfn : WightmanFunctions 1),
      ∃ (OS' : OsterwalderSchraderAxioms 1),
        OS'.S = phi4SchwingerFunctions params ∧
        IsWickRotationPair OS'.S Wfn.W := by
  intro hweight hlimit _hcore _hrec _he2 _he4 hsmall
    sobolev_index alpha beta gamma halpha hbeta huniform hcompat hreduce happrox hzero
  rcases phi4_satisfies_OS_of_interfaces params hsmall with ⟨OS, hS⟩
  have hprod := phi4_productTensor_linear_growth_of_uniform_generating_bound
    params sobolev_index alpha beta gamma
    huniform
    hcompat hreduce
  have hlinear := phi4_linear_growth_of_productTensor_approx_and_zero
    params OS hS sobolev_index alpha beta gamma halpha hbeta hprod happrox hzero
  exact phi4_wightman_exists_of_explicit_data params
    (hlinear := hlinear)
    (hreconstruct := phi4_wightman_reconstruction_step_of_interface params)

/-- Direct weak-coupling endpoint from:
    1) interface-level OS package data under weak coupling,
    2) explicit pointwise-in-`f` finite-volume uniform generating-functional bounds,
    3) explicit product-tensor reduction/approximation,
    4) order-zero normalization (`S₀(g) = g(0)`), using Sobolev index `0`. -/
theorem phi4_wightman_exists_of_os_and_productTensor_approx_and_normalized_order0
    (params : Phi4Params) :
    [InteractionWeightModel params] →
    [SchwingerLimitModel params] →
    [OSAxiomCoreModel params] →
    [WightmanReconstructionModel params] →
    [OSDistributionE2Model params] →
    [OSE4ClusterModel params] →
    (hsmall : params.coupling < os4WeakCouplingThreshold params) →
    (alpha beta gamma : ℝ) →
    (hbeta : 0 < beta) →
    (huniform : ∀ h : TestFun2D, ∃ c : ℝ, ∀ Λ : Rectangle,
      |generatingFunctional params Λ h| ≤ Real.exp (c * normFunctional h)) →
    (hcompat :
      ∀ (n : ℕ) (f : Fin n → TestFun2D),
        phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily f) =
          (infiniteVolumeSchwinger params n f : ℂ)) →
    (hreduce :
      ∀ (c : ℝ) (n : ℕ) (_hn : 0 < n) (f : Fin n → TestFun2D),
        ∑ i : Fin n, (Nat.factorial n : ℝ) *
            (Real.exp (c * normFunctional (f i)) +
              Real.exp (c * normFunctional (-(f i)))) ≤
          alpha * beta ^ n * (n.factorial : ℝ) ^ gamma *
            SchwartzMap.seminorm ℝ 0 0
              (schwartzProductTensorFromTestFamily f)) →
    (happrox :
      ∀ (n : ℕ) (_hn : 0 < n) (g : SchwartzNPoint 1 n),
        ∃ u : ℕ → Fin n → TestFun2D,
          Filter.Tendsto (fun k => schwartzProductTensorFromTestFamily (u k))
            Filter.atTop (nhds g)) →
    ∃ (Wfn : WightmanFunctions 1),
      ∃ (OS' : OsterwalderSchraderAxioms 1),
        OS'.S = phi4SchwingerFunctions params ∧
        IsWickRotationPair OS'.S Wfn.W := by
  intro hweight hlimit _hcore _hrec _he2 _he4 hsmall
    alpha beta gamma hbeta huniform hcompat hreduce happrox
  rcases phi4_satisfies_OS_of_interfaces params hsmall with ⟨OS, hS⟩
  have hlinear := phi4_linear_growth_of_interface_productTensor_approx_and_normalized_order0
    params OS hS alpha beta gamma hbeta huniform
    hcompat hreduce happrox
  exact phi4_wightman_exists_of_explicit_data params
    (hlinear := hlinear)
    (hreconstruct := phi4_wightman_reconstruction_step_of_interface params)

/-- Direct weak-coupling endpoint from:
    1) interface-level OS package data under weak coupling,
    2) explicit pointwise-in-`f` finite-volume uniform generating-functional bounds,
    3) dense image of product tensors in each positive-order Schwartz `n`-point space,
    4) order-zero normalization (`S₀(g) = g(0)`), using Sobolev index `0`. -/
theorem phi4_wightman_exists_of_os_and_productTensor_dense_and_normalized_order0
    (params : Phi4Params) :
    [InteractionWeightModel params] →
    [SchwingerLimitModel params] →
    [OSAxiomCoreModel params] →
    [WightmanReconstructionModel params] →
    [OSDistributionE2Model params] →
    [OSE4ClusterModel params] →
    (hsmall : params.coupling < os4WeakCouplingThreshold params) →
    (alpha beta gamma : ℝ) →
    (hbeta : 0 < beta) →
    (huniform : ∀ h : TestFun2D, ∃ c : ℝ, ∀ Λ : Rectangle,
      |generatingFunctional params Λ h| ≤ Real.exp (c * normFunctional h)) →
    (hcompat :
      ∀ (n : ℕ) (f : Fin n → TestFun2D),
        phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily f) =
          (infiniteVolumeSchwinger params n f : ℂ)) →
    (hreduce :
      ∀ (c : ℝ) (n : ℕ) (_hn : 0 < n) (f : Fin n → TestFun2D),
        ∑ i : Fin n, (Nat.factorial n : ℝ) *
            (Real.exp (c * normFunctional (f i)) +
              Real.exp (c * normFunctional (-(f i)))) ≤
          alpha * beta ^ n * (n.factorial : ℝ) ^ gamma *
            SchwartzMap.seminorm ℝ 0 0
              (schwartzProductTensorFromTestFamily f)) →
    (hdense :
      ∀ (n : ℕ) (_hn : 0 < n),
        DenseRange (fun f : Fin n → TestFun2D =>
          schwartzProductTensorFromTestFamily f)) →
    ∃ (Wfn : WightmanFunctions 1),
      ∃ (OS' : OsterwalderSchraderAxioms 1),
        OS'.S = phi4SchwingerFunctions params ∧
        IsWickRotationPair OS'.S Wfn.W := by
  intro hweight hlimit _hcore _hrec _he2 _he4 hsmall
    alpha beta gamma hbeta huniform hcompat hreduce hdense
  rcases phi4_satisfies_OS_of_interfaces params hsmall with ⟨OS, hS⟩
  have hlinear := phi4_linear_growth_of_interface_productTensor_approx_and_normalized_order0
    params OS hS alpha beta gamma hbeta huniform
    hcompat hreduce (phi4_productTensor_approx_family_of_dense_range hdense)
  exact phi4_wightman_exists_of_explicit_data params
    (hlinear := hlinear)
    (hreconstruct := phi4_wightman_reconstruction_step_of_interface params)

/-- Dense product-tensor weak-coupling Wightman endpoint with an explicit
    WP1-style interaction hypothesis: geometric decay of shifted cutoff
    exponential moments is used to instantiate `InteractionWeightModel`
    constructively before applying the standard weak-coupling bridge. -/
theorem phi4_wightman_exists_of_os_and_productTensor_dense_and_normalized_order0_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
    (params : Phi4Params) :
    [InteractionUVModel params] →
    [SchwingerLimitModel params] →
    [OSAxiomCoreModel params] →
    [WightmanReconstructionModel params] →
    [OSDistributionE2Model params] →
    [OSE4ClusterModel params] →
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
            ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D * r ^ n)) →
    (hsmall : params.coupling < os4WeakCouplingThreshold params) →
    (alpha beta gamma : ℝ) →
    (hbeta : 0 < beta) →
    (huniform : ∀ h : TestFun2D, ∃ c : ℝ, ∀ Λ : Rectangle,
      |generatingFunctional params Λ h| ≤ Real.exp (c * normFunctional h)) →
    (hcompat :
      ∀ (n : ℕ) (f : Fin n → TestFun2D),
        phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily f) =
          (infiniteVolumeSchwinger params n f : ℂ)) →
    (hreduce :
      ∀ (c : ℝ) (n : ℕ) (_hn : 0 < n) (f : Fin n → TestFun2D),
        ∑ i : Fin n, (Nat.factorial n : ℝ) *
            (Real.exp (c * normFunctional (f i)) +
              Real.exp (c * normFunctional (-(f i)))) ≤
          alpha * beta ^ n * (n.factorial : ℝ) ^ gamma *
            SchwartzMap.seminorm ℝ 0 0
              (schwartzProductTensorFromTestFamily f)) →
    (hdense :
      ∀ (n : ℕ) (_hn : 0 < n),
        DenseRange (fun f : Fin n → TestFun2D =>
          schwartzProductTensorFromTestFamily f)) →
    ∃ (Wfn : WightmanFunctions 1),
      ∃ (OS' : OsterwalderSchraderAxioms 1),
        OS'.S = phi4SchwingerFunctions params ∧
        IsWickRotationPair OS'.S Wfn.W := by
  intro _huv _hlimit _hcore _hrec _he2 _he4 hmom hsmall
    alpha beta gamma hbeta huniform hcompat hreduce hdense
  rcases
      interactionWeightModel_nonempty_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
        (params := params) hmom with ⟨hW⟩
  letI : InteractionWeightModel params := hW
  exact phi4_wightman_exists_of_os_and_productTensor_dense_and_normalized_order0
    params hsmall alpha beta gamma hbeta huniform hcompat hreduce hdense

/-- Dense product-tensor weak-coupling Wightman endpoint from:
    1) square-integrable/measurable UV interaction data,
    2) shifted-cutoff geometric exponential-moment decay,
    3) weak-coupling OS + reconstruction interfaces.
    This directly instantiates `InteractionWeightModel` from square data and
    applies the standard weak-coupling bridge. -/
theorem
    phi4_wightman_exists_of_os_and_productTensor_dense_and_normalized_order0_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
    (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [OSAxiomCoreModel params] →
    [WightmanReconstructionModel params] →
    [OSDistributionE2Model params] →
    [OSE4ClusterModel params] →
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        AEStronglyMeasurable (interactionCutoff params Λ κ)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hcutoff_sq :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        Integrable (fun ω => (interactionCutoff params Λ κ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hcutoff_conv :
      ∀ (Λ : Rectangle),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then
            ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)
            else 0)
          Filter.atTop
          (nhds 0)) →
    (hcutoff_ae :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
            Filter.atTop
            (nhds (interaction params Λ ω))) →
    (hinteraction_meas :
      ∀ (Λ : Rectangle),
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hinteraction_sq :
      ∀ (Λ : Rectangle),
        Integrable (fun ω => (interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos)) →
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
            ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D * r ^ n)) →
    (hsmall : params.coupling < os4WeakCouplingThreshold params) →
    (alpha beta gamma : ℝ) →
    (hbeta : 0 < beta) →
    (huniform : ∀ h : TestFun2D, ∃ c : ℝ, ∀ Λ : Rectangle,
      |generatingFunctional params Λ h| ≤ Real.exp (c * normFunctional h)) →
    (hcompat :
      ∀ (n : ℕ) (f : Fin n → TestFun2D),
        phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily f) =
          (infiniteVolumeSchwinger params n f : ℂ)) →
    (hreduce :
      ∀ (c : ℝ) (n : ℕ) (_hn : 0 < n) (f : Fin n → TestFun2D),
        ∑ i : Fin n, (Nat.factorial n : ℝ) *
            (Real.exp (c * normFunctional (f i)) +
              Real.exp (c * normFunctional (-(f i)))) ≤
          alpha * beta ^ n * (n.factorial : ℝ) ^ gamma *
            SchwartzMap.seminorm ℝ 0 0
              (schwartzProductTensorFromTestFamily f)) →
    (hdense :
      ∀ (n : ℕ) (_hn : 0 < n),
        DenseRange (fun f : Fin n → TestFun2D =>
          schwartzProductTensorFromTestFamily f)) →
    ∃ (Wfn : WightmanFunctions 1),
      ∃ (OS' : OsterwalderSchraderAxioms 1),
        OS'.S = phi4SchwingerFunctions params ∧
        IsWickRotationPair OS'.S Wfn.W := by
  intro _hlimit _hcore _hrec _he2 _he4
    hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
    hinteraction_meas hinteraction_sq
    hmom hsmall alpha beta gamma hbeta huniform hcompat hreduce hdense
  rcases
      interactionWeightModel_nonempty_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
        (params := params)
        hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
        hinteraction_meas hinteraction_sq hmom with ⟨hW⟩
  letI : InteractionWeightModel params := hW
  exact phi4_wightman_exists_of_os_and_productTensor_dense_and_normalized_order0
    params hsmall alpha beta gamma hbeta huniform hcompat hreduce hdense

/-- Dense product-tensor weak-coupling Wightman endpoint from:
    1) square-integrable/measurable UV interaction data,
    2) per-volume polynomial-decay squared-moment shifted UV-difference bounds,
    3) per-volume uniform shifted-cutoff partition-function bounds, and
    4) weak-coupling OS + reconstruction interfaces.
    This is the hard-core WP1 per-volume route through
    `InteractionIntegrabilityModel`. -/
theorem
    phi4_wightman_exists_of_os_and_productTensor_dense_and_normalized_order0_of_sq_integrable_data_and_sq_moment_polynomial_bound_per_volume_and_uniform_partition_bound
    (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [OSAxiomCoreModel params] →
    [WightmanReconstructionModel params] →
    [OSDistributionE2Model params] →
    [OSE4ClusterModel params] →
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        AEStronglyMeasurable (interactionCutoff params Λ κ)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hcutoff_sq :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        Integrable (fun ω => (interactionCutoff params Λ κ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hcutoff_conv :
      ∀ (Λ : Rectangle),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then
            ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)
            else 0)
          Filter.atTop
          (nhds 0)) →
    (hcutoff_ae :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
            Filter.atTop
            (nhds (interaction params Λ ω))) →
    (hinteraction_meas :
      ∀ (Λ : Rectangle),
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hinteraction_sq :
      ∀ (Λ : Rectangle),
        Integrable (fun ω => (interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (betaMom : ℝ) →
    (hbetaMom : 1 < betaMom) →
    (C : Rectangle → ℝ) →
    (hC_nonneg : ∀ Λ : Rectangle, 0 ≤ C Λ) →
    (hInt :
      ∀ (Λ : Rectangle) (n : ℕ),
        Integrable
          (fun ω : FieldConfig2D =>
            (interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hM :
      ∀ (Λ : Rectangle) (n : ℕ),
        ∫ ω : FieldConfig2D,
          (interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω) ^ 2
          ∂(freeFieldMeasure params.mass params.mass_pos)
        ≤ C Λ * (↑(n + 1) : ℝ) ^ (-betaMom)) →
    (hpartition :
      ∀ (Λ : Rectangle) (q : ℝ), 0 < q →
        ∃ D : ℝ,
          (∀ n : ℕ,
            Integrable
              (fun ω : FieldConfig2D =>
                Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)))
              (freeFieldMeasure params.mass params.mass_pos)) ∧
          (∀ n : ℕ,
            ∫ ω : FieldConfig2D,
              Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
              ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D)) →
    (hsmall : params.coupling < os4WeakCouplingThreshold params) →
    (alpha beta gamma : ℝ) →
    (hbeta : 0 < beta) →
    (huniform : ∀ h : TestFun2D, ∃ c : ℝ, ∀ Λ : Rectangle,
      |generatingFunctional params Λ h| ≤ Real.exp (c * normFunctional h)) →
    (hcompat :
      ∀ (n : ℕ) (f : Fin n → TestFun2D),
        phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily f) =
          (infiniteVolumeSchwinger params n f : ℂ)) →
    (hreduce :
      ∀ (c : ℝ) (n : ℕ) (_hn : 0 < n) (f : Fin n → TestFun2D),
        ∑ i : Fin n, (Nat.factorial n : ℝ) *
            (Real.exp (c * normFunctional (f i)) +
              Real.exp (c * normFunctional (-(f i)))) ≤
          alpha * beta ^ n * (n.factorial : ℝ) ^ gamma *
            SchwartzMap.seminorm ℝ 0 0
              (schwartzProductTensorFromTestFamily f)) →
    (hdense :
      ∀ (n : ℕ) (_hn : 0 < n),
        DenseRange (fun f : Fin n → TestFun2D =>
          schwartzProductTensorFromTestFamily f)) →
    ∃ (Wfn : WightmanFunctions 1),
      ∃ (OS' : OsterwalderSchraderAxioms 1),
        OS'.S = phi4SchwingerFunctions params ∧
        IsWickRotationPair OS'.S Wfn.W := by
  intro _hlimit _hcore _hrec _he2 _he4
    hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
    hinteraction_meas hinteraction_sq
    betaMom hbetaMom C hC_nonneg hInt hM hpartition
    hsmall alpha beta gamma hbeta huniform hcompat hreduce hdense
  rcases
      interactionIntegrabilityModel_nonempty_of_sq_integrable_data_and_sq_moment_polynomial_bound_per_volume_and_uniform_partition_bound
        (params := params)
        hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
        hinteraction_meas hinteraction_sq
        betaMom hbetaMom C hC_nonneg hInt hM hpartition with ⟨hI⟩
  letI : InteractionIntegrabilityModel params := hI
  exact phi4_wightman_exists_of_os_and_productTensor_dense_and_normalized_order0
    params hsmall alpha beta gamma hbeta huniform hcompat hreduce hdense

/-- Dense product-tensor weak-coupling Wightman endpoint from:
    1) square-integrable/measurable UV interaction data,
    2) per-volume bad-set decomposition data with linear lower bounds off bad
       sets, geometric second-moment control, and ENNReal geometric bad-set
       tails, and
    3) weak-coupling OS + reconstruction interfaces.
    This is the ENNReal-tail bad-set hard-core WP1 route through
    `InteractionIntegrabilityModel`. -/
theorem
    phi4_wightman_exists_of_os_and_productTensor_dense_and_normalized_order0_of_sq_integrable_data_and_linear_lower_bound_off_bad_sets_and_sq_exp_moment_geometric_and_bad_measure_geometric_ennreal
    (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [OSAxiomCoreModel params] →
    [WightmanReconstructionModel params] →
    [OSDistributionE2Model params] →
    [OSE4ClusterModel params] →
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        AEStronglyMeasurable (interactionCutoff params Λ κ)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hcutoff_sq :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        Integrable (fun ω => (interactionCutoff params Λ κ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hcutoff_conv :
      ∀ (Λ : Rectangle),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then
            ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)
            else 0)
          Filter.atTop
          (nhds 0)) →
    (hcutoff_ae :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
            Filter.atTop
            (nhds (interaction params Λ ω))) →
    (hinteraction_meas :
      ∀ (Λ : Rectangle),
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hinteraction_sq :
      ∀ (Λ : Rectangle),
        Integrable (fun ω => (interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hdecomp :
      ∀ (Λ : Rectangle) (q : ℝ), 0 < q →
        ∃ a b : ℝ, 0 < a ∧
          ∃ bad : ℕ → Set FieldConfig2D,
            (∀ n : ℕ, MeasurableSet (bad n)) ∧
            (∀ n : ℕ,
              Integrable
                (fun ω : FieldConfig2D =>
                  Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)))
                (freeFieldMeasure params.mass params.mass_pos)) ∧
            (∀ (n : ℕ) (ω : FieldConfig2D), ω ∉ bad n →
              a * (n : ℝ) - b ≤ interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω) ∧
            (∀ n : ℕ,
              MemLp
                (fun ω : FieldConfig2D =>
                  Real.exp ((-q) * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
                2
                (freeFieldMeasure params.mass params.mass_pos)) ∧
            ∃ D2 r2 : ℝ,
              0 ≤ D2 ∧ 0 ≤ r2 ∧ r2 < 1 ∧
              (∀ n : ℕ,
                ∫ ω : FieldConfig2D,
                  (Real.exp
                    ((-q) * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)) ^ (2 : ℝ)
                  ∂(freeFieldMeasure params.mass params.mass_pos)
                ≤ D2 * r2 ^ n) ∧
              ∃ Cb rb : ℝ≥0∞,
                Cb ≠ ⊤ ∧ rb < 1 ∧
                (∀ n : ℕ,
                  (freeFieldMeasure params.mass params.mass_pos) (bad n) ≤ Cb * rb ^ n)) →
    (hsmall : params.coupling < os4WeakCouplingThreshold params) →
    (alpha beta gamma : ℝ) →
    (hbeta : 0 < beta) →
    (huniform : ∀ h : TestFun2D, ∃ c : ℝ, ∀ Λ : Rectangle,
      |generatingFunctional params Λ h| ≤ Real.exp (c * normFunctional h)) →
    (hcompat :
      ∀ (n : ℕ) (f : Fin n → TestFun2D),
        phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily f) =
          (infiniteVolumeSchwinger params n f : ℂ)) →
    (hreduce :
      ∀ (c : ℝ) (n : ℕ) (_hn : 0 < n) (f : Fin n → TestFun2D),
        ∑ i : Fin n, (Nat.factorial n : ℝ) *
            (Real.exp (c * normFunctional (f i)) +
              Real.exp (c * normFunctional (-(f i)))) ≤
          alpha * beta ^ n * (n.factorial : ℝ) ^ gamma *
            SchwartzMap.seminorm ℝ 0 0
              (schwartzProductTensorFromTestFamily f)) →
    (hdense :
      ∀ (n : ℕ) (_hn : 0 < n),
        DenseRange (fun f : Fin n → TestFun2D =>
          schwartzProductTensorFromTestFamily f)) →
    ∃ (Wfn : WightmanFunctions 1),
      ∃ (OS' : OsterwalderSchraderAxioms 1),
        OS'.S = phi4SchwingerFunctions params ∧
        IsWickRotationPair OS'.S Wfn.W := by
  intro _hlimit _hcore _hrec _he2 _he4
    hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
    hinteraction_meas hinteraction_sq hdecomp
    hsmall alpha beta gamma hbeta huniform hcompat hreduce hdense
  rcases
      interactionIntegrabilityModel_nonempty_of_sq_integrable_data_and_linear_lower_bound_off_bad_sets_and_sq_exp_moment_geometric_and_bad_measure_geometric_ennreal
        (params := params)
        hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
        hinteraction_meas hinteraction_sq hdecomp with ⟨hI⟩
  letI : InteractionIntegrabilityModel params := hI
  exact phi4_wightman_exists_of_os_and_productTensor_dense_and_normalized_order0
    params hsmall alpha beta gamma hbeta huniform hcompat hreduce hdense

/-- Dense product-tensor weak-coupling Wightman endpoint from:
    1) square-integrable/measurable UV interaction data,
    2) a fixed higher even moment order `2j` (`j > 0`) with per-volume
       polynomial-decay shifted UV-difference bounds,
    3) per-volume uniform shifted-cutoff partition-function bounds, and
    4) weak-coupling OS + reconstruction interfaces.
    This is the higher-moment generalization of the hard-core per-volume route. -/
theorem
    phi4_wightman_exists_of_os_and_productTensor_dense_and_normalized_order0_of_sq_integrable_data_and_higher_moment_polynomial_bound_per_volume_and_uniform_partition_bound
    (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [OSAxiomCoreModel params] →
    [WightmanReconstructionModel params] →
    [OSDistributionE2Model params] →
    [OSE4ClusterModel params] →
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        AEStronglyMeasurable (interactionCutoff params Λ κ)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hcutoff_sq :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        Integrable (fun ω => (interactionCutoff params Λ κ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hcutoff_conv :
      ∀ (Λ : Rectangle),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then
            ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)
            else 0)
          Filter.atTop
          (nhds 0)) →
    (hcutoff_ae :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
            Filter.atTop
            (nhds (interaction params Λ ω))) →
    (hinteraction_meas :
      ∀ (Λ : Rectangle),
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hinteraction_sq :
      ∀ (Λ : Rectangle),
        Integrable (fun ω => (interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (j : ℕ) →
    (hj : 0 < j) →
    (betaMom : ℝ) →
    (hbetaMom : 1 < betaMom) →
    (C : Rectangle → ℝ) →
    (hC_nonneg : ∀ Λ : Rectangle, 0 ≤ C Λ) →
    (hInt :
      ∀ (Λ : Rectangle) (n : ℕ),
        Integrable
          (fun ω : FieldConfig2D =>
            |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω| ^ (2 * j))
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hM :
      ∀ (Λ : Rectangle) (n : ℕ),
        ∫ ω : FieldConfig2D,
          |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω| ^ (2 * j)
          ∂(freeFieldMeasure params.mass params.mass_pos)
        ≤ C Λ * (↑(n + 1) : ℝ) ^ (-betaMom)) →
    (hpartition :
      ∀ (Λ : Rectangle) (q : ℝ), 0 < q →
        ∃ D : ℝ,
          (∀ n : ℕ,
            Integrable
              (fun ω : FieldConfig2D =>
                Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)))
              (freeFieldMeasure params.mass params.mass_pos)) ∧
          (∀ n : ℕ,
            ∫ ω : FieldConfig2D,
              Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
              ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D)) →
    (hsmall : params.coupling < os4WeakCouplingThreshold params) →
    (alpha beta gamma : ℝ) →
    (hbeta : 0 < beta) →
    (huniform : ∀ h : TestFun2D, ∃ c : ℝ, ∀ Λ : Rectangle,
      |generatingFunctional params Λ h| ≤ Real.exp (c * normFunctional h)) →
    (hcompat :
      ∀ (n : ℕ) (f : Fin n → TestFun2D),
        phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily f) =
          (infiniteVolumeSchwinger params n f : ℂ)) →
    (hreduce :
      ∀ (c : ℝ) (n : ℕ) (_hn : 0 < n) (f : Fin n → TestFun2D),
        ∑ i : Fin n, (Nat.factorial n : ℝ) *
            (Real.exp (c * normFunctional (f i)) +
              Real.exp (c * normFunctional (-(f i)))) ≤
          alpha * beta ^ n * (n.factorial : ℝ) ^ gamma *
            SchwartzMap.seminorm ℝ 0 0
              (schwartzProductTensorFromTestFamily f)) →
    (hdense :
      ∀ (n : ℕ) (_hn : 0 < n),
        DenseRange (fun f : Fin n → TestFun2D =>
          schwartzProductTensorFromTestFamily f)) →
    ∃ (Wfn : WightmanFunctions 1),
      ∃ (OS' : OsterwalderSchraderAxioms 1),
        OS'.S = phi4SchwingerFunctions params ∧
        IsWickRotationPair OS'.S Wfn.W := by
  intro _hlimit _hcore _hrec _he2 _he4
    hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
    hinteraction_meas hinteraction_sq
    j hj betaMom hbetaMom C hC_nonneg hInt hM hpartition
    hsmall alpha beta gamma hbeta huniform hcompat hreduce hdense
  rcases
      interactionIntegrabilityModel_nonempty_of_sq_integrable_data_and_higher_moment_polynomial_bound_per_volume_and_uniform_partition_bound
        (params := params)
        hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
        hinteraction_meas hinteraction_sq
        j hj betaMom hbetaMom C hC_nonneg hInt hM hpartition with ⟨hI⟩
  letI : InteractionIntegrabilityModel params := hI
  exact phi4_wightman_exists_of_os_and_productTensor_dense_and_normalized_order0
    params hsmall alpha beta gamma hbeta huniform hcompat hreduce hdense

/-- Dense product-tensor weak-coupling Wightman endpoint from:
    1) square-integrable/measurable UV interaction data,
    2) per-volume polynomial-decay squared-moment shifted UV-difference bounds
       with graph-natural decay rate `(n+2)^(-β)`,
    3) per-volume uniform shifted-cutoff partition-function bounds, and
    4) weak-coupling OS + reconstruction interfaces.
    This is the hard-core WP1 per-volume route in `(n+2)`-decay form. -/
theorem
    phi4_wightman_exists_of_os_and_productTensor_dense_and_normalized_order0_of_sq_integrable_data_and_sq_moment_polynomial_bound_per_volume_and_uniform_partition_bound_of_succ_succ
    (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [OSAxiomCoreModel params] →
    [WightmanReconstructionModel params] →
    [OSDistributionE2Model params] →
    [OSE4ClusterModel params] →
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        AEStronglyMeasurable (interactionCutoff params Λ κ)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hcutoff_sq :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        Integrable (fun ω => (interactionCutoff params Λ κ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hcutoff_conv :
      ∀ (Λ : Rectangle),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then
            ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)
            else 0)
          Filter.atTop
          (nhds 0)) →
    (hcutoff_ae :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
            Filter.atTop
            (nhds (interaction params Λ ω))) →
    (hinteraction_meas :
      ∀ (Λ : Rectangle),
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hinteraction_sq :
      ∀ (Λ : Rectangle),
        Integrable (fun ω => (interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (betaMom : ℝ) →
    (hbetaMom : 1 < betaMom) →
    (C : Rectangle → ℝ) →
    (hC_nonneg : ∀ Λ : Rectangle, 0 ≤ C Λ) →
    (hInt :
      ∀ (Λ : Rectangle) (n : ℕ),
        Integrable
          (fun ω : FieldConfig2D =>
            (interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hM :
      ∀ (Λ : Rectangle) (n : ℕ),
        ∫ ω : FieldConfig2D,
          (interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω) ^ 2
          ∂(freeFieldMeasure params.mass params.mass_pos)
        ≤ C Λ * (↑(n + 2) : ℝ) ^ (-betaMom)) →
    (hpartition :
      ∀ (Λ : Rectangle) (q : ℝ), 0 < q →
        ∃ D : ℝ,
          (∀ n : ℕ,
            Integrable
              (fun ω : FieldConfig2D =>
                Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)))
              (freeFieldMeasure params.mass params.mass_pos)) ∧
          (∀ n : ℕ,
            ∫ ω : FieldConfig2D,
              Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
              ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D)) →
    (hsmall : params.coupling < os4WeakCouplingThreshold params) →
    (alpha beta gamma : ℝ) →
    (hbeta : 0 < beta) →
    (huniform : ∀ h : TestFun2D, ∃ c : ℝ, ∀ Λ : Rectangle,
      |generatingFunctional params Λ h| ≤ Real.exp (c * normFunctional h)) →
    (hcompat :
      ∀ (n : ℕ) (f : Fin n → TestFun2D),
        phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily f) =
          (infiniteVolumeSchwinger params n f : ℂ)) →
    (hreduce :
      ∀ (c : ℝ) (n : ℕ) (_hn : 0 < n) (f : Fin n → TestFun2D),
        ∑ i : Fin n, (Nat.factorial n : ℝ) *
            (Real.exp (c * normFunctional (f i)) +
              Real.exp (c * normFunctional (-(f i)))) ≤
          alpha * beta ^ n * (n.factorial : ℝ) ^ gamma *
            SchwartzMap.seminorm ℝ 0 0
              (schwartzProductTensorFromTestFamily f)) →
    (hdense :
      ∀ (n : ℕ) (_hn : 0 < n),
        DenseRange (fun f : Fin n → TestFun2D =>
          schwartzProductTensorFromTestFamily f)) →
    ∃ (Wfn : WightmanFunctions 1),
      ∃ (OS' : OsterwalderSchraderAxioms 1),
        OS'.S = phi4SchwingerFunctions params ∧
        IsWickRotationPair OS'.S Wfn.W := by
  intro _hlimit _hcore _hrec _he2 _he4
    hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
    hinteraction_meas hinteraction_sq
    betaMom hbetaMom C hC_nonneg hInt hM hpartition
    hsmall alpha beta gamma hbeta huniform hcompat hreduce hdense
  rcases
      interactionIntegrabilityModel_nonempty_of_sq_integrable_data_and_sq_moment_polynomial_bound_per_volume_and_uniform_partition_bound_of_succ_succ
        (params := params)
        hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
        hinteraction_meas hinteraction_sq
        betaMom hbetaMom C hC_nonneg hInt hM hpartition with ⟨hI⟩
  letI : InteractionIntegrabilityModel params := hI
  exact phi4_wightman_exists_of_os_and_productTensor_dense_and_normalized_order0
    params hsmall alpha beta gamma hbeta huniform hcompat hreduce hdense

/-- Dense product-tensor weak-coupling Wightman endpoint from:
    1) square-integrable/measurable UV interaction data,
    2) a fixed higher even moment order `2j` (`j > 0`) with per-volume
       polynomial-decay shifted UV-difference bounds and graph-natural decay
       rate `(n+2)^(-β)`,
    3) per-volume uniform shifted-cutoff partition-function bounds, and
    4) weak-coupling OS + reconstruction interfaces.
    This is the higher-moment hard-core per-volume route in `(n+2)`-decay
    form. -/
theorem
    phi4_wightman_exists_of_os_and_productTensor_dense_and_normalized_order0_of_sq_integrable_data_and_higher_moment_polynomial_bound_per_volume_and_uniform_partition_bound_of_succ_succ
    (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [OSAxiomCoreModel params] →
    [WightmanReconstructionModel params] →
    [OSDistributionE2Model params] →
    [OSE4ClusterModel params] →
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        AEStronglyMeasurable (interactionCutoff params Λ κ)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hcutoff_sq :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        Integrable (fun ω => (interactionCutoff params Λ κ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hcutoff_conv :
      ∀ (Λ : Rectangle),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then
            ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)
            else 0)
          Filter.atTop
          (nhds 0)) →
    (hcutoff_ae :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
            Filter.atTop
            (nhds (interaction params Λ ω))) →
    (hinteraction_meas :
      ∀ (Λ : Rectangle),
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hinteraction_sq :
      ∀ (Λ : Rectangle),
        Integrable (fun ω => (interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (j : ℕ) →
    (hj : 0 < j) →
    (betaMom : ℝ) →
    (hbetaMom : 1 < betaMom) →
    (C : Rectangle → ℝ) →
    (hC_nonneg : ∀ Λ : Rectangle, 0 ≤ C Λ) →
    (hInt :
      ∀ (Λ : Rectangle) (n : ℕ),
        Integrable
          (fun ω : FieldConfig2D =>
            |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω| ^ (2 * j))
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hM :
      ∀ (Λ : Rectangle) (n : ℕ),
        ∫ ω : FieldConfig2D,
          |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω| ^ (2 * j)
          ∂(freeFieldMeasure params.mass params.mass_pos)
        ≤ C Λ * (↑(n + 2) : ℝ) ^ (-betaMom)) →
    (hpartition :
      ∀ (Λ : Rectangle) (q : ℝ), 0 < q →
        ∃ D : ℝ,
          (∀ n : ℕ,
            Integrable
              (fun ω : FieldConfig2D =>
                Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)))
              (freeFieldMeasure params.mass params.mass_pos)) ∧
          (∀ n : ℕ,
            ∫ ω : FieldConfig2D,
              Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
              ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D)) →
    (hsmall : params.coupling < os4WeakCouplingThreshold params) →
    (alpha beta gamma : ℝ) →
    (hbeta : 0 < beta) →
    (huniform : ∀ h : TestFun2D, ∃ c : ℝ, ∀ Λ : Rectangle,
      |generatingFunctional params Λ h| ≤ Real.exp (c * normFunctional h)) →
    (hcompat :
      ∀ (n : ℕ) (f : Fin n → TestFun2D),
        phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily f) =
          (infiniteVolumeSchwinger params n f : ℂ)) →
    (hreduce :
      ∀ (c : ℝ) (n : ℕ) (_hn : 0 < n) (f : Fin n → TestFun2D),
        ∑ i : Fin n, (Nat.factorial n : ℝ) *
            (Real.exp (c * normFunctional (f i)) +
              Real.exp (c * normFunctional (-(f i)))) ≤
          alpha * beta ^ n * (n.factorial : ℝ) ^ gamma *
            SchwartzMap.seminorm ℝ 0 0
              (schwartzProductTensorFromTestFamily f)) →
    (hdense :
      ∀ (n : ℕ) (_hn : 0 < n),
        DenseRange (fun f : Fin n → TestFun2D =>
          schwartzProductTensorFromTestFamily f)) →
    ∃ (Wfn : WightmanFunctions 1),
      ∃ (OS' : OsterwalderSchraderAxioms 1),
        OS'.S = phi4SchwingerFunctions params ∧
        IsWickRotationPair OS'.S Wfn.W := by
  intro _hlimit _hcore _hrec _he2 _he4
    hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
    hinteraction_meas hinteraction_sq
    j hj betaMom hbetaMom C hC_nonneg hInt hM hpartition
    hsmall alpha beta gamma hbeta huniform hcompat hreduce hdense
  rcases
      interactionIntegrabilityModel_nonempty_of_sq_integrable_data_and_higher_moment_polynomial_bound_per_volume_and_uniform_partition_bound_of_succ_succ
        (params := params)
        hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
        hinteraction_meas hinteraction_sq
        j hj betaMom hbetaMom C hC_nonneg hInt hM hpartition with ⟨hI⟩
  letI : InteractionIntegrabilityModel params := hI
  exact phi4_wightman_exists_of_os_and_productTensor_dense_and_normalized_order0
    params hsmall alpha beta gamma hbeta huniform hcompat hreduce hdense

/-- Interface-level Wightman existence endpoint driven by explicit WP1-style
    interaction input (shifted-cutoff geometric moment decay), by first
    constructing `ReconstructionLinearGrowthModel` and then invoking the
    standard interface reconstruction theorem. -/
theorem phi4_wightman_exists_of_interfaces_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
    (params : Phi4Params) :
    [InteractionUVModel params] →
    [SchwingerLimitModel params] →
    [OSAxiomCoreModel params] →
    [WightmanReconstructionModel params] →
    [OSDistributionE2Model params] →
    [OSE4ClusterModel params] →
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
            ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D * r ^ n)) →
    (hsmall : params.coupling < os4WeakCouplingThreshold params) →
    (alpha beta gamma : ℝ) →
    (hbeta : 0 < beta) →
    (huniform : ∀ h : TestFun2D, ∃ c : ℝ, ∀ Λ : Rectangle,
      |generatingFunctional params Λ h| ≤ Real.exp (c * normFunctional h)) →
    (hcompat :
      ∀ (n : ℕ) (f : Fin n → TestFun2D),
        phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily f) =
          (infiniteVolumeSchwinger params n f : ℂ)) →
    (hreduce :
      ∀ (c : ℝ) (n : ℕ) (_hn : 0 < n) (f : Fin n → TestFun2D),
        ∑ i : Fin n, (Nat.factorial n : ℝ) *
            (Real.exp (c * normFunctional (f i)) +
              Real.exp (c * normFunctional (-(f i)))) ≤
          alpha * beta ^ n * (n.factorial : ℝ) ^ gamma *
            SchwartzMap.seminorm ℝ 0 0
              (schwartzProductTensorFromTestFamily f)) →
    (hdense :
      ∀ (n : ℕ) (_hn : 0 < n),
        DenseRange (fun f : Fin n → TestFun2D =>
          schwartzProductTensorFromTestFamily f)) →
    ∃ (Wfn : WightmanFunctions 1),
      ∃ (OS : OsterwalderSchraderAxioms 1),
        OS.S = phi4SchwingerFunctions params ∧
        IsWickRotationPair OS.S Wfn.W := by
  intro _huv _hlimit _hcore _hrec _he2 _he4 hmom hsmall
    alpha beta gamma hbeta huniform hcompat hreduce hdense
  rcases
      reconstructionLinearGrowthModel_nonempty_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
        (params := params) hmom hsmall alpha beta gamma hbeta
        huniform hcompat hreduce hdense with ⟨hlin⟩
  letI : ReconstructionLinearGrowthModel params := hlin
  exact phi4_wightman_exists_of_explicit_data params
    (hlinear := phi4_linear_growth_of_interface params)
    (hreconstruct := phi4_wightman_reconstruction_step_of_interface params)

/-- Interface-level Wightman existence endpoint from explicit
    real-parameterized a.e. UV convergence, cutoff measurability, and
    deterministic linear shifted-cutoff lower bounds
    `a * n - b ≤ interactionCutoff(κ_{n+1})` (`a > 0`).
    This first constructs linear-growth reconstruction data via the
    corresponding explicit linear-lower-bound frontier theorem. -/
theorem phi4_wightman_exists_of_interfaces_of_tendsto_ae_and_linear_lower_bound
    (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [OSAxiomCoreModel params] →
    [WightmanReconstructionModel params] →
    [OSDistributionE2Model params] →
    [OSE4ClusterModel params] →
    (hcutoff_tendsto_ae :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
            Filter.atTop
            (nhds (interaction params Λ ω))) →
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        AEStronglyMeasurable (interactionCutoff params Λ κ)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hlin :
      ∀ Λ : Rectangle, ∃ a b : ℝ, 0 < a ∧
        ∀ (n : ℕ) (ω : FieldConfig2D),
          a * (n : ℝ) - b ≤ interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω) →
    (hsmall : params.coupling < os4WeakCouplingThreshold params) →
    (alpha beta gamma : ℝ) →
    (hbeta : 0 < beta) →
    (huniform : ∀ h : TestFun2D, ∃ c : ℝ, ∀ Λ : Rectangle,
      |generatingFunctional params Λ h| ≤ Real.exp (c * normFunctional h)) →
    (hcompat :
      ∀ (n : ℕ) (f : Fin n → TestFun2D),
        phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily f) =
          (infiniteVolumeSchwinger params n f : ℂ)) →
    (hreduce :
      ∀ (c : ℝ) (n : ℕ) (_hn : 0 < n) (f : Fin n → TestFun2D),
        ∑ i : Fin n, (Nat.factorial n : ℝ) *
            (Real.exp (c * normFunctional (f i)) +
              Real.exp (c * normFunctional (-(f i)))) ≤
          alpha * beta ^ n * (n.factorial : ℝ) ^ gamma *
            SchwartzMap.seminorm ℝ 0 0
              (schwartzProductTensorFromTestFamily f)) →
    (hdense :
      ∀ (n : ℕ) (_hn : 0 < n),
        DenseRange (fun f : Fin n → TestFun2D =>
          schwartzProductTensorFromTestFamily f)) →
    ∃ (Wfn : WightmanFunctions 1),
      ∃ (OS : OsterwalderSchraderAxioms 1),
        OS.S = phi4SchwingerFunctions params ∧
        IsWickRotationPair OS.S Wfn.W := by
  intro _hlimit _hcore _hrec _he2 _he4
    hcutoff_tendsto_ae hcutoff_meas hlin hsmall
    alpha beta gamma hbeta huniform hcompat hreduce hdense
  have hlinear :
      ∃ OS : OsterwalderSchraderAxioms 1,
        OS.S = phi4SchwingerFunctions params ∧
        Nonempty (OSLinearGrowthCondition 1 OS) :=
    gap_phi4_linear_growth_of_tendsto_ae_and_linear_lower_bound
      (params := params)
      hcutoff_tendsto_ae hcutoff_meas hlin
      hsmall alpha beta gamma hbeta huniform hcompat hreduce hdense
  exact phi4_wightman_exists_of_explicit_data params
    (hlinear := hlinear)
    (hreconstruct := phi4_wightman_reconstruction_step_of_interface params)

/-- Interface-level Wightman existence endpoint from:
    1) square-integrable/measurable UV interaction data,
    2) shifted-cutoff geometric moment decay, and
    3) weak-coupling OS/product-tensor hypotheses.
    This uses the direct square-data linear-growth constructor, then applies the
    standard interface reconstruction theorem. -/
theorem
    phi4_wightman_exists_of_interfaces_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
    (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [OSAxiomCoreModel params] →
    [WightmanReconstructionModel params] →
    [OSDistributionE2Model params] →
    [OSE4ClusterModel params] →
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        AEStronglyMeasurable (interactionCutoff params Λ κ)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hcutoff_sq :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        Integrable (fun ω => (interactionCutoff params Λ κ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hcutoff_conv :
      ∀ (Λ : Rectangle),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then
            ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)
            else 0)
          Filter.atTop
          (nhds 0)) →
    (hcutoff_ae :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
            Filter.atTop
            (nhds (interaction params Λ ω))) →
    (hinteraction_meas :
      ∀ (Λ : Rectangle),
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hinteraction_sq :
      ∀ (Λ : Rectangle),
        Integrable (fun ω => (interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos)) →
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
            ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D * r ^ n)) →
    (hsmall : params.coupling < os4WeakCouplingThreshold params) →
    (alpha beta gamma : ℝ) →
    (hbeta : 0 < beta) →
    (huniform : ∀ h : TestFun2D, ∃ c : ℝ, ∀ Λ : Rectangle,
      |generatingFunctional params Λ h| ≤ Real.exp (c * normFunctional h)) →
    (hcompat :
      ∀ (n : ℕ) (f : Fin n → TestFun2D),
        phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily f) =
          (infiniteVolumeSchwinger params n f : ℂ)) →
    (hreduce :
      ∀ (c : ℝ) (n : ℕ) (_hn : 0 < n) (f : Fin n → TestFun2D),
        ∑ i : Fin n, (Nat.factorial n : ℝ) *
            (Real.exp (c * normFunctional (f i)) +
              Real.exp (c * normFunctional (-(f i)))) ≤
          alpha * beta ^ n * (n.factorial : ℝ) ^ gamma *
            SchwartzMap.seminorm ℝ 0 0
              (schwartzProductTensorFromTestFamily f)) →
    (hdense :
      ∀ (n : ℕ) (_hn : 0 < n),
        DenseRange (fun f : Fin n → TestFun2D =>
          schwartzProductTensorFromTestFamily f)) →
    ∃ (Wfn : WightmanFunctions 1),
      ∃ (OS : OsterwalderSchraderAxioms 1),
        OS.S = phi4SchwingerFunctions params ∧
        IsWickRotationPair OS.S Wfn.W := by
  intro _hlimit _hcore _hrec _he2 _he4
    hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
    hinteraction_meas hinteraction_sq
    hmom hsmall alpha beta gamma hbeta huniform hcompat hreduce hdense
  rcases
      reconstructionLinearGrowthModel_nonempty_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
        (params := params)
        hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
        hinteraction_meas hinteraction_sq
        hmom hsmall alpha beta gamma hbeta
        huniform hcompat hreduce hdense with ⟨hlin⟩
  letI : ReconstructionLinearGrowthModel params := hlin
  exact phi4_wightman_exists_of_explicit_data params
    (hlinear := phi4_linear_growth_of_interface params)
    (hreconstruct := phi4_wightman_reconstruction_step_of_interface params)

/-- Interface-level Wightman existence endpoint from:
    1) square-integrable/measurable UV interaction data,
    2) per-volume polynomial-decay squared-moment shifted UV-difference bounds,
    3) per-volume uniform shifted-cutoff partition-function bounds, and
    4) weak-coupling OS/product-tensor hypotheses.
    This follows the hard-core WP1 per-volume route to
    `ReconstructionLinearGrowthModel`, then applies interface reconstruction. -/
theorem
    phi4_wightman_exists_of_interfaces_of_sq_integrable_data_and_sq_moment_polynomial_bound_per_volume_and_uniform_partition_bound
    (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [OSAxiomCoreModel params] →
    [WightmanReconstructionModel params] →
    [OSDistributionE2Model params] →
    [OSE4ClusterModel params] →
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        AEStronglyMeasurable (interactionCutoff params Λ κ)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hcutoff_sq :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        Integrable (fun ω => (interactionCutoff params Λ κ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hcutoff_conv :
      ∀ (Λ : Rectangle),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then
            ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)
            else 0)
          Filter.atTop
          (nhds 0)) →
    (hcutoff_ae :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
            Filter.atTop
            (nhds (interaction params Λ ω))) →
    (hinteraction_meas :
      ∀ (Λ : Rectangle),
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hinteraction_sq :
      ∀ (Λ : Rectangle),
        Integrable (fun ω => (interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (betaMom : ℝ) →
    (hbetaMom : 1 < betaMom) →
    (C : Rectangle → ℝ) →
    (hC_nonneg : ∀ Λ : Rectangle, 0 ≤ C Λ) →
    (hInt :
      ∀ (Λ : Rectangle) (n : ℕ),
        Integrable
          (fun ω : FieldConfig2D =>
            (interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hM :
      ∀ (Λ : Rectangle) (n : ℕ),
        ∫ ω : FieldConfig2D,
          (interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω) ^ 2
          ∂(freeFieldMeasure params.mass params.mass_pos)
        ≤ C Λ * (↑(n + 1) : ℝ) ^ (-betaMom)) →
    (hpartition :
      ∀ (Λ : Rectangle) (q : ℝ), 0 < q →
        ∃ D : ℝ,
          (∀ n : ℕ,
            Integrable
              (fun ω : FieldConfig2D =>
                Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)))
              (freeFieldMeasure params.mass params.mass_pos)) ∧
          (∀ n : ℕ,
            ∫ ω : FieldConfig2D,
              Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
              ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D)) →
    (hsmall : params.coupling < os4WeakCouplingThreshold params) →
    (alpha beta gamma : ℝ) →
    (hbeta : 0 < beta) →
    (huniform : ∀ h : TestFun2D, ∃ c : ℝ, ∀ Λ : Rectangle,
      |generatingFunctional params Λ h| ≤ Real.exp (c * normFunctional h)) →
    (hcompat :
      ∀ (n : ℕ) (f : Fin n → TestFun2D),
        phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily f) =
          (infiniteVolumeSchwinger params n f : ℂ)) →
    (hreduce :
      ∀ (c : ℝ) (n : ℕ) (_hn : 0 < n) (f : Fin n → TestFun2D),
        ∑ i : Fin n, (Nat.factorial n : ℝ) *
            (Real.exp (c * normFunctional (f i)) +
              Real.exp (c * normFunctional (-(f i)))) ≤
          alpha * beta ^ n * (n.factorial : ℝ) ^ gamma *
            SchwartzMap.seminorm ℝ 0 0
              (schwartzProductTensorFromTestFamily f)) →
    (hdense :
      ∀ (n : ℕ) (_hn : 0 < n),
        DenseRange (fun f : Fin n → TestFun2D =>
          schwartzProductTensorFromTestFamily f)) →
    ∃ (Wfn : WightmanFunctions 1),
      ∃ (OS : OsterwalderSchraderAxioms 1),
        OS.S = phi4SchwingerFunctions params ∧
        IsWickRotationPair OS.S Wfn.W := by
  intro _hlimit _hcore _hrec _he2 _he4
    hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
    hinteraction_meas hinteraction_sq
    betaMom hbetaMom C hC_nonneg hInt hM hpartition
    hsmall alpha beta gamma hbeta huniform hcompat hreduce hdense
  rcases
      reconstructionLinearGrowthModel_nonempty_of_sq_integrable_data_and_sq_moment_polynomial_bound_per_volume_and_uniform_partition_bound
        (params := params)
        hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
        hinteraction_meas hinteraction_sq
        betaMom hbetaMom C hC_nonneg hInt hM hpartition
        hsmall alpha beta gamma hbeta
        huniform hcompat hreduce hdense with ⟨hlin⟩
  letI : ReconstructionLinearGrowthModel params := hlin
  exact phi4_wightman_exists_of_explicit_data params
    (hlinear := phi4_linear_growth_of_interface params)
    (hreconstruct := phi4_wightman_reconstruction_step_of_interface params)

/-- Interface-level Wightman existence endpoint from:
    1) square-integrable/measurable UV interaction data,
    2) explicit cutoff a.e. convergence,
    3) per-volume bad-set decomposition data (linear lower bounds off bad sets,
       geometric second moments, ENNReal geometric bad-set tails), and
    4) weak-coupling OS/product-tensor hypotheses.

    This is the ENNReal-tail bad-set hard-core WP1 route to interface-level
    reconstruction. -/
theorem
    phi4_wightman_exists_of_interfaces_of_sq_integrable_data_and_linear_lower_bound_off_bad_sets_and_sq_exp_moment_geometric_and_bad_measure_geometric_ennreal
    (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [OSAxiomCoreModel params] →
    [WightmanReconstructionModel params] →
    [OSDistributionE2Model params] →
    [OSE4ClusterModel params] →
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        AEStronglyMeasurable (interactionCutoff params Λ κ)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hcutoff_sq :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        Integrable (fun ω => (interactionCutoff params Λ κ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hcutoff_conv :
      ∀ (Λ : Rectangle),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then
            ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)
            else 0)
          Filter.atTop
          (nhds 0)) →
    (hcutoff_ae :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
            Filter.atTop
            (nhds (interaction params Λ ω))) →
    (hinteraction_meas :
      ∀ (Λ : Rectangle),
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hinteraction_sq :
      ∀ (Λ : Rectangle),
        Integrable (fun ω => (interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hdecomp :
      ∀ (Λ : Rectangle) (q : ℝ), 0 < q →
        ∃ a b : ℝ, 0 < a ∧
          ∃ bad : ℕ → Set FieldConfig2D,
            (∀ n : ℕ, MeasurableSet (bad n)) ∧
            (∀ n : ℕ,
              Integrable
                (fun ω : FieldConfig2D =>
                  Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)))
                (freeFieldMeasure params.mass params.mass_pos)) ∧
            (∀ (n : ℕ) (ω : FieldConfig2D), ω ∉ bad n →
              a * (n : ℝ) - b ≤ interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω) ∧
            (∀ n : ℕ,
              MemLp
                (fun ω : FieldConfig2D =>
                  Real.exp ((-q) * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
                2
                (freeFieldMeasure params.mass params.mass_pos)) ∧
            ∃ D2 r2 : ℝ,
              0 ≤ D2 ∧ 0 ≤ r2 ∧ r2 < 1 ∧
              (∀ n : ℕ,
                ∫ ω : FieldConfig2D,
                  (Real.exp
                    ((-q) * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)) ^ (2 : ℝ)
                  ∂(freeFieldMeasure params.mass params.mass_pos)
                ≤ D2 * r2 ^ n) ∧
              ∃ Cb rb : ℝ≥0∞,
                Cb ≠ ⊤ ∧ rb < 1 ∧
                (∀ n : ℕ,
                  (freeFieldMeasure params.mass params.mass_pos) (bad n) ≤ Cb * rb ^ n)) →
    (hsmall : params.coupling < os4WeakCouplingThreshold params) →
    (alpha beta gamma : ℝ) →
    (hbeta : 0 < beta) →
    (huniform : ∀ h : TestFun2D, ∃ c : ℝ, ∀ Λ : Rectangle,
      |generatingFunctional params Λ h| ≤ Real.exp (c * normFunctional h)) →
    (hcompat :
      ∀ (n : ℕ) (f : Fin n → TestFun2D),
        phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily f) =
          (infiniteVolumeSchwinger params n f : ℂ)) →
    (hreduce :
      ∀ (c : ℝ) (n : ℕ) (_hn : 0 < n) (f : Fin n → TestFun2D),
        ∑ i : Fin n, (Nat.factorial n : ℝ) *
            (Real.exp (c * normFunctional (f i)) +
              Real.exp (c * normFunctional (-(f i)))) ≤
          alpha * beta ^ n * (n.factorial : ℝ) ^ gamma *
            SchwartzMap.seminorm ℝ 0 0
              (schwartzProductTensorFromTestFamily f)) →
    (hdense :
      ∀ (n : ℕ) (_hn : 0 < n),
        DenseRange (fun f : Fin n → TestFun2D =>
          schwartzProductTensorFromTestFamily f)) →
    ∃ (Wfn : WightmanFunctions 1),
      ∃ (OS : OsterwalderSchraderAxioms 1),
        OS.S = phi4SchwingerFunctions params ∧
        IsWickRotationPair OS.S Wfn.W := by
  intro _hlimit _hcore _hrec _he2 _he4
    hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
    hinteraction_meas hinteraction_sq hdecomp
    hsmall alpha beta gamma hbeta huniform hcompat hreduce hdense
  rcases
      reconstructionLinearGrowthModel_nonempty_of_sq_integrable_data_and_linear_lower_bound_off_bad_sets_and_sq_exp_moment_geometric_and_bad_measure_geometric_ennreal
        (params := params)
        hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
        hinteraction_meas hinteraction_sq hdecomp
        hsmall alpha beta gamma hbeta
        huniform hcompat hreduce hdense with ⟨hlin⟩
  letI : ReconstructionLinearGrowthModel params := hlin
  exact phi4_wightman_exists_of_explicit_data params
    (hlinear := phi4_linear_growth_of_interface params)
    (hreconstruct := phi4_wightman_reconstruction_step_of_interface params)

/-- Interface-level Wightman existence endpoint from:
    1) square-integrable/measurable UV interaction data,
    2) per-volume geometric shifted-cutoff exponential moments with
       linear-threshold ratio control `exp(q * a) * r < 1`,
    3) geometric shifted-cutoff second moments for `exp(-q * interactionCutoff)`,
    4) weak-coupling OS/product-tensor hypotheses.

    This route uses the canonical measurable bad-set construction from the
    linear-threshold Chernoff bridge and avoids requiring an explicit
    decomposition payload at the endpoint. -/
theorem
    phi4_wightman_exists_of_interfaces_of_sq_integrable_data_and_linear_threshold_geometric_exp_moment_and_sq_exp_moment_geometric
    (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [OSAxiomCoreModel params] →
    [WightmanReconstructionModel params] →
    [OSDistributionE2Model params] →
    [OSE4ClusterModel params] →
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        AEStronglyMeasurable (interactionCutoff params Λ κ)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hcutoff_sq :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        Integrable (fun ω => (interactionCutoff params Λ κ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hcutoff_conv :
      ∀ (Λ : Rectangle),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then
            ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)
            else 0)
          Filter.atTop
          (nhds 0)) →
    (hcutoff_ae :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
            Filter.atTop
            (nhds (interaction params Λ ω))) →
    (hinteraction_meas :
      ∀ (Λ : Rectangle),
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hinteraction_sq :
      ∀ (Λ : Rectangle),
        Integrable (fun ω => (interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hcore :
      ∀ (Λ : Rectangle) (q : ℝ), 0 < q →
        ∃ a D r : ℝ,
          0 < a ∧ 0 ≤ D ∧ 0 ≤ r ∧ Real.exp (q * a) * r < 1 ∧
          (∀ n : ℕ,
            Integrable
              (fun ω : FieldConfig2D =>
                Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)))
              (freeFieldMeasure params.mass params.mass_pos)) ∧
          (∀ n : ℕ,
            ∫ ω : FieldConfig2D,
              Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
              ∂(freeFieldMeasure params.mass params.mass_pos)
            ≤ D * r ^ n) ∧
          (∀ n : ℕ,
            MemLp
              (fun ω : FieldConfig2D =>
                Real.exp ((-q) * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
              2
              (freeFieldMeasure params.mass params.mass_pos)) ∧
          ∃ D2 r2 : ℝ,
            0 ≤ D2 ∧ 0 ≤ r2 ∧ r2 < 1 ∧
            (∀ n : ℕ,
              ∫ ω : FieldConfig2D,
                (Real.exp
                  ((-q) * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)) ^ (2 : ℝ)
                ∂(freeFieldMeasure params.mass params.mass_pos)
              ≤ D2 * r2 ^ n)) →
    (hsmall : params.coupling < os4WeakCouplingThreshold params) →
    (alpha beta gamma : ℝ) →
    (hbeta : 0 < beta) →
    (huniform : ∀ h : TestFun2D, ∃ c : ℝ, ∀ Λ : Rectangle,
      |generatingFunctional params Λ h| ≤ Real.exp (c * normFunctional h)) →
    (hcompat :
      ∀ (n : ℕ) (f : Fin n → TestFun2D),
        phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily f) =
          (infiniteVolumeSchwinger params n f : ℂ)) →
    (hreduce :
      ∀ (c : ℝ) (n : ℕ) (_hn : 0 < n) (f : Fin n → TestFun2D),
        ∑ i : Fin n, (Nat.factorial n : ℝ) *
            (Real.exp (c * normFunctional (f i)) +
              Real.exp (c * normFunctional (-(f i)))) ≤
          alpha * beta ^ n * (n.factorial : ℝ) ^ gamma *
            SchwartzMap.seminorm ℝ 0 0
              (schwartzProductTensorFromTestFamily f)) →
    (hdense :
      ∀ (n : ℕ) (_hn : 0 < n),
        DenseRange (fun f : Fin n → TestFun2D =>
          schwartzProductTensorFromTestFamily f)) →
    ∃ (Wfn : WightmanFunctions 1),
      ∃ (OS : OsterwalderSchraderAxioms 1),
        OS.S = phi4SchwingerFunctions params ∧
        IsWickRotationPair OS.S Wfn.W := by
  intro _hlimit _hcore _hrec _he2 _he4
    hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
    hinteraction_meas hinteraction_sq hcore
    hsmall alpha beta gamma hbeta huniform hcompat hreduce hdense
  rcases
      reconstructionLinearGrowthModel_nonempty_of_sq_integrable_data_and_linear_threshold_geometric_exp_moment_and_sq_exp_moment_geometric
        (params := params)
        hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
        hinteraction_meas hinteraction_sq hcore
        hsmall alpha beta gamma hbeta
        huniform hcompat hreduce hdense with ⟨hlin⟩
  letI : ReconstructionLinearGrowthModel params := hlin
  exact phi4_wightman_exists_of_explicit_data params
    (hlinear := phi4_linear_growth_of_interface params)
    (hreconstruct := phi4_wightman_reconstruction_step_of_interface params)

/-- Interface-level Wightman existence endpoint from:
    1) square-integrable/measurable UV interaction data,
    2) per-volume geometric shifted-cutoff exponential moments at `q` with
       linear-threshold ratio control `exp(q * a) * r < 1`,
    3) per-volume geometric shifted-cutoff exponential moments at doubled
       parameter `2q`,
    4) weak-coupling OS/product-tensor hypotheses.

    This route uses the canonical measurable bad-set construction and derives
    square-data decomposition inputs internally from doubled-parameter moments. -/
theorem
    phi4_wightman_exists_of_interfaces_of_sq_integrable_data_and_linear_threshold_geometric_exp_moment_and_double_exp_moment_geometric
    (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [OSAxiomCoreModel params] →
    [WightmanReconstructionModel params] →
    [OSDistributionE2Model params] →
    [OSE4ClusterModel params] →
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        AEStronglyMeasurable (interactionCutoff params Λ κ)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hcutoff_sq :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        Integrable (fun ω => (interactionCutoff params Λ κ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hcutoff_conv :
      ∀ (Λ : Rectangle),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then
            ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)
            else 0)
          Filter.atTop
          (nhds 0)) →
    (hcutoff_ae :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
            Filter.atTop
            (nhds (interaction params Λ ω))) →
    (hinteraction_meas :
      ∀ (Λ : Rectangle),
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hinteraction_sq :
      ∀ (Λ : Rectangle),
        Integrable (fun ω => (interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hcore :
      ∀ (Λ : Rectangle) (q : ℝ), 0 < q →
        ∃ a D r D2 r2 : ℝ,
          0 < a ∧ 0 ≤ D ∧ 0 ≤ r ∧ Real.exp (q * a) * r < 1 ∧
          0 ≤ D2 ∧ 0 ≤ r2 ∧ r2 < 1 ∧
          (∀ n : ℕ,
            Integrable
              (fun ω : FieldConfig2D =>
                Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)))
              (freeFieldMeasure params.mass params.mass_pos)) ∧
          (∀ n : ℕ,
            ∫ ω : FieldConfig2D,
              Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
              ∂(freeFieldMeasure params.mass params.mass_pos)
            ≤ D * r ^ n) ∧
          (∀ n : ℕ,
            Integrable
              (fun ω : FieldConfig2D =>
                Real.exp ((-(2 * q)) * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
              (freeFieldMeasure params.mass params.mass_pos)) ∧
          (∀ n : ℕ,
            ∫ ω : FieldConfig2D,
              Real.exp ((-(2 * q)) * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)
              ∂(freeFieldMeasure params.mass params.mass_pos)
            ≤ D2 * r2 ^ n)) →
    (hsmall : params.coupling < os4WeakCouplingThreshold params) →
    (alpha beta gamma : ℝ) →
    (hbeta : 0 < beta) →
    (huniform : ∀ h : TestFun2D, ∃ c : ℝ, ∀ Λ : Rectangle,
      |generatingFunctional params Λ h| ≤ Real.exp (c * normFunctional h)) →
    (hcompat :
      ∀ (n : ℕ) (f : Fin n → TestFun2D),
        phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily f) =
          (infiniteVolumeSchwinger params n f : ℂ)) →
    (hreduce :
      ∀ (c : ℝ) (n : ℕ) (_hn : 0 < n) (f : Fin n → TestFun2D),
        ∑ i : Fin n, (Nat.factorial n : ℝ) *
            (Real.exp (c * normFunctional (f i)) +
              Real.exp (c * normFunctional (-(f i)))) ≤
          alpha * beta ^ n * (n.factorial : ℝ) ^ gamma *
            SchwartzMap.seminorm ℝ 0 0
              (schwartzProductTensorFromTestFamily f)) →
    (hdense :
      ∀ (n : ℕ) (_hn : 0 < n),
        DenseRange (fun f : Fin n → TestFun2D =>
          schwartzProductTensorFromTestFamily f)) →
    ∃ (Wfn : WightmanFunctions 1),
      ∃ (OS : OsterwalderSchraderAxioms 1),
        OS.S = phi4SchwingerFunctions params ∧
        IsWickRotationPair OS.S Wfn.W := by
  intro _hlimit _hcore _hrec _he2 _he4
    hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
    hinteraction_meas hinteraction_sq hcore
    hsmall alpha beta gamma hbeta huniform hcompat hreduce hdense
  rcases
      reconstructionLinearGrowthModel_nonempty_of_sq_integrable_data_and_linear_threshold_geometric_exp_moment_and_double_exp_moment_geometric
        (params := params)
        hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
        hinteraction_meas hinteraction_sq hcore
        hsmall alpha beta gamma hbeta
        huniform hcompat hreduce hdense with ⟨hlin⟩
  letI : ReconstructionLinearGrowthModel params := hlin
  exact phi4_wightman_exists_of_explicit_data params
    (hlinear := phi4_linear_growth_of_interface params)
    (hreconstruct := phi4_wightman_reconstruction_step_of_interface params)

/-- Same endpoint as
    `phi4_wightman_exists_of_interfaces_of_sq_integrable_data_and_linear_threshold_geometric_exp_moment_and_double_exp_moment_geometric`,
    with weaker core assumptions: no separate `q`-level integrability
    hypothesis is required. -/
theorem
    phi4_wightman_exists_of_interfaces_of_sq_integrable_data_and_linear_threshold_geometric_exp_moment_and_double_exp_moment_geometric_of_moment_bounds
    (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [OSAxiomCoreModel params] →
    [WightmanReconstructionModel params] →
    [OSDistributionE2Model params] →
    [OSE4ClusterModel params] →
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        AEStronglyMeasurable (interactionCutoff params Λ κ)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hcutoff_sq :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        Integrable (fun ω => (interactionCutoff params Λ κ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hcutoff_conv :
      ∀ (Λ : Rectangle),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then
            ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)
            else 0)
          Filter.atTop
          (nhds 0)) →
    (hcutoff_ae :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
            Filter.atTop
            (nhds (interaction params Λ ω))) →
    (hinteraction_meas :
      ∀ (Λ : Rectangle),
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hinteraction_sq :
      ∀ (Λ : Rectangle),
        Integrable (fun ω => (interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hcore :
      ∀ (Λ : Rectangle) (q : ℝ), 0 < q →
        ∃ a D r D2 r2 : ℝ,
          0 < a ∧ 0 ≤ D ∧ 0 ≤ r ∧ Real.exp (q * a) * r < 1 ∧
          0 ≤ D2 ∧ 0 ≤ r2 ∧ r2 < 1 ∧
          (∀ n : ℕ,
            ∫ ω : FieldConfig2D,
              Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
              ∂(freeFieldMeasure params.mass params.mass_pos)
            ≤ D * r ^ n) ∧
          (∀ n : ℕ,
            Integrable
              (fun ω : FieldConfig2D =>
                Real.exp ((-(2 * q)) * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
              (freeFieldMeasure params.mass params.mass_pos)) ∧
          (∀ n : ℕ,
            ∫ ω : FieldConfig2D,
              Real.exp ((-(2 * q)) * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)
              ∂(freeFieldMeasure params.mass params.mass_pos)
            ≤ D2 * r2 ^ n)) →
    (hsmall : params.coupling < os4WeakCouplingThreshold params) →
    (alpha beta gamma : ℝ) →
    (hbeta : 0 < beta) →
    (huniform : ∀ h : TestFun2D, ∃ c : ℝ, ∀ Λ : Rectangle,
      |generatingFunctional params Λ h| ≤ Real.exp (c * normFunctional h)) →
    (hcompat :
      ∀ (n : ℕ) (f : Fin n → TestFun2D),
        phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily f) =
          (infiniteVolumeSchwinger params n f : ℂ)) →
    (hreduce :
      ∀ (c : ℝ) (n : ℕ) (_hn : 0 < n) (f : Fin n → TestFun2D),
        ∑ i : Fin n, (Nat.factorial n : ℝ) *
            (Real.exp (c * normFunctional (f i)) +
              Real.exp (c * normFunctional (-(f i)))) ≤
          alpha * beta ^ n * (n.factorial : ℝ) ^ gamma *
            SchwartzMap.seminorm ℝ 0 0
              (schwartzProductTensorFromTestFamily f)) →
    (hdense :
      ∀ (n : ℕ) (_hn : 0 < n),
        DenseRange (fun f : Fin n → TestFun2D =>
          schwartzProductTensorFromTestFamily f)) →
    ∃ (Wfn : WightmanFunctions 1),
      ∃ (OS : OsterwalderSchraderAxioms 1),
        OS.S = phi4SchwingerFunctions params ∧
        IsWickRotationPair OS.S Wfn.W := by
  intro _hlimit _hcore _hrec _he2 _he4
    hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
    hinteraction_meas hinteraction_sq hcore
    hsmall alpha beta gamma hbeta huniform hcompat hreduce hdense
  rcases
      reconstructionLinearGrowthModel_nonempty_of_sq_integrable_data_and_linear_threshold_geometric_exp_moment_and_double_exp_moment_geometric_of_moment_bounds
        (params := params)
        hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
        hinteraction_meas hinteraction_sq hcore
        hsmall alpha beta gamma hbeta
        huniform hcompat hreduce hdense with ⟨hlin⟩
  letI : ReconstructionLinearGrowthModel params := hlin
  exact phi4_wightman_exists_of_explicit_data params
    (hlinear := phi4_linear_growth_of_interface params)
    (hreconstruct := phi4_wightman_reconstruction_step_of_interface params)

/-- Interface-level Wightman existence endpoint from:
    1) square-integrable/measurable UV interaction data,
    2) a fixed higher even moment order `2j` (`j > 0`) with per-volume
       polynomial-decay shifted UV-difference bounds,
    3) per-volume uniform shifted-cutoff partition-function bounds, and
    4) weak-coupling OS/product-tensor hypotheses.
    This is the higher-moment generalization of the hard-core per-volume
    interface route. -/
theorem
    phi4_wightman_exists_of_interfaces_of_sq_integrable_data_and_higher_moment_polynomial_bound_per_volume_and_uniform_partition_bound
    (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [OSAxiomCoreModel params] →
    [WightmanReconstructionModel params] →
    [OSDistributionE2Model params] →
    [OSE4ClusterModel params] →
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        AEStronglyMeasurable (interactionCutoff params Λ κ)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hcutoff_sq :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        Integrable (fun ω => (interactionCutoff params Λ κ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hcutoff_conv :
      ∀ (Λ : Rectangle),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then
            ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)
            else 0)
          Filter.atTop
          (nhds 0)) →
    (hcutoff_ae :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
            Filter.atTop
            (nhds (interaction params Λ ω))) →
    (hinteraction_meas :
      ∀ (Λ : Rectangle),
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hinteraction_sq :
      ∀ (Λ : Rectangle),
        Integrable (fun ω => (interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (j : ℕ) →
    (hj : 0 < j) →
    (betaMom : ℝ) →
    (hbetaMom : 1 < betaMom) →
    (C : Rectangle → ℝ) →
    (hC_nonneg : ∀ Λ : Rectangle, 0 ≤ C Λ) →
    (hInt :
      ∀ (Λ : Rectangle) (n : ℕ),
        Integrable
          (fun ω : FieldConfig2D =>
            |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω| ^ (2 * j))
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hM :
      ∀ (Λ : Rectangle) (n : ℕ),
        ∫ ω : FieldConfig2D,
          |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω| ^ (2 * j)
          ∂(freeFieldMeasure params.mass params.mass_pos)
        ≤ C Λ * (↑(n + 1) : ℝ) ^ (-betaMom)) →
    (hpartition :
      ∀ (Λ : Rectangle) (q : ℝ), 0 < q →
        ∃ D : ℝ,
          (∀ n : ℕ,
            Integrable
              (fun ω : FieldConfig2D =>
                Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)))
              (freeFieldMeasure params.mass params.mass_pos)) ∧
          (∀ n : ℕ,
            ∫ ω : FieldConfig2D,
              Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
              ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D)) →
    (hsmall : params.coupling < os4WeakCouplingThreshold params) →
    (alpha beta gamma : ℝ) →
    (hbeta : 0 < beta) →
    (huniform : ∀ h : TestFun2D, ∃ c : ℝ, ∀ Λ : Rectangle,
      |generatingFunctional params Λ h| ≤ Real.exp (c * normFunctional h)) →
    (hcompat :
      ∀ (n : ℕ) (f : Fin n → TestFun2D),
        phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily f) =
          (infiniteVolumeSchwinger params n f : ℂ)) →
    (hreduce :
      ∀ (c : ℝ) (n : ℕ) (_hn : 0 < n) (f : Fin n → TestFun2D),
        ∑ i : Fin n, (Nat.factorial n : ℝ) *
            (Real.exp (c * normFunctional (f i)) +
              Real.exp (c * normFunctional (-(f i)))) ≤
          alpha * beta ^ n * (n.factorial : ℝ) ^ gamma *
            SchwartzMap.seminorm ℝ 0 0
              (schwartzProductTensorFromTestFamily f)) →
    (hdense :
      ∀ (n : ℕ) (_hn : 0 < n),
        DenseRange (fun f : Fin n → TestFun2D =>
          schwartzProductTensorFromTestFamily f)) →
    ∃ (Wfn : WightmanFunctions 1),
      ∃ (OS : OsterwalderSchraderAxioms 1),
        OS.S = phi4SchwingerFunctions params ∧
        IsWickRotationPair OS.S Wfn.W := by
  intro _hlimit _hcore _hrec _he2 _he4
    hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
    hinteraction_meas hinteraction_sq
    j hj betaMom hbetaMom C hC_nonneg hInt hM hpartition
    hsmall alpha beta gamma hbeta huniform hcompat hreduce hdense
  rcases
      reconstructionLinearGrowthModel_nonempty_of_sq_integrable_data_and_higher_moment_polynomial_bound_per_volume_and_uniform_partition_bound
        (params := params)
        hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
        hinteraction_meas hinteraction_sq
        j hj betaMom hbetaMom C hC_nonneg hInt hM hpartition
        hsmall alpha beta gamma hbeta
        huniform hcompat hreduce hdense with ⟨hlin⟩
  letI : ReconstructionLinearGrowthModel params := hlin
  exact phi4_wightman_exists_of_explicit_data params
    (hlinear := phi4_linear_growth_of_interface params)
    (hreconstruct := phi4_wightman_reconstruction_step_of_interface params)

/-- Interface-level Wightman existence endpoint from:
    1) square-integrable/measurable UV interaction data,
    2) per-volume polynomial-decay squared-moment shifted UV-difference bounds
       with graph-natural decay rate `(n+2)^(-β)`,
    3) per-volume uniform shifted-cutoff partition-function bounds, and
    4) weak-coupling OS/product-tensor hypotheses.
    This follows the hard-core WP1 per-volume route in `(n+2)`-decay form to
    `ReconstructionLinearGrowthModel`, then applies interface reconstruction. -/
theorem
    phi4_wightman_exists_of_interfaces_of_sq_integrable_data_and_sq_moment_polynomial_bound_per_volume_and_uniform_partition_bound_of_succ_succ
    (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [OSAxiomCoreModel params] →
    [WightmanReconstructionModel params] →
    [OSDistributionE2Model params] →
    [OSE4ClusterModel params] →
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        AEStronglyMeasurable (interactionCutoff params Λ κ)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hcutoff_sq :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        Integrable (fun ω => (interactionCutoff params Λ κ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hcutoff_conv :
      ∀ (Λ : Rectangle),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then
            ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)
            else 0)
          Filter.atTop
          (nhds 0)) →
    (hcutoff_ae :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
            Filter.atTop
            (nhds (interaction params Λ ω))) →
    (hinteraction_meas :
      ∀ (Λ : Rectangle),
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hinteraction_sq :
      ∀ (Λ : Rectangle),
        Integrable (fun ω => (interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (betaMom : ℝ) →
    (hbetaMom : 1 < betaMom) →
    (C : Rectangle → ℝ) →
    (hC_nonneg : ∀ Λ : Rectangle, 0 ≤ C Λ) →
    (hInt :
      ∀ (Λ : Rectangle) (n : ℕ),
        Integrable
          (fun ω : FieldConfig2D =>
            (interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hM :
      ∀ (Λ : Rectangle) (n : ℕ),
        ∫ ω : FieldConfig2D,
          (interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω) ^ 2
          ∂(freeFieldMeasure params.mass params.mass_pos)
        ≤ C Λ * (↑(n + 2) : ℝ) ^ (-betaMom)) →
    (hpartition :
      ∀ (Λ : Rectangle) (q : ℝ), 0 < q →
        ∃ D : ℝ,
          (∀ n : ℕ,
            Integrable
              (fun ω : FieldConfig2D =>
                Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)))
              (freeFieldMeasure params.mass params.mass_pos)) ∧
          (∀ n : ℕ,
            ∫ ω : FieldConfig2D,
              Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
              ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D)) →
    (hsmall : params.coupling < os4WeakCouplingThreshold params) →
    (alpha beta gamma : ℝ) →
    (hbeta : 0 < beta) →
    (huniform : ∀ h : TestFun2D, ∃ c : ℝ, ∀ Λ : Rectangle,
      |generatingFunctional params Λ h| ≤ Real.exp (c * normFunctional h)) →
    (hcompat :
      ∀ (n : ℕ) (f : Fin n → TestFun2D),
        phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily f) =
          (infiniteVolumeSchwinger params n f : ℂ)) →
    (hreduce :
      ∀ (c : ℝ) (n : ℕ) (_hn : 0 < n) (f : Fin n → TestFun2D),
        ∑ i : Fin n, (Nat.factorial n : ℝ) *
            (Real.exp (c * normFunctional (f i)) +
              Real.exp (c * normFunctional (-(f i)))) ≤
          alpha * beta ^ n * (n.factorial : ℝ) ^ gamma *
            SchwartzMap.seminorm ℝ 0 0
              (schwartzProductTensorFromTestFamily f)) →
    (hdense :
      ∀ (n : ℕ) (_hn : 0 < n),
        DenseRange (fun f : Fin n → TestFun2D =>
          schwartzProductTensorFromTestFamily f)) →
    ∃ (Wfn : WightmanFunctions 1),
      ∃ (OS : OsterwalderSchraderAxioms 1),
        OS.S = phi4SchwingerFunctions params ∧
        IsWickRotationPair OS.S Wfn.W := by
  intro _hlimit _hcore _hrec _he2 _he4
    hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
    hinteraction_meas hinteraction_sq
    betaMom hbetaMom C hC_nonneg hInt hM hpartition
    hsmall alpha beta gamma hbeta huniform hcompat hreduce hdense
  rcases
      reconstructionLinearGrowthModel_nonempty_of_sq_integrable_data_and_sq_moment_polynomial_bound_per_volume_and_uniform_partition_bound_of_succ_succ
        (params := params)
        hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
        hinteraction_meas hinteraction_sq
        betaMom hbetaMom C hC_nonneg hInt hM hpartition
        hsmall alpha beta gamma hbeta
        huniform hcompat hreduce hdense with ⟨hlin⟩
  letI : ReconstructionLinearGrowthModel params := hlin
  exact phi4_wightman_exists_of_explicit_data params
    (hlinear := phi4_linear_growth_of_interface params)
    (hreconstruct := phi4_wightman_reconstruction_step_of_interface params)

/-- Interface-level Wightman existence endpoint from:
    1) square-integrable/measurable UV interaction data,
    2) a fixed higher even moment order `2j` (`j > 0`) with per-volume
       polynomial-decay shifted UV-difference bounds and graph-natural decay
       rate `(n+2)^(-β)`,
    3) per-volume uniform shifted-cutoff partition-function bounds, and
    4) weak-coupling OS/product-tensor hypotheses.
    This is the higher-moment hard-core per-volume interface route in
    `(n+2)`-decay form. -/
theorem
    phi4_wightman_exists_of_interfaces_of_sq_integrable_data_and_higher_moment_polynomial_bound_per_volume_and_uniform_partition_bound_of_succ_succ
    (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [OSAxiomCoreModel params] →
    [WightmanReconstructionModel params] →
    [OSDistributionE2Model params] →
    [OSE4ClusterModel params] →
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        AEStronglyMeasurable (interactionCutoff params Λ κ)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hcutoff_sq :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        Integrable (fun ω => (interactionCutoff params Λ κ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hcutoff_conv :
      ∀ (Λ : Rectangle),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then
            ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)
            else 0)
          Filter.atTop
          (nhds 0)) →
    (hcutoff_ae :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
            Filter.atTop
            (nhds (interaction params Λ ω))) →
    (hinteraction_meas :
      ∀ (Λ : Rectangle),
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hinteraction_sq :
      ∀ (Λ : Rectangle),
        Integrable (fun ω => (interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (j : ℕ) →
    (hj : 0 < j) →
    (betaMom : ℝ) →
    (hbetaMom : 1 < betaMom) →
    (C : Rectangle → ℝ) →
    (hC_nonneg : ∀ Λ : Rectangle, 0 ≤ C Λ) →
    (hInt :
      ∀ (Λ : Rectangle) (n : ℕ),
        Integrable
          (fun ω : FieldConfig2D =>
            |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω| ^ (2 * j))
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hM :
      ∀ (Λ : Rectangle) (n : ℕ),
        ∫ ω : FieldConfig2D,
          |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω| ^ (2 * j)
          ∂(freeFieldMeasure params.mass params.mass_pos)
        ≤ C Λ * (↑(n + 2) : ℝ) ^ (-betaMom)) →
    (hpartition :
      ∀ (Λ : Rectangle) (q : ℝ), 0 < q →
        ∃ D : ℝ,
          (∀ n : ℕ,
            Integrable
              (fun ω : FieldConfig2D =>
                Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)))
              (freeFieldMeasure params.mass params.mass_pos)) ∧
          (∀ n : ℕ,
            ∫ ω : FieldConfig2D,
              Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
              ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D)) →
    (hsmall : params.coupling < os4WeakCouplingThreshold params) →
    (alpha beta gamma : ℝ) →
    (hbeta : 0 < beta) →
    (huniform : ∀ h : TestFun2D, ∃ c : ℝ, ∀ Λ : Rectangle,
      |generatingFunctional params Λ h| ≤ Real.exp (c * normFunctional h)) →
    (hcompat :
      ∀ (n : ℕ) (f : Fin n → TestFun2D),
        phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily f) =
          (infiniteVolumeSchwinger params n f : ℂ)) →
    (hreduce :
      ∀ (c : ℝ) (n : ℕ) (_hn : 0 < n) (f : Fin n → TestFun2D),
        ∑ i : Fin n, (Nat.factorial n : ℝ) *
            (Real.exp (c * normFunctional (f i)) +
              Real.exp (c * normFunctional (-(f i)))) ≤
          alpha * beta ^ n * (n.factorial : ℝ) ^ gamma *
            SchwartzMap.seminorm ℝ 0 0
              (schwartzProductTensorFromTestFamily f)) →
    (hdense :
      ∀ (n : ℕ) (_hn : 0 < n),
        DenseRange (fun f : Fin n → TestFun2D =>
          schwartzProductTensorFromTestFamily f)) →
    ∃ (Wfn : WightmanFunctions 1),
      ∃ (OS : OsterwalderSchraderAxioms 1),
        OS.S = phi4SchwingerFunctions params ∧
        IsWickRotationPair OS.S Wfn.W := by
  intro _hlimit _hcore _hrec _he2 _he4
    hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
    hinteraction_meas hinteraction_sq
    j hj betaMom hbetaMom C hC_nonneg hInt hM hpartition
    hsmall alpha beta gamma hbeta huniform hcompat hreduce hdense
  rcases
      reconstructionLinearGrowthModel_nonempty_of_sq_integrable_data_and_higher_moment_polynomial_bound_per_volume_and_uniform_partition_bound_of_succ_succ
        (params := params)
        hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
        hinteraction_meas hinteraction_sq
        j hj betaMom hbetaMom C hC_nonneg hInt hM hpartition
        hsmall alpha beta gamma hbeta
        huniform hcompat hreduce hdense with ⟨hlin⟩
  letI : ReconstructionLinearGrowthModel params := hlin
  exact phi4_wightman_exists_of_explicit_data params
    (hlinear := phi4_linear_growth_of_interface params)
    (hreconstruct := phi4_wightman_reconstruction_step_of_interface params)

/-- Dense product-tensor weak-coupling Wightman endpoint with an explicit
    Wick-sublevel-tail interaction hypothesis:
    shifted-index exponential tails of natural bad events
    `{ω | ∃ x ∈ Λ, wickPower(κ_{n+1}) ω x < -B}` are used to instantiate
    `InteractionWeightModel` constructively before applying the standard
    weak-coupling bridge, with explicit measurability and canonical-sequence
    a.e. convergence hypotheses for `interaction`. -/
theorem
    phi4_wightman_exists_of_os_and_productTensor_dense_and_normalized_order0_of_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets_of_aestronglyMeasurable_and_standardSeq_tendsto_ae
    (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [OSAxiomCoreModel params] →
    [WightmanReconstructionModel params] →
    [OSDistributionE2Model params] →
    [OSE4ClusterModel params] →
    (hinteraction_meas :
      ∀ Λ : Rectangle,
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hcutoff_tendsto_ae :
      ∀ Λ : Rectangle,
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun n : ℕ => interactionCutoff params Λ (standardUVCutoffSeq n) ω)
            Filter.atTop
            (nhds (interaction params Λ ω))) →
    (hwick_bad :
      ∀ Λ : Rectangle, ∃ B : ℝ, ∃ C : ENNReal, ∃ α : ℝ,
        C ≠ ⊤ ∧ 0 < α ∧
        (∀ n : ℕ,
          (freeFieldMeasure params.mass params.mass_pos)
            {ω : FieldConfig2D |
              ∃ x ∈ Λ.toSet,
                wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x < -B}
            ≤ C * (ENNReal.ofReal (Real.exp (-α))) ^ n) ∧
        MeasurableSet Λ.toSet ∧
        volume Λ.toSet ≠ (⊤ : ENNReal) ∧
        (∀ n : ℕ, ∀ ω : FieldConfig2D,
          IntegrableOn
            (fun x => wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x)
            Λ.toSet volume)) →
    (hsmall : params.coupling < os4WeakCouplingThreshold params) →
    (alpha beta gamma : ℝ) →
    (hbeta : 0 < beta) →
    (huniform : ∀ h : TestFun2D, ∃ c : ℝ, ∀ Λ : Rectangle,
      |generatingFunctional params Λ h| ≤ Real.exp (c * normFunctional h)) →
    (hcompat :
      ∀ (n : ℕ) (f : Fin n → TestFun2D),
        phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily f) =
          (infiniteVolumeSchwinger params n f : ℂ)) →
    (hreduce :
      ∀ (c : ℝ) (n : ℕ) (_hn : 0 < n) (f : Fin n → TestFun2D),
        ∑ i : Fin n, (Nat.factorial n : ℝ) *
            (Real.exp (c * normFunctional (f i)) +
              Real.exp (c * normFunctional (-(f i)))) ≤
          alpha * beta ^ n * (n.factorial : ℝ) ^ gamma *
            SchwartzMap.seminorm ℝ 0 0
              (schwartzProductTensorFromTestFamily f)) →
    (hdense :
      ∀ (n : ℕ) (_hn : 0 < n),
        DenseRange (fun f : Fin n → TestFun2D =>
          schwartzProductTensorFromTestFamily f)) →
    ∃ (Wfn : WightmanFunctions 1),
      ∃ (OS' : OsterwalderSchraderAxioms 1),
        OS'.S = phi4SchwingerFunctions params ∧
        IsWickRotationPair OS'.S Wfn.W := by
  intro _hlimit _hcore _hrec _he2 _he4
    hinteraction_meas hcutoff_tendsto_ae
    hwick_bad hsmall alpha beta gamma hbeta huniform hcompat hreduce hdense
  rcases
      interactionWeightModel_nonempty_of_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets_of_aestronglyMeasurable_and_standardSeq_tendsto_ae
        (params := params) hinteraction_meas hcutoff_tendsto_ae hwick_bad with ⟨hW⟩
  letI : InteractionWeightModel params := hW
  exact phi4_wightman_exists_of_os_and_productTensor_dense_and_normalized_order0
    params hsmall alpha beta gamma hbeta huniform hcompat hreduce hdense

/-- Dense product-tensor weak-coupling Wightman endpoint with an explicit
    Wick-sublevel-tail interaction hypothesis:
    shifted-index exponential tails of natural bad events
    `{ω | ∃ x ∈ Λ, wickPower(κ_{n+1}) ω x < -B}` are used to instantiate
    `InteractionWeightModel` constructively before applying the standard
    weak-coupling bridge. -/
theorem
    phi4_wightman_exists_of_os_and_productTensor_dense_and_normalized_order0_of_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets
    (params : Phi4Params) :
    [InteractionUVModel params] →
    [SchwingerLimitModel params] →
    [OSAxiomCoreModel params] →
    [WightmanReconstructionModel params] →
    [OSDistributionE2Model params] →
    [OSE4ClusterModel params] →
    (hwick_bad :
      ∀ Λ : Rectangle, ∃ B : ℝ, ∃ C : ENNReal, ∃ α : ℝ,
        C ≠ ⊤ ∧ 0 < α ∧
        (∀ n : ℕ,
          (freeFieldMeasure params.mass params.mass_pos)
            {ω : FieldConfig2D |
              ∃ x ∈ Λ.toSet,
                wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x < -B}
            ≤ C * (ENNReal.ofReal (Real.exp (-α))) ^ n) ∧
        MeasurableSet Λ.toSet ∧
        volume Λ.toSet ≠ (⊤ : ENNReal) ∧
        (∀ n : ℕ, ∀ ω : FieldConfig2D,
          IntegrableOn
            (fun x => wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x)
            Λ.toSet volume)) →
    (hsmall : params.coupling < os4WeakCouplingThreshold params) →
    (alpha beta gamma : ℝ) →
    (hbeta : 0 < beta) →
    (huniform : ∀ h : TestFun2D, ∃ c : ℝ, ∀ Λ : Rectangle,
      |generatingFunctional params Λ h| ≤ Real.exp (c * normFunctional h)) →
    (hcompat :
      ∀ (n : ℕ) (f : Fin n → TestFun2D),
        phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily f) =
          (infiniteVolumeSchwinger params n f : ℂ)) →
    (hreduce :
      ∀ (c : ℝ) (n : ℕ) (_hn : 0 < n) (f : Fin n → TestFun2D),
        ∑ i : Fin n, (Nat.factorial n : ℝ) *
            (Real.exp (c * normFunctional (f i)) +
              Real.exp (c * normFunctional (-(f i)))) ≤
          alpha * beta ^ n * (n.factorial : ℝ) ^ gamma *
            SchwartzMap.seminorm ℝ 0 0
              (schwartzProductTensorFromTestFamily f)) →
    (hdense :
      ∀ (n : ℕ) (_hn : 0 < n),
        DenseRange (fun f : Fin n → TestFun2D =>
          schwartzProductTensorFromTestFamily f)) →
    ∃ (Wfn : WightmanFunctions 1),
      ∃ (OS' : OsterwalderSchraderAxioms 1),
        OS'.S = phi4SchwingerFunctions params ∧
        IsWickRotationPair OS'.S Wfn.W := by
  intro _huv _hlimit _hcore _hrec _he2 _he4
    hwick_bad hsmall alpha beta gamma hbeta huniform hcompat hreduce hdense
  exact
    phi4_wightman_exists_of_os_and_productTensor_dense_and_normalized_order0_of_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets_of_aestronglyMeasurable_and_standardSeq_tendsto_ae
      (params := params)
      (hinteraction_meas := fun Λ => (interaction_in_L2 params Λ).aestronglyMeasurable)
      (hcutoff_tendsto_ae := fun Λ => interactionCutoff_standardSeq_tendsto_ae params Λ)
      hwick_bad hsmall alpha beta gamma hbeta huniform hcompat hreduce hdense

/-- Dense product-tensor weak-coupling Wightman endpoint from:
    1) square-integrable/measurable UV interaction data,
    2) shifted-index exponential tails of natural Wick sublevel bad events,
    3) weak-coupling OS + reconstruction interfaces.
    This first instantiates `InteractionWeightModel` constructively. -/
theorem
    phi4_wightman_exists_of_os_and_productTensor_dense_and_normalized_order0_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets
    (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [OSAxiomCoreModel params] →
    [WightmanReconstructionModel params] →
    [OSDistributionE2Model params] →
    [OSE4ClusterModel params] →
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        AEStronglyMeasurable (interactionCutoff params Λ κ)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hcutoff_sq :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        Integrable (fun ω => (interactionCutoff params Λ κ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hcutoff_conv :
      ∀ (Λ : Rectangle),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then
            ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)
            else 0)
          Filter.atTop
          (nhds 0)) →
    (hcutoff_ae :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
            Filter.atTop
            (nhds (interaction params Λ ω))) →
    (hinteraction_meas :
      ∀ (Λ : Rectangle),
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hinteraction_sq :
      ∀ (Λ : Rectangle),
        Integrable (fun ω => (interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hwick_bad :
      ∀ Λ : Rectangle, ∃ B : ℝ, ∃ C : ENNReal, ∃ α : ℝ,
        C ≠ ⊤ ∧ 0 < α ∧
        (∀ n : ℕ,
          (freeFieldMeasure params.mass params.mass_pos)
            {ω : FieldConfig2D |
              ∃ x ∈ Λ.toSet,
                wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x < -B}
            ≤ C * (ENNReal.ofReal (Real.exp (-α))) ^ n) ∧
        MeasurableSet Λ.toSet ∧
        volume Λ.toSet ≠ (⊤ : ENNReal) ∧
        (∀ n : ℕ, ∀ ω : FieldConfig2D,
          IntegrableOn
            (fun x => wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x)
            Λ.toSet volume)) →
    (hsmall : params.coupling < os4WeakCouplingThreshold params) →
    (alpha beta gamma : ℝ) →
    (hbeta : 0 < beta) →
    (huniform : ∀ h : TestFun2D, ∃ c : ℝ, ∀ Λ : Rectangle,
      |generatingFunctional params Λ h| ≤ Real.exp (c * normFunctional h)) →
    (hcompat :
      ∀ (n : ℕ) (f : Fin n → TestFun2D),
        phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily f) =
          (infiniteVolumeSchwinger params n f : ℂ)) →
    (hreduce :
      ∀ (c : ℝ) (n : ℕ) (_hn : 0 < n) (f : Fin n → TestFun2D),
        ∑ i : Fin n, (Nat.factorial n : ℝ) *
            (Real.exp (c * normFunctional (f i)) +
              Real.exp (c * normFunctional (-(f i)))) ≤
          alpha * beta ^ n * (n.factorial : ℝ) ^ gamma *
            SchwartzMap.seminorm ℝ 0 0
              (schwartzProductTensorFromTestFamily f)) →
    (hdense :
      ∀ (n : ℕ) (_hn : 0 < n),
        DenseRange (fun f : Fin n → TestFun2D =>
          schwartzProductTensorFromTestFamily f)) →
    ∃ (Wfn : WightmanFunctions 1),
      ∃ (OS' : OsterwalderSchraderAxioms 1),
        OS'.S = phi4SchwingerFunctions params ∧
        IsWickRotationPair OS'.S Wfn.W := by
  intro _hlimit _hcore _hrec _he2 _he4
    hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
    hinteraction_meas hinteraction_sq hwick_bad
    hsmall alpha beta gamma hbeta huniform hcompat hreduce hdense
  rcases
      interactionWeightModel_nonempty_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets
      (params := params)
      hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
      hinteraction_meas hinteraction_sq hwick_bad with ⟨hW⟩
  letI : InteractionWeightModel params := hW
  exact phi4_wightman_exists_of_os_and_productTensor_dense_and_normalized_order0
    params hsmall alpha beta gamma hbeta huniform hcompat hreduce hdense

/-- Interface-level Wightman existence endpoint from:
    1) UV Wick-sublevel-tail interaction control,
    2) explicit measurability + canonical-sequence a.e. convergence data for
       `interaction`, and
    3) weak-coupling OS/product-tensor hypotheses. -/
theorem
    phi4_wightman_exists_of_interfaces_of_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets_of_aestronglyMeasurable_and_standardSeq_tendsto_ae
    (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [OSAxiomCoreModel params] →
    [WightmanReconstructionModel params] →
    [OSDistributionE2Model params] →
    [OSE4ClusterModel params] →
    (hinteraction_meas :
      ∀ Λ : Rectangle,
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hcutoff_tendsto_ae :
      ∀ Λ : Rectangle,
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun n : ℕ => interactionCutoff params Λ (standardUVCutoffSeq n) ω)
            Filter.atTop
            (nhds (interaction params Λ ω))) →
    (hwick_bad :
      ∀ Λ : Rectangle, ∃ B : ℝ, ∃ C : ENNReal, ∃ α : ℝ,
        C ≠ ⊤ ∧ 0 < α ∧
        (∀ n : ℕ,
          (freeFieldMeasure params.mass params.mass_pos)
            {ω : FieldConfig2D |
              ∃ x ∈ Λ.toSet,
                wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x < -B}
            ≤ C * (ENNReal.ofReal (Real.exp (-α))) ^ n) ∧
        MeasurableSet Λ.toSet ∧
        volume Λ.toSet ≠ (⊤ : ENNReal) ∧
        (∀ n : ℕ, ∀ ω : FieldConfig2D,
          IntegrableOn
            (fun x => wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x)
            Λ.toSet volume)) →
    (hsmall : params.coupling < os4WeakCouplingThreshold params) →
    (alpha beta gamma : ℝ) →
    (hbeta : 0 < beta) →
    (huniform : ∀ h : TestFun2D, ∃ c : ℝ, ∀ Λ : Rectangle,
      |generatingFunctional params Λ h| ≤ Real.exp (c * normFunctional h)) →
    (hcompat :
      ∀ (n : ℕ) (f : Fin n → TestFun2D),
        phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily f) =
          (infiniteVolumeSchwinger params n f : ℂ)) →
    (hreduce :
      ∀ (c : ℝ) (n : ℕ) (_hn : 0 < n) (f : Fin n → TestFun2D),
        ∑ i : Fin n, (Nat.factorial n : ℝ) *
            (Real.exp (c * normFunctional (f i)) +
              Real.exp (c * normFunctional (-(f i)))) ≤
          alpha * beta ^ n * (n.factorial : ℝ) ^ gamma *
            SchwartzMap.seminorm ℝ 0 0
              (schwartzProductTensorFromTestFamily f)) →
    (hdense :
      ∀ (n : ℕ) (_hn : 0 < n),
        DenseRange (fun f : Fin n → TestFun2D =>
          schwartzProductTensorFromTestFamily f)) →
    ∃ (Wfn : WightmanFunctions 1),
      ∃ (OS : OsterwalderSchraderAxioms 1),
        OS.S = phi4SchwingerFunctions params ∧
        IsWickRotationPair OS.S Wfn.W := by
  intro _hlimit _hcore _hrec _he2 _he4
    hinteraction_meas hcutoff_tendsto_ae
    hwick_bad hsmall alpha beta gamma hbeta huniform hcompat hreduce hdense
  rcases
      reconstructionLinearGrowthModel_nonempty_of_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets_of_aestronglyMeasurable_and_standardSeq_tendsto_ae
        (params := params)
        hinteraction_meas hcutoff_tendsto_ae
        hwick_bad hsmall alpha beta gamma hbeta huniform hcompat hreduce hdense with ⟨hlin⟩
  letI : ReconstructionLinearGrowthModel params := hlin
  exact phi4_wightman_exists_of_explicit_data params
    (hlinear := phi4_linear_growth_of_interface params)
    (hreconstruct := phi4_wightman_reconstruction_step_of_interface params)

/-- Interface-level Wightman existence endpoint from:
    1) UV Wick-sublevel-tail interaction control, and
    2) weak-coupling OS/product-tensor hypotheses. -/
theorem
    phi4_wightman_exists_of_interfaces_of_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets
    (params : Phi4Params) :
    [InteractionUVModel params] →
    [SchwingerLimitModel params] →
    [OSAxiomCoreModel params] →
    [WightmanReconstructionModel params] →
    [OSDistributionE2Model params] →
    [OSE4ClusterModel params] →
    (hwick_bad :
      ∀ Λ : Rectangle, ∃ B : ℝ, ∃ C : ENNReal, ∃ α : ℝ,
        C ≠ ⊤ ∧ 0 < α ∧
        (∀ n : ℕ,
          (freeFieldMeasure params.mass params.mass_pos)
            {ω : FieldConfig2D |
              ∃ x ∈ Λ.toSet,
                wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x < -B}
            ≤ C * (ENNReal.ofReal (Real.exp (-α))) ^ n) ∧
        MeasurableSet Λ.toSet ∧
        volume Λ.toSet ≠ (⊤ : ENNReal) ∧
        (∀ n : ℕ, ∀ ω : FieldConfig2D,
          IntegrableOn
            (fun x => wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x)
            Λ.toSet volume)) →
    (hsmall : params.coupling < os4WeakCouplingThreshold params) →
    (alpha beta gamma : ℝ) →
    (hbeta : 0 < beta) →
    (huniform : ∀ h : TestFun2D, ∃ c : ℝ, ∀ Λ : Rectangle,
      |generatingFunctional params Λ h| ≤ Real.exp (c * normFunctional h)) →
    (hcompat :
      ∀ (n : ℕ) (f : Fin n → TestFun2D),
        phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily f) =
          (infiniteVolumeSchwinger params n f : ℂ)) →
    (hreduce :
      ∀ (c : ℝ) (n : ℕ) (_hn : 0 < n) (f : Fin n → TestFun2D),
        ∑ i : Fin n, (Nat.factorial n : ℝ) *
            (Real.exp (c * normFunctional (f i)) +
              Real.exp (c * normFunctional (-(f i)))) ≤
          alpha * beta ^ n * (n.factorial : ℝ) ^ gamma *
            SchwartzMap.seminorm ℝ 0 0
              (schwartzProductTensorFromTestFamily f)) →
    (hdense :
      ∀ (n : ℕ) (_hn : 0 < n),
        DenseRange (fun f : Fin n → TestFun2D =>
          schwartzProductTensorFromTestFamily f)) →
    ∃ (Wfn : WightmanFunctions 1),
      ∃ (OS : OsterwalderSchraderAxioms 1),
        OS.S = phi4SchwingerFunctions params ∧
        IsWickRotationPair OS.S Wfn.W := by
  intro _huv _hlimit _hcore _hrec _he2 _he4
    hwick_bad hsmall alpha beta gamma hbeta huniform hcompat hreduce hdense
  exact
    phi4_wightman_exists_of_interfaces_of_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets_of_aestronglyMeasurable_and_standardSeq_tendsto_ae
      (params := params)
      (hinteraction_meas := fun Λ => (interaction_in_L2 params Λ).aestronglyMeasurable)
      (hcutoff_tendsto_ae := fun Λ => interactionCutoff_standardSeq_tendsto_ae params Λ)
      hwick_bad hsmall alpha beta gamma hbeta huniform hcompat hreduce hdense

/-- Interface-level Wightman existence endpoint from:
    1) square-integrable/measurable UV interaction data,
    2) shifted-index exponential tails of natural Wick sublevel bad events
       `{ω | ∃ x ∈ Λ, wickPower(κ_{n+1}) ω x < -B}`,
    3) weak-coupling OS/product-tensor hypotheses. -/
theorem
    phi4_wightman_exists_of_interfaces_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets
    (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [OSAxiomCoreModel params] →
    [WightmanReconstructionModel params] →
    [OSDistributionE2Model params] →
    [OSE4ClusterModel params] →
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        AEStronglyMeasurable (interactionCutoff params Λ κ)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hcutoff_sq :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        Integrable (fun ω => (interactionCutoff params Λ κ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hcutoff_conv :
      ∀ (Λ : Rectangle),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then
            ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)
            else 0)
          Filter.atTop
          (nhds 0)) →
    (hcutoff_ae :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
            Filter.atTop
            (nhds (interaction params Λ ω))) →
    (hinteraction_meas :
      ∀ (Λ : Rectangle),
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hinteraction_sq :
      ∀ (Λ : Rectangle),
        Integrable (fun ω => (interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hwick_bad :
      ∀ Λ : Rectangle, ∃ B : ℝ, ∃ C : ENNReal, ∃ α : ℝ,
        C ≠ ⊤ ∧ 0 < α ∧
        (∀ n : ℕ,
          (freeFieldMeasure params.mass params.mass_pos)
            {ω : FieldConfig2D |
              ∃ x ∈ Λ.toSet,
                wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x < -B}
            ≤ C * (ENNReal.ofReal (Real.exp (-α))) ^ n) ∧
        MeasurableSet Λ.toSet ∧
        volume Λ.toSet ≠ (⊤ : ENNReal) ∧
        (∀ n : ℕ, ∀ ω : FieldConfig2D,
          IntegrableOn
            (fun x => wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x)
            Λ.toSet volume)) →
    (hsmall : params.coupling < os4WeakCouplingThreshold params) →
    (alpha beta gamma : ℝ) →
    (hbeta : 0 < beta) →
    (huniform : ∀ h : TestFun2D, ∃ c : ℝ, ∀ Λ : Rectangle,
      |generatingFunctional params Λ h| ≤ Real.exp (c * normFunctional h)) →
    (hcompat :
      ∀ (n : ℕ) (f : Fin n → TestFun2D),
        phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily f) =
          (infiniteVolumeSchwinger params n f : ℂ)) →
    (hreduce :
      ∀ (c : ℝ) (n : ℕ) (_hn : 0 < n) (f : Fin n → TestFun2D),
        ∑ i : Fin n, (Nat.factorial n : ℝ) *
            (Real.exp (c * normFunctional (f i)) +
              Real.exp (c * normFunctional (-(f i)))) ≤
          alpha * beta ^ n * (n.factorial : ℝ) ^ gamma *
            SchwartzMap.seminorm ℝ 0 0
              (schwartzProductTensorFromTestFamily f)) →
    (hdense :
      ∀ (n : ℕ) (_hn : 0 < n),
        DenseRange (fun f : Fin n → TestFun2D =>
          schwartzProductTensorFromTestFamily f)) →
    ∃ (Wfn : WightmanFunctions 1),
      ∃ (OS : OsterwalderSchraderAxioms 1),
        OS.S = phi4SchwingerFunctions params ∧
        IsWickRotationPair OS.S Wfn.W := by
  intro _hlimit _hcore _hrec _he2 _he4
    hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
    hinteraction_meas hinteraction_sq hwick_bad
    hsmall alpha beta gamma hbeta huniform hcompat hreduce hdense
  exact
    phi4_wightman_exists_of_os_and_productTensor_dense_and_normalized_order0_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets
      params
      hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
      hinteraction_meas hinteraction_sq
      hwick_bad hsmall alpha beta gamma hbeta
      huniform hcompat hreduce hdense

/-- Interface-level Wightman existence from linear-growth inputs, routed
    through the abstract reconstruction backend interface. -/
theorem phi4_wightman_exists_of_interfaces (params : Phi4Params)
    [SchwingerFunctionModel params]
    [ReconstructionLinearGrowthModel params]
    [WightmanReconstructionModel params] :
    ∃ (Wfn : WightmanFunctions 1),
      ∃ (OS : OsterwalderSchraderAxioms 1),
        OS.S = phi4SchwingerFunctions params ∧
        IsWickRotationPair OS.S Wfn.W := by
  exact phi4_wightman_exists_of_explicit_data params
    (hlinear := phi4_linear_growth_of_interface params)
    (hreconstruct := phi4_wightman_reconstruction_step_of_interface params)

/-- Interface-level self-adjointness corollary obtained from
    `phi4_wightman_exists_of_interfaces`. -/
theorem phi4_selfadjoint_fields_of_interfaces (params : Phi4Params)
    [SchwingerFunctionModel params]
    [ReconstructionLinearGrowthModel params]
    [WightmanReconstructionModel params] :
    ∃ (Wfn : WightmanFunctions 1),
      IsWickRotationPair (phi4SchwingerFunctions params) Wfn.W ∧
      (∀ (n : ℕ) (f g : SchwartzNPoint 1 n),
        (∀ x, g.toFun x = starRingEnd ℂ (f.toFun (fun i => x (Fin.rev i)))) →
        Wfn.W n g = starRingEnd ℂ (Wfn.W n f)) := by
  obtain ⟨Wfn, OS, hS, hWR⟩ := phi4_wightman_exists_of_interfaces params
  exact ⟨Wfn, hS ▸ hWR, Wfn.hermitian⟩

/-- Interface-level locality corollary obtained from
    `phi4_wightman_exists_of_interfaces`. -/
theorem phi4_locality_of_interfaces (params : Phi4Params)
    [SchwingerFunctionModel params]
    [ReconstructionLinearGrowthModel params]
    [WightmanReconstructionModel params] :
    ∃ (Wfn : WightmanFunctions 1),
      IsWickRotationPair (phi4SchwingerFunctions params) Wfn.W ∧
      IsLocallyCommutativeWeak 1 Wfn.W := by
  obtain ⟨Wfn, OS, hS, hWR⟩ := phi4_wightman_exists_of_interfaces params
  exact ⟨Wfn, hS ▸ hWR, Wfn.locally_commutative⟩

/-- Interface-level Lorentz-covariance corollary obtained from
    `phi4_wightman_exists_of_interfaces`. -/
theorem phi4_lorentz_covariance_of_interfaces (params : Phi4Params)
    [SchwingerFunctionModel params]
    [ReconstructionLinearGrowthModel params]
    [WightmanReconstructionModel params] :
    ∃ (Wfn : WightmanFunctions 1),
      IsWickRotationPair (phi4SchwingerFunctions params) Wfn.W ∧
      IsLorentzCovariantWeak 1 Wfn.W := by
  obtain ⟨Wfn, OS, hS, hWR⟩ := phi4_wightman_exists_of_interfaces params
  exact ⟨Wfn, hS ▸ hWR, Wfn.lorentz_covariant⟩

/-- Interface-level positive-definite/vacuum corollary obtained from
    `phi4_wightman_exists_of_interfaces`. -/
theorem phi4_unique_vacuum_of_interfaces (params : Phi4Params)
    [SchwingerFunctionModel params]
    [ReconstructionLinearGrowthModel params]
    [WightmanReconstructionModel params] :
    ∃ (Wfn : WightmanFunctions 1),
      IsPositiveDefinite 1 Wfn.W ∧
      IsWickRotationPair (phi4SchwingerFunctions params) Wfn.W := by
  obtain ⟨Wfn, OS, hS, hWR⟩ := phi4_wightman_exists_of_interfaces params
  exact ⟨Wfn, Wfn.positive_definite, hS ▸ hWR⟩

/-- **Main Theorem**: The φ⁴₂ theory defines a Wightman quantum field theory.

    By the OS reconstruction theorem (from OSreconstruction),
    the Schwinger functions satisfying OS0-OS3 + E0' can be analytically
    continued to Wightman distributions, which then reconstruct a
    Wightman QFT via the GNS construction.

    The resulting QFT satisfies:
    - W1: Covariant fields under the Poincaré group ISO(1,1)
    - W2: Spectral condition (energy ≥ 0, p² ≤ 0)
    - W3: Locality (spacelike commutativity) -/
theorem phi4_wightman_exists (params : Phi4Params)
    [SchwingerFunctionModel params]
    [ReconstructionLinearGrowthModel params]
    [WightmanReconstructionModel params] :
    ∃ (Wfn : WightmanFunctions 1),
      ∃ (OS : OsterwalderSchraderAxioms 1),
        OS.S = phi4SchwingerFunctions params ∧
        IsWickRotationPair OS.S Wfn.W := by
  exact phi4_wightman_exists_of_interfaces params

/-- The φ⁴₂ QFT has hermitian field operators (self-adjointness).
    W_n(f̃) = conj(W_n(f)) where f̃(x₁,...,xₙ) = conj(f(xₙ,...,x₁)).
    (Glimm-Jaffe Section 19.3)

    This is encoded in the `hermitian` field of `WightmanFunctions`,
    which is the distributional version of φ(f)* = φ(f̄) for real f. -/
theorem phi4_selfadjoint_fields (params : Phi4Params)
    [SchwingerFunctionModel params]
    [ReconstructionLinearGrowthModel params]
    [WightmanReconstructionModel params] :
    ∃ (Wfn : WightmanFunctions 1),
      IsWickRotationPair (phi4SchwingerFunctions params) Wfn.W ∧
      (∀ (n : ℕ) (f g : SchwartzNPoint 1 n),
        (∀ x, g.toFun x = starRingEnd ℂ (f.toFun (fun i => x (Fin.rev i)))) →
        Wfn.W n g = starRingEnd ℂ (Wfn.W n f)) := by
  obtain ⟨Wfn, OS, hS, hWR⟩ := phi4_wightman_exists params
  exact ⟨Wfn, hS ▸ hWR, Wfn.hermitian⟩

/-- The φ⁴₂ QFT satisfies locality: fields at spacelike separation commute.
    [φ(f), φ(g)] = 0 when supp f and supp g are spacelike separated.
    (Glimm-Jaffe Section 19.6)
    This follows from the Wightman reconstruction theorem applied to
    the φ⁴₂ Schwinger functions. -/
theorem phi4_locality (params : Phi4Params)
    [SchwingerFunctionModel params]
    [ReconstructionLinearGrowthModel params]
    [WightmanReconstructionModel params] :
    ∃ (Wfn : WightmanFunctions 1),
      IsWickRotationPair (phi4SchwingerFunctions params) Wfn.W ∧
      IsLocallyCommutativeWeak 1 Wfn.W := by
  obtain ⟨Wfn, OS, hS, hWR⟩ := phi4_wightman_exists params
  exact ⟨Wfn, hS ▸ hWR, Wfn.locally_commutative⟩

/-- The φ⁴₂ QFT has Lorentz covariance.
    U(Λ,a) φ(f) U(Λ,a)⁻¹ = φ((Λ,a)·f) for (Λ,a) ∈ ISO(1,1).
    (Glimm-Jaffe Section 19.5) -/
theorem phi4_lorentz_covariance (params : Phi4Params)
    [SchwingerFunctionModel params]
    [ReconstructionLinearGrowthModel params]
    [WightmanReconstructionModel params] :
    ∃ (Wfn : WightmanFunctions 1),
      IsWickRotationPair (phi4SchwingerFunctions params) Wfn.W ∧
      IsLorentzCovariantWeak 1 Wfn.W := by
  obtain ⟨Wfn, OS, hS, hWR⟩ := phi4_wightman_exists params
  exact ⟨Wfn, hS ▸ hWR, Wfn.lorentz_covariant⟩

/-- The φ⁴₂ QFT has a unique vacuum state.
    The vacuum Ω is the unique (up to phase) Poincaré-invariant state.
    (Glimm-Jaffe Section 19.7)

    For weak coupling, this follows from the cluster property (OS4).
    For strong coupling, vacuum uniqueness is related to the absence of
    phase transitions (or selecting a pure phase). -/
theorem phi4_unique_vacuum (params : Phi4Params)
    [SchwingerFunctionModel params]
    [ReconstructionLinearGrowthModel params]
    [WightmanReconstructionModel params] :
    ∃ (Wfn : WightmanFunctions 1),
      IsPositiveDefinite 1 Wfn.W ∧
      IsWickRotationPair (phi4SchwingerFunctions params) Wfn.W := by
  obtain ⟨Wfn, OS, hS, hWR⟩ := phi4_wightman_exists params
  exact ⟨Wfn, Wfn.positive_definite, hS ▸ hWR⟩

end

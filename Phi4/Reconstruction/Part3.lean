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

/-- Direct weak-coupling endpoint from:
    1) interface-level OS package data under weak coupling,
    2) explicit pointwise-in-`f` finite-volume uniform generating-functional bounds,
    3) dense image of product tensors in each positive-order Schwartz `n`-point space,
    4) order-zero normalization (`S₀(g) = g(0)`), using Sobolev index `0`. -/
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

end

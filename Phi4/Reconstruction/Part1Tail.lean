/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.Reconstruction.Part1Core

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

/-- Construct `ReconstructionLinearGrowthModel` from:
    1) square-integrable/measurable UV interaction data,
    2) per-volume geometric shifted-cutoff exponential moments at `q` with
       linear-threshold ratio control `exp(q * a) * r < 1`,
    3) per-volume geometric shifted-cutoff exponential moments at doubled
       parameter `2q`,
    4) weak-coupling OS + product-tensor linear-growth reduction hypotheses.

    The doubled-parameter data is converted internally to the square-data
    decomposition inputs required by the hard-core ENNReal bad-tail route. -/
theorem
    reconstructionLinearGrowthModel_nonempty_of_sq_integrable_data_and_linear_threshold_geometric_exp_moment_and_double_exp_moment_geometric
    (params : Phi4Params)
    [SchwingerLimitModel params]
    [OSAxiomCoreModel params]
    [OSDistributionE2Model params]
    [OSE4ClusterModel params]
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        AEStronglyMeasurable (interactionCutoff params Λ κ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_sq :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        Integrable (fun ω => (interactionCutoff params Λ κ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_conv :
      ∀ (Λ : Rectangle),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then
            ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)
            else 0)
          Filter.atTop
          (nhds 0))
    (hcutoff_ae :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
            Filter.atTop
            (nhds (interaction params Λ ω)))
    (hinteraction_meas :
      ∀ (Λ : Rectangle),
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hinteraction_sq :
      ∀ (Λ : Rectangle),
        Integrable (fun ω => (interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
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
            ≤ D2 * r2 ^ n))
    (hsmall : params.coupling < os4WeakCouplingThreshold params)
    (alpha beta gamma : ℝ)
    (hbeta : 0 < beta)
    (huniform : ∀ h : TestFun2D, ∃ c : ℝ, ∀ Λ : Rectangle,
      |generatingFunctional params Λ h| ≤ Real.exp (c * normFunctional h))
    (hcompat :
      ∀ (n : ℕ) (f : Fin n → TestFun2D),
        phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily f) =
          (infiniteVolumeSchwinger params n f : ℂ))
    (hreduce :
      ∀ (c : ℝ) (n : ℕ) (_hn : 0 < n) (f : Fin n → TestFun2D),
        ∑ i : Fin n, (Nat.factorial n : ℝ) *
            (Real.exp (c * normFunctional (f i)) +
              Real.exp (c * normFunctional (-(f i)))) ≤
          alpha * beta ^ n * (n.factorial : ℝ) ^ gamma *
            SchwartzMap.seminorm ℝ 0 0
              (schwartzProductTensorFromTestFamily f))
    (hdense :
      ∀ (n : ℕ) (_hn : 0 < n),
        DenseRange (fun f : Fin n → TestFun2D =>
          schwartzProductTensorFromTestFamily f)) :
    Nonempty (ReconstructionLinearGrowthModel params) := by
  rcases
      interactionIntegrabilityModel_nonempty_of_sq_integrable_data_and_linear_threshold_geometric_exp_moment_and_double_exp_moment_geometric
        (params := params)
        hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
        hinteraction_meas hinteraction_sq hcore with ⟨hIntModel⟩
  letI : InteractionIntegrabilityModel params := hIntModel
  exact reconstructionLinearGrowthModel_nonempty_of_data params
    (hlinear :=
      gap_phi4_linear_growth params hsmall alpha beta gamma hbeta
        huniform hcompat hreduce hdense)

/-- Public linear-growth endpoint from `ReconstructionLinearGrowthModel`. -/
theorem phi4_linear_growth (params : Phi4Params)
    [SchwingerFunctionModel params]
    [ReconstructionLinearGrowthModel params] :
    ∃ OS : OsterwalderSchraderAxioms 1,
      OS.S = phi4SchwingerFunctions params ∧
      Nonempty (OSLinearGrowthCondition 1 OS) := by
  exact ReconstructionLinearGrowthModel.phi4_linear_growth (params := params)

/-- Construct `WightmanReconstructionModel` from an explicit reconstruction rule. -/
theorem wightmanReconstructionModel_nonempty_of_data (params : Phi4Params)
    (hreconstruct :
      ∀ (OS : OsterwalderSchraderAxioms 1),
        OSLinearGrowthCondition 1 OS →
          ∃ (Wfn : WightmanFunctions 1),
            IsWickRotationPair OS.S Wfn.W) :
    Nonempty (WightmanReconstructionModel params) := by
  exact ⟨{ wightman_reconstruction := hreconstruct }⟩

/-- Honest frontier: reconstruction step from OS+linear-growth data via the
    abstract reconstruction backend interface.
    Assumptions are stated explicitly (no interface-class smuggling). -/
theorem gap_phi4_wightman_reconstruction_step (_params : Phi4Params)
    (hreconstruct :
      ∀ (OS : OsterwalderSchraderAxioms 1),
        OSLinearGrowthCondition 1 OS →
          ∃ (Wfn : WightmanFunctions 1),
            IsWickRotationPair OS.S Wfn.W) :
    ∀ (OS : OsterwalderSchraderAxioms 1),
      OSLinearGrowthCondition 1 OS →
        ∃ (Wfn : WightmanFunctions 1),
          IsWickRotationPair OS.S Wfn.W := by
  exact hreconstruct

/-- Public reconstruction step from OS + linear growth to Wightman data,
    routed through `WightmanReconstructionModel`. -/
theorem phi4_wightman_reconstruction_step (params : Phi4Params)
    [WightmanReconstructionModel params] :
    ∀ (OS : OsterwalderSchraderAxioms 1),
      OSLinearGrowthCondition 1 OS →
        ∃ (Wfn : WightmanFunctions 1),
          IsWickRotationPair OS.S Wfn.W := by
  exact phi4_wightman_reconstruction_step_of_interface params

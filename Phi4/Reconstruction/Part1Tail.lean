/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.Reconstruction.Part1Core

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

/-- Construct `ReconstructionLinearGrowthModel` from:
    1) UV interaction control plus shifted-cutoff geometric exponential-moment
       decay (used to instantiate `InteractionWeightModel` constructively),
    2) weak-coupling OS interfaces, and
    3) explicit product-tensor linear-growth reduction hypotheses. -/

theorem reconstructionLinearGrowthModel_nonempty_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
    (params : Phi4Params)
    [InteractionUVModel params]
    [SchwingerLimitModel params]
    [OSAxiomCoreModel params]
    [OSDistributionE2Model params]
    [OSE4ClusterModel params]
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
            ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D * r ^ n))
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
  exact reconstructionLinearGrowthModel_nonempty_of_data params
    (hlinear :=
      gap_phi4_linear_growth_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
        params hmom hsmall alpha beta gamma hbeta huniform hcompat hreduce hdense)

/-- Construct `ReconstructionLinearGrowthModel` from:
    1) square-integrable/measurable UV interaction data,
    2) shifted-cutoff geometric exponential-moment decay, and
    3) weak-coupling OS + product-tensor linear-growth reduction hypotheses.
    This uses the direct square-data linear-growth frontier bridge. -/
theorem
    reconstructionLinearGrowthModel_nonempty_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
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
            ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D * r ^ n))
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
  exact reconstructionLinearGrowthModel_nonempty_of_data params
    (hlinear :=
      gap_phi4_linear_growth_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
        params
        hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
        hinteraction_meas hinteraction_sq
        hmom hsmall alpha beta gamma hbeta
        huniform hcompat hreduce hdense)

/-- Construct `ReconstructionLinearGrowthModel` from:
    1) square-integrable/measurable UV interaction data,
    2) per-volume polynomial-decay squared-moment bounds for shifted UV
       differences,
    3) per-volume uniform shifted-cutoff partition-function bounds, and
    4) weak-coupling OS + product-tensor linear-growth reduction hypotheses.
    This is the hard-core WP1 route through
    `InteractionIntegrabilityModel`. -/
theorem
    reconstructionLinearGrowthModel_nonempty_of_sq_integrable_data_and_sq_moment_polynomial_bound_per_volume_and_uniform_partition_bound
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
    (betaMom : ℝ) (hbetaMom : 1 < betaMom)
    (C : Rectangle → ℝ)
    (hC_nonneg : ∀ Λ : Rectangle, 0 ≤ C Λ)
    (hInt :
      ∀ (Λ : Rectangle) (n : ℕ),
        Integrable
          (fun ω : FieldConfig2D =>
            (interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hM :
      ∀ (Λ : Rectangle) (n : ℕ),
        ∫ ω : FieldConfig2D,
          (interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω) ^ 2
          ∂(freeFieldMeasure params.mass params.mass_pos)
        ≤ C Λ * (↑(n + 1) : ℝ) ^ (-betaMom))
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
              ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D))
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
      interactionIntegrabilityModel_nonempty_of_sq_integrable_data_and_sq_moment_polynomial_bound_per_volume_and_uniform_partition_bound
        (params := params)
        hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
        hinteraction_meas hinteraction_sq
        betaMom hbetaMom C hC_nonneg hInt hM hpartition with ⟨hIntModel⟩
  letI : InteractionIntegrabilityModel params := hIntModel
  exact reconstructionLinearGrowthModel_nonempty_of_data params
    (hlinear :=
      gap_phi4_linear_growth params hsmall alpha beta gamma hbeta
        huniform hcompat hreduce hdense)

/-- Construct `ReconstructionLinearGrowthModel` from:
    1) square-integrable/measurable UV interaction data,
    2) explicit cutoff a.e. convergence,
    3) per-volume bad-set decomposition data (linear lower bounds off bad sets,
       geometric second moments, ENNReal geometric bad-set tails), and
    4) weak-coupling OS + product-tensor linear-growth reduction hypotheses.

    This is the ENNReal-tail bad-set hard-core WP1 route to reconstruction
    linear growth. -/
theorem
    reconstructionLinearGrowthModel_nonempty_of_sq_integrable_data_and_linear_lower_bound_off_bad_sets_and_sq_exp_moment_geometric_and_bad_measure_geometric_ennreal
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
                  (freeFieldMeasure params.mass params.mass_pos) (bad n) ≤ Cb * rb ^ n))
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
      interactionIntegrabilityModel_nonempty_of_sq_integrable_data_and_linear_lower_bound_off_bad_sets_and_sq_exp_moment_geometric_and_bad_measure_geometric_ennreal
        (params := params)
        hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
        hinteraction_meas hinteraction_sq hdecomp with ⟨hIntModel⟩
  letI : InteractionIntegrabilityModel params := hIntModel
  exact reconstructionLinearGrowthModel_nonempty_of_data params
    (hlinear :=
      gap_phi4_linear_growth params hsmall alpha beta gamma hbeta
        huniform hcompat hreduce hdense)

/-- Construct `ReconstructionLinearGrowthModel` from:
    1) square-integrable/measurable UV interaction data,
    2) per-volume geometric shifted-cutoff exponential moments with
       linear-threshold ratio control `exp(q * a) * r < 1`,
    3) geometric shifted-cutoff second moments for `exp(-q * interactionCutoff)`,
    4) weak-coupling OS + product-tensor linear-growth reduction hypotheses.

    This uses the canonical measurable bad-set construction from the
    linear-threshold Chernoff bridge, so no explicit `hdecomp` payload is
    required at this layer. -/
theorem
    reconstructionLinearGrowthModel_nonempty_of_sq_integrable_data_and_linear_threshold_geometric_exp_moment_and_sq_exp_moment_geometric
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
      interactionIntegrabilityModel_nonempty_of_sq_integrable_data_and_linear_threshold_geometric_exp_moment_and_sq_exp_moment_geometric
        (params := params)
        hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
        hinteraction_meas hinteraction_sq hcore with ⟨hIntModel⟩
  letI : InteractionIntegrabilityModel params := hIntModel
  exact reconstructionLinearGrowthModel_nonempty_of_data params
    (hlinear :=
      gap_phi4_linear_growth params hsmall alpha beta gamma hbeta
        huniform hcompat hreduce hdense)

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

/-- Same endpoint as
    `reconstructionLinearGrowthModel_nonempty_of_sq_integrable_data_and_linear_threshold_geometric_exp_moment_and_double_exp_moment_geometric`,
    with weaker core assumptions: no separate `q`-level integrability
    hypothesis is required. -/
theorem
    reconstructionLinearGrowthModel_nonempty_of_sq_integrable_data_and_linear_threshold_geometric_exp_moment_and_double_exp_moment_geometric_of_moment_bounds
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
      interactionIntegrabilityModel_nonempty_of_sq_integrable_data_and_linear_threshold_geometric_exp_moment_and_double_exp_moment_geometric_of_moment_bounds
        (params := params)
        hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
        hinteraction_meas hinteraction_sq hcore with ⟨hIntModel⟩
  letI : InteractionIntegrabilityModel params := hIntModel
  exact reconstructionLinearGrowthModel_nonempty_of_data params
    (hlinear :=
      gap_phi4_linear_growth params hsmall alpha beta gamma hbeta
        huniform hcompat hreduce hdense)

/-- Construct `ReconstructionLinearGrowthModel` from:
    1) square-integrable/measurable UV interaction data,
    2) a fixed higher even moment order `2j` (`j > 0`) with per-volume
       polynomial-decay shifted UV-difference bounds,
    3) per-volume uniform shifted-cutoff partition-function bounds, and
    4) weak-coupling OS + product-tensor linear-growth reduction hypotheses.
    This generalizes the hard-core WP1 route beyond the squared-moment case. -/
theorem
    reconstructionLinearGrowthModel_nonempty_of_sq_integrable_data_and_higher_moment_polynomial_bound_per_volume_and_uniform_partition_bound
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
    (j : ℕ) (hj : 0 < j)
    (betaMom : ℝ) (hbetaMom : 1 < betaMom)
    (C : Rectangle → ℝ)
    (hC_nonneg : ∀ Λ : Rectangle, 0 ≤ C Λ)
    (hInt :
      ∀ (Λ : Rectangle) (n : ℕ),
        Integrable
          (fun ω : FieldConfig2D =>
            |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω| ^ (2 * j))
          (freeFieldMeasure params.mass params.mass_pos))
    (hM :
      ∀ (Λ : Rectangle) (n : ℕ),
        ∫ ω : FieldConfig2D,
          |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω| ^ (2 * j)
          ∂(freeFieldMeasure params.mass params.mass_pos)
        ≤ C Λ * (↑(n + 1) : ℝ) ^ (-betaMom))
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
              ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D))
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
      interactionIntegrabilityModel_nonempty_of_sq_integrable_data_and_higher_moment_polynomial_bound_per_volume_and_uniform_partition_bound
        (params := params)
        hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
        hinteraction_meas hinteraction_sq
        j hj betaMom hbetaMom C hC_nonneg hInt hM hpartition with ⟨hIntModel⟩
  letI : InteractionIntegrabilityModel params := hIntModel
  exact reconstructionLinearGrowthModel_nonempty_of_data params
    (hlinear :=
      gap_phi4_linear_growth params hsmall alpha beta gamma hbeta
        huniform hcompat hreduce hdense)

/-- Construct `ReconstructionLinearGrowthModel` from:
    1) square-integrable/measurable UV interaction data,
    2) per-volume polynomial-decay squared-moment shifted UV-difference bounds
       on the graph-natural `(n+2)` index,
    3) per-volume uniform shifted-cutoff partition-function bounds,
    4) weak-coupling OS + product-tensor linear-growth reduction hypotheses.
    This is the hard-core WP1 route without index-shift conversion. -/
theorem
    reconstructionLinearGrowthModel_nonempty_of_sq_integrable_data_and_sq_moment_polynomial_bound_per_volume_and_uniform_partition_bound_of_succ_succ
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
    (betaMom : ℝ) (hbetaMom : 1 < betaMom)
    (C : Rectangle → ℝ)
    (hC_nonneg : ∀ Λ : Rectangle, 0 ≤ C Λ)
    (hInt :
      ∀ (Λ : Rectangle) (n : ℕ),
        Integrable
          (fun ω : FieldConfig2D =>
            (interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hM :
      ∀ (Λ : Rectangle) (n : ℕ),
        ∫ ω : FieldConfig2D,
          (interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω) ^ 2
          ∂(freeFieldMeasure params.mass params.mass_pos)
        ≤ C Λ * (↑(n + 2) : ℝ) ^ (-betaMom))
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
              ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D))
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
      interactionIntegrabilityModel_nonempty_of_sq_integrable_data_and_sq_moment_polynomial_bound_per_volume_and_uniform_partition_bound_of_succ_succ
        (params := params)
        hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
        hinteraction_meas hinteraction_sq
        betaMom hbetaMom C hC_nonneg hInt hM hpartition with ⟨hIntModel⟩
  letI : InteractionIntegrabilityModel params := hIntModel
  exact reconstructionLinearGrowthModel_nonempty_of_data params
    (hlinear :=
      gap_phi4_linear_growth params hsmall alpha beta gamma hbeta
        huniform hcompat hreduce hdense)

/-- Construct `ReconstructionLinearGrowthModel` from:
    1) square-integrable/measurable UV interaction data,
    2) a fixed higher even moment order `2j` (`j > 0`) with per-volume
       polynomial-decay shifted UV-difference bounds on the graph-natural
       `(n+2)` index,
    3) per-volume uniform shifted-cutoff partition-function bounds,
    4) weak-coupling OS + product-tensor linear-growth reduction hypotheses.
    This is the higher-moment hard-core WP1 route without index-shift
    conversion. -/
theorem
    reconstructionLinearGrowthModel_nonempty_of_sq_integrable_data_and_higher_moment_polynomial_bound_per_volume_and_uniform_partition_bound_of_succ_succ
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
    (j : ℕ) (hj : 0 < j)
    (betaMom : ℝ) (hbetaMom : 1 < betaMom)
    (C : Rectangle → ℝ)
    (hC_nonneg : ∀ Λ : Rectangle, 0 ≤ C Λ)
    (hInt :
      ∀ (Λ : Rectangle) (n : ℕ),
        Integrable
          (fun ω : FieldConfig2D =>
            |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω| ^ (2 * j))
          (freeFieldMeasure params.mass params.mass_pos))
    (hM :
      ∀ (Λ : Rectangle) (n : ℕ),
        ∫ ω : FieldConfig2D,
          |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω| ^ (2 * j)
          ∂(freeFieldMeasure params.mass params.mass_pos)
        ≤ C Λ * (↑(n + 2) : ℝ) ^ (-betaMom))
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
              ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D))
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
      interactionIntegrabilityModel_nonempty_of_sq_integrable_data_and_higher_moment_polynomial_bound_per_volume_and_uniform_partition_bound_of_succ_succ
        (params := params)
        hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
        hinteraction_meas hinteraction_sq
        j hj betaMom hbetaMom C hC_nonneg hInt hM hpartition with ⟨hIntModel⟩
  letI : InteractionIntegrabilityModel params := hIntModel
  exact reconstructionLinearGrowthModel_nonempty_of_data params
    (hlinear :=
      gap_phi4_linear_growth params hsmall alpha beta gamma hbeta
        huniform hcompat hreduce hdense)

/-- Construct `ReconstructionInputModel` from:
    1) weak-coupling decay infrastructure,
    2) UV Wick-sublevel-tail interaction control,
    3) explicit measurability + canonical-sequence a.e. convergence data for
       `interaction`, and
    4) explicit product-tensor reduction/approximation hypotheses. -/
theorem
    reconstructionInputModel_nonempty_of_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets_of_aestronglyMeasurable_and_standardSeq_tendsto_ae
    (params : Phi4Params)
    [SchwingerLimitModel params]
    [OSAxiomCoreModel params]
    [OSDistributionE2Model params]
    [OSE4ClusterModel params]
    [ReconstructionWeakCouplingModel params]
    (hinteraction_meas :
      ∀ Λ : Rectangle,
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_tendsto_ae :
      ∀ Λ : Rectangle,
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun n : ℕ => interactionCutoff params Λ (standardUVCutoffSeq n) ω)
            Filter.atTop
            (nhds (interaction params Λ ω)))
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
            Λ.toSet volume))
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
    Nonempty (ReconstructionInputModel params) := by
  rcases
      reconstructionLinearGrowthModel_nonempty_of_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets_of_aestronglyMeasurable_and_standardSeq_tendsto_ae
        (params := params)
        hinteraction_meas hcutoff_tendsto_ae
        hwick_bad hsmall alpha beta gamma hbeta huniform hcompat hreduce hdense with ⟨hlin⟩
  letI : ReconstructionLinearGrowthModel params := hlin
  exact ⟨inferInstance⟩

/-- Construct `ReconstructionInputModel` from:
    1) weak-coupling decay infrastructure,
    2) UV Wick-sublevel-tail interaction control, and
    3) explicit product-tensor reduction/approximation hypotheses. -/
theorem
    reconstructionInputModel_nonempty_of_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets
    (params : Phi4Params)
    [InteractionUVModel params]
    [SchwingerLimitModel params]
    [OSAxiomCoreModel params]
    [OSDistributionE2Model params]
    [OSE4ClusterModel params]
    [ReconstructionWeakCouplingModel params]
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
            Λ.toSet volume))
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
    Nonempty (ReconstructionInputModel params) := by
  exact
    reconstructionInputModel_nonempty_of_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets_of_aestronglyMeasurable_and_standardSeq_tendsto_ae
      (params := params)
      (hinteraction_meas := fun Λ => (interaction_in_L2 params Λ).aestronglyMeasurable)
      (hcutoff_tendsto_ae := fun Λ => interactionCutoff_standardSeq_tendsto_ae params Λ)
      hwick_bad hsmall alpha beta gamma hbeta huniform hcompat hreduce hdense

/-- Construct `ReconstructionInputModel` from:
    1) weak-coupling decay infrastructure (`ReconstructionWeakCouplingModel`),
    2) UV shifted-cutoff geometric moment decay (used to instantiate
       linear-growth reconstruction data constructively), and
    3) explicit product-tensor reduction/approximation hypotheses. -/
theorem reconstructionInputModel_nonempty_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
    (params : Phi4Params)
    [InteractionUVModel params]
    [SchwingerLimitModel params]
    [OSAxiomCoreModel params]
    [OSDistributionE2Model params]
    [OSE4ClusterModel params]
    [ReconstructionWeakCouplingModel params]
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
            ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D * r ^ n))
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
    Nonempty (ReconstructionInputModel params) := by
  rcases
      reconstructionLinearGrowthModel_nonempty_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
        (params := params) hmom hsmall alpha beta gamma hbeta
        huniform hcompat hreduce hdense with ⟨hlin⟩
  letI : ReconstructionLinearGrowthModel params := hlin
  exact ⟨inferInstance⟩

/-- Construct `ReconstructionInputModel` from:
    1) weak-coupling decay infrastructure,
    2) square-integrable/measurable UV interaction data,
    3) explicit cutoff a.e. convergence,
    4) per-volume bad-set decomposition data (linear lower bounds off bad sets,
       geometric second moments, ENNReal geometric bad-set tails), and
    5) explicit product-tensor reduction/approximation hypotheses. -/
theorem
    reconstructionInputModel_nonempty_of_sq_integrable_data_and_linear_lower_bound_off_bad_sets_and_sq_exp_moment_geometric_and_bad_measure_geometric_ennreal
    (params : Phi4Params)
    [SchwingerLimitModel params]
    [OSAxiomCoreModel params]
    [OSDistributionE2Model params]
    [OSE4ClusterModel params]
    [ReconstructionWeakCouplingModel params]
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
                  (freeFieldMeasure params.mass params.mass_pos) (bad n) ≤ Cb * rb ^ n))
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
    Nonempty (ReconstructionInputModel params) := by
  rcases
      reconstructionLinearGrowthModel_nonempty_of_sq_integrable_data_and_linear_lower_bound_off_bad_sets_and_sq_exp_moment_geometric_and_bad_measure_geometric_ennreal
        (params := params)
        hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
        hinteraction_meas hinteraction_sq hdecomp
        hsmall alpha beta gamma hbeta
        huniform hcompat hreduce hdense with ⟨hlin⟩
  letI : ReconstructionLinearGrowthModel params := hlin
  exact ⟨inferInstance⟩

/-- Construct `ReconstructionInputModel` from:
    1) weak-coupling decay infrastructure,
    2) square-integrable/measurable UV interaction data,
    3) shifted-cutoff geometric moment decay, and
    4) explicit product-tensor reduction/approximation hypotheses.
    This uses the direct square-data linear-growth constructor. -/
theorem
    reconstructionInputModel_nonempty_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
    (params : Phi4Params)
    [SchwingerLimitModel params]
    [OSAxiomCoreModel params]
    [OSDistributionE2Model params]
    [OSE4ClusterModel params]
    [ReconstructionWeakCouplingModel params]
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
            ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D * r ^ n))
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
    Nonempty (ReconstructionInputModel params) := by
  rcases
      reconstructionLinearGrowthModel_nonempty_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
        (params := params)
        hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
        hinteraction_meas hinteraction_sq
        hmom hsmall alpha beta gamma hbeta
        huniform hcompat hreduce hdense with ⟨hlin⟩
  letI : ReconstructionLinearGrowthModel params := hlin
  exact ⟨inferInstance⟩

/-- Construct `ReconstructionInputModel` from:
    1) weak-coupling decay infrastructure,
    2) square-integrable/measurable UV interaction data,
    3) per-volume polynomial-decay squared-moment shifted UV-difference bounds,
    4) per-volume uniform shifted-cutoff partition-function bounds, and
    5) explicit product-tensor reduction/approximation hypotheses. -/
theorem
    reconstructionInputModel_nonempty_of_sq_integrable_data_and_sq_moment_polynomial_bound_per_volume_and_uniform_partition_bound
    (params : Phi4Params)
    [SchwingerLimitModel params]
    [OSAxiomCoreModel params]
    [OSDistributionE2Model params]
    [OSE4ClusterModel params]
    [ReconstructionWeakCouplingModel params]
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
    (betaMom : ℝ) (hbetaMom : 1 < betaMom)
    (C : Rectangle → ℝ)
    (hC_nonneg : ∀ Λ : Rectangle, 0 ≤ C Λ)
    (hInt :
      ∀ (Λ : Rectangle) (n : ℕ),
        Integrable
          (fun ω : FieldConfig2D =>
            (interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hM :
      ∀ (Λ : Rectangle) (n : ℕ),
        ∫ ω : FieldConfig2D,
          (interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω) ^ 2
          ∂(freeFieldMeasure params.mass params.mass_pos)
        ≤ C Λ * (↑(n + 1) : ℝ) ^ (-betaMom))
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
              ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D))
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
    Nonempty (ReconstructionInputModel params) := by
  rcases
      reconstructionLinearGrowthModel_nonempty_of_sq_integrable_data_and_sq_moment_polynomial_bound_per_volume_and_uniform_partition_bound
        (params := params)
        hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
        hinteraction_meas hinteraction_sq
        betaMom hbetaMom C hC_nonneg hInt hM hpartition
        hsmall alpha beta gamma hbeta
        huniform hcompat hreduce hdense with ⟨hlin⟩
  letI : ReconstructionLinearGrowthModel params := hlin
  exact ⟨inferInstance⟩

/-- Construct `ReconstructionInputModel` from:
    1) weak-coupling decay infrastructure,
    2) square-integrable/measurable UV interaction data,
    3) a fixed higher even moment order `2j` (`j > 0`) with per-volume
       polynomial-decay shifted UV-difference bounds,
    4) per-volume uniform shifted-cutoff partition-function bounds, and
    5) explicit product-tensor reduction/approximation hypotheses. -/
theorem
    reconstructionInputModel_nonempty_of_sq_integrable_data_and_higher_moment_polynomial_bound_per_volume_and_uniform_partition_bound
    (params : Phi4Params)
    [SchwingerLimitModel params]
    [OSAxiomCoreModel params]
    [OSDistributionE2Model params]
    [OSE4ClusterModel params]
    [ReconstructionWeakCouplingModel params]
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
    (j : ℕ) (hj : 0 < j)
    (betaMom : ℝ) (hbetaMom : 1 < betaMom)
    (C : Rectangle → ℝ)
    (hC_nonneg : ∀ Λ : Rectangle, 0 ≤ C Λ)
    (hInt :
      ∀ (Λ : Rectangle) (n : ℕ),
        Integrable
          (fun ω : FieldConfig2D =>
            |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω| ^ (2 * j))
          (freeFieldMeasure params.mass params.mass_pos))
    (hM :
      ∀ (Λ : Rectangle) (n : ℕ),
        ∫ ω : FieldConfig2D,
          |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω| ^ (2 * j)
          ∂(freeFieldMeasure params.mass params.mass_pos)
        ≤ C Λ * (↑(n + 1) : ℝ) ^ (-betaMom))
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
              ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D))
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
    Nonempty (ReconstructionInputModel params) := by
  rcases
      reconstructionLinearGrowthModel_nonempty_of_sq_integrable_data_and_higher_moment_polynomial_bound_per_volume_and_uniform_partition_bound
        (params := params)
        hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
        hinteraction_meas hinteraction_sq
        j hj betaMom hbetaMom C hC_nonneg hInt hM hpartition
        hsmall alpha beta gamma hbeta
        huniform hcompat hreduce hdense with ⟨hlin⟩
  letI : ReconstructionLinearGrowthModel params := hlin
  exact ⟨inferInstance⟩

/-- Construct `ReconstructionInputModel` from:
    1) weak-coupling decay infrastructure,
    2) square-integrable/measurable UV interaction data,
    3) per-volume polynomial-decay squared-moment shifted UV-difference bounds
       on the graph-natural `(n+2)` index,
    4) per-volume uniform shifted-cutoff partition-function bounds,
    5) explicit product-tensor reduction/approximation hypotheses. -/
theorem
    reconstructionInputModel_nonempty_of_sq_integrable_data_and_sq_moment_polynomial_bound_per_volume_and_uniform_partition_bound_of_succ_succ
    (params : Phi4Params)
    [SchwingerLimitModel params]
    [OSAxiomCoreModel params]
    [OSDistributionE2Model params]
    [OSE4ClusterModel params]
    [ReconstructionWeakCouplingModel params]
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
    (betaMom : ℝ) (hbetaMom : 1 < betaMom)
    (C : Rectangle → ℝ)
    (hC_nonneg : ∀ Λ : Rectangle, 0 ≤ C Λ)
    (hInt :
      ∀ (Λ : Rectangle) (n : ℕ),
        Integrable
          (fun ω : FieldConfig2D =>
            (interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hM :
      ∀ (Λ : Rectangle) (n : ℕ),
        ∫ ω : FieldConfig2D,
          (interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω) ^ 2
          ∂(freeFieldMeasure params.mass params.mass_pos)
        ≤ C Λ * (↑(n + 2) : ℝ) ^ (-betaMom))
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
              ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D))
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
    Nonempty (ReconstructionInputModel params) := by
  rcases
      reconstructionLinearGrowthModel_nonempty_of_sq_integrable_data_and_sq_moment_polynomial_bound_per_volume_and_uniform_partition_bound_of_succ_succ
        (params := params)
        hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
        hinteraction_meas hinteraction_sq
        betaMom hbetaMom C hC_nonneg hInt hM hpartition
        hsmall alpha beta gamma hbeta
        huniform hcompat hreduce hdense with ⟨hlin⟩
  letI : ReconstructionLinearGrowthModel params := hlin
  exact ⟨inferInstance⟩

/-- Construct `ReconstructionInputModel` from:
    1) weak-coupling decay infrastructure,
    2) square-integrable/measurable UV interaction data,
    3) a fixed higher even moment order `2j` (`j > 0`) with per-volume
       polynomial-decay shifted UV-difference bounds on the graph-natural
       `(n+2)` index,
    4) per-volume uniform shifted-cutoff partition-function bounds,
    5) explicit product-tensor reduction/approximation hypotheses. -/
theorem
    reconstructionInputModel_nonempty_of_sq_integrable_data_and_higher_moment_polynomial_bound_per_volume_and_uniform_partition_bound_of_succ_succ
    (params : Phi4Params)
    [SchwingerLimitModel params]
    [OSAxiomCoreModel params]
    [OSDistributionE2Model params]
    [OSE4ClusterModel params]
    [ReconstructionWeakCouplingModel params]
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
    (j : ℕ) (hj : 0 < j)
    (betaMom : ℝ) (hbetaMom : 1 < betaMom)
    (C : Rectangle → ℝ)
    (hC_nonneg : ∀ Λ : Rectangle, 0 ≤ C Λ)
    (hInt :
      ∀ (Λ : Rectangle) (n : ℕ),
        Integrable
          (fun ω : FieldConfig2D =>
            |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω| ^ (2 * j))
          (freeFieldMeasure params.mass params.mass_pos))
    (hM :
      ∀ (Λ : Rectangle) (n : ℕ),
        ∫ ω : FieldConfig2D,
          |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω - interaction params Λ ω| ^ (2 * j)
          ∂(freeFieldMeasure params.mass params.mass_pos)
        ≤ C Λ * (↑(n + 2) : ℝ) ^ (-betaMom))
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
              ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D))
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
    Nonempty (ReconstructionInputModel params) := by
  rcases
      reconstructionLinearGrowthModel_nonempty_of_sq_integrable_data_and_higher_moment_polynomial_bound_per_volume_and_uniform_partition_bound_of_succ_succ
        (params := params)
        hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
        hinteraction_meas hinteraction_sq
        j hj betaMom hbetaMom C hC_nonneg hInt hM hpartition
        hsmall alpha beta gamma hbeta
        huniform hcompat hreduce hdense with ⟨hlin⟩
  letI : ReconstructionLinearGrowthModel params := hlin
  exact ⟨inferInstance⟩

/-- Linear-growth frontier with explicit Wick-sublevel-tail interaction input:
    shifted-index exponential tails of natural bad events
    `{ω | ∃ x ∈ Λ, wickPower(κ_{n+1}) ω x < -B}` are routed through the
    direct `InteractionWeightModel` bridge, then into `gap_phi4_linear_growth`,
    using explicit measurability and canonical-sequence a.e. convergence data. -/
theorem
    gap_phi4_linear_growth_of_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets_of_aestronglyMeasurable_and_standardSeq_tendsto_ae
    (params : Phi4Params)
    [SchwingerLimitModel params]
    [OSAxiomCoreModel params]
    [OSDistributionE2Model params]
    [OSE4ClusterModel params]
    (hinteraction_meas :
      ∀ Λ : Rectangle,
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_tendsto_ae :
      ∀ Λ : Rectangle,
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun n : ℕ => interactionCutoff params Λ (standardUVCutoffSeq n) ω)
            Filter.atTop
            (nhds (interaction params Λ ω)))
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
            Λ.toSet volume))
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
    ∃ OS : OsterwalderSchraderAxioms 1,
      OS.S = phi4SchwingerFunctions params ∧
      Nonempty (OSLinearGrowthCondition 1 OS) := by
  rcases
      interactionWeightModel_nonempty_of_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets_of_aestronglyMeasurable_and_standardSeq_tendsto_ae
      (params := params) hinteraction_meas hcutoff_tendsto_ae hwick_bad with ⟨hWinst⟩
  letI : InteractionWeightModel params := hWinst
  exact gap_phi4_linear_growth params hsmall alpha beta gamma hbeta
    huniform hcompat hreduce hdense

/-- Linear-growth frontier with explicit Wick-sublevel-tail interaction input:
    shifted-index exponential tails of natural bad events
    `{ω | ∃ x ∈ Λ, wickPower(κ_{n+1}) ω x < -B}` are routed through the
    direct `InteractionWeightModel` bridge, then into `gap_phi4_linear_growth`. -/
theorem
    gap_phi4_linear_growth_of_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets
    (params : Phi4Params)
    [InteractionUVModel params]
    [SchwingerLimitModel params]
    [OSAxiomCoreModel params]
    [OSDistributionE2Model params]
    [OSE4ClusterModel params]
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
            Λ.toSet volume))
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
    ∃ OS : OsterwalderSchraderAxioms 1,
      OS.S = phi4SchwingerFunctions params ∧
      Nonempty (OSLinearGrowthCondition 1 OS) := by
  exact
    gap_phi4_linear_growth_of_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets_of_aestronglyMeasurable_and_standardSeq_tendsto_ae
      (params := params)
      (hinteraction_meas := fun Λ => (interaction_in_L2 params Λ).aestronglyMeasurable)
      (hcutoff_tendsto_ae := fun Λ => interactionCutoff_standardSeq_tendsto_ae params Λ)
      hwick_bad hsmall alpha beta gamma hbeta huniform hcompat hreduce hdense

/-- Linear-growth frontier from:
    1) square-integrable/measurable UV interaction data,
    2) shifted-index exponential tails of natural Wick sublevel bad events
       `{ω | ∃ x ∈ Λ, wickPower(κ_{n+1}) ω x < -B}`,
    3) weak-coupling OS + product-tensor linear-growth reduction hypotheses.
    This routes the bad-set assumptions through the direct
    `InteractionWeightModel` bridge, then applies `gap_phi4_linear_growth`. -/
theorem
    gap_phi4_linear_growth_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets
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
            Λ.toSet volume))
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
    ∃ OS : OsterwalderSchraderAxioms 1,
      OS.S = phi4SchwingerFunctions params ∧
      Nonempty (OSLinearGrowthCondition 1 OS) := by
  rcases
      interactionWeightModel_nonempty_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets
      (params := params)
      hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
      hinteraction_meas hinteraction_sq hwick_bad with ⟨hW⟩
  letI : InteractionWeightModel params := hW
  exact gap_phi4_linear_growth params hsmall alpha beta gamma hbeta
    huniform hcompat hreduce hdense

/-- Construct `ReconstructionLinearGrowthModel` from:
    1) square-integrable/measurable UV interaction data,
    2) shifted-index exponential tails for natural Wick sublevel bad events,
    3) weak-coupling OS + product-tensor linear-growth reduction hypotheses.
    This first builds `InteractionWeightModel` constructively and then
    applies the linear-growth frontier above. -/
theorem
    reconstructionLinearGrowthModel_nonempty_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets
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
            Λ.toSet volume))
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
  exact reconstructionLinearGrowthModel_nonempty_of_data params
    (hlinear :=
      gap_phi4_linear_growth_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets
        (params := params)
        hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
        hinteraction_meas hinteraction_sq
        hwick_bad hsmall alpha beta gamma hbeta
        huniform hcompat hreduce hdense)

/-- Construct `ReconstructionInputModel` from:
    1) weak-coupling decay infrastructure,
    2) square-integrable/measurable UV interaction data,
    3) shifted-index exponential tails for natural Wick sublevel bad events,
    4) explicit product-tensor reduction/approximation hypotheses.
    This first builds `ReconstructionLinearGrowthModel` constructively. -/
theorem
    reconstructionInputModel_nonempty_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets
    (params : Phi4Params)
    [SchwingerLimitModel params]
    [OSAxiomCoreModel params]
    [OSDistributionE2Model params]
    [OSE4ClusterModel params]
    [ReconstructionWeakCouplingModel params]
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
            Λ.toSet volume))
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
    Nonempty (ReconstructionInputModel params) := by
  rcases
      reconstructionLinearGrowthModel_nonempty_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets
      (params := params)
      hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
      hinteraction_meas hinteraction_sq
      hwick_bad hsmall alpha beta gamma hbeta
      huniform hcompat hreduce hdense with ⟨hlin⟩
  letI : ReconstructionLinearGrowthModel params := hlin
  exact ⟨inferInstance⟩

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
    abstract reconstruction backend interface. -/
theorem gap_phi4_wightman_reconstruction_step (params : Phi4Params)
    [WightmanReconstructionModel params] :
    ∀ (OS : OsterwalderSchraderAxioms 1),
      OSLinearGrowthCondition 1 OS →
        ∃ (Wfn : WightmanFunctions 1),
          IsWickRotationPair OS.S Wfn.W := by
  exact phi4_wightman_reconstruction_step_of_interface params

/-- Public reconstruction step from OS + linear growth to Wightman data,
    routed through `WightmanReconstructionModel`. -/
theorem phi4_wightman_reconstruction_step (params : Phi4Params)
    [WightmanReconstructionModel params] :
    ∀ (OS : OsterwalderSchraderAxioms 1),
      OSLinearGrowthCondition 1 OS →
        ∃ (Wfn : WightmanFunctions 1),
          IsWickRotationPair OS.S Wfn.W := by
  exact phi4_wightman_reconstruction_step_of_interface params

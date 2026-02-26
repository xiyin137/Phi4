/- 
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.Reconstruction

/-!
# Phi4 Model Bundle

This file provides a single bundled assumption class collecting the current
`...Model` interfaces used across the project. It gives a convenient way to
activate all development interfaces with one instance argument.
-/

noncomputable section

open Reconstruction

/-- Bundled development assumptions for the φ⁴₂ pipeline at fixed parameters. -/
class Phi4ModelBundle (params : Phi4Params) where
  freeCovarianceKernel : FreeCovarianceKernelModel params.mass params.mass_pos
  boundaryKernel : BoundaryKernelModel params.mass params.mass_pos
  boundaryComparison : @BoundaryComparisonModel params.mass params.mass_pos boundaryKernel
  boundaryRegularity : @BoundaryRegularityModel params.mass params.mass_pos boundaryKernel
  interactionWeight : InteractionWeightModel params
  finiteVolumeComparison : FiniteVolumeComparisonModel params
  correlationTwoPoint : CorrelationTwoPointModel params
  correlationFourPoint : CorrelationFourPointModel params
  correlationFKG : CorrelationFKGModel params
  freeRP : FreeReflectionPositivityModel params.mass params.mass_pos
  dirichletRP : DirichletReflectionPositivityModel params.mass params.mass_pos
  interactingRP : InteractingReflectionPositivityModel params
  multipleReflection : MultipleReflectionModel params
  infiniteVolumeSchwinger : InfiniteVolumeSchwingerModel params
  infiniteVolumeMeasure : @InfiniteVolumeMeasureModel params infiniteVolumeSchwinger
  uniformWeakCoupling : @UniformWeakCouplingDecayModel params
    infiniteVolumeSchwinger
  wickPowers : @WickPowersModel params
    (@infiniteVolumeLimitModel_of_submodels params
      infiniteVolumeSchwinger infiniteVolumeMeasure)
  regularity : @RegularityModel params
    (@infiniteVolumeLimitModel_of_submodels params
      infiniteVolumeSchwinger infiniteVolumeMeasure)
  measureOS3 : @MeasureOS3Model params
    infiniteVolumeSchwinger infiniteVolumeMeasure
  osAxiom : OSAxiomCoreModel params
  osE4 : @OSE4ClusterModel params osAxiom
  osE2 : @OSDistributionE2Model params osAxiom
  reconstructionInput : @ReconstructionInputModel params
    infiniteVolumeSchwinger osAxiom
  wightmanReconstruction : @WightmanReconstructionModel params
    osAxiom

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    FreeCovarianceKernelModel params.mass params.mass_pos :=
  h.freeCovarianceKernel

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    BoundaryKernelModel params.mass params.mass_pos :=
  h.boundaryKernel

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    BoundaryComparisonModel params.mass params.mass_pos := by
  letI : BoundaryKernelModel params.mass params.mass_pos := h.boundaryKernel
  exact h.boundaryComparison

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    BoundaryRegularityModel params.mass params.mass_pos := by
  letI : BoundaryKernelModel params.mass params.mass_pos := h.boundaryKernel
  exact h.boundaryRegularity

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    InteractionWeightModel params :=
  h.interactionWeight

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    FiniteVolumeComparisonModel params :=
  h.finiteVolumeComparison

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    CorrelationTwoPointModel params :=
  h.correlationTwoPoint

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    CorrelationFourPointModel params :=
  h.correlationFourPoint

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    CorrelationFKGModel params :=
  h.correlationFKG

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    CorrelationInequalityModel params := by
  letI : CorrelationTwoPointModel params := h.correlationTwoPoint
  letI : CorrelationFourPointModel params := h.correlationFourPoint
  letI : CorrelationFKGModel params := h.correlationFKG
  infer_instance

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    FreeReflectionPositivityModel params.mass params.mass_pos :=
  h.freeRP

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    DirichletReflectionPositivityModel params.mass params.mass_pos :=
  h.dirichletRP

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    InteractingReflectionPositivityModel params :=
  h.interactingRP

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    MultipleReflectionModel params :=
  h.multipleReflection

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    InfiniteVolumeSchwingerModel params :=
  h.infiniteVolumeSchwinger

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    InfiniteVolumeMeasureModel params := by
  letI : InfiniteVolumeSchwingerModel params := h.infiniteVolumeSchwinger
  exact h.infiniteVolumeMeasure

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    InfiniteVolumeLimitModel params := by
  letI : InfiniteVolumeSchwingerModel params := h.infiniteVolumeSchwinger
  letI : InfiniteVolumeMeasureModel params := h.infiniteVolumeMeasure
  infer_instance

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    UniformWeakCouplingDecayModel params := by
  letI : InfiniteVolumeSchwingerModel params := h.infiniteVolumeSchwinger
  exact h.uniformWeakCoupling

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    WickPowersModel params := by
  letI : InfiniteVolumeSchwingerModel params := h.infiniteVolumeSchwinger
  letI : InfiniteVolumeMeasureModel params := h.infiniteVolumeMeasure
  letI : InfiniteVolumeLimitModel params := inferInstance
  exact h.wickPowers

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    RegularityModel params := by
  letI : InfiniteVolumeSchwingerModel params := h.infiniteVolumeSchwinger
  letI : InfiniteVolumeMeasureModel params := h.infiniteVolumeMeasure
  letI : InfiniteVolumeLimitModel params := inferInstance
  exact h.regularity

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    MeasureOS3Model params := by
  letI : InfiniteVolumeSchwingerModel params := h.infiniteVolumeSchwinger
  letI : InfiniteVolumeMeasureModel params := h.infiniteVolumeMeasure
  exact h.measureOS3

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    OSAxiomCoreModel params := by
  exact h.osAxiom

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    OSE4ClusterModel params := by
  letI : OSAxiomCoreModel params := h.osAxiom
  exact h.osE4

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    OSDistributionE2Model params := by
  letI : OSAxiomCoreModel params := h.osAxiom
  exact h.osE2

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    ReconstructionInputModel params := by
  letI : InfiniteVolumeSchwingerModel params := h.infiniteVolumeSchwinger
  letI : OSAxiomCoreModel params := h.osAxiom
  exact h.reconstructionInput

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    WightmanReconstructionModel params := by
  letI : InfiniteVolumeSchwingerModel params := h.infiniteVolumeSchwinger
  letI : OSAxiomCoreModel params := h.osAxiom
  exact h.wightmanReconstruction

/-- Convenience wrapper: a bundled model gives the Wightman reconstruction result. -/
theorem phi4_wightman_exists_of_bundle (params : Phi4Params)
    [Phi4ModelBundle params] :
    ∃ (Wfn : WightmanFunctions 1),
      ∃ (OS : OsterwalderSchraderAxioms 1),
        OS.S = phi4SchwingerFunctions params ∧
        IsWickRotationPair OS.S Wfn.W :=
  phi4_wightman_exists params

/-- Bundled wrapper for weak-coupling connected 2-point decay threshold existence. -/
theorem phi4_connectedTwoPoint_decay_threshold_of_bundle (params : Phi4Params)
    [Phi4ModelBundle params] :
    ConnectedTwoPointDecayThreshold params :=
  phi4_connectedTwoPoint_decay_threshold params

/-- Bundled wrapper: positivity of the selected weak-coupling threshold. -/
theorem phi4WeakCouplingThreshold_pos_of_bundle (params : Phi4Params)
    [Phi4ModelBundle params] :
    0 < phi4WeakCouplingThreshold params :=
  phi4WeakCouplingThreshold_pos params

/-- Bundled wrapper: connected 2-point exponential decay below the selected threshold. -/
theorem phi4_connectedTwoPoint_decay_below_threshold_of_bundle (params : Phi4Params)
    [Phi4ModelBundle params]
    (hsmall : params.coupling < phi4WeakCouplingThreshold params) :
    ConnectedTwoPointDecayAtParams params :=
  phi4_connectedTwoPoint_decay_below_threshold params hsmall

/-- Bundled wrapper: infinite-volume connected 2-point nonnegativity. -/
theorem phi4_connectedTwoPoint_nonneg_of_bundle (params : Phi4Params)
    [Phi4ModelBundle params] :
    ∀ (f g : TestFun2D), 0 ≤ connectedTwoPoint params f g :=
  phi4_connectedTwoPoint_nonneg params

/-- Bundled wrapper: infinite-volume diagonal connected 2-point nonnegativity. -/
theorem phi4_connectedTwoPoint_self_nonneg_of_bundle (params : Phi4Params)
    [Phi4ModelBundle params] :
    ∀ (f : TestFun2D), 0 ≤ connectedTwoPoint params f f :=
  phi4_connectedTwoPoint_self_nonneg params

/-- Bundled wrapper: infinite-volume connected 2-point Cauchy-Schwarz inequality. -/
theorem phi4_connectedTwoPoint_sq_le_mul_diag_of_bundle (params : Phi4Params)
    [Phi4ModelBundle params] :
    ∀ (f g : TestFun2D),
      (connectedTwoPoint params f g) ^ 2 ≤
        connectedTwoPoint params f f * connectedTwoPoint params g g :=
  phi4_connectedTwoPoint_sq_le_mul_diag params

/-- Bundled wrapper: infinite-volume connected 2-point geometric-mean bound. -/
theorem phi4_connectedTwoPoint_abs_le_sqrt_diag_mul_of_bundle (params : Phi4Params)
    [Phi4ModelBundle params] :
    ∀ (f g : TestFun2D),
      |connectedTwoPoint params f g| ≤
        Real.sqrt (connectedTwoPoint params f f * connectedTwoPoint params g g) :=
  phi4_connectedTwoPoint_abs_le_sqrt_diag_mul params

/-- Bundled wrapper: infinite-volume connected 2-point half-diagonal bound. -/
theorem phi4_connectedTwoPoint_abs_le_half_diag_sum_of_bundle (params : Phi4Params)
    [Phi4ModelBundle params] :
    ∀ (f g : TestFun2D),
      |connectedTwoPoint params f g| ≤
        (connectedTwoPoint params f f + connectedTwoPoint params g g) / 2 :=
  phi4_connectedTwoPoint_abs_le_half_diag_sum params

/-- Bundled wrapper: finite-family PSD for the infinite-volume connected 2-point kernel. -/
theorem phi4_connectedTwoPoint_quadratic_nonneg_of_bundle (params : Phi4Params)
    [Phi4ModelBundle params] :
    ∀ {ι : Type*} (s : Finset ι) (f : ι → TestFun2D) (c : ι → ℝ),
      0 ≤ Finset.sum s (fun i =>
        c i * Finset.sum s (fun j => c j * connectedTwoPoint params (f j) (f i))) :=
  phi4_connectedTwoPoint_quadratic_nonneg params

/-- Bundled wrapper: standard-index-order form of finite-family PSD. -/
theorem phi4_connectedTwoPoint_quadratic_nonneg_standard_of_bundle (params : Phi4Params)
    [Phi4ModelBundle params] :
    ∀ {ι : Type*} (s : Finset ι) (f : ι → TestFun2D) (c : ι → ℝ),
      0 ≤ Finset.sum s (fun i => Finset.sum s (fun j =>
        c i * c j * connectedTwoPoint params (f i) (f j))) :=
  phi4_connectedTwoPoint_quadratic_nonneg_standard params

/-- Bundled wrapper: infinite-volume 4-point cumulant nonpositivity. -/
theorem phi4_infiniteCumulantFourPoint_nonpos_of_bundle (params : Phi4Params)
    [Phi4ModelBundle params] :
    ∀ (f₁ f₂ f₃ f₄ : TestFun2D),
      (∀ x, 0 ≤ f₁ x) → (∀ x, 0 ≤ f₂ x) →
      (∀ x, 0 ≤ f₃ x) → (∀ x, 0 ≤ f₄ x) →
      infiniteCumulantFourPoint params f₁ f₂ f₃ f₄ ≤ 0 :=
  phi4_infiniteCumulantFourPoint_nonpos params

/-- Bundled wrapper: infinite-volume absolute bound for the fully connected
    4-point cumulant. -/
theorem phi4_infiniteCumulantFourPoint_abs_bound_of_bundle (params : Phi4Params)
    [Phi4ModelBundle params] :
    ∀ (f₁ f₂ f₃ f₄ : TestFun2D),
      (∀ x, 0 ≤ f₁ x) → (∀ x, 0 ≤ f₂ x) →
      (∀ x, 0 ≤ f₃ x) → (∀ x, 0 ≤ f₄ x) →
      |infiniteCumulantFourPoint params f₁ f₂ f₃ f₄| ≤
        infiniteVolumeSchwinger params 2 ![f₁, f₃] *
          infiniteVolumeSchwinger params 2 ![f₂, f₄] +
        infiniteVolumeSchwinger params 2 ![f₁, f₄] *
          infiniteVolumeSchwinger params 2 ![f₂, f₃] :=
  phi4_infiniteCumulantFourPoint_abs_bound params

/-- Bundled wrapper: channel-wise lower bounds for the infinite-volume
    fully connected 4-point cumulant. -/
theorem phi4_infiniteCumulantFourPoint_lower_bounds_all_channels_of_bundle
    (params : Phi4Params)
    [Phi4ModelBundle params] :
    ∀ (f₁ f₂ f₃ f₄ : TestFun2D),
      (∀ x, 0 ≤ f₁ x) → (∀ x, 0 ≤ f₂ x) →
      (∀ x, 0 ≤ f₃ x) → (∀ x, 0 ≤ f₄ x) →
      -(infiniteVolumeSchwinger params 2 ![f₁, f₃] *
        infiniteVolumeSchwinger params 2 ![f₂, f₄] +
        infiniteVolumeSchwinger params 2 ![f₁, f₄] *
        infiniteVolumeSchwinger params 2 ![f₂, f₃])
        ≤ infiniteCumulantFourPoint params f₁ f₂ f₃ f₄ ∧
      -(infiniteVolumeSchwinger params 2 ![f₁, f₂] *
        infiniteVolumeSchwinger params 2 ![f₃, f₄] +
        infiniteVolumeSchwinger params 2 ![f₁, f₄] *
        infiniteVolumeSchwinger params 2 ![f₂, f₃])
        ≤ infiniteCumulantFourPoint params f₁ f₂ f₃ f₄ ∧
      -(infiniteVolumeSchwinger params 2 ![f₁, f₂] *
        infiniteVolumeSchwinger params 2 ![f₃, f₄] +
        infiniteVolumeSchwinger params 2 ![f₁, f₃] *
        infiniteVolumeSchwinger params 2 ![f₂, f₄])
        ≤ infiniteCumulantFourPoint params f₁ f₂ f₃ f₄ :=
  phi4_infiniteCumulantFourPoint_lower_bounds_all_channels params

/-- Bundled wrapper: alternative infinite-volume cumulant absolute bound from
    the `(13)(24)` channel. -/
theorem phi4_infiniteCumulantFourPoint_abs_bound_alt13_of_bundle
    (params : Phi4Params)
    [Phi4ModelBundle params] :
    ∀ (f₁ f₂ f₃ f₄ : TestFun2D),
      (∀ x, 0 ≤ f₁ x) → (∀ x, 0 ≤ f₂ x) →
      (∀ x, 0 ≤ f₃ x) → (∀ x, 0 ≤ f₄ x) →
      |infiniteCumulantFourPoint params f₁ f₂ f₃ f₄| ≤
        infiniteVolumeSchwinger params 2 ![f₁, f₂] *
          infiniteVolumeSchwinger params 2 ![f₃, f₄] +
        infiniteVolumeSchwinger params 2 ![f₁, f₄] *
          infiniteVolumeSchwinger params 2 ![f₂, f₃] :=
  phi4_infiniteCumulantFourPoint_abs_bound_alt13 params

/-- Bundled wrapper: alternative infinite-volume cumulant absolute bound from
    the `(14)(23)` channel. -/
theorem phi4_infiniteCumulantFourPoint_abs_bound_alt14_of_bundle
    (params : Phi4Params)
    [Phi4ModelBundle params] :
    ∀ (f₁ f₂ f₃ f₄ : TestFun2D),
      (∀ x, 0 ≤ f₁ x) → (∀ x, 0 ≤ f₂ x) →
      (∀ x, 0 ≤ f₃ x) → (∀ x, 0 ≤ f₄ x) →
      |infiniteCumulantFourPoint params f₁ f₂ f₃ f₄| ≤
        infiniteVolumeSchwinger params 2 ![f₁, f₂] *
          infiniteVolumeSchwinger params 2 ![f₃, f₄] +
        infiniteVolumeSchwinger params 2 ![f₁, f₃] *
          infiniteVolumeSchwinger params 2 ![f₂, f₄] :=
  phi4_infiniteCumulantFourPoint_abs_bound_alt14 params

/-- Bundled wrapper: infinite-volume all-channel 4-point bounds. -/
theorem phi4_infiniteSchwinger_four_bounds_all_channels_of_bundle
    (params : Phi4Params)
    [Phi4ModelBundle params] :
    ∀ (f₁ f₂ f₃ f₄ : TestFun2D),
      (∀ x, 0 ≤ f₁ x) → (∀ x, 0 ≤ f₂ x) →
      (∀ x, 0 ≤ f₃ x) → (∀ x, 0 ≤ f₄ x) →
      max (infiniteVolumeSchwinger params 2 ![f₁, f₂] *
        infiniteVolumeSchwinger params 2 ![f₃, f₄])
        (max (infiniteVolumeSchwinger params 2 ![f₁, f₃] *
          infiniteVolumeSchwinger params 2 ![f₂, f₄])
          (infiniteVolumeSchwinger params 2 ![f₁, f₄] *
            infiniteVolumeSchwinger params 2 ![f₂, f₃]))
        ≤ infiniteVolumeSchwinger params 4 ![f₁, f₂, f₃, f₄] ∧
      infiniteVolumeSchwinger params 4 ![f₁, f₂, f₃, f₄] ≤
        infiniteVolumeSchwinger params 2 ![f₁, f₂] *
          infiniteVolumeSchwinger params 2 ![f₃, f₄] +
        infiniteVolumeSchwinger params 2 ![f₁, f₃] *
          infiniteVolumeSchwinger params 2 ![f₂, f₄] +
        infiniteVolumeSchwinger params 2 ![f₁, f₄] *
          infiniteVolumeSchwinger params 2 ![f₂, f₃] :=
  phi4_infiniteSchwinger_four_bounds_all_channels params

/-- Bundled wrapper: nonnegativity of infinite-volume `(12)(34)` pairing-subtracted
    4-point channel. -/
theorem phi4_infiniteTruncatedFourPoint12_nonneg_of_bundle
    (params : Phi4Params)
    [Phi4ModelBundle params] :
    ∀ (f₁ f₂ f₃ f₄ : TestFun2D),
      (∀ x, 0 ≤ f₁ x) → (∀ x, 0 ≤ f₂ x) →
      (∀ x, 0 ≤ f₃ x) → (∀ x, 0 ≤ f₄ x) →
      0 ≤ infiniteTruncatedFourPoint12 params f₁ f₂ f₃ f₄ :=
  phi4_infiniteTruncatedFourPoint12_nonneg params

/-- Bundled wrapper: nonnegativity of infinite-volume `(13)(24)` pairing-subtracted
    4-point channel. -/
theorem phi4_infiniteTruncatedFourPoint13_nonneg_of_bundle
    (params : Phi4Params)
    [Phi4ModelBundle params] :
    ∀ (f₁ f₂ f₃ f₄ : TestFun2D),
      (∀ x, 0 ≤ f₁ x) → (∀ x, 0 ≤ f₂ x) →
      (∀ x, 0 ≤ f₃ x) → (∀ x, 0 ≤ f₄ x) →
      0 ≤ infiniteTruncatedFourPoint13 params f₁ f₂ f₃ f₄ :=
  phi4_infiniteTruncatedFourPoint13_nonneg params

/-- Bundled wrapper: nonnegativity of infinite-volume `(14)(23)` pairing-subtracted
    4-point channel. -/
theorem phi4_infiniteTruncatedFourPoint14_nonneg_of_bundle
    (params : Phi4Params)
    [Phi4ModelBundle params] :
    ∀ (f₁ f₂ f₃ f₄ : TestFun2D),
      (∀ x, 0 ≤ f₁ x) → (∀ x, 0 ≤ f₂ x) →
      (∀ x, 0 ≤ f₃ x) → (∀ x, 0 ≤ f₄ x) →
      0 ≤ infiniteTruncatedFourPoint14 params f₁ f₂ f₃ f₄ :=
  phi4_infiniteTruncatedFourPoint14_nonneg params

/-- Bundled wrapper: upper bound for infinite-volume `(12)(34)` pairing-subtracted
    4-point channel. -/
theorem phi4_infiniteTruncatedFourPoint12_upper_of_bundle
    (params : Phi4Params)
    [Phi4ModelBundle params] :
    ∀ (f₁ f₂ f₃ f₄ : TestFun2D),
      (∀ x, 0 ≤ f₁ x) → (∀ x, 0 ≤ f₂ x) →
      (∀ x, 0 ≤ f₃ x) → (∀ x, 0 ≤ f₄ x) →
      infiniteTruncatedFourPoint12 params f₁ f₂ f₃ f₄ ≤
        infiniteVolumeSchwinger params 2 ![f₁, f₃] *
          infiniteVolumeSchwinger params 2 ![f₂, f₄] +
        infiniteVolumeSchwinger params 2 ![f₁, f₄] *
          infiniteVolumeSchwinger params 2 ![f₂, f₃] :=
  phi4_infiniteTruncatedFourPoint12_upper params

/-- Bundled wrapper: upper bound for infinite-volume `(13)(24)` pairing-subtracted
    4-point channel. -/
theorem phi4_infiniteTruncatedFourPoint13_upper_of_bundle
    (params : Phi4Params)
    [Phi4ModelBundle params] :
    ∀ (f₁ f₂ f₃ f₄ : TestFun2D),
      (∀ x, 0 ≤ f₁ x) → (∀ x, 0 ≤ f₂ x) →
      (∀ x, 0 ≤ f₃ x) → (∀ x, 0 ≤ f₄ x) →
      infiniteTruncatedFourPoint13 params f₁ f₂ f₃ f₄ ≤
        infiniteVolumeSchwinger params 2 ![f₁, f₂] *
          infiniteVolumeSchwinger params 2 ![f₃, f₄] +
        infiniteVolumeSchwinger params 2 ![f₁, f₄] *
          infiniteVolumeSchwinger params 2 ![f₂, f₃] :=
  phi4_infiniteTruncatedFourPoint13_upper params

/-- Bundled wrapper: upper bound for infinite-volume `(14)(23)` pairing-subtracted
    4-point channel. -/
theorem phi4_infiniteTruncatedFourPoint14_upper_of_bundle
    (params : Phi4Params)
    [Phi4ModelBundle params] :
    ∀ (f₁ f₂ f₃ f₄ : TestFun2D),
      (∀ x, 0 ≤ f₁ x) → (∀ x, 0 ≤ f₂ x) →
      (∀ x, 0 ≤ f₃ x) → (∀ x, 0 ≤ f₄ x) →
      infiniteTruncatedFourPoint14 params f₁ f₂ f₃ f₄ ≤
        infiniteVolumeSchwinger params 2 ![f₁, f₂] *
          infiniteVolumeSchwinger params 2 ![f₃, f₄] +
        infiniteVolumeSchwinger params 2 ![f₁, f₃] *
          infiniteVolumeSchwinger params 2 ![f₂, f₄] :=
  phi4_infiniteTruncatedFourPoint14_upper params

/-- Bundled wrapper: absolute-value bound for infinite-volume `(12)(34)`
    pairing-subtracted 4-point channel. -/
theorem phi4_infiniteTruncatedFourPoint12_abs_bound_of_bundle
    (params : Phi4Params)
    [Phi4ModelBundle params] :
    ∀ (f₁ f₂ f₃ f₄ : TestFun2D),
      (∀ x, 0 ≤ f₁ x) → (∀ x, 0 ≤ f₂ x) →
      (∀ x, 0 ≤ f₃ x) → (∀ x, 0 ≤ f₄ x) →
      |infiniteTruncatedFourPoint12 params f₁ f₂ f₃ f₄| ≤
        infiniteVolumeSchwinger params 2 ![f₁, f₃] *
          infiniteVolumeSchwinger params 2 ![f₂, f₄] +
        infiniteVolumeSchwinger params 2 ![f₁, f₄] *
          infiniteVolumeSchwinger params 2 ![f₂, f₃] :=
  phi4_infiniteTruncatedFourPoint12_abs_bound params

/-- Bundled wrapper: absolute-value bound for infinite-volume `(13)(24)`
    pairing-subtracted 4-point channel. -/
theorem phi4_infiniteTruncatedFourPoint13_abs_bound_of_bundle
    (params : Phi4Params)
    [Phi4ModelBundle params] :
    ∀ (f₁ f₂ f₃ f₄ : TestFun2D),
      (∀ x, 0 ≤ f₁ x) → (∀ x, 0 ≤ f₂ x) →
      (∀ x, 0 ≤ f₃ x) → (∀ x, 0 ≤ f₄ x) →
      |infiniteTruncatedFourPoint13 params f₁ f₂ f₃ f₄| ≤
        infiniteVolumeSchwinger params 2 ![f₁, f₂] *
          infiniteVolumeSchwinger params 2 ![f₃, f₄] +
        infiniteVolumeSchwinger params 2 ![f₁, f₄] *
          infiniteVolumeSchwinger params 2 ![f₂, f₃] :=
  phi4_infiniteTruncatedFourPoint13_abs_bound params

/-- Bundled wrapper: absolute-value bound for infinite-volume `(14)(23)`
    pairing-subtracted 4-point channel. -/
theorem phi4_infiniteTruncatedFourPoint14_abs_bound_of_bundle
    (params : Phi4Params)
    [Phi4ModelBundle params] :
    ∀ (f₁ f₂ f₃ f₄ : TestFun2D),
      (∀ x, 0 ≤ f₁ x) → (∀ x, 0 ≤ f₂ x) →
      (∀ x, 0 ≤ f₃ x) → (∀ x, 0 ≤ f₄ x) →
      |infiniteTruncatedFourPoint14 params f₁ f₂ f₃ f₄| ≤
        infiniteVolumeSchwinger params 2 ![f₁, f₂] *
          infiniteVolumeSchwinger params 2 ![f₃, f₄] +
        infiniteVolumeSchwinger params 2 ![f₁, f₃] *
          infiniteVolumeSchwinger params 2 ![f₂, f₄] :=
  phi4_infiniteTruncatedFourPoint14_abs_bound params

/-- Bundled wrapper: two-sided bounds for infinite-volume `(12)(34)`
    pairing-subtracted 4-point channel. -/
theorem phi4_infiniteTruncatedFourPoint12_bounds_of_bundle
    (params : Phi4Params)
    [Phi4ModelBundle params] :
    ∀ (f₁ f₂ f₃ f₄ : TestFun2D),
      (∀ x, 0 ≤ f₁ x) → (∀ x, 0 ≤ f₂ x) →
      (∀ x, 0 ≤ f₃ x) → (∀ x, 0 ≤ f₄ x) →
      0 ≤ infiniteTruncatedFourPoint12 params f₁ f₂ f₃ f₄ ∧
        infiniteTruncatedFourPoint12 params f₁ f₂ f₃ f₄ ≤
          infiniteVolumeSchwinger params 2 ![f₁, f₃] *
            infiniteVolumeSchwinger params 2 ![f₂, f₄] +
          infiniteVolumeSchwinger params 2 ![f₁, f₄] *
            infiniteVolumeSchwinger params 2 ![f₂, f₃] :=
  phi4_infiniteTruncatedFourPoint12_bounds params

/-- Bundled wrapper: two-sided bounds for infinite-volume `(13)(24)`
    pairing-subtracted 4-point channel. -/
theorem phi4_infiniteTruncatedFourPoint13_bounds_of_bundle
    (params : Phi4Params)
    [Phi4ModelBundle params] :
    ∀ (f₁ f₂ f₃ f₄ : TestFun2D),
      (∀ x, 0 ≤ f₁ x) → (∀ x, 0 ≤ f₂ x) →
      (∀ x, 0 ≤ f₃ x) → (∀ x, 0 ≤ f₄ x) →
      0 ≤ infiniteTruncatedFourPoint13 params f₁ f₂ f₃ f₄ ∧
        infiniteTruncatedFourPoint13 params f₁ f₂ f₃ f₄ ≤
          infiniteVolumeSchwinger params 2 ![f₁, f₂] *
            infiniteVolumeSchwinger params 2 ![f₃, f₄] +
          infiniteVolumeSchwinger params 2 ![f₁, f₄] *
            infiniteVolumeSchwinger params 2 ![f₂, f₃] :=
  phi4_infiniteTruncatedFourPoint13_bounds params

/-- Bundled wrapper: two-sided bounds for infinite-volume `(14)(23)`
    pairing-subtracted 4-point channel. -/
theorem phi4_infiniteTruncatedFourPoint14_bounds_of_bundle
    (params : Phi4Params)
    [Phi4ModelBundle params] :
    ∀ (f₁ f₂ f₃ f₄ : TestFun2D),
      (∀ x, 0 ≤ f₁ x) → (∀ x, 0 ≤ f₂ x) →
      (∀ x, 0 ≤ f₃ x) → (∀ x, 0 ≤ f₄ x) →
      0 ≤ infiniteTruncatedFourPoint14 params f₁ f₂ f₃ f₄ ∧
        infiniteTruncatedFourPoint14 params f₁ f₂ f₃ f₄ ≤
          infiniteVolumeSchwinger params 2 ![f₁, f₂] *
            infiniteVolumeSchwinger params 2 ![f₃, f₄] +
          infiniteVolumeSchwinger params 2 ![f₁, f₃] *
            infiniteVolumeSchwinger params 2 ![f₂, f₄] :=
  phi4_infiniteTruncatedFourPoint14_bounds params

/-- Bundled wrapper: combined two-sided bounds for all infinite-volume
    pairing-subtracted 4-point channels. -/
theorem phi4_infiniteTruncatedFourPoint_bounds_all_channels_of_bundle
    (params : Phi4Params)
    [Phi4ModelBundle params] :
    ∀ (f₁ f₂ f₃ f₄ : TestFun2D),
      (∀ x, 0 ≤ f₁ x) → (∀ x, 0 ≤ f₂ x) →
      (∀ x, 0 ≤ f₃ x) → (∀ x, 0 ≤ f₄ x) →
      0 ≤ infiniteTruncatedFourPoint12 params f₁ f₂ f₃ f₄ ∧
        infiniteTruncatedFourPoint12 params f₁ f₂ f₃ f₄ ≤
          infiniteVolumeSchwinger params 2 ![f₁, f₃] *
            infiniteVolumeSchwinger params 2 ![f₂, f₄] +
          infiniteVolumeSchwinger params 2 ![f₁, f₄] *
            infiniteVolumeSchwinger params 2 ![f₂, f₃] ∧
      0 ≤ infiniteTruncatedFourPoint13 params f₁ f₂ f₃ f₄ ∧
        infiniteTruncatedFourPoint13 params f₁ f₂ f₃ f₄ ≤
          infiniteVolumeSchwinger params 2 ![f₁, f₂] *
            infiniteVolumeSchwinger params 2 ![f₃, f₄] +
          infiniteVolumeSchwinger params 2 ![f₁, f₄] *
            infiniteVolumeSchwinger params 2 ![f₂, f₃] ∧
      0 ≤ infiniteTruncatedFourPoint14 params f₁ f₂ f₃ f₄ ∧
        infiniteTruncatedFourPoint14 params f₁ f₂ f₃ f₄ ≤
          infiniteVolumeSchwinger params 2 ![f₁, f₂] *
            infiniteVolumeSchwinger params 2 ![f₃, f₄] +
          infiniteVolumeSchwinger params 2 ![f₁, f₃] *
            infiniteVolumeSchwinger params 2 ![f₂, f₄] :=
  phi4_infiniteTruncatedFourPoint_bounds_all_channels params

/-- Bundled wrapper: infinite-volume connected 2-point symmetry. -/
theorem phi4_connectedTwoPoint_symm_of_bundle (params : Phi4Params)
    [Phi4ModelBundle params] :
    ∀ (f g : TestFun2D),
      connectedTwoPoint params f g = connectedTwoPoint params g f :=
  phi4_connectedTwoPoint_symm params

end

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
  boundaryCovariance : BoundaryCovarianceModel params.mass params.mass_pos
  interactionIntegrability : InteractionIntegrabilityModel params
  finiteVolumeComparison : FiniteVolumeComparisonModel params
  correlationIneq : CorrelationInequalityModel params
  freeRP : FreeReflectionPositivityModel params.mass params.mass_pos
  dirichletRP : DirichletReflectionPositivityModel params.mass params.mass_pos
  interactingRP : InteractingReflectionPositivityModel params
  multipleReflection : MultipleReflectionModel params
  infiniteVolume : InfiniteVolumeLimitModel params
  uniformWeakCoupling : @UniformWeakCouplingDecayModel params infiniteVolume
  wickPowers : @WickPowersModel params infiniteVolume
  regularity : @RegularityModel params infiniteVolume
  measureOS3 : @MeasureOS3Model params infiniteVolume
  osAxiom : @OSAxiomCoreModel params infiniteVolume
  osE4 : @OSE4ClusterModel params infiniteVolume osAxiom
  osE2 : @OSDistributionE2Model params infiniteVolume osAxiom
  reconstructionInput : @ReconstructionInputModel params infiniteVolume osAxiom
  wightmanReconstruction : @WightmanReconstructionModel params infiniteVolume osAxiom

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    FreeCovarianceKernelModel params.mass params.mass_pos :=
  h.freeCovarianceKernel

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    BoundaryCovarianceModel params.mass params.mass_pos :=
  h.boundaryCovariance

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    InteractionIntegrabilityModel params :=
  h.interactionIntegrability

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    FiniteVolumeComparisonModel params :=
  h.finiteVolumeComparison

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    CorrelationInequalityModel params :=
  h.correlationIneq

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
    InfiniteVolumeLimitModel params :=
  h.infiniteVolume

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    UniformWeakCouplingDecayModel params := by
  letI : InfiniteVolumeLimitModel params := h.infiniteVolume
  exact h.uniformWeakCoupling

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    WickPowersModel params := by
  letI : InfiniteVolumeLimitModel params := h.infiniteVolume
  exact h.wickPowers

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    RegularityModel params := by
  letI : InfiniteVolumeLimitModel params := h.infiniteVolume
  exact h.regularity

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    MeasureOS3Model params := by
  letI : InfiniteVolumeLimitModel params := h.infiniteVolume
  exact h.measureOS3

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    OSAxiomCoreModel params := by
  letI : InfiniteVolumeLimitModel params := h.infiniteVolume
  exact h.osAxiom

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    OSE4ClusterModel params := by
  letI : InfiniteVolumeLimitModel params := h.infiniteVolume
  letI : OSAxiomCoreModel params := h.osAxiom
  exact h.osE4

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    OSDistributionE2Model params := by
  letI : InfiniteVolumeLimitModel params := h.infiniteVolume
  letI : OSAxiomCoreModel params := h.osAxiom
  exact h.osE2

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    ReconstructionInputModel params := by
  letI : InfiniteVolumeLimitModel params := h.infiniteVolume
  letI : OSAxiomCoreModel params := h.osAxiom
  exact h.reconstructionInput

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    WightmanReconstructionModel params := by
  letI : InfiniteVolumeLimitModel params := h.infiniteVolume
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

/-- Bundled wrapper: infinite-volume connected 2-point symmetry. -/
theorem phi4_connectedTwoPoint_symm_of_bundle (params : Phi4Params)
    [Phi4ModelBundle params] :
    ∀ (f g : TestFun2D),
      connectedTwoPoint params f g = connectedTwoPoint params g f :=
  phi4_connectedTwoPoint_symm params

end

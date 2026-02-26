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
  osAxiom : @OSAxiomModel params infiniteVolume
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
    OSAxiomModel params := by
  letI : InfiniteVolumeLimitModel params := h.infiniteVolume
  exact h.osAxiom

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    ReconstructionInputModel params := by
  letI : InfiniteVolumeLimitModel params := h.infiniteVolume
  letI : OSAxiomModel params := h.osAxiom
  exact h.reconstructionInput

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    WightmanReconstructionModel params := by
  letI : InfiniteVolumeLimitModel params := h.infiniteVolume
  letI : OSAxiomModel params := h.osAxiom
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

end

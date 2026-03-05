/- 
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.Reconstruction.Part3

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
  correlationGKSSecond : CorrelationGKSSecondModel params
  correlationLebowitz : CorrelationLebowitzModel params
  schwingerFourMonotone : SchwingerNMonotoneModel params 4
  correlationFKG : CorrelationFKGModel params
  freeRP : FreeReflectionPositivityModel params.mass params.mass_pos
  dirichletRP : DirichletReflectionPositivityModel params.mass params.mass_pos
  interactingRP : InteractingReflectionPositivityModel params
  multipleReflection : MultipleReflectionModel params
  infiniteVolumeLimit : InfiniteVolumeLimitModel params
  uniformWeakCoupling : UniformWeakCouplingDecayModel params
  wickPowers : WickPowersModel params
  regularity : RegularityModel params
  measureOS3 : MeasureOS3Model params
  osaCore : OSAxiomCoreModel params
  osE4 : OSE4ClusterModel params
  osE2 : OSDistributionE2Model params
  reconstructionLinearGrowth : ReconstructionLinearGrowthModel params
  wightmanReconstruction : WightmanReconstructionModel params

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
    CorrelationGKSSecondModel params :=
  h.correlationGKSSecond

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    CorrelationLebowitzModel params :=
  h.correlationLebowitz

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    SchwingerNMonotoneModel params 4 :=
  h.schwingerFourMonotone

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    CorrelationFKGModel params :=
  h.correlationFKG

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    CorrelationInequalityModel params := by
  letI : CorrelationTwoPointModel params := h.correlationTwoPoint
  letI : CorrelationGKSSecondModel params := h.correlationGKSSecond
  letI : CorrelationLebowitzModel params := h.correlationLebowitz
  letI : SchwingerNMonotoneModel params 4 := h.schwingerFourMonotone
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
by
  letI : InfiniteVolumeLimitModel params := h.infiniteVolumeLimit
  infer_instance

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    InfiniteVolumeMeasureModel params := by
  letI : InfiniteVolumeLimitModel params := h.infiniteVolumeLimit
  infer_instance

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    InfiniteVolumeMomentModel params := by
  letI : InfiniteVolumeLimitModel params := h.infiniteVolumeLimit
  infer_instance

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    InfiniteVolumeLimitModel params := by
  exact h.infiniteVolumeLimit

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    UniformWeakCouplingDecayModel params := by
  letI : InfiniteVolumeLimitModel params := h.infiniteVolumeLimit
  exact h.uniformWeakCoupling

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    WickPowersModel params := by
  letI : InfiniteVolumeLimitModel params := h.infiniteVolumeLimit
  exact h.wickPowers

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    WickCubicConvergenceModel params := by
  letI : InfiniteVolumeLimitModel params := h.infiniteVolumeLimit
  letI : RegularityModel params := h.regularity
  infer_instance

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    EuclideanEquationModel params := by
  letI : InfiniteVolumeLimitModel params := h.infiniteVolumeLimit
  letI : RegularityModel params := h.regularity
  infer_instance

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    GeneratingFunctionalBoundModel params := by
  letI : InfiniteVolumeLimitModel params := h.infiniteVolumeLimit
  letI : RegularityModel params := h.regularity
  infer_instance

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    NonlocalPhi4BoundModel params := by
  letI : InfiniteVolumeLimitModel params := h.infiniteVolumeLimit
  letI : RegularityModel params := h.regularity
  infer_instance

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    UniformGeneratingFunctionalBoundModel params := by
  letI : InfiniteVolumeLimitModel params := h.infiniteVolumeLimit
  letI : RegularityModel params := h.regularity
  infer_instance

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    RegularityModel params := by
  exact h.regularity

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    MeasureOS3Model params := by
  letI : InfiniteVolumeLimitModel params := h.infiniteVolumeLimit
  exact h.measureOS3

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    SchwingerFunctionModel params := by
  letI : OSAxiomCoreModel params := h.osaCore
  infer_instance

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    OSTemperedModel params := by
  letI : OSAxiomCoreModel params := h.osaCore
  infer_instance

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    OSEuclideanCovarianceModel params := by
  letI : OSAxiomCoreModel params := h.osaCore
  infer_instance

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    OSE3SymmetryModel params := by
  letI : OSAxiomCoreModel params := h.osaCore
  infer_instance

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    OSAxiomCoreModel params := by
  exact h.osaCore

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    OSE4ClusterModel params := by
  letI : OSAxiomCoreModel params := h.osaCore
  exact h.osE4

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    OSDistributionE2Model params := by
  letI : OSAxiomCoreModel params := h.osaCore
  exact h.osE2

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    ReconstructionLinearGrowthModel params := by
  letI : OSAxiomCoreModel params := h.osaCore
  exact h.reconstructionLinearGrowth

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    WightmanReconstructionModel params := by
  exact h.wightmanReconstruction

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    ReconstructionWeakCouplingModel params := by
  letI : InfiniteVolumeLimitModel params := h.infiniteVolumeLimit
  letI : UniformWeakCouplingDecayModel params := h.uniformWeakCoupling
  infer_instance

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    ReconstructionInputModel params := by
  letI : InfiniteVolumeLimitModel params := h.infiniteVolumeLimit
  letI : OSAxiomCoreModel params := h.osaCore
  letI : ReconstructionLinearGrowthModel params := h.reconstructionLinearGrowth
  letI : ReconstructionWeakCouplingModel params := inferInstance
  infer_instance

end

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
  infiniteVolumeMeasure : InfiniteVolumeMeasureModel params
  infiniteVolumeMoment : @InfiniteVolumeMomentModel params
    infiniteVolumeSchwinger infiniteVolumeMeasure
  uniformWeakCoupling : @UniformWeakCouplingDecayModel params
    infiniteVolumeSchwinger
  wickPowers : @WickPowersModel params
    infiniteVolumeSchwinger infiniteVolumeMeasure
  regularity : @RegularityModel params
    infiniteVolumeSchwinger infiniteVolumeMeasure
  measureOS3 : @MeasureOS3Model params
    infiniteVolumeMeasure
  osAxiom : OSAxiomCoreModel params
  osE4 : @OSE4ClusterModel params osAxiom
  osE2 : @OSDistributionE2Model params osAxiom
  reconstructionLinearGrowth : @ReconstructionLinearGrowthModel params
    osAxiom
  wightmanReconstruction : @WightmanReconstructionModel params osAxiom

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
  exact h.infiniteVolumeMeasure

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    InfiniteVolumeMomentModel params := by
  letI : InfiniteVolumeSchwingerModel params := h.infiniteVolumeSchwinger
  letI : InfiniteVolumeMeasureModel params := h.infiniteVolumeMeasure
  exact h.infiniteVolumeMoment

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    InfiniteVolumeLimitModel params := by
  letI : InfiniteVolumeSchwingerModel params := h.infiniteVolumeSchwinger
  letI : InfiniteVolumeMeasureModel params := h.infiniteVolumeMeasure
  letI : InfiniteVolumeMomentModel params := h.infiniteVolumeMoment
  infer_instance

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    UniformWeakCouplingDecayModel params := by
  letI : InfiniteVolumeSchwingerModel params := h.infiniteVolumeSchwinger
  exact h.uniformWeakCoupling

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    WickPowersModel params := by
  letI : InfiniteVolumeSchwingerModel params := h.infiniteVolumeSchwinger
  letI : InfiniteVolumeMeasureModel params := h.infiniteVolumeMeasure
  exact h.wickPowers

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    RegularityModel params := by
  letI : InfiniteVolumeSchwingerModel params := h.infiniteVolumeSchwinger
  letI : InfiniteVolumeMeasureModel params := h.infiniteVolumeMeasure
  exact h.regularity

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    MeasureOS3Model params := by
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
    ReconstructionLinearGrowthModel params := by
  letI : OSAxiomCoreModel params := h.osAxiom
  exact h.reconstructionLinearGrowth

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    WightmanReconstructionModel params := by
  letI : OSAxiomCoreModel params := h.osAxiom
  exact h.wightmanReconstruction

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    ReconstructionWeakCouplingModel params := by
  letI : InfiniteVolumeSchwingerModel params := h.infiniteVolumeSchwinger
  letI : UniformWeakCouplingDecayModel params := h.uniformWeakCoupling
  infer_instance

instance (params : Phi4Params) [h : Phi4ModelBundle params] :
    ReconstructionInputModel params := by
  letI : InfiniteVolumeSchwingerModel params := h.infiniteVolumeSchwinger
  letI : OSAxiomCoreModel params := h.osAxiom
  letI : ReconstructionLinearGrowthModel params := h.reconstructionLinearGrowth
  letI : ReconstructionWeakCouplingModel params := inferInstance
  infer_instance

/-- Convenience wrapper: bundled regularity interfaces yield the generating-functional
    bound directly from `RegularityModel` (trusted interface path). -/
theorem generating_functional_bound_of_bundle (params : Phi4Params)
    [Phi4ModelBundle params] :
    ∃ c : ℝ, ∀ f : TestFun2D,
      |∫ ω, Real.exp (ω f) ∂(infiniteVolumeMeasure params)| ≤
        Real.exp (c * normFunctional f) :=
  generating_functional_bound_of_interface params

/-- Convenience wrapper: bundled regularity interfaces yield the nonlocal φ⁴ bound
    directly from `RegularityModel` (trusted interface path). -/
theorem nonlocal_phi4_bound_of_bundle (params : Phi4Params)
    [Phi4ModelBundle params] :
    ∀ (g : TestFun2D), ∃ C₁ C₂ : ℝ, ∀ (Λ : Rectangle),
      |generatingFunctional params Λ g| ≤
        Real.exp (C₁ * Λ.area + C₂) :=
  nonlocal_phi4_bound_of_interface params

/-- Convenience wrapper: bundled regularity interfaces yield uniform-in-volume
    generating-functional bounds directly from `RegularityModel`. -/
theorem generating_functional_bound_uniform_of_bundle (params : Phi4Params)
    [Phi4ModelBundle params]
    (f : TestFun2D) :
    ∃ c : ℝ, ∀ Λ : Rectangle,
      |generatingFunctional params Λ f| ≤ Real.exp (c * normFunctional f) :=
  generating_functional_bound_uniform_of_interface params f

/-- Convenience wrapper: bundled interfaces yield OS1 through the trusted
    interface theorem `phi4_os1_of_interface`. -/
theorem phi4_os1_of_bundle (params : Phi4Params)
    [Phi4ModelBundle params] :
    ∃ c : ℝ, ∀ f : TestFun2D,
      |∫ ω, Real.exp (ω f) ∂(infiniteVolumeMeasure params)| ≤
        Real.exp (c * normFunctional f) :=
  phi4_os1_of_interface params

/-- Convenience wrapper: bundled interfaces yield the OS package theorem under
    explicit weak-coupling smallness. -/
theorem phi4_satisfies_OS_of_bundle (params : Phi4Params)
    [Phi4ModelBundle params]
    (hsmall : params.coupling < os4WeakCouplingThreshold params) :
    ∃ OS : OsterwalderSchraderAxioms 1,
      OS.S = phi4SchwingerFunctions params :=
  phi4_satisfies_OS_of_interfaces params hsmall

/-- Convenience wrapper: a bundled model gives the Wightman reconstruction result. -/
theorem phi4_wightman_exists_of_bundle (params : Phi4Params)
    [Phi4ModelBundle params] :
    ∃ (Wfn : WightmanFunctions 1),
      ∃ (OS : OsterwalderSchraderAxioms 1),
        OS.S = phi4SchwingerFunctions params ∧
        IsWickRotationPair OS.S Wfn.W :=
  phi4_wightman_exists_of_interfaces params

/-- Bundled self-adjointness corollary via interface-level reconstruction path. -/
theorem phi4_selfadjoint_fields_of_bundle (params : Phi4Params)
    [Phi4ModelBundle params] :
    ∃ (Wfn : WightmanFunctions 1),
      IsWickRotationPair (phi4SchwingerFunctions params) Wfn.W ∧
      (∀ (n : ℕ) (f g : SchwartzNPoint 1 n),
        (∀ x, g.toFun x = starRingEnd ℂ (f.toFun (fun i => x (Fin.rev i)))) →
        Wfn.W n g = starRingEnd ℂ (Wfn.W n f)) :=
  phi4_selfadjoint_fields_of_interfaces params

/-- Bundled locality corollary via interface-level reconstruction path. -/
theorem phi4_locality_of_bundle (params : Phi4Params)
    [Phi4ModelBundle params] :
    ∃ (Wfn : WightmanFunctions 1),
      IsWickRotationPair (phi4SchwingerFunctions params) Wfn.W ∧
      IsLocallyCommutativeWeak 1 Wfn.W :=
  phi4_locality_of_interfaces params

/-- Bundled Lorentz-covariance corollary via interface-level reconstruction path. -/
theorem phi4_lorentz_covariance_of_bundle (params : Phi4Params)
    [Phi4ModelBundle params] :
    ∃ (Wfn : WightmanFunctions 1),
      IsWickRotationPair (phi4SchwingerFunctions params) Wfn.W ∧
      IsLorentzCovariantWeak 1 Wfn.W :=
  phi4_lorentz_covariance_of_interfaces params

/-- Bundled positive-definite/vacuum corollary via interface-level reconstruction path. -/
theorem phi4_unique_vacuum_of_bundle (params : Phi4Params)
    [Phi4ModelBundle params] :
    ∃ (Wfn : WightmanFunctions 1),
      IsPositiveDefinite 1 Wfn.W ∧
      IsWickRotationPair (phi4SchwingerFunctions params) Wfn.W :=
  phi4_unique_vacuum_of_interfaces params

/-- Bundled wrapper for weak-coupling connected 2-point decay threshold existence. -/
theorem phi4_connectedTwoPoint_decay_threshold_of_bundle (params : Phi4Params)
    [Phi4ModelBundle params] :
    ConnectedTwoPointDecayThreshold params :=
  phi4_connectedTwoPoint_decay_threshold params

/-- Bundled wrapper: global weak-coupling connected 2-point exponential decay. -/
theorem phi4_os4_weak_coupling_of_bundle (params : Phi4Params)
    [Phi4ModelBundle params] :
    ∃ coupling_bound : ℝ, 0 < coupling_bound ∧
      ∀ p : Phi4Params, [InfiniteVolumeSchwingerModel p] →
        p.coupling < coupling_bound →
          ConnectedTwoPointDecayAtParams p :=
  phi4_os4_weak_coupling params

/-- Bundled wrapper: explicit-Schwinger global weak-coupling connected 2-point
    exponential decay. -/
theorem phi4_os4_weak_coupling_explicit_of_bundle (params : Phi4Params)
    [Phi4ModelBundle params] :
    ∃ coupling_bound : ℝ, 0 < coupling_bound ∧
      ∀ p : Phi4Params, [InfiniteVolumeSchwingerModel p] →
        p.coupling < coupling_bound →
          ∃ m_gap : ℝ, 0 < m_gap ∧
            ∀ (f g : TestFun2D), ∃ Cfg : ℝ, 0 ≤ Cfg ∧
              ∀ (a : Fin 2 → ℝ),
                let g_shifted : TestFun2D := translateTestFun a g
                |infiniteVolumeSchwinger p 2 ![f, g_shifted] -
                  infiniteVolumeSchwinger p 1 ![f] *
                    infiniteVolumeSchwinger p 1 ![g_shifted]| ≤
                  Cfg * Real.exp (-m_gap * ‖a‖) :=
  phi4_os4_weak_coupling_explicit params

/-- Bundled wrapper: global weak-coupling `ε`-`R` clustering for connected
    2-point functions. -/
theorem phi4_os4_weak_coupling_eventually_small_of_bundle (params : Phi4Params)
    [Phi4ModelBundle params] :
    ∃ coupling_bound : ℝ, 0 < coupling_bound ∧
      ∀ p : Phi4Params, [InfiniteVolumeSchwingerModel p] →
        p.coupling < coupling_bound →
          ∀ (f g : TestFun2D) (ε : ℝ), 0 < ε → ∃ R : ℝ, 0 < R ∧
            ∀ a : Fin 2 → ℝ, R < ‖a‖ →
              let g_shifted : TestFun2D := translateTestFun a g
              |connectedTwoPoint p f g_shifted| < ε :=
  phi4_os4_weak_coupling_eventually_small params

/-- Bundled wrapper: explicit-Schwinger global weak-coupling `ε`-`R`
    clustering for connected 2-point functions. -/
theorem phi4_os4_weak_coupling_eventually_small_explicit_of_bundle
    (params : Phi4Params)
    [Phi4ModelBundle params] :
    ∃ coupling_bound : ℝ, 0 < coupling_bound ∧
      ∀ p : Phi4Params, [InfiniteVolumeSchwingerModel p] →
        p.coupling < coupling_bound →
          ∀ (f g : TestFun2D) (ε : ℝ), 0 < ε → ∃ R : ℝ, 0 < R ∧
            ∀ a : Fin 2 → ℝ, R < ‖a‖ →
              let g_shifted : TestFun2D := translateTestFun a g
              |infiniteVolumeSchwinger p 2 ![f, g_shifted] -
                infiniteVolumeSchwinger p 1 ![f] *
                  infiniteVolumeSchwinger p 1 ![g_shifted]| < ε :=
  phi4_os4_weak_coupling_eventually_small_explicit params

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

/-- Bundled wrapper: `ε`-`R` connected 2-point clustering below the selected
    weak-coupling threshold. -/
theorem phi4_connectedTwoPoint_decay_below_threshold_eventually_small_of_bundle
    (params : Phi4Params)
    [Phi4ModelBundle params]
    (hsmall : params.coupling < phi4WeakCouplingThreshold params) :
    ∀ (f g : TestFun2D), ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
      ∀ a : Fin 2 → ℝ, R < ‖a‖ →
        let g_shifted : TestFun2D := translateTestFun a g
        |connectedTwoPoint params f g_shifted| < ε :=
  phi4_connectedTwoPoint_decay_below_threshold_eventually_small params hsmall

/-- Bundled wrapper: explicit-Schwinger `ε`-`R` connected 2-point clustering
    below the selected weak-coupling threshold. -/
theorem phi4_connectedTwoPoint_decay_below_threshold_eventually_small_explicit_of_bundle
    (params : Phi4Params)
    [Phi4ModelBundle params]
    (hsmall : params.coupling < phi4WeakCouplingThreshold params) :
    ∀ (f g : TestFun2D), ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
      ∀ a : Fin 2 → ℝ, R < ‖a‖ →
        let g_shifted : TestFun2D := translateTestFun a g
        |infiniteVolumeSchwinger params 2 ![f, g_shifted] -
          infiniteVolumeSchwinger params 1 ![f] *
            infiniteVolumeSchwinger params 1 ![g_shifted]| < ε :=
  phi4_connectedTwoPoint_decay_below_threshold_eventually_small_explicit params hsmall

/-- Bundled wrapper: infinite-volume connected 2-point nonnegativity for
    nonnegative test functions. -/
theorem phi4_connectedTwoPoint_nonneg_of_bundle (params : Phi4Params)
    [Phi4ModelBundle params] :
    ∀ (f g : TestFun2D), (∀ x, 0 ≤ f x) → (∀ x, 0 ≤ g x) →
      0 ≤ connectedTwoPoint params f g :=
  phi4_connectedTwoPoint_nonneg params

/-- Bundled wrapper: infinite-volume diagonal connected 2-point nonnegativity
    for nonnegative test functions. -/
theorem phi4_connectedTwoPoint_self_nonneg_of_bundle (params : Phi4Params)
    [Phi4ModelBundle params] :
    ∀ (f : TestFun2D), (∀ x, 0 ≤ f x) → 0 ≤ connectedTwoPoint params f f :=
  phi4_connectedTwoPoint_self_nonneg params

/-- Bundled wrapper: infinite-volume diagonal connected 2-point nonnegativity
    in variance form (no sign restrictions on test functions). -/
theorem phi4_connectedTwoPoint_self_nonneg_variance_of_bundle (params : Phi4Params)
    [Phi4ModelBundle params] :
    ∀ (f : TestFun2D), 0 ≤ connectedTwoPoint params f f :=
  phi4_connectedTwoPoint_self_nonneg_variance params

/-- Bundled wrapper: additivity in the first argument of connected two-point. -/
theorem phi4_connectedTwoPoint_add_left_of_bundle (params : Phi4Params)
    [Phi4ModelBundle params] :
    ∀ (f₁ f₂ g : TestFun2D),
      connectedTwoPoint params (f₁ + f₂) g =
        connectedTwoPoint params f₁ g + connectedTwoPoint params f₂ g :=
  phi4_connectedTwoPoint_add_left params

/-- Bundled wrapper: scalar linearity in the first argument of connected two-point. -/
theorem phi4_connectedTwoPoint_smul_left_of_bundle (params : Phi4Params)
    [Phi4ModelBundle params] :
    ∀ (c : ℝ) (f g : TestFun2D),
      connectedTwoPoint params (c • f) g = c * connectedTwoPoint params f g :=
  phi4_connectedTwoPoint_smul_left params

/-- Bundled wrapper: additivity in the second argument of connected two-point. -/
theorem phi4_connectedTwoPoint_add_right_of_bundle (params : Phi4Params)
    [Phi4ModelBundle params] :
    ∀ (f g₁ g₂ : TestFun2D),
      connectedTwoPoint params f (g₁ + g₂) =
        connectedTwoPoint params f g₁ + connectedTwoPoint params f g₂ :=
  phi4_connectedTwoPoint_add_right params

/-- Bundled wrapper: scalar linearity in the second argument of connected two-point. -/
theorem phi4_connectedTwoPoint_smul_right_of_bundle (params : Phi4Params)
    [Phi4ModelBundle params] :
    ∀ (c : ℝ) (f g : TestFun2D),
      connectedTwoPoint params f (c • g) = c * connectedTwoPoint params f g :=
  phi4_connectedTwoPoint_smul_right params

/-- Bundled wrapper: connected two-point as a bilinear map. -/
def phi4_connectedTwoPoint_bilinear_of_bundle (params : Phi4Params)
    [Phi4ModelBundle params] :
    TestFun2D →ₗ[ℝ] TestFun2D →ₗ[ℝ] ℝ :=
  phi4_connectedTwoPoint_bilinear params

/-- Bundled wrapper: symmetry of connected two-point bilinear form. -/
theorem phi4_connectedTwoPoint_bilinear_symm_of_bundle (params : Phi4Params)
    [Phi4ModelBundle params] :
    ∀ (f g : TestFun2D),
      connectedTwoPointBilinear params f g =
        connectedTwoPointBilinear params g f :=
  phi4_connectedTwoPoint_bilinear_symm params

/-- Bundled wrapper: diagonal nonnegativity of connected two-point bilinear form. -/
theorem phi4_connectedTwoPoint_bilinear_self_nonneg_of_bundle (params : Phi4Params)
    [Phi4ModelBundle params] :
    ∀ (f : TestFun2D), 0 ≤ connectedTwoPointBilinear params f f :=
  phi4_connectedTwoPoint_bilinear_self_nonneg params

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

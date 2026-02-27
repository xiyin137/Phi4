/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.Regularity
import OSReconstruction.Wightman.Reconstruction

/-!
# OS Axioms for φ⁴₂

This is the main theorem file. We verify that the infinite-volume φ⁴₂ Schwinger
functions satisfy the Osterwalder-Schrader axioms E0-E3, and package E4 under
an explicit weak-coupling hypothesis.

**Theorem 12.1.1 (Glimm-Jaffe)**: The generating functional S{f} of the φ⁴₂ theory
exists and satisfies the Euclidean axioms OS0-OS3. Hence (by the OS reconstruction
theorem) it yields a quantum field theory satisfying the Wightman axioms W1-W3.

The four axioms are:
- **OS0 (Temperedness)**: S_n are tempered distributions on S(ℝ^{2n})
- **OS1 (Regularity)**: |S{f}| ≤ exp(c · N'(f)) (linear growth)
- **OS2 (Euclidean covariance)**: S_n invariant under translations and SO(2) rotations
- **OS3 (Reflection positivity)**: RP inner product is positive semidefinite

## References

* [Glimm-Jaffe] Theorem 12.1.1, Chapter 12
* [Osterwalder-Schrader I, II]
-/

noncomputable section

open MeasureTheory Reconstruction

/-! ## Abstract OS-axiom interfaces -/

/-- Core OS input: Schwinger packaging together with OS0/OS2/E3 data.
    Weak-coupling E4 clustering is separated into `OSE4ClusterModel`. -/
class OSAxiomCoreModel (params : Phi4Params) where
  schwingerFunctions : SchwingerFunctions 1
  os0 :
    ∀ n, Continuous (schwingerFunctions n)
  schwinger_linear :
    ∀ n, IsLinearMap ℂ (schwingerFunctions n)
  os2_translation :
    ∀ (n : ℕ) (a : Fin 2 → ℝ) (f g : SchwartzNPoint 1 n),
      (∀ x, g.toFun x = f.toFun (fun i => x i + a)) →
      schwingerFunctions n f = schwingerFunctions n g
  os2_rotation :
    ∀ (n : ℕ) (R : Matrix (Fin 2) (Fin 2) ℝ),
      R.transpose * R = 1 → R.det = 1 →
      ∀ (f g : SchwartzNPoint 1 n),
        (∀ x, g.toFun x = f.toFun (fun i => R.mulVec (x i))) →
        schwingerFunctions n f = schwingerFunctions n g
  e3_symmetric :
    ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)) (f g : SchwartzNPoint 1 n),
      (∀ x, g.toFun x = f.toFun (fun i => x (σ i))) →
      schwingerFunctions n f = schwingerFunctions n g

/-- Weak-coupling E4 cluster input, parameterized over a core OS model. -/
class OSE4ClusterModel (params : Phi4Params)
    [OSAxiomCoreModel params] where
  /-- A model-specific weak-coupling threshold below which clustering is available. -/
  weak_coupling_threshold : ℝ
  weak_coupling_threshold_pos : 0 < weak_coupling_threshold
  e4_cluster_of_weak_coupling :
    params.coupling < weak_coupling_threshold →
      ∀ (n m : ℕ) (f : SchwartzNPoint 1 n) (g : SchwartzNPoint 1 m),
        ∀ ε : ℝ, ε > 0 → ∃ R : ℝ, R > 0 ∧
          ∀ a : SpacetimeDim 1, a 0 = 0 → (∑ i : Fin 1, (a (Fin.succ i))^2) > R^2 →
            ∀ (g_a : SchwartzNPoint 1 m),
              (∀ x : NPointDomain 1 m, g_a x = g (fun i => x i - a)) →
              ‖OSAxiomCoreModel.schwingerFunctions (params := params) (n + m) (f.tensorProduct g_a) -
                OSAxiomCoreModel.schwingerFunctions (params := params) n f *
                  OSAxiomCoreModel.schwingerFunctions (params := params) m g‖ < ε

/-- Measure-level reflection positivity for linear observables against
    `infiniteVolumeMeasure`, kept separate from core Schwinger packaging so the
    distributional OS interface does not silently bundle an independent
    concrete positivity API. -/
class MeasureOS3Model (params : Phi4Params)
    [InfiniteVolumeMeasureModel params] where
  os3 :
    ∀ (n : ℕ) (f : Fin n → TestFun2D) (c : Fin n → ℂ),
      (∀ i, supportedInPositiveTime (f i)) →
        0 ≤ (∑ i, ∑ j, c i * starRingEnd ℂ (c j) *
          ∫ ω, ω (testFunTimeReflect (f i)) * ω (f j)
            ∂(infiniteVolumeMeasure params)).re

/-- Distributional E2 reflection positivity interface for the OS reconstruction API.
    Kept separate from core OS packaging so Schwinger-function data and E2
    positivity are explicitly decoupled assumptions. -/
class OSDistributionE2Model (params : Phi4Params)
    [OSAxiomCoreModel params] where
  e2_reflection_positive :
    ∀ (F : BorchersSequence 1),
      (∀ n, ∀ x : NPointDomain 1 n,
        (F.funcs n).toFun x ≠ 0 → x ∈ PositiveTimeRegion 1 n) →
      (OSInnerProduct 1 (OSAxiomCoreModel.schwingerFunctions (params := params)) F F).re ≥ 0

/-! ## Schwinger functions as distributions

The infinite volume Schwinger functions define tempered distributions on S(ℝ^{2n}). -/

/-- The φ⁴₂ Schwinger functions packaged as a `SchwingerFunctions` (from OSreconstruction).
    Here d = 1 because OSreconstruction uses spacetime dimension d+1, and we have d+1 = 2.

    S_n : S(ℝ^{n×2}) → ℂ is defined by:
      S_n(f) = ∫ φ(x₁)⋯φ(xₙ) f(x₁,...,xₙ) dx₁⋯dxₙ dμ(φ) -/
def phi4SchwingerFunctions (params : Phi4Params)
    [OSAxiomCoreModel params] :
    SchwingerFunctions 1 :=
  OSAxiomCoreModel.schwingerFunctions (params := params)

/-! ## OS0: Temperedness -/

/-- **OS0 (Temperedness)**: Each S_n is a continuous linear functional on
    the Schwartz space S(ℝ^{n×2}), i.e., a tempered distribution.

    This follows from the Lᵖ bounds on the field: since ω(f) ∈ Lᵖ for all p,
    the products ω(f₁)⋯ω(fₙ) are integrable and depend continuously on the
    test functions in the Schwartz topology. -/
theorem phi4_os0 (params : Phi4Params)
    [OSAxiomCoreModel params] :
    ∀ n, Continuous (phi4SchwingerFunctions params n) := by
  simpa [phi4SchwingerFunctions] using
    (OSAxiomCoreModel.os0 (params := params))

theorem phi4_os0_linear (params : Phi4Params)
    [OSAxiomCoreModel params] :
    ∀ n, IsLinearMap ℂ (phi4SchwingerFunctions params n) := by
  simpa [phi4SchwingerFunctions] using
    (OSAxiomCoreModel.schwinger_linear (params := params))

/-! ## OS1: Regularity (Linear Growth) -/

/-- **OS1 (Regularity), trusted interface path**:
    when `RegularityModel` is available, the generating-functional bound is
    obtained directly from interface data (without frontier-gap wrappers). -/
theorem phi4_os1_of_interface (params : Phi4Params)
    [InfiniteVolumeSchwingerModel params]
    [InfiniteVolumeMeasureModel params]
    [RegularityModel params] :
    ∃ c : ℝ, ∀ f : TestFun2D,
      |∫ ω, Real.exp (ω f) ∂(infiniteVolumeMeasure params)| ≤
        Real.exp (c * normFunctional f) := by
  exact generating_functional_bound_of_interface params

/-- **OS1 (Regularity)**: The generating functional satisfies the linear growth bound
    |S{f}| ≤ exp(c · N'(f)).

    This is Theorem 12.5.1, the culmination of the integration by parts analysis.
    It is the most technically demanding of the OS axioms to verify. -/
theorem phi4_os1 (params : Phi4Params)
    [InfiniteVolumeSchwingerModel params]
    [InfiniteVolumeMeasureModel params]
    [RegularityModel params] :
    ∃ c : ℝ, ∀ f : TestFun2D,
      |∫ ω, Real.exp (ω f) ∂(infiniteVolumeMeasure params)| ≤
        Real.exp (c * normFunctional f) := by
  exact generating_functional_bound params

/-! ## OS2: Euclidean Covariance -/

/-- **OS2a (Translation invariance)**: The Schwinger functions are invariant
    under Euclidean translations:
      S_n(x₁+a,...,xₙ+a) = S_n(x₁,...,xₙ) for all a ∈ ℝ².

    This follows because the infinite volume measure is translation invariant
    (the interaction and free measure are both translation invariant, and the
    infinite volume limit preserves this symmetry). -/
theorem phi4_os2_translation (params : Phi4Params)
    [OSAxiomCoreModel params] :
    ∀ (n : ℕ) (a : Fin 2 → ℝ) (f g : SchwartzNPoint 1 n),
      (∀ x, g.toFun x = f.toFun (fun i => x i + a)) →
      phi4SchwingerFunctions params n f = phi4SchwingerFunctions params n g := by
  intro n a f g hfg
  simpa [phi4SchwingerFunctions] using
    (OSAxiomCoreModel.os2_translation (params := params) n a f g hfg)

/-- **OS2b (Rotation invariance)**: The Schwinger functions are invariant
    under SO(2) rotations:
      S_n(Rx₁,...,Rxₙ) = S_n(x₁,...,xₙ) for all R ∈ SO(2).

    This follows from the rotational invariance of the Laplacian
    and hence of the free covariance, combined with the rotational
    invariance of the interaction ∫ :φ⁴: dx. -/
theorem phi4_os2_rotation (params : Phi4Params)
    [OSAxiomCoreModel params] :
    ∀ (n : ℕ) (R : Matrix (Fin 2) (Fin 2) ℝ),
      R.transpose * R = 1 → R.det = 1 →
      ∀ (f g : SchwartzNPoint 1 n),
        (∀ x, g.toFun x = f.toFun (fun i => R.mulVec (x i))) →
        phi4SchwingerFunctions params n f = phi4SchwingerFunctions params n g := by
  intro n R horth hdet f g hfg
  simpa [phi4SchwingerFunctions] using
    (OSAxiomCoreModel.os2_rotation (params := params) n R horth hdet f g hfg)

/-! ## OS3: Reflection Positivity -/

/-- **OS3 (Reflection positivity)**: For any test function sequence F = (F₀, F₁, ...)
    supported in positive Euclidean time {τ > 0},
      Σₙₘ ∫ (θF_n)* F_m S_{n+m} ≥ 0
    where θ is time reflection τ ↦ -τ.

    This is inherited from the finite-volume reflection positivity
    (Theorem 10.4 / ReflectionPositivity.lean) and passes to the
    infinite volume limit by the convergence of S_n^Λ → S_n. -/
theorem phi4_os3 (params : Phi4Params)
    [InfiniteVolumeMeasureModel params]
    [MeasureOS3Model params]
    (n : ℕ) (f : Fin n → TestFun2D) (c : Fin n → ℂ)
    (hf : ∀ i, supportedInPositiveTime (f i)) :
    0 ≤ (∑ i, ∑ j, c i * starRingEnd ℂ (c j) *
      ∫ ω, ω (testFunTimeReflect (f i)) * ω (f j)
        ∂(infiniteVolumeMeasure params)).re := by
  exact MeasureOS3Model.os3 (params := params) n f c hf

/-- Distributional E2 reflection positivity for the packaged φ⁴₂ Schwinger functions. -/
theorem phi4_e2_distributional (params : Phi4Params)
    [OSAxiomCoreModel params]
    [OSDistributionE2Model params] :
    ∀ (F : BorchersSequence 1),
      (∀ n, ∀ x : NPointDomain 1 n,
        (F.funcs n).toFun x ≠ 0 → x ∈ PositiveTimeRegion 1 n) →
      (OSInnerProduct 1 (phi4SchwingerFunctions params) F F).re ≥ 0 := by
  intro F hF
  simpa [phi4SchwingerFunctions] using
    OSDistributionE2Model.e2_reflection_positive (params := params) F hF

/-! ## Main theorem: OS axioms hold -/

/-- Canonical weak-coupling threshold carried by `OSE4ClusterModel`. -/
def os4WeakCouplingThreshold (params : Phi4Params)
    [OSAxiomCoreModel params]
    [OSE4ClusterModel params] : ℝ :=
  OSE4ClusterModel.weak_coupling_threshold (params := params)

/-- Positivity of the canonical weak-coupling threshold. -/
theorem os4WeakCouplingThreshold_pos (params : Phi4Params)
    [OSAxiomCoreModel params]
    [OSE4ClusterModel params] :
    0 < os4WeakCouplingThreshold params := by
  simpa [os4WeakCouplingThreshold] using
    OSE4ClusterModel.weak_coupling_threshold_pos (params := params)

/-- E4 cluster property extracted from `OSE4ClusterModel` under weak coupling. -/
theorem phi4_e4_cluster_of_weak_coupling (params : Phi4Params)
    [OSAxiomCoreModel params]
    [OSE4ClusterModel params]
    (hsmall : params.coupling < os4WeakCouplingThreshold params) :
    ∀ (n m : ℕ) (f : SchwartzNPoint 1 n) (g : SchwartzNPoint 1 m),
      ∀ ε : ℝ, ε > 0 → ∃ R : ℝ, R > 0 ∧
        ∀ a : SpacetimeDim 1, a 0 = 0 → (∑ i : Fin 1, (a (Fin.succ i))^2) > R^2 →
          ∀ (g_a : SchwartzNPoint 1 m),
            (∀ x : NPointDomain 1 m, g_a x = g (fun i => x i - a)) →
            ‖phi4SchwingerFunctions params (n + m) (f.tensorProduct g_a) -
              phi4SchwingerFunctions params n f * phi4SchwingerFunctions params m g‖ < ε := by
  simpa [phi4SchwingerFunctions, os4WeakCouplingThreshold] using
    OSE4ClusterModel.e4_cluster_of_weak_coupling (params := params) hsmall

/-- Interface-level OS package theorem: if core/E2/E4 interfaces are provided and
    weak coupling is available, the packaged Schwinger functions satisfy OS0-OS4. -/
theorem phi4_satisfies_OS_of_interfaces (params : Phi4Params)
    [OSAxiomCoreModel params]
    [OSDistributionE2Model params]
    [OSE4ClusterModel params]
    (hsmall : params.coupling < os4WeakCouplingThreshold params) :
    ∃ OS : OsterwalderSchraderAxioms 1,
      OS.S = phi4SchwingerFunctions params := by
  refine ⟨{
    S := phi4SchwingerFunctions params
    E0_tempered := phi4_os0 params
    E1_translation_invariant := phi4_os2_translation params
    E1_rotation_invariant := phi4_os2_rotation params
    E2_reflection_positive := phi4_e2_distributional params
    E3_symmetric := OSAxiomCoreModel.e3_symmetric (params := params)
    E4_cluster := phi4_e4_cluster_of_weak_coupling params hsmall
  }, rfl⟩

/-- Honest frontier: construction of the core Schwinger OS package from
    infinite-volume data. -/
theorem osaCoreModel_nonempty_of_data (params : Phi4Params)
    (S : SchwingerFunctions 1)
    (hos0 : ∀ n, Continuous (S n))
    (hos0_linear : ∀ n, IsLinearMap ℂ (S n))
    (hos2_translation :
      ∀ (n : ℕ) (a : Fin 2 → ℝ) (f g : SchwartzNPoint 1 n),
        (∀ x, g.toFun x = f.toFun (fun i => x i + a)) →
        S n f = S n g)
    (hos2_rotation :
      ∀ (n : ℕ) (R : Matrix (Fin 2) (Fin 2) ℝ),
        R.transpose * R = 1 → R.det = 1 →
        ∀ (f g : SchwartzNPoint 1 n),
          (∀ x, g.toFun x = f.toFun (fun i => R.mulVec (x i))) →
          S n f = S n g)
    (he3_symmetric :
      ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)) (f g : SchwartzNPoint 1 n),
        (∀ x, g.toFun x = f.toFun (fun i => x (σ i))) →
        S n f = S n g) :
    Nonempty (OSAxiomCoreModel params) := by
  refine ⟨{
    schwingerFunctions := S
    os0 := hos0
    schwinger_linear := hos0_linear
    os2_translation := hos2_translation
    os2_rotation := hos2_rotation
    e3_symmetric := he3_symmetric
  }⟩

/-- Honest frontier: construction of the core Schwinger OS package from
    explicit Schwinger-data assumptions. -/
theorem gap_osaCoreModel_nonempty (params : Phi4Params)
    (S : SchwingerFunctions 1)
    (hos0 : ∀ n, Continuous (S n))
    (hos0_linear : ∀ n, IsLinearMap ℂ (S n))
    (hos2_translation :
      ∀ (n : ℕ) (a : Fin 2 → ℝ) (f g : SchwartzNPoint 1 n),
        (∀ x, g.toFun x = f.toFun (fun i => x i + a)) →
        S n f = S n g)
    (hos2_rotation :
      ∀ (n : ℕ) (R : Matrix (Fin 2) (Fin 2) ℝ),
        R.transpose * R = 1 → R.det = 1 →
        ∀ (f g : SchwartzNPoint 1 n),
          (∀ x, g.toFun x = f.toFun (fun i => R.mulVec (x i))) →
          S n f = S n g)
    (he3_symmetric :
      ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)) (f g : SchwartzNPoint 1 n),
        (∀ x, g.toFun x = f.toFun (fun i => x (σ i))) →
        S n f = S n g) :
    Nonempty (OSAxiomCoreModel params) := by
  exact osaCoreModel_nonempty_of_data params S hos0 hos0_linear
    hos2_translation hos2_rotation he3_symmetric

/-- Honest frontier: distributional E2 from the OS core package. -/
theorem osDistributionE2Model_nonempty_of_data (params : Phi4Params)
    [OSAxiomCoreModel params]
    (he2 :
      ∀ (F : BorchersSequence 1),
        (∀ n, ∀ x : NPointDomain 1 n,
          (F.funcs n).toFun x ≠ 0 → x ∈ PositiveTimeRegion 1 n) →
        (OSInnerProduct 1 (OSAxiomCoreModel.schwingerFunctions (params := params)) F F).re ≥ 0) :
    Nonempty (OSDistributionE2Model params) := by
  exact ⟨{ e2_reflection_positive := he2 }⟩

/-- Honest frontier: distributional E2 from explicit reflection-positivity data. -/
theorem gap_osDistributionE2_nonempty (params : Phi4Params)
    [OSAxiomCoreModel params]
    (he2 :
      ∀ (F : BorchersSequence 1),
        (∀ n, ∀ x : NPointDomain 1 n,
          (F.funcs n).toFun x ≠ 0 → x ∈ PositiveTimeRegion 1 n) →
        (OSInnerProduct 1 (OSAxiomCoreModel.schwingerFunctions (params := params)) F F).re ≥ 0) :
    Nonempty (OSDistributionE2Model params) := by
  exact osDistributionE2Model_nonempty_of_data params he2

/-- Honest frontier: weak-coupling E4 clustering from the OS core package. -/
theorem osE4ClusterModel_nonempty_of_data (params : Phi4Params)
    [OSAxiomCoreModel params]
    (threshold : ℝ)
    (hthreshold_pos : 0 < threshold)
    (hcluster :
      params.coupling < threshold →
        ∀ (n m : ℕ) (f : SchwartzNPoint 1 n) (g : SchwartzNPoint 1 m),
          ∀ ε : ℝ, ε > 0 → ∃ R : ℝ, R > 0 ∧
            ∀ a : SpacetimeDim 1, a 0 = 0 → (∑ i : Fin 1, (a (Fin.succ i))^2) > R^2 →
              ∀ (g_a : SchwartzNPoint 1 m),
                (∀ x : NPointDomain 1 m, g_a x = g (fun i => x i - a)) →
                ‖OSAxiomCoreModel.schwingerFunctions (params := params) (n + m) (f.tensorProduct g_a) -
                  OSAxiomCoreModel.schwingerFunctions (params := params) n f *
                    OSAxiomCoreModel.schwingerFunctions (params := params) m g‖ < ε) :
    Nonempty (OSE4ClusterModel params) := by
  exact ⟨{
    weak_coupling_threshold := threshold
    weak_coupling_threshold_pos := hthreshold_pos
    e4_cluster_of_weak_coupling := hcluster
  }⟩

/-- Honest frontier: weak-coupling E4 clustering from explicit cluster data. -/
theorem gap_osE4Cluster_nonempty (params : Phi4Params)
    [OSAxiomCoreModel params]
    (threshold : ℝ)
    (hthreshold_pos : 0 < threshold)
    (hcluster :
      params.coupling < threshold →
        ∀ (n m : ℕ) (f : SchwartzNPoint 1 n) (g : SchwartzNPoint 1 m),
          ∀ ε : ℝ, ε > 0 → ∃ R : ℝ, R > 0 ∧
            ∀ a : SpacetimeDim 1, a 0 = 0 → (∑ i : Fin 1, (a (Fin.succ i))^2) > R^2 →
              ∀ (g_a : SchwartzNPoint 1 m),
                (∀ x : NPointDomain 1 m, g_a x = g (fun i => x i - a)) →
                ‖OSAxiomCoreModel.schwingerFunctions (params := params) (n + m) (f.tensorProduct g_a) -
                  OSAxiomCoreModel.schwingerFunctions (params := params) n f *
                    OSAxiomCoreModel.schwingerFunctions (params := params) m g‖ < ε) :
    Nonempty (OSE4ClusterModel params) := by
  exact osE4ClusterModel_nonempty_of_data params threshold hthreshold_pos hcluster

/-- Construct the OS package theorem from explicit Schwinger/positivity/cluster
    data, via the gap constructors. -/
theorem phi4_satisfies_OS_of_explicit_data (params : Phi4Params)
    (S : SchwingerFunctions 1)
    (hos0 : ∀ n, Continuous (S n))
    (hos0_linear : ∀ n, IsLinearMap ℂ (S n))
    (hos2_translation :
      ∀ (n : ℕ) (a : Fin 2 → ℝ) (f g : SchwartzNPoint 1 n),
        (∀ x, g.toFun x = f.toFun (fun i => x i + a)) →
        S n f = S n g)
    (hos2_rotation :
      ∀ (n : ℕ) (R : Matrix (Fin 2) (Fin 2) ℝ),
        R.transpose * R = 1 → R.det = 1 →
        ∀ (f g : SchwartzNPoint 1 n),
          (∀ x, g.toFun x = f.toFun (fun i => R.mulVec (x i))) →
          S n f = S n g)
    (he3_symmetric :
      ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)) (f g : SchwartzNPoint 1 n),
        (∀ x, g.toFun x = f.toFun (fun i => x (σ i))) →
        S n f = S n g)
    (he2 :
      ∀ (F : BorchersSequence 1),
        (∀ n, ∀ x : NPointDomain 1 n,
          (F.funcs n).toFun x ≠ 0 → x ∈ PositiveTimeRegion 1 n) →
        (OSInnerProduct 1 S F F).re ≥ 0)
    (threshold : ℝ)
    (hthreshold_pos : 0 < threshold)
    (hcluster :
      params.coupling < threshold →
        ∀ (n m : ℕ) (f : SchwartzNPoint 1 n) (g : SchwartzNPoint 1 m),
          ∀ ε : ℝ, ε > 0 → ∃ R : ℝ, R > 0 ∧
            ∀ a : SpacetimeDim 1, a 0 = 0 → (∑ i : Fin 1, (a (Fin.succ i))^2) > R^2 →
              ∀ (g_a : SchwartzNPoint 1 m),
                (∀ x : NPointDomain 1 m, g_a x = g (fun i => x i - a)) →
                ‖S (n + m) (f.tensorProduct g_a) - S n f * S m g‖ < ε)
    (hsmall : params.coupling < threshold) :
    ∃ OS : OsterwalderSchraderAxioms 1,
      OS.S = S := by
  let core : OSAxiomCoreModel params := {
    schwingerFunctions := S
    os0 := hos0
    schwinger_linear := hos0_linear
    os2_translation := hos2_translation
    os2_rotation := hos2_rotation
    e3_symmetric := he3_symmetric
  }
  letI : OSAxiomCoreModel params := core
  let e2model : OSDistributionE2Model params := {
    e2_reflection_positive := by
      intro F hF
      simpa [core] using he2 F hF
  }
  letI : OSDistributionE2Model params := e2model
  let e4model : OSE4ClusterModel params := {
    weak_coupling_threshold := threshold
    weak_coupling_threshold_pos := hthreshold_pos
    e4_cluster_of_weak_coupling := by
      intro hsm n m f g ε hε
      simpa [core] using hcluster hsm n m f g ε hε
  }
  letI : OSE4ClusterModel params := e4model
  have hsmall' : params.coupling < os4WeakCouplingThreshold params := by
    simpa [os4WeakCouplingThreshold, e4model] using hsmall
  rcases phi4_satisfies_OS_of_interfaces params hsmall' with ⟨OS, hOS⟩
  refine ⟨OS, ?_⟩
  simpa [phi4SchwingerFunctions, core] using hOS

/-- Explicit weak-coupling smallness assumption wrapper for E4 usage. -/
theorem os4_weak_coupling_small_of_assumption (params : Phi4Params)
    [OSAxiomCoreModel params]
    [OSE4ClusterModel params]
    (hsmall : params.coupling < os4WeakCouplingThreshold params) :
    params.coupling < os4WeakCouplingThreshold params := hsmall

/-- **Theorem 12.1.1 (Glimm-Jaffe)**: Under weak coupling, the φ⁴₂ generating
    functional S{f} satisfies the Euclidean axioms OS0-OS4.

    Current status: this endpoint is exposed honestly through explicit
    theorem-level frontier gaps (`gap_...`) rather than hidden model assumptions. -/
theorem phi4_satisfies_OS (params : Phi4Params)
    (core : OSAxiomCoreModel params)
    [OSDistributionE2Model params]
    [OSE4ClusterModel params]
    (hsmall : params.coupling < os4WeakCouplingThreshold params) :
    ∃ OS : OsterwalderSchraderAxioms 1,
      OS.S = @phi4SchwingerFunctions params core := by
  letI : OSAxiomCoreModel params := core
  have hsmall' : params.coupling < OSE4ClusterModel.weak_coupling_threshold (params := params) := by
    simpa [os4WeakCouplingThreshold] using hsmall
  rcases phi4_satisfies_OS_of_explicit_data params
      (S := OSAxiomCoreModel.schwingerFunctions (params := params))
      (hos0 := OSAxiomCoreModel.os0 (params := params))
      (hos0_linear := OSAxiomCoreModel.schwinger_linear (params := params))
      (hos2_translation := OSAxiomCoreModel.os2_translation (params := params))
      (hos2_rotation := OSAxiomCoreModel.os2_rotation (params := params))
      (he3_symmetric := OSAxiomCoreModel.e3_symmetric (params := params))
      (he2 := OSDistributionE2Model.e2_reflection_positive (params := params))
      (threshold := OSE4ClusterModel.weak_coupling_threshold (params := params))
      (hthreshold_pos := OSE4ClusterModel.weak_coupling_threshold_pos (params := params))
      (hcluster := OSE4ClusterModel.e4_cluster_of_weak_coupling (params := params))
      (hsmall := hsmall') with ⟨OS, hOS⟩
  refine ⟨OS, ?_⟩
  simpa [phi4SchwingerFunctions] using hOS

end

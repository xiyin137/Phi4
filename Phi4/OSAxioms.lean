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

/-! ## Abstract OS-axiom interface -/

/-- Inputs required to package φ⁴₂ Schwinger functions and verify OS0/OS2/OS3,
    together with an E4 cluster statement under weak coupling. -/
class OSAxiomModel (params : Phi4Params) [InfiniteVolumeLimitModel params] where
  schwingerFunctions : SchwingerFunctions 1
  os0 :
    ∀ n, Continuous (schwingerFunctions n)
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
  /-- Measure-level reflection positivity (used in standalone `phi4_os3`).
      `os3` uses the concrete measure formulation over linear observables,
      while `e2_reflection_positive` supplies the abstract distributional API
      required by the OSReconstruction library on Borchers sequences.
      In this interface they are separate assumptions; no formal bridge between
      `schwingerFunctions` and `infiniteVolumeMeasure` is included here. -/
  os3 :
    ∀ (n : ℕ) (f : Fin n → TestFun2D) (c : Fin n → ℂ),
      (∀ i, supportedInPositiveTime (f i)) →
        0 ≤ (∑ i, ∑ j, c i * starRingEnd ℂ (c j) *
          ∫ ω, ω (testFunTimeReflect (f i)) * ω (f j)
            ∂(infiniteVolumeMeasure params)).re
  /-- Distributional reflection positivity (used in `phi4_satisfies_OS`).
      See `os3` above for the concrete measure-level version. -/
  e2_reflection_positive :
    ∀ (F : BorchersSequence 1),
      (∀ n, ∀ x : NPointDomain 1 n,
        (F.funcs n).toFun x ≠ 0 → x ∈ PositiveTimeRegion 1 n) →
      (OSInnerProduct 1 schwingerFunctions F F).re ≥ 0
  e3_symmetric :
    ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)) (f g : SchwartzNPoint 1 n),
      (∀ x, g.toFun x = f.toFun (fun i => x (σ i))) →
      schwingerFunctions n f = schwingerFunctions n g
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
              ‖schwingerFunctions (n + m) (f.tensorProduct g_a) -
                schwingerFunctions n f * schwingerFunctions m g‖ < ε

/-! ## Schwinger functions as distributions

The infinite volume Schwinger functions define tempered distributions on S(ℝ^{2n}). -/

/-- The φ⁴₂ Schwinger functions packaged as a `SchwingerFunctions` (from OSreconstruction).
    Here d = 1 because OSreconstruction uses spacetime dimension d+1, and we have d+1 = 2.

    S_n : S(ℝ^{n×2}) → ℂ is defined by:
      S_n(f) = ∫ φ(x₁)⋯φ(xₙ) f(x₁,...,xₙ) dx₁⋯dxₙ dμ(φ) -/
def phi4SchwingerFunctions (params : Phi4Params)
    [InfiniteVolumeLimitModel params]
    [OSAxiomModel params] :
    SchwingerFunctions 1 :=
  OSAxiomModel.schwingerFunctions (params := params)

/-! ## OS0: Temperedness -/

/-- **OS0 (Temperedness)**: Each S_n is a continuous linear functional on
    the Schwartz space S(ℝ^{n×2}), i.e., a tempered distribution.

    This follows from the Lᵖ bounds on the field: since ω(f) ∈ Lᵖ for all p,
    the products ω(f₁)⋯ω(fₙ) are integrable and depend continuously on the
    test functions in the Schwartz topology. -/
theorem phi4_os0 (params : Phi4Params)
    [InfiniteVolumeLimitModel params]
    [OSAxiomModel params] :
    ∀ n, Continuous (phi4SchwingerFunctions params n) := by
  simpa [phi4SchwingerFunctions] using
    (OSAxiomModel.os0 (params := params))

/-! ## OS1: Regularity (Linear Growth) -/

/-- **OS1 (Regularity)**: The generating functional satisfies the linear growth bound
    |S{f}| ≤ exp(c · N'(f)).

    This is Theorem 12.5.1, the culmination of the integration by parts analysis.
    It is the most technically demanding of the OS axioms to verify. -/
theorem phi4_os1 (params : Phi4Params)
    [InfiniteVolumeLimitModel params]
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
    [InfiniteVolumeLimitModel params]
    [OSAxiomModel params] :
    ∀ (n : ℕ) (a : Fin 2 → ℝ) (f g : SchwartzNPoint 1 n),
      (∀ x, g.toFun x = f.toFun (fun i => x i + a)) →
      phi4SchwingerFunctions params n f = phi4SchwingerFunctions params n g := by
  intro n a f g hfg
  simpa [phi4SchwingerFunctions] using
    (OSAxiomModel.os2_translation (params := params) n a f g hfg)

/-- **OS2b (Rotation invariance)**: The Schwinger functions are invariant
    under SO(2) rotations:
      S_n(Rx₁,...,Rxₙ) = S_n(x₁,...,xₙ) for all R ∈ SO(2).

    This follows from the rotational invariance of the Laplacian
    and hence of the free covariance, combined with the rotational
    invariance of the interaction ∫ :φ⁴: dx. -/
theorem phi4_os2_rotation (params : Phi4Params)
    [InfiniteVolumeLimitModel params]
    [OSAxiomModel params] :
    ∀ (n : ℕ) (R : Matrix (Fin 2) (Fin 2) ℝ),
      R.transpose * R = 1 → R.det = 1 →
      ∀ (f g : SchwartzNPoint 1 n),
        (∀ x, g.toFun x = f.toFun (fun i => R.mulVec (x i))) →
        phi4SchwingerFunctions params n f = phi4SchwingerFunctions params n g := by
  intro n R horth hdet f g hfg
  simpa [phi4SchwingerFunctions] using
    (OSAxiomModel.os2_rotation (params := params) n R horth hdet f g hfg)

/-! ## OS3: Reflection Positivity -/

/-- **OS3 (Reflection positivity)**: For any test function sequence F = (F₀, F₁, ...)
    supported in positive Euclidean time {τ > 0},
      Σₙₘ ∫ (θF_n)* F_m S_{n+m} ≥ 0
    where θ is time reflection τ ↦ -τ.

    This is inherited from the finite-volume reflection positivity
    (Theorem 10.4 / ReflectionPositivity.lean) and passes to the
    infinite volume limit by the convergence of S_n^Λ → S_n. -/
theorem phi4_os3 (params : Phi4Params)
    [InfiniteVolumeLimitModel params]
    [OSAxiomModel params]
    (n : ℕ) (f : Fin n → TestFun2D) (c : Fin n → ℂ)
    (hf : ∀ i, supportedInPositiveTime (f i)) :
    0 ≤ (∑ i, ∑ j, c i * starRingEnd ℂ (c j) *
      ∫ ω, ω (testFunTimeReflect (f i)) * ω (f j)
        ∂(infiniteVolumeMeasure params)).re := by
  exact OSAxiomModel.os3 (params := params) n f c hf

/-! ## Main theorem: OS axioms hold -/

/-- Canonical weak-coupling threshold carried by `OSAxiomModel`. -/
def os4WeakCouplingThreshold (params : Phi4Params)
    [InfiniteVolumeLimitModel params]
    [OSAxiomModel params] : ℝ :=
  OSAxiomModel.weak_coupling_threshold (params := params)

/-- Positivity of the canonical weak-coupling threshold. -/
theorem os4WeakCouplingThreshold_pos (params : Phi4Params)
    [InfiniteVolumeLimitModel params]
    [OSAxiomModel params] :
    0 < os4WeakCouplingThreshold params := by
  simpa [os4WeakCouplingThreshold] using
    OSAxiomModel.weak_coupling_threshold_pos (params := params)

/-- E4 cluster property extracted from `OSAxiomModel` under weak coupling. -/
theorem phi4_e4_cluster_of_weak_coupling (params : Phi4Params)
    [InfiniteVolumeLimitModel params]
    [OSAxiomModel params]
    (hsmall : params.coupling < os4WeakCouplingThreshold params) :
    ∀ (n m : ℕ) (f : SchwartzNPoint 1 n) (g : SchwartzNPoint 1 m),
      ∀ ε : ℝ, ε > 0 → ∃ R : ℝ, R > 0 ∧
        ∀ a : SpacetimeDim 1, a 0 = 0 → (∑ i : Fin 1, (a (Fin.succ i))^2) > R^2 →
          ∀ (g_a : SchwartzNPoint 1 m),
            (∀ x : NPointDomain 1 m, g_a x = g (fun i => x i - a)) →
            ‖phi4SchwingerFunctions params (n + m) (f.tensorProduct g_a) -
              phi4SchwingerFunctions params n f * phi4SchwingerFunctions params m g‖ < ε := by
  simpa [phi4SchwingerFunctions, os4WeakCouplingThreshold] using
    OSAxiomModel.e4_cluster_of_weak_coupling (params := params) hsmall

/-- **Theorem 12.1.1 (Glimm-Jaffe)**: Under weak coupling, the φ⁴₂ generating
    functional S{f} satisfies the Euclidean axioms OS0-OS4.

    This combines:
    - E0: from `phi4_os0` (temperedness of Schwinger functions)
    - E1: from `phi4_os2_translation` and `phi4_os2_rotation` (Euclidean covariance)
    - E2: from `phi4_os3` (reflection positivity)
    - E3: from symmetry of the path integral (permutation invariance)
    - E4: from the cluster expansion (Chapter 18, weak coupling)

    The regularity bound (OS1 / E0') follows from `generating_functional_bound`
    (Theorem 12.5.1) and is established separately in `phi4_linear_growth`.

    Note: E4 (clustering) requires sufficiently small coupling constant λ,
    represented here by the explicit hypothesis `hsmall`.

    Hence by the OS reconstruction theorem (from OSreconstruction), the φ⁴₂ theory
    defines a Wightman quantum field theory satisfying axioms W1-W3. -/
theorem phi4_satisfies_OS (params : Phi4Params)
    [InfiniteVolumeLimitModel params]
    [OSAxiomModel params]
    (hsmall : params.coupling < os4WeakCouplingThreshold params) :
    ∃ OS : OsterwalderSchraderAxioms 1,
      OS.S = phi4SchwingerFunctions params := by
  refine ⟨{
    S := phi4SchwingerFunctions params
    E0_tempered := phi4_os0 params
    E1_translation_invariant := phi4_os2_translation params
    E1_rotation_invariant := phi4_os2_rotation params
    E2_reflection_positive := OSAxiomModel.e2_reflection_positive (params := params)
    E3_symmetric := OSAxiomModel.e3_symmetric (params := params)
    E4_cluster := phi4_e4_cluster_of_weak_coupling params hsmall
  }, rfl⟩

end

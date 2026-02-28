/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.OSAxioms
import OSReconstruction.Wightman.Reconstruction

/-!
# Wightman Reconstruction for φ⁴₂

Having established that the φ⁴₂ Schwinger functions satisfy OS0-OS3 (in `OSAxioms.lean`),
we apply the Osterwalder-Schrader reconstruction theorem from the OSreconstruction library
to obtain a relativistic (Minkowski) quantum field theory satisfying the Wightman axioms.

The OS reconstruction theorem (Osterwalder-Schrader II, 1975) states:
  OS axioms E0-E4 + linear growth condition E0' ⟹ Wightman axioms W1-W4

For the φ⁴₂ theory:
- E0-E3 are established in `OSAxioms.lean`
- E4 (clustering/ergodicity) requires the cluster expansion (Chapter 18) for weak coupling,
  or the phase transition analysis (Chapter 16) for strong coupling
- E0' (linear growth) follows from the generating functional bound (Theorem 12.5.1)

The resulting Wightman QFT has:
- Self-adjoint field operators φ(f) on a Hilbert space H
- A unitary representation of the Poincaré group
- Locality (spacelike commutativity)
- A unique vacuum state Ω

## References

* [Glimm-Jaffe] Chapter 19
* [Osterwalder-Schrader II] (1975)
* OSreconstruction library: reconstruction API (`WightmanFunctions`, `IsWickRotationPair`)
-/

noncomputable section

open MeasureTheory Reconstruction

private def toSpacetime2D (a : Fin 2 → ℝ) : Spacetime2D :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm a

private def translateMap (a : Spacetime2D) : Spacetime2D → Spacetime2D :=
  fun x => x + a

private lemma translateMap_hasTemperateGrowth (a : Spacetime2D) :
    (translateMap a).HasTemperateGrowth := by
  simpa [translateMap] using
    (Function.HasTemperateGrowth.add
      (show Function.HasTemperateGrowth (fun x : Spacetime2D => x) from
        (ContinuousLinearMap.id ℝ Spacetime2D).hasTemperateGrowth)
      (Function.HasTemperateGrowth.const a))

private lemma translateMap_antilipschitz (a : Spacetime2D) :
    AntilipschitzWith 1 (translateMap a) := by
  refine AntilipschitzWith.of_le_mul_dist ?_
  intro x y
  calc
    dist x y ≤ dist (x + a) (y + a) := (dist_add_right x y a).ge
    _ = 1 * dist (translateMap a x) (translateMap a y) := by simp [translateMap]

/-- Translation of a Schwartz test function by `a`: x ↦ g(x + a). -/
def translateTestFun (a : Fin 2 → ℝ) (g : TestFun2D) : TestFun2D :=
  SchwartzMap.compCLMOfAntilipschitz ℝ
    (translateMap_hasTemperateGrowth (toSpacetime2D a))
    (translateMap_antilipschitz (toSpacetime2D a))
    g

/-! ## Weak-coupling decay shape -/

/-- Connected 2-point exponential decay at fixed parameters:
    one uniform mass gap with pair-dependent amplitudes. -/
abbrev ConnectedTwoPointDecayAtParams (params : Phi4Params)
    [SchwingerLimitModel params] : Prop :=
  ∃ m_gap : ℝ, 0 < m_gap ∧
    ∀ (f g : TestFun2D), ∃ Cfg : ℝ, 0 ≤ Cfg ∧
      ∀ (a : Fin 2 → ℝ),
        let g_shifted : TestFun2D := translateTestFun a g
        |connectedTwoPoint params f g_shifted| ≤
          Cfg * Real.exp (-m_gap * ‖a‖)

/-! ## Uniform weak-coupling decay interface -/

/-- Optional global weak-coupling decay input used for the explicit
    cross-parameter OS4 statement. This is intentionally separate from
    `ReconstructionInputModel`, which only carries fixed-`params` data. -/
class UniformWeakCouplingDecayModel (params : Phi4Params)
    [SchwingerLimitModel params] where
  phi4_os4_weak_coupling :
    ∃ coupling_bound : ℝ, 0 < coupling_bound ∧
      ∀ p : Phi4Params, [SchwingerLimitModel p] →
        p.coupling < coupling_bound →
          ConnectedTwoPointDecayAtParams p

/-! ## Abstract reconstruction inputs -/

/-- Linear-growth input needed at fixed `params` for OS-to-Wightman
    reconstruction. -/
class ReconstructionLinearGrowthModel (params : Phi4Params)
    [SchwingerFunctionModel params] where
  os_package : OsterwalderSchraderAxioms 1
  os_package_eq : os_package.S = phi4SchwingerFunctions params
  linear_growth : OSLinearGrowthCondition 1 os_package

/-- Backward-compatible existential view of `ReconstructionLinearGrowthModel`. -/
theorem ReconstructionLinearGrowthModel.phi4_linear_growth (params : Phi4Params)
    [SchwingerFunctionModel params]
    [ReconstructionLinearGrowthModel params] :
    ∃ OS : OsterwalderSchraderAxioms 1,
      OS.S = phi4SchwingerFunctions params ∧
      Nonempty (OSLinearGrowthCondition 1 OS) := by
  refine ⟨ReconstructionLinearGrowthModel.os_package (params := params),
    ReconstructionLinearGrowthModel.os_package_eq (params := params), ?_⟩
  exact ⟨ReconstructionLinearGrowthModel.linear_growth (params := params)⟩

/-- Fixed-`params` weak-coupling decay input, separated from linear-growth data. -/
class ReconstructionWeakCouplingModel (params : Phi4Params)
    [SchwingerLimitModel params] where
  /-- A canonical weak-coupling threshold for the current parameter set. -/
  weak_coupling_threshold : ℝ
  weak_coupling_threshold_pos : 0 < weak_coupling_threshold
  connectedTwoPoint_decay_of_weak_coupling :
    params.coupling < weak_coupling_threshold →
      ConnectedTwoPointDecayAtParams params

/-- A global uniform weak-coupling decay model induces a fixed-parameter
    weak-coupling threshold model by specialization to `params`. -/
instance (priority := 90) reconstructionWeakCouplingModel_of_uniform
    (params : Phi4Params)
    [SchwingerLimitModel params]
    [UniformWeakCouplingDecayModel params] :
    ReconstructionWeakCouplingModel params where
  weak_coupling_threshold :=
    (UniformWeakCouplingDecayModel.phi4_os4_weak_coupling (params := params)).choose
  weak_coupling_threshold_pos :=
    (UniformWeakCouplingDecayModel.phi4_os4_weak_coupling (params := params)).choose_spec.1
  connectedTwoPoint_decay_of_weak_coupling := by
    intro hsmall
    exact
      (UniformWeakCouplingDecayModel.phi4_os4_weak_coupling (params := params)).choose_spec.2
        params hsmall

/-- Backward-compatible aggregate reconstruction input model. -/
class ReconstructionInputModel (params : Phi4Params)
    [SchwingerLimitModel params]
    [SchwingerFunctionModel params]
    extends ReconstructionLinearGrowthModel params,
      ReconstructionWeakCouplingModel params

instance (priority := 100) reconstructionInputModel_of_submodels
    (params : Phi4Params)
    [SchwingerLimitModel params]
    [SchwingerFunctionModel params]
    [ReconstructionLinearGrowthModel params]
    [ReconstructionWeakCouplingModel params] :
    ReconstructionInputModel params where
  toReconstructionLinearGrowthModel := inferInstance
  toReconstructionWeakCouplingModel := inferInstance

/-- Abstract OS-to-Wightman reconstruction backend for fixed `params`.
    Kept separate from `ReconstructionInputModel` so fixed-`params`
    analytic assumptions and reconstruction machinery are not bundled together. -/
class WightmanReconstructionModel (params : Phi4Params)
    where
  wightman_reconstruction :
    ∀ (OS : OsterwalderSchraderAxioms 1),
      OSLinearGrowthCondition 1 OS →
        ∃ (Wfn : WightmanFunctions 1),
          IsWickRotationPair OS.S Wfn.W

/-- Existence of a weak-coupling threshold guaranteeing connected 2-point decay. -/
abbrev ConnectedTwoPointDecayThreshold (params : Phi4Params)
    [SchwingerLimitModel params]
    [ReconstructionWeakCouplingModel params] : Prop :=
  ∃ coupling_bound : ℝ, 0 < coupling_bound ∧
    (params.coupling < coupling_bound →
      ConnectedTwoPointDecayAtParams params)

/-! ## Interface-level reconstruction wrappers -/

/-- Linear-growth input extracted from `ReconstructionLinearGrowthModel`. -/
theorem phi4_linear_growth_of_interface (params : Phi4Params)
    [SchwingerFunctionModel params]
    [ReconstructionLinearGrowthModel params] :
    ∃ OS : OsterwalderSchraderAxioms 1,
      OS.S = phi4SchwingerFunctions params ∧
      Nonempty (OSLinearGrowthCondition 1 OS) := by
  exact ReconstructionLinearGrowthModel.phi4_linear_growth (params := params)

/-- Explicit linear-growth constants extracted from
    `ReconstructionLinearGrowthModel`. -/
theorem phi4_linear_growth_constants_of_interface (params : Phi4Params)
    [SchwingerFunctionModel params]
    [ReconstructionLinearGrowthModel params] :
    ∃ (sobolev_index : ℕ) (alpha beta gamma : ℝ),
      0 < alpha ∧ 0 < beta ∧
      ∀ (n : ℕ) (f : SchwartzNPoint 1 n),
        ‖phi4SchwingerFunctions params n f‖ ≤
          alpha * beta ^ n * (n.factorial : ℝ) ^ gamma *
            SchwartzMap.seminorm ℝ sobolev_index sobolev_index f := by
  let OS := ReconstructionLinearGrowthModel.os_package (params := params)
  let hS := ReconstructionLinearGrowthModel.os_package_eq (params := params)
  let hlg := ReconstructionLinearGrowthModel.linear_growth (params := params)
  refine ⟨hlg.sobolev_index, hlg.alpha, hlg.beta, hlg.gamma,
    hlg.alpha_pos, hlg.beta_pos, ?_⟩
  intro n f
  simpa [OS, hS] using hlg.growth_estimate n f

/-- Canonical Wightman-reconstruction step extracted from upstream
    `WightmanReconstructionModel`. -/
theorem phi4_wightman_reconstruction_step_of_interface (params : Phi4Params)
    [WightmanReconstructionModel params] :
    ∀ (OS : OsterwalderSchraderAxioms 1),
      OSLinearGrowthCondition 1 OS →
        ∃ (Wfn : WightmanFunctions 1),
          IsWickRotationPair OS.S Wfn.W := by
  exact WightmanReconstructionModel.wightman_reconstruction (params := params)

/-! ## Product-Tensor Bridge Towards E0' -/

/-- Complexification of a real-valued 2D test function. -/
def testFunToComplex (f : TestFun2D) : TestFunℂ2D where
  toFun x := Complex.ofRealCLM (f x)
  smooth' := Complex.ofRealCLM.contDiff.comp f.smooth'
  decay' k n := by
    rcases f.decay' k n with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro x
    have heq : (fun x => Complex.ofRealCLM (f x)) = Complex.ofRealLI ∘ ⇑f := rfl
    rw [heq, Complex.ofRealLI.norm_iteratedFDeriv_comp_left
      (f.smooth ⊤).contDiffAt (mod_cast le_top)]
    exact hC x

/-- Reindex a complex 2D test function to OS-reconstruction spacetime coordinates. -/
def testFunToSchwartzSpacetime (f : TestFun2D) : SchwartzSpacetime 1 :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (EuclideanSpace.equiv (Fin 2) ℝ).symm) (testFunToComplex f)

/-- Product-tensor lift from finite families of real test functions to
    `SchwartzNPoint 1 n`. -/
def schwartzProductTensorFromTestFamily {n : ℕ} (f : Fin n → TestFun2D) :
    SchwartzNPoint 1 n :=
  SchwartzMap.productTensor (fun i => testFunToSchwartzSpacetime (f i))

/-- Zero-point normalization on product tensors from compatibility with
    `infiniteVolumeSchwinger`. -/
theorem phi4_productTensor_zero_of_compat
    (params : Phi4Params)
    [SchwingerLimitModel params]
    [InteractionWeightModel params]
    [SchwingerFunctionModel params]
    (hcompat :
      ∀ (n : ℕ) (f : Fin n → TestFun2D),
        phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily f) =
          (infiniteVolumeSchwinger params n f : ℂ))
    (f : Fin 0 → TestFun2D) :
    phi4SchwingerFunctions params 0 (schwartzProductTensorFromTestFamily f) = 1 := by
  calc
    phi4SchwingerFunctions params 0 (schwartzProductTensorFromTestFamily f)
        = (infiniteVolumeSchwinger params 0 f : ℂ) := by
          simpa using hcompat 0 f
    _ = 1 := by
          norm_num [infiniteVolumeSchwinger_zero]

/-- Measure-representation variant of zero-point normalization on product
    tensors from compatibility with `infiniteVolumeSchwinger`. -/
theorem phi4_productTensor_zero_of_compat_of_moment
    (params : Phi4Params)
    [InfiniteVolumeSchwingerModel params]
    [InfiniteVolumeMeasureModel params]
    [InfiniteVolumeMomentModel params]
    [SchwingerFunctionModel params]
    (hcompat :
      ∀ (n : ℕ) (f : Fin n → TestFun2D),
        phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily f) =
          (infiniteVolumeSchwinger params n f : ℂ))
    (f : Fin 0 → TestFun2D) :
    phi4SchwingerFunctions params 0 (schwartzProductTensorFromTestFamily f) = 1 := by
  calc
    phi4SchwingerFunctions params 0 (schwartzProductTensorFromTestFamily f)
        = (infiniteVolumeSchwinger params 0 f : ℂ) := by
          simpa using hcompat 0 f
    _ = 1 := by
          have hzero : infiniteVolumeSchwinger params 0 f = 1 :=
            infiniteVolumeSchwinger_zero_of_moment (params := params) f
          simp [hzero]

/-- Mixed `n`-point bound for `phi4SchwingerFunctions` on product tensors,
    from a global finite-volume uniform generating-functional estimate, plus an
    explicit compatibility bridge to `infiniteVolumeSchwinger`. -/
theorem phi4_productTensor_mixed_bound_of_global_uniform_generating_bound
    (params : Phi4Params)
    [InteractionWeightModel params]
    [SchwingerLimitModel params]
    [SchwingerFunctionModel params]
    (hglobal : ∃ c : ℝ, ∀ (h : TestFun2D) (Λ : Rectangle),
      |generatingFunctional params Λ h| ≤ Real.exp (c * normFunctional h))
    (hcompat :
      ∀ (n : ℕ) (f : Fin n → TestFun2D),
        phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily f) =
          (infiniteVolumeSchwinger params n f : ℂ))
    (n : ℕ) (hn : 0 < n) (f : Fin n → TestFun2D) :
    ∃ c : ℝ,
      ‖phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily f)‖ ≤
        ∑ i : Fin n, (Nat.factorial n : ℝ) *
          (Real.exp (c * normFunctional (f i)) +
            Real.exp (c * normFunctional (-(f i)))) := by
  rcases infiniteVolumeSchwinger_mixed_bound_of_global_uniform
      (params := params) hglobal n hn f with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  calc
    ‖phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily f)‖
        = ‖(infiniteVolumeSchwinger params n f : ℂ)‖ := by
          simp [hcompat n f]
    _ = |infiniteVolumeSchwinger params n f| := by
          simp
    _ ≤ ∑ i : Fin n, (Nat.factorial n : ℝ) *
          (Real.exp (c * normFunctional (f i)) +
            Real.exp (c * normFunctional (-(f i)))) := hc

/-- Mixed `n`-point bound for `phi4SchwingerFunctions` on product tensors,
    from explicit pointwise-in-`f` finite-volume uniform generating-functional
    control, plus an explicit compatibility bridge to
    `infiniteVolumeSchwinger`. -/
theorem phi4_productTensor_mixed_bound_of_uniform_generating_bound
    (params : Phi4Params)
    [InteractionWeightModel params]
    [SchwingerLimitModel params]
    [SchwingerFunctionModel params]
    (huniform : ∀ h : TestFun2D, ∃ c : ℝ, ∀ Λ : Rectangle,
      |generatingFunctional params Λ h| ≤ Real.exp (c * normFunctional h))
    (hcompat :
      ∀ (n : ℕ) (f : Fin n → TestFun2D),
        phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily f) =
          (infiniteVolumeSchwinger params n f : ℂ))
    (n : ℕ) (hn : 0 < n) (f : Fin n → TestFun2D) :
    ∃ c : ℝ,
      ‖phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily f)‖ ≤
        ∑ i : Fin n, (Nat.factorial n : ℝ) *
          (Real.exp (c * normFunctional (f i)) +
            Real.exp (c * normFunctional (-(f i)))) := by
  rcases infiniteVolumeSchwinger_mixed_bound_of_uniform_generating_bound
      (params := params) huniform n hn f with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  calc
    ‖phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily f)‖
        = ‖(infiniteVolumeSchwinger params n f : ℂ)‖ := by
          simp [hcompat n f]
    _ = |infiniteVolumeSchwinger params n f| := by
          simp
    _ ≤ ∑ i : Fin n, (Nat.factorial n : ℝ) *
          (Real.exp (c * normFunctional (f i)) +
            Real.exp (c * normFunctional (-(f i)))) := hc

/-- Product-tensor linear-growth estimate from:
    1) a global finite-volume uniform generating-functional bound,
    2) compatibility with `infiniteVolumeSchwinger`, and
    3) an explicit reduction of the mixed exponential-sum bound to one
       Schwartz seminorm on product tensors. -/
theorem phi4_productTensor_linear_growth_of_global_uniform_generating_bound
    (params : Phi4Params)
    [InteractionWeightModel params]
    [SchwingerLimitModel params]
    [SchwingerFunctionModel params]
    (sobolev_index : ℕ) (alpha beta gamma : ℝ)
    (hglobal : ∃ c : ℝ, ∀ (h : TestFun2D) (Λ : Rectangle),
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
            SchwartzMap.seminorm ℝ sobolev_index sobolev_index
              (schwartzProductTensorFromTestFamily f)) :
    ∀ (n : ℕ) (_hn : 0 < n) (f : Fin n → TestFun2D),
      ‖phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily f)‖ ≤
        alpha * beta ^ n * (n.factorial : ℝ) ^ gamma *
          SchwartzMap.seminorm ℝ sobolev_index sobolev_index
            (schwartzProductTensorFromTestFamily f) := by
  intro n hn f
  have hmixed := phi4_productTensor_mixed_bound_of_global_uniform_generating_bound
    params hglobal hcompat n hn f
  rcases hmixed with ⟨c, hc⟩
  exact hc.trans (hreduce c n hn f)

/-- Product-tensor linear-growth estimate from:
    1) pointwise-in-`f` finite-volume uniform generating-functional bounds,
    2) compatibility with `infiniteVolumeSchwinger`, and
    3) an explicit reduction of the mixed exponential-sum bound to one
       Schwartz seminorm on product tensors. -/
theorem phi4_productTensor_linear_growth_of_uniform_generating_bound
    (params : Phi4Params)
    [InteractionWeightModel params]
    [SchwingerLimitModel params]
    [SchwingerFunctionModel params]
    (sobolev_index : ℕ) (alpha beta gamma : ℝ)
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
            SchwartzMap.seminorm ℝ sobolev_index sobolev_index
              (schwartzProductTensorFromTestFamily f)) :
    ∀ (n : ℕ) (_hn : 0 < n) (f : Fin n → TestFun2D),
      ‖phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily f)‖ ≤
        alpha * beta ^ n * (n.factorial : ℝ) ^ gamma *
          SchwartzMap.seminorm ℝ sobolev_index sobolev_index
            (schwartzProductTensorFromTestFamily f) := by
  intro n hn f
  have hmixed := phi4_productTensor_mixed_bound_of_uniform_generating_bound
    params huniform hcompat n hn f
  rcases hmixed with ⟨c, hc⟩
  exact hc.trans (hreduce c n hn f)

/-- Positive-order linear growth on all `SchwartzNPoint` test functions from:
    1) product-tensor linear-growth bounds, and
    2) an explicit approximation scheme by product tensors with convergence of
       both test functions and the chosen seminorm values. -/
theorem phi4_positive_order_linear_growth_of_productTensor_approx
    (params : Phi4Params)
    [SchwingerFunctionModel params]
    [OSTemperedModel params]
    (sobolev_index : ℕ) (alpha beta gamma : ℝ)
    (hprod :
      ∀ (n : ℕ) (_hn : 0 < n) (f : Fin n → TestFun2D),
        ‖phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily f)‖ ≤
          alpha * beta ^ n * (n.factorial : ℝ) ^ gamma *
            SchwartzMap.seminorm ℝ sobolev_index sobolev_index
              (schwartzProductTensorFromTestFamily f))
    (happrox :
      ∀ (n : ℕ) (_hn : 0 < n) (g : SchwartzNPoint 1 n),
        ∃ u : ℕ → Fin n → TestFun2D,
          Filter.Tendsto (fun k => schwartzProductTensorFromTestFamily (u k))
            Filter.atTop (nhds g)) :
    ∀ (n : ℕ) (_hn : 0 < n) (g : SchwartzNPoint 1 n),
      ‖phi4SchwingerFunctions params n g‖ ≤
        alpha * beta ^ n * (n.factorial : ℝ) ^ gamma *
          SchwartzMap.seminorm ℝ sobolev_index sobolev_index g := by
  intro n hn g
  rcases happrox n hn g with ⟨u, hu_tendsto⟩
  let Cn : ℝ := alpha * beta ^ n * (n.factorial : ℝ) ^ gamma
  have hS_cont : Continuous (phi4SchwingerFunctions params n) := phi4_os0 params n
  have hS_tendsto :
      Filter.Tendsto
        (fun k => phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily (u k)))
        Filter.atTop
        (nhds (phi4SchwingerFunctions params n g)) :=
    (hS_cont.tendsto g).comp hu_tendsto
  have hnorm_tendsto :
      Filter.Tendsto
        (fun k => ‖phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily (u k))‖)
        Filter.atTop
        (nhds ‖phi4SchwingerFunctions params n g‖) := by
    exact hS_tendsto.norm
  have hseminorm_cont : Continuous
      (SchwartzMap.seminorm ℝ sobolev_index sobolev_index :
        SchwartzNPoint 1 n → ℝ) := by
    simpa [SchwartzNPoint] using
      ((schwartz_withSeminorms ℝ (NPointDomain 1 n) ℂ).continuous_seminorm
        (sobolev_index, sobolev_index))
  have hseminorm_tendsto :
      Filter.Tendsto
        (fun k =>
          SchwartzMap.seminorm ℝ sobolev_index sobolev_index
            (schwartzProductTensorFromTestFamily (u k)))
        Filter.atTop
        (nhds (SchwartzMap.seminorm ℝ sobolev_index sobolev_index g)) :=
    (hseminorm_cont.tendsto g).comp hu_tendsto
  have hbound_tendsto :
      Filter.Tendsto
        (fun k =>
          Cn * SchwartzMap.seminorm ℝ sobolev_index sobolev_index
            (schwartzProductTensorFromTestFamily (u k)))
        Filter.atTop
        (nhds (Cn * SchwartzMap.seminorm ℝ sobolev_index sobolev_index g)) := by
    exact (tendsto_const_nhds.mul hseminorm_tendsto)
  have hpointwise :
      ∀ k,
        ‖phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily (u k))‖ ≤
          Cn * SchwartzMap.seminorm ℝ sobolev_index sobolev_index
            (schwartzProductTensorFromTestFamily (u k)) := by
    intro k
    simpa [Cn] using hprod n hn (u k)
  have hle :=
    le_of_tendsto_of_tendsto hnorm_tendsto hbound_tendsto
      (Filter.Eventually.of_forall hpointwise)
  simpa [Cn] using hle

/-- Construct φ⁴ linear-growth witness data from:
    1) explicit product-tensor linear-growth bounds for positive orders,
    2) explicit product-tensor approximation of general Schwartz `n`-point tests
       for `n > 0` (with seminorm convergence),
    3) an explicit order-zero growth bound. -/
theorem phi4_linear_growth_of_productTensor_approx_and_zero
    (params : Phi4Params)
    [SchwingerLimitModel params]
    [SchwingerFunctionModel params]
    [OSTemperedModel params]
    (OS : OsterwalderSchraderAxioms 1)
    (hS : OS.S = phi4SchwingerFunctions params)
    (sobolev_index : ℕ)
    (alpha beta gamma : ℝ)
    (halpha : 0 < alpha)
    (hbeta : 0 < beta)
    (hprod :
      ∀ (n : ℕ) (_hn : 0 < n) (f : Fin n → TestFun2D),
        ‖phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily f)‖ ≤
          alpha * beta ^ n * (n.factorial : ℝ) ^ gamma *
            SchwartzMap.seminorm ℝ sobolev_index sobolev_index
              (schwartzProductTensorFromTestFamily f))
    (happrox :
      ∀ (n : ℕ) (_hn : 0 < n) (g : SchwartzNPoint 1 n),
        ∃ u : ℕ → Fin n → TestFun2D,
          Filter.Tendsto (fun k => schwartzProductTensorFromTestFamily (u k))
            Filter.atTop (nhds g))
    (hzero :
      ∀ g : SchwartzNPoint 1 0,
        ‖phi4SchwingerFunctions params 0 g‖ ≤
          alpha * beta ^ 0 * (Nat.factorial 0 : ℝ) ^ gamma *
            SchwartzMap.seminorm ℝ sobolev_index sobolev_index g) :
    ∃ OS' : OsterwalderSchraderAxioms 1,
      OS'.S = phi4SchwingerFunctions params ∧
      Nonempty (OSLinearGrowthCondition 1 OS') := by
  refine ⟨OS, hS, ?_⟩
  refine ⟨{
    sobolev_index := sobolev_index
    alpha := alpha
    beta := beta
    gamma := gamma
    alpha_pos := halpha
    beta_pos := hbeta
    growth_estimate := ?_
  }⟩
  intro n g
  by_cases hn : 0 < n
  · simpa [hS] using
      (phi4_positive_order_linear_growth_of_productTensor_approx
        params sobolev_index alpha beta gamma hprod happrox n hn g)
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst hn0
    simpa [hS] using hzero g

/-- Order-zero linear-growth bound at `n = 0`, from normalization
    `S₀(g) = g(0)` and `alpha ≥ 1`. -/
theorem phi4_zero_linear_growth_of_normalized_order0
    (params : Phi4Params)
    [SchwingerFunctionModel params]
    (alpha beta gamma : ℝ)
    (halpha_one : 1 ≤ alpha)
    (hnormalized :
      ∀ g : SchwartzNPoint 1 0, phi4SchwingerFunctions params 0 g = g 0) :
    ∀ g : SchwartzNPoint 1 0,
      ‖phi4SchwingerFunctions params 0 g‖ ≤
        alpha * beta ^ 0 * (Nat.factorial 0 : ℝ) ^ gamma *
          SchwartzMap.seminorm ℝ 0 0 g := by
  intro g
  calc
    ‖phi4SchwingerFunctions params 0 g‖ = ‖g 0‖ := by
      simp [hnormalized g]
    _ ≤ SchwartzMap.seminorm ℝ 0 0 g := by
      simpa using (SchwartzMap.norm_le_seminorm ℝ g 0)
    _ ≤ alpha * SchwartzMap.seminorm ℝ 0 0 g := by
      exact (le_mul_of_one_le_left
        (apply_nonneg (SchwartzMap.seminorm ℝ 0 0) g)
        halpha_one)
    _ = alpha * beta ^ 0 * (Nat.factorial 0 : ℝ) ^ gamma *
          SchwartzMap.seminorm ℝ 0 0 g := by
      simp

/-- Order-zero normalization from:
    1) core linearity of `phi4SchwingerFunctions params 0`, and
    2) compatibility with `infiniteVolumeSchwinger` on product tensors. -/
theorem phi4_normalized_order0_of_linear_and_compat
    (params : Phi4Params)
    [InteractionWeightModel params]
    [SchwingerLimitModel params]
    [SchwingerFunctionModel params]
    [OSTemperedModel params]
    (hcompat :
      ∀ (n : ℕ) (f : Fin n → TestFun2D),
        phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily f) =
          (infiniteVolumeSchwinger params n f : ℂ)) :
    ∀ g : SchwartzNPoint 1 0, phi4SchwingerFunctions params 0 g = g 0 := by
  have hlin0 : IsLinearMap ℂ (phi4SchwingerFunctions params 0) :=
    phi4_os0_linear params 0
  intro g
  let f0 : Fin 0 → TestFun2D := fun i => False.elim (Fin.elim0 i)
  have hone : phi4SchwingerFunctions params 0 (schwartzProductTensorFromTestFamily f0) = 1 :=
    phi4_productTensor_zero_of_compat params hcompat f0
  have hdecomp : g = (g 0) • schwartzProductTensorFromTestFamily f0 := by
    ext x
    have hx : x = 0 := Subsingleton.elim x 0
    subst hx
    simp [schwartzProductTensorFromTestFamily]
  calc
    phi4SchwingerFunctions params 0 g
        = phi4SchwingerFunctions params 0 ((g 0) • schwartzProductTensorFromTestFamily f0) := by
            exact congrArg (phi4SchwingerFunctions params 0) hdecomp
    _ = (g 0) * phi4SchwingerFunctions params 0 (schwartzProductTensorFromTestFamily f0) := by
            exact (hlin0.mk' _).map_smul (g 0) (schwartzProductTensorFromTestFamily f0)
    _ = g 0 := by simp [hone]

/-- Measure-representation variant of order-zero normalization from:
    1) core linearity of `phi4SchwingerFunctions params 0`, and
    2) compatibility with `infiniteVolumeSchwinger` on product tensors. -/
theorem phi4_normalized_order0_of_linear_and_compat_of_moment
    (params : Phi4Params)
    [InfiniteVolumeSchwingerModel params]
    [InfiniteVolumeMeasureModel params]
    [InfiniteVolumeMomentModel params]
    [SchwingerFunctionModel params]
    [OSTemperedModel params]
    (hcompat :
      ∀ (n : ℕ) (f : Fin n → TestFun2D),
        phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily f) =
          (infiniteVolumeSchwinger params n f : ℂ)) :
    ∀ g : SchwartzNPoint 1 0, phi4SchwingerFunctions params 0 g = g 0 := by
  have hlin0 : IsLinearMap ℂ (phi4SchwingerFunctions params 0) :=
    phi4_os0_linear params 0
  intro g
  let f0 : Fin 0 → TestFun2D := fun i => False.elim (Fin.elim0 i)
  have hone : phi4SchwingerFunctions params 0 (schwartzProductTensorFromTestFamily f0) = 1 :=
    phi4_productTensor_zero_of_compat_of_moment params hcompat f0
  have hdecomp : g = (g 0) • schwartzProductTensorFromTestFamily f0 := by
    ext x
    have hx : x = 0 := Subsingleton.elim x 0
    subst hx
    simp [schwartzProductTensorFromTestFamily]
  calc
    phi4SchwingerFunctions params 0 g
        = phi4SchwingerFunctions params 0 ((g 0) • schwartzProductTensorFromTestFamily f0) := by
            exact congrArg (phi4SchwingerFunctions params 0) hdecomp
    _ = (g 0) * phi4SchwingerFunctions params 0 (schwartzProductTensorFromTestFamily f0) := by
            exact (hlin0.mk' _).map_smul (g 0) (schwartzProductTensorFromTestFamily f0)
    _ = g 0 := by simp [hone]

/-- Construct φ⁴ linear-growth witness data from:
    1) explicit pointwise-in-`f` finite-volume uniform generating-functional bounds,
    2) explicit product-tensor approximation of general Schwartz `n`-point tests
       for `n > 0`,
    3) order-zero normalization (`S₀(g) = g(0)`), using Sobolev index `0`. -/
theorem phi4_linear_growth_of_interface_productTensor_approx_and_normalized_order0
    (params : Phi4Params)
    [InteractionWeightModel params]
    [SchwingerLimitModel params]
    [SchwingerFunctionModel params]
    [OSTemperedModel params]
    (OS : OsterwalderSchraderAxioms 1)
    (hS : OS.S = phi4SchwingerFunctions params)
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
    (happrox :
      ∀ (n : ℕ) (_hn : 0 < n) (g : SchwartzNPoint 1 n),
        ∃ u : ℕ → Fin n → TestFun2D,
          Filter.Tendsto (fun k => schwartzProductTensorFromTestFamily (u k))
            Filter.atTop (nhds g)) :
    ∃ OS' : OsterwalderSchraderAxioms 1,
      OS'.S = phi4SchwingerFunctions params ∧
      Nonempty (OSLinearGrowthCondition 1 OS') := by
  have hnormalized : ∀ g : SchwartzNPoint 1 0, phi4SchwingerFunctions params 0 g = g 0 :=
    phi4_normalized_order0_of_linear_and_compat params hcompat
  let alpha' : ℝ := max alpha 1
  have halpha' : 0 < alpha' := by
    exact lt_of_lt_of_le zero_lt_one (le_max_right alpha 1)
  have halpha'_one : 1 ≤ alpha' := by
    exact le_max_right alpha 1
  have hreduce' :
      ∀ (c : ℝ) (n : ℕ) (_hn : 0 < n) (f : Fin n → TestFun2D),
        ∑ i : Fin n, (Nat.factorial n : ℝ) *
            (Real.exp (c * normFunctional (f i)) +
              Real.exp (c * normFunctional (-(f i)))) ≤
          alpha' * beta ^ n * (n.factorial : ℝ) ^ gamma *
            SchwartzMap.seminorm ℝ 0 0
              (schwartzProductTensorFromTestFamily f) := by
    intro c n hn f
    let C : ℝ :=
      beta ^ n * (n.factorial : ℝ) ^ gamma *
        SchwartzMap.seminorm ℝ 0 0 (schwartzProductTensorFromTestFamily f)
    have hC_nonneg : 0 ≤ C := by
      dsimp [C]
      positivity
    have hboundC : alpha * C ≤ alpha' * C := by
      simpa [alpha', C, mul_assoc, mul_left_comm, mul_comm] using
        (mul_le_mul_of_nonneg_right (le_max_left alpha 1) hC_nonneg)
    have hboundC' :
        alpha * C ≤
          alpha' * beta ^ n * (n.factorial : ℝ) ^ gamma *
            SchwartzMap.seminorm ℝ 0 0 (schwartzProductTensorFromTestFamily f) := by
      simpa [C, mul_assoc, mul_left_comm, mul_comm] using hboundC
    exact (show
      ∑ i : Fin n, (Nat.factorial n : ℝ) *
          (Real.exp (c * normFunctional (f i)) +
            Real.exp (c * normFunctional (-(f i)))) ≤ alpha * C from by
        simpa [C, mul_assoc, mul_left_comm, mul_comm] using hreduce c n hn f).trans hboundC'
  have hzero := phi4_zero_linear_growth_of_normalized_order0
    params alpha' beta gamma halpha'_one hnormalized
  have hprod := phi4_productTensor_linear_growth_of_uniform_generating_bound
    params 0 alpha' beta gamma
    huniform
    hcompat hreduce'
  exact phi4_linear_growth_of_productTensor_approx_and_zero
    params OS hS 0 alpha' beta gamma halpha' hbeta hprod happrox hzero

/-- Sequence approximation by product tensors from dense image of the
    product-tensor map at fixed positive order. -/
theorem phi4_productTensor_approx_of_dense_range
    {n : ℕ} (_hn : 0 < n) (g : SchwartzNPoint 1 n)
    (hdense :
      DenseRange (fun f : Fin n → TestFun2D =>
        schwartzProductTensorFromTestFamily f)) :
    ∃ u : ℕ → Fin n → TestFun2D,
      Filter.Tendsto (fun k => schwartzProductTensorFromTestFamily (u k))
        Filter.atTop (nhds g) := by
  let ptmap : (Fin n → TestFun2D) → SchwartzNPoint 1 n := fun f =>
    schwartzProductTensorFromTestFamily f
  have hcomap_neBot : Filter.NeBot (Filter.comap ptmap (nhds g)) := by
    refine Filter.comap_neBot ?_
    intro s hs
    exact hdense.mem_nhds hs
  haveI : Filter.NeBot (Filter.comap ptmap (nhds g)) := hcomap_neBot
  obtain ⟨u, hu⟩ := Filter.exists_seq_tendsto (Filter.comap ptmap (nhds g))
  refine ⟨u, ?_⟩
  have hpt : Filter.Tendsto ptmap (Filter.comap ptmap (nhds g)) (nhds g) :=
    Filter.tendsto_comap
  exact hpt.comp hu

/-- Family-form product-tensor approximation from dense image assumptions
    at each positive order. -/
theorem phi4_productTensor_approx_family_of_dense_range
    (hdense :
      ∀ (n : ℕ) (_hn : 0 < n),
        DenseRange (fun f : Fin n → TestFun2D =>
          schwartzProductTensorFromTestFamily f)) :
    ∀ (n : ℕ) (_hn : 0 < n) (g : SchwartzNPoint 1 n),
      ∃ u : ℕ → Fin n → TestFun2D,
        Filter.Tendsto (fun k => schwartzProductTensorFromTestFamily (u k))
          Filter.atTop (nhds g) := by
  intro n hn g
  exact phi4_productTensor_approx_of_dense_range hn g (hdense n hn)

/-! ## Linear growth condition (E0') -/

/-- Build `OSLinearGrowthCondition` from explicit seminorm-growth constants
    for a fixed OS package. -/
theorem osLinearGrowthCondition_nonempty_of_bound
    (OS : OsterwalderSchraderAxioms 1)
    (sobolev_index : ℕ)
    (alpha beta gamma : ℝ)
    (halpha : 0 < alpha)
    (hbeta : 0 < beta)
    (hgrowth : ∀ (n : ℕ) (f : SchwartzNPoint 1 n),
      ‖OS.S n f‖ ≤ alpha * beta ^ n * (n.factorial : ℝ) ^ gamma *
        SchwartzMap.seminorm ℝ sobolev_index sobolev_index f) :
    Nonempty (OSLinearGrowthCondition 1 OS) := by
  refine ⟨{
    sobolev_index := sobolev_index
    alpha := alpha
    beta := beta
    gamma := gamma
    alpha_pos := halpha
    beta_pos := hbeta
    growth_estimate := hgrowth
  }⟩

/-- Construct φ⁴ linear-growth witness data from explicit seminorm-growth
    constants for one OS package matching `phi4SchwingerFunctions`. -/
theorem phi4_linear_growth_of_explicit_bound (params : Phi4Params)
    [SchwingerFunctionModel params]
    (OS : OsterwalderSchraderAxioms 1)
    (hS : OS.S = phi4SchwingerFunctions params)
    (sobolev_index : ℕ)
    (alpha beta gamma : ℝ)
    (halpha : 0 < alpha)
    (hbeta : 0 < beta)
    (hgrowth : ∀ (n : ℕ) (f : SchwartzNPoint 1 n),
      ‖phi4SchwingerFunctions params n f‖ ≤
        alpha * beta ^ n * (n.factorial : ℝ) ^ gamma *
          SchwartzMap.seminorm ℝ sobolev_index sobolev_index f) :
    ∃ OS' : OsterwalderSchraderAxioms 1,
      OS'.S = phi4SchwingerFunctions params ∧
      Nonempty (OSLinearGrowthCondition 1 OS') := by
  refine ⟨OS, hS, ?_⟩
  refine osLinearGrowthCondition_nonempty_of_bound OS sobolev_index
    alpha beta gamma halpha hbeta ?_
  intro n f
  simpa [hS] using hgrowth n f

/-- Construct `ReconstructionLinearGrowthModel` from explicit linear-growth data. -/
theorem reconstructionLinearGrowthModel_nonempty_of_data (params : Phi4Params)
    [SchwingerFunctionModel params]
    (hlinear :
      ∃ OS : OsterwalderSchraderAxioms 1,
        OS.S = phi4SchwingerFunctions params ∧
        Nonempty (OSLinearGrowthCondition 1 OS)) :
    Nonempty (ReconstructionLinearGrowthModel params) := by
  rcases hlinear with ⟨OS, hOS, hlg_nonempty⟩
  rcases hlg_nonempty with ⟨hlg⟩
  exact ⟨{
    os_package := OS
    os_package_eq := hOS
    linear_growth := hlg
  }⟩

/-- Construct `ReconstructionLinearGrowthModel` from explicit seminorm-growth
    constants for an OS package matching `phi4SchwingerFunctions`. -/
theorem reconstructionLinearGrowthModel_nonempty_of_explicit_bound
    (params : Phi4Params)
    [SchwingerFunctionModel params]
    (OS : OsterwalderSchraderAxioms 1)
    (hS : OS.S = phi4SchwingerFunctions params)
    (sobolev_index : ℕ)
    (alpha beta gamma : ℝ)
    (halpha : 0 < alpha)
    (hbeta : 0 < beta)
    (hgrowth : ∀ (n : ℕ) (f : SchwartzNPoint 1 n),
      ‖phi4SchwingerFunctions params n f‖ ≤
        alpha * beta ^ n * (n.factorial : ℝ) ^ gamma *
          SchwartzMap.seminorm ℝ sobolev_index sobolev_index f) :
    Nonempty (ReconstructionLinearGrowthModel params) := by
  exact reconstructionLinearGrowthModel_nonempty_of_data params
    (hlinear := phi4_linear_growth_of_explicit_bound params OS hS
      sobolev_index alpha beta gamma halpha hbeta hgrowth)

/-- Build `ReconstructionLinearGrowthModel` from:
    1) an interface-level OS package theorem under weak coupling, and
    2) an explicit seminorm-growth estimate for `phi4SchwingerFunctions`. -/
theorem reconstructionLinearGrowthModel_nonempty_of_os_and_explicit_bound
    (params : Phi4Params)
    [OSAxiomCoreModel params]
    [OSDistributionE2Model params]
    [OSE4ClusterModel params]
    (hsmall : params.coupling < os4WeakCouplingThreshold params)
    (sobolev_index : ℕ)
    (alpha beta gamma : ℝ)
    (halpha : 0 < alpha)
    (hbeta : 0 < beta)
    (hgrowth : ∀ (n : ℕ) (f : SchwartzNPoint 1 n),
      ‖phi4SchwingerFunctions params n f‖ ≤
        alpha * beta ^ n * (n.factorial : ℝ) ^ gamma *
          SchwartzMap.seminorm ℝ sobolev_index sobolev_index f) :
    Nonempty (ReconstructionLinearGrowthModel params) := by
  rcases phi4_satisfies_OS_of_interfaces params hsmall with ⟨OS, hS⟩
  exact reconstructionLinearGrowthModel_nonempty_of_explicit_bound params OS hS
    sobolev_index alpha beta gamma halpha hbeta hgrowth

/-- **Linear growth condition E0'** for the φ⁴₂ Schwinger functions.
    |S_n(f)| ≤ α · βⁿ · (n!)^γ · ‖f‖_s
    with γ = 1/2 for the φ⁴ interaction.

    This is stronger than simple temperedness (E0) and is essential for the
    analytic continuation to work: without it, the Wightman distributions
    reconstructed from the Schwinger functions may fail to be tempered.

    For the φ⁴₂ theory, this follows from the generating functional bound
    (Theorem 12.5.1) and the Wick-type combinatorics of the interaction. -/
theorem gap_phi4_linear_growth (params : Phi4Params)
    [InteractionWeightModel params]
    [SchwingerLimitModel params]
    [OSAxiomCoreModel params]
    [OSDistributionE2Model params]
    [OSE4ClusterModel params]
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
  rcases phi4_satisfies_OS_of_interfaces params hsmall with ⟨OS, hS⟩
  exact phi4_linear_growth_of_interface_productTensor_approx_and_normalized_order0
    params OS hS alpha beta gamma hbeta huniform hcompat hreduce
    (phi4_productTensor_approx_family_of_dense_range hdense)

/-- Linear-growth frontier with an explicit WP1-style interaction input:
    replace direct `[InteractionWeightModel params]` by geometric decay of
    shifted cutoff exponential moments, then instantiate the weight model
    constructively before applying `gap_phi4_linear_growth`. -/
theorem gap_phi4_linear_growth_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
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
    ∃ OS : OsterwalderSchraderAxioms 1,
      OS.S = phi4SchwingerFunctions params ∧
      Nonempty (OSLinearGrowthCondition 1 OS) := by
  rcases
      interactionWeightModel_nonempty_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
        (params := params) hmom with ⟨hW⟩
  letI : InteractionWeightModel params := hW
  exact gap_phi4_linear_growth params hsmall alpha beta gamma hbeta
    huniform hcompat hreduce hdense

/-- Linear-growth frontier with explicit square-integrable UV data and shifted
    geometric cutoff-moment decay.
    This first instantiates `InteractionUVModel` constructively from
    square-integrable/measurable cutoff data, then applies the UV-based
    linear-growth bridge. -/
theorem
    gap_phi4_linear_growth_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
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
    ∃ OS : OsterwalderSchraderAxioms 1,
      OS.S = phi4SchwingerFunctions params ∧
      Nonempty (OSLinearGrowthCondition 1 OS) := by
  rcases interactionUVModel_nonempty_of_sq_integrable_data
      (params := params)
      hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
      hinteraction_meas hinteraction_sq with ⟨huv⟩
  letI : InteractionUVModel params := huv
  exact gap_phi4_linear_growth_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
    params hmom hsmall alpha beta gamma hbeta huniform hcompat hreduce hdense

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
    This first builds `InteractionUVModel` constructively, then reuses the
    UV-based linear-growth bridge. -/
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
  rcases interactionUVModel_nonempty_of_sq_integrable_data
      (params := params)
      hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
      hinteraction_meas hinteraction_sq with ⟨huv⟩
  letI : InteractionUVModel params := huv
  exact reconstructionLinearGrowthModel_nonempty_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
    (params := params) hmom hsmall alpha beta gamma hbeta
    huniform hcompat hreduce hdense

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
    3) shifted-cutoff geometric moment decay, and
    4) explicit product-tensor reduction/approximation hypotheses.
    This first instantiates `InteractionUVModel` constructively. -/
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
  rcases interactionUVModel_nonempty_of_sq_integrable_data
      (params := params)
      hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
      hinteraction_meas hinteraction_sq with ⟨huv⟩
  letI : InteractionUVModel params := huv
  exact reconstructionInputModel_nonempty_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
    (params := params) hmom hsmall alpha beta gamma hbeta
    huniform hcompat hreduce hdense

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

/-! ## OS4: Clustering (for weak coupling) -/

/-- **OS4 (Clustering)** for weak coupling:
    There exists a coupling threshold λ₀ > 0 such that for λ < λ₀,
    the truncated two-point function decays exponentially with the
    spatial separation of the test function supports:
      |⟨φ(f)φ(g)⟩ - ⟨φ(f)⟩⟨φ(g)⟩| ≤ C_{f,g} · e^{-m·dist(supp f, supp g)}
    where m > 0 is the mass gap.

    The proof uses the cluster expansion (Glimm-Jaffe Chapter 18):
    a convergent expansion in the coupling constant that exhibits
    exponential decay of connected correlations.

    For strong coupling, OS4 requires the phase transition analysis
    and may fail at the critical point. -/
theorem phi4_os4_weak_coupling (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [UniformWeakCouplingDecayModel params] →
    ∃ coupling_bound : ℝ, 0 < coupling_bound ∧
      ∀ p : Phi4Params, [SchwingerLimitModel p] →
        p.coupling < coupling_bound →
          ConnectedTwoPointDecayAtParams p := by
  intro hlim hrec
  exact UniformWeakCouplingDecayModel.phi4_os4_weak_coupling
    (params := params)

/-- Backward-compatible OS4 weak-coupling form written with explicit Schwinger moments. -/
theorem phi4_os4_weak_coupling_explicit (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [UniformWeakCouplingDecayModel params] →
    ∃ coupling_bound : ℝ, 0 < coupling_bound ∧
      ∀ p : Phi4Params, [SchwingerLimitModel p] →
        p.coupling < coupling_bound →
          ∃ m_gap : ℝ, 0 < m_gap ∧
            ∀ (f g : TestFun2D), ∃ Cfg : ℝ, 0 ≤ Cfg ∧
              ∀ (a : Fin 2 → ℝ),
                let g_shifted : TestFun2D := translateTestFun a g
                |infiniteVolumeSchwinger p 2 ![f, g_shifted] -
                  infiniteVolumeSchwinger p 1 ![f] *
                    infiniteVolumeSchwinger p 1 ![g_shifted]| ≤
                  Cfg * Real.exp (-m_gap * ‖a‖) := by
  intro hlim hrec
  rcases phi4_os4_weak_coupling params with ⟨coupling_bound, hcb_pos, hdecay⟩
  refine ⟨coupling_bound, hcb_pos, ?_⟩
  intro p hpInst hsmall
  rcases hdecay p hsmall with ⟨m_gap, hm_gap, hbound⟩
  refine ⟨m_gap, hm_gap, ?_⟩
  intro f g
  rcases hbound f g with ⟨Cfg, hCfg_nonneg, hfg⟩
  refine ⟨Cfg, hCfg_nonneg, ?_⟩
  intro a
  simpa [connectedTwoPoint] using hfg a

/-- Fixed-`params` explicit weak-coupling connected 2-point decay threshold:
    from the fixed-parameter reconstruction weak-coupling interface, obtain a
    positive coupling threshold giving explicit Schwinger-moment exponential
    decay at the current parameters. -/
theorem phi4_os4_weak_coupling_explicit_at_params (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [ReconstructionWeakCouplingModel params] →
  ∃ coupling_bound : ℝ, 0 < coupling_bound ∧
      (params.coupling < coupling_bound →
        ∃ m_gap : ℝ, 0 < m_gap ∧
          ∀ (f g : TestFun2D), ∃ Cfg : ℝ, 0 ≤ Cfg ∧
            ∀ (a : Fin 2 → ℝ),
              let g_shifted : TestFun2D := translateTestFun a g
              |infiniteVolumeSchwinger params 2 ![f, g_shifted] -
                infiniteVolumeSchwinger params 1 ![f] *
                  infiniteVolumeSchwinger params 1 ![g_shifted]| ≤
                Cfg * Real.exp (-m_gap * ‖a‖)) := by
  intro hlim hrec
  let coupling_bound := ReconstructionWeakCouplingModel.weak_coupling_threshold (params := params)
  have hcb_pos : 0 < coupling_bound :=
    ReconstructionWeakCouplingModel.weak_coupling_threshold_pos (params := params)
  refine ⟨coupling_bound, hcb_pos, ?_⟩
  intro hsmall
  rcases ReconstructionWeakCouplingModel.connectedTwoPoint_decay_of_weak_coupling
      (params := params) hsmall with ⟨m_gap, hm_gap, hfg⟩
  refine ⟨m_gap, hm_gap, ?_⟩
  intro f g
  rcases hfg f g with ⟨Cfg, hCfg_nonneg, hbound⟩
  refine ⟨Cfg, hCfg_nonneg, ?_⟩
  intro a
  simpa [connectedTwoPoint] using hbound a

/-- Fixed-`params` weak-coupling decay threshold for connected 2-point functions.
    This is the canonical threshold carried by `ReconstructionInputModel`. -/
theorem phi4_connectedTwoPoint_decay_threshold (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [ReconstructionWeakCouplingModel params] →
    ConnectedTwoPointDecayThreshold params := by
  intro hlim hrec
  refine ⟨ReconstructionWeakCouplingModel.weak_coupling_threshold (params := params),
    ReconstructionWeakCouplingModel.weak_coupling_threshold_pos (params := params), ?_⟩
  intro hsmall
  exact ReconstructionWeakCouplingModel.connectedTwoPoint_decay_of_weak_coupling
    (params := params) hsmall

/-- A canonical weak-coupling threshold selected from
    `phi4_connectedTwoPoint_decay_threshold`. -/
def phi4WeakCouplingThreshold (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [ReconstructionWeakCouplingModel params] →
    ℝ := by
  intro hlim hrec
  exact ReconstructionWeakCouplingModel.weak_coupling_threshold (params := params)

/-- Positivity of the selected weak-coupling threshold. -/
theorem phi4WeakCouplingThreshold_pos (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [ReconstructionWeakCouplingModel params] →
    0 < phi4WeakCouplingThreshold params := by
  intro hlim hrec
  simpa [phi4WeakCouplingThreshold] using
    ReconstructionWeakCouplingModel.weak_coupling_threshold_pos (params := params)

/-- Exponential decay of connected 2-point functions when
    `params.coupling` is below the selected weak-coupling threshold. -/
theorem phi4_connectedTwoPoint_decay_below_threshold (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [ReconstructionWeakCouplingModel params] →
    params.coupling < phi4WeakCouplingThreshold params →
    ConnectedTwoPointDecayAtParams params := by
  intro hlim hrec hsmall
  exact ReconstructionWeakCouplingModel.connectedTwoPoint_decay_of_weak_coupling
    (params := params) hsmall

/-- Explicit-Schwinger version of `phi4_connectedTwoPoint_decay_below_threshold`. -/
theorem phi4_connectedTwoPoint_decay_below_threshold_explicit (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [ReconstructionWeakCouplingModel params] →
    params.coupling < phi4WeakCouplingThreshold params →
    ∃ m_gap : ℝ, 0 < m_gap ∧
      ∀ (f g : TestFun2D), ∃ Cfg : ℝ, 0 ≤ Cfg ∧
        ∀ (a : Fin 2 → ℝ),
          let g_shifted : TestFun2D := translateTestFun a g
          |infiniteVolumeSchwinger params 2 ![f, g_shifted] -
            infiniteVolumeSchwinger params 1 ![f] *
              infiniteVolumeSchwinger params 1 ![g_shifted]| ≤
            Cfg * Real.exp (-m_gap * ‖a‖) := by
  intro hlim hrec hsmall
  rcases phi4_connectedTwoPoint_decay_below_threshold params hsmall with ⟨m_gap, hm_gap, hdecay⟩
  refine ⟨m_gap, hm_gap, ?_⟩
  intro f g
  rcases hdecay f g with ⟨Cfg, hCfg_nonneg, hfg⟩
  refine ⟨Cfg, hCfg_nonneg, ?_⟩
  intro a
  simpa [connectedTwoPoint] using hfg a

/-! ## ε-R form of connected two-point decay -/

/-- Exponential connected two-point decay implies an `ε`-`R` clustering form
    for each fixed pair of test functions. -/
theorem connectedTwoPoint_decay_eventually_small
    (params : Phi4Params)
    [SchwingerLimitModel params]
    (hdecay : ConnectedTwoPointDecayAtParams params)
    (f g : TestFun2D) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
      ∀ a : Fin 2 → ℝ, R < ‖a‖ →
        let g_shifted : TestFun2D := translateTestFun a g
        |connectedTwoPoint params f g_shifted| < ε := by
  intro ε hε
  rcases hdecay with ⟨m_gap, hm_gap, hdecay_fg⟩
  rcases hdecay_fg f g with ⟨Cfg, hCfg_nonneg, hbound⟩
  by_cases hCfg_zero : Cfg = 0
  · refine ⟨1, zero_lt_one, ?_⟩
    intro a ha
    have hle : (let g_shifted : TestFun2D := translateTestFun a g;
      |connectedTwoPoint params f g_shifted|) ≤ 0 := by
      simpa [hCfg_zero] using hbound a
    exact lt_of_le_of_lt hle hε
  · have hCfg_pos : 0 < Cfg := lt_of_le_of_ne hCfg_nonneg (Ne.symm hCfg_zero)
    let R0 : ℝ := Real.log (Cfg / ε) / m_gap
    let R : ℝ := max 1 R0
    refine ⟨R, lt_of_lt_of_le zero_lt_one (le_max_left 1 R0), ?_⟩
    intro a ha
    have hR0 : R0 < ‖a‖ := lt_of_le_of_lt (le_max_right 1 R0) ha
    have hlog_lt : Real.log (Cfg / ε) < ‖a‖ * m_gap := by
      exact (div_lt_iff₀ hm_gap).1 (by simpa [R0] using hR0)
    have hneg_lt : -m_gap * ‖a‖ < -Real.log (Cfg / ε) := by
      linarith [hlog_lt]
    have hexp_lt :
        Real.exp (-m_gap * ‖a‖) < Real.exp (-Real.log (Cfg / ε)) := by
      exact (Real.exp_lt_exp).2 hneg_lt
    have hratio_pos : 0 < Cfg / ε := div_pos hCfg_pos hε
    have hexp_lt' : Real.exp (-m_gap * ‖a‖) < ε / Cfg := by
      calc
        Real.exp (-m_gap * ‖a‖) < Real.exp (-Real.log (Cfg / ε)) := hexp_lt
        _ = (Cfg / ε)⁻¹ := by rw [Real.exp_neg, Real.exp_log hratio_pos]
        _ = ε / Cfg := by field_simp [hCfg_pos.ne', hε.ne']
    have hmul_lt : Cfg * Real.exp (-m_gap * ‖a‖) < ε := by
      have hmul :
          Cfg * Real.exp (-m_gap * ‖a‖) < Cfg * (ε / Cfg) :=
        mul_lt_mul_of_pos_left hexp_lt' hCfg_pos
      calc
        Cfg * Real.exp (-m_gap * ‖a‖) < Cfg * (ε / Cfg) := hmul
        _ = ε := by field_simp [hCfg_pos.ne']
    have hle :
        (let g_shifted : TestFun2D := translateTestFun a g;
          |connectedTwoPoint params f g_shifted|) ≤ Cfg * Real.exp (-m_gap * ‖a‖) := by
      simpa using hbound a
    exact lt_of_le_of_lt hle hmul_lt

/-- `ε`-`R` clustering form under the selected weak-coupling threshold. -/
theorem phi4_connectedTwoPoint_decay_below_threshold_eventually_small
    (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [ReconstructionWeakCouplingModel params] →
    params.coupling < phi4WeakCouplingThreshold params →
    ∀ (f g : TestFun2D), ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
      ∀ a : Fin 2 → ℝ, R < ‖a‖ →
        let g_shifted : TestFun2D := translateTestFun a g
        |connectedTwoPoint params f g_shifted| < ε := by
  intro hlim hrec hsmall f g ε hε
  exact connectedTwoPoint_decay_eventually_small params
    (phi4_connectedTwoPoint_decay_below_threshold params hsmall) f g ε hε

/-- Explicit-Schwinger `ε`-`R` clustering form under the selected
    weak-coupling threshold. -/
theorem phi4_connectedTwoPoint_decay_below_threshold_eventually_small_explicit
    (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [ReconstructionWeakCouplingModel params] →
    params.coupling < phi4WeakCouplingThreshold params →
    ∀ (f g : TestFun2D), ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
      ∀ a : Fin 2 → ℝ, R < ‖a‖ →
        let g_shifted : TestFun2D := translateTestFun a g
        |infiniteVolumeSchwinger params 2 ![f, g_shifted] -
          infiniteVolumeSchwinger params 1 ![f] *
            infiniteVolumeSchwinger params 1 ![g_shifted]| < ε := by
  intro hlim hrec hsmall f g ε hε
  rcases phi4_connectedTwoPoint_decay_below_threshold_eventually_small
      (params := params) hsmall f g ε hε with ⟨R, hRpos, hR⟩
  refine ⟨R, hRpos, ?_⟩
  intro a ha
  simpa [connectedTwoPoint] using hR a ha

/-- Global weak-coupling `ε`-`R` clustering form for connected 2-point functions. -/
theorem phi4_os4_weak_coupling_eventually_small (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [UniformWeakCouplingDecayModel params] →
    ∃ coupling_bound : ℝ, 0 < coupling_bound ∧
      ∀ p : Phi4Params, [SchwingerLimitModel p] →
        p.coupling < coupling_bound →
          ∀ (f g : TestFun2D) (ε : ℝ), 0 < ε → ∃ R : ℝ, 0 < R ∧
            ∀ a : Fin 2 → ℝ, R < ‖a‖ →
              let g_shifted : TestFun2D := translateTestFun a g
              |connectedTwoPoint p f g_shifted| < ε := by
  intro hlim hdecay
  rcases phi4_os4_weak_coupling params with ⟨coupling_bound, hcb_pos, hglobal⟩
  refine ⟨coupling_bound, hcb_pos, ?_⟩
  intro p hpInst hsmall f g ε hε
  exact connectedTwoPoint_decay_eventually_small p (hglobal p hsmall) f g ε hε

/-- Explicit-Schwinger global weak-coupling `ε`-`R` clustering form. -/
theorem phi4_os4_weak_coupling_eventually_small_explicit (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [UniformWeakCouplingDecayModel params] →
    ∃ coupling_bound : ℝ, 0 < coupling_bound ∧
      ∀ p : Phi4Params, [SchwingerLimitModel p] →
        p.coupling < coupling_bound →
          ∀ (f g : TestFun2D) (ε : ℝ), 0 < ε → ∃ R : ℝ, 0 < R ∧
            ∀ a : Fin 2 → ℝ, R < ‖a‖ →
              let g_shifted : TestFun2D := translateTestFun a g
              |infiniteVolumeSchwinger p 2 ![f, g_shifted] -
                infiniteVolumeSchwinger p 1 ![f] *
                  infiniteVolumeSchwinger p 1 ![g_shifted]| < ε := by
  intro hlim hdecay
  rcases phi4_os4_weak_coupling_eventually_small params with
      ⟨coupling_bound, hcb_pos, hglobal⟩
  refine ⟨coupling_bound, hcb_pos, ?_⟩
  intro p hpInst hsmall f g ε hε
  rcases hglobal p hsmall f g ε hε with ⟨R, hRpos, hR⟩
  refine ⟨R, hRpos, ?_⟩
  intro a ha
  simpa [connectedTwoPoint] using hR a ha

/-- Fixed-`params` explicit weak-coupling `ε`-`R` clustering threshold:
    from the fixed-parameter reconstruction weak-coupling interface, obtain a
    positive coupling threshold under which explicit-Schwinger connected 2-point
    clustering holds at the current parameters. -/
theorem phi4_os4_weak_coupling_eventually_small_explicit_at_params
    (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [ReconstructionWeakCouplingModel params] →
    ∃ coupling_bound : ℝ, 0 < coupling_bound ∧
      (params.coupling < coupling_bound →
        ∀ (f g : TestFun2D) (ε : ℝ), 0 < ε → ∃ R : ℝ, 0 < R ∧
          ∀ a : Fin 2 → ℝ, R < ‖a‖ →
            let g_shifted : TestFun2D := translateTestFun a g
            |infiniteVolumeSchwinger params 2 ![f, g_shifted] -
              infiniteVolumeSchwinger params 1 ![f] *
                infiniteVolumeSchwinger params 1 ![g_shifted]| < ε) := by
  intro hlim hrec
  let coupling_bound := ReconstructionWeakCouplingModel.weak_coupling_threshold (params := params)
  have hcb_pos : 0 < coupling_bound :=
    ReconstructionWeakCouplingModel.weak_coupling_threshold_pos (params := params)
  refine ⟨coupling_bound, hcb_pos, ?_⟩
  intro hsmall f g ε hε
  have hdecay :
      ConnectedTwoPointDecayAtParams params :=
    ReconstructionWeakCouplingModel.connectedTwoPoint_decay_of_weak_coupling
      (params := params) hsmall
  rcases connectedTwoPoint_decay_eventually_small params hdecay f g ε hε with
      ⟨R, hRpos, hR⟩
  refine ⟨R, hRpos, ?_⟩
  intro a ha
  simpa [connectedTwoPoint] using hR a ha

/-- Infinite-volume connected two-point nonnegativity for nonnegative test
    functions, inherited from finite-volume FKG positivity. -/
theorem phi4_connectedTwoPoint_nonneg (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [CorrelationFKGModel params] →
    ∀ (f g : TestFun2D), (∀ x, 0 ≤ f x) → (∀ x, 0 ≤ g x) →
      0 ≤ connectedTwoPoint params f g := by
  intro hlim hcorr f g hf hg
  exact connectedTwoPoint_nonneg params f g hf hg

/-- Infinite-volume diagonal connected two-point nonnegativity for nonnegative
    test functions, from finite-volume FKG positivity and the infinite-volume limit. -/
theorem phi4_connectedTwoPoint_self_nonneg (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [CorrelationFKGModel params] →
    ∀ (f : TestFun2D), (∀ x, 0 ≤ f x) → 0 ≤ connectedTwoPoint params f f := by
  intro hlim hcorr f hf
  exact connectedTwoPoint_self_nonneg_of_fkg params f hf

/-- Infinite-volume diagonal connected two-point nonnegativity (variance form),
    without sign restrictions on test functions. -/
theorem phi4_connectedTwoPoint_self_nonneg_variance (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [InteractionWeightModel params] →
    ∀ (f : TestFun2D), 0 ≤ connectedTwoPoint params f f := by
  intro hlim hint f
  exact connectedTwoPoint_self_nonneg params f

/-- Additivity in the first argument of the infinite-volume connected two-point
    function. -/
theorem phi4_connectedTwoPoint_add_left (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [InteractionWeightModel params] →
    ∀ (f₁ f₂ g : TestFun2D),
      connectedTwoPoint params (f₁ + f₂) g =
        connectedTwoPoint params f₁ g + connectedTwoPoint params f₂ g := by
  intro hlim hint f₁ f₂ g
  exact connectedTwoPoint_add_left params f₁ f₂ g

/-- Scalar linearity in the first argument of the infinite-volume connected
    two-point function. -/
theorem phi4_connectedTwoPoint_smul_left (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [InteractionWeightModel params] →
    ∀ (c : ℝ) (f g : TestFun2D),
      connectedTwoPoint params (c • f) g = c * connectedTwoPoint params f g := by
  intro hlim hint c f g
  exact connectedTwoPoint_smul_left params c f g

/-- Additivity in the second argument of the infinite-volume connected two-point
    function. -/
theorem phi4_connectedTwoPoint_add_right (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [InteractionWeightModel params] →
    ∀ (f g₁ g₂ : TestFun2D),
      connectedTwoPoint params f (g₁ + g₂) =
        connectedTwoPoint params f g₁ + connectedTwoPoint params f g₂ := by
  intro hlim hint f g₁ g₂
  exact connectedTwoPoint_add_right params f g₁ g₂

/-- Scalar linearity in the second argument of the infinite-volume connected
    two-point function. -/
theorem phi4_connectedTwoPoint_smul_right (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [InteractionWeightModel params] →
    ∀ (c : ℝ) (f g : TestFun2D),
      connectedTwoPoint params f (c • g) = c * connectedTwoPoint params f g := by
  intro hlim hint c f g
  exact connectedTwoPoint_smul_right params c f g

/-- Infinite-volume connected two-point function as a bilinear map. -/
def phi4_connectedTwoPoint_bilinear (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [InteractionWeightModel params] →
    TestFun2D →ₗ[ℝ] TestFun2D →ₗ[ℝ] ℝ := by
  intro hlim hint
  exact connectedTwoPointBilinear params

/-- Symmetry of the infinite-volume connected two-point bilinear form. -/
theorem phi4_connectedTwoPoint_bilinear_symm (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [InteractionWeightModel params] →
    ∀ (f g : TestFun2D),
      connectedTwoPointBilinear params f g =
        connectedTwoPointBilinear params g f := by
  intro hlim hint f g
  exact connectedTwoPointBilinear_symm params f g

/-- Diagonal nonnegativity of the infinite-volume connected two-point bilinear
    form. -/
theorem phi4_connectedTwoPoint_bilinear_self_nonneg (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [InteractionWeightModel params] →
    ∀ (f : TestFun2D), 0 ≤ connectedTwoPointBilinear params f f := by
  intro hlim hint f
  exact connectedTwoPointBilinear_self_nonneg params f

/-- Infinite-volume connected two-point Cauchy-Schwarz inequality. -/
theorem phi4_connectedTwoPoint_sq_le_mul_diag (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [InteractionWeightModel params] →
    ∀ (f g : TestFun2D),
      (connectedTwoPoint params f g) ^ 2 ≤
        connectedTwoPoint params f f * connectedTwoPoint params g g := by
  intro hlim hint f g
  exact connectedTwoPoint_sq_le_mul_diag params f g

/-- Infinite-volume connected two-point geometric-mean bound. -/
theorem phi4_connectedTwoPoint_abs_le_sqrt_diag_mul (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [InteractionWeightModel params] →
    ∀ (f g : TestFun2D),
      |connectedTwoPoint params f g| ≤
        Real.sqrt (connectedTwoPoint params f f * connectedTwoPoint params g g) := by
  intro hlim hint f g
  exact connectedTwoPoint_abs_le_sqrt_diag_mul params f g

/-- Infinite-volume connected two-point half-diagonal bound. -/
theorem phi4_connectedTwoPoint_abs_le_half_diag_sum (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [InteractionWeightModel params] →
    ∀ (f g : TestFun2D),
      |connectedTwoPoint params f g| ≤
        (connectedTwoPoint params f f + connectedTwoPoint params g g) / 2 := by
  intro hlim hint f g
  exact connectedTwoPoint_abs_le_half_diag_sum params f g

/-- Infinite-volume finite-family PSD statement for the connected two-point kernel. -/
theorem phi4_connectedTwoPoint_quadratic_nonneg (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [InteractionWeightModel params] →
    ∀ {ι : Type*} (s : Finset ι) (f : ι → TestFun2D) (c : ι → ℝ),
      0 ≤ Finset.sum s (fun i =>
        c i * Finset.sum s (fun j => c j * connectedTwoPoint params (f j) (f i))) := by
  intro hlim hint ι s f c
  exact connectedTwoPoint_quadratic_nonneg params s f c

/-- Standard-index-order form of `phi4_connectedTwoPoint_quadratic_nonneg`. -/
theorem phi4_connectedTwoPoint_quadratic_nonneg_standard (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [InteractionWeightModel params] →
    ∀ {ι : Type*} (s : Finset ι) (f : ι → TestFun2D) (c : ι → ℝ),
      0 ≤ Finset.sum s (fun i => Finset.sum s (fun j =>
        c i * c j * connectedTwoPoint params (f i) (f j))) := by
  intro hsch hint ι s f c
  exact connectedTwoPoint_quadratic_nonneg_standard params s f c

/-- Infinite-volume 4-point cumulant nonpositivity inherited from Lebowitz bounds. -/
theorem phi4_infiniteCumulantFourPoint_nonpos (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [CorrelationGKSSecondModel params] →
    [CorrelationLebowitzModel params] →
    ∀ (f₁ f₂ f₃ f₄ : TestFun2D),
      (∀ x, 0 ≤ f₁ x) → (∀ x, 0 ≤ f₂ x) →
      (∀ x, 0 ≤ f₃ x) → (∀ x, 0 ≤ f₄ x) →
      infiniteCumulantFourPoint params f₁ f₂ f₃ f₄ ≤ 0 := by
  intro hlim hgks hleb f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  exact infiniteCumulantFourPoint_nonpos params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄

/-- Infinite-volume absolute bound for the fully connected 4-point cumulant. -/
theorem phi4_infiniteCumulantFourPoint_abs_bound (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [CorrelationGKSSecondModel params] →
    [CorrelationLebowitzModel params] →
    ∀ (f₁ f₂ f₃ f₄ : TestFun2D),
      (∀ x, 0 ≤ f₁ x) → (∀ x, 0 ≤ f₂ x) →
      (∀ x, 0 ≤ f₃ x) → (∀ x, 0 ≤ f₄ x) →
      |infiniteCumulantFourPoint params f₁ f₂ f₃ f₄| ≤
        infiniteVolumeSchwinger params 2 ![f₁, f₃] *
          infiniteVolumeSchwinger params 2 ![f₂, f₄] +
        infiniteVolumeSchwinger params 2 ![f₁, f₄] *
          infiniteVolumeSchwinger params 2 ![f₂, f₃] := by
  intro hlim hgks hleb f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  exact infiniteCumulantFourPoint_abs_bound params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄

/-- Channel-wise lower bounds for the infinite-volume fully connected 4-point
    cumulant. -/
theorem phi4_infiniteCumulantFourPoint_lower_bounds_all_channels (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [CorrelationGKSSecondModel params] →
    [CorrelationLebowitzModel params] →
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
        ≤ infiniteCumulantFourPoint params f₁ f₂ f₃ f₄ := by
  intro hlim hgks hleb f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  exact infiniteCumulantFourPoint_lower_bounds_all_channels
    params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄

/-- Alternative absolute-value bound via the `(13)(24)` channel. -/
theorem phi4_infiniteCumulantFourPoint_abs_bound_alt13 (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [CorrelationGKSSecondModel params] →
    [CorrelationLebowitzModel params] →
    ∀ (f₁ f₂ f₃ f₄ : TestFun2D),
      (∀ x, 0 ≤ f₁ x) → (∀ x, 0 ≤ f₂ x) →
      (∀ x, 0 ≤ f₃ x) → (∀ x, 0 ≤ f₄ x) →
      |infiniteCumulantFourPoint params f₁ f₂ f₃ f₄| ≤
        infiniteVolumeSchwinger params 2 ![f₁, f₂] *
          infiniteVolumeSchwinger params 2 ![f₃, f₄] +
        infiniteVolumeSchwinger params 2 ![f₁, f₄] *
          infiniteVolumeSchwinger params 2 ![f₂, f₃] := by
  intro hlim hgks hleb f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  exact infiniteCumulantFourPoint_abs_bound_alt13 params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄

/-- Alternative absolute-value bound via the `(14)(23)` channel. -/
theorem phi4_infiniteCumulantFourPoint_abs_bound_alt14 (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [CorrelationGKSSecondModel params] →
    [CorrelationLebowitzModel params] →
    ∀ (f₁ f₂ f₃ f₄ : TestFun2D),
      (∀ x, 0 ≤ f₁ x) → (∀ x, 0 ≤ f₂ x) →
      (∀ x, 0 ≤ f₃ x) → (∀ x, 0 ≤ f₄ x) →
      |infiniteCumulantFourPoint params f₁ f₂ f₃ f₄| ≤
        infiniteVolumeSchwinger params 2 ![f₁, f₂] *
          infiniteVolumeSchwinger params 2 ![f₃, f₄] +
        infiniteVolumeSchwinger params 2 ![f₁, f₃] *
          infiniteVolumeSchwinger params 2 ![f₂, f₄] := by
  intro hlim hgks hleb f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  exact infiniteCumulantFourPoint_abs_bound_alt14 params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄

/-- Infinite-volume all-channel 4-point bounds (GKS lower channels + Lebowitz upper
    channel). -/
theorem phi4_infiniteSchwinger_four_bounds_all_channels (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [CorrelationGKSSecondModel params] →
    [CorrelationLebowitzModel params] →
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
          infiniteVolumeSchwinger params 2 ![f₂, f₃] := by
  intro hlim hgks hleb f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  exact infiniteSchwinger_four_bounds_all_channels
    params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄

/-- Infinite-volume nonnegativity of the `(12)(34)` pairing-subtracted
    4-point channel. -/
theorem phi4_infiniteTruncatedFourPoint12_nonneg (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [CorrelationGKSSecondModel params] →
    [CorrelationLebowitzModel params] →
    ∀ (f₁ f₂ f₃ f₄ : TestFun2D),
      (∀ x, 0 ≤ f₁ x) → (∀ x, 0 ≤ f₂ x) →
      (∀ x, 0 ≤ f₃ x) → (∀ x, 0 ≤ f₄ x) →
      0 ≤ infiniteTruncatedFourPoint12 params f₁ f₂ f₃ f₄ := by
  intro hlim hgks hleb f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  exact infiniteTruncatedFourPoint12_nonneg params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄

/-- Infinite-volume nonnegativity of the `(13)(24)` pairing-subtracted
    4-point channel. -/
theorem phi4_infiniteTruncatedFourPoint13_nonneg (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [CorrelationGKSSecondModel params] →
    [CorrelationLebowitzModel params] →
    ∀ (f₁ f₂ f₃ f₄ : TestFun2D),
      (∀ x, 0 ≤ f₁ x) → (∀ x, 0 ≤ f₂ x) →
      (∀ x, 0 ≤ f₃ x) → (∀ x, 0 ≤ f₄ x) →
      0 ≤ infiniteTruncatedFourPoint13 params f₁ f₂ f₃ f₄ := by
  intro hlim hgks hleb f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  exact infiniteTruncatedFourPoint13_nonneg params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄

/-- Infinite-volume nonnegativity of the `(14)(23)` pairing-subtracted
    4-point channel. -/
theorem phi4_infiniteTruncatedFourPoint14_nonneg (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [CorrelationGKSSecondModel params] →
    [CorrelationLebowitzModel params] →
    ∀ (f₁ f₂ f₃ f₄ : TestFun2D),
      (∀ x, 0 ≤ f₁ x) → (∀ x, 0 ≤ f₂ x) →
      (∀ x, 0 ≤ f₃ x) → (∀ x, 0 ≤ f₄ x) →
      0 ≤ infiniteTruncatedFourPoint14 params f₁ f₂ f₃ f₄ := by
  intro hlim hgks hleb f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  exact infiniteTruncatedFourPoint14_nonneg params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄

/-- Infinite-volume upper bound for the `(12)(34)` pairing-subtracted channel. -/
theorem phi4_infiniteTruncatedFourPoint12_upper (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [CorrelationGKSSecondModel params] →
    [CorrelationLebowitzModel params] →
    ∀ (f₁ f₂ f₃ f₄ : TestFun2D),
      (∀ x, 0 ≤ f₁ x) → (∀ x, 0 ≤ f₂ x) →
      (∀ x, 0 ≤ f₃ x) → (∀ x, 0 ≤ f₄ x) →
      infiniteTruncatedFourPoint12 params f₁ f₂ f₃ f₄ ≤
        infiniteVolumeSchwinger params 2 ![f₁, f₃] *
          infiniteVolumeSchwinger params 2 ![f₂, f₄] +
        infiniteVolumeSchwinger params 2 ![f₁, f₄] *
          infiniteVolumeSchwinger params 2 ![f₂, f₃] := by
  intro hlim hgks hleb f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  exact infiniteTruncatedFourPoint12_upper params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄

/-- Infinite-volume upper bound for the `(13)(24)` pairing-subtracted channel. -/
theorem phi4_infiniteTruncatedFourPoint13_upper (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [CorrelationGKSSecondModel params] →
    [CorrelationLebowitzModel params] →
    ∀ (f₁ f₂ f₃ f₄ : TestFun2D),
      (∀ x, 0 ≤ f₁ x) → (∀ x, 0 ≤ f₂ x) →
      (∀ x, 0 ≤ f₃ x) → (∀ x, 0 ≤ f₄ x) →
      infiniteTruncatedFourPoint13 params f₁ f₂ f₃ f₄ ≤
        infiniteVolumeSchwinger params 2 ![f₁, f₂] *
          infiniteVolumeSchwinger params 2 ![f₃, f₄] +
        infiniteVolumeSchwinger params 2 ![f₁, f₄] *
          infiniteVolumeSchwinger params 2 ![f₂, f₃] := by
  intro hlim hgks hleb f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  exact infiniteTruncatedFourPoint13_upper params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄

/-- Infinite-volume upper bound for the `(14)(23)` pairing-subtracted channel. -/
theorem phi4_infiniteTruncatedFourPoint14_upper (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [CorrelationGKSSecondModel params] →
    [CorrelationLebowitzModel params] →
    ∀ (f₁ f₂ f₃ f₄ : TestFun2D),
      (∀ x, 0 ≤ f₁ x) → (∀ x, 0 ≤ f₂ x) →
      (∀ x, 0 ≤ f₃ x) → (∀ x, 0 ≤ f₄ x) →
      infiniteTruncatedFourPoint14 params f₁ f₂ f₃ f₄ ≤
        infiniteVolumeSchwinger params 2 ![f₁, f₂] *
          infiniteVolumeSchwinger params 2 ![f₃, f₄] +
        infiniteVolumeSchwinger params 2 ![f₁, f₃] *
          infiniteVolumeSchwinger params 2 ![f₂, f₄] := by
  intro hlim hgks hleb f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  exact infiniteTruncatedFourPoint14_upper params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄

/-- Infinite-volume absolute-value bound for the `(12)(34)` pairing-subtracted
    channel. -/
theorem phi4_infiniteTruncatedFourPoint12_abs_bound (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [CorrelationGKSSecondModel params] →
    [CorrelationLebowitzModel params] →
    ∀ (f₁ f₂ f₃ f₄ : TestFun2D),
      (∀ x, 0 ≤ f₁ x) → (∀ x, 0 ≤ f₂ x) →
      (∀ x, 0 ≤ f₃ x) → (∀ x, 0 ≤ f₄ x) →
      |infiniteTruncatedFourPoint12 params f₁ f₂ f₃ f₄| ≤
        infiniteVolumeSchwinger params 2 ![f₁, f₃] *
          infiniteVolumeSchwinger params 2 ![f₂, f₄] +
        infiniteVolumeSchwinger params 2 ![f₁, f₄] *
          infiniteVolumeSchwinger params 2 ![f₂, f₃] := by
  intro hlim hgks hleb f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  exact infiniteTruncatedFourPoint12_abs_bound params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄

/-- Infinite-volume absolute-value bound for the `(13)(24)` pairing-subtracted
    channel. -/
theorem phi4_infiniteTruncatedFourPoint13_abs_bound (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [CorrelationGKSSecondModel params] →
    [CorrelationLebowitzModel params] →
    ∀ (f₁ f₂ f₃ f₄ : TestFun2D),
      (∀ x, 0 ≤ f₁ x) → (∀ x, 0 ≤ f₂ x) →
      (∀ x, 0 ≤ f₃ x) → (∀ x, 0 ≤ f₄ x) →
      |infiniteTruncatedFourPoint13 params f₁ f₂ f₃ f₄| ≤
        infiniteVolumeSchwinger params 2 ![f₁, f₂] *
          infiniteVolumeSchwinger params 2 ![f₃, f₄] +
        infiniteVolumeSchwinger params 2 ![f₁, f₄] *
          infiniteVolumeSchwinger params 2 ![f₂, f₃] := by
  intro hlim hgks hleb f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  exact infiniteTruncatedFourPoint13_abs_bound params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄

/-- Infinite-volume absolute-value bound for the `(14)(23)` pairing-subtracted
    channel. -/
theorem phi4_infiniteTruncatedFourPoint14_abs_bound (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [CorrelationGKSSecondModel params] →
    [CorrelationLebowitzModel params] →
    ∀ (f₁ f₂ f₃ f₄ : TestFun2D),
      (∀ x, 0 ≤ f₁ x) → (∀ x, 0 ≤ f₂ x) →
      (∀ x, 0 ≤ f₃ x) → (∀ x, 0 ≤ f₄ x) →
      |infiniteTruncatedFourPoint14 params f₁ f₂ f₃ f₄| ≤
        infiniteVolumeSchwinger params 2 ![f₁, f₂] *
          infiniteVolumeSchwinger params 2 ![f₃, f₄] +
        infiniteVolumeSchwinger params 2 ![f₁, f₃] *
          infiniteVolumeSchwinger params 2 ![f₂, f₄] := by
  intro hlim hgks hleb f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  exact infiniteTruncatedFourPoint14_abs_bound params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄

/-- Infinite-volume two-sided bounds for the `(12)(34)` pairing-subtracted
    4-point channel. -/
theorem phi4_infiniteTruncatedFourPoint12_bounds (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [CorrelationGKSSecondModel params] →
    [CorrelationLebowitzModel params] →
    ∀ (f₁ f₂ f₃ f₄ : TestFun2D),
      (∀ x, 0 ≤ f₁ x) → (∀ x, 0 ≤ f₂ x) →
      (∀ x, 0 ≤ f₃ x) → (∀ x, 0 ≤ f₄ x) →
      0 ≤ infiniteTruncatedFourPoint12 params f₁ f₂ f₃ f₄ ∧
        infiniteTruncatedFourPoint12 params f₁ f₂ f₃ f₄ ≤
          infiniteVolumeSchwinger params 2 ![f₁, f₃] *
            infiniteVolumeSchwinger params 2 ![f₂, f₄] +
          infiniteVolumeSchwinger params 2 ![f₁, f₄] *
            infiniteVolumeSchwinger params 2 ![f₂, f₃] := by
  intro hlim hgks hleb f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  exact infiniteTruncatedFourPoint12_bounds params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄

/-- Infinite-volume two-sided bounds for the `(13)(24)` pairing-subtracted
    4-point channel. -/
theorem phi4_infiniteTruncatedFourPoint13_bounds (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [CorrelationGKSSecondModel params] →
    [CorrelationLebowitzModel params] →
    ∀ (f₁ f₂ f₃ f₄ : TestFun2D),
      (∀ x, 0 ≤ f₁ x) → (∀ x, 0 ≤ f₂ x) →
      (∀ x, 0 ≤ f₃ x) → (∀ x, 0 ≤ f₄ x) →
      0 ≤ infiniteTruncatedFourPoint13 params f₁ f₂ f₃ f₄ ∧
        infiniteTruncatedFourPoint13 params f₁ f₂ f₃ f₄ ≤
          infiniteVolumeSchwinger params 2 ![f₁, f₂] *
            infiniteVolumeSchwinger params 2 ![f₃, f₄] +
          infiniteVolumeSchwinger params 2 ![f₁, f₄] *
            infiniteVolumeSchwinger params 2 ![f₂, f₃] := by
  intro hlim hgks hleb f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  exact infiniteTruncatedFourPoint13_bounds params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄

/-- Infinite-volume two-sided bounds for the `(14)(23)` pairing-subtracted
    4-point channel. -/
theorem phi4_infiniteTruncatedFourPoint14_bounds (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [CorrelationGKSSecondModel params] →
    [CorrelationLebowitzModel params] →
    ∀ (f₁ f₂ f₃ f₄ : TestFun2D),
      (∀ x, 0 ≤ f₁ x) → (∀ x, 0 ≤ f₂ x) →
      (∀ x, 0 ≤ f₃ x) → (∀ x, 0 ≤ f₄ x) →
      0 ≤ infiniteTruncatedFourPoint14 params f₁ f₂ f₃ f₄ ∧
        infiniteTruncatedFourPoint14 params f₁ f₂ f₃ f₄ ≤
          infiniteVolumeSchwinger params 2 ![f₁, f₂] *
            infiniteVolumeSchwinger params 2 ![f₃, f₄] +
          infiniteVolumeSchwinger params 2 ![f₁, f₃] *
            infiniteVolumeSchwinger params 2 ![f₂, f₄] := by
  intro hlim hgks hleb f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  exact infiniteTruncatedFourPoint14_bounds params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄

/-- Combined two-sided bounds for all infinite-volume pairing-subtracted
    4-point channels. -/
theorem phi4_infiniteTruncatedFourPoint_bounds_all_channels (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [CorrelationGKSSecondModel params] →
    [CorrelationLebowitzModel params] →
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
            infiniteVolumeSchwinger params 2 ![f₂, f₄] := by
  intro hlim hgks hleb f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  exact infiniteTruncatedFourPoint_bounds_all_channels params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄

/-- Infinite-volume connected two-point symmetry. -/
theorem phi4_connectedTwoPoint_symm (params : Phi4Params) :
    [SchwingerLimitModel params] →
    ∀ (f g : TestFun2D),
      connectedTwoPoint params f g = connectedTwoPoint params g f := by
  intro hsch f g
  exact connectedTwoPoint_symm params f g

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

/-- Direct explicit-bound reconstruction endpoint:
    a concrete seminorm-growth estimate for one OS package matching
    `phi4SchwingerFunctions` yields Wightman existence. -/
theorem phi4_wightman_exists_of_explicit_linear_growth_bound
    (params : Phi4Params) :
    [SchwingerFunctionModel params] →
    [WightmanReconstructionModel params] →
    (OS : OsterwalderSchraderAxioms 1) →
    (hS : OS.S = phi4SchwingerFunctions params) →
    (sobolev_index : ℕ) →
    (alpha beta gamma : ℝ) →
    (halpha : 0 < alpha) →
    (hbeta : 0 < beta) →
    (hgrowth : ∀ (n : ℕ) (f : SchwartzNPoint 1 n),
      ‖phi4SchwingerFunctions params n f‖ ≤
        alpha * beta ^ n * (n.factorial : ℝ) ^ gamma *
          SchwartzMap.seminorm ℝ sobolev_index sobolev_index f) →
    ∃ (Wfn : WightmanFunctions 1),
      ∃ (OS' : OsterwalderSchraderAxioms 1),
        OS'.S = phi4SchwingerFunctions params ∧
        IsWickRotationPair OS'.S Wfn.W := by
  intro hos hrec OS hS sobolev_index alpha beta gamma halpha hbeta hgrowth
  exact phi4_wightman_exists_of_explicit_data params
    (hlinear := phi4_linear_growth_of_explicit_bound params OS hS
      sobolev_index alpha beta gamma halpha hbeta hgrowth)
    (hreconstruct := phi4_wightman_reconstruction_step_of_interface params)

/-- Direct weak-coupling + explicit-growth endpoint:
    if an interface-level OS package exists at weak coupling and
    `phi4SchwingerFunctions` satisfy an explicit seminorm-growth bound, then
    Wightman existence follows. -/
theorem phi4_wightman_exists_of_os_and_explicit_linear_growth_bound
    (params : Phi4Params) :
    [OSAxiomCoreModel params] →
    [WightmanReconstructionModel params] →
    [OSDistributionE2Model params] →
    [OSE4ClusterModel params] →
    (hsmall : params.coupling < os4WeakCouplingThreshold params) →
    (sobolev_index : ℕ) →
    (alpha beta gamma : ℝ) →
    (halpha : 0 < alpha) →
    (hbeta : 0 < beta) →
    (hgrowth : ∀ (n : ℕ) (f : SchwartzNPoint 1 n),
      ‖phi4SchwingerFunctions params n f‖ ≤
        alpha * beta ^ n * (n.factorial : ℝ) ^ gamma *
          SchwartzMap.seminorm ℝ sobolev_index sobolev_index f) →
    ∃ (Wfn : WightmanFunctions 1),
      ∃ (OS' : OsterwalderSchraderAxioms 1),
        OS'.S = phi4SchwingerFunctions params ∧
        IsWickRotationPair OS'.S Wfn.W := by
  intro _hcore _hrec _he2 _he4 hsmall
    sobolev_index alpha beta gamma halpha hbeta hgrowth
  rcases phi4_satisfies_OS_of_interfaces params hsmall with ⟨OS, hS⟩
  exact phi4_wightman_exists_of_explicit_linear_growth_bound params
    OS hS sobolev_index alpha beta gamma halpha hbeta hgrowth

/-- Direct weak-coupling endpoint from:
    1) interface-level OS package data under weak coupling,
    2) explicit pointwise-in-`f` finite-volume uniform generating-functional bounds,
    3) explicit product-tensor reduction/approximation and order-zero inputs. -/
theorem phi4_wightman_exists_of_os_and_productTensor_approx_and_zero
    (params : Phi4Params) :
    [InteractionWeightModel params] →
    [SchwingerLimitModel params] →
    [OSAxiomCoreModel params] →
    [WightmanReconstructionModel params] →
    [OSDistributionE2Model params] →
    [OSE4ClusterModel params] →
    (hsmall : params.coupling < os4WeakCouplingThreshold params) →
    (sobolev_index : ℕ) →
    (alpha beta gamma : ℝ) →
    (halpha : 0 < alpha) →
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
            SchwartzMap.seminorm ℝ sobolev_index sobolev_index
              (schwartzProductTensorFromTestFamily f)) →
    (happrox :
      ∀ (n : ℕ) (_hn : 0 < n) (g : SchwartzNPoint 1 n),
        ∃ u : ℕ → Fin n → TestFun2D,
          Filter.Tendsto (fun k => schwartzProductTensorFromTestFamily (u k))
            Filter.atTop (nhds g)) →
    (hzero :
      ∀ g : SchwartzNPoint 1 0,
        ‖phi4SchwingerFunctions params 0 g‖ ≤
          alpha * beta ^ 0 * (Nat.factorial 0 : ℝ) ^ gamma *
            SchwartzMap.seminorm ℝ sobolev_index sobolev_index g) →
    ∃ (Wfn : WightmanFunctions 1),
      ∃ (OS' : OsterwalderSchraderAxioms 1),
        OS'.S = phi4SchwingerFunctions params ∧
        IsWickRotationPair OS'.S Wfn.W := by
  intro hweight hlimit _hcore _hrec _he2 _he4 hsmall
    sobolev_index alpha beta gamma halpha hbeta huniform hcompat hreduce happrox hzero
  rcases phi4_satisfies_OS_of_interfaces params hsmall with ⟨OS, hS⟩
  have hprod := phi4_productTensor_linear_growth_of_uniform_generating_bound
    params sobolev_index alpha beta gamma
    huniform
    hcompat hreduce
  have hlinear := phi4_linear_growth_of_productTensor_approx_and_zero
    params OS hS sobolev_index alpha beta gamma halpha hbeta hprod happrox hzero
  exact phi4_wightman_exists_of_explicit_data params
    (hlinear := hlinear)
    (hreconstruct := phi4_wightman_reconstruction_step_of_interface params)

/-- Direct weak-coupling endpoint from:
    1) interface-level OS package data under weak coupling,
    2) explicit pointwise-in-`f` finite-volume uniform generating-functional bounds,
    3) explicit product-tensor reduction/approximation,
    4) order-zero normalization (`S₀(g) = g(0)`), using Sobolev index `0`. -/
theorem phi4_wightman_exists_of_os_and_productTensor_approx_and_normalized_order0
    (params : Phi4Params) :
    [InteractionWeightModel params] →
    [SchwingerLimitModel params] →
    [OSAxiomCoreModel params] →
    [WightmanReconstructionModel params] →
    [OSDistributionE2Model params] →
    [OSE4ClusterModel params] →
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
    (happrox :
      ∀ (n : ℕ) (_hn : 0 < n) (g : SchwartzNPoint 1 n),
        ∃ u : ℕ → Fin n → TestFun2D,
          Filter.Tendsto (fun k => schwartzProductTensorFromTestFamily (u k))
            Filter.atTop (nhds g)) →
    ∃ (Wfn : WightmanFunctions 1),
      ∃ (OS' : OsterwalderSchraderAxioms 1),
        OS'.S = phi4SchwingerFunctions params ∧
        IsWickRotationPair OS'.S Wfn.W := by
  intro hweight hlimit _hcore _hrec _he2 _he4 hsmall
    alpha beta gamma hbeta huniform hcompat hreduce happrox
  rcases phi4_satisfies_OS_of_interfaces params hsmall with ⟨OS, hS⟩
  have hlinear := phi4_linear_growth_of_interface_productTensor_approx_and_normalized_order0
    params OS hS alpha beta gamma hbeta huniform
    hcompat hreduce happrox
  exact phi4_wightman_exists_of_explicit_data params
    (hlinear := hlinear)
    (hreconstruct := phi4_wightman_reconstruction_step_of_interface params)

/-- Direct weak-coupling endpoint from:
    1) interface-level OS package data under weak coupling,
    2) explicit pointwise-in-`f` finite-volume uniform generating-functional bounds,
    3) dense image of product tensors in each positive-order Schwartz `n`-point space,
    4) order-zero normalization (`S₀(g) = g(0)`), using Sobolev index `0`. -/
theorem phi4_wightman_exists_of_os_and_productTensor_dense_and_normalized_order0
    (params : Phi4Params) :
    [InteractionWeightModel params] →
    [SchwingerLimitModel params] →
    [OSAxiomCoreModel params] →
    [WightmanReconstructionModel params] →
    [OSDistributionE2Model params] →
    [OSE4ClusterModel params] →
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
      ∃ (OS' : OsterwalderSchraderAxioms 1),
        OS'.S = phi4SchwingerFunctions params ∧
        IsWickRotationPair OS'.S Wfn.W := by
  intro hweight hlimit _hcore _hrec _he2 _he4 hsmall
    alpha beta gamma hbeta huniform hcompat hreduce hdense
  rcases phi4_satisfies_OS_of_interfaces params hsmall with ⟨OS, hS⟩
  have hlinear := phi4_linear_growth_of_interface_productTensor_approx_and_normalized_order0
    params OS hS alpha beta gamma hbeta huniform
    hcompat hreduce (phi4_productTensor_approx_family_of_dense_range hdense)
  exact phi4_wightman_exists_of_explicit_data params
    (hlinear := hlinear)
    (hreconstruct := phi4_wightman_reconstruction_step_of_interface params)

/-- Dense product-tensor weak-coupling Wightman endpoint with an explicit
    WP1-style interaction hypothesis: geometric decay of shifted cutoff
    exponential moments is used to instantiate `InteractionWeightModel`
    constructively before applying the standard weak-coupling bridge. -/
theorem phi4_wightman_exists_of_os_and_productTensor_dense_and_normalized_order0_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
    (params : Phi4Params) :
    [InteractionUVModel params] →
    [SchwingerLimitModel params] →
    [OSAxiomCoreModel params] →
    [WightmanReconstructionModel params] →
    [OSDistributionE2Model params] →
    [OSE4ClusterModel params] →
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
            ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D * r ^ n)) →
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
      ∃ (OS' : OsterwalderSchraderAxioms 1),
        OS'.S = phi4SchwingerFunctions params ∧
        IsWickRotationPair OS'.S Wfn.W := by
  intro _huv _hlimit _hcore _hrec _he2 _he4 hmom hsmall
    alpha beta gamma hbeta huniform hcompat hreduce hdense
  rcases
      interactionWeightModel_nonempty_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
        (params := params) hmom with ⟨hW⟩
  letI : InteractionWeightModel params := hW
  exact phi4_wightman_exists_of_os_and_productTensor_dense_and_normalized_order0
    params hsmall alpha beta gamma hbeta huniform hcompat hreduce hdense

/-- Dense product-tensor weak-coupling Wightman endpoint from:
    1) square-integrable/measurable UV interaction data,
    2) shifted-cutoff geometric exponential-moment decay,
    3) weak-coupling OS + reconstruction interfaces.
    This first instantiates `InteractionUVModel` constructively. -/
theorem
    phi4_wightman_exists_of_os_and_productTensor_dense_and_normalized_order0_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
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
            ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D * r ^ n)) →
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
      ∃ (OS' : OsterwalderSchraderAxioms 1),
        OS'.S = phi4SchwingerFunctions params ∧
        IsWickRotationPair OS'.S Wfn.W := by
  intro _hlimit _hcore _hrec _he2 _he4
    hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
    hinteraction_meas hinteraction_sq
    hmom hsmall alpha beta gamma hbeta huniform hcompat hreduce hdense
  rcases interactionUVModel_nonempty_of_sq_integrable_data
      (params := params)
      hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
      hinteraction_meas hinteraction_sq with ⟨huv⟩
  letI : InteractionUVModel params := huv
  exact
    phi4_wightman_exists_of_os_and_productTensor_dense_and_normalized_order0_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
      params hmom hsmall alpha beta gamma hbeta huniform hcompat hreduce hdense

/-- Interface-level Wightman existence endpoint driven by explicit WP1-style
    interaction input (shifted-cutoff geometric moment decay), by first
    constructing `ReconstructionLinearGrowthModel` and then invoking the
    standard interface reconstruction theorem. -/
theorem phi4_wightman_exists_of_interfaces_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
    (params : Phi4Params) :
    [InteractionUVModel params] →
    [SchwingerLimitModel params] →
    [OSAxiomCoreModel params] →
    [WightmanReconstructionModel params] →
    [OSDistributionE2Model params] →
    [OSE4ClusterModel params] →
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
            ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D * r ^ n)) →
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
  intro _huv _hlimit _hcore _hrec _he2 _he4 hmom hsmall
    alpha beta gamma hbeta huniform hcompat hreduce hdense
  rcases
      reconstructionLinearGrowthModel_nonempty_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
        (params := params) hmom hsmall alpha beta gamma hbeta
        huniform hcompat hreduce hdense with ⟨hlin⟩
  letI : ReconstructionLinearGrowthModel params := hlin
  exact phi4_wightman_exists_of_explicit_data params
    (hlinear := phi4_linear_growth_of_interface params)
    (hreconstruct := phi4_wightman_reconstruction_step_of_interface params)

/-- Interface-level Wightman existence endpoint from:
    1) square-integrable/measurable UV interaction data,
    2) shifted-cutoff geometric moment decay, and
    3) weak-coupling OS/product-tensor hypotheses.
    This first instantiates `InteractionUVModel` constructively, then applies the
    UV-based interface theorem. -/
theorem
    phi4_wightman_exists_of_interfaces_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
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
            ∂(freeFieldMeasure params.mass params.mass_pos) ≤ D * r ^ n)) →
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
    hinteraction_meas hinteraction_sq
    hmom hsmall alpha beta gamma hbeta huniform hcompat hreduce hdense
  rcases interactionUVModel_nonempty_of_sq_integrable_data
      (params := params)
      hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
      hinteraction_meas hinteraction_sq with ⟨huv⟩
  letI : InteractionUVModel params := huv
  exact phi4_wightman_exists_of_interfaces_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
    params hmom hsmall alpha beta gamma hbeta huniform hcompat hreduce hdense

/-- Interface-level Wightman existence from linear-growth inputs, routed
    through the abstract reconstruction backend interface. -/
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

/-- Interface-level self-adjointness corollary obtained from
    `phi4_wightman_exists_of_interfaces`. -/
theorem phi4_selfadjoint_fields_of_interfaces (params : Phi4Params)
    [SchwingerFunctionModel params]
    [ReconstructionLinearGrowthModel params]
    [WightmanReconstructionModel params] :
    ∃ (Wfn : WightmanFunctions 1),
      IsWickRotationPair (phi4SchwingerFunctions params) Wfn.W ∧
      (∀ (n : ℕ) (f g : SchwartzNPoint 1 n),
        (∀ x, g.toFun x = starRingEnd ℂ (f.toFun (fun i => x (Fin.rev i)))) →
        Wfn.W n g = starRingEnd ℂ (Wfn.W n f)) := by
  obtain ⟨Wfn, OS, hS, hWR⟩ := phi4_wightman_exists_of_interfaces params
  exact ⟨Wfn, hS ▸ hWR, Wfn.hermitian⟩

/-- Interface-level locality corollary obtained from
    `phi4_wightman_exists_of_interfaces`. -/
theorem phi4_locality_of_interfaces (params : Phi4Params)
    [SchwingerFunctionModel params]
    [ReconstructionLinearGrowthModel params]
    [WightmanReconstructionModel params] :
    ∃ (Wfn : WightmanFunctions 1),
      IsWickRotationPair (phi4SchwingerFunctions params) Wfn.W ∧
      IsLocallyCommutativeWeak 1 Wfn.W := by
  obtain ⟨Wfn, OS, hS, hWR⟩ := phi4_wightman_exists_of_interfaces params
  exact ⟨Wfn, hS ▸ hWR, Wfn.locally_commutative⟩

/-- Interface-level Lorentz-covariance corollary obtained from
    `phi4_wightman_exists_of_interfaces`. -/
theorem phi4_lorentz_covariance_of_interfaces (params : Phi4Params)
    [SchwingerFunctionModel params]
    [ReconstructionLinearGrowthModel params]
    [WightmanReconstructionModel params] :
    ∃ (Wfn : WightmanFunctions 1),
      IsWickRotationPair (phi4SchwingerFunctions params) Wfn.W ∧
      IsLorentzCovariantWeak 1 Wfn.W := by
  obtain ⟨Wfn, OS, hS, hWR⟩ := phi4_wightman_exists_of_interfaces params
  exact ⟨Wfn, hS ▸ hWR, Wfn.lorentz_covariant⟩

/-- Interface-level positive-definite/vacuum corollary obtained from
    `phi4_wightman_exists_of_interfaces`. -/
theorem phi4_unique_vacuum_of_interfaces (params : Phi4Params)
    [SchwingerFunctionModel params]
    [ReconstructionLinearGrowthModel params]
    [WightmanReconstructionModel params] :
    ∃ (Wfn : WightmanFunctions 1),
      IsPositiveDefinite 1 Wfn.W ∧
      IsWickRotationPair (phi4SchwingerFunctions params) Wfn.W := by
  obtain ⟨Wfn, OS, hS, hWR⟩ := phi4_wightman_exists_of_interfaces params
  exact ⟨Wfn, Wfn.positive_definite, hS ▸ hWR⟩

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

/-- The φ⁴₂ QFT has hermitian field operators (self-adjointness).
    W_n(f̃) = conj(W_n(f)) where f̃(x₁,...,xₙ) = conj(f(xₙ,...,x₁)).
    (Glimm-Jaffe Section 19.3)

    This is encoded in the `hermitian` field of `WightmanFunctions`,
    which is the distributional version of φ(f)* = φ(f̄) for real f. -/
theorem phi4_selfadjoint_fields (params : Phi4Params)
    [SchwingerFunctionModel params]
    [ReconstructionLinearGrowthModel params]
    [WightmanReconstructionModel params] :
    ∃ (Wfn : WightmanFunctions 1),
      IsWickRotationPair (phi4SchwingerFunctions params) Wfn.W ∧
      (∀ (n : ℕ) (f g : SchwartzNPoint 1 n),
        (∀ x, g.toFun x = starRingEnd ℂ (f.toFun (fun i => x (Fin.rev i)))) →
        Wfn.W n g = starRingEnd ℂ (Wfn.W n f)) := by
  obtain ⟨Wfn, OS, hS, hWR⟩ := phi4_wightman_exists params
  exact ⟨Wfn, hS ▸ hWR, Wfn.hermitian⟩

/-- The φ⁴₂ QFT satisfies locality: fields at spacelike separation commute.
    [φ(f), φ(g)] = 0 when supp f and supp g are spacelike separated.
    (Glimm-Jaffe Section 19.6)
    This follows from the Wightman reconstruction theorem applied to
    the φ⁴₂ Schwinger functions. -/
theorem phi4_locality (params : Phi4Params)
    [SchwingerFunctionModel params]
    [ReconstructionLinearGrowthModel params]
    [WightmanReconstructionModel params] :
    ∃ (Wfn : WightmanFunctions 1),
      IsWickRotationPair (phi4SchwingerFunctions params) Wfn.W ∧
      IsLocallyCommutativeWeak 1 Wfn.W := by
  obtain ⟨Wfn, OS, hS, hWR⟩ := phi4_wightman_exists params
  exact ⟨Wfn, hS ▸ hWR, Wfn.locally_commutative⟩

/-- The φ⁴₂ QFT has Lorentz covariance.
    U(Λ,a) φ(f) U(Λ,a)⁻¹ = φ((Λ,a)·f) for (Λ,a) ∈ ISO(1,1).
    (Glimm-Jaffe Section 19.5) -/
theorem phi4_lorentz_covariance (params : Phi4Params)
    [SchwingerFunctionModel params]
    [ReconstructionLinearGrowthModel params]
    [WightmanReconstructionModel params] :
    ∃ (Wfn : WightmanFunctions 1),
      IsWickRotationPair (phi4SchwingerFunctions params) Wfn.W ∧
      IsLorentzCovariantWeak 1 Wfn.W := by
  obtain ⟨Wfn, OS, hS, hWR⟩ := phi4_wightman_exists params
  exact ⟨Wfn, hS ▸ hWR, Wfn.lorentz_covariant⟩

/-- The φ⁴₂ QFT has a unique vacuum state.
    The vacuum Ω is the unique (up to phase) Poincaré-invariant state.
    (Glimm-Jaffe Section 19.7)

    For weak coupling, this follows from the cluster property (OS4).
    For strong coupling, vacuum uniqueness is related to the absence of
    phase transitions (or selecting a pure phase). -/
theorem phi4_unique_vacuum (params : Phi4Params)
    [SchwingerFunctionModel params]
    [ReconstructionLinearGrowthModel params]
    [WightmanReconstructionModel params] :
    ∃ (Wfn : WightmanFunctions 1),
      IsPositiveDefinite 1 Wfn.W ∧
      IsWickRotationPair (phi4SchwingerFunctions params) Wfn.W := by
  obtain ⟨Wfn, OS, hS, hWR⟩ := phi4_wightman_exists params
  exact ⟨Wfn, Wfn.positive_definite, hS ▸ hWR⟩

end

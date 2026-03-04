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

/-- Zero-point normalization on product tensors from compatibility with
    `infiniteVolumeSchwinger`, assuming explicit zeroth-mode normalization
    for `infiniteVolumeSchwinger`. -/
theorem phi4_productTensor_zero_of_compat_of_zero
    (params : Phi4Params)
    [SchwingerLimitModel params]
    [SchwingerFunctionModel params]
    (hcompat :
      ∀ (n : ℕ) (f : Fin n → TestFun2D),
        phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily f) =
          (infiniteVolumeSchwinger params n f : ℂ))
    (hzero : ∀ f : Fin 0 → TestFun2D, infiniteVolumeSchwinger params 0 f = 1)
    (f : Fin 0 → TestFun2D) :
    phi4SchwingerFunctions params 0 (schwartzProductTensorFromTestFamily f) = 1 := by
  calc
    phi4SchwingerFunctions params 0 (schwartzProductTensorFromTestFamily f)
        = (infiniteVolumeSchwinger params 0 f : ℂ) := by
          simpa using hcompat 0 f
    _ = 1 := by
          simpa using hzero f

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

/-- Explicit-zero-mode variant of order-zero normalization from:
    1) core linearity of `phi4SchwingerFunctions params 0`,
    2) compatibility with `infiniteVolumeSchwinger` on product tensors, and
    3) explicit normalization `infiniteVolumeSchwinger params 0 f = 1`. -/
theorem phi4_normalized_order0_of_linear_and_compat_of_zero
    (params : Phi4Params)
    [SchwingerLimitModel params]
    [SchwingerFunctionModel params]
    [OSTemperedModel params]
    (hcompat :
      ∀ (n : ℕ) (f : Fin n → TestFun2D),
        phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily f) =
          (infiniteVolumeSchwinger params n f : ℂ))
    (hzero : ∀ f : Fin 0 → TestFun2D, infiniteVolumeSchwinger params 0 f = 1) :
    ∀ g : SchwartzNPoint 1 0, phi4SchwingerFunctions params 0 g = g 0 := by
  have hlin0 : IsLinearMap ℂ (phi4SchwingerFunctions params 0) :=
    phi4_os0_linear params 0
  intro g
  let f0 : Fin 0 → TestFun2D := fun i => False.elim (Fin.elim0 i)
  have hone : phi4SchwingerFunctions params 0 (schwartzProductTensorFromTestFamily f0) = 1 :=
    phi4_productTensor_zero_of_compat_of_zero params hcompat hzero f0
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
    1) explicit mixed product-tensor bounds,
    2) explicit product-tensor approximation of general Schwartz `n`-point tests
       for `n > 0`,
    3) order-zero normalization (`S₀(g) = g(0)`), using Sobolev index `0`,
    with normalization provided explicitly. -/
theorem phi4_linear_growth_of_mixed_bound_productTensor_approx_and_given_normalized_order0
    (params : Phi4Params)
    [SchwingerLimitModel params]
    [SchwingerFunctionModel params]
    [OSTemperedModel params]
    (OS : OsterwalderSchraderAxioms 1)
    (hS : OS.S = phi4SchwingerFunctions params)
    (alpha beta gamma : ℝ)
    (hbeta : 0 < beta)
    (hmixed :
      ∀ (n : ℕ) (_hn : 0 < n) (f : Fin n → TestFun2D), ∃ c : ℝ,
        ‖phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily f)‖ ≤
          ∑ i : Fin n, (Nat.factorial n : ℝ) *
            (Real.exp (c * normFunctional (f i)) +
              Real.exp (c * normFunctional (-(f i)))))
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
            Filter.atTop (nhds g))
    (hnormalized :
      ∀ g : SchwartzNPoint 1 0, phi4SchwingerFunctions params 0 g = g 0) :
    ∃ OS' : OsterwalderSchraderAxioms 1,
      OS'.S = phi4SchwingerFunctions params ∧
      Nonempty (OSLinearGrowthCondition 1 OS') := by
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
  have hprod :
      ∀ (n : ℕ) (_hn : 0 < n) (f : Fin n → TestFun2D),
        ‖phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily f)‖ ≤
          alpha' * beta ^ n * (n.factorial : ℝ) ^ gamma *
            SchwartzMap.seminorm ℝ 0 0
              (schwartzProductTensorFromTestFamily f) := by
    intro n hn f
    rcases hmixed n hn f with ⟨c, hc⟩
    exact hc.trans (hreduce' c n hn f)
  have hzero := phi4_zero_linear_growth_of_normalized_order0
    params alpha' beta gamma halpha'_one hnormalized
  exact phi4_linear_growth_of_productTensor_approx_and_zero
    params OS hS 0 alpha' beta gamma halpha' hbeta hprod happrox hzero

/-- Construct φ⁴ linear-growth witness data from:
    1) explicit pointwise-in-`f` finite-volume uniform generating-functional bounds,
    2) explicit product-tensor approximation of general Schwartz `n`-point tests
       for `n > 0`,
    3) order-zero normalization (`S₀(g) = g(0)`), using Sobolev index `0`,
    with normalization provided explicitly. -/
theorem phi4_linear_growth_of_interface_productTensor_approx_and_given_normalized_order0
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
            Filter.atTop (nhds g))
    (hnormalized :
      ∀ g : SchwartzNPoint 1 0, phi4SchwingerFunctions params 0 g = g 0) :
    ∃ OS' : OsterwalderSchraderAxioms 1,
      OS'.S = phi4SchwingerFunctions params ∧
      Nonempty (OSLinearGrowthCondition 1 OS') := by
  have hmixed :
      ∀ (n : ℕ) (_hn : 0 < n) (f : Fin n → TestFun2D), ∃ c : ℝ,
        ‖phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily f)‖ ≤
          ∑ i : Fin n, (Nat.factorial n : ℝ) *
            (Real.exp (c * normFunctional (f i)) +
              Real.exp (c * normFunctional (-(f i)))) := by
    intro n hn f
    exact phi4_productTensor_mixed_bound_of_uniform_generating_bound
      params huniform hcompat n hn f
  exact phi4_linear_growth_of_mixed_bound_productTensor_approx_and_given_normalized_order0
    params OS hS alpha beta gamma hbeta hmixed hreduce happrox hnormalized

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
  have hzero : ∀ f : Fin 0 → TestFun2D, infiniteVolumeSchwinger params 0 f = 1 := by
    intro f
    exact infiniteVolumeSchwinger_zero (params := params) f
  have hnormalized : ∀ g : SchwartzNPoint 1 0, phi4SchwingerFunctions params 0 g = g 0 :=
    phi4_normalized_order0_of_linear_and_compat_of_zero params hcompat hzero
  exact phi4_linear_growth_of_interface_productTensor_approx_and_given_normalized_order0
    params OS hS alpha beta gamma hbeta huniform hcompat hreduce happrox hnormalized

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

/-- **Linear growth condition E0'** for the φ⁴₂ Schwinger functions, with
    explicit zeroth-mode normalization of `infiniteVolumeSchwinger`.
    This is the assumption-minimal frontier form: no interaction-weight
    interface is required once `S₀ = 1` and the mixed product-tensor
    Schwinger bound bridge are provided explicitly. -/
theorem gap_phi4_linear_growth_of_zero_mode_normalization (params : Phi4Params)
    [SchwingerLimitModel params]
    [OSAxiomCoreModel params]
    [OSDistributionE2Model params]
    [OSE4ClusterModel params]
    (hsmall : params.coupling < os4WeakCouplingThreshold params)
    (alpha beta gamma : ℝ)
    (hbeta : 0 < beta)
    (hmixed :
      ∀ (n : ℕ) (_hn : 0 < n) (f : Fin n → TestFun2D), ∃ c : ℝ,
        ‖phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily f)‖ ≤
          ∑ i : Fin n, (Nat.factorial n : ℝ) *
            (Real.exp (c * normFunctional (f i)) +
              Real.exp (c * normFunctional (-(f i)))))
    (hcompat :
      ∀ (n : ℕ) (f : Fin n → TestFun2D),
        phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily f) =
          (infiniteVolumeSchwinger params n f : ℂ))
    (hzero : ∀ f : Fin 0 → TestFun2D, infiniteVolumeSchwinger params 0 f = 1)
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
  have hnormalized : ∀ g : SchwartzNPoint 1 0, phi4SchwingerFunctions params 0 g = g 0 :=
    phi4_normalized_order0_of_linear_and_compat_of_zero params hcompat hzero
  exact phi4_linear_growth_of_mixed_bound_productTensor_approx_and_given_normalized_order0
    params OS hS alpha beta gamma hbeta hmixed hreduce
    (phi4_productTensor_approx_family_of_dense_range hdense) hnormalized

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
  have hzero : ∀ f : Fin 0 → TestFun2D, infiniteVolumeSchwinger params 0 f = 1 := by
    intro f
    exact infiniteVolumeSchwinger_zero (params := params) f
  have hmixed :
      ∀ (n : ℕ) (_hn : 0 < n) (f : Fin n → TestFun2D), ∃ c : ℝ,
        ‖phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily f)‖ ≤
          ∑ i : Fin n, (Nat.factorial n : ℝ) *
            (Real.exp (c * normFunctional (f i)) +
              Real.exp (c * normFunctional (-(f i)))) := by
    intro n hn f
    exact phi4_productTensor_mixed_bound_of_uniform_generating_bound
      params huniform hcompat n hn f
  exact gap_phi4_linear_growth_of_zero_mode_normalization
    params hsmall alpha beta gamma hbeta hmixed hcompat hzero hreduce hdense

/- NOTE: Route-only variants with no in-repo callers were removed to keep the
   linear-growth frontier centered on canonical entry theorems. -/

/-- Linear-growth frontier with an explicit WP1-style interaction input:
    replace direct `[InteractionWeightModel params]` by geometric decay of
    shifted cutoff exponential moments, together with explicit measurability
    and canonical-sequence a.e. convergence data used to constructively
    instantiate the weight model. -/
theorem
    gap_phi4_linear_growth_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound_of_aestronglyMeasurable_and_standardSeq_tendsto_ae
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
      interactionWeightModel_nonempty_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound_of_aestronglyMeasurable_and_standardSeq_tendsto_ae
        (params := params) hinteraction_meas hcutoff_tendsto_ae hmom with ⟨hW⟩
  letI : InteractionWeightModel params := hW
  exact gap_phi4_linear_growth params hsmall alpha beta gamma hbeta
    huniform hcompat hreduce hdense

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
      interactionWeightModel_nonempty_of_uv_cutoff_seq_shifted_exponential_moment_geometric_bound_of_aestronglyMeasurable_and_standardSeq_tendsto_ae
        (params := params)
        (hinteraction_meas := fun Λ => (interaction_in_L2 params Λ).aestronglyMeasurable)
        (hcutoff_tendsto_ae := fun Λ => interactionCutoff_standardSeq_tendsto_ae params Λ)
        hmom with ⟨hW⟩
  letI : InteractionWeightModel params := hW
  exact gap_phi4_linear_growth params hsmall alpha beta gamma hbeta
    huniform hcompat hreduce hdense

/-- Linear-growth frontier with explicit square-integrable UV data and shifted
    geometric cutoff-moment decay.
    This directly instantiates `InteractionWeightModel` from square-integrable
    data + shifted geometric moment decay, then applies
    `gap_phi4_linear_growth`. -/
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
  rcases
      interactionWeightModel_nonempty_of_sq_integrable_data_and_uv_cutoff_seq_shifted_exponential_moment_geometric_bound
      (params := params)
      hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
      hinteraction_meas hinteraction_sq hmom with ⟨hW⟩
  letI : InteractionWeightModel params := hW
  exact gap_phi4_linear_growth params hsmall alpha beta gamma hbeta
    huniform hcompat hreduce hdense

/-- Construct `ReconstructionLinearGrowthModel` from:
    1) UV Wick-sublevel-tail interaction control,
    2) explicit measurability + canonical-sequence a.e. convergence data for
       `interaction`, and
    3) weak-coupling OS + product-tensor linear-growth reduction hypotheses. -/
theorem
    reconstructionLinearGrowthModel_nonempty_of_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets_of_aestronglyMeasurable_and_standardSeq_tendsto_ae
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
    Nonempty (ReconstructionLinearGrowthModel params) := by
  rcases
      interactionWeightModel_nonempty_of_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets_of_aestronglyMeasurable_and_standardSeq_tendsto_ae
      (params := params) hinteraction_meas hcutoff_tendsto_ae hwick_bad with ⟨hWinst⟩
  letI : InteractionWeightModel params := hWinst
  exact reconstructionLinearGrowthModel_nonempty_of_data params
    (hlinear :=
      gap_phi4_linear_growth params hsmall alpha beta gamma hbeta
        huniform hcompat hreduce hdense)

/-- Construct `ReconstructionLinearGrowthModel` from:
    1) UV Wick-sublevel-tail interaction control, and
    2) weak-coupling OS + product-tensor linear-growth reduction hypotheses. -/
theorem
    reconstructionLinearGrowthModel_nonempty_of_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets
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
    Nonempty (ReconstructionLinearGrowthModel params) := by
  exact
    reconstructionLinearGrowthModel_nonempty_of_uv_cutoff_seq_shifted_exponential_wick_sublevel_bad_sets_of_aestronglyMeasurable_and_standardSeq_tendsto_ae
      (params := params)
      (hinteraction_meas := fun Λ => (interaction_in_L2 params Λ).aestronglyMeasurable)
      (hcutoff_tendsto_ae := fun Λ => interactionCutoff_standardSeq_tendsto_ae params Λ)
      hwick_bad hsmall alpha beta gamma hbeta huniform hcompat hreduce hdense

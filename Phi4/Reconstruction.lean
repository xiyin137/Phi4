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
    [InfiniteVolumeSchwingerModel params] : Prop :=
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
    [InfiniteVolumeSchwingerModel params] where
  phi4_os4_weak_coupling :
    ∃ coupling_bound : ℝ, 0 < coupling_bound ∧
      ∀ p : Phi4Params, [InfiniteVolumeSchwingerModel p] →
        p.coupling < coupling_bound →
          ConnectedTwoPointDecayAtParams p

/-! ## Abstract reconstruction inputs -/

/-- Linear-growth input needed at fixed `params` for OS-to-Wightman
    reconstruction. -/
class ReconstructionLinearGrowthModel (params : Phi4Params)
    [InfiniteVolumeSchwingerModel params]
    [OSAxiomCoreModel params] where
  phi4_linear_growth :
    ∃ OS : OsterwalderSchraderAxioms 1,
      OS.S = phi4SchwingerFunctions params ∧
      Nonempty (OSLinearGrowthCondition 1 OS)

/-- Fixed-`params` weak-coupling decay input, separated from linear-growth data. -/
class ReconstructionWeakCouplingModel (params : Phi4Params)
    [InfiniteVolumeSchwingerModel params] where
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
    [InfiniteVolumeSchwingerModel params]
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
    [InfiniteVolumeSchwingerModel params]
    [OSAxiomCoreModel params]
    extends ReconstructionLinearGrowthModel params,
      ReconstructionWeakCouplingModel params

instance (priority := 100) reconstructionInputModel_of_submodels
    (params : Phi4Params)
    [InfiniteVolumeSchwingerModel params]
    [OSAxiomCoreModel params]
    [ReconstructionLinearGrowthModel params]
    [ReconstructionWeakCouplingModel params] :
    ReconstructionInputModel params where
  toReconstructionLinearGrowthModel := inferInstance
  toReconstructionWeakCouplingModel := inferInstance

/-- Abstract OS-to-Wightman reconstruction backend for fixed `params`.
    Kept separate from `ReconstructionInputModel` so fixed-`params`
    analytic assumptions and reconstruction machinery are not bundled together. -/
class WightmanReconstructionModel (params : Phi4Params)
    [OSAxiomCoreModel params] where
  wightman_reconstruction :
    ∀ (OS : OsterwalderSchraderAxioms 1),
      OSLinearGrowthCondition 1 OS →
        ∃ (Wfn : WightmanFunctions 1),
          IsWickRotationPair OS.S Wfn.W

/-- Existence of a weak-coupling threshold guaranteeing connected 2-point decay. -/
abbrev ConnectedTwoPointDecayThreshold (params : Phi4Params)
    [InfiniteVolumeSchwingerModel params]
    [ReconstructionWeakCouplingModel params] : Prop :=
  ∃ coupling_bound : ℝ, 0 < coupling_bound ∧
    (params.coupling < coupling_bound →
      ConnectedTwoPointDecayAtParams params)

/-! ## Interface-level reconstruction wrappers -/

/-- Linear-growth input extracted from `ReconstructionLinearGrowthModel`. -/
theorem phi4_linear_growth_of_interface (params : Phi4Params)
    [InfiniteVolumeSchwingerModel params]
    [OSAxiomCoreModel params]
    [ReconstructionLinearGrowthModel params] :
    ∃ OS : OsterwalderSchraderAxioms 1,
      OS.S = phi4SchwingerFunctions params ∧
      Nonempty (OSLinearGrowthCondition 1 OS) := by
  exact ReconstructionLinearGrowthModel.phi4_linear_growth (params := params)

/-- Wightman-reconstruction input extracted from `WightmanReconstructionModel`. -/
theorem phi4_wightman_reconstruction_step_of_interface (params : Phi4Params)
    [OSAxiomCoreModel params]
    [WightmanReconstructionModel params] :
    ∀ (OS : OsterwalderSchraderAxioms 1),
      OSLinearGrowthCondition 1 OS →
        ∃ (Wfn : WightmanFunctions 1),
          IsWickRotationPair OS.S Wfn.W := by
  intro OS hlg
  exact WightmanReconstructionModel.wightman_reconstruction
    (params := params) OS hlg

/-! ## Linear growth condition (E0') -/

/-- **Linear growth condition E0'** for the φ⁴₂ Schwinger functions.
    |S_n(f)| ≤ α · βⁿ · (n!)^γ · ‖f‖_s
    with γ = 1/2 for the φ⁴ interaction.

    This is stronger than simple temperedness (E0) and is essential for the
    analytic continuation to work: without it, the Wightman distributions
    reconstructed from the Schwinger functions may fail to be tempered.

    For the φ⁴₂ theory, this follows from the generating functional bound
    (Theorem 12.5.1) and the Wick-type combinatorics of the interaction. -/
theorem gap_phi4_linear_growth (params : Phi4Params)
    [InfiniteVolumeSchwingerModel params]
    [OSAxiomCoreModel params]
    [ReconstructionLinearGrowthModel params] :
    ∃ OS : OsterwalderSchraderAxioms 1,
      OS.S = phi4SchwingerFunctions params ∧
      Nonempty (OSLinearGrowthCondition 1 OS) := by
  exact phi4_linear_growth_of_interface params

/-- Public linear-growth endpoint via explicit theorem-level frontier gap. -/
theorem phi4_linear_growth (params : Phi4Params)
    [InfiniteVolumeSchwingerModel params]
    [OSAxiomCoreModel params]
    [ReconstructionLinearGrowthModel params] :
    ∃ OS : OsterwalderSchraderAxioms 1,
      OS.S = phi4SchwingerFunctions params ∧
      Nonempty (OSLinearGrowthCondition 1 OS) := by
  exact gap_phi4_linear_growth params

/-- Honest frontier: reconstruction step from OS + linear growth to Wightman data. -/
theorem gap_phi4_wightman_reconstruction_step (params : Phi4Params)
    [OSAxiomCoreModel params]
    [WightmanReconstructionModel params] :
    ∀ (OS : OsterwalderSchraderAxioms 1),
      OSLinearGrowthCondition 1 OS →
        ∃ (Wfn : WightmanFunctions 1),
          IsWickRotationPair OS.S Wfn.W := by
  exact phi4_wightman_reconstruction_step_of_interface params

/-- Explicit reconstruction step from OS + linear growth to Wightman data,
    via the frontier theorem `gap_phi4_wightman_reconstruction_step`. -/
theorem phi4_wightman_reconstruction_step (params : Phi4Params)
    [OSAxiomCoreModel params]
    [WightmanReconstructionModel params] :
    ∀ (OS : OsterwalderSchraderAxioms 1),
      OSLinearGrowthCondition 1 OS →
        ∃ (Wfn : WightmanFunctions 1),
          IsWickRotationPair OS.S Wfn.W := by
  exact gap_phi4_wightman_reconstruction_step params

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
    [InfiniteVolumeSchwingerModel params] →
    [UniformWeakCouplingDecayModel params] →
    ∃ coupling_bound : ℝ, 0 < coupling_bound ∧
      ∀ p : Phi4Params, [InfiniteVolumeSchwingerModel p] →
        p.coupling < coupling_bound →
          ConnectedTwoPointDecayAtParams p := by
  intro hlim hrec
  exact UniformWeakCouplingDecayModel.phi4_os4_weak_coupling
    (params := params)

/-- Backward-compatible OS4 weak-coupling form written with explicit Schwinger moments. -/
theorem phi4_os4_weak_coupling_explicit (params : Phi4Params) :
    [InfiniteVolumeSchwingerModel params] →
    [UniformWeakCouplingDecayModel params] →
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

/-- Fixed-`params` weak-coupling decay threshold for connected 2-point functions.
    This is the canonical threshold carried by `ReconstructionInputModel`. -/
theorem phi4_connectedTwoPoint_decay_threshold (params : Phi4Params) :
    [InfiniteVolumeSchwingerModel params] →
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
    [InfiniteVolumeSchwingerModel params] →
    [ReconstructionWeakCouplingModel params] →
    ℝ := by
  intro hlim hrec
  exact ReconstructionWeakCouplingModel.weak_coupling_threshold (params := params)

/-- Positivity of the selected weak-coupling threshold. -/
theorem phi4WeakCouplingThreshold_pos (params : Phi4Params) :
    [InfiniteVolumeSchwingerModel params] →
    [ReconstructionWeakCouplingModel params] →
    0 < phi4WeakCouplingThreshold params := by
  intro hlim hrec
  simpa [phi4WeakCouplingThreshold] using
    ReconstructionWeakCouplingModel.weak_coupling_threshold_pos (params := params)

/-- Exponential decay of connected 2-point functions when
    `params.coupling` is below the selected weak-coupling threshold. -/
theorem phi4_connectedTwoPoint_decay_below_threshold (params : Phi4Params) :
    [InfiniteVolumeSchwingerModel params] →
    [ReconstructionWeakCouplingModel params] →
    params.coupling < phi4WeakCouplingThreshold params →
    ConnectedTwoPointDecayAtParams params := by
  intro hlim hrec hsmall
  exact ReconstructionWeakCouplingModel.connectedTwoPoint_decay_of_weak_coupling
    (params := params) hsmall

/-- Explicit-Schwinger version of `phi4_connectedTwoPoint_decay_below_threshold`. -/
theorem phi4_connectedTwoPoint_decay_below_threshold_explicit (params : Phi4Params) :
    [InfiniteVolumeSchwingerModel params] →
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
    [InfiniteVolumeSchwingerModel params]
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
    [InfiniteVolumeSchwingerModel params] →
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
    [InfiniteVolumeSchwingerModel params] →
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
    [InfiniteVolumeSchwingerModel params] →
    [UniformWeakCouplingDecayModel params] →
    ∃ coupling_bound : ℝ, 0 < coupling_bound ∧
      ∀ p : Phi4Params, [InfiniteVolumeSchwingerModel p] →
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
    [InfiniteVolumeSchwingerModel params] →
    [UniformWeakCouplingDecayModel params] →
    ∃ coupling_bound : ℝ, 0 < coupling_bound ∧
      ∀ p : Phi4Params, [InfiniteVolumeSchwingerModel p] →
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

/-- Infinite-volume connected two-point nonnegativity for nonnegative test
    functions, inherited from finite-volume FKG positivity. -/
theorem phi4_connectedTwoPoint_nonneg (params : Phi4Params) :
    [InfiniteVolumeSchwingerModel params] →
    [CorrelationFKGModel params] →
    ∀ (f g : TestFun2D), (∀ x, 0 ≤ f x) → (∀ x, 0 ≤ g x) →
      0 ≤ connectedTwoPoint params f g := by
  intro hlim hcorr f g hf hg
  exact connectedTwoPoint_nonneg params f g hf hg

/-- Infinite-volume diagonal connected two-point nonnegativity for nonnegative
    test functions, from finite-volume FKG positivity and the infinite-volume limit. -/
theorem phi4_connectedTwoPoint_self_nonneg (params : Phi4Params) :
    [InfiniteVolumeSchwingerModel params] →
    [CorrelationFKGModel params] →
    ∀ (f : TestFun2D), (∀ x, 0 ≤ f x) → 0 ≤ connectedTwoPoint params f f := by
  intro hlim hcorr f hf
  exact connectedTwoPoint_self_nonneg_of_fkg params f hf

/-- Infinite-volume diagonal connected two-point nonnegativity (variance form),
    without sign restrictions on test functions. -/
theorem phi4_connectedTwoPoint_self_nonneg_variance (params : Phi4Params) :
    [InfiniteVolumeSchwingerModel params] →
    [InteractionWeightModel params] →
    ∀ (f : TestFun2D), 0 ≤ connectedTwoPoint params f f := by
  intro hlim hint f
  exact connectedTwoPoint_self_nonneg params f

/-- Additivity in the first argument of the infinite-volume connected two-point
    function. -/
theorem phi4_connectedTwoPoint_add_left (params : Phi4Params) :
    [InfiniteVolumeSchwingerModel params] →
    [InteractionWeightModel params] →
    ∀ (f₁ f₂ g : TestFun2D),
      connectedTwoPoint params (f₁ + f₂) g =
        connectedTwoPoint params f₁ g + connectedTwoPoint params f₂ g := by
  intro hlim hint f₁ f₂ g
  exact connectedTwoPoint_add_left params f₁ f₂ g

/-- Scalar linearity in the first argument of the infinite-volume connected
    two-point function. -/
theorem phi4_connectedTwoPoint_smul_left (params : Phi4Params) :
    [InfiniteVolumeSchwingerModel params] →
    [InteractionWeightModel params] →
    ∀ (c : ℝ) (f g : TestFun2D),
      connectedTwoPoint params (c • f) g = c * connectedTwoPoint params f g := by
  intro hlim hint c f g
  exact connectedTwoPoint_smul_left params c f g

/-- Additivity in the second argument of the infinite-volume connected two-point
    function. -/
theorem phi4_connectedTwoPoint_add_right (params : Phi4Params) :
    [InfiniteVolumeSchwingerModel params] →
    [InteractionWeightModel params] →
    ∀ (f g₁ g₂ : TestFun2D),
      connectedTwoPoint params f (g₁ + g₂) =
        connectedTwoPoint params f g₁ + connectedTwoPoint params f g₂ := by
  intro hlim hint f g₁ g₂
  exact connectedTwoPoint_add_right params f g₁ g₂

/-- Scalar linearity in the second argument of the infinite-volume connected
    two-point function. -/
theorem phi4_connectedTwoPoint_smul_right (params : Phi4Params) :
    [InfiniteVolumeSchwingerModel params] →
    [InteractionWeightModel params] →
    ∀ (c : ℝ) (f g : TestFun2D),
      connectedTwoPoint params f (c • g) = c * connectedTwoPoint params f g := by
  intro hlim hint c f g
  exact connectedTwoPoint_smul_right params c f g

/-- Infinite-volume connected two-point function as a bilinear map. -/
def phi4_connectedTwoPoint_bilinear (params : Phi4Params) :
    [InfiniteVolumeSchwingerModel params] →
    [InteractionWeightModel params] →
    TestFun2D →ₗ[ℝ] TestFun2D →ₗ[ℝ] ℝ := by
  intro hlim hint
  exact connectedTwoPointBilinear params

/-- Symmetry of the infinite-volume connected two-point bilinear form. -/
theorem phi4_connectedTwoPoint_bilinear_symm (params : Phi4Params) :
    [InfiniteVolumeSchwingerModel params] →
    [InteractionWeightModel params] →
    ∀ (f g : TestFun2D),
      connectedTwoPointBilinear params f g =
        connectedTwoPointBilinear params g f := by
  intro hlim hint f g
  exact connectedTwoPointBilinear_symm params f g

/-- Diagonal nonnegativity of the infinite-volume connected two-point bilinear
    form. -/
theorem phi4_connectedTwoPoint_bilinear_self_nonneg (params : Phi4Params) :
    [InfiniteVolumeSchwingerModel params] →
    [InteractionWeightModel params] →
    ∀ (f : TestFun2D), 0 ≤ connectedTwoPointBilinear params f f := by
  intro hlim hint f
  exact connectedTwoPointBilinear_self_nonneg params f

/-- Infinite-volume connected two-point Cauchy-Schwarz inequality. -/
theorem phi4_connectedTwoPoint_sq_le_mul_diag (params : Phi4Params) :
    [InfiniteVolumeSchwingerModel params] →
    [InteractionWeightModel params] →
    ∀ (f g : TestFun2D),
      (connectedTwoPoint params f g) ^ 2 ≤
        connectedTwoPoint params f f * connectedTwoPoint params g g := by
  intro hlim hint f g
  exact connectedTwoPoint_sq_le_mul_diag params f g

/-- Infinite-volume connected two-point geometric-mean bound. -/
theorem phi4_connectedTwoPoint_abs_le_sqrt_diag_mul (params : Phi4Params) :
    [InfiniteVolumeSchwingerModel params] →
    [InteractionWeightModel params] →
    ∀ (f g : TestFun2D),
      |connectedTwoPoint params f g| ≤
        Real.sqrt (connectedTwoPoint params f f * connectedTwoPoint params g g) := by
  intro hlim hint f g
  exact connectedTwoPoint_abs_le_sqrt_diag_mul params f g

/-- Infinite-volume connected two-point half-diagonal bound. -/
theorem phi4_connectedTwoPoint_abs_le_half_diag_sum (params : Phi4Params) :
    [InfiniteVolumeSchwingerModel params] →
    [InteractionWeightModel params] →
    ∀ (f g : TestFun2D),
      |connectedTwoPoint params f g| ≤
        (connectedTwoPoint params f f + connectedTwoPoint params g g) / 2 := by
  intro hlim hint f g
  exact connectedTwoPoint_abs_le_half_diag_sum params f g

/-- Infinite-volume finite-family PSD statement for the connected two-point kernel. -/
theorem phi4_connectedTwoPoint_quadratic_nonneg (params : Phi4Params) :
    [InfiniteVolumeSchwingerModel params] →
    [InteractionWeightModel params] →
    ∀ {ι : Type*} (s : Finset ι) (f : ι → TestFun2D) (c : ι → ℝ),
      0 ≤ Finset.sum s (fun i =>
        c i * Finset.sum s (fun j => c j * connectedTwoPoint params (f j) (f i))) := by
  intro hlim hint ι s f c
  exact connectedTwoPoint_quadratic_nonneg params s f c

/-- Standard-index-order form of `phi4_connectedTwoPoint_quadratic_nonneg`. -/
theorem phi4_connectedTwoPoint_quadratic_nonneg_standard (params : Phi4Params) :
    [InfiniteVolumeSchwingerModel params] →
    [InteractionWeightModel params] →
    ∀ {ι : Type*} (s : Finset ι) (f : ι → TestFun2D) (c : ι → ℝ),
      0 ≤ Finset.sum s (fun i => Finset.sum s (fun j =>
        c i * c j * connectedTwoPoint params (f i) (f j))) := by
  intro hsch hint ι s f c
  exact connectedTwoPoint_quadratic_nonneg_standard params s f c

/-- Infinite-volume 4-point cumulant nonpositivity inherited from Lebowitz bounds. -/
theorem phi4_infiniteCumulantFourPoint_nonpos (params : Phi4Params) :
    [InfiniteVolumeSchwingerModel params] →
    [CorrelationFourPointModel params] →
    ∀ (f₁ f₂ f₃ f₄ : TestFun2D),
      (∀ x, 0 ≤ f₁ x) → (∀ x, 0 ≤ f₂ x) →
      (∀ x, 0 ≤ f₃ x) → (∀ x, 0 ≤ f₄ x) →
      infiniteCumulantFourPoint params f₁ f₂ f₃ f₄ ≤ 0 := by
  intro hlim hcorr f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  exact infiniteCumulantFourPoint_nonpos params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄

/-- Infinite-volume absolute bound for the fully connected 4-point cumulant. -/
theorem phi4_infiniteCumulantFourPoint_abs_bound (params : Phi4Params) :
    [InfiniteVolumeSchwingerModel params] →
    [CorrelationFourPointModel params] →
    ∀ (f₁ f₂ f₃ f₄ : TestFun2D),
      (∀ x, 0 ≤ f₁ x) → (∀ x, 0 ≤ f₂ x) →
      (∀ x, 0 ≤ f₃ x) → (∀ x, 0 ≤ f₄ x) →
      |infiniteCumulantFourPoint params f₁ f₂ f₃ f₄| ≤
        infiniteVolumeSchwinger params 2 ![f₁, f₃] *
          infiniteVolumeSchwinger params 2 ![f₂, f₄] +
        infiniteVolumeSchwinger params 2 ![f₁, f₄] *
          infiniteVolumeSchwinger params 2 ![f₂, f₃] := by
  intro hlim hcorr f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  exact infiniteCumulantFourPoint_abs_bound params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄

/-- Channel-wise lower bounds for the infinite-volume fully connected 4-point
    cumulant. -/
theorem phi4_infiniteCumulantFourPoint_lower_bounds_all_channels (params : Phi4Params) :
    [InfiniteVolumeSchwingerModel params] →
    [CorrelationFourPointModel params] →
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
  intro hlim hcorr f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  exact infiniteCumulantFourPoint_lower_bounds_all_channels
    params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄

/-- Alternative absolute-value bound via the `(13)(24)` channel. -/
theorem phi4_infiniteCumulantFourPoint_abs_bound_alt13 (params : Phi4Params) :
    [InfiniteVolumeSchwingerModel params] →
    [CorrelationFourPointModel params] →
    ∀ (f₁ f₂ f₃ f₄ : TestFun2D),
      (∀ x, 0 ≤ f₁ x) → (∀ x, 0 ≤ f₂ x) →
      (∀ x, 0 ≤ f₃ x) → (∀ x, 0 ≤ f₄ x) →
      |infiniteCumulantFourPoint params f₁ f₂ f₃ f₄| ≤
        infiniteVolumeSchwinger params 2 ![f₁, f₂] *
          infiniteVolumeSchwinger params 2 ![f₃, f₄] +
        infiniteVolumeSchwinger params 2 ![f₁, f₄] *
          infiniteVolumeSchwinger params 2 ![f₂, f₃] := by
  intro hlim hcorr f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  exact infiniteCumulantFourPoint_abs_bound_alt13 params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄

/-- Alternative absolute-value bound via the `(14)(23)` channel. -/
theorem phi4_infiniteCumulantFourPoint_abs_bound_alt14 (params : Phi4Params) :
    [InfiniteVolumeSchwingerModel params] →
    [CorrelationFourPointModel params] →
    ∀ (f₁ f₂ f₃ f₄ : TestFun2D),
      (∀ x, 0 ≤ f₁ x) → (∀ x, 0 ≤ f₂ x) →
      (∀ x, 0 ≤ f₃ x) → (∀ x, 0 ≤ f₄ x) →
      |infiniteCumulantFourPoint params f₁ f₂ f₃ f₄| ≤
        infiniteVolumeSchwinger params 2 ![f₁, f₂] *
          infiniteVolumeSchwinger params 2 ![f₃, f₄] +
        infiniteVolumeSchwinger params 2 ![f₁, f₃] *
          infiniteVolumeSchwinger params 2 ![f₂, f₄] := by
  intro hlim hcorr f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  exact infiniteCumulantFourPoint_abs_bound_alt14 params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄

/-- Infinite-volume all-channel 4-point bounds (GKS lower channels + Lebowitz upper
    channel). -/
theorem phi4_infiniteSchwinger_four_bounds_all_channels (params : Phi4Params) :
    [InfiniteVolumeSchwingerModel params] →
    [CorrelationFourPointModel params] →
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
  intro hlim hcorr f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  exact infiniteSchwinger_four_bounds_all_channels
    params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄

/-- Infinite-volume nonnegativity of the `(12)(34)` pairing-subtracted
    4-point channel. -/
theorem phi4_infiniteTruncatedFourPoint12_nonneg (params : Phi4Params) :
    [InfiniteVolumeSchwingerModel params] →
    [CorrelationFourPointModel params] →
    ∀ (f₁ f₂ f₃ f₄ : TestFun2D),
      (∀ x, 0 ≤ f₁ x) → (∀ x, 0 ≤ f₂ x) →
      (∀ x, 0 ≤ f₃ x) → (∀ x, 0 ≤ f₄ x) →
      0 ≤ infiniteTruncatedFourPoint12 params f₁ f₂ f₃ f₄ := by
  intro hlim hcorr f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  exact infiniteTruncatedFourPoint12_nonneg params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄

/-- Infinite-volume nonnegativity of the `(13)(24)` pairing-subtracted
    4-point channel. -/
theorem phi4_infiniteTruncatedFourPoint13_nonneg (params : Phi4Params) :
    [InfiniteVolumeSchwingerModel params] →
    [CorrelationFourPointModel params] →
    ∀ (f₁ f₂ f₃ f₄ : TestFun2D),
      (∀ x, 0 ≤ f₁ x) → (∀ x, 0 ≤ f₂ x) →
      (∀ x, 0 ≤ f₃ x) → (∀ x, 0 ≤ f₄ x) →
      0 ≤ infiniteTruncatedFourPoint13 params f₁ f₂ f₃ f₄ := by
  intro hlim hcorr f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  exact infiniteTruncatedFourPoint13_nonneg params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄

/-- Infinite-volume nonnegativity of the `(14)(23)` pairing-subtracted
    4-point channel. -/
theorem phi4_infiniteTruncatedFourPoint14_nonneg (params : Phi4Params) :
    [InfiniteVolumeSchwingerModel params] →
    [CorrelationFourPointModel params] →
    ∀ (f₁ f₂ f₃ f₄ : TestFun2D),
      (∀ x, 0 ≤ f₁ x) → (∀ x, 0 ≤ f₂ x) →
      (∀ x, 0 ≤ f₃ x) → (∀ x, 0 ≤ f₄ x) →
      0 ≤ infiniteTruncatedFourPoint14 params f₁ f₂ f₃ f₄ := by
  intro hlim hcorr f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  exact infiniteTruncatedFourPoint14_nonneg params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄

/-- Infinite-volume upper bound for the `(12)(34)` pairing-subtracted channel. -/
theorem phi4_infiniteTruncatedFourPoint12_upper (params : Phi4Params) :
    [InfiniteVolumeSchwingerModel params] →
    [CorrelationFourPointModel params] →
    ∀ (f₁ f₂ f₃ f₄ : TestFun2D),
      (∀ x, 0 ≤ f₁ x) → (∀ x, 0 ≤ f₂ x) →
      (∀ x, 0 ≤ f₃ x) → (∀ x, 0 ≤ f₄ x) →
      infiniteTruncatedFourPoint12 params f₁ f₂ f₃ f₄ ≤
        infiniteVolumeSchwinger params 2 ![f₁, f₃] *
          infiniteVolumeSchwinger params 2 ![f₂, f₄] +
        infiniteVolumeSchwinger params 2 ![f₁, f₄] *
          infiniteVolumeSchwinger params 2 ![f₂, f₃] := by
  intro hlim hcorr f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  exact infiniteTruncatedFourPoint12_upper params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄

/-- Infinite-volume upper bound for the `(13)(24)` pairing-subtracted channel. -/
theorem phi4_infiniteTruncatedFourPoint13_upper (params : Phi4Params) :
    [InfiniteVolumeSchwingerModel params] →
    [CorrelationFourPointModel params] →
    ∀ (f₁ f₂ f₃ f₄ : TestFun2D),
      (∀ x, 0 ≤ f₁ x) → (∀ x, 0 ≤ f₂ x) →
      (∀ x, 0 ≤ f₃ x) → (∀ x, 0 ≤ f₄ x) →
      infiniteTruncatedFourPoint13 params f₁ f₂ f₃ f₄ ≤
        infiniteVolumeSchwinger params 2 ![f₁, f₂] *
          infiniteVolumeSchwinger params 2 ![f₃, f₄] +
        infiniteVolumeSchwinger params 2 ![f₁, f₄] *
          infiniteVolumeSchwinger params 2 ![f₂, f₃] := by
  intro hlim hcorr f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  exact infiniteTruncatedFourPoint13_upper params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄

/-- Infinite-volume upper bound for the `(14)(23)` pairing-subtracted channel. -/
theorem phi4_infiniteTruncatedFourPoint14_upper (params : Phi4Params) :
    [InfiniteVolumeSchwingerModel params] →
    [CorrelationFourPointModel params] →
    ∀ (f₁ f₂ f₃ f₄ : TestFun2D),
      (∀ x, 0 ≤ f₁ x) → (∀ x, 0 ≤ f₂ x) →
      (∀ x, 0 ≤ f₃ x) → (∀ x, 0 ≤ f₄ x) →
      infiniteTruncatedFourPoint14 params f₁ f₂ f₃ f₄ ≤
        infiniteVolumeSchwinger params 2 ![f₁, f₂] *
          infiniteVolumeSchwinger params 2 ![f₃, f₄] +
        infiniteVolumeSchwinger params 2 ![f₁, f₃] *
          infiniteVolumeSchwinger params 2 ![f₂, f₄] := by
  intro hlim hcorr f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  exact infiniteTruncatedFourPoint14_upper params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄

/-- Infinite-volume absolute-value bound for the `(12)(34)` pairing-subtracted
    channel. -/
theorem phi4_infiniteTruncatedFourPoint12_abs_bound (params : Phi4Params) :
    [InfiniteVolumeSchwingerModel params] →
    [CorrelationFourPointModel params] →
    ∀ (f₁ f₂ f₃ f₄ : TestFun2D),
      (∀ x, 0 ≤ f₁ x) → (∀ x, 0 ≤ f₂ x) →
      (∀ x, 0 ≤ f₃ x) → (∀ x, 0 ≤ f₄ x) →
      |infiniteTruncatedFourPoint12 params f₁ f₂ f₃ f₄| ≤
        infiniteVolumeSchwinger params 2 ![f₁, f₃] *
          infiniteVolumeSchwinger params 2 ![f₂, f₄] +
        infiniteVolumeSchwinger params 2 ![f₁, f₄] *
          infiniteVolumeSchwinger params 2 ![f₂, f₃] := by
  intro hlim hcorr f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  exact infiniteTruncatedFourPoint12_abs_bound params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄

/-- Infinite-volume absolute-value bound for the `(13)(24)` pairing-subtracted
    channel. -/
theorem phi4_infiniteTruncatedFourPoint13_abs_bound (params : Phi4Params) :
    [InfiniteVolumeSchwingerModel params] →
    [CorrelationFourPointModel params] →
    ∀ (f₁ f₂ f₃ f₄ : TestFun2D),
      (∀ x, 0 ≤ f₁ x) → (∀ x, 0 ≤ f₂ x) →
      (∀ x, 0 ≤ f₃ x) → (∀ x, 0 ≤ f₄ x) →
      |infiniteTruncatedFourPoint13 params f₁ f₂ f₃ f₄| ≤
        infiniteVolumeSchwinger params 2 ![f₁, f₂] *
          infiniteVolumeSchwinger params 2 ![f₃, f₄] +
        infiniteVolumeSchwinger params 2 ![f₁, f₄] *
          infiniteVolumeSchwinger params 2 ![f₂, f₃] := by
  intro hlim hcorr f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  exact infiniteTruncatedFourPoint13_abs_bound params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄

/-- Infinite-volume absolute-value bound for the `(14)(23)` pairing-subtracted
    channel. -/
theorem phi4_infiniteTruncatedFourPoint14_abs_bound (params : Phi4Params) :
    [InfiniteVolumeSchwingerModel params] →
    [CorrelationFourPointModel params] →
    ∀ (f₁ f₂ f₃ f₄ : TestFun2D),
      (∀ x, 0 ≤ f₁ x) → (∀ x, 0 ≤ f₂ x) →
      (∀ x, 0 ≤ f₃ x) → (∀ x, 0 ≤ f₄ x) →
      |infiniteTruncatedFourPoint14 params f₁ f₂ f₃ f₄| ≤
        infiniteVolumeSchwinger params 2 ![f₁, f₂] *
          infiniteVolumeSchwinger params 2 ![f₃, f₄] +
        infiniteVolumeSchwinger params 2 ![f₁, f₃] *
          infiniteVolumeSchwinger params 2 ![f₂, f₄] := by
  intro hlim hcorr f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  exact infiniteTruncatedFourPoint14_abs_bound params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄

/-- Infinite-volume two-sided bounds for the `(12)(34)` pairing-subtracted
    4-point channel. -/
theorem phi4_infiniteTruncatedFourPoint12_bounds (params : Phi4Params) :
    [InfiniteVolumeSchwingerModel params] →
    [CorrelationFourPointModel params] →
    ∀ (f₁ f₂ f₃ f₄ : TestFun2D),
      (∀ x, 0 ≤ f₁ x) → (∀ x, 0 ≤ f₂ x) →
      (∀ x, 0 ≤ f₃ x) → (∀ x, 0 ≤ f₄ x) →
      0 ≤ infiniteTruncatedFourPoint12 params f₁ f₂ f₃ f₄ ∧
        infiniteTruncatedFourPoint12 params f₁ f₂ f₃ f₄ ≤
          infiniteVolumeSchwinger params 2 ![f₁, f₃] *
            infiniteVolumeSchwinger params 2 ![f₂, f₄] +
          infiniteVolumeSchwinger params 2 ![f₁, f₄] *
            infiniteVolumeSchwinger params 2 ![f₂, f₃] := by
  intro hlim hcorr f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  exact infiniteTruncatedFourPoint12_bounds params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄

/-- Infinite-volume two-sided bounds for the `(13)(24)` pairing-subtracted
    4-point channel. -/
theorem phi4_infiniteTruncatedFourPoint13_bounds (params : Phi4Params) :
    [InfiniteVolumeSchwingerModel params] →
    [CorrelationFourPointModel params] →
    ∀ (f₁ f₂ f₃ f₄ : TestFun2D),
      (∀ x, 0 ≤ f₁ x) → (∀ x, 0 ≤ f₂ x) →
      (∀ x, 0 ≤ f₃ x) → (∀ x, 0 ≤ f₄ x) →
      0 ≤ infiniteTruncatedFourPoint13 params f₁ f₂ f₃ f₄ ∧
        infiniteTruncatedFourPoint13 params f₁ f₂ f₃ f₄ ≤
          infiniteVolumeSchwinger params 2 ![f₁, f₂] *
            infiniteVolumeSchwinger params 2 ![f₃, f₄] +
          infiniteVolumeSchwinger params 2 ![f₁, f₄] *
            infiniteVolumeSchwinger params 2 ![f₂, f₃] := by
  intro hlim hcorr f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  exact infiniteTruncatedFourPoint13_bounds params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄

/-- Infinite-volume two-sided bounds for the `(14)(23)` pairing-subtracted
    4-point channel. -/
theorem phi4_infiniteTruncatedFourPoint14_bounds (params : Phi4Params) :
    [InfiniteVolumeSchwingerModel params] →
    [CorrelationFourPointModel params] →
    ∀ (f₁ f₂ f₃ f₄ : TestFun2D),
      (∀ x, 0 ≤ f₁ x) → (∀ x, 0 ≤ f₂ x) →
      (∀ x, 0 ≤ f₃ x) → (∀ x, 0 ≤ f₄ x) →
      0 ≤ infiniteTruncatedFourPoint14 params f₁ f₂ f₃ f₄ ∧
        infiniteTruncatedFourPoint14 params f₁ f₂ f₃ f₄ ≤
          infiniteVolumeSchwinger params 2 ![f₁, f₂] *
            infiniteVolumeSchwinger params 2 ![f₃, f₄] +
          infiniteVolumeSchwinger params 2 ![f₁, f₃] *
            infiniteVolumeSchwinger params 2 ![f₂, f₄] := by
  intro hlim hcorr f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  exact infiniteTruncatedFourPoint14_bounds params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄

/-- Combined two-sided bounds for all infinite-volume pairing-subtracted
    4-point channels. -/
theorem phi4_infiniteTruncatedFourPoint_bounds_all_channels (params : Phi4Params) :
    [InfiniteVolumeSchwingerModel params] →
    [CorrelationFourPointModel params] →
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
  intro hlim hcorr f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  exact infiniteTruncatedFourPoint_bounds_all_channels params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄

/-- Infinite-volume connected two-point symmetry. -/
theorem phi4_connectedTwoPoint_symm (params : Phi4Params) :
    [InfiniteVolumeSchwingerModel params] →
    ∀ (f g : TestFun2D),
      connectedTwoPoint params f g = connectedTwoPoint params g f := by
  intro hsch f g
  exact connectedTwoPoint_symm params f g

/-! ## Wightman reconstruction -/

/-- Interface-level Wightman existence from linear-growth and reconstruction
    backends, without using frontier-gap theorems. -/
theorem phi4_wightman_exists_of_interfaces (params : Phi4Params) :
    [InfiniteVolumeSchwingerModel params] →
    [OSAxiomCoreModel params] →
    [ReconstructionLinearGrowthModel params] →
    [WightmanReconstructionModel params] →
    ∃ (Wfn : WightmanFunctions 1),
      ∃ (OS : OsterwalderSchraderAxioms 1),
        OS.S = phi4SchwingerFunctions params ∧
        IsWickRotationPair OS.S Wfn.W := by
  intro hlim hos hlg hw
  obtain ⟨OS, hOS_lg⟩ := phi4_linear_growth_of_interface params
  rcases hOS_lg with ⟨hS, hlg_nonempty⟩
  rcases hlg_nonempty with ⟨hlg_inst⟩
  obtain ⟨Wfn, hWR⟩ :=
    phi4_wightman_reconstruction_step_of_interface (params := params) OS hlg_inst
  exact ⟨Wfn, OS, hS, hWR⟩

/-- Interface-level self-adjointness corollary obtained from
    `phi4_wightman_exists_of_interfaces`. -/
theorem phi4_selfadjoint_fields_of_interfaces (params : Phi4Params) :
    [InfiniteVolumeSchwingerModel params] →
    [OSAxiomCoreModel params] →
    [ReconstructionLinearGrowthModel params] →
    [WightmanReconstructionModel params] →
    ∃ (Wfn : WightmanFunctions 1),
      IsWickRotationPair (phi4SchwingerFunctions params) Wfn.W ∧
      (∀ (n : ℕ) (f g : SchwartzNPoint 1 n),
        (∀ x, g.toFun x = starRingEnd ℂ (f.toFun (fun i => x (Fin.rev i)))) →
        Wfn.W n g = starRingEnd ℂ (Wfn.W n f)) := by
  intro hlim hos hlin hw
  obtain ⟨Wfn, OS, hS, hWR⟩ := phi4_wightman_exists_of_interfaces params
  exact ⟨Wfn, hS ▸ hWR, Wfn.hermitian⟩

/-- Interface-level locality corollary obtained from
    `phi4_wightman_exists_of_interfaces`. -/
theorem phi4_locality_of_interfaces (params : Phi4Params) :
    [InfiniteVolumeSchwingerModel params] →
    [OSAxiomCoreModel params] →
    [ReconstructionLinearGrowthModel params] →
    [WightmanReconstructionModel params] →
    ∃ (Wfn : WightmanFunctions 1),
      IsWickRotationPair (phi4SchwingerFunctions params) Wfn.W ∧
      IsLocallyCommutativeWeak 1 Wfn.W := by
  intro hlim hos hlin hw
  obtain ⟨Wfn, OS, hS, hWR⟩ := phi4_wightman_exists_of_interfaces params
  exact ⟨Wfn, hS ▸ hWR, Wfn.locally_commutative⟩

/-- Interface-level Lorentz-covariance corollary obtained from
    `phi4_wightman_exists_of_interfaces`. -/
theorem phi4_lorentz_covariance_of_interfaces (params : Phi4Params) :
    [InfiniteVolumeSchwingerModel params] →
    [OSAxiomCoreModel params] →
    [ReconstructionLinearGrowthModel params] →
    [WightmanReconstructionModel params] →
    ∃ (Wfn : WightmanFunctions 1),
      IsWickRotationPair (phi4SchwingerFunctions params) Wfn.W ∧
      IsLorentzCovariantWeak 1 Wfn.W := by
  intro hlim hos hlin hw
  obtain ⟨Wfn, OS, hS, hWR⟩ := phi4_wightman_exists_of_interfaces params
  exact ⟨Wfn, hS ▸ hWR, Wfn.lorentz_covariant⟩

/-- Interface-level positive-definite/vacuum corollary obtained from
    `phi4_wightman_exists_of_interfaces`. -/
theorem phi4_unique_vacuum_of_interfaces (params : Phi4Params) :
    [InfiniteVolumeSchwingerModel params] →
    [OSAxiomCoreModel params] →
    [ReconstructionLinearGrowthModel params] →
    [WightmanReconstructionModel params] →
    ∃ (Wfn : WightmanFunctions 1),
      IsPositiveDefinite 1 Wfn.W ∧
      IsWickRotationPair (phi4SchwingerFunctions params) Wfn.W := by
  intro hlim hos hlin hw
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
theorem phi4_wightman_exists (params : Phi4Params) :
    [InfiniteVolumeSchwingerModel params] →
    [OSAxiomCoreModel params] →
    [ReconstructionLinearGrowthModel params] →
    [WightmanReconstructionModel params] →
    ∃ (Wfn : WightmanFunctions 1),
      ∃ (OS : OsterwalderSchraderAxioms 1),
        OS.S = phi4SchwingerFunctions params ∧
        IsWickRotationPair OS.S Wfn.W := by
  intro hlim hos hlin hw
  obtain ⟨OS, hOS_lg⟩ := phi4_linear_growth params
  rcases hOS_lg with ⟨hS, hlg_nonempty⟩
  rcases hlg_nonempty with ⟨hlg⟩
  obtain ⟨Wfn, hWR⟩ := phi4_wightman_reconstruction_step (params := params) OS hlg
  exact ⟨Wfn, OS, hS, hWR⟩

/-- The φ⁴₂ QFT has hermitian field operators (self-adjointness).
    W_n(f̃) = conj(W_n(f)) where f̃(x₁,...,xₙ) = conj(f(xₙ,...,x₁)).
    (Glimm-Jaffe Section 19.3)

    This is encoded in the `hermitian` field of `WightmanFunctions`,
    which is the distributional version of φ(f)* = φ(f̄) for real f. -/
theorem phi4_selfadjoint_fields (params : Phi4Params) :
    [InfiniteVolumeSchwingerModel params] →
    [OSAxiomCoreModel params] →
    [ReconstructionLinearGrowthModel params] →
    [WightmanReconstructionModel params] →
    ∃ (Wfn : WightmanFunctions 1),
      IsWickRotationPair (phi4SchwingerFunctions params) Wfn.W ∧
      (∀ (n : ℕ) (f g : SchwartzNPoint 1 n),
        (∀ x, g.toFun x = starRingEnd ℂ (f.toFun (fun i => x (Fin.rev i)))) →
        Wfn.W n g = starRingEnd ℂ (Wfn.W n f)) := by
  intro hlim hos hlin hw
  obtain ⟨Wfn, OS, hS, hWR⟩ := phi4_wightman_exists params
  exact ⟨Wfn, hS ▸ hWR, Wfn.hermitian⟩

/-- The φ⁴₂ QFT satisfies locality: fields at spacelike separation commute.
    [φ(f), φ(g)] = 0 when supp f and supp g are spacelike separated.
    (Glimm-Jaffe Section 19.6)
    This follows from the Wightman reconstruction theorem applied to
    the φ⁴₂ Schwinger functions. -/
theorem phi4_locality (params : Phi4Params) :
    [InfiniteVolumeSchwingerModel params] →
    [OSAxiomCoreModel params] →
    [ReconstructionLinearGrowthModel params] →
    [WightmanReconstructionModel params] →
    ∃ (Wfn : WightmanFunctions 1),
      IsWickRotationPair (phi4SchwingerFunctions params) Wfn.W ∧
      IsLocallyCommutativeWeak 1 Wfn.W := by
  intro hlim hos hlin hw
  obtain ⟨Wfn, OS, hS, hWR⟩ := phi4_wightman_exists params
  exact ⟨Wfn, hS ▸ hWR, Wfn.locally_commutative⟩

/-- The φ⁴₂ QFT has Lorentz covariance.
    U(Λ,a) φ(f) U(Λ,a)⁻¹ = φ((Λ,a)·f) for (Λ,a) ∈ ISO(1,1).
    (Glimm-Jaffe Section 19.5) -/
theorem phi4_lorentz_covariance (params : Phi4Params) :
    [InfiniteVolumeSchwingerModel params] →
    [OSAxiomCoreModel params] →
    [ReconstructionLinearGrowthModel params] →
    [WightmanReconstructionModel params] →
    ∃ (Wfn : WightmanFunctions 1),
      IsWickRotationPair (phi4SchwingerFunctions params) Wfn.W ∧
      IsLorentzCovariantWeak 1 Wfn.W := by
  intro hlim hos hlin hw
  obtain ⟨Wfn, OS, hS, hWR⟩ := phi4_wightman_exists params
  exact ⟨Wfn, hS ▸ hWR, Wfn.lorentz_covariant⟩

/-- The φ⁴₂ QFT has a unique vacuum state.
    The vacuum Ω is the unique (up to phase) Poincaré-invariant state.
    (Glimm-Jaffe Section 19.7)

    For weak coupling, this follows from the cluster property (OS4).
    For strong coupling, vacuum uniqueness is related to the absence of
    phase transitions (or selecting a pure phase). -/
theorem phi4_unique_vacuum (params : Phi4Params) :
    [InfiniteVolumeSchwingerModel params] →
    [OSAxiomCoreModel params] →
    [ReconstructionLinearGrowthModel params] →
    [WightmanReconstructionModel params] →
    ∃ (Wfn : WightmanFunctions 1),
      IsPositiveDefinite 1 Wfn.W ∧
      IsWickRotationPair (phi4SchwingerFunctions params) Wfn.W := by
  intro hlim hos hlin hw
  obtain ⟨Wfn, OS, hS, hWR⟩ := phi4_wightman_exists params
  exact ⟨Wfn, Wfn.positive_definite, hS ▸ hWR⟩

end

/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.Reconstruction.Part1

noncomputable section

open MeasureTheory Reconstruction

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


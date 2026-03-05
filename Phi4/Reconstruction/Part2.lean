/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.Reconstruction.Part1Tail

noncomputable section

open MeasureTheory Reconstruction

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

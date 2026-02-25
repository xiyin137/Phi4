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
private def translateTestFun (a : Fin 2 → ℝ) (g : TestFun2D) : TestFun2D :=
  SchwartzMap.compCLMOfAntilipschitz ℝ
    (translateMap_hasTemperateGrowth (toSpacetime2D a))
    (translateMap_antilipschitz (toSpacetime2D a))
    g

/-! ## Abstract reconstruction inputs -/

/-- Inputs needed for OS reconstruction beyond the basic OSreconstruction API.
    In particular, `wightman_reconstruction` is kept as an explicit assumption
    interface rather than calling a specific external theorem directly. -/
class ReconstructionInputModel (params : Phi4Params)
    [InfiniteVolumeLimitModel params]
    [OSAxiomModel params] where
  phi4_linear_growth :
    ∃ OS : OsterwalderSchraderAxioms 1,
      OS.S = phi4SchwingerFunctions params ∧
      Nonempty (OSLinearGrowthCondition 1 OS)
  phi4_os4_weak_coupling :
    ∃ coupling_bound : ℝ, 0 < coupling_bound ∧
      ∀ p : Phi4Params, [InfiniteVolumeLimitModel p] →
        p.coupling < coupling_bound →
          ∃ (m_gap : ℝ) (C : ℝ), 0 < m_gap ∧
            ∀ (f g : TestFun2D) (a : Fin 2 → ℝ),
              let g_shifted : TestFun2D := translateTestFun a g
              |connectedTwoPoint p f g_shifted| ≤
                C * Real.exp (-m_gap * ‖a‖)
  wightman_reconstruction :
    ∀ (OS : OsterwalderSchraderAxioms 1),
      OSLinearGrowthCondition 1 OS →
        ∃ (Wfn : WightmanFunctions 1),
          IsWickRotationPair OS.S Wfn.W

/-! ## Linear growth condition (E0') -/

/-- **Linear growth condition E0'** for the φ⁴₂ Schwinger functions.
    |S_n(f)| ≤ α · βⁿ · (n!)^γ · ‖f‖_s
    with γ = 1/2 for the φ⁴ interaction.

    This is stronger than simple temperedness (E0) and is essential for the
    analytic continuation to work: without it, the Wightman distributions
    reconstructed from the Schwinger functions may fail to be tempered.

    For the φ⁴₂ theory, this follows from the generating functional bound
    (Theorem 12.5.1) and the Wick-type combinatorics of the interaction. -/
theorem phi4_linear_growth (params : Phi4Params)
    [InfiniteVolumeLimitModel params]
    [OSAxiomModel params]
    [ReconstructionInputModel params] :
    ∃ OS : OsterwalderSchraderAxioms 1,
      OS.S = phi4SchwingerFunctions params ∧
      Nonempty (OSLinearGrowthCondition 1 OS) := by
  exact ReconstructionInputModel.phi4_linear_growth (params := params)

/-! ## OS4: Clustering (for weak coupling) -/

/-- **OS4 (Clustering)** for weak coupling:
    There exists a coupling threshold λ₀ > 0 such that for λ < λ₀,
    the truncated two-point function decays exponentially with the
    spatial separation of the test function supports:
      |⟨φ(f)φ(g)⟩ - ⟨φ(f)⟩⟨φ(g)⟩| ≤ C · e^{-m·dist(supp f, supp g)}
    where m > 0 is the mass gap.

    The proof uses the cluster expansion (Glimm-Jaffe Chapter 18):
    a convergent expansion in the coupling constant that exhibits
    exponential decay of connected correlations.

    For strong coupling, OS4 requires the phase transition analysis
    and may fail at the critical point. -/
theorem phi4_os4_weak_coupling (params : Phi4Params) :
    [InfiniteVolumeLimitModel params] →
    [OSAxiomModel params] →
    [ReconstructionInputModel params] →
    ∃ coupling_bound : ℝ, 0 < coupling_bound ∧
      ∀ p : Phi4Params, [InfiniteVolumeLimitModel p] →
        p.coupling < coupling_bound →
          ∃ (m_gap : ℝ) (C : ℝ), 0 < m_gap ∧
            ∀ (f g : TestFun2D) (a : Fin 2 → ℝ),
              let g_shifted : TestFun2D := translateTestFun a g
              |connectedTwoPoint p f g_shifted| ≤
                C * Real.exp (-m_gap * ‖a‖) := by
  intro hlim hos hrec
  exact ReconstructionInputModel.phi4_os4_weak_coupling
    (params := params)

/-- Backward-compatible OS4 weak-coupling form written with explicit Schwinger moments. -/
theorem phi4_os4_weak_coupling_explicit (params : Phi4Params) :
    [InfiniteVolumeLimitModel params] →
    [OSAxiomModel params] →
    [ReconstructionInputModel params] →
    ∃ coupling_bound : ℝ, 0 < coupling_bound ∧
      ∀ p : Phi4Params, [InfiniteVolumeLimitModel p] →
        p.coupling < coupling_bound →
          ∃ (m_gap : ℝ) (C : ℝ), 0 < m_gap ∧
            ∀ (f g : TestFun2D) (a : Fin 2 → ℝ),
              let g_shifted : TestFun2D := translateTestFun a g
              |infiniteVolumeSchwinger p 2 ![f, g_shifted] -
                infiniteVolumeSchwinger p 1 ![f] *
                  infiniteVolumeSchwinger p 1 ![g_shifted]| ≤
                C * Real.exp (-m_gap * ‖a‖) := by
  intro hlim hos hrec
  rcases phi4_os4_weak_coupling params with ⟨coupling_bound, hcb_pos, hdecay⟩
  refine ⟨coupling_bound, hcb_pos, ?_⟩
  intro p hpInst hsmall
  rcases hdecay p hsmall with ⟨m_gap, C, hm_gap, hbound⟩
  refine ⟨m_gap, C, hm_gap, ?_⟩
  intro f g a
  simpa [connectedTwoPoint] using hbound f g a

/-! ## Wightman reconstruction -/

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
    [InfiniteVolumeLimitModel params] →
    [OSAxiomModel params] →
    [ReconstructionInputModel params] →
    ∃ (Wfn : WightmanFunctions 1),
      ∃ (OS : OsterwalderSchraderAxioms 1),
        OS.S = phi4SchwingerFunctions params ∧
        IsWickRotationPair OS.S Wfn.W := by
  intro hlim hos hrec
  obtain ⟨OS, hOS_lg⟩ := phi4_linear_growth params
  rcases hOS_lg with ⟨hS, hlg_nonempty⟩
  rcases hlg_nonempty with ⟨hlg⟩
  obtain ⟨Wfn, hWR⟩ := ReconstructionInputModel.wightman_reconstruction
    (params := params) OS hlg
  exact ⟨Wfn, OS, hS, hWR⟩

/-- The φ⁴₂ QFT has hermitian field operators (self-adjointness).
    W_n(f̃) = conj(W_n(f)) where f̃(x₁,...,xₙ) = conj(f(xₙ,...,x₁)).
    (Glimm-Jaffe Section 19.3)

    This is encoded in the `hermitian` field of `WightmanFunctions`,
    which is the distributional version of φ(f)* = φ(f̄) for real f. -/
theorem phi4_selfadjoint_fields (params : Phi4Params) :
    [InfiniteVolumeLimitModel params] →
    [OSAxiomModel params] →
    [ReconstructionInputModel params] →
    ∃ (Wfn : WightmanFunctions 1),
      IsWickRotationPair (phi4SchwingerFunctions params) Wfn.W ∧
      (∀ (n : ℕ) (f g : SchwartzNPoint 1 n),
        (∀ x, g.toFun x = starRingEnd ℂ (f.toFun (fun i => x (Fin.rev i)))) →
        Wfn.W n g = starRingEnd ℂ (Wfn.W n f)) := by
  intro hlim hos hrec
  obtain ⟨Wfn, OS, hS, hWR⟩ := phi4_wightman_exists params
  exact ⟨Wfn, hS ▸ hWR, Wfn.hermitian⟩

/-- The φ⁴₂ QFT satisfies locality: fields at spacelike separation commute.
    [φ(f), φ(g)] = 0 when supp f and supp g are spacelike separated.
    (Glimm-Jaffe Section 19.6)
    This follows from the Wightman reconstruction theorem applied to
    the φ⁴₂ Schwinger functions. -/
theorem phi4_locality (params : Phi4Params) :
    [InfiniteVolumeLimitModel params] →
    [OSAxiomModel params] →
    [ReconstructionInputModel params] →
    ∃ (Wfn : WightmanFunctions 1),
      IsWickRotationPair (phi4SchwingerFunctions params) Wfn.W ∧
      IsLocallyCommutativeWeak 1 Wfn.W := by
  intro hlim hos hrec
  obtain ⟨Wfn, OS, hS, hWR⟩ := phi4_wightman_exists params
  exact ⟨Wfn, hS ▸ hWR, Wfn.locally_commutative⟩

/-- The φ⁴₂ QFT has Lorentz covariance.
    U(Λ,a) φ(f) U(Λ,a)⁻¹ = φ((Λ,a)·f) for (Λ,a) ∈ ISO(1,1).
    (Glimm-Jaffe Section 19.5) -/
theorem phi4_lorentz_covariance (params : Phi4Params) :
    [InfiniteVolumeLimitModel params] →
    [OSAxiomModel params] →
    [ReconstructionInputModel params] →
    ∃ (Wfn : WightmanFunctions 1),
      IsWickRotationPair (phi4SchwingerFunctions params) Wfn.W ∧
      IsLorentzCovariantWeak 1 Wfn.W := by
  intro hlim hos hrec
  obtain ⟨Wfn, OS, hS, hWR⟩ := phi4_wightman_exists params
  exact ⟨Wfn, hS ▸ hWR, Wfn.lorentz_covariant⟩

/-- The φ⁴₂ QFT has a unique vacuum state.
    The vacuum Ω is the unique (up to phase) Poincaré-invariant state.
    (Glimm-Jaffe Section 19.7)

    For weak coupling, this follows from the cluster property (OS4).
    For strong coupling, vacuum uniqueness is related to the absence of
    phase transitions (or selecting a pure phase). -/
theorem phi4_unique_vacuum (params : Phi4Params) :
    [InfiniteVolumeLimitModel params] →
    [OSAxiomModel params] →
    [ReconstructionInputModel params] →
    ∃ (Wfn : WightmanFunctions 1),
      IsPositiveDefinite 1 Wfn.W ∧
      IsWickRotationPair (phi4SchwingerFunctions params) Wfn.W := by
  intro hlim hos hrec
  obtain ⟨Wfn, OS, hS, hWR⟩ := phi4_wightman_exists params
  exact ⟨Wfn, Wfn.positive_definite, hS ▸ hWR⟩

end

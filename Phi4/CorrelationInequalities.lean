/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.FiniteVolumeMeasure
import Phi4.LatticeApproximation

/-!
# Correlation Inequalities

Correlation inequalities are the key tool for controlling the infinite volume limit.
They provide monotonicity and uniform bounds on Schwinger functions.

The main inequalities are:
- **GKS-I (Griffiths' first inequality)**: ⟨φ(f)φ(g)⟩ ≥ 0 for f,g ≥ 0
- **GKS-II (Griffiths' second inequality)**: truncated 4-point function is non-negative
- **FKG inequality**: monotone functions are positively correlated
- **Lebowitz inequality**: 4-point function bounded by sum of products of 2-point functions

These hold for the φ⁴ interaction because P(φ) = λφ⁴ + (lower order) with λ > 0
satisfies the Griffiths-Simon conditions.

## References

* [Glimm-Jaffe] Chapter 4 (lattice version), Section 10.2 (continuum version)
* [Simon] "The P(φ)₂ Euclidean (Quantum) Field Theory"
-/

noncomputable section

open MeasureTheory

/-! ## Abstract correlation-inequality interface -/

/-- Correlation inequalities for a fixed interacting model `params`.
    These are the continuum counterparts of the lattice inequalities used in
    Glimm-Jaffe Chapters 4 and 10, exposed as reusable assumptions so
    downstream infinite-volume/OS arguments can be developed independently of
    the lattice-approximation proof layer. -/
class CorrelationInequalityModel (params : Phi4Params) where
  /-- GKS-I positivity of the 2-point function for nonnegative test functions. -/
  griffiths_first : ∀ (Λ : Rectangle) (f g : TestFun2D)
      (_hf : ∀ x, 0 ≤ f x) (_hg : ∀ x, 0 ≤ g x),
      0 ≤ schwingerTwo params Λ f g
  /-- GKS-II lower bound in the `(12)(34)` pairing channel. -/
  griffiths_second : ∀ (Λ : Rectangle)
      (f₁ f₂ f₃ f₄ : TestFun2D)
      (_hf₁ : ∀ x, 0 ≤ f₁ x) (_hf₂ : ∀ x, 0 ≤ f₂ x)
      (_hf₃ : ∀ x, 0 ≤ f₃ x) (_hf₄ : ∀ x, 0 ≤ f₄ x),
      schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ ≤
        schwingerN params Λ 4 ![f₁, f₂, f₃, f₄]
  /-- FKG positive-correlation inequality for monotone observables. -/
  fkg_inequality : ∀ (Λ : Rectangle)
      (F G : FieldConfig2D → ℝ)
      (_hF_mono : ∀ ω₁ ω₂ : FieldConfig2D, (∀ f, ω₁ f ≤ ω₂ f) → F ω₁ ≤ F ω₂)
      (_hG_mono : ∀ ω₁ ω₂ : FieldConfig2D, (∀ f, ω₁ f ≤ ω₂ f) → G ω₁ ≤ G ω₂),
      (∫ ω, F ω ∂(finiteVolumeMeasure params Λ)) *
        (∫ ω, G ω ∂(finiteVolumeMeasure params Λ)) ≤
      ∫ ω, F ω * G ω ∂(finiteVolumeMeasure params Λ)
  /-- Lebowitz 4-point upper bound. -/
  lebowitz_inequality : ∀ (Λ : Rectangle)
      (f₁ f₂ f₃ f₄ : TestFun2D)
      (_hf₁ : ∀ x, 0 ≤ f₁ x) (_hf₂ : ∀ x, 0 ≤ f₂ x)
      (_hf₃ : ∀ x, 0 ≤ f₃ x) (_hf₄ : ∀ x, 0 ≤ f₄ x),
      schwingerN params Λ 4 ![f₁, f₂, f₃, f₄] ≤
        schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ +
        schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄ +
        schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃
  /-- Monotonicity of the finite-volume 2-point function under domain inclusion. -/
  schwinger_two_monotone : ∀ (Λ₁ Λ₂ : Rectangle)
      (_h : Λ₁.toSet ⊆ Λ₂.toSet)
      (f g : TestFun2D) (_hf : ∀ x, 0 ≤ f x) (_hg : ∀ x, 0 ≤ g x)
      (_hfΛ : ∀ x ∉ Λ₁.toSet, f x = 0) (_hgΛ : ∀ x ∉ Λ₁.toSet, g x = 0),
      schwingerTwo params Λ₁ f g ≤ schwingerTwo params Λ₂ f g

/-! ## Lattice-to-continuum bridge for GKS-I -/

/-- Real-analysis helper: if `x` can be approximated arbitrarily well by
    nonnegative reals, then `x` is nonnegative. -/
lemma nonneg_of_approx_nonneg (x : ℝ)
    (happrox : ∀ ε > 0, ∃ y : ℝ, 0 ≤ y ∧ |x - y| < ε) :
    0 ≤ x := by
  by_contra hx
  have hxlt : x < 0 := lt_of_not_ge hx
  have hxeps : 0 < -x := by linarith
  rcases happrox (-x) hxeps with ⟨y, hy_nonneg, hy_close⟩
  have hlower : -x ≤ |x - y| := by
    calc
      -x ≤ y - x := by linarith
      _ = |y - x| := by
            rw [abs_of_nonneg]
            linarith
      _ = |x - y| := by simp [abs_sub_comm]
  linarith

/-- Real-analysis helper: if `x` and `y` can be approximated arbitrarily well by
    ordered pairs `a ≤ b`, then `x ≤ y`. -/
lemma le_of_approx_ordered (x y : ℝ)
    (happrox : ∀ ε > 0,
      ∃ a b : ℝ, a ≤ b ∧ |x - a| < ε ∧ |y - b| < ε) :
    x ≤ y := by
  by_contra hxy
  have hxylt : y < x := lt_of_not_ge hxy
  let ε : ℝ := (x - y) / 4
  have hε : 0 < ε := by
    have : 0 < x - y := by linarith
    exact div_pos this (by norm_num)
  rcases happrox ε hε with ⟨a, b, hab, hxa, hyb⟩
  have hxa' := abs_lt.mp hxa
  have hyb' := abs_lt.mp hyb
  have ha_lower : x - ε < a := by linarith [hxa'.2]
  have hb_upper : b < y + ε := by linarith [hyb'.1]
  have hgap : y + ε < x - ε := by
    dsimp [ε]
    linarith
  have hab_false : ¬ a ≤ b := by
    have : b < a := by linarith
    exact not_le_of_gt this
  exact hab_false hab

/-- Bridge assumptions for deriving continuum GKS-I from lattice approximants. -/
class LatticeGriffithsFirstModel (params : Phi4Params) where
  /-- Lattice approximant of the continuum two-point function at fixed volume and mesh. -/
  latticeTwo : ∀ Λ : Rectangle, Phi4.RectLattice Λ → TestFun2D → TestFun2D → ℝ
  /-- Lattice GKS-I positivity. -/
  lattice_gks1 : ∀ (Λ : Rectangle) (L : Phi4.RectLattice Λ) (f g : TestFun2D)
      (_hf : ∀ x, 0 ≤ f x) (_hg : ∀ x, 0 ≤ g x),
      0 ≤ latticeTwo Λ L f g
  /-- Arbitrarily fine lattice approximation of the continuum two-point function. -/
  schwingerTwo_approx_lattice : ∀ (Λ : Rectangle) (f g : TestFun2D)
      (ε : ℝ), 0 < ε →
      ∃ L : Phi4.RectLattice Λ,
        |schwingerTwo params Λ f g - latticeTwo Λ L f g| < ε

/-- Continuum GKS-I obtained from lattice GKS-I plus convergence of lattice
    approximants to the continuum two-point function. -/
theorem griffiths_first_from_lattice
    (params : Phi4Params)
    [LatticeGriffithsFirstModel params]
    (Λ : Rectangle) (f g : TestFun2D)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) :
    0 ≤ schwingerTwo params Λ f g := by
  apply nonneg_of_approx_nonneg
  intro ε hε
  rcases LatticeGriffithsFirstModel.schwingerTwo_approx_lattice
      (params := params) Λ f g ε hε with ⟨L, hclose⟩
  refine ⟨LatticeGriffithsFirstModel.latticeTwo (params := params) Λ L f g,
    LatticeGriffithsFirstModel.lattice_gks1 (params := params) Λ L f g hf hg,
    ?_⟩
  simpa [abs_sub_comm] using hclose

/-- Bridge assumptions for deriving continuum volume-monotonicity of the
    two-point function from lattice-ordered approximants. -/
class LatticeSchwingerTwoMonotoneModel (params : Phi4Params) where
  latticeTwo : ∀ Λ : Rectangle, Phi4.RectLattice Λ → TestFun2D → TestFun2D → ℝ
  approx_monotone_pair : ∀ (Λ₁ Λ₂ : Rectangle)
      (_h : Λ₁.toSet ⊆ Λ₂.toSet)
      (f g : TestFun2D) (_hf : ∀ x, 0 ≤ f x) (_hg : ∀ x, 0 ≤ g x)
      (_hfΛ : ∀ x ∉ Λ₁.toSet, f x = 0) (_hgΛ : ∀ x ∉ Λ₁.toSet, g x = 0)
      (ε : ℝ), 0 < ε →
      ∃ L₁ : Phi4.RectLattice Λ₁, ∃ L₂ : Phi4.RectLattice Λ₂,
        latticeTwo Λ₁ L₁ f g ≤ latticeTwo Λ₂ L₂ f g ∧
        |schwingerTwo params Λ₁ f g - latticeTwo Λ₁ L₁ f g| < ε ∧
        |schwingerTwo params Λ₂ f g - latticeTwo Λ₂ L₂ f g| < ε

/-- Continuum two-point monotonicity from lattice-ordered approximation pairs. -/
theorem schwinger_two_monotone_from_lattice
    (params : Phi4Params)
    [LatticeSchwingerTwoMonotoneModel params]
    (Λ₁ Λ₂ : Rectangle)
    (h : Λ₁.toSet ⊆ Λ₂.toSet)
    (f g : TestFun2D) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfΛ : ∀ x ∉ Λ₁.toSet, f x = 0) (hgΛ : ∀ x ∉ Λ₁.toSet, g x = 0) :
    schwingerTwo params Λ₁ f g ≤ schwingerTwo params Λ₂ f g := by
  apply le_of_approx_ordered
  intro ε hε
  rcases LatticeSchwingerTwoMonotoneModel.approx_monotone_pair
      (params := params) Λ₁ Λ₂ h f g hf hg hfΛ hgΛ ε hε with
      ⟨L₁, L₂, hmon, hclose₁, hclose₂⟩
  refine ⟨LatticeSchwingerTwoMonotoneModel.latticeTwo (params := params) Λ₁ L₁ f g,
    LatticeSchwingerTwoMonotoneModel.latticeTwo (params := params) Λ₂ L₂ f g,
    hmon, hclose₁, hclose₂⟩

/-- Core correlation-inequality inputs not yet derived from the current
    lattice bridge layer. This isolates the remaining analytic assumptions
    while allowing GKS-I and two-point monotonicity to be sourced from
    lattice approximation results. -/
class CorrelationInequalityCoreModel (params : Phi4Params) where
  /-- GKS-II lower bound in the `(12)(34)` channel. -/
  griffiths_second : ∀ (Λ : Rectangle)
      (f₁ f₂ f₃ f₄ : TestFun2D)
      (_hf₁ : ∀ x, 0 ≤ f₁ x) (_hf₂ : ∀ x, 0 ≤ f₂ x)
      (_hf₃ : ∀ x, 0 ≤ f₃ x) (_hf₄ : ∀ x, 0 ≤ f₄ x),
      schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ ≤
        schwingerN params Λ 4 ![f₁, f₂, f₃, f₄]
  /-- FKG positive-correlation inequality. -/
  fkg_inequality : ∀ (Λ : Rectangle)
      (F G : FieldConfig2D → ℝ)
      (_hF_mono : ∀ ω₁ ω₂ : FieldConfig2D, (∀ f, ω₁ f ≤ ω₂ f) → F ω₁ ≤ F ω₂)
      (_hG_mono : ∀ ω₁ ω₂ : FieldConfig2D, (∀ f, ω₁ f ≤ ω₂ f) → G ω₁ ≤ G ω₂),
      (∫ ω, F ω ∂(finiteVolumeMeasure params Λ)) *
        (∫ ω, G ω ∂(finiteVolumeMeasure params Λ)) ≤
      ∫ ω, F ω * G ω ∂(finiteVolumeMeasure params Λ)
  /-- Lebowitz 4-point upper bound. -/
  lebowitz_inequality : ∀ (Λ : Rectangle)
      (f₁ f₂ f₃ f₄ : TestFun2D)
      (_hf₁ : ∀ x, 0 ≤ f₁ x) (_hf₂ : ∀ x, 0 ≤ f₂ x)
      (_hf₃ : ∀ x, 0 ≤ f₃ x) (_hf₄ : ∀ x, 0 ≤ f₄ x),
      schwingerN params Λ 4 ![f₁, f₂, f₃, f₄] ≤
        schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ +
        schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄ +
        schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃

/-- Build the full `CorrelationInequalityModel` from:
    1. lattice bridge inputs for GKS-I and 2-point monotonicity, and
    2. remaining core assumptions (GKS-II, FKG, Lebowitz). -/
def correlationInequalityModelOfLattice
    (params : Phi4Params)
    [LatticeGriffithsFirstModel params]
    [LatticeSchwingerTwoMonotoneModel params]
    [CorrelationInequalityCoreModel params] :
    CorrelationInequalityModel params where
  griffiths_first := griffiths_first_from_lattice (params := params)
  griffiths_second := CorrelationInequalityCoreModel.griffiths_second (params := params)
  fkg_inequality := CorrelationInequalityCoreModel.fkg_inequality (params := params)
  lebowitz_inequality := CorrelationInequalityCoreModel.lebowitz_inequality (params := params)
  schwinger_two_monotone := schwinger_two_monotone_from_lattice (params := params)

/-! ## Griffiths' First Inequality (GKS-I) -/

/-- **GKS-I**: For the φ⁴₂ measure dμ_Λ with P = even + linear,
    ⟨φ(f)φ(g)⟩ ≥ 0 for non-negative test functions f, g ≥ 0.

    This extends from the lattice Griffiths inequality to the continuum
    via lattice approximation. The key input is that e^{-V} is a function
    of φ with a "ferromagnetic" structure (all couplings positive). -/
theorem griffiths_first (params : Phi4Params) (Λ : Rectangle)
    [CorrelationInequalityModel params]
    (f g : TestFun2D) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) :
    0 ≤ schwingerTwo params Λ f g := by
  exact CorrelationInequalityModel.griffiths_first (params := params) Λ f g hf hg

/-! ## Griffiths' Second Inequality (GKS-II) -/

/-- **GKS-II** in the `(12)(34)` channel:
    ⟨φ(f₁)φ(f₂)φ(f₃)φ(f₄)⟩ ≥ ⟨φ(f₁)φ(f₂)⟩⟨φ(f₃)φ(f₄)⟩
    for non-negative test functions f₁,...,f₄ ≥ 0.

    Equivalently, the `(12)(34)` pairing-subtracted quantity is nonnegative.
    This channel inequality is one of the core inputs in the monotonicity
    arguments used for the infinite-volume limit. -/
theorem griffiths_second (params : Phi4Params) (Λ : Rectangle)
    [CorrelationInequalityModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ ≤
      schwingerN params Λ 4 ![f₁, f₂, f₃, f₄] := by
  exact CorrelationInequalityModel.griffiths_second
    (params := params) Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄

private def fin4_1 : Fin 4 := ⟨1, by decide⟩
private def fin4_2 : Fin 4 := ⟨2, by decide⟩
private def fin4_3 : Fin 4 := ⟨3, by decide⟩

private lemma schwingerN4_swap12
    (params : Phi4Params) (Λ : Rectangle)
    (f₁ f₂ f₃ f₄ : TestFun2D) :
    schwingerN params Λ 4 ![f₁, f₃, f₂, f₄] =
      schwingerN params Λ 4 ![f₁, f₂, f₃, f₄] := by
  have hperm := schwingerN_perm params Λ 4 ![f₁, f₃, f₂, f₄]
    (Equiv.swap fin4_1 fin4_2)
  simpa [fin4_1, fin4_2, Function.comp] using hperm.symm

private lemma schwingerN4_perm_01423
    (params : Phi4Params) (Λ : Rectangle)
    (f₁ f₂ f₃ f₄ : TestFun2D) :
    schwingerN params Λ 4 ![f₁, f₄, f₂, f₃] =
      schwingerN params Λ 4 ![f₁, f₂, f₃, f₄] := by
  let σ : Equiv.Perm (Fin 4) :=
    (Equiv.swap fin4_2 fin4_3) * (Equiv.swap fin4_1 fin4_2)
  have hperm := schwingerN_perm params Λ 4 ![f₁, f₂, f₃, f₄] σ
  simpa [σ, fin4_1, fin4_2, fin4_3, Function.comp, Equiv.Perm.mul_apply] using hperm

/-- GKS-II in the `(13)(24)` channel, obtained from `(12)(34)` via permutation symmetry. -/
theorem griffiths_second_13_24 (params : Phi4Params) (Λ : Rectangle)
    [CorrelationInequalityModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄ ≤
      schwingerN params Λ 4 ![f₁, f₂, f₃, f₄] := by
  have h := griffiths_second params Λ f₁ f₃ f₂ f₄ hf₁ hf₃ hf₂ hf₄
  calc
    schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄
        ≤ schwingerN params Λ 4 ![f₁, f₃, f₂, f₄] := h
    _ = schwingerN params Λ 4 ![f₁, f₂, f₃, f₄] :=
      schwingerN4_swap12 params Λ f₁ f₂ f₃ f₄

/-- GKS-II in the `(14)(23)` channel, obtained from `(12)(34)` via permutation symmetry. -/
theorem griffiths_second_14_23 (params : Phi4Params) (Λ : Rectangle)
    [CorrelationInequalityModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃ ≤
      schwingerN params Λ 4 ![f₁, f₂, f₃, f₄] := by
  have h := griffiths_second params Λ f₁ f₄ f₂ f₃ hf₁ hf₄ hf₂ hf₃
  calc
    schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃
        ≤ schwingerN params Λ 4 ![f₁, f₄, f₂, f₃] := h
    _ = schwingerN params Λ 4 ![f₁, f₂, f₃, f₄] :=
      schwingerN4_perm_01423 params Λ f₁ f₂ f₃ f₄

/-! ## Pairing-subtracted 4-point bounds -/

/-- The `(12)(34)` pairing-subtracted 4-point quantity
    `S₄ - S₂(12)S₂(34)`. -/
def truncatedFourPoint12 (params : Phi4Params) (Λ : Rectangle)
    (f₁ f₂ f₃ f₄ : TestFun2D) : ℝ :=
  schwingerN params Λ 4 ![f₁, f₂, f₃, f₄] -
    schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄

/-- The `(13)(24)` pairing-subtracted 4-point quantity
    `S₄ - S₂(13)S₂(24)`. -/
def truncatedFourPoint13 (params : Phi4Params) (Λ : Rectangle)
    (f₁ f₂ f₃ f₄ : TestFun2D) : ℝ :=
  schwingerN params Λ 4 ![f₁, f₂, f₃, f₄] -
    schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄

/-- The `(14)(23)` pairing-subtracted 4-point quantity
    `S₄ - S₂(14)S₂(23)`. -/
def truncatedFourPoint14 (params : Phi4Params) (Λ : Rectangle)
    (f₁ f₂ f₃ f₄ : TestFun2D) : ℝ :=
  schwingerN params Λ 4 ![f₁, f₂, f₃, f₄] -
    schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃

/-- Nonnegativity of the `(12)(34)` pairing-subtracted 4-point expression:
    `S₄ - S₂(12)S₂(34) ≥ 0`. -/
theorem pairing_subtracted_four_point_nonneg (params : Phi4Params) (Λ : Rectangle)
    [CorrelationInequalityModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    0 ≤ truncatedFourPoint12 params Λ f₁ f₂ f₃ f₄ := by
  have h := griffiths_second params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  unfold truncatedFourPoint12
  linarith

/-- Nonnegativity of the `(13)(24)` pairing-subtracted expression:
    `S₄ - S₂(13)S₂(24) ≥ 0`. -/
theorem pairing_subtracted_four_point_nonneg_13_24
    (params : Phi4Params) (Λ : Rectangle)
    [CorrelationInequalityModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    0 ≤ truncatedFourPoint13 params Λ f₁ f₂ f₃ f₄ := by
  have h := griffiths_second_13_24 params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  unfold truncatedFourPoint13
  linarith

/-- Nonnegativity of the `(14)(23)` pairing-subtracted expression:
    `S₄ - S₂(14)S₂(23) ≥ 0`. -/
theorem pairing_subtracted_four_point_nonneg_14_23
    (params : Phi4Params) (Λ : Rectangle)
    [CorrelationInequalityModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    0 ≤ truncatedFourPoint14 params Λ f₁ f₂ f₃ f₄ := by
  have h := griffiths_second_14_23 params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  unfold truncatedFourPoint14
  linarith

/-! ## FKG Inequality -/

/-- **FKG inequality**: For the φ⁴₂ measure, monotone increasing functions
    are positively correlated:
      ⟨F · G⟩ ≥ ⟨F⟩ · ⟨G⟩
    for F, G monotone increasing (in the sense of distributions).

    This is a far-reaching generalization of GKS-I and implies, among other things,
    that the 2-point function dominates the truncated 4-point function. -/
theorem fkg_inequality (params : Phi4Params) (Λ : Rectangle)
    [CorrelationInequalityModel params]
    (F G : FieldConfig2D → ℝ)
    (hF_mono : ∀ ω₁ ω₂ : FieldConfig2D, (∀ f, ω₁ f ≤ ω₂ f) → F ω₁ ≤ F ω₂)
    (hG_mono : ∀ ω₁ ω₂ : FieldConfig2D, (∀ f, ω₁ f ≤ ω₂ f) → G ω₁ ≤ G ω₂) :
    (∫ ω, F ω ∂(finiteVolumeMeasure params Λ)) *
      (∫ ω, G ω ∂(finiteVolumeMeasure params Λ)) ≤
    ∫ ω, F ω * G ω ∂(finiteVolumeMeasure params Λ) := by
  exact CorrelationInequalityModel.fkg_inequality
    (params := params) Λ F G hF_mono hG_mono

/-! ## Lebowitz Inequality -/

/-- **Lebowitz inequality**: The 4-point Schwinger function is bounded by the
    Gaussian (free field) prediction:
      ⟨φ(f₁)φ(f₂)φ(f₃)φ(f₄)⟩ ≤ ⟨φ(f₁)φ(f₂)⟩⟨φ(f₃)φ(f₄)⟩
                                    + ⟨φ(f₁)φ(f₃)⟩⟨φ(f₂)φ(f₄)⟩
                                    + ⟨φ(f₁)φ(f₄)⟩⟨φ(f₂)φ(f₃)⟩
    for f₁,...,f₄ ≥ 0.

    This is the upper bound complementing GKS-II (which gives a lower bound).
    Together, they "squeeze" the 4-point function near its Gaussian value
    for weak coupling. -/
theorem lebowitz_inequality (params : Phi4Params) (Λ : Rectangle)
    [CorrelationInequalityModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    schwingerN params Λ 4 ![f₁, f₂, f₃, f₄] ≤
      schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ +
      schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄ +
      schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃ := by
  exact CorrelationInequalityModel.lebowitz_inequality
    (params := params) Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄

/-- Upper bound on the `(12)(34)` pairing-subtracted expression from Lebowitz:
    `S₄ - S₂(12)S₂(34) ≤ S₂(13)S₂(24) + S₂(14)S₂(23)`. -/
theorem pairing_subtracted_four_point_upper_bound
    (params : Phi4Params) (Λ : Rectangle)
    [CorrelationInequalityModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    truncatedFourPoint12 params Λ f₁ f₂ f₃ f₄ ≤
      schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄ +
      schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃ := by
  have h := lebowitz_inequality params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  unfold truncatedFourPoint12
  linarith

/-- Upper bound on the `(13)(24)` pairing-subtracted expression from Lebowitz:
    `S₄ - S₂(13)S₂(24) ≤ S₂(12)S₂(34) + S₂(14)S₂(23)`. -/
theorem pairing_subtracted_four_point_upper_bound_13_24
    (params : Phi4Params) (Λ : Rectangle)
    [CorrelationInequalityModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    truncatedFourPoint13 params Λ f₁ f₂ f₃ f₄ ≤
      schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ +
      schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃ := by
  have h := lebowitz_inequality params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  unfold truncatedFourPoint13
  linarith

/-- Upper bound on the `(14)(23)` pairing-subtracted expression from Lebowitz:
    `S₄ - S₂(14)S₂(23) ≤ S₂(12)S₂(34) + S₂(13)S₂(24)`. -/
theorem pairing_subtracted_four_point_upper_bound_14_23
    (params : Phi4Params) (Λ : Rectangle)
    [CorrelationInequalityModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    truncatedFourPoint14 params Λ f₁ f₂ f₃ f₄ ≤
      schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ +
      schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄ := by
  have h := lebowitz_inequality params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  unfold truncatedFourPoint14
  linarith

/-- Two-sided estimate for the `(12)(34)` pairing-subtracted 4-point expression. -/
theorem pairing_subtracted_four_point_bounds
    (params : Phi4Params) (Λ : Rectangle)
    [CorrelationInequalityModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    0 ≤ truncatedFourPoint12 params Λ f₁ f₂ f₃ f₄ ∧
      truncatedFourPoint12 params Λ f₁ f₂ f₃ f₄ ≤
      schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄ +
      schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃ := by
  constructor
  · exact pairing_subtracted_four_point_nonneg
      params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  · exact pairing_subtracted_four_point_upper_bound
      params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄

/-- Absolute-value control of the `(12)(34)` pairing-subtracted 4-point expression:
    `|S₄ - S₂(12)S₂(34)| ≤ S₂(13)S₂(24) + S₂(14)S₂(23)`. -/
theorem pairing_subtracted_four_point_abs_bound
    (params : Phi4Params) (Λ : Rectangle)
    [CorrelationInequalityModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    |truncatedFourPoint12 params Λ f₁ f₂ f₃ f₄| ≤
      schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄ +
      schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃ := by
  have hnonneg := pairing_subtracted_four_point_nonneg
    params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  have hupper := pairing_subtracted_four_point_upper_bound
    params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  simpa [abs_of_nonneg hnonneg] using hupper

/-- Absolute-value control of the `(13)(24)` pairing-subtracted expression:
    `|S₄ - S₂(13)S₂(24)| ≤ S₂(12)S₂(34) + S₂(14)S₂(23)`. -/
theorem pairing_subtracted_four_point_abs_bound_13_24
    (params : Phi4Params) (Λ : Rectangle)
    [CorrelationInequalityModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    |truncatedFourPoint13 params Λ f₁ f₂ f₃ f₄| ≤
      schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ +
      schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃ := by
  have hnonneg := pairing_subtracted_four_point_nonneg_13_24
    params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  have hupper := pairing_subtracted_four_point_upper_bound_13_24
    params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  simpa [abs_of_nonneg hnonneg] using hupper

/-- Absolute-value control of the `(14)(23)` pairing-subtracted expression:
    `|S₄ - S₂(14)S₂(23)| ≤ S₂(12)S₂(34) + S₂(13)S₂(24)`. -/
theorem pairing_subtracted_four_point_abs_bound_14_23
    (params : Phi4Params) (Λ : Rectangle)
    [CorrelationInequalityModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    |truncatedFourPoint14 params Λ f₁ f₂ f₃ f₄| ≤
      schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ +
      schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄ := by
  have hnonneg := pairing_subtracted_four_point_nonneg_14_23
    params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  have hupper := pairing_subtracted_four_point_upper_bound_14_23
    params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  simpa [abs_of_nonneg hnonneg] using hupper

/-! ## Fully connected 4-point bounds -/

/-- Fully pairing-subtracted 4-point cumulant:
    `S₄ - (S₂(12)S₂(34) + S₂(13)S₂(24) + S₂(14)S₂(23))`.
    For Gaussian measures this vanishes identically. -/
def cumulantFourPoint (params : Phi4Params) (Λ : Rectangle)
    (f₁ f₂ f₃ f₄ : TestFun2D) : ℝ :=
  schwingerN params Λ 4 ![f₁, f₂, f₃, f₄] -
    (schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ +
      schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄ +
      schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃)

/-- Lebowitz implies nonpositivity of the fully connected 4-point cumulant. -/
theorem cumulantFourPoint_nonpos
    (params : Phi4Params) (Λ : Rectangle)
    [CorrelationInequalityModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    cumulantFourPoint params Λ f₁ f₂ f₃ f₄ ≤ 0 := by
  have hleb := lebowitz_inequality params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  unfold cumulantFourPoint
  linarith

/-- GKS-II yields a lower bound on the fully connected 4-point cumulant. -/
theorem cumulantFourPoint_lower_bound
    (params : Phi4Params) (Λ : Rectangle)
    [CorrelationInequalityModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    -(schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄ +
      schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃) ≤
      cumulantFourPoint params Λ f₁ f₂ f₃ f₄ := by
  have hgks := griffiths_second params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  unfold cumulantFourPoint
  linarith

/-- Absolute-value control of the fully connected 4-point cumulant. -/
theorem cumulantFourPoint_abs_bound
    (params : Phi4Params) (Λ : Rectangle)
    [CorrelationInequalityModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    |cumulantFourPoint params Λ f₁ f₂ f₃ f₄| ≤
      schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄ +
      schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃ := by
  have hnonpos := cumulantFourPoint_nonpos params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  have hlower := cumulantFourPoint_lower_bound params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  rw [abs_of_nonpos hnonpos]
  linarith

/-! ## All-channel combined bounds -/

/-- Combined 4-point bounds:
    every GKS-II pairing channel gives a lower bound, and Lebowitz gives the upper bound. -/
theorem schwinger_four_bounds_all_channels
    (params : Phi4Params) (Λ : Rectangle)
    [CorrelationInequalityModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    max (schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄)
      (max (schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄)
        (schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃))
      ≤ schwingerN params Λ 4 ![f₁, f₂, f₃, f₄] ∧
    schwingerN params Λ 4 ![f₁, f₂, f₃, f₄] ≤
      schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ +
      schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄ +
      schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃ := by
  have h12 := griffiths_second params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  have h13 := griffiths_second_13_24 params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  have h14 := griffiths_second_14_23 params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  have hupper := lebowitz_inequality params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  constructor
  · exact max_le h12 (max_le h13 h14)
  · exact hupper

/-- Three channel-wise lower bounds on the fully connected 4-point cumulant. -/
theorem cumulantFourPoint_lower_bounds_all_channels
    (params : Phi4Params) (Λ : Rectangle)
    [CorrelationInequalityModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    -(schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄ +
      schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃)
      ≤ cumulantFourPoint params Λ f₁ f₂ f₃ f₄ ∧
    -(schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ +
      schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃)
      ≤ cumulantFourPoint params Λ f₁ f₂ f₃ f₄ ∧
    -(schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ +
      schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄)
      ≤ cumulantFourPoint params Λ f₁ f₂ f₃ f₄ := by
  have h12 := griffiths_second params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  have h13 := griffiths_second_13_24 params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  have h14 := griffiths_second_14_23 params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  unfold cumulantFourPoint
  constructor
  · linarith
  · constructor
    · linarith
    · linarith

/-- Alternative absolute-value bound using the `(13)(24)` GKS-II lower channel. -/
theorem cumulantFourPoint_abs_bound_alt13
    (params : Phi4Params) (Λ : Rectangle)
    [CorrelationInequalityModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    |cumulantFourPoint params Λ f₁ f₂ f₃ f₄| ≤
      schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ +
      schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃ := by
  have hnonpos := cumulantFourPoint_nonpos params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  have hLowerAll := cumulantFourPoint_lower_bounds_all_channels
    params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  rcases hLowerAll with ⟨_, h13, _⟩
  rw [abs_of_nonpos hnonpos]
  linarith

/-- Alternative absolute-value bound using the `(14)(23)` GKS-II lower channel. -/
theorem cumulantFourPoint_abs_bound_alt14
    (params : Phi4Params) (Λ : Rectangle)
    [CorrelationInequalityModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    |cumulantFourPoint params Λ f₁ f₂ f₃ f₄| ≤
      schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ +
      schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄ := by
  have hnonpos := cumulantFourPoint_nonpos params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  have hLowerAll := cumulantFourPoint_lower_bounds_all_channels
    params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  rcases hLowerAll with ⟨_, _, h14⟩
  rw [abs_of_nonpos hnonpos]
  linarith

/-- Absolute value of the connected 4-point cumulant is bounded by the minimum
    of the three two-pair channel sums. -/
theorem cumulantFourPoint_abs_bound_min_channels
    (params : Phi4Params) (Λ : Rectangle)
    [CorrelationInequalityModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    |cumulantFourPoint params Λ f₁ f₂ f₃ f₄| ≤
      min
        (schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄ +
          schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃)
        (min
          (schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ +
            schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃)
          (schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ +
            schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄)) := by
  have h12 := cumulantFourPoint_abs_bound params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  have h13 := cumulantFourPoint_abs_bound_alt13 params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  have h14 := cumulantFourPoint_abs_bound_alt14 params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  exact le_min h12 (le_min h13 h14)

/-! ## Monotonicity of Schwinger functions in volume

The combination of GKS-II with Dirichlet monotonicity gives:
  Λ₁ ⊂ Λ₂ ⟹ S_{Λ₁}(f₁,...,fₙ) ≤ S_{Λ₂}(f₁,...,fₙ)
for non-negative test functions. -/

/-- **Dirichlet monotonicity of 2-point function**: For Λ₁ ⊂ Λ₂,
    S₂^{Λ₁}(f,g) ≤ S₂^{Λ₂}(f,g) for f, g ≥ 0.

    Proof: Dirichlet BC on the smaller region gives a smaller covariance,
    and by GKS-II the 2-point function is monotone in the covariance. -/
theorem schwinger_two_monotone (params : Phi4Params) (Λ₁ Λ₂ : Rectangle)
    [CorrelationInequalityModel params]
    (h : Λ₁.toSet ⊆ Λ₂.toSet)
    (f g : TestFun2D) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfΛ : ∀ x ∉ Λ₁.toSet, f x = 0) (hgΛ : ∀ x ∉ Λ₁.toSet, g x = 0) :
    schwingerTwo params Λ₁ f g ≤ schwingerTwo params Λ₂ f g := by
  exact CorrelationInequalityModel.schwinger_two_monotone
    (params := params) Λ₁ Λ₂ h f g hf hg hfΛ hgΛ

end

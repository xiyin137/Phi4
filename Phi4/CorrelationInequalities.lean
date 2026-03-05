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
      (_hF_mono : ∀ ω₁ ω₂ : FieldConfig2D,
        (∀ f, (∀ x, 0 ≤ f x) → ω₁ f ≤ ω₂ f) → F ω₁ ≤ F ω₂)
      (_hG_mono : ∀ ω₁ ω₂ : FieldConfig2D,
        (∀ f, (∀ x, 0 ≤ f x) → ω₁ f ≤ ω₂ f) → G ω₁ ≤ G ω₂),
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
  /-- Monotonicity of finite-volume 4-point moments under domain inclusion
      for nonnegative test-function inputs supported in the smaller volume. -/
  schwinger_four_monotone : ∀ (Λ₁ Λ₂ : Rectangle)
      (_h : Λ₁.toSet ⊆ Λ₂.toSet)
      (f : Fin 4 → TestFun2D)
      (_hf : ∀ i, ∀ x, 0 ≤ f i x)
      (_hfΛ : ∀ i, ∀ x ∉ Λ₁.toSet, f i x = 0),
      schwingerN params Λ₁ 4 f ≤ schwingerN params Λ₂ 4 f
  /-- Monotonicity of the finite-volume 2-point function under domain inclusion. -/
  schwinger_two_monotone : ∀ (Λ₁ Λ₂ : Rectangle)
      (_h : Λ₁.toSet ⊆ Λ₂.toSet)
      (f g : TestFun2D) (_hf : ∀ x, 0 ≤ f x) (_hg : ∀ x, 0 ≤ g x)
      (_hfΛ : ∀ x ∉ Λ₁.toSet, f x = 0) (_hgΛ : ∀ x ∉ Λ₁.toSet, g x = 0),
      schwingerTwo params Λ₁ f g ≤ schwingerTwo params Λ₂ f g

/-- Two-point correlation inequality input: GKS-I positivity and
    finite-volume monotonicity under domain inclusion. -/
class CorrelationTwoPointModel (params : Phi4Params) where
  griffiths_first : ∀ (Λ : Rectangle) (f g : TestFun2D)
      (_hf : ∀ x, 0 ≤ f x) (_hg : ∀ x, 0 ≤ g x),
      0 ≤ schwingerTwo params Λ f g
  schwinger_two_monotone : ∀ (Λ₁ Λ₂ : Rectangle)
      (_h : Λ₁.toSet ⊆ Λ₂.toSet)
      (f g : TestFun2D) (_hf : ∀ x, 0 ≤ f x) (_hg : ∀ x, 0 ≤ g x)
      (_hfΛ : ∀ x ∉ Λ₁.toSet, f x = 0) (_hgΛ : ∀ x ∉ Λ₁.toSet, g x = 0),
      schwingerTwo params Λ₁ f g ≤ schwingerTwo params Λ₂ f g

/-- Monotonicity interface for finite-volume `k`-point Schwinger moments under
    domain inclusion. This extends the existing two-point monotonicity surface
    to arbitrary fixed arity `k`. -/
class SchwingerNMonotoneModel (params : Phi4Params) (k : ℕ) where
  schwingerN_monotone : ∀ (Λ₁ Λ₂ : Rectangle)
      (_h : Λ₁.toSet ⊆ Λ₂.toSet)
      (f : Fin k → TestFun2D)
      (_hf : ∀ i, ∀ x, 0 ≤ f i x)
      (_hfΛ : ∀ i, ∀ x ∉ Λ₁.toSet, f i x = 0),
      schwingerN params Λ₁ k f ≤ schwingerN params Λ₂ k f

/-- Positivity interface for finite-volume `k`-point Schwinger moments on
    nonnegative test-function inputs. -/
class SchwingerNNonnegModel (params : Phi4Params) (k : ℕ) where
  schwingerN_nonneg : ∀ (Λ : Rectangle)
      (f : Fin k → TestFun2D)
      (_hf : ∀ i, ∀ x, 0 ≤ f i x),
      0 ≤ schwingerN params Λ k f

/-- Two-point monotonicity implies `k = 2` Schwinger-moment monotonicity. -/
instance (priority := 100) schwingerNMonotoneModel_two_of_correlationTwoPoint
    (params : Phi4Params) [CorrelationTwoPointModel params] :
    SchwingerNMonotoneModel params 2 where
  schwingerN_monotone := by
    intro Λ₁ Λ₂ h f hf hfΛ
    have hmono := CorrelationTwoPointModel.schwinger_two_monotone
      (params := params) Λ₁ Λ₂ h (f 0) (f 1) (hf 0) (hf 1) (hfΛ 0) (hfΛ 1)
    simpa [schwingerN_two_eq_schwingerTwo] using hmono

/-- GKS-I two-point positivity implies `k = 2` Schwinger-moment nonnegativity. -/
instance (priority := 100) schwingerNNonnegModel_two_of_correlationTwoPoint
    (params : Phi4Params) [CorrelationTwoPointModel params] :
    SchwingerNNonnegModel params 2 where
  schwingerN_nonneg := by
    intro Λ f hf
    have hnonneg := CorrelationTwoPointModel.griffiths_first
      (params := params) Λ (f 0) (f 1) (hf 0) (hf 1)
    simpa [schwingerN_two_eq_schwingerTwo] using hnonneg

/-- Four-point GKS-II input: one nonnegative pairing channel
    `(12)(34)` for nonnegative test functions. -/
class CorrelationGKSSecondModel (params : Phi4Params) where
  griffiths_second : ∀ (Λ : Rectangle)
      (f₁ f₂ f₃ f₄ : TestFun2D)
      (_hf₁ : ∀ x, 0 ≤ f₁ x) (_hf₂ : ∀ x, 0 ≤ f₂ x)
      (_hf₃ : ∀ x, 0 ≤ f₃ x) (_hf₄ : ∀ x, 0 ≤ f₄ x),
      schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ ≤
        schwingerN params Λ 4 ![f₁, f₂, f₃, f₄]

/-- Four-point Lebowitz upper-bound input for nonnegative test functions. -/
class CorrelationLebowitzModel (params : Phi4Params) where
  lebowitz_inequality : ∀ (Λ : Rectangle)
      (f₁ f₂ f₃ f₄ : TestFun2D)
      (_hf₁ : ∀ x, 0 ≤ f₁ x) (_hf₂ : ∀ x, 0 ≤ f₂ x)
      (_hf₃ : ∀ x, 0 ≤ f₃ x) (_hf₄ : ∀ x, 0 ≤ f₄ x),
      schwingerN params Λ 4 ![f₁, f₂, f₃, f₄] ≤
        schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ +
        schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄ +
        schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃

/-- FKG positive-correlation input for finite-volume observables. -/
class CorrelationFKGModel (params : Phi4Params) where
  fkg_inequality : ∀ (Λ : Rectangle)
      (F G : FieldConfig2D → ℝ)
      (_hF_mono : ∀ ω₁ ω₂ : FieldConfig2D,
        (∀ f, (∀ x, 0 ≤ f x) → ω₁ f ≤ ω₂ f) → F ω₁ ≤ F ω₂)
      (_hG_mono : ∀ ω₁ ω₂ : FieldConfig2D,
        (∀ f, (∀ x, 0 ≤ f x) → ω₁ f ≤ ω₂ f) → G ω₁ ≤ G ω₂),
      (∫ ω, F ω ∂(finiteVolumeMeasure params Λ)) *
        (∫ ω, G ω ∂(finiteVolumeMeasure params Λ)) ≤
      ∫ ω, F ω * G ω ∂(finiteVolumeMeasure params Λ)

/-- Any full correlation-inequality model provides the two-point subinterface. -/
instance (priority := 100) correlationTwoPointModel_of_full
    (params : Phi4Params) [CorrelationInequalityModel params] :
    CorrelationTwoPointModel params where
  griffiths_first := CorrelationInequalityModel.griffiths_first (params := params)
  schwinger_two_monotone := CorrelationInequalityModel.schwinger_two_monotone (params := params)

/-- Any full correlation-inequality model provides the FKG subinterface. -/
instance (priority := 100) correlationFKGModel_of_full
    (params : Phi4Params) [CorrelationInequalityModel params] :
    CorrelationFKGModel params where
  fkg_inequality := CorrelationInequalityModel.fkg_inequality (params := params)

/-- Atomic two-point/four-point/FKG inputs plus `k = 4` Schwinger-moment
    monotonicity reconstruct `CorrelationInequalityModel`. -/
instance (priority := 100) correlationInequalityModel_of_submodels
    (params : Phi4Params)
    [CorrelationTwoPointModel params]
    [CorrelationGKSSecondModel params]
    [CorrelationLebowitzModel params]
    [CorrelationFKGModel params]
    [SchwingerNMonotoneModel params 4] :
  CorrelationInequalityModel params where
  griffiths_first := CorrelationTwoPointModel.griffiths_first (params := params)
  griffiths_second := CorrelationGKSSecondModel.griffiths_second (params := params)
  fkg_inequality := CorrelationFKGModel.fkg_inequality (params := params)
  lebowitz_inequality := CorrelationLebowitzModel.lebowitz_inequality (params := params)
  schwinger_four_monotone := by
    intro Λ₁ Λ₂ h f hf hfΛ
    exact SchwingerNMonotoneModel.schwingerN_monotone
      (params := params) (k := 4) Λ₁ Λ₂ h f hf hfΛ
  schwinger_two_monotone := CorrelationTwoPointModel.schwinger_two_monotone (params := params)

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

/-- Bridge assumptions for deriving continuum volume-monotonicity of
    finite-volume `k`-point Schwinger moments from lattice-ordered
    approximants. -/
class LatticeSchwingerNMonotoneModel (params : Phi4Params) (k : ℕ) where
  latticeN : ∀ Λ : Rectangle, Phi4.RectLattice Λ → (Fin k → TestFun2D) → ℝ
  approx_monotone_pair : ∀ (Λ₁ Λ₂ : Rectangle)
      (_h : Λ₁.toSet ⊆ Λ₂.toSet)
      (f : Fin k → TestFun2D) (_hf : ∀ i, ∀ x, 0 ≤ f i x)
      (_hfΛ : ∀ i, ∀ x ∉ Λ₁.toSet, f i x = 0)
      (ε : ℝ), 0 < ε →
      ∃ L₁ : Phi4.RectLattice Λ₁, ∃ L₂ : Phi4.RectLattice Λ₂,
        latticeN Λ₁ L₁ f ≤ latticeN Λ₂ L₂ f ∧
        |schwingerN params Λ₁ k f - latticeN Λ₁ L₁ f| < ε ∧
        |schwingerN params Λ₂ k f - latticeN Λ₂ L₂ f| < ε

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

/-- Continuum `k`-point monotonicity from lattice-ordered approximation pairs. -/
theorem schwingerN_monotone_from_lattice
    (params : Phi4Params) (k : ℕ)
    [LatticeSchwingerNMonotoneModel params k]
    (Λ₁ Λ₂ : Rectangle)
    (h : Λ₁.toSet ⊆ Λ₂.toSet)
    (f : Fin k → TestFun2D) (hf : ∀ i, ∀ x, 0 ≤ f i x)
    (hfΛ : ∀ i, ∀ x ∉ Λ₁.toSet, f i x = 0) :
    schwingerN params Λ₁ k f ≤ schwingerN params Λ₂ k f := by
  apply le_of_approx_ordered
  intro ε hε
  rcases LatticeSchwingerNMonotoneModel.approx_monotone_pair
      (params := params) Λ₁ Λ₂ h f hf hfΛ ε hε with
      ⟨L₁, L₂, hmon, hclose₁, hclose₂⟩
  refine ⟨LatticeSchwingerNMonotoneModel.latticeN (params := params) Λ₁ L₁ f,
    LatticeSchwingerNMonotoneModel.latticeN (params := params) Λ₂ L₂ f,
    hmon, hclose₁, hclose₂⟩

/-- Lattice `k`-point monotonicity assumptions induce the continuum
    `SchwingerNMonotoneModel` interface. -/
instance (priority := 100) schwingerNMonotoneModel_of_lattice
    (params : Phi4Params) (k : ℕ)
    [LatticeSchwingerNMonotoneModel params k] :
    SchwingerNMonotoneModel params k where
  schwingerN_monotone := schwingerN_monotone_from_lattice (params := params) (k := k)

/-- Lattice two-point monotonicity yields a `k = 2` Schwinger-moment
    monotonicity instance directly (without a separate `_nonempty_of_` route). -/
instance (priority := 100) schwingerNMonotoneModel_two_of_lattice
    (params : Phi4Params)
    [LatticeSchwingerTwoMonotoneModel params] :
    SchwingerNMonotoneModel params 2 := by
  letI : LatticeSchwingerNMonotoneModel params 2 := {
    latticeN := fun Λ L f =>
      LatticeSchwingerTwoMonotoneModel.latticeTwo (params := params) Λ L (f 0) (f 1)
    approx_monotone_pair := by
      intro Λ₁ Λ₂ h f hf hfΛ ε hε
      rcases LatticeSchwingerTwoMonotoneModel.approx_monotone_pair
          (params := params) Λ₁ Λ₂ h
          (f 0) (f 1) (hf 0) (hf 1) (hfΛ 0) (hfΛ 1) ε hε with
          ⟨L₁, L₂, hmon, hclose₁, hclose₂⟩
      refine ⟨L₁, L₂, hmon, ?_, ?_⟩
      · simpa [schwingerN_two_eq_schwingerTwo] using hclose₁
      · simpa [schwingerN_two_eq_schwingerTwo] using hclose₂
  }
  infer_instance

/-- Build the full `CorrelationInequalityModel` from:
    1. lattice bridge inputs for GKS-I and 2-point monotonicity, and
    2. remaining core assumptions (GKS-II, FKG, Lebowitz, 4-point monotonicity). -/
def correlationInequalityModelOfLattice
    (params : Phi4Params)
    [LatticeGriffithsFirstModel params]
    [LatticeSchwingerTwoMonotoneModel params]
    [CorrelationGKSSecondModel params]
    [CorrelationLebowitzModel params]
    [CorrelationFKGModel params]
    [SchwingerNMonotoneModel params 4] :
    CorrelationInequalityModel params where
  griffiths_first := griffiths_first_from_lattice (params := params)
  griffiths_second := CorrelationGKSSecondModel.griffiths_second (params := params)
  fkg_inequality := CorrelationFKGModel.fkg_inequality (params := params)
  lebowitz_inequality := CorrelationLebowitzModel.lebowitz_inequality (params := params)
  schwinger_four_monotone := SchwingerNMonotoneModel.schwingerN_monotone (params := params)
  schwinger_two_monotone := schwinger_two_monotone_from_lattice (params := params)

/-- Low-priority instance: if lattice bridge data and the remaining core
    inequalities are available, synthesize the full correlation-inequality model. -/
instance (priority := 100) correlationInequalityModel_of_lattice
    (params : Phi4Params)
    [LatticeGriffithsFirstModel params]
    [LatticeSchwingerTwoMonotoneModel params]
    [CorrelationGKSSecondModel params]
    [CorrelationLebowitzModel params]
    [CorrelationFKGModel params]
    [SchwingerNMonotoneModel params 4] :
    CorrelationInequalityModel params :=
  correlationInequalityModelOfLattice params

/-- Lattice bridge data yields the two-point correlation-inequality subinterface. -/
instance (priority := 100) correlationTwoPointModel_of_lattice
    (params : Phi4Params)
    [LatticeGriffithsFirstModel params]
    [LatticeSchwingerTwoMonotoneModel params] :
    CorrelationTwoPointModel params where
  griffiths_first := griffiths_first_from_lattice (params := params)
  schwinger_two_monotone := schwinger_two_monotone_from_lattice (params := params)

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
    [CorrelationGKSSecondModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄ ≤
      schwingerN params Λ 4 ![f₁, f₂, f₃, f₄] := by
  have h := CorrelationGKSSecondModel.griffiths_second (params := params) Λ f₁ f₃ f₂ f₄ hf₁ hf₃ hf₂ hf₄
  calc
    schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄
        ≤ schwingerN params Λ 4 ![f₁, f₃, f₂, f₄] := h
    _ = schwingerN params Λ 4 ![f₁, f₂, f₃, f₄] :=
      schwingerN4_swap12 params Λ f₁ f₂ f₃ f₄

/-- GKS-II in the `(14)(23)` channel, obtained from `(12)(34)` via permutation symmetry. -/
theorem griffiths_second_14_23 (params : Phi4Params) (Λ : Rectangle)
    [CorrelationGKSSecondModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃ ≤
      schwingerN params Λ 4 ![f₁, f₂, f₃, f₄] := by
  have h := CorrelationGKSSecondModel.griffiths_second (params := params) Λ f₁ f₄ f₂ f₃ hf₁ hf₄ hf₂ hf₃
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
    [CorrelationGKSSecondModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    0 ≤ truncatedFourPoint12 params Λ f₁ f₂ f₃ f₄ := by
  have h := CorrelationGKSSecondModel.griffiths_second (params := params) Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  unfold truncatedFourPoint12
  linarith

/-- Nonnegativity of the `(13)(24)` pairing-subtracted expression:
    `S₄ - S₂(13)S₂(24) ≥ 0`. -/
theorem pairing_subtracted_four_point_nonneg_13_24
    (params : Phi4Params) (Λ : Rectangle)
    [CorrelationGKSSecondModel params]
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
    [CorrelationGKSSecondModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    0 ≤ truncatedFourPoint14 params Λ f₁ f₂ f₃ f₄ := by
  have h := griffiths_second_14_23 params Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  unfold truncatedFourPoint14
  linarith

/-- FKG implies nonnegativity of the connected finite-volume two-point function
    for nonnegative test functions. -/
theorem connectedSchwingerTwo_nonneg
    (params : Phi4Params) (Λ : Rectangle)
    [CorrelationFKGModel params]
    (f g : TestFun2D)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) :
    0 ≤ connectedSchwingerTwo params Λ f g := by
  have hmonoF :
      ∀ ω₁ ω₂ : FieldConfig2D,
        (∀ h : TestFun2D, (∀ x, 0 ≤ h x) → ω₁ h ≤ ω₂ h) →
        (fun ω : FieldConfig2D => ω f) ω₁ ≤ (fun ω : FieldConfig2D => ω f) ω₂ := by
    intro ω₁ ω₂ hω
    exact hω f hf
  have hmonoG :
      ∀ ω₁ ω₂ : FieldConfig2D,
        (∀ h : TestFun2D, (∀ x, 0 ≤ h x) → ω₁ h ≤ ω₂ h) →
        (fun ω : FieldConfig2D => ω g) ω₁ ≤ (fun ω : FieldConfig2D => ω g) ω₂ := by
    intro ω₁ ω₂ hω
    exact hω g hg
  have hfkg := CorrelationFKGModel.fkg_inequality (params := params) Λ
    (fun ω : FieldConfig2D => ω f)
    (fun ω : FieldConfig2D => ω g)
    hmonoF hmonoG
  have hfkg' :
      schwingerN params Λ 1 ![f] * schwingerN params Λ 1 ![g] ≤ schwingerTwo params Λ f g := by
    simpa [schwingerN, schwingerTwo] using hfkg
  unfold connectedSchwingerTwo
  exact sub_nonneg.mpr hfkg'

/-- Upper bound on the `(12)(34)` pairing-subtracted expression from Lebowitz:
    `S₄ - S₂(12)S₂(34) ≤ S₂(13)S₂(24) + S₂(14)S₂(23)`. -/
theorem pairing_subtracted_four_point_upper_bound
    (params : Phi4Params) (Λ : Rectangle)
    [CorrelationLebowitzModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    truncatedFourPoint12 params Λ f₁ f₂ f₃ f₄ ≤
      schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄ +
      schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃ := by
  have h := CorrelationLebowitzModel.lebowitz_inequality (params := params) Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  unfold truncatedFourPoint12
  linarith

/-- Upper bound on the `(13)(24)` pairing-subtracted expression from Lebowitz:
    `S₄ - S₂(13)S₂(24) ≤ S₂(12)S₂(34) + S₂(14)S₂(23)`. -/
theorem pairing_subtracted_four_point_upper_bound_13_24
    (params : Phi4Params) (Λ : Rectangle)
    [CorrelationLebowitzModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    truncatedFourPoint13 params Λ f₁ f₂ f₃ f₄ ≤
      schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ +
      schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃ := by
  have h := CorrelationLebowitzModel.lebowitz_inequality (params := params) Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  unfold truncatedFourPoint13
  linarith

/-- Upper bound on the `(14)(23)` pairing-subtracted expression from Lebowitz:
    `S₄ - S₂(14)S₂(23) ≤ S₂(12)S₂(34) + S₂(13)S₂(24)`. -/
theorem pairing_subtracted_four_point_upper_bound_14_23
    (params : Phi4Params) (Λ : Rectangle)
    [CorrelationLebowitzModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    truncatedFourPoint14 params Λ f₁ f₂ f₃ f₄ ≤
      schwingerTwo params Λ f₁ f₂ * schwingerTwo params Λ f₃ f₄ +
      schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄ := by
  have h := CorrelationLebowitzModel.lebowitz_inequality (params := params) Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  unfold truncatedFourPoint14
  linarith

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
    [CorrelationLebowitzModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    cumulantFourPoint params Λ f₁ f₂ f₃ f₄ ≤ 0 := by
  have hleb := CorrelationLebowitzModel.lebowitz_inequality (params := params) Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  unfold cumulantFourPoint
  linarith

/-- GKS-II yields a lower bound on the fully connected 4-point cumulant. -/
theorem cumulantFourPoint_lower_bound
    (params : Phi4Params) (Λ : Rectangle)
    [CorrelationGKSSecondModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    -(schwingerTwo params Λ f₁ f₃ * schwingerTwo params Λ f₂ f₄ +
      schwingerTwo params Λ f₁ f₄ * schwingerTwo params Λ f₂ f₃) ≤
      cumulantFourPoint params Λ f₁ f₂ f₃ f₄ := by
  have hgks := CorrelationGKSSecondModel.griffiths_second (params := params) Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  unfold cumulantFourPoint
  linarith

/-- Absolute-value control of the fully connected 4-point cumulant. -/
theorem cumulantFourPoint_abs_bound
    (params : Phi4Params) (Λ : Rectangle)
    [CorrelationGKSSecondModel params]
    [CorrelationLebowitzModel params]
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

/-- Three channel-wise lower bounds on the fully connected 4-point cumulant. -/
theorem cumulantFourPoint_lower_bounds_all_channels
    (params : Phi4Params) (Λ : Rectangle)
    [CorrelationGKSSecondModel params]
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
  have h12 := CorrelationGKSSecondModel.griffiths_second (params := params) Λ f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
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
    [CorrelationGKSSecondModel params]
    [CorrelationLebowitzModel params]
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
    [CorrelationGKSSecondModel params]
    [CorrelationLebowitzModel params]
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

end

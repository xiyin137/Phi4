/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import GaussianField
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Algebra.Module.WeakDual

/-!
# Core Definitions for φ⁴₂ Theory

This file defines the basic objects for the φ⁴ quantum field theory in 2 Euclidean dimensions,
following Glimm-Jaffe, *Quantum Physics: A Functional Integral Point of View*, Part II.

## Main definitions

* `TestFun2D` — Test function space S(ℝ²), Schwartz functions on Euclidean 2-space
* `FieldConfig2D` — Field configuration space S'(ℝ²) = WeakDual ℝ (S(ℝ²))
* `Phi4Params` — Parameters for the φ⁴₂ theory: mass m > 0 and coupling λ > 0
* `Rectangle` — Bounded rectangular regions Λ ⊂ ℝ² for volume cutoffs

## References

* [Glimm-Jaffe] Chapters 6-12
-/

noncomputable section

open MeasureTheory Topology

/-! ## Spacetime and test function spaces -/

/-- The Euclidean spacetime for d=2: ℝ². -/
abbrev Spacetime2D := EuclideanSpace ℝ (Fin 2)

/-- Test function space: Schwartz functions S(ℝ²).
    These are the "smearing functions" for the quantum field. -/
abbrev TestFun2D := SchwartzMap Spacetime2D ℝ

/-- Complex test functions S(ℝ²) → ℂ, needed for generating functionals. -/
abbrev TestFunℂ2D := SchwartzMap Spacetime2D ℂ

/-- Field configuration space: the topological dual S'(ℝ²).
    Elements ω ∈ S'(ℝ²) are distributions (generalized functions) on ℝ².
    This is `WeakDual ℝ (S(ℝ²))` from gaussian-field. -/
abbrev FieldConfig2D := GaussianField.Configuration TestFun2D

/-! ## Theory parameters -/

/-- Parameters for the φ⁴₂ theory: mass and coupling constant. -/
structure Phi4Params where
  /-- Mass parameter m > 0. -/
  mass : ℝ
  /-- Coupling constant λ > 0. -/
  coupling : ℝ
  /-- Mass is positive. -/
  mass_pos : 0 < mass
  /-- Coupling constant is positive. -/
  coupling_pos : 0 < coupling

/-! ## Volume cutoffs -/

/-- A rectangular region Λ = [a₁, b₁] × [a₂, b₂] ⊂ ℝ² for volume cutoffs.
    We use half-open rectangles aligned with the coordinate axes. -/
structure Rectangle where
  /-- Lower-left corner. -/
  x_min : ℝ
  y_min : ℝ
  /-- Upper-right corner. -/
  x_max : ℝ
  y_max : ℝ
  /-- The rectangle is non-degenerate. -/
  hx : x_min < x_max
  hy : y_min < y_max

namespace Rectangle

/-- The set of points in the rectangle. -/
def toSet (Λ : Rectangle) : Set Spacetime2D :=
  { x | Λ.x_min ≤ x 0 ∧ x 0 ≤ Λ.x_max ∧ Λ.y_min ≤ x 1 ∧ x 1 ≤ Λ.y_max }

/-- Width of the rectangle. -/
def width (Λ : Rectangle) : ℝ := Λ.x_max - Λ.x_min

/-- Height of the rectangle. -/
def height (Λ : Rectangle) : ℝ := Λ.y_max - Λ.y_min

/-- Area of the rectangle. -/
def area (Λ : Rectangle) : ℝ := Λ.width * Λ.height

theorem area_pos (Λ : Rectangle) : 0 < Λ.area := by
  exact mul_pos (sub_pos.mpr Λ.hx) (sub_pos.mpr Λ.hy)

/-- Symmetric rectangle [-L, L] × [-T, T]. -/
def symmetric (L T : ℝ) (hL : 0 < L) (hT : 0 < T) : Rectangle where
  x_min := -L
  y_min := -T
  x_max := L
  y_max := T
  hx := by linarith
  hy := by linarith

/-- Time-reflection of a rectangle across the x-axis (t ↦ -t).
    Convention: coordinate 0 is time (Euclidean time τ), coordinate 1 is space x. -/
def timeReflect (Λ : Rectangle) : Rectangle where
  x_min := -Λ.x_max
  y_min := Λ.y_min
  x_max := -Λ.x_min
  y_max := Λ.y_max
  hx := by linarith [Λ.hx]
  hy := Λ.hy

/-- The positive-time half: Λ ∩ {τ > 0}. -/
def positiveTimeHalf (Λ : Rectangle) (hΛ : Λ.x_min < 0 ∧ 0 < Λ.x_max) : Rectangle where
  x_min := 0
  y_min := Λ.y_min
  x_max := Λ.x_max
  y_max := Λ.y_max
  hx := hΛ.2
  hy := Λ.hy

/-- A rectangle is time-symmetric if x_min = -x_max. -/
def IsTimeSymmetric (Λ : Rectangle) : Prop :=
  Λ.x_min = -Λ.x_max

end Rectangle

/-! ## UV cutoff -/

/-- UV cutoff parameter κ > 0. The regularized field φ_κ = δ_κ * φ is obtained by
    convolving with an approximate delta function δ_κ of width ~ 1/κ. -/
structure UVCutoff where
  /-- The cutoff scale. -/
  κ : ℝ
  /-- κ is positive. -/
  hκ : 0 < κ

end

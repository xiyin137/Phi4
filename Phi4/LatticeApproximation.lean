/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.Defs

/-!
# Lattice Approximation Infrastructure on Rectangles

This file provides a concrete rectangular lattice over a finite-volume cutoff
region `Λ`. It is a geometric foundation for lattice-to-continuum arguments
used in correlation inequalities and infinite-volume construction.

## Main definitions

* `RectLattice Λ` — a rectangular mesh with positive time/space subdivisions
* `RectLattice.timeStep`, `RectLattice.spaceStep` — mesh spacings
* `RectLattice.node` — lattice nodes in `Λ`
* `RectLattice.cell` — mesh cells as sub-rectangles of `Λ`

## Main lemmas

* positivity of mesh spacings,
* nodes lie in `Λ`,
* each cell is contained in `Λ`.
-/

noncomputable section

namespace Phi4

open MeasureTheory

/-- Rectangular lattice with `Nt` time slices and `Nx` spatial slices over `Λ`. -/
structure RectLattice (Λ : Rectangle) where
  Nt : ℕ
  Nx : ℕ
  hNt : 0 < Nt
  hNx : 0 < Nx

namespace RectLattice

variable {Λ : Rectangle}

private def mkSpacetime2D (t x : ℝ) : Spacetime2D :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![t, x]

@[simp] private theorem mkSpacetime2D_time (t x : ℝ) :
    (mkSpacetime2D t x) 0 = t := by
  simp [mkSpacetime2D]

@[simp] private theorem mkSpacetime2D_space (t x : ℝ) :
    (mkSpacetime2D t x) 1 = x := by
  simp [mkSpacetime2D]

/-- Time mesh spacing `Δt = (x_max - x_min) / Nt`. -/
def timeStep (L : RectLattice Λ) : ℝ :=
  Λ.width / L.Nt

/-- Space mesh spacing `Δx = (y_max - y_min) / Nx`. -/
def spaceStep (L : RectLattice Λ) : ℝ :=
  Λ.height / L.Nx

theorem timeStep_pos (L : RectLattice Λ) : 0 < L.timeStep := by
  have hNtR : (0 : ℝ) < L.Nt := by exact_mod_cast L.hNt
  unfold timeStep Rectangle.width
  exact div_pos (sub_pos.mpr Λ.hx) hNtR

theorem spaceStep_pos (L : RectLattice Λ) : 0 < L.spaceStep := by
  have hNxR : (0 : ℝ) < L.Nx := by exact_mod_cast L.hNx
  unfold spaceStep Rectangle.height
  exact div_pos (sub_pos.mpr Λ.hy) hNxR

theorem timeStep_mul_Nt (L : RectLattice Λ) :
    (L.Nt : ℝ) * L.timeStep = Λ.width := by
  have hNt_ne : (L.Nt : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt L.hNt)
  unfold timeStep
  field_simp [hNt_ne]

theorem spaceStep_mul_Nx (L : RectLattice Λ) :
    (L.Nx : ℝ) * L.spaceStep = Λ.height := by
  have hNx_ne : (L.Nx : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt L.hNx)
  unfold spaceStep
  field_simp [hNx_ne]

/-- Lattice node `(i,j)` as a point in `ℝ²`. -/
def node (L : RectLattice Λ) (i : Fin (L.Nt + 1)) (j : Fin (L.Nx + 1)) : Spacetime2D :=
  mkSpacetime2D
    (Λ.x_min + (i.1 : ℝ) * L.timeStep)
    (Λ.y_min + (j.1 : ℝ) * L.spaceStep)

private theorem node_time_ge_lower (L : RectLattice Λ)
    (i : Fin (L.Nt + 1)) (j : Fin (L.Nx + 1)) :
    Λ.x_min ≤ (L.node i j) 0 := by
  have hnonneg : 0 ≤ (i.1 : ℝ) * L.timeStep := by
    exact mul_nonneg (Nat.cast_nonneg i.1) (le_of_lt L.timeStep_pos)
  simpa [node] using add_le_add_left hnonneg Λ.x_min

private theorem node_time_le_upper (L : RectLattice Λ)
    (i : Fin (L.Nt + 1)) (j : Fin (L.Nx + 1)) :
    (L.node i j) 0 ≤ Λ.x_max := by
  have hi_le_nat : i.1 ≤ L.Nt := Nat.le_of_lt_succ i.2
  have hi_le : (i.1 : ℝ) ≤ L.Nt := by exact_mod_cast hi_le_nat
  have hmul : (i.1 : ℝ) * L.timeStep ≤ (L.Nt : ℝ) * L.timeStep := by
    exact mul_le_mul_of_nonneg_right hi_le (le_of_lt L.timeStep_pos)
  have hNt : (L.Nt : ℝ) * L.timeStep = Λ.width := L.timeStep_mul_Nt
  have hbound : Λ.x_min + (i.1 : ℝ) * L.timeStep ≤ Λ.x_min + (L.Nt : ℝ) * L.timeStep := by
    simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hmul Λ.x_min
  have hupper : Λ.x_min + (L.Nt : ℝ) * L.timeStep = Λ.x_max := by
    calc
      Λ.x_min + (L.Nt : ℝ) * L.timeStep = Λ.x_min + Λ.width := by rw [hNt]
      _ = Λ.x_max := by
        unfold Rectangle.width
        ring
  have : Λ.x_min + (i.1 : ℝ) * L.timeStep ≤ Λ.x_max := by
    exact hbound.trans (by simp [hupper])
  simpa [node] using this

private theorem node_space_ge_lower (L : RectLattice Λ)
    (i : Fin (L.Nt + 1)) (j : Fin (L.Nx + 1)) :
    Λ.y_min ≤ (L.node i j) 1 := by
  have hnonneg : 0 ≤ (j.1 : ℝ) * L.spaceStep := by
    exact mul_nonneg (Nat.cast_nonneg j.1) (le_of_lt L.spaceStep_pos)
  simpa [node] using add_le_add_left hnonneg Λ.y_min

private theorem node_space_le_upper (L : RectLattice Λ)
    (i : Fin (L.Nt + 1)) (j : Fin (L.Nx + 1)) :
    (L.node i j) 1 ≤ Λ.y_max := by
  have hj_le_nat : j.1 ≤ L.Nx := Nat.le_of_lt_succ j.2
  have hj_le : (j.1 : ℝ) ≤ L.Nx := by exact_mod_cast hj_le_nat
  have hmul : (j.1 : ℝ) * L.spaceStep ≤ (L.Nx : ℝ) * L.spaceStep := by
    exact mul_le_mul_of_nonneg_right hj_le (le_of_lt L.spaceStep_pos)
  have hNx : (L.Nx : ℝ) * L.spaceStep = Λ.height := L.spaceStep_mul_Nx
  have hbound : Λ.y_min + (j.1 : ℝ) * L.spaceStep ≤ Λ.y_min + (L.Nx : ℝ) * L.spaceStep := by
    simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hmul Λ.y_min
  have hupper : Λ.y_min + (L.Nx : ℝ) * L.spaceStep = Λ.y_max := by
    calc
      Λ.y_min + (L.Nx : ℝ) * L.spaceStep = Λ.y_min + Λ.height := by rw [hNx]
      _ = Λ.y_max := by
        unfold Rectangle.height
        ring
  have : Λ.y_min + (j.1 : ℝ) * L.spaceStep ≤ Λ.y_max := by
    exact hbound.trans (by simp [hupper])
  simpa [node] using this

/-- Mesh cell `(i,j)` as a sub-rectangle of `Λ`. -/
def cell (L : RectLattice Λ) (i : Fin L.Nt) (j : Fin L.Nx) : Rectangle where
  x_min := Λ.x_min + (i.1 : ℝ) * L.timeStep
  y_min := Λ.y_min + (j.1 : ℝ) * L.spaceStep
  x_max := Λ.x_min + ((i.1 + 1 : ℕ) : ℝ) * L.timeStep
  y_max := Λ.y_min + ((j.1 + 1 : ℕ) : ℝ) * L.spaceStep
  hx := by
    have hi : (i.1 : ℝ) < ((i.1 + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_succ_self i.1
    have hmul : (i.1 : ℝ) * L.timeStep < ((i.1 + 1 : ℕ) : ℝ) * L.timeStep :=
      mul_lt_mul_of_pos_right hi L.timeStep_pos
    linarith
  hy := by
    have hj : (j.1 : ℝ) < ((j.1 + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_succ_self j.1
    have hmul : (j.1 : ℝ) * L.spaceStep < ((j.1 + 1 : ℕ) : ℝ) * L.spaceStep :=
      mul_lt_mul_of_pos_right hj L.spaceStep_pos
    linarith

/-- Cell width equals the time mesh spacing. -/
theorem cell_width_eq_timeStep (L : RectLattice Λ) (i : Fin L.Nt) (j : Fin L.Nx) :
    (L.cell i j).width = L.timeStep := by
  simp [Rectangle.width, cell]
  ring

/-- Cell height equals the space mesh spacing. -/
theorem cell_height_eq_spaceStep (L : RectLattice Λ) (i : Fin L.Nt) (j : Fin L.Nx) :
    (L.cell i j).height = L.spaceStep := by
  simp [Rectangle.height, cell]
  ring

/-- Cell area equals one mesh area element `Δt * Δx`. -/
theorem cell_area_eq_meshArea (L : RectLattice Λ) (i : Fin L.Nt) (j : Fin L.Nx) :
    (L.cell i j).area = L.timeStep * L.spaceStep := by
  simp [Rectangle.area, cell_width_eq_timeStep, cell_height_eq_spaceStep]

/-- Anchor point of cell `(i,j)`, chosen as its lower-left corner node. -/
def cellAnchor (L : RectLattice Λ) (i : Fin L.Nt) (j : Fin L.Nx) : Spacetime2D :=
  L.node ⟨i.1, Nat.lt_succ_of_lt i.2⟩ ⟨j.1, Nat.lt_succ_of_lt j.2⟩

/-- Node-sampling discretization of a test function on lattice nodes. -/
def discretizeByNode (L : RectLattice Λ) (f : TestFun2D) :
    Fin (L.Nt + 1) → Fin (L.Nx + 1) → ℝ :=
  fun i j => f (L.node i j)

/-- Cell-anchor sampling discretization of a test function on mesh cells. -/
def discretizeByCellAnchor (L : RectLattice Λ) (f : TestFun2D) :
    Fin L.Nt → Fin L.Nx → ℝ :=
  fun i j => f (L.cellAnchor i j)

/-- Integral of a test function over one mesh cell. -/
def cellIntegral (L : RectLattice Λ) (f : TestFun2D) (i : Fin L.Nt) (j : Fin L.Nx) : ℝ :=
  ∫ x in (L.cell i j).toSet, f x

/-- Additivity of cell integrals. -/
theorem cellIntegral_add
    (L : RectLattice Λ) (f g : TestFun2D) (i : Fin L.Nt) (j : Fin L.Nx) :
    L.cellIntegral (f + g) i j = L.cellIntegral f i j + L.cellIntegral g i j := by
  unfold cellIntegral
  have hf : Integrable f (volume.restrict (L.cell i j).toSet) :=
    (SchwartzMap.integrable (μ := (volume : Measure Spacetime2D)) f).restrict
  have hg : Integrable g (volume.restrict (L.cell i j).toSet) :=
    (SchwartzMap.integrable (μ := (volume : Measure Spacetime2D)) g).restrict
  exact integral_add hf hg

/-- Scalar linearity of cell integrals. -/
theorem cellIntegral_smul
    (L : RectLattice Λ) (c : ℝ) (f : TestFun2D) (i : Fin L.Nt) (j : Fin L.Nx) :
    L.cellIntegral (c • f) i j = c * L.cellIntegral f i j := by
  unfold cellIntegral
  exact integral_const_mul c f

/-- Average value of a test function over one mesh cell. -/
def cellAverage (L : RectLattice Λ) (f : TestFun2D) (i : Fin L.Nt) (j : Fin L.Nx) : ℝ :=
  L.cellIntegral f i j / (L.cell i j).area

/-- Cell-average discretization of a test function on mesh cells. -/
def discretizeByCellAverage (L : RectLattice Λ) (f : TestFun2D) :
    Fin L.Nt → Fin L.Nx → ℝ :=
  fun i j => L.cellAverage f i j

/-- Additivity of cell averages. -/
theorem cellAverage_add
    (L : RectLattice Λ) (f g : TestFun2D) (i : Fin L.Nt) (j : Fin L.Nx) :
    L.cellAverage (f + g) i j = L.cellAverage f i j + L.cellAverage g i j := by
  unfold cellAverage
  rw [L.cellIntegral_add f g i j]
  ring

/-- Scalar linearity of cell averages. -/
theorem cellAverage_smul
    (L : RectLattice Λ) (c : ℝ) (f : TestFun2D) (i : Fin L.Nt) (j : Fin L.Nx) :
    L.cellAverage (c • f) i j = c * L.cellAverage f i j := by
  unfold cellAverage
  rw [L.cellIntegral_smul c f i j]
  ring

/-- Cell-anchor Riemann sum on the finite lattice. -/
def riemannSumCellAnchor (L : RectLattice Λ) (f : TestFun2D) : ℝ :=
  ∑ i : Fin L.Nt, ∑ j : Fin L.Nx,
    (L.cell i j).area * L.discretizeByCellAnchor f i j

/-- Cell-average Riemann sum on the finite lattice. -/
def riemannSumCellAverage (L : RectLattice Λ) (f : TestFun2D) : ℝ :=
  ∑ i : Fin L.Nt, ∑ j : Fin L.Nx,
    (L.cell i j).area * L.discretizeByCellAverage f i j

/-- Additivity of cell-average Riemann sums. -/
theorem riemannSumCellAverage_add
    (L : RectLattice Λ) (f g : TestFun2D) :
    L.riemannSumCellAverage (f + g) =
      L.riemannSumCellAverage f + L.riemannSumCellAverage g := by
  unfold riemannSumCellAverage discretizeByCellAverage
  simp [L.cellAverage_add, Finset.sum_add_distrib, left_distrib]

/-- Scalar linearity of cell-average Riemann sums. -/
theorem riemannSumCellAverage_smul
    (L : RectLattice Λ) (c : ℝ) (f : TestFun2D) :
    L.riemannSumCellAverage (c • f) = c * L.riemannSumCellAverage f := by
  unfold riemannSumCellAverage discretizeByCellAverage
  simp [L.cellAverage_smul, Finset.mul_sum, mul_left_comm]

/-- Total cell integral: sum of exact integrals over all mesh cells. -/
def totalCellIntegral (L : RectLattice Λ) (f : TestFun2D) : ℝ :=
  ∑ i : Fin L.Nt, ∑ j : Fin L.Nx, L.cellIntegral f i j

/-- Additivity of total cell integrals. -/
theorem totalCellIntegral_add
    (L : RectLattice Λ) (f g : TestFun2D) :
    L.totalCellIntegral (f + g) = L.totalCellIntegral f + L.totalCellIntegral g := by
  unfold totalCellIntegral
  simp [cellIntegral_add, Finset.sum_add_distrib]

/-- Scalar linearity of total cell integrals. -/
theorem totalCellIntegral_smul
    (L : RectLattice Λ) (c : ℝ) (f : TestFun2D) :
    L.totalCellIntegral (c • f) = c * L.totalCellIntegral f := by
  unfold totalCellIntegral
  simp [cellIntegral_smul, Finset.mul_sum]

/-- Linear map given by total exact cell integration. -/
def totalCellIntegralLM (L : RectLattice Λ) : TestFun2D →ₗ[ℝ] ℝ where
  toFun := fun f => L.totalCellIntegral f
  map_add' := by
    intro f g
    exact L.totalCellIntegral_add f g
  map_smul' := by
    intro c f
    exact L.totalCellIntegral_smul c f

@[simp] theorem totalCellIntegralLM_apply (L : RectLattice Λ) (f : TestFun2D) :
    L.totalCellIntegralLM f = L.totalCellIntegral f := rfl

/-- Linear map given by cell-average Riemann summation. -/
def riemannSumCellAverageLM (L : RectLattice Λ) : TestFun2D →ₗ[ℝ] ℝ where
  toFun := fun f => L.riemannSumCellAverage f
  map_add' := by
    intro f g
    exact L.riemannSumCellAverage_add f g
  map_smul' := by
    intro c f
    exact L.riemannSumCellAverage_smul c f

@[simp] theorem riemannSumCellAverageLM_apply (L : RectLattice Λ) (f : TestFun2D) :
    L.riemannSumCellAverageLM f = L.riemannSumCellAverage f := rfl

end RectLattice

end Phi4

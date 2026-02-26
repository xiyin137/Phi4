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

private theorem timeStep_mul_Nt (L : RectLattice Λ) :
    (L.Nt : ℝ) * L.timeStep = Λ.width := by
  have hNt_ne : (L.Nt : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt L.hNt)
  unfold timeStep
  field_simp [hNt_ne]

private theorem spaceStep_mul_Nx (L : RectLattice Λ) :
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

/-- Every lattice node lies in the cutoff rectangle `Λ`. -/
theorem node_mem_toSet (L : RectLattice Λ)
    (i : Fin (L.Nt + 1)) (j : Fin (L.Nx + 1)) :
    L.node i j ∈ Λ.toSet := by
  exact ⟨L.node_time_ge_lower i j, L.node_time_le_upper i j,
    L.node_space_ge_lower i j, L.node_space_le_upper i j⟩

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

/-- Every mesh cell has strictly positive area. -/
theorem cell_area_pos (L : RectLattice Λ) (i : Fin L.Nt) (j : Fin L.Nx) :
    0 < (L.cell i j).area := by
  simpa [cell_area_eq_meshArea] using mul_pos L.timeStep_pos L.spaceStep_pos

/-- Anchor point of cell `(i,j)`, chosen as its lower-left corner node. -/
def cellAnchor (L : RectLattice Λ) (i : Fin L.Nt) (j : Fin L.Nx) : Spacetime2D :=
  L.node ⟨i.1, Nat.lt_succ_of_lt i.2⟩ ⟨j.1, Nat.lt_succ_of_lt j.2⟩

/-- The cell anchor lies in the corresponding mesh cell. -/
theorem cellAnchor_mem_cell (L : RectLattice Λ) (i : Fin L.Nt) (j : Fin L.Nx) :
    L.cellAnchor i j ∈ (L.cell i j).toSet := by
  constructor
  · rfl
  constructor
  · have h : (i.1 : ℝ) * L.timeStep ≤ ((i.1 + 1 : ℕ) : ℝ) * L.timeStep := by
      have hi : (i.1 : ℝ) ≤ ((i.1 + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ i.1
      exact mul_le_mul_of_nonneg_right hi (le_of_lt L.timeStep_pos)
    simpa [cellAnchor, node, cell, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      add_le_add_left h Λ.x_min
  constructor
  · rfl
  · have h : (j.1 : ℝ) * L.spaceStep ≤ ((j.1 + 1 : ℕ) : ℝ) * L.spaceStep := by
      have hj : (j.1 : ℝ) ≤ ((j.1 + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ j.1
      exact mul_le_mul_of_nonneg_right hj (le_of_lt L.spaceStep_pos)
    simpa [cellAnchor, node, cell, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      add_le_add_left h Λ.y_min

/-- The cell anchor lies in the ambient cutoff rectangle `Λ`. -/
theorem cellAnchor_mem_toSet (L : RectLattice Λ) (i : Fin L.Nt) (j : Fin L.Nx) :
    L.cellAnchor i j ∈ Λ.toSet := by
  simpa [cellAnchor] using
    (L.node_mem_toSet ⟨i.1, Nat.lt_succ_of_lt i.2⟩ ⟨j.1, Nat.lt_succ_of_lt j.2⟩)

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

/-- Average value of a test function over one mesh cell. -/
def cellAverage (L : RectLattice Λ) (f : TestFun2D) (i : Fin L.Nt) (j : Fin L.Nx) : ℝ :=
  L.cellIntegral f i j / (L.cell i j).area

/-- Cell-average discretization of a test function on mesh cells. -/
def discretizeByCellAverage (L : RectLattice Λ) (f : TestFun2D) :
    Fin L.Nt → Fin L.Nx → ℝ :=
  fun i j => L.cellAverage f i j

/-- Positivity of cell integrals for nonnegative test functions. -/
theorem cellIntegral_nonneg (L : RectLattice Λ) (f : TestFun2D)
    (i : Fin L.Nt) (j : Fin L.Nx)
    (hf : ∀ x, 0 ≤ f x) :
    0 ≤ L.cellIntegral f i j := by
  unfold cellIntegral
  exact integral_nonneg_of_ae (Filter.Eventually.of_forall hf)

/-- Positivity of cell averages for nonnegative test functions. -/
theorem cellAverage_nonneg (L : RectLattice Λ) (f : TestFun2D)
    (i : Fin L.Nt) (j : Fin L.Nx)
    (hf : ∀ x, 0 ≤ f x) :
    0 ≤ L.cellAverage f i j := by
  unfold cellAverage
  exact div_nonneg (L.cellIntegral_nonneg f i j hf) (le_of_lt (L.cell_area_pos i j))

/-- Each lattice cell is contained in the ambient rectangle `Λ`. -/
theorem cell_subset (L : RectLattice Λ) (i : Fin L.Nt) (j : Fin L.Nx) :
    (L.cell i j).toSet ⊆ Λ.toSet := by
  intro x hx
  rcases hx with ⟨hx0min, hx0max, hx1min, hx1max⟩

  have hcell_xmin_ge : Λ.x_min ≤ (L.cell i j).x_min := by
    have hnonneg : 0 ≤ (i.1 : ℝ) * L.timeStep := by
      exact mul_nonneg (Nat.cast_nonneg i.1) (le_of_lt L.timeStep_pos)
    simpa [cell] using add_le_add_left hnonneg Λ.x_min

  have hcell_ymin_ge : Λ.y_min ≤ (L.cell i j).y_min := by
    have hnonneg : 0 ≤ (j.1 : ℝ) * L.spaceStep := by
      exact mul_nonneg (Nat.cast_nonneg j.1) (le_of_lt L.spaceStep_pos)
    simpa [cell] using add_le_add_left hnonneg Λ.y_min

  have hx0lower : Λ.x_min ≤ x 0 := hcell_xmin_ge.trans hx0min
  have hx1lower : Λ.y_min ≤ x 1 := hcell_ymin_ge.trans hx1min

  have hi1_le_nat : i.1 + 1 ≤ L.Nt := Nat.succ_le_of_lt i.2
  have hj1_le_nat : j.1 + 1 ≤ L.Nx := Nat.succ_le_of_lt j.2
  have hi1_le : (((i.1 + 1 : ℕ) : ℝ)) ≤ L.Nt := by exact_mod_cast hi1_le_nat
  have hj1_le : (((j.1 + 1 : ℕ) : ℝ)) ≤ L.Nx := by exact_mod_cast hj1_le_nat

  have htime : (((i.1 + 1 : ℕ) : ℝ)) * L.timeStep ≤ (L.Nt : ℝ) * L.timeStep :=
    mul_le_mul_of_nonneg_right hi1_le (le_of_lt L.timeStep_pos)
  have hspace : (((j.1 + 1 : ℕ) : ℝ)) * L.spaceStep ≤ (L.Nx : ℝ) * L.spaceStep :=
    mul_le_mul_of_nonneg_right hj1_le (le_of_lt L.spaceStep_pos)

  have hNt : (L.Nt : ℝ) * L.timeStep = Λ.width := L.timeStep_mul_Nt
  have hNx : (L.Nx : ℝ) * L.spaceStep = Λ.height := L.spaceStep_mul_Nx

  have hx0upper : x 0 ≤ Λ.x_max := by
    have hcellTop : x 0 ≤ Λ.x_min + (((i.1 + 1 : ℕ) : ℝ)) * L.timeStep := by
      simpa [cell] using hx0max
    have hbound : Λ.x_min + (((i.1 + 1 : ℕ) : ℝ)) * L.timeStep ≤ Λ.x_max := by
      calc
        Λ.x_min + (((i.1 + 1 : ℕ) : ℝ)) * L.timeStep ≤
            Λ.x_min + (L.Nt : ℝ) * L.timeStep := by
              simpa [add_comm, add_left_comm, add_assoc] using
                add_le_add_left htime Λ.x_min
        _ = Λ.x_min + Λ.width := by rw [hNt]
        _ = Λ.x_max := by
          unfold Rectangle.width
          ring
    exact hcellTop.trans hbound

  have hx1upper : x 1 ≤ Λ.y_max := by
    have hcellTop : x 1 ≤ Λ.y_min + (((j.1 + 1 : ℕ) : ℝ)) * L.spaceStep := by
      simpa [cell] using hx1max
    have hbound : Λ.y_min + (((j.1 + 1 : ℕ) : ℝ)) * L.spaceStep ≤ Λ.y_max := by
      calc
        Λ.y_min + (((j.1 + 1 : ℕ) : ℝ)) * L.spaceStep ≤
            Λ.y_min + (L.Nx : ℝ) * L.spaceStep := by
              simpa [add_comm, add_left_comm, add_assoc] using
                add_le_add_left hspace Λ.y_min
        _ = Λ.y_min + Λ.height := by rw [hNx]
        _ = Λ.y_max := by
          unfold Rectangle.height
          ring
    exact hcellTop.trans hbound

  exact ⟨hx0lower, hx0upper, hx1lower, hx1upper⟩

end RectLattice

end Phi4

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

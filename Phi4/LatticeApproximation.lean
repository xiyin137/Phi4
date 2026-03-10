/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.Defs
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Order.SuccPred.IntervalSucc

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
open scoped Function

namespace Rectangle

/-- The half-open rectangle companion of `Λ`, using `Ioc` in each coordinate. -/
def iocSet (Λ : Rectangle) : Set Spacetime2D :=
  {x | Λ.x_min < x 0 ∧ x 0 ≤ Λ.x_max ∧ Λ.y_min < x 1 ∧ x 1 ≤ Λ.y_max}

/-- The half-open rectangle is a.e.-equal to the closed cutoff rectangle. -/
theorem iocSet_ae_eq_toSet (Λ : Rectangle) :
    Rectangle.iocSet Λ =ᵐ[volume] Λ.toSet := by
  let a : Fin 2 → ℝ := ![Λ.x_min, Λ.y_min]
  let b : Fin 2 → ℝ := ![Λ.x_max, Λ.y_max]
  have hpre_ioc :
      ((MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm ⁻¹' Set.pi Set.univ (fun k => Set.Ioc (a k) (b k))) =
        Rectangle.iocSet Λ := by
    ext x
    simp [Rectangle.iocSet, a, b, Fin.forall_fin_two, and_assoc]
  have hpre_icc :
      ((MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm ⁻¹' Set.Icc a b) = Λ.toSet := by
    ext x
    change a ≤ x.ofLp ∧ x.ofLp ≤ b ↔
      Λ.x_min ≤ x 0 ∧ x 0 ≤ Λ.x_max ∧ Λ.y_min ≤ x 1 ∧ x 1 ≤ Λ.y_max
    simp [a, b, Pi.le_def, Fin.forall_fin_two]
    constructor
    · rintro ⟨⟨hxmin, hymin⟩, hxmax, hymax⟩
      exact ⟨hxmin, hxmax, hymin, hymax⟩
    · rintro ⟨hxmin, hxmax, hymin, hymax⟩
      exact ⟨⟨hxmin, hymin⟩, hxmax, hymax⟩
  have hpi :
      Set.pi Set.univ (fun k => Set.Ioc (a k) (b k))
        =ᵐ[Measure.pi (fun _ : Fin 2 => (volume : Measure ℝ))] Set.Icc a b := by
    simpa using
      (Measure.univ_pi_Ioc_ae_eq_Icc (μ := fun _ : Fin 2 => (volume : Measure ℝ)) (f := a) (g := b))
  have hqmp :=
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)).quasiMeasurePreserving
  have hpre := hqmp.preimage_ae_eq hpi
  rwa [hpre_ioc, hpre_icc] at hpre

/-- The half-open rectangle is contained in the closed cutoff rectangle. -/
theorem iocSet_subset_toSet (Λ : Rectangle) :
    Rectangle.iocSet Λ ⊆ Λ.toSet := by
  intro x hx
  rcases hx with ⟨hxmin, hxmax, hymin, hymax⟩
  exact ⟨le_of_lt hxmin, hxmax, le_of_lt hymin, hymax⟩

/-- The real Lebesgue volume of a cutoff rectangle is its Euclidean area. -/
theorem volume_real_toSet_eq_area (Λ : Rectangle) :
    volume.real Λ.toSet = Λ.area := by
  let a : Fin 2 → ℝ := ![Λ.x_min, Λ.y_min]
  let b : Fin 2 → ℝ := ![Λ.x_max, Λ.y_max]
  have hpre :
      ((MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm ⁻¹' Set.Icc a b) = Λ.toSet := by
    ext x
    change a ≤ x.ofLp ∧ x.ofLp ≤ b ↔
      Λ.x_min ≤ x 0 ∧ x 0 ≤ Λ.x_max ∧ Λ.y_min ≤ x 1 ∧ x 1 ≤ Λ.y_max
    simp [a, b, Pi.le_def, Fin.forall_fin_two]
    constructor
    · rintro ⟨⟨hxmin, hymin⟩, hxmax, hymax⟩
      exact ⟨hxmin, hxmax, hymin, hymax⟩
    · rintro ⟨hxmin, hxmax, hymin, hymax⟩
      exact ⟨⟨hxmin, hymin⟩, hxmax, hymax⟩
  rw [← hpre,
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)).measureReal_preimage
      (s := Set.Icc a b) measurableSet_Icc.nullMeasurableSet,
    Measure.real, Real.volume_Icc_pi_toReal]
  · simp [Rectangle.area, Rectangle.width, Rectangle.height, a, b]
  · intro i
    fin_cases i
    · simpa [a, b] using le_of_lt Λ.hx
    · simpa [a, b] using le_of_lt Λ.hy

end Rectangle

/-- Rectangular lattice with `Nt` time slices and `Nx` spatial slices over `Λ`. -/
structure RectLattice (Λ : Rectangle) where
  Nt : ℕ
  Nx : ℕ
  hNt : 0 < Nt
  hNx : 0 < Nx

/-- Canonical square refinement lattice on `Λ` with `(n+1) × (n+1)` cells. -/
def uniformRectLattice (Λ : Rectangle) (n : ℕ) : RectLattice Λ where
  Nt := n + 1
  Nx := n + 1
  hNt := Nat.succ_pos n
  hNx := Nat.succ_pos n

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

/-- Half-open cell associated to `(i,j)`, using `Ioc` in each coordinate. This
is the disjoint mesh companion of `cell`, and is a.e.-equal to `cell.toSet`. -/
def cellIocSet (L : RectLattice Λ) (i : Fin L.Nt) (j : Fin L.Nx) : Set Spacetime2D :=
  {x | (L.cell i j).x_min < x 0 ∧ x 0 ≤ (L.cell i j).x_max ∧
       (L.cell i j).y_min < x 1 ∧ x 1 ≤ (L.cell i j).y_max}

/-- The half-open cell is a.e.-equal to the closed cell. -/
theorem cellIocSet_ae_eq_cell
    (L : RectLattice Λ) (i : Fin L.Nt) (j : Fin L.Nx) :
    L.cellIocSet i j =ᵐ[volume] (L.cell i j).toSet := by
  let a : Fin 2 → ℝ := ![(L.cell i j).x_min, (L.cell i j).y_min]
  let b : Fin 2 → ℝ := ![(L.cell i j).x_max, (L.cell i j).y_max]
  have hpre_ioc :
      ((MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm ⁻¹' Set.pi Set.univ (fun k => Set.Ioc (a k) (b k))) =
        L.cellIocSet i j := by
    ext x
    simp [cellIocSet, a, b, Fin.forall_fin_two, and_assoc]
  have hpre_icc :
      ((MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm ⁻¹' Set.Icc a b) = (L.cell i j).toSet := by
    ext x
    change a ≤ x.ofLp ∧ x.ofLp ≤ b ↔ _
    simp [a, b, Pi.le_def, Fin.forall_fin_two]
    constructor
    · rintro ⟨⟨hxmin, hymin⟩, hxmax, hymax⟩
      exact ⟨hxmin, hxmax, hymin, hymax⟩
    · rintro ⟨hxmin, hxmax, hymin, hymax⟩
      exact ⟨⟨hxmin, hymin⟩, hxmax, hymax⟩
  have hpi :
      Set.pi Set.univ (fun k => Set.Ioc (a k) (b k))
        =ᵐ[Measure.pi (fun _ : Fin 2 => (volume : Measure ℝ))] Set.Icc a b := by
    simpa using
      (Measure.univ_pi_Ioc_ae_eq_Icc (μ := fun _ : Fin 2 => (volume : Measure ℝ)) (f := a) (g := b))
  have hqmp :=
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)).quasiMeasurePreserving
  have hpre := hqmp.preimage_ae_eq hpi
  rwa [hpre_ioc, hpre_icc] at hpre

/-- Measurability of a half-open cell. -/
theorem measurableSet_cellIocSet
    (L : RectLattice Λ) (i : Fin L.Nt) (j : Fin L.Nx) :
    MeasurableSet (L.cellIocSet i j) := by
  unfold cellIocSet
  measurability

/-- A half-open cell is contained in the half-open ambient rectangle. -/
theorem cellIocSet_subset_iocSet
    (L : RectLattice Λ) (i : Fin L.Nt) (j : Fin L.Nx) :
    L.cellIocSet i j ⊆ Rectangle.iocSet Λ := by
  intro x hx
  rcases hx with ⟨htmin, htmax, hsmin, hsmax⟩
  have htime_nonneg : 0 ≤ (i : ℝ) * L.timeStep := by
    exact mul_nonneg (Nat.cast_nonneg i) (le_of_lt L.timeStep_pos)
  have hspace_nonneg : 0 ≤ (j : ℝ) * L.spaceStep := by
    exact mul_nonneg (Nat.cast_nonneg j) (le_of_lt L.spaceStep_pos)
  have htime_min_le : Λ.x_min ≤ (L.cell i j).x_min := by
    simpa [RectLattice.cell] using add_le_add_left htime_nonneg Λ.x_min
  have hspace_min_le : Λ.y_min ≤ (L.cell i j).y_min := by
    simpa [RectLattice.cell] using add_le_add_left hspace_nonneg Λ.y_min
  have hi_succ_le : (((i : ℕ) + 1 : ℕ) : ℝ) ≤ L.Nt := by
    exact_mod_cast Nat.succ_le_of_lt i.2
  have hj_succ_le : (((j : ℕ) + 1 : ℕ) : ℝ) ≤ L.Nx := by
    exact_mod_cast Nat.succ_le_of_lt j.2
  have htime_max_le : Λ.x_min + (((i : ℕ) + 1 : ℕ) : ℝ) * L.timeStep ≤ Λ.x_max := by
    have hmul :
        (((i : ℕ) + 1 : ℕ) : ℝ) * L.timeStep ≤ (L.Nt : ℝ) * L.timeStep := by
      exact mul_le_mul_of_nonneg_right hi_succ_le (le_of_lt L.timeStep_pos)
    rw [L.timeStep_mul_Nt] at hmul
    unfold Rectangle.width at hmul
    linarith
  have hspace_max_le : Λ.y_min + (((j : ℕ) + 1 : ℕ) : ℝ) * L.spaceStep ≤ Λ.y_max := by
    have hmul :
        (((j : ℕ) + 1 : ℕ) : ℝ) * L.spaceStep ≤ (L.Nx : ℝ) * L.spaceStep := by
      exact mul_le_mul_of_nonneg_right hj_succ_le (le_of_lt L.spaceStep_pos)
    rw [L.spaceStep_mul_Nx] at hmul
    unfold Rectangle.height at hmul
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact lt_of_le_of_lt htime_min_le htmin
  · exact htmax.trans htime_max_le
  · exact lt_of_le_of_lt hspace_min_le hsmin
  · exact hsmax.trans hspace_max_le

/-- The half-open time strips of the mesh cover the half-open time interval. -/
theorem iUnion_timeStrip_eq
    (L : RectLattice Λ) :
    (⋃ i : Fin L.Nt,
      Set.Ioc (Λ.x_min + (i : ℝ) * L.timeStep)
        (Λ.x_min + (((i : ℕ) + 1 : ℕ) : ℝ) * L.timeStep))
      = Set.Ioc Λ.x_min Λ.x_max := by
  have hf : Monotone (fun m : ℕ => Λ.x_min + (m : ℝ) * L.timeStep) := by
    intro a b hab
    have habR : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_left (mul_le_mul_of_nonneg_right habR (le_of_lt L.timeStep_pos)) Λ.x_min
  have hcover :
      (⋃ m ∈ Set.Ico 0 L.Nt,
        Set.Ioc (Λ.x_min + (m : ℝ) * L.timeStep)
          (Λ.x_min + ((m + 1 : ℕ) : ℝ) * L.timeStep))
        = Set.Ioc (Λ.x_min + (0 : ℕ) * L.timeStep)
            (Λ.x_min + (L.Nt : ℝ) * L.timeStep) := by
    simpa [Order.succ_eq_add_one] using
      (Monotone.biUnion_Ico_Ioc_map_succ
        (f := fun m : ℕ => Λ.x_min + (m : ℝ) * L.timeStep) hf 0 L.Nt)
  rw [show (Λ.x_min + (0 : ℕ) * L.timeStep) = Λ.x_min by ring,
    show (Λ.x_min + (L.Nt : ℝ) * L.timeStep) = Λ.x_max by
      rw [L.timeStep_mul_Nt]
      unfold Rectangle.width
      ring] at hcover
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
    have : x ∈ ⋃ m ∈ Set.Ico 0 L.Nt,
        Set.Ioc (Λ.x_min + (m : ℝ) * L.timeStep)
          (Λ.x_min + ((m + 1 : ℕ) : ℝ) * L.timeStep) := by
      refine Set.mem_iUnion.mpr ⟨(i : ℕ), ?_⟩
      refine Set.mem_iUnion.mpr ?_
      exact ⟨⟨Nat.zero_le i, i.2⟩, by simpa using hi⟩
    rw [hcover] at this
    exact this
  · intro x hx
    rw [← hcover] at hx
    rcases Set.mem_iUnion.mp hx with ⟨m, hm⟩
    rcases Set.mem_iUnion.mp hm with ⟨hmIco, hxIoc⟩
    exact Set.mem_iUnion.mpr ⟨⟨m, hmIco.2⟩, by simpa using hxIoc⟩

/-- The half-open space strips of the mesh cover the half-open spatial interval. -/
theorem iUnion_spaceStrip_eq
    (L : RectLattice Λ) :
    (⋃ j : Fin L.Nx,
      Set.Ioc (Λ.y_min + (j : ℝ) * L.spaceStep)
        (Λ.y_min + (((j : ℕ) + 1 : ℕ) : ℝ) * L.spaceStep))
      = Set.Ioc Λ.y_min Λ.y_max := by
  have hf : Monotone (fun m : ℕ => Λ.y_min + (m : ℝ) * L.spaceStep) := by
    intro a b hab
    have habR : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_left (mul_le_mul_of_nonneg_right habR (le_of_lt L.spaceStep_pos)) Λ.y_min
  have hcover :
      (⋃ m ∈ Set.Ico 0 L.Nx,
        Set.Ioc (Λ.y_min + (m : ℝ) * L.spaceStep)
          (Λ.y_min + ((m + 1 : ℕ) : ℝ) * L.spaceStep))
        = Set.Ioc (Λ.y_min + (0 : ℕ) * L.spaceStep)
            (Λ.y_min + (L.Nx : ℝ) * L.spaceStep) := by
    simpa [Order.succ_eq_add_one] using
      (Monotone.biUnion_Ico_Ioc_map_succ
        (f := fun m : ℕ => Λ.y_min + (m : ℝ) * L.spaceStep) hf 0 L.Nx)
  rw [show (Λ.y_min + (0 : ℕ) * L.spaceStep) = Λ.y_min by ring,
    show (Λ.y_min + (L.Nx : ℝ) * L.spaceStep) = Λ.y_max by
      rw [L.spaceStep_mul_Nx]
      unfold Rectangle.height
      ring] at hcover
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨j, hj⟩
    have : x ∈ ⋃ m ∈ Set.Ico 0 L.Nx,
        Set.Ioc (Λ.y_min + (m : ℝ) * L.spaceStep)
          (Λ.y_min + ((m + 1 : ℕ) : ℝ) * L.spaceStep) := by
      refine Set.mem_iUnion.mpr ⟨(j : ℕ), ?_⟩
      refine Set.mem_iUnion.mpr ?_
      exact ⟨⟨Nat.zero_le j, j.2⟩, by simpa using hj⟩
    rw [hcover] at this
    exact this
  · intro x hx
    rw [← hcover] at hx
    rcases Set.mem_iUnion.mp hx with ⟨m, hm⟩
    rcases Set.mem_iUnion.mp hm with ⟨hmIco, hxIoc⟩
    exact Set.mem_iUnion.mpr ⟨⟨m, hmIco.2⟩, by simpa using hxIoc⟩

/-- The half-open mesh cells cover the half-open ambient rectangle. -/
theorem iUnion_cellIocSet_eq_iocSet
    (L : RectLattice Λ) :
    (⋃ p : Fin L.Nt × Fin L.Nx, L.cellIocSet p.1 p.2) = Rectangle.iocSet Λ := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨p, hp⟩
    exact L.cellIocSet_subset_iocSet p.1 p.2 hp
  · intro hx
    have htime :
        x 0 ∈ ⋃ i : Fin L.Nt,
          Set.Ioc (Λ.x_min + (i : ℝ) * L.timeStep)
            (Λ.x_min + (((i : ℕ) + 1 : ℕ) : ℝ) * L.timeStep) := by
      rw [L.iUnion_timeStrip_eq]
      exact ⟨hx.1, hx.2.1⟩
    have hspace :
        x 1 ∈ ⋃ j : Fin L.Nx,
          Set.Ioc (Λ.y_min + (j : ℝ) * L.spaceStep)
            (Λ.y_min + (((j : ℕ) + 1 : ℕ) : ℝ) * L.spaceStep) := by
      rw [L.iUnion_spaceStrip_eq]
      exact ⟨hx.2.2.1, hx.2.2.2⟩
    rcases Set.mem_iUnion.mp htime with ⟨i, hi⟩
    rcases Set.mem_iUnion.mp hspace with ⟨j, hj⟩
    exact Set.mem_iUnion.mpr ⟨(i, j), by
      simpa [cellIocSet, RectLattice.cell] using And.intro hi.1 (And.intro hi.2 (And.intro hj.1 hj.2))⟩

/-- Half-open mesh cells are pairwise disjoint. -/
theorem pairwiseDisjoint_cellIocSet
    (L : RectLattice Λ) :
    Pairwise (fun p q : Fin L.Nt × Fin L.Nx => Disjoint (L.cellIocSet p.1 p.2) (L.cellIocSet q.1 q.2)) := by
  have htime_mono : Monotone (fun m : ℕ => Λ.x_min + (m : ℝ) * L.timeStep) := by
    intro a b hab
    have habR : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_left (mul_le_mul_of_nonneg_right habR (le_of_lt L.timeStep_pos)) Λ.x_min
  have hspace_mono : Monotone (fun m : ℕ => Λ.y_min + (m : ℝ) * L.spaceStep) := by
    intro a b hab
    have habR : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_left (mul_le_mul_of_nonneg_right habR (le_of_lt L.spaceStep_pos)) Λ.y_min
  have htime_pair :
      Pairwise (fun i i' : Fin L.Nt =>
        Disjoint
          (Set.Ioc (Λ.x_min + (i : ℝ) * L.timeStep)
            (Λ.x_min + (((i : ℕ) + 1 : ℕ) : ℝ) * L.timeStep))
          (Set.Ioc (Λ.x_min + (i' : ℝ) * L.timeStep)
            (Λ.x_min + (((i' : ℕ) + 1 : ℕ) : ℝ) * L.timeStep))) := by
    intro i i' hii'
    exact
      (Monotone.pairwise_disjoint_on_Ioc_succ (f := fun m : ℕ => Λ.x_min + (m : ℝ) * L.timeStep) htime_mono)
        (by exact fun h => hii' (Fin.ext h))
  have hspace_pair :
      Pairwise (fun j j' : Fin L.Nx =>
        Disjoint
          (Set.Ioc (Λ.y_min + (j : ℝ) * L.spaceStep)
            (Λ.y_min + (((j : ℕ) + 1 : ℕ) : ℝ) * L.spaceStep))
          (Set.Ioc (Λ.y_min + (j' : ℝ) * L.spaceStep)
            (Λ.y_min + (((j' : ℕ) + 1 : ℕ) : ℝ) * L.spaceStep))) := by
    intro j j' hjj'
    exact
      (Monotone.pairwise_disjoint_on_Ioc_succ (f := fun m : ℕ => Λ.y_min + (m : ℝ) * L.spaceStep) hspace_mono)
        (by exact fun h => hjj' (Fin.ext h))
  intro p q hpq
  rcases p with ⟨i, j⟩
  rcases q with ⟨i', j'⟩
  by_cases hi : i = i'
  · have hj : j ≠ j' := by
      intro h
      apply hpq
      exact Prod.ext hi h
    refine Set.disjoint_left.2 ?_
    intro x hx hx'
    have hsj : x 1 ∈ Set.Ioc (Λ.y_min + (j : ℝ) * L.spaceStep)
        (Λ.y_min + (((j : ℕ) + 1 : ℕ) : ℝ) * L.spaceStep) := ⟨hx.2.2.1, hx.2.2.2⟩
    have hsj' : x 1 ∈ Set.Ioc (Λ.y_min + (j' : ℝ) * L.spaceStep)
        (Λ.y_min + (((j' : ℕ) + 1 : ℕ) : ℝ) * L.spaceStep) := ⟨hx'.2.2.1, hx'.2.2.2⟩
    exact (hspace_pair hj).le_bot ⟨hsj, hsj'⟩
  · refine Set.disjoint_left.2 ?_
    intro x hx hx'
    have hti : x 0 ∈ Set.Ioc (Λ.x_min + (i : ℝ) * L.timeStep)
        (Λ.x_min + (((i : ℕ) + 1 : ℕ) : ℝ) * L.timeStep) := ⟨hx.1, hx.2.1⟩
    have hti' : x 0 ∈ Set.Ioc (Λ.x_min + (i' : ℝ) * L.timeStep)
        (Λ.x_min + (((i' : ℕ) + 1 : ℕ) : ℝ) * L.timeStep) := ⟨hx'.1, hx'.2.1⟩
    exact (htime_pair hi).le_bot ⟨hti, hti'⟩

/-- The sum of exact cell integrals equals the integral over the ambient rectangle. -/
theorem sum_cellIntegral_eq_setIntegral
    (L : RectLattice Λ) {f : Spacetime2D → ℝ}
    (hf : IntegrableOn f Λ.toSet volume) :
    (∑ i : Fin L.Nt, ∑ j : Fin L.Nx, ∫ x in (L.cell i j).toSet, f x)
      = ∫ x in Λ.toSet, f x := by
  let s : Fin L.Nt × Fin L.Nx → Set Spacetime2D := fun p => L.cellIocSet p.1 p.2
  have hs_meas : ∀ p, MeasurableSet (s p) := by
    intro p
    exact L.measurableSet_cellIocSet p.1 p.2
  have hs_disj : Pairwise (Disjoint on s) := by
    intro p q hpq
    simpa [s] using L.pairwiseDisjoint_cellIocSet hpq
  have hs_int : ∀ p, IntegrableOn f (s p) volume := by
    intro p
    exact hf.mono_set (Set.Subset.trans (L.cellIocSet_subset_iocSet p.1 p.2) (Rectangle.iocSet_subset_toSet Λ))
  have hioc :
      (∑ i : Fin L.Nt, ∑ j : Fin L.Nx, ∫ x in (L.cell i j).toSet, f x)
        = ∑ p : Fin L.Nt × Fin L.Nx, ∫ x in s p, f x := by
    have hprod :
        (∑ i : Fin L.Nt, ∑ j : Fin L.Nx, ∫ x in s (i, j), f x)
          = ∑ p : Fin L.Nt × Fin L.Nx, ∫ x in s p, f x := by
      simpa [s] using
        (Fintype.sum_prod_type'
          (fun i : Fin L.Nt => fun j : Fin L.Nx => ∫ x in s (i, j), f x)).symm
    calc
      (∑ i : Fin L.Nt, ∑ j : Fin L.Nx, ∫ x in (L.cell i j).toSet, f x)
        = ∑ i : Fin L.Nt, ∑ j : Fin L.Nx, ∫ x in s (i, j), f x := by
            refine Finset.sum_congr rfl ?_
            intro i _
            refine Finset.sum_congr rfl ?_
            intro j _
            simpa [s] using (MeasureTheory.setIntegral_congr_set (L.cellIocSet_ae_eq_cell i j).symm : _)
      _ = ∑ p : Fin L.Nt × Fin L.Nx, ∫ x in s p, f x := hprod
  calc
    (∑ i : Fin L.Nt, ∑ j : Fin L.Nx, ∫ x in (L.cell i j).toSet, f x)
      = ∑ p : Fin L.Nt × Fin L.Nx, ∫ x in s p, f x := hioc
    _ = ∫ x in ⋃ p, s p, f x := by
      symm
      exact MeasureTheory.integral_iUnion_fintype hs_meas hs_disj hs_int
    _ = ∫ x in Rectangle.iocSet Λ, f x := by rw [L.iUnion_cellIocSet_eq_iocSet]
    _ = ∫ x in Λ.toSet, f x := by
      exact MeasureTheory.setIntegral_congr_set (Rectangle.iocSet_ae_eq_toSet Λ)

/-- Anchor point of cell `(i,j)`, chosen as its lower-left corner node. -/
def cellAnchor (L : RectLattice Λ) (i : Fin L.Nt) (j : Fin L.Nx) : Spacetime2D :=
  L.node ⟨i.1, Nat.lt_succ_of_lt i.2⟩ ⟨j.1, Nat.lt_succ_of_lt j.2⟩

@[simp] theorem cellAnchor_time (L : RectLattice Λ) (i : Fin L.Nt) (j : Fin L.Nx) :
    (L.cellAnchor i j) 0 = Λ.x_min + (i.1 : ℝ) * L.timeStep := by
  simp [cellAnchor, node]

@[simp] theorem cellAnchor_space (L : RectLattice Λ) (i : Fin L.Nt) (j : Fin L.Nx) :
    (L.cellAnchor i j) 1 = Λ.y_min + (j.1 : ℝ) * L.spaceStep := by
  simp [cellAnchor, node]

/-- The chosen anchor is contained in its cell. -/
theorem cellAnchor_mem_cell (L : RectLattice Λ) (i : Fin L.Nt) (j : Fin L.Nx) :
    L.cellAnchor i j ∈ (L.cell i j).toSet := by
  constructor
  · simp [cell, cellAnchor_time]
  constructor
  · have hi : (i.1 : ℝ) ≤ ((i.1 + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.le_succ i.1)
    have hmul : (i.1 : ℝ) * L.timeStep ≤ ((i.1 + 1 : ℕ) : ℝ) * L.timeStep :=
      mul_le_mul_of_nonneg_right hi (le_of_lt L.timeStep_pos)
    simpa [cell, cellAnchor_time] using add_le_add_left hmul Λ.x_min
  constructor
  · simp [cell, cellAnchor_space]
  · have hj : (j.1 : ℝ) ≤ ((j.1 + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.le_succ j.1)
    have hmul : (j.1 : ℝ) * L.spaceStep ≤ ((j.1 + 1 : ℕ) : ℝ) * L.spaceStep :=
      mul_le_mul_of_nonneg_right hj (le_of_lt L.spaceStep_pos)
    simpa [cell, cellAnchor_space] using add_le_add_left hmul Λ.y_min

/-- Points in a cell differ from the anchor by at most one time-step in the time
coordinate. -/
theorem abs_sub_cellAnchor_time_le_timeStep
    (L : RectLattice Λ) (i : Fin L.Nt) (j : Fin L.Nx) {x : Spacetime2D}
    (hx : x ∈ (L.cell i j).toSet) :
    |x 0 - (L.cellAnchor i j) 0| ≤ L.timeStep := by
  rcases hx with ⟨hxmin, hxmax, -, -⟩
  have hleft : 0 ≤ x 0 - (L.cellAnchor i j) 0 := by
    exact sub_nonneg.mpr (by simpa [cell, cellAnchor_time] using hxmin)
  have hright : x 0 - (L.cellAnchor i j) 0 ≤ L.timeStep := by
    have hxmax' : x 0 ≤ Λ.x_min + ((i.1 + 1 : ℕ) : ℝ) * L.timeStep := by
      simpa [cell] using hxmax
    rw [cellAnchor_time]
    have hsub :=
      sub_le_sub_right hxmax' (Λ.x_min + (i.1 : ℝ) * L.timeStep)
    calc
      x 0 - (Λ.x_min + (i.1 : ℝ) * L.timeStep)
        ≤ (Λ.x_min + ((i.1 + 1 : ℕ) : ℝ) * L.timeStep) -
            (Λ.x_min + (i.1 : ℝ) * L.timeStep) := hsub
      _ = (((i.1 : ℝ) + 1) * L.timeStep) - (i.1 : ℝ) * L.timeStep := by
            norm_num
      _ = L.timeStep := by ring
  rw [abs_of_nonneg hleft]
  exact hright

/-- Points in a cell differ from the anchor by at most one space-step in the
space coordinate. -/
theorem abs_sub_cellAnchor_space_le_spaceStep
    (L : RectLattice Λ) (i : Fin L.Nt) (j : Fin L.Nx) {x : Spacetime2D}
    (hx : x ∈ (L.cell i j).toSet) :
    |x 1 - (L.cellAnchor i j) 1| ≤ L.spaceStep := by
  rcases hx with ⟨-, -, hymin, hymax⟩
  have hleft : 0 ≤ x 1 - (L.cellAnchor i j) 1 := by
    exact sub_nonneg.mpr (by simpa [cell, cellAnchor_space] using hymin)
  have hright : x 1 - (L.cellAnchor i j) 1 ≤ L.spaceStep := by
    have hymax' : x 1 ≤ Λ.y_min + ((j.1 + 1 : ℕ) : ℝ) * L.spaceStep := by
      simpa [cell] using hymax
    rw [cellAnchor_space]
    have hsub :=
      sub_le_sub_right hymax' (Λ.y_min + (j.1 : ℝ) * L.spaceStep)
    calc
      x 1 - (Λ.y_min + (j.1 : ℝ) * L.spaceStep)
        ≤ (Λ.y_min + ((j.1 + 1 : ℕ) : ℝ) * L.spaceStep) -
            (Λ.y_min + (j.1 : ℝ) * L.spaceStep) := hsub
      _ = (((j.1 : ℝ) + 1) * L.spaceStep) - (j.1 : ℝ) * L.spaceStep := by
            norm_num
      _ = L.spaceStep := by ring
  rw [abs_of_nonneg hleft]
  exact hright

/-- The distance from any point in a cell to the chosen anchor is bounded by the
sum of the two mesh spacings. -/
theorem dist_cellAnchor_le_timeStep_add_spaceStep
    (L : RectLattice Λ) (i : Fin L.Nt) (j : Fin L.Nx) {x : Spacetime2D}
    (hx : x ∈ (L.cell i j).toSet) :
    dist x (L.cellAnchor i j) ≤ L.timeStep + L.spaceStep := by
  rw [dist_eq_norm]
  have h0 : ‖(x - L.cellAnchor i j) 0‖ ≤ L.timeStep := by
    simpa using L.abs_sub_cellAnchor_time_le_timeStep (i := i) (j := j) hx
  have h1 : ‖(x - L.cellAnchor i j) 1‖ ≤ L.spaceStep := by
    simpa using L.abs_sub_cellAnchor_space_le_spaceStep (i := i) (j := j) hx
  have hsq :
      ‖x - L.cellAnchor i j‖ ^ 2 =
        ‖(x - L.cellAnchor i j) 0‖ ^ 2 + ‖(x - L.cellAnchor i j) 1‖ ^ 2 := by
    simpa using (PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 => ℝ) (x - L.cellAnchor i j))
  have h0' : ‖(x - L.cellAnchor i j) 0‖ ^ 2 ≤ L.timeStep ^ 2 := by
    gcongr
  have h1' : ‖(x - L.cellAnchor i j) 1‖ ^ 2 ≤ L.spaceStep ^ 2 := by
    gcongr
  have hcross : 0 ≤ 2 * L.timeStep * L.spaceStep := by
    nlinarith [L.timeStep_pos, L.spaceStep_pos]
  have hsum_sq : ‖x - L.cellAnchor i j‖ ^ 2 ≤ (L.timeStep + L.spaceStep) ^ 2 := by
    rw [hsq]
    nlinarith [h0', h1', hcross]
  have hnonneg : 0 ≤ ‖x - L.cellAnchor i j‖ := norm_nonneg _
  have hrhs_nonneg : 0 ≤ L.timeStep + L.spaceStep := by
    nlinarith [L.timeStep_pos, L.spaceStep_pos]
  exact (sq_le_sq₀ hnonneg hrhs_nonneg).mp hsum_sq

/-- Every mesh cell is contained in the ambient rectangle. -/
theorem cell_subset_rect
    (L : RectLattice Λ) (i : Fin L.Nt) (j : Fin L.Nx) {x : Spacetime2D}
    (hx : x ∈ (L.cell i j).toSet) :
    x ∈ Λ.toSet := by
  rcases hx with ⟨hxmin, hxmax, hymin, hymax⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      Λ.x_min ≤ (L.cell i j).x_min := by
        simp [cell, mul_nonneg (Nat.cast_nonneg i.1) (le_of_lt L.timeStep_pos)]
      _ ≤ x 0 := hxmin
  · have hi_le_nat : i.1 + 1 ≤ L.Nt := i.2
    have hi_le : (((i.1 + 1 : ℕ) : ℝ)) ≤ L.Nt := by
      exact_mod_cast hi_le_nat
    have hmul :
        (((i.1 + 1 : ℕ) : ℝ)) * L.timeStep ≤ (L.Nt : ℝ) * L.timeStep := by
      exact mul_le_mul_of_nonneg_right hi_le (le_of_lt L.timeStep_pos)
    calc
      x 0 ≤ (L.cell i j).x_max := hxmax
      _ = Λ.x_min + (((i.1 + 1 : ℕ) : ℝ)) * L.timeStep := by simp [cell]
      _ ≤ Λ.x_min + (L.Nt : ℝ) * L.timeStep := by
        simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hmul Λ.x_min
      _ = Λ.x_max := by
        rw [L.timeStep_mul_Nt]
        unfold Rectangle.width
        ring
  · calc
      Λ.y_min ≤ (L.cell i j).y_min := by
        simp [cell, mul_nonneg (Nat.cast_nonneg j.1) (le_of_lt L.spaceStep_pos)]
      _ ≤ x 1 := hymin
  · have hj_le_nat : j.1 + 1 ≤ L.Nx := j.2
    have hj_le : (((j.1 + 1 : ℕ) : ℝ)) ≤ L.Nx := by
      exact_mod_cast hj_le_nat
    have hmul :
        (((j.1 + 1 : ℕ) : ℝ)) * L.spaceStep ≤ (L.Nx : ℝ) * L.spaceStep := by
      exact mul_le_mul_of_nonneg_right hj_le (le_of_lt L.spaceStep_pos)
    calc
      x 1 ≤ (L.cell i j).y_max := hymax
      _ = Λ.y_min + (((j.1 + 1 : ℕ) : ℝ)) * L.spaceStep := by simp [cell]
      _ ≤ Λ.y_min + (L.Nx : ℝ) * L.spaceStep := by
        simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hmul Λ.y_min
      _ = Λ.y_max := by
        rw [L.spaceStep_mul_Nx]
        unfold Rectangle.height
        ring

/-- Every cell has width `Δt`. -/
theorem cell_width_eq_timeStep
    (L : RectLattice Λ) (i : Fin L.Nt) (j : Fin L.Nx) :
    (L.cell i j).width = L.timeStep := by
  unfold Rectangle.width cell
  calc
    (Λ.x_min + ((i.1 + 1 : ℕ) : ℝ) * L.timeStep) - (Λ.x_min + (i.1 : ℝ) * L.timeStep)
      = ((((i.1 + 1 : ℕ) : ℝ) - (i.1 : ℝ)) * L.timeStep) := by ring
    _ = (1 : ℝ) * L.timeStep := by norm_num
    _ = L.timeStep := by ring

/-- Every cell has height `Δx`. -/
theorem cell_height_eq_spaceStep
    (L : RectLattice Λ) (i : Fin L.Nt) (j : Fin L.Nx) :
    (L.cell i j).height = L.spaceStep := by
  unfold Rectangle.height cell
  calc
    (Λ.y_min + ((j.1 + 1 : ℕ) : ℝ) * L.spaceStep) - (Λ.y_min + (j.1 : ℝ) * L.spaceStep)
      = ((((j.1 + 1 : ℕ) : ℝ) - (j.1 : ℝ)) * L.spaceStep) := by ring
    _ = (1 : ℝ) * L.spaceStep := by norm_num
    _ = L.spaceStep := by ring

/-- Every cell has area `Δt * Δx`. -/
theorem cell_area_eq_timeStep_mul_spaceStep
    (L : RectLattice Λ) (i : Fin L.Nt) (j : Fin L.Nx) :
    (L.cell i j).area = L.timeStep * L.spaceStep := by
  unfold Rectangle.area
  rw [cell_width_eq_timeStep, cell_height_eq_spaceStep]

/-- The real Lebesgue volume of a mesh cell is its Euclidean area. -/
theorem cell_volume_real_toSet_eq_area
    (L : RectLattice Λ) (i : Fin L.Nt) (j : Fin L.Nx) :
    volume.real (L.cell i j).toSet = (L.cell i j).area :=
  Rectangle.volume_real_toSet_eq_area (L.cell i j)

/-- Cell areas are positive. -/
theorem cell_area_pos (L : RectLattice Λ) (i : Fin L.Nt) (j : Fin L.Nx) :
    0 < (L.cell i j).area := by
  rw [cell_area_eq_timeStep_mul_spaceStep]
  exact mul_pos L.timeStep_pos L.spaceStep_pos

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

/-- Cell-anchor Riemann sum for an arbitrary real-valued function on spacetime. -/
def riemannSumCellAnchorFun (L : RectLattice Λ) (f : Spacetime2D → ℝ) : ℝ :=
  ∑ i : Fin L.Nt, ∑ j : Fin L.Nx, (L.cell i j).area * f (L.cellAnchor i j)

/-- Piecewise-constant cell-anchor approximation over the half-open mesh. -/
def cellAnchorApproxFun (L : RectLattice Λ) (f : Spacetime2D → ℝ) : Spacetime2D → ℝ :=
  fun x =>
    ∑ p : Fin L.Nt × Fin L.Nx,
      Set.indicator (L.cellIocSet p.1 p.2) (fun _ => f (L.cellAnchor p.1 p.2)) x

/-- On a given half-open cell, the piecewise cell-anchor approximation equals
the anchor value of the corresponding cell. -/
theorem cellAnchorApproxFun_eq_of_mem_cellIocSet
    (L : RectLattice Λ) (f : Spacetime2D → ℝ)
    {i : Fin L.Nt} {j : Fin L.Nx} {x : Spacetime2D}
    (hx : x ∈ L.cellIocSet i j) :
    L.cellAnchorApproxFun f x = f (L.cellAnchor i j) := by
  classical
  let p₀ : Fin L.Nt × Fin L.Nx := (i, j)
  unfold cellAnchorApproxFun
  rw [Finset.sum_eq_single p₀]
  · simp [p₀, hx]
  · intro p hp hpne
    have hdisj := L.pairwiseDisjoint_cellIocSet hpne.symm
    have hnot : x ∉ L.cellIocSet p.1 p.2 := by
      intro hxp
      exact hdisj.le_bot ⟨hx, hxp⟩
    simp [Set.indicator_of_notMem, hnot]
  · intro hp₀
    simp at hp₀

/-- Integrating the piecewise cell-anchor approximation over the half-open mesh
recovers the cell-anchor Riemann sum. -/
theorem setIntegral_cellAnchorApproxFun_eq_riemannSumCellAnchorFun_ioc
    (L : RectLattice Λ) (f : Spacetime2D → ℝ) :
    ∫ x in Rectangle.iocSet Λ, L.cellAnchorApproxFun f x =
      L.riemannSumCellAnchorFun f := by
  have htoSet_ne_top : volume Λ.toSet ≠ ⊤ := by
    intro htop
    have hzero : volume.real Λ.toSet = 0 := by
      simp [Measure.real, htop]
    rw [Rectangle.volume_real_toSet_eq_area Λ] at hzero
    linarith [Λ.area_pos]
  have hioc_lt_top : volume (Rectangle.iocSet Λ) < ⊤ := by
    exact lt_of_le_of_lt
      (measure_mono (Rectangle.iocSet_subset_toSet Λ))
      (lt_top_iff_ne_top.mpr htoSet_ne_top)
  letI : IsFiniteMeasure (volume.restrict (Rectangle.iocSet Λ)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hioc_lt_top⟩
  have h_int :
      ∀ p : Fin L.Nt × Fin L.Nx,
        Integrable
          (Set.indicator (L.cellIocSet p.1 p.2) (fun _ : Spacetime2D => f (L.cellAnchor p.1 p.2)))
          (volume.restrict (Rectangle.iocSet Λ)) := by
    intro p
    have hconst :
        Integrable (fun _ : Spacetime2D => f (L.cellAnchor p.1 p.2))
          (volume.restrict (Rectangle.iocSet Λ)) := by
      exact integrable_const _
    exact hconst.indicator (L.measurableSet_cellIocSet p.1 p.2)
  unfold cellAnchorApproxFun riemannSumCellAnchorFun
  rw [integral_finset_sum]
  have hprod :
      (∑ i : Fin L.Nt, ∑ j : Fin L.Nx, (L.cell i j).area * f (L.cellAnchor i j))
        =
      ∑ p : Fin L.Nt × Fin L.Nx, (L.cell p.1 p.2).area * f (L.cellAnchor p.1 p.2) := by
    simpa using
      (Fintype.sum_prod_type'
        (fun i : Fin L.Nt => fun j : Fin L.Nx => (L.cell i j).area * f (L.cellAnchor i j))).symm
  rw [hprod]
  refine Finset.sum_congr rfl ?_
  intro p hp
  rcases p with ⟨i, j⟩
  calc
    ∫ x in Rectangle.iocSet Λ,
        Set.indicator (L.cellIocSet i j) (fun _ => f (L.cellAnchor i j)) x
      = ∫ x in Rectangle.iocSet Λ ∩ L.cellIocSet i j, f (L.cellAnchor i j) := by
          rw [MeasureTheory.setIntegral_indicator (L.measurableSet_cellIocSet i j)]
    _ = ∫ x in L.cellIocSet i j, f (L.cellAnchor i j) := by
          simpa [Set.inter_comm] using
            (show ∫ x in L.cellIocSet i j ∩ Rectangle.iocSet Λ, f (L.cellAnchor i j) =
                ∫ x in L.cellIocSet i j, f (L.cellAnchor i j) by
              rw [Set.inter_eq_left.mpr (L.cellIocSet_subset_iocSet i j)])
    _ = ∫ x in (L.cell i j).toSet, f (L.cellAnchor i j) := by
          exact MeasureTheory.setIntegral_congr_set (L.cellIocSet_ae_eq_cell i j)
    _ = (L.cell i j).area * f (L.cellAnchor i j) := by
          rw [MeasureTheory.setIntegral_const, L.cell_volume_real_toSet_eq_area i j]
          simp [smul_eq_mul]
  · intro p hp
    exact h_int p

/-- Integrating the piecewise cell-anchor approximation over the rectangle
recovers the cell-anchor Riemann sum. -/
theorem setIntegral_cellAnchorApproxFun_eq_riemannSumCellAnchorFun
    (L : RectLattice Λ) (f : Spacetime2D → ℝ) :
    ∫ x in Λ.toSet, L.cellAnchorApproxFun f x =
      L.riemannSumCellAnchorFun f := by
  calc
    ∫ x in Λ.toSet, L.cellAnchorApproxFun f x
      = ∫ x in Rectangle.iocSet Λ, L.cellAnchorApproxFun f x := by
          exact MeasureTheory.setIntegral_congr_set (Rectangle.iocSet_ae_eq_toSet Λ).symm
    _ = L.riemannSumCellAnchorFun f :=
          L.setIntegral_cellAnchorApproxFun_eq_riemannSumCellAnchorFun_ioc f

/-- The piecewise cell-anchor approximation is integrable on the ambient
rectangle. -/
theorem integrable_cellAnchorApproxFun
    (L : RectLattice Λ) (f : Spacetime2D → ℝ) :
    Integrable (L.cellAnchorApproxFun f) (volume.restrict Λ.toSet) := by
  have htoSet_ne_top : volume Λ.toSet ≠ ⊤ := by
    intro htop
    have hzero : volume.real Λ.toSet = 0 := by
      simp [Measure.real, htop]
    rw [Rectangle.volume_real_toSet_eq_area Λ] at hzero
    linarith [Λ.area_pos]
  letI : IsFiniteMeasure (volume.restrict Λ.toSet) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.mpr htoSet_ne_top⟩
  unfold cellAnchorApproxFun
  refine integrable_finset_sum _ ?_
  intro p hp
  exact (integrable_const _).indicator (L.measurableSet_cellIocSet p.1 p.2)

/-- Error bound on one cell between the anchor-value approximation and the exact
cell integral, assuming a uniform oscillation bound on that cell. -/
theorem cellAnchor_integral_error_le
    (L : RectLattice Λ) {f : Spacetime2D → ℝ}
    (i : Fin L.Nt) (j : Fin L.Nx) {a ε : ℝ}
    (h_int : IntegrableOn f (L.cell i j).toSet volume)
    (hosc : ∀ x ∈ (L.cell i j).toSet, |f x - a| ≤ ε) :
    |(L.cell i j).area * a - ∫ x in (L.cell i j).toSet, f x|
      ≤ ε * (L.cell i j).area := by
  have hvol_ne_top : volume ((L.cell i j).toSet) ≠ ⊤ := by
    intro htop
    have hzero : volume.real ((L.cell i j).toSet) = 0 := by
      simp [Measure.real, htop]
    rw [L.cell_volume_real_toSet_eq_area i j] at hzero
    linarith [L.cell_area_pos i j]
  have h_int_const : IntegrableOn (fun _ : Spacetime2D => a) (L.cell i j).toSet volume := by
    simpa using
      (integrableOn_const (μ := volume) (s := (L.cell i j).toSet) (C := a) (hs := hvol_ne_top))
  have hrestrict : (volume.restrict (L.cell i j).toSet).real Set.univ = (L.cell i j).area := by
    rw [Measure.real_def, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    simpa [Measure.real_def] using (L.cell_volume_real_toSet_eq_area i j)
  have hconst : ∫ x in (L.cell i j).toSet, a = (L.cell i j).area * a := by
    rw [MeasureTheory.integral_const, hrestrict]
    simp [smul_eq_mul]
  calc
    |(L.cell i j).area * a - ∫ x in (L.cell i j).toSet, f x|
      = |∫ x in (L.cell i j).toSet, (a - f x)| := by
          rw [integral_sub h_int_const h_int, hconst]
    _ = ‖∫ x in (L.cell i j).toSet, (a - f x)‖ := by rw [Real.norm_eq_abs]
    _ ≤ ε * volume.real (L.cell i j).toSet := by
          refine norm_setIntegral_le_of_norm_le_const (s := (L.cell i j).toSet) (C := ε) ?_ ?_
          · exact hvol_ne_top.lt_top
          · intro x hx
            simpa [Real.norm_eq_abs, abs_sub_comm] using hosc x hx
    _ = ε * (L.cell i j).area := by rw [L.cell_volume_real_toSet_eq_area]

/-- Global error bound between the cell-anchor Riemann sum and the sum of exact
cell integrals, assuming a uniform oscillation bound on every cell. -/
theorem riemannSumCellAnchorFun_sub_cellIntegral_sum_abs_le
    (L : RectLattice Λ) {f : Spacetime2D → ℝ} {ε : ℝ}
    (h_int : ∀ i j, IntegrableOn f (L.cell i j).toSet volume)
    (hosc : ∀ i j, ∀ x ∈ (L.cell i j).toSet, |f x - f (L.cellAnchor i j)| ≤ ε) :
    |L.riemannSumCellAnchorFun f - ∑ i : Fin L.Nt, ∑ j : Fin L.Nx, ∫ x in (L.cell i j).toSet, f x|
      ≤ ε * Λ.area := by
  let d : Fin L.Nt → Fin L.Nx → ℝ := fun i j =>
    (L.cell i j).area * f (L.cellAnchor i j) - ∫ x in (L.cell i j).toSet, f x
  have hcell : ∀ i j, |d i j| ≤ ε * (L.cell i j).area := by
    intro i j
    exact L.cellAnchor_integral_error_le i j (h_int i j) (hosc i j)
  calc
    |L.riemannSumCellAnchorFun f - ∑ i : Fin L.Nt, ∑ j : Fin L.Nx, ∫ x in (L.cell i j).toSet, f x|
      = |∑ i : Fin L.Nt, (∑ j : Fin L.Nx, d i j)| := by
          unfold riemannSumCellAnchorFun d
          rw [← Finset.sum_sub_distrib]
          simp_rw [← Finset.sum_sub_distrib]
    _ ≤ ∑ i : Fin L.Nt, |∑ j : Fin L.Nx, d i j| := by
          simpa using
            (Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := fun i : Fin L.Nt => ∑ j : Fin L.Nx, d i j))
    _ ≤ ∑ i : Fin L.Nt, ∑ j : Fin L.Nx, |d i j| := by
          refine Finset.sum_le_sum ?_
          intro i _
          simpa using
            (Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := fun j : Fin L.Nx => d i j))
    _ ≤ ∑ i : Fin L.Nt, ∑ j : Fin L.Nx, ε * (L.cell i j).area := by
          refine Finset.sum_le_sum ?_
          intro i _
          refine Finset.sum_le_sum ?_
          intro j _
          exact hcell i j
    _ = ∑ i : Fin L.Nt, ε * ∑ j : Fin L.Nx, (L.cell i j).area := by
          refine Finset.sum_congr rfl ?_
          intro i _
          exact Eq.symm (Finset.mul_sum _ _ _)
    _ = ε * (∑ i : Fin L.Nt, ∑ j : Fin L.Nx, (L.cell i j).area) := by
          exact Eq.symm (Finset.mul_sum _ _ _)
    _ = ε * Λ.area := by
          have harea : (∑ i : Fin L.Nt, ∑ j : Fin L.Nx, (L.cell i j).area) = Λ.area := by
            rw [Rectangle.area]
            simp_rw [cell_area_eq_timeStep_mul_spaceStep]
            simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            calc
              ↑(Fintype.card (Fin L.Nt)) * (↑(Fintype.card (Fin L.Nx)) * (L.timeStep * L.spaceStep))
                  = ((L.Nt : ℝ) * L.timeStep) * ((L.Nx : ℝ) * L.spaceStep) := by
                      simp [mul_assoc, mul_left_comm, mul_comm]
              _ = Λ.width * Λ.height := by rw [L.timeStep_mul_Nt, L.spaceStep_mul_Nx]
          rw [harea]

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

/-- The sum of all cell areas equals the area of the ambient rectangle. -/
theorem totalCellArea_eq_area (L : RectLattice Λ) :
    (∑ i : Fin L.Nt, ∑ j : Fin L.Nx, (L.cell i j).area) = Λ.area := by
  rw [Rectangle.area]
  simp_rw [cell_area_eq_timeStep_mul_spaceStep]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc
    ↑(Fintype.card (Fin L.Nt)) * (↑(Fintype.card (Fin L.Nx)) * (L.timeStep * L.spaceStep))
        = ((L.Nt : ℝ) * L.timeStep) * ((L.Nx : ℝ) * L.spaceStep) := by
            simp [mul_assoc, mul_left_comm, mul_comm]
    _ = Λ.width * Λ.height := by rw [L.timeStep_mul_Nt, L.spaceStep_mul_Nx]

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

/-- Cell-average Riemann sums coincide with the sum of exact cell integrals. -/
theorem riemannSumCellAverage_eq_totalCellIntegral
    (L : RectLattice Λ) (f : TestFun2D) :
    L.riemannSumCellAverage f = L.totalCellIntegral f := by
  unfold riemannSumCellAverage discretizeByCellAverage totalCellIntegral cellAverage
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  have hne : (L.cell i j).area ≠ 0 := (L.cell_area_pos i j).ne'
  field_simp [hne]

end RectLattice

@[simp] theorem uniformRectLattice_Nt (Λ : Rectangle) (n : ℕ) :
    (uniformRectLattice Λ n).Nt = n + 1 := rfl

@[simp] theorem uniformRectLattice_Nx (Λ : Rectangle) (n : ℕ) :
    (uniformRectLattice Λ n).Nx = n + 1 := rfl

@[simp] theorem uniformRectLattice_timeStep (Λ : Rectangle) (n : ℕ) :
    (uniformRectLattice Λ n).timeStep = Λ.width / (n + 1 : ℕ) := rfl

@[simp] theorem uniformRectLattice_spaceStep (Λ : Rectangle) (n : ℕ) :
    (uniformRectLattice Λ n).spaceStep = Λ.height / (n + 1 : ℕ) := rfl

theorem tendsto_uniformRectLattice_timeStep (Λ : Rectangle) :
    Filter.Tendsto (fun n : ℕ => (uniformRectLattice Λ n).timeStep) Filter.atTop (nhds 0) := by
  convert (tendsto_const_div_atTop_nhds_zero_nat Λ.width).comp (Filter.tendsto_add_atTop_nat 1) using 1

theorem tendsto_uniformRectLattice_spaceStep (Λ : Rectangle) :
    Filter.Tendsto (fun n : ℕ => (uniformRectLattice Λ n).spaceStep) Filter.atTop (nhds 0) := by
  convert (tendsto_const_div_atTop_nhds_zero_nat Λ.height).comp (Filter.tendsto_add_atTop_nat 1) using 1

/-- For a continuous function on a compact rectangle, the oscillation on each
mesh cell eventually becomes uniformly small under canonical uniform refinement. -/
theorem eventually_cell_anchor_oscillation_lt_of_continuousOn
    (Λ : Rectangle) {f : Spacetime2D → ℝ}
    (hK : IsCompact Λ.toSet) (hcont : ContinuousOn f Λ.toSet)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N,
      ∀ (i : Fin (uniformRectLattice Λ n).Nt) (j : Fin (uniformRectLattice Λ n).Nx)
        {x : Spacetime2D},
        x ∈ ((uniformRectLattice Λ n).cell i j).toSet →
        |f x - f ((uniformRectLattice Λ n).cellAnchor i j)| < ε := by
  have huc : UniformContinuousOn f Λ.toSet := hK.uniformContinuousOn_of_continuous hcont
  rw [Metric.uniformContinuousOn_iff] at huc
  rcases huc ε hε with ⟨δ, hδpos, hδ⟩
  have hstep :
      Filter.Tendsto
        (fun n : ℕ => (uniformRectLattice Λ n).timeStep + (uniformRectLattice Λ n).spaceStep)
        Filter.atTop (nhds 0) := by
    simpa [zero_add] using
      (tendsto_uniformRectLattice_timeStep Λ).add (tendsto_uniformRectLattice_spaceStep Λ)
  have hsmall : ∀ᶠ n : ℕ in Filter.atTop,
      (uniformRectLattice Λ n).timeStep + (uniformRectLattice Λ n).spaceStep < δ :=
    hstep (Iio_mem_nhds hδpos)
  rcases Filter.eventually_atTop.mp hsmall with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn i j x hx
  have hxΛ : x ∈ Λ.toSet :=
    RectLattice.cell_subset_rect (L := uniformRectLattice Λ n) i j hx
  have haΛ : (uniformRectLattice Λ n).cellAnchor i j ∈ Λ.toSet :=
    RectLattice.cell_subset_rect (L := uniformRectLattice Λ n) i j
      ((uniformRectLattice Λ n).cellAnchor_mem_cell i j)
  have hdist : dist x ((uniformRectLattice Λ n).cellAnchor i j) < δ := by
    have hle :=
      RectLattice.dist_cellAnchor_le_timeStep_add_spaceStep
        (L := uniformRectLattice Λ n) (i := i) (j := j) hx
    exact lt_of_le_of_lt hle (hN n hn)
  have := hδ x hxΛ ((uniformRectLattice Λ n).cellAnchor i j) haΛ hdist
  simpa [Real.dist_eq, abs_sub_comm] using this

/-- Cell-anchor Riemann sums along the canonical uniform refinement converge to
the set integral over the rectangle for continuous functions. -/
theorem tendsto_riemannSumCellAnchorFun_of_continuousOn
    (Λ : Rectangle) {f : Spacetime2D → ℝ}
    (hK : IsCompact Λ.toSet)
    (hcont : ContinuousOn f Λ.toSet) :
    IntegrableOn f Λ.toSet volume →
    Filter.Tendsto
      (fun n : ℕ => (uniformRectLattice Λ n).riemannSumCellAnchorFun f)
      Filter.atTop
      (nhds (∫ x in Λ.toSet, f x)) := by
  intro hint
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  let η : ℝ := ε / (2 * Λ.area)
  have hη : 0 < η := by
    unfold η
    exact div_pos hε (mul_pos (by norm_num) Λ.area_pos)
  rcases eventually_cell_anchor_oscillation_lt_of_continuousOn
      Λ hK hcont hη with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  let L := uniformRectLattice Λ n
  have hcell_int : ∀ i j, IntegrableOn f (L.cell i j).toSet volume := by
    intro i j
    exact hint.mono_set (fun x hx => RectLattice.cell_subset_rect (L := L) i j hx)
  have herror :=
    L.riemannSumCellAnchorFun_sub_cellIntegral_sum_abs_le
      hcell_int
      (fun i j x hx => (le_of_lt (hN n hn i j hx)))
  have hsum := L.sum_cellIntegral_eq_setIntegral hint
  have hη_area : η * Λ.area = ε / 2 := by
    unfold η
    field_simp [Λ.area_pos.ne']
  have habs :
      |L.riemannSumCellAnchorFun f - ∫ x in Λ.toSet, f x| < ε := by
    calc
      |L.riemannSumCellAnchorFun f - ∫ x in Λ.toSet, f x|
          = |L.riemannSumCellAnchorFun f
              - ∑ i : Fin L.Nt, ∑ j : Fin L.Nx, ∫ x in (L.cell i j).toSet, f x| := by
                rw [hsum]
      _ ≤ η * Λ.area := herror
      _ = ε / 2 := hη_area
      _ < ε := by linarith
  simpa [Real.dist_eq, L] using habs

end Phi4

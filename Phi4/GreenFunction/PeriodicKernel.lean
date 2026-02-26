/- 
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.FreeField

/-!
# Periodic Image-Sum Kernel Infrastructure

This file develops concrete method-of-images infrastructure for periodic
boundary kernels on rectangles/tori:

* periodic lattice shifts `periodicShift` and translated points `shiftPoint`,
* finite index windows `periodicIndexFinset`,
* truncated periodic image sums `periodicKernelTrunc`.

These definitions are mathematically sound and physically motivated:
the periodic Green kernel on a torus is represented by summing free-space
propagators over lattice images.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Phi4

/-- Periodic lattice shift vector with periods `L₁`, `L₂` and indices `(m,n)`. -/
def periodicShift (L₁ L₂ : ℝ) (m n : ℤ) : Spacetime2D :=
  EuclideanSpace.equiv (Fin 2) ℝ |>.symm
    (fun i => if i = 0 then (m : ℝ) * L₁ else (n : ℝ) * L₂)

@[simp] theorem periodicShift_apply (L₁ L₂ : ℝ) (m n : ℤ) (i : Fin 2) :
    periodicShift L₁ L₂ m n i = if i = 0 then (m : ℝ) * L₁ else (n : ℝ) * L₂ := by
  simp [periodicShift]

/-- Translate a spacetime point by a periodic lattice shift. -/
def shiftPoint (L₁ L₂ : ℝ) (m n : ℤ) (x : Spacetime2D) : Spacetime2D :=
  x + periodicShift L₁ L₂ m n

@[simp] theorem shiftPoint_apply (L₁ L₂ : ℝ) (m n : ℤ) (x : Spacetime2D) (i : Fin 2) :
    shiftPoint L₁ L₂ m n x i =
      x i + (if i = 0 then (m : ℝ) * L₁ else (n : ℝ) * L₂) := by
  simp [shiftPoint, periodicShift]

@[simp] theorem shiftPoint_zero_zero (L₁ L₂ : ℝ) (x : Spacetime2D) :
    shiftPoint L₁ L₂ 0 0 x = x := by
  ext i
  simp [shiftPoint, periodicShift]

@[simp] theorem shiftPoint_sub (L₁ L₂ : ℝ) (m n : ℤ) (x y : Spacetime2D) :
    shiftPoint L₁ L₂ m n x - shiftPoint L₁ L₂ m n y = x - y := by
  simp [shiftPoint, sub_eq_add_neg, add_assoc, add_comm]

theorem periodicShift_add_indices (L₁ L₂ : ℝ)
    (m₁ m₂ n₁ n₂ : ℤ) :
    periodicShift L₁ L₂ (m₁ + m₂) (n₁ + n₂) =
      periodicShift L₁ L₂ m₁ n₁ + periodicShift L₁ L₂ m₂ n₂ := by
  ext i
  by_cases hi : i = 0
  · simp [periodicShift, hi, add_mul]
  · simp [periodicShift, hi, add_mul]

theorem shiftPoint_add_indices (L₁ L₂ : ℝ)
    (m₁ m₂ n₁ n₂ : ℤ) (x : Spacetime2D) :
    shiftPoint L₁ L₂ (m₁ + m₂) (n₁ + n₂) x =
      shiftPoint L₁ L₂ m₁ n₁ (shiftPoint L₁ L₂ m₂ n₂ x) := by
  unfold shiftPoint
  rw [periodicShift_add_indices]
  abel

/-- Composition of two lattice shifts commutes (addition in `ℤ²` is abelian). -/
theorem shiftPoint_comm_indices (L₁ L₂ : ℝ)
    (m n a b : ℤ) (x : Spacetime2D) :
    shiftPoint L₁ L₂ m n (shiftPoint L₁ L₂ a b x) =
      shiftPoint L₁ L₂ a b (shiftPoint L₁ L₂ m n x) := by
  calc
    shiftPoint L₁ L₂ m n (shiftPoint L₁ L₂ a b x)
        = shiftPoint L₁ L₂ (m + a) (n + b) x := by
          simpa using (shiftPoint_add_indices L₁ L₂ m a n b x).symm
    _ = shiftPoint L₁ L₂ (a + m) (b + n) x := by
          simp [add_comm]
    _ = shiftPoint L₁ L₂ a b (shiftPoint L₁ L₂ m n x) := by
          simpa using (shiftPoint_add_indices L₁ L₂ a m b n x)

@[simp] theorem shiftPoint_neg_cancel (L₁ L₂ : ℝ) (m n : ℤ) (x : Spacetime2D) :
    shiftPoint L₁ L₂ m n (shiftPoint L₁ L₂ (-m) (-n) x) = x := by
  simpa using (shiftPoint_add_indices L₁ L₂ m (-m) n (-n) x).symm

@[simp] theorem shiftPoint_neg_cancel' (L₁ L₂ : ℝ) (m n : ℤ) (x : Spacetime2D) :
    shiftPoint L₁ L₂ (-m) (-n) (shiftPoint L₁ L₂ m n x) = x := by
  simpa [add_comm] using (shiftPoint_add_indices L₁ L₂ (-m) m (-n) n x).symm

/-- Free covariance is invariant under simultaneous periodic lattice translation
    of both arguments. -/
theorem freeCovKernel_shift_both (mass L₁ L₂ : ℝ)
    (m n : ℤ) (x y : Spacetime2D) :
    freeCovKernel mass (shiftPoint L₁ L₂ m n x) (shiftPoint L₁ L₂ m n y) =
      freeCovKernel mass x y := by
  simp [freeCovKernel]

/-- Shift-transfer identity: moving the image shift from the second argument to
    the first argument with opposite sign. -/
theorem freeCovKernel_shift_transfer (mass L₁ L₂ : ℝ)
    (m n : ℤ) (x y : Spacetime2D) :
    freeCovKernel mass x (shiftPoint L₁ L₂ m n y) =
      freeCovKernel mass (shiftPoint L₁ L₂ (-m) (-n) x) y := by
  have h := freeCovKernel_shift_both mass L₁ L₂ m n
    (shiftPoint L₁ L₂ (-m) (-n) x) y
  simpa using h

/-- Finite index set `{-N, ..., N}` used in truncated periodic image sums. -/
def periodicIndexFinset (N : ℕ) : Finset ℤ :=
  Finset.Icc (-(N : ℤ)) (N : ℤ)

@[simp] theorem periodicIndexFinset_zero : periodicIndexFinset 0 = ({0} : Finset ℤ) := by
  ext z
  simp [periodicIndexFinset]

/-- The index set `{-N,...,N}` is stable under negation. -/
theorem periodicIndexFinset_neg_mem (N : ℕ) {m : ℤ}
    (hm : m ∈ periodicIndexFinset N) :
    -m ∈ periodicIndexFinset N := by
  simp [periodicIndexFinset] at hm ⊢
  omega

/-- Reindexing a sum over `{-N,...,N}` by negation. -/
theorem sum_periodicIndexFinset_comp_neg
    {α : Type*} [AddCommMonoid α] (N : ℕ) (f : ℤ → α) :
    Finset.sum (periodicIndexFinset N) (fun m => f (-m))
      = Finset.sum (periodicIndexFinset N) (fun m => f m) := by
  classical
  refine Finset.sum_bij (fun m hm => -m) ?hmem ?hinj ?hsurj ?heq
  · intro m hm
    exact periodicIndexFinset_neg_mem N hm
  · intro m₁ hm₁ m₂ hm₂ h
    exact neg_injective h
  · intro m hm
    refine ⟨-m, periodicIndexFinset_neg_mem N hm, by simp⟩
  · intro m hm
    simp

/-- One periodic image term in the method-of-images construction. -/
def periodicKernelTerm (mass L₁ L₂ : ℝ) (m n : ℤ)
    (x y : Spacetime2D) : ℝ :=
  freeCovKernel mass x (shiftPoint L₁ L₂ m n y)

/-- Symmetry of one image term under argument swap and index sign reversal. -/
theorem periodicKernelTerm_symm (mass L₁ L₂ : ℝ)
    (m n : ℤ) (x y : Spacetime2D) :
    periodicKernelTerm mass L₁ L₂ m n x y =
      periodicKernelTerm mass L₁ L₂ (-m) (-n) y x := by
  unfold periodicKernelTerm
  calc
    freeCovKernel mass x (shiftPoint L₁ L₂ m n y)
        = freeCovKernel mass (shiftPoint L₁ L₂ (-m) (-n) x) y := by
          exact freeCovKernel_shift_transfer mass L₁ L₂ m n x y
    _ = freeCovKernel mass y (shiftPoint L₁ L₂ (-m) (-n) x) := by
          exact freeCovKernel_symm mass _ _

/-- One image term is invariant under simultaneous lattice translation of both
    spacetime arguments. -/
theorem periodicKernelTerm_shift_both (mass L₁ L₂ : ℝ)
    (m n a b : ℤ) (x y : Spacetime2D) :
    periodicKernelTerm mass L₁ L₂ m n
      (shiftPoint L₁ L₂ a b x) (shiftPoint L₁ L₂ a b y)
      = periodicKernelTerm mass L₁ L₂ m n x y := by
  unfold periodicKernelTerm
  calc
    freeCovKernel mass (shiftPoint L₁ L₂ a b x)
      (shiftPoint L₁ L₂ m n (shiftPoint L₁ L₂ a b y))
        = freeCovKernel mass (shiftPoint L₁ L₂ a b x)
            (shiftPoint L₁ L₂ a b (shiftPoint L₁ L₂ m n y)) := by
              rw [shiftPoint_comm_indices]
    _ = freeCovKernel mass x (shiftPoint L₁ L₂ m n y) := by
          simpa using
            (freeCovKernel_shift_both mass L₁ L₂ a b x
              (shiftPoint L₁ L₂ m n y))

/-- Truncated periodic image kernel:
    sum over lattice shifts `(m,n) ∈ {-N,...,N}²`. -/
def periodicKernelTrunc (mass L₁ L₂ : ℝ) (N : ℕ)
    (x y : Spacetime2D) : ℝ :=
  Finset.sum (periodicIndexFinset N) (fun m =>
    Finset.sum (periodicIndexFinset N) (fun n =>
      periodicKernelTerm mass L₁ L₂ m n x y))

@[simp] theorem periodicKernelTrunc_zero (mass L₁ L₂ : ℝ) (x y : Spacetime2D) :
    periodicKernelTrunc mass L₁ L₂ 0 x y = freeCovKernel mass x y := by
  simp [periodicKernelTrunc, periodicKernelTerm]

/-- Truncated image sums are invariant under simultaneous lattice translation
    of both arguments. -/
theorem periodicKernelTrunc_shift_both (mass L₁ L₂ : ℝ) (N : ℕ)
    (a b : ℤ) (x y : Spacetime2D) :
    periodicKernelTrunc mass L₁ L₂ N
      (shiftPoint L₁ L₂ a b x) (shiftPoint L₁ L₂ a b y)
      = periodicKernelTrunc mass L₁ L₂ N x y := by
  simp [periodicKernelTrunc, periodicKernelTerm_shift_both]

/-- Symmetry of the truncated periodic image kernel. -/
theorem periodicKernelTrunc_symm (mass L₁ L₂ : ℝ) (N : ℕ)
    (x y : Spacetime2D) :
    periodicKernelTrunc mass L₁ L₂ N x y =
      periodicKernelTrunc mass L₁ L₂ N y x := by
  calc
    periodicKernelTrunc mass L₁ L₂ N x y
        = Finset.sum (periodicIndexFinset N) (fun m =>
            Finset.sum (periodicIndexFinset N) (fun n =>
              periodicKernelTerm mass L₁ L₂ m n x y)) := by
              rfl
    _ = Finset.sum (periodicIndexFinset N) (fun m =>
            Finset.sum (periodicIndexFinset N) (fun n =>
              periodicKernelTerm mass L₁ L₂ (-m) (-n) y x)) := by
            refine Finset.sum_congr rfl ?_
            intro m hm
            refine Finset.sum_congr rfl ?_
            intro n hn
            simpa using (periodicKernelTerm_symm mass L₁ L₂ m n x y)
    _ = Finset.sum (periodicIndexFinset N) (fun m =>
            Finset.sum (periodicIndexFinset N) (fun n =>
              periodicKernelTerm mass L₁ L₂ (-m) n y x)) := by
            refine Finset.sum_congr rfl ?_
            intro m hm
            simpa using
              (sum_periodicIndexFinset_comp_neg N
                (fun n => periodicKernelTerm mass L₁ L₂ (-m) n y x))
    _ = Finset.sum (periodicIndexFinset N) (fun m =>
            Finset.sum (periodicIndexFinset N) (fun n =>
              periodicKernelTerm mass L₁ L₂ m n y x)) := by
            simpa using
              (sum_periodicIndexFinset_comp_neg N
                (fun m => Finset.sum (periodicIndexFinset N)
                  (fun n => periodicKernelTerm mass L₁ L₂ m n y x)))
    _ = periodicKernelTrunc mass L₁ L₂ N y x := by
          rfl

end Phi4

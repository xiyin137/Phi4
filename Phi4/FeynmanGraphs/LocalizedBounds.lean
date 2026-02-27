/- 
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.FeynmanGraphs

/-!
# Localized Graph Bound Infrastructure

Reusable combinatorial lemmas for localized graph estimates (Glimm-Jaffe §8.5).
In particular, we record factorial product-vs-sum bounds used to control
per-cell occupancy factors in cluster/chessboard arguments.
-/

noncomputable section

open scoped BigOperators

section Factorial

variable {α : Type*}

/-- Product of factorials divides factorial of the sum. -/
theorem factorial_prod_dvd_factorial_sum (s : Finset α) (N : α → ℕ) :
    (∏ i ∈ s, Nat.factorial (N i)) ∣ Nat.factorial (∑ i ∈ s, N i) := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s ha hs
    have hmul :
        Nat.factorial (N a) * Nat.factorial (∑ i ∈ s, N i) ∣
          Nat.factorial (N a + ∑ i ∈ s, N i) :=
      Nat.factorial_mul_factorial_dvd_factorial_add (N a) (∑ i ∈ s, N i)
    have hleft :
        Nat.factorial (N a) * ∏ i ∈ s, Nat.factorial (N i) ∣
          Nat.factorial (N a) * Nat.factorial (∑ i ∈ s, N i) :=
      Nat.mul_dvd_mul_left (Nat.factorial (N a)) hs
    exact dvd_trans (by simpa [Finset.prod_insert, ha] using hleft)
      (by simpa [Finset.sum_insert, ha] using hmul)

/-- Product of factorials is bounded by factorial of the sum. -/
theorem factorial_prod_le_factorial_sum (s : Finset α) (N : α → ℕ) :
    (∏ i ∈ s, Nat.factorial (N i)) ≤ Nat.factorial (∑ i ∈ s, N i) := by
  exact Nat.le_of_dvd (Nat.factorial_pos _) (factorial_prod_dvd_factorial_sum s N)

/-- Real-cast variant of `factorial_prod_le_factorial_sum`. -/
theorem factorial_prod_le_factorial_sum_real (s : Finset α) (N : α → ℕ) :
    (∏ i ∈ s, (Nat.factorial (N i) : ℝ)) ≤
      (Nat.factorial (∑ i ∈ s, N i) : ℝ) := by
  exact_mod_cast factorial_prod_le_factorial_sum (s := s) N

/-- Factorized form of weighted factorial occupancy products:
    factorial factors times per-cell powers combine into a global power
    of the total occupancy. -/
theorem factorial_weighted_prod_eq (s : Finset α) (N : α → ℕ) (A : ℝ) :
    (∏ i ∈ s, (Nat.factorial (N i) : ℝ) * A ^ (N i)) =
      (∏ i ∈ s, (Nat.factorial (N i) : ℝ)) * A ^ (∑ i ∈ s, N i) := by
  calc
    (∏ i ∈ s, (Nat.factorial (N i) : ℝ) * A ^ (N i))
        = (∏ i ∈ s, (Nat.factorial (N i) : ℝ)) * (∏ i ∈ s, A ^ (N i)) := by
          simp [Finset.prod_mul_distrib]
    _ = (∏ i ∈ s, (Nat.factorial (N i) : ℝ)) * A ^ (∑ i ∈ s, N i) := by
          simp [Finset.prod_pow_eq_pow_sum]

/-- Weighted factorial occupancy control:
    `∏ (N(i)! * A^{N(i)}) ≤ (∑ N(i))! * A^{∑ N(i)}` for `A ≥ 0`. -/
theorem factorial_weighted_prod_le_factorial_sum_pow
    (s : Finset α) (N : α → ℕ) (A : ℝ) (hA : 0 ≤ A) :
    (∏ i ∈ s, (Nat.factorial (N i) : ℝ) * A ^ (N i)) ≤
      (Nat.factorial (∑ i ∈ s, N i) : ℝ) * A ^ (∑ i ∈ s, N i) := by
  rw [factorial_weighted_prod_eq]
  exact mul_le_mul_of_nonneg_right
    (factorial_prod_le_factorial_sum_real (s := s) N)
    (pow_nonneg hA _)

end Factorial

section GraphSpecialized

/-- Graph-specialized factorial occupancy bound at vertices. -/
theorem graph_vertex_factorial_prod_le_total_factorial {r : ℕ} (G : FeynmanGraph r) :
    (∏ v : Fin r, Nat.factorial (G.legs v)) ≤
      Nat.factorial (∑ v : Fin r, G.legs v) := by
  simpa using
    factorial_prod_le_factorial_sum (s := (Finset.univ : Finset (Fin r))) G.legs

/-- Real-cast graph-specialized factorial occupancy bound at vertices. -/
theorem graph_vertex_factorial_prod_le_total_factorial_real {r : ℕ} (G : FeynmanGraph r) :
    (∏ v : Fin r, (Nat.factorial (G.legs v) : ℝ)) ≤
      (Nat.factorial (∑ v : Fin r, G.legs v) : ℝ) := by
  exact_mod_cast graph_vertex_factorial_prod_le_total_factorial G

/-- Graph-specialized factorization of weighted vertex occupancy products. -/
theorem graph_vertex_factorial_weighted_prod_eq
    {r : ℕ} (G : FeynmanGraph r) (A : ℝ) :
    (∏ v : Fin r, (Nat.factorial (G.legs v) : ℝ) * A ^ (G.legs v)) =
      (∏ v : Fin r, (Nat.factorial (G.legs v) : ℝ)) *
        A ^ (∑ v : Fin r, G.legs v) := by
  simpa using factorial_weighted_prod_eq
    (s := (Finset.univ : Finset (Fin r))) (N := G.legs) A

/-- Graph-specialized weighted factorial occupancy bound. -/
theorem graph_vertex_factorial_weighted_prod_le_total_factorial_pow
    {r : ℕ} (G : FeynmanGraph r) (A : ℝ) (hA : 0 ≤ A) :
    (∏ v : Fin r, (Nat.factorial (G.legs v) : ℝ) * A ^ (G.legs v)) ≤
      (Nat.factorial (∑ v : Fin r, G.legs v) : ℝ) *
        A ^ (∑ v : Fin r, G.legs v) := by
  simpa using factorial_weighted_prod_le_factorial_sum_pow
    (s := (Finset.univ : Finset (Fin r))) (N := G.legs) A hA

end GraphSpecialized

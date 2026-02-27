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

variable {α : Type*} [DecidableEq α]

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

end GraphSpecialized

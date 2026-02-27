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

section GraphCounting

namespace FeynmanGraph

variable {r : ℕ}

/-- The finite type of all valid legs of a graph. -/
abbrev LegIdx (G : FeynmanGraph r) := Σ v : Fin r, Fin (G.legs v)

/-- Forgetful projection from valid legs to raw `(vertex, leg)` indices. -/
def legRaw {G : FeynmanGraph r} (i : G.LegIdx) : Fin r × ℕ :=
  (i.1, i.2.1)

private theorem legRaw_injective (G : FeynmanGraph r) :
    Function.Injective (legRaw (G := G)) := by
  intro i j hij
  cases i with
  | mk vi li =>
    cases j with
    | mk vj lj =>
      simp [legRaw] at hij
      rcases hij with ⟨hv, hl⟩
      subst hv
      have hfin : li = lj := Fin.ext hl
      subst hfin
      rfl

private def coveringLine (G : FeynmanGraph r) (i : G.LegIdx) :
    ((Fin r × ℕ) × (Fin r × ℕ)) :=
  Classical.choose (ExistsUnique.exists (G.covering i.1 i.2.1 i.2.2))

private theorem coveringLine_mem (G : FeynmanGraph r) (i : G.LegIdx) :
    coveringLine G i ∈ G.lines := by
  exact (Classical.choose_spec (ExistsUnique.exists (G.covering i.1 i.2.1 i.2.2))).1

private theorem coveringLine_contains (G : FeynmanGraph r) (i : G.LegIdx) :
    (coveringLine G i).1 = legRaw i ∨ (coveringLine G i).2 = legRaw i := by
  exact (Classical.choose_spec (ExistsUnique.exists (G.covering i.1 i.2.1 i.2.2))).2

private theorem coveringLine_eq_of_mem_contains
    (G : FeynmanGraph r) (i : G.LegIdx)
    (p : (Fin r × ℕ) × (Fin r × ℕ))
    (hpMem : p ∈ G.lines) (hpContains : p.1 = legRaw i ∨ p.2 = legRaw i) :
    coveringLine G i = p := by
  have hchosen :
      coveringLine G i ∈ G.lines ∧
        ((coveringLine G i).1 = legRaw i ∨ (coveringLine G i).2 = legRaw i) :=
    Classical.choose_spec (ExistsUnique.exists (G.covering i.1 i.2.1 i.2.2))
  exact ExistsUnique.unique (G.covering i.1 i.2.1 i.2.2) hchosen ⟨hpMem, hpContains⟩

/-- Graph line counting identity: each line has two endpoints and each valid leg
    appears in exactly one line, so `2 * |lines| = Σ_v legs(v)`. -/
theorem two_mul_lines_card_eq_total_legs (G : FeynmanGraph r) :
    2 * G.lines.card = ∑ v : Fin r, G.legs v := by
  classical
  have hMaps :
      ((Finset.univ : Finset G.LegIdx) : Set G.LegIdx).MapsTo
        (coveringLine G) (G.lines : Set ((Fin r × ℕ) × (Fin r × ℕ))) := by
    intro i hi
    exact coveringLine_mem G i
  have hCount := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset G.LegIdx))
    (t := G.lines)
    (f := coveringLine G)
    hMaps
  have hFiber : ∀ p ∈ G.lines,
      ({i : G.LegIdx | coveringLine G i = p} : Finset G.LegIdx).card = 2 := by
    intro p hp
    let i₁ : G.LegIdx := ⟨p.1.1, ⟨p.1.2, (G.line_valid p hp).1⟩⟩
    let i₂ : G.LegIdx := ⟨p.2.1, ⟨p.2.2, (G.line_valid p hp).2⟩⟩
    have hi₁_raw : legRaw i₁ = p.1 := by simp [legRaw, i₁]
    have hi₂_raw : legRaw i₂ = p.2 := by simp [legRaw, i₂]
    have hi₁_mem :
        i₁ ∈ ({i : G.LegIdx | coveringLine G i = p} : Finset G.LegIdx) := by
      have : coveringLine G i₁ = p :=
        coveringLine_eq_of_mem_contains G i₁ p hp (Or.inl hi₁_raw.symm)
      simp [Finset.mem_filter, this]
    have hi₂_mem :
        i₂ ∈ ({i : G.LegIdx | coveringLine G i = p} : Finset G.LegIdx) := by
      have : coveringLine G i₂ = p :=
        coveringLine_eq_of_mem_contains G i₂ p hp (Or.inr hi₂_raw.symm)
      simp [Finset.mem_filter, this]
    have hpne : p.1 ≠ p.2 := ne_of_lt (G.ordered p hp)
    have hi₁_ne_i₂ : i₁ ≠ i₂ := by
      intro h
      apply hpne
      have hraw : legRaw i₁ = legRaw i₂ := congrArg (legRaw (G := G)) h
      calc
        p.1 = legRaw i₁ := hi₁_raw.symm
        _ = legRaw i₂ := hraw
        _ = p.2 := hi₂_raw
    have hsubset :
        ({i : G.LegIdx | coveringLine G i = p} : Finset G.LegIdx) ⊆ ({i₁, i₂} : Finset G.LegIdx) := by
      intro i hi
      have hEq : coveringLine G i = p := by
        simpa [Finset.mem_filter] using hi
      have hcontains : p.1 = legRaw i ∨ p.2 = legRaw i := by
        simpa [hEq] using (coveringLine_contains G i)
      rcases hcontains with hleft | hright
      · have : i = i₁ := by
          apply (legRaw_injective G)
          exact hleft.symm.trans hi₁_raw.symm
        simp [this]
      · have : i = i₂ := by
          apply (legRaw_injective G)
          exact hright.symm.trans hi₂_raw.symm
        simp [this]
    have hpair_subset :
        ({i₁, i₂} : Finset G.LegIdx) ⊆
          ({i : G.LegIdx | coveringLine G i = p} : Finset G.LegIdx) := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact hi₁_mem
      · exact hi₂_mem
    have hcard_ge : 2 ≤ ({i : G.LegIdx | coveringLine G i = p} : Finset G.LegIdx).card := by
      calc
        2 = ({i₁, i₂} : Finset G.LegIdx).card := (Finset.card_pair hi₁_ne_i₂).symm
        _ ≤ ({i : G.LegIdx | coveringLine G i = p} : Finset G.LegIdx).card :=
          Finset.card_le_card hpair_subset
    have hcard_le :
        ({i : G.LegIdx | coveringLine G i = p} : Finset G.LegIdx).card ≤ 2 := by
      calc
        ({i : G.LegIdx | coveringLine G i = p} : Finset G.LegIdx).card
            ≤ ({i₁, i₂} : Finset G.LegIdx).card := Finset.card_le_card hsubset
        _ = 2 := Finset.card_pair hi₁_ne_i₂
    exact le_antisymm hcard_le hcard_ge
  have hCount2 : Fintype.card G.LegIdx = ∑ b ∈ G.lines, 2 := by
    calc
      Fintype.card G.LegIdx
          = ∑ b ∈ G.lines, ({a : G.LegIdx | coveringLine G a = b} : Finset G.LegIdx).card := by
            simpa using hCount
      _ = ∑ b ∈ G.lines, 2 := by
            refine Finset.sum_congr rfl ?_
            intro b hb
            exact hFiber b hb
  have hLegCard : Fintype.card G.LegIdx = ∑ v : Fin r, G.legs v := by
    simp [LegIdx]
  calc
    2 * G.lines.card = ∑ b ∈ G.lines, 2 := by
      simp [Nat.mul_comm]
    _ = Fintype.card G.LegIdx := by
      exact hCount2.symm
    _ = ∑ v : Fin r, G.legs v := hLegCard

/-- Equivalent form of `two_mul_lines_card_eq_total_legs`. -/
theorem total_legs_eq_two_mul_lines_card (G : FeynmanGraph r) :
    (∑ v : Fin r, G.legs v) = 2 * G.lines.card := by
  simpa [Nat.mul_comm] using (two_mul_lines_card_eq_total_legs G).symm

/-- The total number of legs is even. -/
theorem total_legs_even (G : FeynmanGraph r) :
    Even (∑ v : Fin r, G.legs v) := by
  refine ⟨G.lines.card, ?_⟩
  simpa [two_mul] using total_legs_eq_two_mul_lines_card G

/-- Number of lines is half the total number of legs. -/
theorem lines_card_eq_total_legs_half (G : FeynmanGraph r) :
    G.lines.card = (∑ v : Fin r, G.legs v) / 2 := by
  calc
    G.lines.card = (2 * G.lines.card) / 2 := by simp
    _ = (∑ v : Fin r, G.legs v) / 2 := by
      simp [two_mul_lines_card_eq_total_legs G]

end FeynmanGraph

end GraphCounting

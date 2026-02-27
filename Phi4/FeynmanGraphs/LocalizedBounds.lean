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

section GraphLineSpecialized

namespace FeynmanGraph

variable {r : ℕ}

/-- Rewrite powers indexed by total vertex legs as powers indexed by line count. -/
theorem total_legs_pow_eq_pow_lines (G : FeynmanGraph r) (A : ℝ) :
    A ^ (∑ v : Fin r, G.legs v) = (A ^ 2) ^ G.lines.card := by
  calc
    A ^ (∑ v : Fin r, G.legs v) = A ^ (2 * G.lines.card) := by
      simp [total_legs_eq_two_mul_lines_card (G := G)]
    _ = (A ^ 2) ^ G.lines.card := by
      simp [pow_mul]

/-- Vertex factorial product bound rewritten with line count. -/
theorem vertex_factorial_prod_le_factorial_two_mul_lines_card
    (G : FeynmanGraph r) :
    (∏ v : Fin r, Nat.factorial (G.legs v)) ≤
      Nat.factorial (2 * G.lines.card) := by
  calc
    (∏ v : Fin r, Nat.factorial (G.legs v))
        ≤ Nat.factorial (∑ v : Fin r, G.legs v) :=
          graph_vertex_factorial_prod_le_total_factorial G
    _ = Nat.factorial (2 * G.lines.card) := by
          simp [total_legs_eq_two_mul_lines_card (G := G)]

/-- Real-cast line-count form of the vertex factorial product bound. -/
theorem vertex_factorial_prod_le_factorial_two_mul_lines_card_real
    (G : FeynmanGraph r) :
    (∏ v : Fin r, (Nat.factorial (G.legs v) : ℝ)) ≤
      (Nat.factorial (2 * G.lines.card) : ℝ) := by
  exact_mod_cast vertex_factorial_prod_le_factorial_two_mul_lines_card (G := G)

/-- Weighted vertex occupancy bound rewritten entirely in line-count form. -/
theorem vertex_factorial_weighted_prod_le_total_factorial_pow_lines
    (G : FeynmanGraph r) (A : ℝ) (hA : 0 ≤ A) :
    (∏ v : Fin r, (Nat.factorial (G.legs v) : ℝ) * A ^ (G.legs v)) ≤
      (Nat.factorial (2 * G.lines.card) : ℝ) * (A ^ 2) ^ G.lines.card := by
  calc
    (∏ v : Fin r, (Nat.factorial (G.legs v) : ℝ) * A ^ (G.legs v))
        ≤ (Nat.factorial (∑ v : Fin r, G.legs v) : ℝ) *
            A ^ (∑ v : Fin r, G.legs v) :=
          graph_vertex_factorial_weighted_prod_le_total_factorial_pow
            (G := G) A hA
    _ = (Nat.factorial (2 * G.lines.card) : ℝ) * A ^ (∑ v : Fin r, G.legs v) := by
          simp [total_legs_eq_two_mul_lines_card (G := G)]
    _ = (Nat.factorial (2 * G.lines.card) : ℝ) * (A ^ 2) ^ G.lines.card := by
          simp [total_legs_pow_eq_pow_lines (G := G)]

end FeynmanGraph

end GraphLineSpecialized

section DegreeBound

namespace FeynmanGraph

variable {r : ℕ}

private theorem factorial_le_pow_factorial_of_le
    {k d : ℕ} (hk : k ≤ d) :
    Nat.factorial k ≤ (Nat.factorial d) ^ k := by
  cases k with
  | zero =>
      simp
  | succ n =>
      have hmono : Nat.factorial (n + 1) ≤ Nat.factorial d :=
        Nat.factorial_le hk
      have hbase : 1 ≤ Nat.factorial d := Nat.succ_le_of_lt (Nat.factorial_pos d)
      have hpow :
          Nat.factorial d ≤ (Nat.factorial d) ^ (n + 1) := by
        calc
          Nat.factorial d = Nat.factorial d * 1 := by simp
          _ ≤ Nat.factorial d * (Nat.factorial d) ^ n := by
                gcongr
                exact one_le_pow_of_one_le' hbase n
          _ = (Nat.factorial d) ^ (n + 1) := by
                simp [pow_succ, Nat.mul_comm]
      exact hmono.trans hpow

/-- With a uniform leg bound `legs(v) ≤ d`, vertex factorial products are
    bounded by a pure power with exponent `Σ legs(v)`. -/
theorem vertex_factorial_prod_le_degree_factorial_pow_total_legs
    (G : FeynmanGraph r) (d : ℕ) (hdeg : ∀ v : Fin r, G.legs v ≤ d) :
    (∏ v : Fin r, Nat.factorial (G.legs v)) ≤
      (Nat.factorial d) ^ (∑ v : Fin r, G.legs v) := by
  have hpoint :
      ∀ v : Fin r, Nat.factorial (G.legs v) ≤ (Nat.factorial d) ^ (G.legs v) := by
    intro v
    exact factorial_le_pow_factorial_of_le (hdeg v)
  calc
    (∏ v : Fin r, Nat.factorial (G.legs v))
        ≤ ∏ v : Fin r, (Nat.factorial d) ^ (G.legs v) := by
          exact Finset.prod_le_prod' (fun v _ => hpoint v)
    _ = (Nat.factorial d) ^ (∑ v : Fin r, G.legs v) := by
          simp [Finset.prod_pow_eq_pow_sum]

/-- Degree-bounded vertex factorial control rewritten in pure line-count form. -/
theorem vertex_factorial_prod_le_degree_factorial_pow_lines
    (G : FeynmanGraph r) (d : ℕ) (hdeg : ∀ v : Fin r, G.legs v ≤ d) :
    (∏ v : Fin r, Nat.factorial (G.legs v)) ≤
      ((Nat.factorial d) ^ 2) ^ G.lines.card := by
  calc
    (∏ v : Fin r, Nat.factorial (G.legs v))
        ≤ (Nat.factorial d) ^ (∑ v : Fin r, G.legs v) :=
          vertex_factorial_prod_le_degree_factorial_pow_total_legs G d hdeg
    _ = (Nat.factorial d) ^ (2 * G.lines.card) := by
          simp [total_legs_eq_two_mul_lines_card (G := G)]
    _ = ((Nat.factorial d) ^ 2) ^ G.lines.card := by
          simp [pow_mul]

/-- Real-cast variant of `vertex_factorial_prod_le_degree_factorial_pow_lines`. -/
theorem vertex_factorial_prod_le_degree_factorial_pow_lines_real
    (G : FeynmanGraph r) (d : ℕ) (hdeg : ∀ v : Fin r, G.legs v ≤ d) :
    (∏ v : Fin r, (Nat.factorial (G.legs v) : ℝ)) ≤
      (((Nat.factorial d : ℝ) ^ 2) ^ G.lines.card) := by
  exact_mod_cast vertex_factorial_prod_le_degree_factorial_pow_lines G d hdeg

end FeynmanGraph

end DegreeBound

section DegreeWeighted

namespace FeynmanGraph

variable {r : ℕ}

/-- Degree-capped weighted occupancy control in pure line-count form:
    under `legs(v) ≤ d` and `A ≥ 0`, the product
    `∏ (legs(v)! * A^{legs(v)})` is bounded by
    `(((d!)^2) * A^2)^{|lines|}`. -/
theorem vertex_factorial_weighted_prod_le_degree_const_pow_lines
    (G : FeynmanGraph r) (d : ℕ) (hdeg : ∀ v : Fin r, G.legs v ≤ d)
    (A : ℝ) (hA : 0 ≤ A) :
    (∏ v : Fin r, (Nat.factorial (G.legs v) : ℝ) * A ^ (G.legs v)) ≤
      ((((Nat.factorial d : ℝ) ^ 2) * (A ^ 2)) ^ G.lines.card) := by
  rw [graph_vertex_factorial_weighted_prod_eq (G := G) (A := A)]
  have hfac :
      (∏ v : Fin r, (Nat.factorial (G.legs v) : ℝ)) ≤
        (((Nat.factorial d : ℝ) ^ 2) ^ G.lines.card) :=
    vertex_factorial_prod_le_degree_factorial_pow_lines_real G d hdeg
  have hpow_nonneg : 0 ≤ A ^ (∑ v : Fin r, G.legs v) := pow_nonneg hA _
  have hmul :
      (∏ v : Fin r, (Nat.factorial (G.legs v) : ℝ)) * A ^ (∑ v : Fin r, G.legs v) ≤
        (((Nat.factorial d : ℝ) ^ 2) ^ G.lines.card) * A ^ (∑ v : Fin r, G.legs v) :=
    mul_le_mul_of_nonneg_right hfac hpow_nonneg
  calc
    (∏ v : Fin r, (Nat.factorial (G.legs v) : ℝ)) * A ^ (∑ v : Fin r, G.legs v)
        ≤ (((Nat.factorial d : ℝ) ^ 2) ^ G.lines.card) * A ^ (∑ v : Fin r, G.legs v) := hmul
    _ = (((Nat.factorial d : ℝ) ^ 2) ^ G.lines.card) * (A ^ 2) ^ G.lines.card := by
          simp [total_legs_pow_eq_pow_lines (G := G) (A := A)]
    _ = ((((Nat.factorial d : ℝ) ^ 2) * (A ^ 2)) ^ G.lines.card) := by
          simpa using (mul_pow ((Nat.factorial d : ℝ) ^ 2) (A ^ 2) G.lines.card).symm

end FeynmanGraph

end DegreeWeighted

section DegreeCardinality

namespace FeynmanGraph

variable {r : ℕ}

/-- A uniform degree cap controls total leg count by `|V| * d`. -/
theorem total_legs_le_mul_card_of_degree_le
    (G : FeynmanGraph r) (d : ℕ) (hdeg : ∀ v : Fin r, G.legs v ≤ d) :
    (∑ v : Fin r, G.legs v) ≤ r * d := by
  have hsum : (∑ v : Fin r, G.legs v) ≤ ∑ v : Fin r, d := by
    exact Finset.sum_le_sum (fun v _ => hdeg v)
  simpa using hsum

/-- Under a uniform degree cap, doubled line count is bounded by `|V| * d`. -/
theorem two_mul_lines_card_le_mul_card_of_degree_le
    (G : FeynmanGraph r) (d : ℕ) (hdeg : ∀ v : Fin r, G.legs v ≤ d) :
    2 * G.lines.card ≤ r * d := by
  calc
    2 * G.lines.card = ∑ v : Fin r, G.legs v := two_mul_lines_card_eq_total_legs G
    _ ≤ r * d := total_legs_le_mul_card_of_degree_le G d hdeg

end FeynmanGraph

end DegreeCardinality

section ConstantValence

namespace FeynmanGraph

variable {r : ℕ}

/-- Constant valence `d` gives exact total leg count `|V| * d`. -/
theorem total_legs_eq_mul_card_of_const_legs
    (G : FeynmanGraph r) (d : ℕ) (hconst : ∀ v : Fin r, G.legs v = d) :
    (∑ v : Fin r, G.legs v) = r * d := by
  simp [hconst]

/-- Constant valence `d` gives exact doubled line count `|V| * d`. -/
theorem two_mul_lines_card_eq_mul_card_of_const_legs
    (G : FeynmanGraph r) (d : ℕ) (hconst : ∀ v : Fin r, G.legs v = d) :
    2 * G.lines.card = r * d := by
  calc
    2 * G.lines.card = ∑ v : Fin r, G.legs v := two_mul_lines_card_eq_total_legs G
    _ = r * d := total_legs_eq_mul_card_of_const_legs G d hconst

/-- If every vertex has valence `2e`, then `|lines| = |V| * e`. -/
theorem lines_card_eq_mul_card_of_const_legs_even
    (G : FeynmanGraph r) (e : ℕ) (hconst : ∀ v : Fin r, G.legs v = 2 * e) :
    G.lines.card = r * e := by
  have hmul : 2 * G.lines.card = 2 * (r * e) := by
    calc
      2 * G.lines.card = r * (2 * e) :=
        two_mul_lines_card_eq_mul_card_of_const_legs G (2 * e) hconst
      _ = 2 * (r * e) := by
        simp [Nat.mul_assoc, Nat.mul_comm]
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) hmul

/-- φ⁴ valence condition (`legs(v)=4`) implies `|lines| = 2|V|`. -/
theorem lines_card_eq_two_mul_vertices_of_phi4
    (G : FeynmanGraph r) (hphi4 : ∀ v : Fin r, G.legs v = 4) :
    G.lines.card = 2 * r := by
  calc
    G.lines.card = r * 2 := by
      simpa [Nat.mul_comm] using
        lines_card_eq_mul_card_of_const_legs_even G 2 (by
          intro v
          simpa [two_mul] using hphi4 v)
    _ = 2 * r := by simp [Nat.mul_comm]

/-- φ⁴ valence condition (`legs(v)=4`) implies `2|lines| = 4|V|`. -/
theorem two_mul_lines_card_eq_four_mul_vertices_of_phi4
    (G : FeynmanGraph r) (hphi4 : ∀ v : Fin r, G.legs v = 4) :
    2 * G.lines.card = 4 * r := by
  calc
    2 * G.lines.card = r * 4 :=
      two_mul_lines_card_eq_mul_card_of_const_legs G 4 hphi4
    _ = 4 * r := by simp [Nat.mul_comm]

end FeynmanGraph

end ConstantValence

section GraphIntegralBridge

namespace FeynmanGraph

variable {r : ℕ}

/-- Bridge from weighted occupancy control to a pure `C^{|lines|}` graph-integral
    bound under a degree cap.

    This isolates the combinatorial part of localized graph bounds: once an
    analytic estimate supplies
    `|I(G)| ≤ (∏ (legs! * A^legs)) * B^{|lines|}`, the degree-capped occupancy
    lemmas collapse it to `|I(G)| ≤ C^{|lines|}`. -/
theorem graphIntegral_abs_le_const_pow_lines_of_degree_weighted_bound
    (G : FeynmanGraph r) (mass : ℝ)
    (d : ℕ) (hdeg : ∀ v : Fin r, G.legs v ≤ d)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbound :
      |graphIntegral G mass| ≤
        (∏ v : Fin r, (Nat.factorial (G.legs v) : ℝ) * A ^ (G.legs v)) *
          B ^ G.lines.card) :
    |graphIntegral G mass| ≤
      (((((Nat.factorial d : ℝ) ^ 2) * (A ^ 2)) * B) ^ G.lines.card) := by
  have hocc :
      (∏ v : Fin r, (Nat.factorial (G.legs v) : ℝ) * A ^ (G.legs v)) ≤
        ((((Nat.factorial d : ℝ) ^ 2) * (A ^ 2)) ^ G.lines.card) :=
    vertex_factorial_weighted_prod_le_degree_const_pow_lines G d hdeg A hA
  have hmul :
      (∏ v : Fin r, (Nat.factorial (G.legs v) : ℝ) * A ^ (G.legs v)) *
          B ^ G.lines.card ≤
        ((((Nat.factorial d : ℝ) ^ 2) * (A ^ 2)) ^ G.lines.card) *
          B ^ G.lines.card :=
    mul_le_mul_of_nonneg_right hocc (pow_nonneg hB _)
  calc
    |graphIntegral G mass|
        ≤ (∏ v : Fin r, (Nat.factorial (G.legs v) : ℝ) * A ^ (G.legs v)) *
            B ^ G.lines.card := hbound
    _ ≤ ((((Nat.factorial d : ℝ) ^ 2) * (A ^ 2)) ^ G.lines.card) *
          B ^ G.lines.card := hmul
    _ = (((((Nat.factorial d : ℝ) ^ 2) * (A ^ 2)) * B) ^ G.lines.card) := by
          simpa using
            (mul_pow (((Nat.factorial d : ℝ) ^ 2) * (A ^ 2)) B G.lines.card).symm

/-- Uniform positive-constant `C^{|lines|}` bound from a family-level weighted
    degree-capped estimate. -/
theorem uniform_graphIntegral_abs_le_pos_const_pow_lines_of_degree_weighted_family
    (mass : ℝ) (d : ℕ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hweighted :
      ∀ {r : ℕ} (G : FeynmanGraph r), (∀ v : Fin r, G.legs v ≤ d) →
        |graphIntegral G mass| ≤
          (∏ v : Fin r, (Nat.factorial (G.legs v) : ℝ) * A ^ (G.legs v)) *
            B ^ G.lines.card) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {r : ℕ} (G : FeynmanGraph r), (∀ v : Fin r, G.legs v ≤ d) →
        |graphIntegral G mass| ≤ C ^ G.lines.card := by
  let C0 : ℝ := (((Nat.factorial d : ℝ) ^ 2) * (A ^ 2)) * B
  have hfact_nonneg : 0 ≤ (Nat.factorial d : ℝ) := by
    exact_mod_cast (Nat.zero_le (Nat.factorial d))
  have hC0_nonneg : 0 ≤ C0 := by
    dsimp [C0]
    exact mul_nonneg
      (mul_nonneg (pow_nonneg hfact_nonneg 2) (pow_nonneg hA 2))
      hB
  refine ⟨C0 + 1, by linarith, ?_⟩
  intro r G hdeg
  have hbase :
      |graphIntegral G mass| ≤ C0 ^ G.lines.card := by
    have hG := hweighted G hdeg
    simpa [C0] using
      graphIntegral_abs_le_const_pow_lines_of_degree_weighted_bound
        (G := G) (mass := mass) (d := d) hdeg A B hA hB hG
  have hpow :
      C0 ^ G.lines.card ≤ (C0 + 1) ^ G.lines.card := by
    exact pow_le_pow_left₀ hC0_nonneg (le_add_of_nonneg_right zero_le_one) _
  exact hbase.trans hpow

end FeynmanGraph

end GraphIntegralBridge

section EstimateModelBridge

open MeasureTheory

/-- Global localized graph bound from weighted degree-capped family bounds
    plus a global degree cap. -/
theorem localized_graph_bound_of_degree_weighted_family
    (mass : ℝ) (d : ℕ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hweighted :
      ∀ {r : ℕ} (G : FeynmanGraph r), (∀ v : Fin r, G.legs v ≤ d) →
        |graphIntegral G mass| ≤
          (∏ v : Fin r, (Nat.factorial (G.legs v) : ℝ) * A ^ (G.legs v)) *
            B ^ G.lines.card)
    (hdegGlobal :
      ∀ {r : ℕ} (G : FeynmanGraph r), ∀ v : Fin r, G.legs v ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℕ) (G : FeynmanGraph r),
      |graphIntegral G mass| ≤ C ^ G.lines.card := by
  rcases FeynmanGraph.uniform_graphIntegral_abs_le_pos_const_pow_lines_of_degree_weighted_family
      (mass := mass) (d := d) (A := A) (B := B) hA hB hweighted with ⟨C, hCpos, hCbound⟩
  refine ⟨C, hCpos, ?_⟩
  intro r G
  exact hCbound G (hdegGlobal G)

/-- Construct `FeynmanGraphEstimateModel` from:
    1) explicit graph-expansion data,
    2) weighted degree-capped graph-integral bounds,
    3) a global degree cap. -/
theorem feynmanGraphEstimateModel_nonempty_of_expansion_and_degree_weighted
    (mass : ℝ) (hmass : 0 < mass)
    (hexpansion :
      ∀ (r : ℕ) (f : Fin r → TestFun2D),
        ∃ (graphs : Finset (FeynmanGraph r)),
          ∫ ω, (∏ i, ω (f i)) ∂(freeFieldMeasure mass hmass) =
            ∑ G ∈ graphs, graphIntegral G mass)
    (d : ℕ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hweighted :
      ∀ {r : ℕ} (G : FeynmanGraph r), (∀ v : Fin r, G.legs v ≤ d) →
        |graphIntegral G mass| ≤
          (∏ v : Fin r, (Nat.factorial (G.legs v) : ℝ) * A ^ (G.legs v)) *
            B ^ G.lines.card)
    (hdegGlobal :
      ∀ {r : ℕ} (G : FeynmanGraph r), ∀ v : Fin r, G.legs v ≤ d) :
    Nonempty (FeynmanGraphEstimateModel mass hmass) := by
  rcases localized_graph_bound_of_degree_weighted_family
      (mass := mass) (d := d) (A := A) (B := B) hA hB hweighted hdegGlobal with
    ⟨C, hCpos, hCbound⟩
  exact ⟨{
    feynman_graph_expansion := hexpansion
    localized_graph_bound := ⟨C, hCpos, hCbound⟩
  }⟩

end EstimateModelBridge

section Phi4Specialization

open MeasureTheory
namespace FeynmanGraph

variable {r : ℕ}

/-- Local φ⁴ specialization for a single graph:
    if `legs(v)=4` for this graph and a weighted bound is available, then
    `|I(G)| ≤ C^{|lines|}` with explicit `C` from the degree-4 bridge. -/
theorem graphIntegral_abs_le_const_pow_lines_of_phi4_weighted_bound
    (G : FeynmanGraph r) (mass : ℝ)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hphi4 : ∀ v : Fin r, G.legs v = 4)
    (hbound :
      |graphIntegral G mass| ≤
        (∏ v : Fin r, (Nat.factorial (G.legs v) : ℝ) * A ^ (G.legs v)) *
          B ^ G.lines.card) :
    |graphIntegral G mass| ≤
      (((((Nat.factorial 4 : ℝ) ^ 2) * (A ^ 2)) * B) ^ G.lines.card) := by
  have hdeg : ∀ v : Fin r, G.legs v ≤ 4 := by
    intro v
    simp [hphi4 v]
  exact graphIntegral_abs_le_const_pow_lines_of_degree_weighted_bound
    (G := G) (mass := mass) (d := 4) hdeg A B hA hB hbound

/-- Family-level local φ⁴ specialization:
    weighted bounds for each valence-4 graph imply a uniform positive
    `C^{|lines|}` control on all such graphs. -/
theorem uniform_graphIntegral_abs_le_pos_const_pow_lines_of_phi4_weighted_family_local
    (mass : ℝ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hweighted :
      ∀ {r : ℕ} (G : FeynmanGraph r), (∀ v : Fin r, G.legs v = 4) →
        |graphIntegral G mass| ≤
          (∏ v : Fin r, (Nat.factorial (G.legs v) : ℝ) * A ^ (G.legs v)) *
            B ^ G.lines.card) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {r : ℕ} (G : FeynmanGraph r), (∀ v : Fin r, G.legs v = 4) →
        |graphIntegral G mass| ≤ C ^ G.lines.card := by
  let C0 : ℝ := (((Nat.factorial 4 : ℝ) ^ 2) * (A ^ 2)) * B
  have hfact_nonneg : 0 ≤ (Nat.factorial 4 : ℝ) := by
    exact_mod_cast (Nat.zero_le (Nat.factorial 4))
  have hC0_nonneg : 0 ≤ C0 := by
    dsimp [C0]
    exact mul_nonneg
      (mul_nonneg (pow_nonneg hfact_nonneg 2) (pow_nonneg hA 2))
      hB
  refine ⟨C0 + 1, by linarith, ?_⟩
  intro r G hphi4
  have hbase : |graphIntegral G mass| ≤ C0 ^ G.lines.card := by
    have hG := hweighted G hphi4
    simpa [C0] using
      graphIntegral_abs_le_const_pow_lines_of_phi4_weighted_bound
        (G := G) (mass := mass) (A := A) (B := B) hA hB hphi4 hG
  have hpow : C0 ^ G.lines.card ≤ (C0 + 1) ^ G.lines.card := by
    exact pow_le_pow_left₀ hC0_nonneg (le_add_of_nonneg_right zero_le_one) _
  exact hbase.trans hpow

end FeynmanGraph

namespace FeynmanGraph

variable {r : ℕ}

/-- For φ⁴ graphs, `C^{|lines|}` rewrites as `(C^2)^{|V|}`. -/
theorem pow_lines_eq_pow_vertices_of_phi4
    (G : FeynmanGraph r) (C : ℝ) (hphi4 : ∀ v : Fin r, G.legs v = 4) :
    C ^ G.lines.card = (C ^ 2) ^ r := by
  calc
    C ^ G.lines.card = C ^ (2 * r) := by
      simp [lines_card_eq_two_mul_vertices_of_phi4 (G := G) hphi4]
    _ = (C ^ 2) ^ r := by
      simp [pow_mul]

/-- Convert any line-count bound into a vertex-count bound for φ⁴ graphs. -/
theorem graphIntegral_abs_le_const_pow_vertices_of_phi4
    (G : FeynmanGraph r) (mass C : ℝ)
    (hphi4 : ∀ v : Fin r, G.legs v = 4)
    (hbound : |graphIntegral G mass| ≤ C ^ G.lines.card) :
    |graphIntegral G mass| ≤ (C ^ 2) ^ r := by
  simpa [pow_lines_eq_pow_vertices_of_phi4 (G := G) (C := C) hphi4] using hbound

/-- Weighted φ⁴ single-graph bound in vertex-count form. -/
theorem graphIntegral_abs_le_const_pow_vertices_of_phi4_weighted_bound
    (G : FeynmanGraph r) (mass : ℝ)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hphi4 : ∀ v : Fin r, G.legs v = 4)
    (hbound :
      |graphIntegral G mass| ≤
        (∏ v : Fin r, (Nat.factorial (G.legs v) : ℝ) * A ^ (G.legs v)) *
          B ^ G.lines.card) :
    |graphIntegral G mass| ≤
      ((((((Nat.factorial 4 : ℝ) ^ 2) * (A ^ 2)) * B) ^ 2) ^ r) := by
  have hlines :
      |graphIntegral G mass| ≤
        (((((Nat.factorial 4 : ℝ) ^ 2) * (A ^ 2)) * B) ^ G.lines.card) :=
    graphIntegral_abs_le_const_pow_lines_of_phi4_weighted_bound
      (G := G) (mass := mass) (A := A) (B := B) hA hB hphi4 hbound
  exact graphIntegral_abs_le_const_pow_vertices_of_phi4
    (G := G) (mass := mass)
    (C := ((((Nat.factorial 4 : ℝ) ^ 2) * (A ^ 2)) * B))
    hphi4 hlines

/-- Exact simplification of weighted vertex occupancy factors in φ⁴:
    each vertex contributes the same factor `(4! * A^4)`. -/
theorem vertex_factorial_weighted_prod_eq_const_pow_vertices_of_phi4
    (G : FeynmanGraph r) (A : ℝ)
    (hphi4 : ∀ v : Fin r, G.legs v = 4) :
    (∏ v : Fin r, (Nat.factorial (G.legs v) : ℝ) * A ^ (G.legs v)) =
      ((Nat.factorial 4 : ℝ) * A ^ 4) ^ r := by
  simp [hphi4]

/-- Sharp φ⁴ weighted bound in vertex-count form, obtained by exact
    simplification (`|lines| = 2|V|` and constant per-vertex occupancy factor). -/
theorem graphIntegral_abs_le_const_pow_vertices_of_phi4_weighted_bound_sharp
    (G : FeynmanGraph r) (mass : ℝ)
    (A B : ℝ)
    (hphi4 : ∀ v : Fin r, G.legs v = 4)
    (hbound :
      |graphIntegral G mass| ≤
        (∏ v : Fin r, (Nat.factorial (G.legs v) : ℝ) * A ^ (G.legs v)) *
          B ^ G.lines.card) :
    |graphIntegral G mass| ≤
      ((((Nat.factorial 4 : ℝ) * A ^ 4) * (B ^ 2)) ^ r) := by
  calc
    |graphIntegral G mass|
        ≤ (∏ v : Fin r, (Nat.factorial (G.legs v) : ℝ) * A ^ (G.legs v)) *
            B ^ G.lines.card := hbound
    _ = (((Nat.factorial 4 : ℝ) * A ^ 4) ^ r) * B ^ G.lines.card := by
          simp [vertex_factorial_weighted_prod_eq_const_pow_vertices_of_phi4
            (G := G) (A := A) hphi4]
    _ = (((Nat.factorial 4 : ℝ) * A ^ 4) ^ r) * B ^ (2 * r) := by
          simp [lines_card_eq_two_mul_vertices_of_phi4 (G := G) hphi4]
    _ = (((Nat.factorial 4 : ℝ) * A ^ 4) ^ r) * (B ^ 2) ^ r := by
          simp [pow_mul]
    _ = ((((Nat.factorial 4 : ℝ) * A ^ 4) * (B ^ 2)) ^ r) := by
          simpa using (mul_pow ((Nat.factorial 4 : ℝ) * A ^ 4) (B ^ 2) r).symm

/-- Uniform local φ⁴ weighted family bound in vertex-count form:
    `∃ K > 0` such that `|I(G)| ≤ K^{|V|}` for all φ⁴ graphs. -/
theorem uniform_graphIntegral_abs_le_pos_const_pow_vertices_of_phi4_weighted_family_local
    (mass : ℝ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hweighted :
      ∀ {r : ℕ} (G : FeynmanGraph r), (∀ v : Fin r, G.legs v = 4) →
        |graphIntegral G mass| ≤
          (∏ v : Fin r, (Nat.factorial (G.legs v) : ℝ) * A ^ (G.legs v)) *
            B ^ G.lines.card) :
    ∃ K : ℝ, 0 < K ∧
      ∀ {r : ℕ} (G : FeynmanGraph r), (∀ v : Fin r, G.legs v = 4) →
        |graphIntegral G mass| ≤ K ^ r := by
  rcases uniform_graphIntegral_abs_le_pos_const_pow_lines_of_phi4_weighted_family_local
      (mass := mass) (A := A) (B := B) hA hB hweighted with ⟨C, hCpos, hCbound⟩
  refine ⟨C ^ 2, by positivity, ?_⟩
  intro r G hphi4
  exact graphIntegral_abs_le_const_pow_vertices_of_phi4
    (G := G) (mass := mass) (C := C) hphi4 (hCbound G hphi4)

end FeynmanGraph

/-- φ⁴-specialized localized graph bound from weighted-family assumptions
    and a global valence-4 constraint. -/
theorem localized_graph_bound_of_phi4_weighted_family
    (mass : ℝ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hweighted :
      ∀ {r : ℕ} (G : FeynmanGraph r),
        |graphIntegral G mass| ≤
          (∏ v : Fin r, (Nat.factorial (G.legs v) : ℝ) * A ^ (G.legs v)) *
            B ^ G.lines.card)
    (hphi4Global :
      ∀ {r : ℕ} (G : FeynmanGraph r), ∀ v : Fin r, G.legs v = 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℕ) (G : FeynmanGraph r),
      |graphIntegral G mass| ≤ C ^ G.lines.card := by
  have hweightedDeg :
      ∀ {r : ℕ} (G : FeynmanGraph r), (∀ v : Fin r, G.legs v ≤ 4) →
        |graphIntegral G mass| ≤
          (∏ v : Fin r, (Nat.factorial (G.legs v) : ℝ) * A ^ (G.legs v)) *
            B ^ G.lines.card := by
    intro r G hdeg
    exact hweighted G
  have hdegGlobal :
      ∀ {r : ℕ} (G : FeynmanGraph r), ∀ v : Fin r, G.legs v ≤ 4 := by
    intro r G v
    simp [hphi4Global G v]
  exact localized_graph_bound_of_degree_weighted_family
    (mass := mass) (d := 4) (A := A) (B := B) hA hB hweightedDeg hdegGlobal

/-- φ⁴-specialized constructor of `FeynmanGraphEstimateModel` from explicit
    expansion data and weighted graph-integral bounds. -/
theorem feynmanGraphEstimateModel_nonempty_of_expansion_and_phi4_weighted
    (mass : ℝ) (hmass : 0 < mass)
    (hexpansion :
      ∀ (r : ℕ) (f : Fin r → TestFun2D),
        ∃ (graphs : Finset (FeynmanGraph r)),
          ∫ ω, (∏ i, ω (f i)) ∂(freeFieldMeasure mass hmass) =
            ∑ G ∈ graphs, graphIntegral G mass)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hweighted :
      ∀ {r : ℕ} (G : FeynmanGraph r),
        |graphIntegral G mass| ≤
          (∏ v : Fin r, (Nat.factorial (G.legs v) : ℝ) * A ^ (G.legs v)) *
            B ^ G.lines.card)
    (hphi4Global :
      ∀ {r : ℕ} (G : FeynmanGraph r), ∀ v : Fin r, G.legs v = 4) :
    Nonempty (FeynmanGraphEstimateModel mass hmass) := by
  have hweightedDeg :
      ∀ {r : ℕ} (G : FeynmanGraph r), (∀ v : Fin r, G.legs v ≤ 4) →
        |graphIntegral G mass| ≤
          (∏ v : Fin r, (Nat.factorial (G.legs v) : ℝ) * A ^ (G.legs v)) *
            B ^ G.lines.card := by
    intro r G hdeg
    exact hweighted G
  have hdegGlobal :
      ∀ {r : ℕ} (G : FeynmanGraph r), ∀ v : Fin r, G.legs v ≤ 4 := by
    intro r G v
    simp [hphi4Global G v]
  exact feynmanGraphEstimateModel_nonempty_of_expansion_and_degree_weighted
    (mass := mass) (hmass := hmass) hexpansion
    (d := 4) (A := A) (B := B) hA hB hweightedDeg hdegGlobal

end Phi4Specialization

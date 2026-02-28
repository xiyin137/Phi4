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

/-- Fiberwise occupancy control:
    if indices `s` are assigned to cells `t` via `loc`, then the product of
    per-index factorials is bounded by the product of factorials of per-cell
    occupancies. -/
theorem factorial_prod_le_factorial_sum_fiberwise
    {β : Type*} [DecidableEq β]
    (s : Finset α) (t : Finset β) (loc : α → β) (N : α → ℕ)
    (hmap : ∀ i ∈ s, loc i ∈ t) :
    (∏ i ∈ s, Nat.factorial (N i)) ≤
      ∏ b ∈ t, Nat.factorial (∑ i ∈ s with loc i = b, N i) := by
  have hpartition :
      (∏ b ∈ t, ∏ i ∈ s with loc i = b, Nat.factorial (N i)) =
        ∏ i ∈ s, Nat.factorial (N i) := by
    simpa using
      (Finset.prod_fiberwise_of_maps_to (s := s) (t := t) (g := loc)
        (h := hmap) (f := fun i => Nat.factorial (N i)))
  have hcell :
      ∀ b ∈ t,
        (∏ i ∈ s with loc i = b, Nat.factorial (N i)) ≤
          Nat.factorial (∑ i ∈ s with loc i = b, N i) := by
    intro b hb
    exact factorial_prod_le_factorial_sum (s := s.filter fun i => loc i = b) N
  have hprod :
      (∏ b ∈ t, ∏ i ∈ s with loc i = b, Nat.factorial (N i)) ≤
        ∏ b ∈ t, Nat.factorial (∑ i ∈ s with loc i = b, N i) := by
    exact Finset.prod_le_prod
      (fun b hb => Nat.zero_le _)
      (fun b hb => hcell b hb)
  calc
    (∏ i ∈ s, Nat.factorial (N i))
        = ∏ b ∈ t, ∏ i ∈ s with loc i = b, Nat.factorial (N i) := by
          simpa using hpartition.symm
    _ ≤ ∏ b ∈ t, Nat.factorial (∑ i ∈ s with loc i = b, N i) := hprod

/-- Real-cast variant of `factorial_prod_le_factorial_sum_fiberwise`. -/
theorem factorial_prod_le_factorial_sum_fiberwise_real
    {β : Type*} [DecidableEq β]
    (s : Finset α) (t : Finset β) (loc : α → β) (N : α → ℕ)
    (hmap : ∀ i ∈ s, loc i ∈ t) :
    (∏ i ∈ s, (Nat.factorial (N i) : ℝ)) ≤
      ∏ b ∈ t, (Nat.factorial (∑ i ∈ s with loc i = b, N i) : ℝ) := by
  exact_mod_cast factorial_prod_le_factorial_sum_fiberwise
    (s := s) (t := t) (loc := loc) (N := N) hmap

/-- Fiberwise weighted occupancy control:
    `∏ (N(i)! * A^{N(i)})` is bounded by the product of per-cell weighted
    occupancy factors, for any localization map `loc` into a finite cell set. -/
theorem factorial_weighted_prod_le_factorial_sum_pow_fiberwise
    {β : Type*} [DecidableEq β]
    (s : Finset α) (t : Finset β) (loc : α → β) (N : α → ℕ)
    (hmap : ∀ i ∈ s, loc i ∈ t) (A : ℝ) (hA : 0 ≤ A) :
    (∏ i ∈ s, (Nat.factorial (N i) : ℝ) * A ^ (N i)) ≤
      ∏ b ∈ t,
        (Nat.factorial (∑ i ∈ s with loc i = b, N i) : ℝ) *
          A ^ (∑ i ∈ s with loc i = b, N i) := by
  have hpartition :
      (∏ b ∈ t, ∏ i ∈ s with loc i = b, (Nat.factorial (N i) : ℝ) * A ^ (N i)) =
        ∏ i ∈ s, (Nat.factorial (N i) : ℝ) * A ^ (N i) := by
    simpa using
      (Finset.prod_fiberwise_of_maps_to (s := s) (t := t) (g := loc)
        (h := hmap) (f := fun i => (Nat.factorial (N i) : ℝ) * A ^ (N i)))
  have hcell :
      ∀ b ∈ t,
        (∏ i ∈ s with loc i = b, (Nat.factorial (N i) : ℝ) * A ^ (N i)) ≤
          (Nat.factorial (∑ i ∈ s with loc i = b, N i) : ℝ) *
            A ^ (∑ i ∈ s with loc i = b, N i) := by
    intro b hb
    exact factorial_weighted_prod_le_factorial_sum_pow
      (s := s.filter fun i => loc i = b) (N := N) A hA
  have hnonneg :
      ∀ b ∈ t, 0 ≤ ∏ i ∈ s with loc i = b, (Nat.factorial (N i) : ℝ) * A ^ (N i) := by
    intro b hb
    exact Finset.prod_nonneg (fun i hi =>
      mul_nonneg
        (by exact_mod_cast (Nat.zero_le (Nat.factorial (N i))))
        (pow_nonneg hA _))
  have hprod :
      (∏ b ∈ t, ∏ i ∈ s with loc i = b, (Nat.factorial (N i) : ℝ) * A ^ (N i)) ≤
        ∏ b ∈ t,
          (Nat.factorial (∑ i ∈ s with loc i = b, N i) : ℝ) *
            A ^ (∑ i ∈ s with loc i = b, N i) := by
    exact Finset.prod_le_prod hnonneg hcell
  calc
    (∏ i ∈ s, (Nat.factorial (N i) : ℝ) * A ^ (N i))
        = ∏ b ∈ t, ∏ i ∈ s with loc i = b, (Nat.factorial (N i) : ℝ) * A ^ (N i) := by
          simpa using hpartition.symm
    _ ≤ ∏ b ∈ t,
          (Nat.factorial (∑ i ∈ s with loc i = b, N i) : ℝ) *
            A ^ (∑ i ∈ s with loc i = b, N i) := hprod

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

/-- Vertex-to-cell occupancy transfer (unweighted):
    localization `loc` groups vertex legs into cell occupancies, and the product
    of vertex factorials is bounded by the product of cell-occupancy factorials. -/
theorem graph_vertex_factorial_prod_le_cell_occupancy_real
    {r : ℕ} {β : Type*} [DecidableEq β]
    (G : FeynmanGraph r) (cells : Finset β) (loc : Fin r → β)
    (hloc : ∀ v : Fin r, loc v ∈ cells) :
    (∏ v : Fin r, (Nat.factorial (G.legs v) : ℝ)) ≤
      ∏ c ∈ cells, (Nat.factorial (∑ v : Fin r with loc v = c, G.legs v) : ℝ) := by
  exact factorial_prod_le_factorial_sum_fiberwise_real
    (s := (Finset.univ : Finset (Fin r))) (t := cells) (loc := loc) (N := G.legs)
    (hmap := by
      intro v hv
      simpa using hloc v)

/-- Vertex-to-cell occupancy transfer (weighted):
    localization `loc` groups vertex legs into cell occupancies, and the weighted
    vertex occupancy product is bounded by weighted per-cell occupancies. -/
theorem graph_vertex_factorial_weighted_prod_le_cell_occupancy_weighted
    {r : ℕ} {β : Type*} [DecidableEq β]
    (G : FeynmanGraph r) (cells : Finset β) (loc : Fin r → β)
    (hloc : ∀ v : Fin r, loc v ∈ cells) (A : ℝ) (hA : 0 ≤ A) :
    (∏ v : Fin r, (Nat.factorial (G.legs v) : ℝ) * A ^ (G.legs v)) ≤
      ∏ c ∈ cells,
        (Nat.factorial (∑ v : Fin r with loc v = c, G.legs v) : ℝ) *
          A ^ (∑ v : Fin r with loc v = c, G.legs v) := by
  exact factorial_weighted_prod_le_factorial_sum_pow_fiberwise
    (s := (Finset.univ : Finset (Fin r))) (t := cells) (loc := loc) (N := G.legs)
    (hmap := by
      intro v hv
      simpa using hloc v)
    A hA

/-- Canonical-image variant of
    `graph_vertex_factorial_prod_le_cell_occupancy_real`. -/
theorem graph_vertex_factorial_prod_le_cell_occupancy_real_image
    {r : ℕ} {β : Type*} [DecidableEq β]
    (G : FeynmanGraph r) (loc : Fin r → β) :
    (∏ v : Fin r, (Nat.factorial (G.legs v) : ℝ)) ≤
      ∏ c ∈ (Finset.univ.image loc),
        (Nat.factorial (∑ v : Fin r with loc v = c, G.legs v) : ℝ) := by
  exact graph_vertex_factorial_prod_le_cell_occupancy_real
    (G := G) (cells := Finset.univ.image loc) (loc := loc)
    (hloc := by
      intro v
      exact Finset.mem_image.mpr ⟨v, by simp, rfl⟩)

/-- Canonical-image variant of
    `graph_vertex_factorial_weighted_prod_le_cell_occupancy_weighted`. -/
theorem graph_vertex_factorial_weighted_prod_le_cell_occupancy_weighted_image
    {r : ℕ} {β : Type*} [DecidableEq β]
    (G : FeynmanGraph r) (loc : Fin r → β) (A : ℝ) (hA : 0 ≤ A) :
    (∏ v : Fin r, (Nat.factorial (G.legs v) : ℝ) * A ^ (G.legs v)) ≤
      ∏ c ∈ (Finset.univ.image loc),
        (Nat.factorial (∑ v : Fin r with loc v = c, G.legs v) : ℝ) *
          A ^ (∑ v : Fin r with loc v = c, G.legs v) := by
  exact graph_vertex_factorial_weighted_prod_le_cell_occupancy_weighted
    (G := G) (cells := Finset.univ.image loc) (loc := loc)
    (hloc := by
      intro v
      exact Finset.mem_image.mpr ⟨v, by simp, rfl⟩)
    A hA

/-- Transfer a vertex-weighted graph-integral bound to a per-cell weighted form
    using a localization map `loc : vertices → cells`. -/
theorem graphIntegral_abs_le_cell_occupancy_weighted_of_vertex_weighted_bound
    {r : ℕ} {β : Type*} [DecidableEq β]
    (G : FeynmanGraph r) (mass : ℝ) (cells : Finset β) (loc : Fin r → β)
    (hloc : ∀ v : Fin r, loc v ∈ cells)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbound :
      |graphIntegral G mass| ≤
        (∏ v : Fin r, (Nat.factorial (G.legs v) : ℝ) * A ^ (G.legs v)) *
          B ^ G.lines.card) :
    |graphIntegral G mass| ≤
      (∏ c ∈ cells,
        (Nat.factorial (∑ v : Fin r with loc v = c, G.legs v) : ℝ) *
          A ^ (∑ v : Fin r with loc v = c, G.legs v)) *
        B ^ G.lines.card := by
  have hocc :
      (∏ v : Fin r, (Nat.factorial (G.legs v) : ℝ) * A ^ (G.legs v)) ≤
        ∏ c ∈ cells,
          (Nat.factorial (∑ v : Fin r with loc v = c, G.legs v) : ℝ) *
            A ^ (∑ v : Fin r with loc v = c, G.legs v) :=
    graph_vertex_factorial_weighted_prod_le_cell_occupancy_weighted
      (G := G) (cells := cells) (loc := loc) hloc A hA
  have hmul :
      (∏ v : Fin r, (Nat.factorial (G.legs v) : ℝ) * A ^ (G.legs v)) *
          B ^ G.lines.card ≤
        (∏ c ∈ cells,
          (Nat.factorial (∑ v : Fin r with loc v = c, G.legs v) : ℝ) *
            A ^ (∑ v : Fin r with loc v = c, G.legs v)) *
          B ^ G.lines.card := by
    exact mul_le_mul_of_nonneg_right hocc (pow_nonneg hB _)
  exact hbound.trans hmul

/-- Canonical-image variant of
    `graphIntegral_abs_le_cell_occupancy_weighted_of_vertex_weighted_bound`. -/
theorem graphIntegral_abs_le_cell_occupancy_weighted_of_vertex_weighted_bound_image
    {r : ℕ} {β : Type*} [DecidableEq β]
    (G : FeynmanGraph r) (mass : ℝ) (loc : Fin r → β)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbound :
      |graphIntegral G mass| ≤
        (∏ v : Fin r, (Nat.factorial (G.legs v) : ℝ) * A ^ (G.legs v)) *
          B ^ G.lines.card) :
    |graphIntegral G mass| ≤
      (∏ c ∈ (Finset.univ.image loc),
        (Nat.factorial (∑ v : Fin r with loc v = c, G.legs v) : ℝ) *
          A ^ (∑ v : Fin r with loc v = c, G.legs v)) *
        B ^ G.lines.card := by
  exact graphIntegral_abs_le_cell_occupancy_weighted_of_vertex_weighted_bound
    (G := G) (mass := mass) (cells := Finset.univ.image loc) (loc := loc)
    (hloc := by
      intro v
      exact Finset.mem_image.mpr ⟨v, by simp, rfl⟩)
    (A := A) (B := B) hA hB hbound

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

/-- φ⁴-localized per-cell bound:
    under `legs(v)=4`, a vertex-weighted bound rewrites to a per-cell occupancy
    form with explicit occupancies `4 * #(vertices in cell)` and
    `B^(2|V|)` from `|lines| = 2|V|`. -/
theorem graphIntegral_abs_le_cell_occupancy_weighted_of_phi4_vertex_weighted_bound
    {β : Type*} [DecidableEq β]
    (G : FeynmanGraph r) (mass : ℝ) (cells : Finset β) (loc : Fin r → β)
    (hloc : ∀ v : Fin r, loc v ∈ cells)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hphi4 : ∀ v : Fin r, G.legs v = 4)
    (hbound :
      |graphIntegral G mass| ≤
        (∏ v : Fin r, (Nat.factorial (G.legs v) : ℝ) * A ^ (G.legs v)) *
          B ^ G.lines.card) :
    |graphIntegral G mass| ≤
      (∏ c ∈ cells,
        (Nat.factorial (4 * ((Finset.univ.filter fun v : Fin r => loc v = c).card)) : ℝ) *
          A ^ (4 * ((Finset.univ.filter fun v : Fin r => loc v = c).card))) *
        B ^ (2 * r) := by
  have hbase :
      |graphIntegral G mass| ≤
        (∏ c ∈ cells,
          (Nat.factorial (∑ v : Fin r with loc v = c, G.legs v) : ℝ) *
            A ^ (∑ v : Fin r with loc v = c, G.legs v)) *
          B ^ G.lines.card :=
    graphIntegral_abs_le_cell_occupancy_weighted_of_vertex_weighted_bound
      (G := G) (mass := mass) (cells := cells) (loc := loc) hloc
      (A := A) (B := B) hA hB hbound
  have hsum :
      ∀ c : β,
        (∑ v : Fin r with loc v = c, G.legs v) =
          4 * ((Finset.univ.filter fun v : Fin r => loc v = c).card) := by
    intro c
    calc
      (∑ v : Fin r with loc v = c, G.legs v)
          = ∑ v : Fin r with loc v = c, 4 := by
              refine Finset.sum_congr rfl ?_
              intro v hv
              simp [hphi4 v]
      _ = ((Finset.univ.filter fun v : Fin r => loc v = c).card) * 4 := by
            simp
      _ = 4 * ((Finset.univ.filter fun v : Fin r => loc v = c).card) := by
            simp [Nat.mul_comm]
  have hcells :
      (∏ c ∈ cells,
        (Nat.factorial (∑ v : Fin r with loc v = c, G.legs v) : ℝ) *
          A ^ (∑ v : Fin r with loc v = c, G.legs v)) =
      (∏ c ∈ cells,
        (Nat.factorial (4 * ((Finset.univ.filter fun v : Fin r => loc v = c).card)) : ℝ) *
          A ^ (4 * ((Finset.univ.filter fun v : Fin r => loc v = c).card))) := by
    refine Finset.prod_congr rfl ?_
    intro c hc
    simp [hsum c]
  have hlines : B ^ G.lines.card = B ^ (2 * r) := by
    simp [lines_card_eq_two_mul_vertices_of_phi4 (G := G) hphi4]
  calc
    |graphIntegral G mass|
        ≤ (∏ c ∈ cells,
            (Nat.factorial (∑ v : Fin r with loc v = c, G.legs v) : ℝ) *
              A ^ (∑ v : Fin r with loc v = c, G.legs v)) *
            B ^ G.lines.card := hbase
    _ = (∏ c ∈ cells,
          (Nat.factorial (4 * ((Finset.univ.filter fun v : Fin r => loc v = c).card)) : ℝ) *
            A ^ (4 * ((Finset.univ.filter fun v : Fin r => loc v = c).card))) *
          B ^ G.lines.card := by
            simp [hcells]
    _ = (∏ c ∈ cells,
          (Nat.factorial (4 * ((Finset.univ.filter fun v : Fin r => loc v = c).card)) : ℝ) *
            A ^ (4 * ((Finset.univ.filter fun v : Fin r => loc v = c).card))) *
          B ^ (2 * r) := by
            simp [hlines]

/-- Under a localization map `loc : Fin r → cells` covering all vertices,
    the summed φ⁴ cell occupancies are exactly `4 * r`. -/
theorem phi4_sum_cell_occupancies_eq_four_mul_vertices
    {β : Type*} [DecidableEq β]
    (cells : Finset β) (loc : Fin r → β)
    (hloc : ∀ v : Fin r, loc v ∈ cells) :
    (∑ c ∈ cells, 4 * ((Finset.univ.filter fun v : Fin r => loc v = c).card)) = 4 * r := by
  have hmap :
      ((Finset.univ : Finset (Fin r)) : Set (Fin r)).MapsTo loc (cells : Set β) := by
    intro v hv
    simpa using hloc v
  have hcount :
      (Finset.univ : Finset (Fin r)).card =
        ∑ c ∈ cells, ((Finset.univ.filter fun v : Fin r => loc v = c).card) := by
    simpa using
      (Finset.card_eq_sum_card_fiberwise
        (f := loc) (s := (Finset.univ : Finset (Fin r))) (t := cells) hmap)
  calc
    (∑ c ∈ cells, 4 * ((Finset.univ.filter fun v : Fin r => loc v = c).card))
        = 4 * (∑ c ∈ cells, ((Finset.univ.filter fun v : Fin r => loc v = c).card)) := by
          simp [Finset.mul_sum]
    _ = 4 * ((Finset.univ : Finset (Fin r)).card) := by
          rw [← hcount]
    _ = 4 * r := by simp

/-- The φ⁴ per-cell weighted occupancy product is bounded by the global
    weighted total-leg factor `((4r)!)*A^(4r)`. -/
theorem phi4_cell_occupancy_weighted_prod_le_total_factorial_pow
    {β : Type*} [DecidableEq β]
    (cells : Finset β) (loc : Fin r → β)
    (hloc : ∀ v : Fin r, loc v ∈ cells)
    (A : ℝ) (hA : 0 ≤ A) :
    (∏ c ∈ cells,
      (Nat.factorial (4 * ((Finset.univ.filter fun v : Fin r => loc v = c).card)) : ℝ) *
        A ^ (4 * ((Finset.univ.filter fun v : Fin r => loc v = c).card))) ≤
      (Nat.factorial (4 * r) : ℝ) * A ^ (4 * r) := by
  have hbase :
      (∏ c ∈ cells,
        (Nat.factorial (4 * ((Finset.univ.filter fun v : Fin r => loc v = c).card)) : ℝ) *
          A ^ (4 * ((Finset.univ.filter fun v : Fin r => loc v = c).card))) ≤
        (Nat.factorial
          (∑ c ∈ cells, 4 * ((Finset.univ.filter fun v : Fin r => loc v = c).card)) : ℝ) *
          A ^ (∑ c ∈ cells, 4 * ((Finset.univ.filter fun v : Fin r => loc v = c).card)) := by
    exact factorial_weighted_prod_le_factorial_sum_pow
      (s := cells)
      (N := fun c => 4 * ((Finset.univ.filter fun v : Fin r => loc v = c).card))
      A hA
  simpa [phi4_sum_cell_occupancies_eq_four_mul_vertices (cells := cells) (loc := loc) hloc]
    using hbase

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

/-- φ⁴ weighted bound in global factorial form:
    `|I(G)| ≤ ((4r)! * A^(4r)) * B^(2r)`. -/
theorem graphIntegral_abs_le_total_factorial_pow_vertices_of_phi4_weighted_bound
    (G : FeynmanGraph r) (mass : ℝ)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hphi4 : ∀ v : Fin r, G.legs v = 4)
    (hbound :
      |graphIntegral G mass| ≤
        (∏ v : Fin r, (Nat.factorial (G.legs v) : ℝ) * A ^ (G.legs v)) *
          B ^ G.lines.card) :
    |graphIntegral G mass| ≤
      ((Nat.factorial (4 * r) : ℝ) * A ^ (4 * r)) * B ^ (2 * r) := by
  have hocc :
      (∏ v : Fin r, (Nat.factorial (G.legs v) : ℝ) * A ^ (G.legs v)) ≤
        (Nat.factorial (∑ v : Fin r, G.legs v) : ℝ) * A ^ (∑ v : Fin r, G.legs v) :=
    graph_vertex_factorial_weighted_prod_le_total_factorial_pow (G := G) (A := A) hA
  have hmul :
      (∏ v : Fin r, (Nat.factorial (G.legs v) : ℝ) * A ^ (G.legs v)) *
          B ^ G.lines.card ≤
        ((Nat.factorial (∑ v : Fin r, G.legs v) : ℝ) * A ^ (∑ v : Fin r, G.legs v)) *
          B ^ G.lines.card := by
    exact mul_le_mul_of_nonneg_right hocc (pow_nonneg hB _)
  have hlegs : (∑ v : Fin r, G.legs v) = 4 * r := by
    calc
      (∑ v : Fin r, G.legs v) = r * 4 :=
        total_legs_eq_mul_card_of_const_legs (G := G) 4 hphi4
      _ = 4 * r := by simp [Nat.mul_comm]
  have hlines : G.lines.card = 2 * r :=
    lines_card_eq_two_mul_vertices_of_phi4 (G := G) hphi4
  calc
    |graphIntegral G mass|
        ≤ (∏ v : Fin r, (Nat.factorial (G.legs v) : ℝ) * A ^ (G.legs v)) *
            B ^ G.lines.card := hbound
    _ ≤ ((Nat.factorial (∑ v : Fin r, G.legs v) : ℝ) * A ^ (∑ v : Fin r, G.legs v)) *
          B ^ G.lines.card := hmul
    _ = ((Nat.factorial (4 * r) : ℝ) * A ^ (4 * r)) * B ^ (2 * r) := by
          simp [hlegs, hlines]

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

/-- Finite φ⁴ graph-family control:
    the sum of absolute graph integrals is bounded by graph count times the
    sharp per-vertex constant. -/
theorem sum_abs_graphIntegral_le_card_mul_const_pow_vertices_of_phi4_weighted_sharp
    (graphs : Finset (FeynmanGraph r)) (mass : ℝ) (A B : ℝ)
    (hphi4 : ∀ G ∈ graphs, ∀ v : Fin r, G.legs v = 4)
    (hbound :
      ∀ G ∈ graphs, |graphIntegral G mass| ≤
        (∏ v : Fin r, (Nat.factorial (G.legs v) : ℝ) * A ^ (G.legs v)) *
          B ^ G.lines.card) :
    Finset.sum graphs (fun G => |graphIntegral G mass|) ≤
      graphs.card * ((((Nat.factorial 4 : ℝ) * A ^ 4) * (B ^ 2)) ^ r) := by
  have hsum :
      Finset.sum graphs (fun G => |graphIntegral G mass|) ≤
        Finset.sum graphs (fun _ => ((((Nat.factorial 4 : ℝ) * A ^ 4) * (B ^ 2)) ^ r)) := by
    refine Finset.sum_le_sum ?_
    intro G hG
    exact graphIntegral_abs_le_const_pow_vertices_of_phi4_weighted_bound_sharp
      (G := G) (mass := mass) (A := A) (B := B)
      (hphi4 := hphi4 G hG) (hbound := hbound G hG)
  calc
    Finset.sum graphs (fun G => |graphIntegral G mass|)
        ≤ Finset.sum graphs (fun _ => ((((Nat.factorial 4 : ℝ) * A ^ 4) * (B ^ 2)) ^ r)) := hsum
    _ = graphs.card * ((((Nat.factorial 4 : ℝ) * A ^ 4) * (B ^ 2)) ^ r) := by
          simp [Finset.sum_const, nsmul_eq_mul]

/-- Finite φ⁴ expansion control:
    if an expansion uses a finite graph family, then the absolute value of the
    expansion is bounded by graph count times the sharp per-vertex constant. -/
theorem feynman_expansion_abs_le_card_mul_const_pow_vertices_of_phi4_weighted_sharp
    (graphs : Finset (FeynmanGraph r)) (mass : ℝ) (hmass : 0 < mass)
    (A B : ℝ)
    (f : Fin r → TestFun2D)
    (hexp :
      ∫ ω, (∏ i, ω (f i)) ∂(freeFieldMeasure mass hmass) =
        Finset.sum graphs (fun G => graphIntegral G mass))
    (hphi4 : ∀ G ∈ graphs, ∀ v : Fin r, G.legs v = 4)
    (hbound :
      ∀ G ∈ graphs, |graphIntegral G mass| ≤
        (∏ v : Fin r, (Nat.factorial (G.legs v) : ℝ) * A ^ (G.legs v)) *
          B ^ G.lines.card) :
    |∫ ω, (∏ i, ω (f i)) ∂(freeFieldMeasure mass hmass)| ≤
      graphs.card * ((((Nat.factorial 4 : ℝ) * A ^ 4) * (B ^ 2)) ^ r) := by
  rw [hexp]
  have habs :
      |Finset.sum graphs (fun G => graphIntegral G mass)| ≤
        Finset.sum graphs (fun G => |graphIntegral G mass|) := by
    simpa using
      (Finset.abs_sum_le_sum_abs
        (f := fun G : FeynmanGraph r => graphIntegral G mass)
        (s := graphs))
  exact habs.trans
    (sum_abs_graphIntegral_le_card_mul_const_pow_vertices_of_phi4_weighted_sharp
      (graphs := graphs) (mass := mass) (A := A) (B := B) hphi4 hbound)

/-- Finite φ⁴ graph-family bound in global factorial form:
    if each graph satisfies the weighted φ⁴ hypothesis, then
    `∑ |I(G)| ≤ #graphs * (((4r)! * A^(4r)) * B^(2r))`. -/
theorem sum_abs_graphIntegral_le_card_mul_total_factorial_pow_vertices_of_phi4_weighted
    (graphs : Finset (FeynmanGraph r)) (mass : ℝ)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hphi4 : ∀ G ∈ graphs, ∀ v : Fin r, G.legs v = 4)
    (hbound :
      ∀ G ∈ graphs, |graphIntegral G mass| ≤
        (∏ v : Fin r, (Nat.factorial (G.legs v) : ℝ) * A ^ (G.legs v)) *
          B ^ G.lines.card) :
    Finset.sum graphs (fun G => |graphIntegral G mass|) ≤
      graphs.card * (((Nat.factorial (4 * r) : ℝ) * A ^ (4 * r)) * B ^ (2 * r)) := by
  have hsum :
      Finset.sum graphs (fun G => |graphIntegral G mass|) ≤
        Finset.sum graphs (fun _ =>
          ((Nat.factorial (4 * r) : ℝ) * A ^ (4 * r)) * B ^ (2 * r)) := by
    refine Finset.sum_le_sum ?_
    intro G hG
    exact graphIntegral_abs_le_total_factorial_pow_vertices_of_phi4_weighted_bound
      (G := G) (mass := mass) (A := A) (B := B) hA hB
      (hphi4 := hphi4 G hG) (hbound := hbound G hG)
  calc
    Finset.sum graphs (fun G => |graphIntegral G mass|)
        ≤ Finset.sum graphs (fun _ =>
            ((Nat.factorial (4 * r) : ℝ) * A ^ (4 * r)) * B ^ (2 * r)) := hsum
    _ = graphs.card * (((Nat.factorial (4 * r) : ℝ) * A ^ (4 * r)) * B ^ (2 * r)) := by
          simp [Finset.sum_const, nsmul_eq_mul]

/-- Finite φ⁴ expansion control in global factorial form:
    `|expansion| ≤ #graphs * (((4r)! * A^(4r)) * B^(2r))`. -/
theorem feynman_expansion_abs_le_card_mul_total_factorial_pow_vertices_of_phi4_weighted
    (graphs : Finset (FeynmanGraph r)) (mass : ℝ) (hmass : 0 < mass)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (f : Fin r → TestFun2D)
    (hexp :
      ∫ ω, (∏ i, ω (f i)) ∂(freeFieldMeasure mass hmass) =
        Finset.sum graphs (fun G => graphIntegral G mass))
    (hphi4 : ∀ G ∈ graphs, ∀ v : Fin r, G.legs v = 4)
    (hbound :
      ∀ G ∈ graphs, |graphIntegral G mass| ≤
        (∏ v : Fin r, (Nat.factorial (G.legs v) : ℝ) * A ^ (G.legs v)) *
          B ^ G.lines.card) :
    |∫ ω, (∏ i, ω (f i)) ∂(freeFieldMeasure mass hmass)| ≤
      graphs.card * (((Nat.factorial (4 * r) : ℝ) * A ^ (4 * r)) * B ^ (2 * r)) := by
  rw [hexp]
  have habs :
      |Finset.sum graphs (fun G => graphIntegral G mass)| ≤
        Finset.sum graphs (fun G => |graphIntegral G mass|) := by
    simpa using
      (Finset.abs_sum_le_sum_abs
        (f := fun G : FeynmanGraph r => graphIntegral G mass)
        (s := graphs))
  exact habs.trans
    (sum_abs_graphIntegral_le_card_mul_total_factorial_pow_vertices_of_phi4_weighted
      (graphs := graphs) (mass := mass) (A := A) (B := B) hA hB hphi4 hbound)

/-- Generic finite graph-family control from a per-graph `K^{|V|}` bound. -/
theorem sum_abs_graphIntegral_le_card_mul_const_pow_vertices
    (graphs : Finset (FeynmanGraph r)) (mass K : ℝ)
    (hbound : ∀ G ∈ graphs, |graphIntegral G mass| ≤ K ^ r) :
    Finset.sum graphs (fun G => |graphIntegral G mass|) ≤ graphs.card * (K ^ r) := by
  have hsum :
      Finset.sum graphs (fun G => |graphIntegral G mass|) ≤
        Finset.sum graphs (fun _ => K ^ r) := by
    refine Finset.sum_le_sum ?_
    intro G hG
    exact hbound G hG
  calc
    Finset.sum graphs (fun G => |graphIntegral G mass|)
        ≤ Finset.sum graphs (fun _ => K ^ r) := hsum
    _ = graphs.card * (K ^ r) := by
          simp [Finset.sum_const, nsmul_eq_mul]

/-- Generic finite expansion control from a per-graph `K^{|V|}` bound. -/
theorem feynman_expansion_abs_le_card_mul_const_pow_vertices
    (graphs : Finset (FeynmanGraph r)) (mass : ℝ) (hmass : 0 < mass)
    (f : Fin r → TestFun2D)
    (hexp :
      ∫ ω, (∏ i, ω (f i)) ∂(freeFieldMeasure mass hmass) =
        Finset.sum graphs (fun G => graphIntegral G mass))
    (K : ℝ)
    (hbound : ∀ G ∈ graphs, |graphIntegral G mass| ≤ K ^ r) :
    |∫ ω, (∏ i, ω (f i)) ∂(freeFieldMeasure mass hmass)| ≤
      graphs.card * (K ^ r) := by
  rw [hexp]
  have habs :
      |Finset.sum graphs (fun G => graphIntegral G mass)| ≤
        Finset.sum graphs (fun G => |graphIntegral G mass|) := by
    simpa using
      (Finset.abs_sum_le_sum_abs
        (f := fun G : FeynmanGraph r => graphIntegral G mass)
        (s := graphs))
  exact habs.trans
    (sum_abs_graphIntegral_le_card_mul_const_pow_vertices
      (graphs := graphs) (mass := mass) (K := K) hbound)

/-- If the number of graphs is itself exponentially bounded in `|V|`,
    then finite expansion bounds collapse to a pure exponential in `|V|`. -/
theorem feynman_expansion_abs_le_const_pow_vertices_of_card_bound
    (graphs : Finset (FeynmanGraph r)) (mass : ℝ) (hmass : 0 < mass)
    (f : Fin r → TestFun2D)
    (hexp :
      ∫ ω, (∏ i, ω (f i)) ∂(freeFieldMeasure mass hmass) =
        Finset.sum graphs (fun G => graphIntegral G mass))
    (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ G ∈ graphs, |graphIntegral G mass| ≤ K ^ r)
    (N : ℕ) (hcard : graphs.card ≤ N ^ r) :
    |∫ ω, (∏ i, ω (f i)) ∂(freeFieldMeasure mass hmass)| ≤
      (((N : ℝ) * K) ^ r) := by
  have hbase :
      |∫ ω, (∏ i, ω (f i)) ∂(freeFieldMeasure mass hmass)| ≤
        graphs.card * (K ^ r) :=
    feynman_expansion_abs_le_card_mul_const_pow_vertices
      (graphs := graphs) (mass := mass) (hmass := hmass) (f := f) hexp (K := K) hbound
  have hcardR : (graphs.card : ℝ) ≤ (N : ℝ) ^ r := by
    exact_mod_cast hcard
  have hmul :
      (graphs.card : ℝ) * (K ^ r) ≤ ((N : ℝ) ^ r) * (K ^ r) := by
    exact mul_le_mul_of_nonneg_right hcardR (pow_nonneg hK _)
  calc
    |∫ ω, (∏ i, ω (f i)) ∂(freeFieldMeasure mass hmass)|
        ≤ (graphs.card : ℝ) * (K ^ r) := hbase
    _ ≤ ((N : ℝ) ^ r) * (K ^ r) := hmul
    _ = (((N : ℝ) * K) ^ r) := by
          simpa using (mul_pow (N : ℝ) K r).symm

/-- Finite φ⁴ expansion control via the local weighted-family infrastructure:
    extract a positive `K`, then bound by `#graphs * K^{|V|}`. -/
theorem feynman_expansion_abs_le_card_mul_uniform_const_pow_vertices_of_phi4_weighted_family_local
    (graphs : Finset (FeynmanGraph r)) (mass : ℝ) (hmass : 0 < mass)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (f : Fin r → TestFun2D)
    (hexp :
      ∫ ω, (∏ i, ω (f i)) ∂(freeFieldMeasure mass hmass) =
        Finset.sum graphs (fun G => graphIntegral G mass))
    (hphi4 : ∀ G ∈ graphs, ∀ v : Fin r, G.legs v = 4)
    (hweighted :
      ∀ {r : ℕ} (G : FeynmanGraph r), (∀ v : Fin r, G.legs v = 4) →
        |graphIntegral G mass| ≤
          (∏ v : Fin r, (Nat.factorial (G.legs v) : ℝ) * A ^ (G.legs v)) *
            B ^ G.lines.card) :
    ∃ K : ℝ, 0 < K ∧
      |∫ ω, (∏ i, ω (f i)) ∂(freeFieldMeasure mass hmass)| ≤
        graphs.card * (K ^ r) := by
  let K0 : ℝ := ((Nat.factorial 4 : ℝ) * A ^ 4) * (B ^ 2)
  have hfact_nonneg : 0 ≤ (Nat.factorial 4 : ℝ) := by
    exact_mod_cast (Nat.zero_le (Nat.factorial 4))
  have hK0_nonneg : 0 ≤ K0 := by
    dsimp [K0]
    exact mul_nonneg (mul_nonneg hfact_nonneg (pow_nonneg hA 4)) (pow_nonneg hB 2)
  refine ⟨K0 + 1, by linarith, ?_⟩
  exact feynman_expansion_abs_le_card_mul_const_pow_vertices
    (graphs := graphs) (mass := mass) (hmass := hmass) (f := f) hexp (K := K0 + 1)
    (fun G hG => by
      have hsharp :
          |graphIntegral G mass| ≤ K0 ^ r := by
        dsimp [K0]
        exact graphIntegral_abs_le_const_pow_vertices_of_phi4_weighted_bound_sharp
          (G := G) (mass := mass) (A := A) (B := B)
          (hphi4 := hphi4 G hG) (hbound := hweighted G (hphi4 G hG))
      have hpow : K0 ^ r ≤ (K0 + 1) ^ r := by
        exact pow_le_pow_left₀ hK0_nonneg (le_add_of_nonneg_right zero_le_one) _
      exact hsharp.trans hpow)

/-- Local φ⁴ weighted-family expansion control in pure exponential form, using
    an explicit graph-count growth bound `#graphs ≤ N^{|V|}`. -/
theorem feynman_expansion_abs_le_uniform_const_pow_vertices_of_phi4_weighted_family_local
    (graphs : Finset (FeynmanGraph r)) (mass : ℝ) (hmass : 0 < mass)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (f : Fin r → TestFun2D)
    (hexp :
      ∫ ω, (∏ i, ω (f i)) ∂(freeFieldMeasure mass hmass) =
        Finset.sum graphs (fun G => graphIntegral G mass))
    (hphi4 : ∀ G ∈ graphs, ∀ v : Fin r, G.legs v = 4)
    (hweighted :
      ∀ {r : ℕ} (G : FeynmanGraph r), (∀ v : Fin r, G.legs v = 4) →
        |graphIntegral G mass| ≤
          (∏ v : Fin r, (Nat.factorial (G.legs v) : ℝ) * A ^ (G.legs v)) *
            B ^ G.lines.card)
    (N : ℕ) (hcard : graphs.card ≤ N ^ r) :
    ∃ K : ℝ, 0 < K ∧
      |∫ ω, (∏ i, ω (f i)) ∂(freeFieldMeasure mass hmass)| ≤
        (((N : ℝ) * K) ^ r) := by
  rcases feynman_expansion_abs_le_card_mul_uniform_const_pow_vertices_of_phi4_weighted_family_local
      (graphs := graphs) (mass := mass) (hmass := hmass)
      (A := A) (B := B) hA hB (f := f) hexp hphi4 hweighted with
    ⟨K, hKpos, hbound⟩
  refine ⟨K, hKpos, ?_⟩
  have hcardR : (graphs.card : ℝ) ≤ (N : ℝ) ^ r := by
    exact_mod_cast hcard
  have hmul :
      (graphs.card : ℝ) * (K ^ r) ≤ ((N : ℝ) ^ r) * (K ^ r) := by
    exact mul_le_mul_of_nonneg_right hcardR (pow_nonneg hKpos.le _)
  calc
    |∫ ω, (∏ i, ω (f i)) ∂(freeFieldMeasure mass hmass)|
        ≤ (graphs.card : ℝ) * (K ^ r) := hbound
    _ ≤ ((N : ℝ) ^ r) * (K ^ r) := hmul
    _ = (((N : ℝ) * K) ^ r) := by
          simpa using (mul_pow (N : ℝ) K r).symm

/-- Explicit local φ⁴ weighted-family finite expansion bound with concrete
    constant `K0 = (4! * A^4) * B^2`. -/
theorem feynman_expansion_abs_le_card_mul_explicit_const_pow_vertices_of_phi4_weighted_family_local
    (graphs : Finset (FeynmanGraph r)) (mass : ℝ) (hmass : 0 < mass)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (f : Fin r → TestFun2D)
    (hexp :
      ∫ ω, (∏ i, ω (f i)) ∂(freeFieldMeasure mass hmass) =
        Finset.sum graphs (fun G => graphIntegral G mass))
    (hphi4 : ∀ G ∈ graphs, ∀ v : Fin r, G.legs v = 4)
    (hweighted :
      ∀ {r : ℕ} (G : FeynmanGraph r), (∀ v : Fin r, G.legs v = 4) →
        |graphIntegral G mass| ≤
          (∏ v : Fin r, (Nat.factorial (G.legs v) : ℝ) * A ^ (G.legs v)) *
            B ^ G.lines.card) :
    |∫ ω, (∏ i, ω (f i)) ∂(freeFieldMeasure mass hmass)| ≤
      graphs.card * ((((Nat.factorial 4 : ℝ) * A ^ 4) * (B ^ 2) + 1) ^ r) := by
  let K0 : ℝ := ((Nat.factorial 4 : ℝ) * A ^ 4) * (B ^ 2)
  have hK0_nonneg : 0 ≤ K0 := by
    dsimp [K0]
    have hfact_nonneg : 0 ≤ (Nat.factorial 4 : ℝ) := by
      exact_mod_cast (Nat.zero_le (Nat.factorial 4))
    exact mul_nonneg (mul_nonneg hfact_nonneg (pow_nonneg hA 4)) (pow_nonneg hB 2)
  have hgraph :
      ∀ G ∈ graphs, |graphIntegral G mass| ≤ (K0 + 1) ^ r := by
    intro G hG
    have hsharp : |graphIntegral G mass| ≤ K0 ^ r := by
      dsimp [K0]
      exact graphIntegral_abs_le_const_pow_vertices_of_phi4_weighted_bound_sharp
        (G := G) (mass := mass) (A := A) (B := B)
        (hphi4 := hphi4 G hG) (hbound := hweighted G (hphi4 G hG))
    have hpow : K0 ^ r ≤ (K0 + 1) ^ r := by
      exact pow_le_pow_left₀ hK0_nonneg (le_add_of_nonneg_right zero_le_one) _
    exact hsharp.trans hpow
  simpa [K0] using
    feynman_expansion_abs_le_card_mul_const_pow_vertices
      (graphs := graphs) (mass := mass) (hmass := hmass) (f := f) hexp
      (K := K0 + 1) hgraph

/-- Explicit local φ⁴ weighted-family finite expansion bound in pure
    exponential form under graph-count growth `#graphs ≤ N^{|V|}`. -/
theorem feynman_expansion_abs_le_explicit_uniform_const_pow_vertices_of_phi4_weighted_family_local
    (graphs : Finset (FeynmanGraph r)) (mass : ℝ) (hmass : 0 < mass)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (f : Fin r → TestFun2D)
    (hexp :
      ∫ ω, (∏ i, ω (f i)) ∂(freeFieldMeasure mass hmass) =
        Finset.sum graphs (fun G => graphIntegral G mass))
    (hphi4 : ∀ G ∈ graphs, ∀ v : Fin r, G.legs v = 4)
    (hweighted :
      ∀ {r : ℕ} (G : FeynmanGraph r), (∀ v : Fin r, G.legs v = 4) →
        |graphIntegral G mass| ≤
          (∏ v : Fin r, (Nat.factorial (G.legs v) : ℝ) * A ^ (G.legs v)) *
            B ^ G.lines.card)
    (N : ℕ) (hcard : graphs.card ≤ N ^ r) :
    |∫ ω, (∏ i, ω (f i)) ∂(freeFieldMeasure mass hmass)| ≤
      (((N : ℝ) * (((Nat.factorial 4 : ℝ) * A ^ 4) * (B ^ 2) + 1)) ^ r) := by
  have hbase :
      |∫ ω, (∏ i, ω (f i)) ∂(freeFieldMeasure mass hmass)| ≤
        graphs.card * ((((Nat.factorial 4 : ℝ) * A ^ 4) * (B ^ 2) + 1) ^ r) :=
    feynman_expansion_abs_le_card_mul_explicit_const_pow_vertices_of_phi4_weighted_family_local
      (graphs := graphs) (mass := mass) (hmass := hmass)
      (A := A) (B := B) hA hB (f := f) hexp hphi4 hweighted
  have hcardR : (graphs.card : ℝ) ≤ (N : ℝ) ^ r := by
    exact_mod_cast hcard
  have hmul :
      (graphs.card : ℝ) * ((((Nat.factorial 4 : ℝ) * A ^ 4) * (B ^ 2) + 1) ^ r) ≤
        ((N : ℝ) ^ r) * ((((Nat.factorial 4 : ℝ) * A ^ 4) * (B ^ 2) + 1) ^ r) := by
    exact mul_le_mul_of_nonneg_right hcardR
      (pow_nonneg (by positivity) _)
  calc
    |∫ ω, (∏ i, ω (f i)) ∂(freeFieldMeasure mass hmass)|
        ≤ (graphs.card : ℝ) * ((((Nat.factorial 4 : ℝ) * A ^ 4) * (B ^ 2) + 1) ^ r) := hbase
    _ ≤ ((N : ℝ) ^ r) * ((((Nat.factorial 4 : ℝ) * A ^ 4) * (B ^ 2) + 1) ^ r) := hmul
    _ = (((N : ℝ) * (((Nat.factorial 4 : ℝ) * A ^ 4) * (B ^ 2) + 1)) ^ r) := by
          simpa using
            (mul_pow (N : ℝ) (((Nat.factorial 4 : ℝ) * A ^ 4) * (B ^ 2) + 1) r).symm

/-- Finite φ⁴ expansion bound in per-cell occupancy form for a fixed
    localization map `loc : vertices → cells`. -/
theorem feynman_expansion_abs_le_card_mul_cell_occupancy_weighted_of_phi4_vertex_weighted
    {β : Type*} [DecidableEq β]
    (graphs : Finset (FeynmanGraph r)) (mass : ℝ) (hmass : 0 < mass)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (cells : Finset β) (loc : Fin r → β) (hloc : ∀ v : Fin r, loc v ∈ cells)
    (f : Fin r → TestFun2D)
    (hexp :
      ∫ ω, (∏ i, ω (f i)) ∂(freeFieldMeasure mass hmass) =
        Finset.sum graphs (fun G => graphIntegral G mass))
    (hphi4 : ∀ G ∈ graphs, ∀ v : Fin r, G.legs v = 4)
    (hbound :
      ∀ G ∈ graphs,
        |graphIntegral G mass| ≤
          (∏ v : Fin r, (Nat.factorial (G.legs v) : ℝ) * A ^ (G.legs v)) *
            B ^ G.lines.card) :
    |∫ ω, (∏ i, ω (f i)) ∂(freeFieldMeasure mass hmass)| ≤
      graphs.card *
        ((∏ c ∈ cells,
          (Nat.factorial (4 * ((Finset.univ.filter fun v : Fin r => loc v = c).card)) : ℝ) *
            A ^ (4 * ((Finset.univ.filter fun v : Fin r => loc v = c).card))) *
          B ^ (2 * r)) := by
  let K : ℝ :=
    (∏ c ∈ cells,
      (Nat.factorial (4 * ((Finset.univ.filter fun v : Fin r => loc v = c).card)) : ℝ) *
        A ^ (4 * ((Finset.univ.filter fun v : Fin r => loc v = c).card))) *
      B ^ (2 * r)
  have hgraph : ∀ G ∈ graphs, |graphIntegral G mass| ≤ K := by
    intro G hG
    have hG :
        |graphIntegral G mass| ≤
          (∏ c ∈ cells,
            (Nat.factorial (4 * ((Finset.univ.filter fun v : Fin r => loc v = c).card)) : ℝ) *
              A ^ (4 * ((Finset.univ.filter fun v : Fin r => loc v = c).card))) *
            B ^ (2 * r) :=
      graphIntegral_abs_le_cell_occupancy_weighted_of_phi4_vertex_weighted_bound
        (G := G) (mass := mass) (cells := cells) (loc := loc) hloc
        (A := A) (B := B) hA hB (hphi4 := hphi4 G hG) (hbound := hbound G hG)
    simpa [K] using hG
  rw [hexp]
  have habs :
      |Finset.sum graphs (fun G => graphIntegral G mass)| ≤
        Finset.sum graphs (fun G => |graphIntegral G mass|) := by
    simpa using
      (Finset.abs_sum_le_sum_abs
        (f := fun G : FeynmanGraph r => graphIntegral G mass)
        (s := graphs))
  have hsum :
      Finset.sum graphs (fun G => |graphIntegral G mass|) ≤
        Finset.sum graphs (fun _ => K) := by
    refine Finset.sum_le_sum ?_
    intro G hG
    exact hgraph G hG
  calc
    |Finset.sum graphs (fun G => graphIntegral G mass)|
        ≤ Finset.sum graphs (fun G => |graphIntegral G mass|) := habs
    _ ≤ Finset.sum graphs (fun _ => K) := hsum
    _ = graphs.card * K := by
          simp [Finset.sum_const, nsmul_eq_mul]
    _ = graphs.card *
          ((∏ c ∈ cells,
            (Nat.factorial (4 * ((Finset.univ.filter fun v : Fin r => loc v = c).card)) : ℝ) *
              A ^ (4 * ((Finset.univ.filter fun v : Fin r => loc v = c).card))) *
            B ^ (2 * r)) := by
          simp [K]

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

/- 
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# Perfect Matchings on `Fin n`

Reusable finite combinatorics infrastructure for Wick expansions:

* `Pairing r` is a perfect matching on `Fin r`.
* `halfSplitPairing n` gives an explicit witness on `2n` labels.
* parity/cardinality lemmas: pairings exist on even cardinality and are empty on odd cardinality.
-/

noncomputable section

/-- A pairing of `Fin r` is a perfect matching: a set of disjoint pairs
    that cover all labels exactly once. -/
structure Pairing (r : ℕ) where
  pairs : Finset (Fin r × Fin r)
  covers : ∀ i : Fin r, ∃! p ∈ pairs, p.1 = i ∨ p.2 = i
  ordered : ∀ p ∈ pairs, p.1 < p.2

instance pairingFinite (r : ℕ) : Finite (Pairing r) := by
  classical
  refine Finite.of_injective (fun p : Pairing r => p.pairs) ?_
  intro p q h
  cases p
  cases q
  cases h
  rfl

noncomputable instance pairingFintype (r : ℕ) : Fintype (Pairing r) :=
  Fintype.ofFinite (Pairing r)

private def pairingLeftIdx (n : ℕ) (i : Fin n) : Fin (2 * n) :=
  ⟨i.1, by
    have hi : i.1 < n := i.2
    omega⟩

private def pairingRightIdx (n : ℕ) (i : Fin n) : Fin (2 * n) :=
  ⟨n + i.1, by
    have hi : i.1 < n := i.2
    omega⟩

private def halfSplitPair (n : ℕ) (i : Fin n) : Fin (2 * n) × Fin (2 * n) :=
  (pairingLeftIdx n i, pairingRightIdx n i)

private def halfSplitPairs (n : ℕ) : Finset (Fin (2 * n) × Fin (2 * n)) :=
  Finset.univ.image (halfSplitPair n)

private lemma halfSplitPair_injective (n : ℕ) : Function.Injective (halfSplitPair n) := by
  intro i j hij
  have hfst : pairingLeftIdx n i = pairingLeftIdx n j := congrArg Prod.fst hij
  have hval : i.1 = j.1 := congrArg (fun t : Fin (2 * n) => t.1) hfst
  exact Fin.ext hval

private lemma halfSplitPairs_mem_iff
    (n : ℕ) (p : Fin (2 * n) × Fin (2 * n)) :
    p ∈ halfSplitPairs n ↔ ∃ i : Fin n, halfSplitPair n i = p := by
  constructor
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨i, _, hi⟩
    exact ⟨i, hi⟩
  · intro hp
    rcases hp with ⟨i, rfl⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

/-- Canonical pairing on `2n` labels obtained by pairing each `i < n`
    with `n + i`. -/
def halfSplitPairing (n : ℕ) : Pairing (2 * n) where
  pairs := halfSplitPairs n
  covers := by
    intro j
    by_cases hj : j.1 < n
    · let i : Fin n := ⟨j.1, hj⟩
      refine ⟨halfSplitPair n i, ?_, ?_⟩
      · refine ⟨(halfSplitPairs_mem_iff n (halfSplitPair n i)).2 ⟨i, rfl⟩, Or.inl ?_⟩
        ext
        simp [halfSplitPair, pairingLeftIdx, i]
      · intro p hp
        rcases hp with ⟨hpMem, hpj⟩
        rcases (halfSplitPairs_mem_iff n p).1 hpMem with ⟨k, hk⟩
        have hpj' : (halfSplitPair n k).1 = j ∨ (halfSplitPair n k).2 = j := by
          simpa [hk] using hpj
        rcases hpj' with hkleft | hkright
        · have hkval : k.1 = j.1 := congrArg Fin.val hkleft
          have hkival : k.1 = i.1 := by simpa [i] using hkval
          have hki : k = i := Fin.ext hkival
          calc
            p = halfSplitPair n k := by simp [hk]
            _ = halfSplitPair n i := by simp [hki]
        · exfalso
          have hge : n ≤ j.1 := by
            have hkval : n + k.1 = j.1 := congrArg Fin.val hkright
            omega
          exact (Nat.not_lt.mpr hge) hj
    · have hjn : n ≤ j.1 := Nat.not_lt.mp hj
      have hjlt : j.1 - n < n := by
        have hj2 : j.1 < 2 * n := j.2
        omega
      let i : Fin n := ⟨j.1 - n, hjlt⟩
      refine ⟨halfSplitPair n i, ?_, ?_⟩
      · refine ⟨(halfSplitPairs_mem_iff n (halfSplitPair n i)).2 ⟨i, rfl⟩, Or.inr ?_⟩
        ext
        simp [halfSplitPair, pairingRightIdx, i]
        omega
      · intro p hp
        rcases hp with ⟨hpMem, hpj⟩
        rcases (halfSplitPairs_mem_iff n p).1 hpMem with ⟨k, hk⟩
        have hpj' : (halfSplitPair n k).1 = j ∨ (halfSplitPair n k).2 = j := by
          simpa [hk] using hpj
        rcases hpj' with hkleft | hkright
        · exfalso
          have hlt : j.1 < n := by
            have hkval : k.1 = j.1 := congrArg Fin.val hkleft
            omega
          exact hj hlt
        · have hkval : n + k.1 = j.1 := congrArg Fin.val hkright
          have hkiVal : k.1 = j.1 - n := by omega
          have hkival : k.1 = i.1 := by simpa [i] using hkiVal
          have hki : k = i := Fin.ext hkival
          calc
            p = halfSplitPair n k := by simp [hk]
            _ = halfSplitPair n i := by simp [hki]
  ordered := by
    intro p hp
    rcases (halfSplitPairs_mem_iff n p).1 hp with ⟨i, rfl⟩
    change pairingLeftIdx n i < pairingRightIdx n i
    show i.1 < n + i.1
    omega

namespace Pairing

variable {r : ℕ}

private def coveringPair (π : Pairing r) (i : Fin r) : Fin r × Fin r :=
  Classical.choose (ExistsUnique.exists (π.covers i))

private lemma coveringPair_mem (π : Pairing r) (i : Fin r) :
    coveringPair π i ∈ π.pairs := by
  exact (Classical.choose_spec (ExistsUnique.exists (π.covers i))).1

private lemma coveringPair_contains (π : Pairing r) (i : Fin r) :
    (coveringPair π i).1 = i ∨ (coveringPair π i).2 = i := by
  exact (Classical.choose_spec (ExistsUnique.exists (π.covers i))).2

/-- The unique pair in `π.pairs` that is incident to vertex `i`. -/
def incidentPair (π : Pairing r) (i : Fin r) : Fin r × Fin r :=
  coveringPair π i

/-- The incident pair is indeed a member of `π.pairs`. -/
theorem incidentPair_mem (π : Pairing r) (i : Fin r) :
    π.incidentPair i ∈ π.pairs := by
  exact coveringPair_mem π i

/-- The incident pair contains `i` as one of its two endpoints. -/
theorem incidentPair_contains (π : Pairing r) (i : Fin r) :
    (π.incidentPair i).1 = i ∨ (π.incidentPair i).2 = i := by
  exact coveringPair_contains π i

/-- The partner of `i` in pairing `π`: the other endpoint of `incidentPair i`. -/
def partner (π : Pairing r) (i : Fin r) : Fin r :=
  if _h : (π.incidentPair i).1 = i then (π.incidentPair i).2 else (π.incidentPair i).1

/-- The partner of `i` is distinct from `i`. -/
theorem partner_ne_self (π : Pairing r) (i : Fin r) :
    π.partner i ≠ i := by
  by_cases hleft : (π.incidentPair i).1 = i
  · intro hEq
    have hlt := π.ordered (π.incidentPair i) (π.incidentPair_mem i)
    have hsnd : (π.incidentPair i).2 = i := by
      simpa [partner, hleft] using hEq
    have hlt' : i < i := by
      simp [hleft, hsnd] at hlt
    exact (lt_irrefl _ hlt')
  · intro hEq
    simp [partner, hleft] at hEq

/-- The edge witnessing `partner` is in the pairing. -/
theorem incidentPair_eq_pair_partner_or_partner_pair
    (π : Pairing r) (i : Fin r) :
    π.incidentPair i = (i, π.partner i) ∨
      π.incidentPair i = (π.partner i, i) := by
  unfold partner
  by_cases hleft : (π.incidentPair i).1 = i
  · left
    ext <;> simp [hleft]
  · right
    have hcontains := π.incidentPair_contains i
    rcases hcontains with hfst | hsnd
    · exact False.elim (hleft hfst)
    · ext <;> simp [hleft, hsnd]

/-- One of the two oriented partner pairs belongs to `π.pairs`. -/
theorem pair_partner_mem_or_partner_pair_mem
    (π : Pairing r) (i : Fin r) :
    (i, π.partner i) ∈ π.pairs ∨ (π.partner i, i) ∈ π.pairs := by
  have hmem : π.incidentPair i ∈ π.pairs := π.incidentPair_mem i
  rcases π.incidentPair_eq_pair_partner_or_partner_pair i with h | h
  · left
    simpa [h] using hmem
  · right
    simpa [h] using hmem

private lemma coveringPair_eq_of_mem_contains
    (π : Pairing r) (i : Fin r) (p : Fin r × Fin r)
    (hpMem : p ∈ π.pairs) (hpContains : p.1 = i ∨ p.2 = i) :
    coveringPair π i = p := by
  have hchosen :
      coveringPair π i ∈ π.pairs ∧
        ((coveringPair π i).1 = i ∨ (coveringPair π i).2 = i) :=
    Classical.choose_spec (ExistsUnique.exists (π.covers i))
  exact ExistsUnique.unique (π.covers i) hchosen ⟨hpMem, hpContains⟩

private lemma coveringPair_eq_iff_endpoint
    (π : Pairing r) (i : Fin r) (p : Fin r × Fin r)
    (hpMem : p ∈ π.pairs) :
    coveringPair π i = p ↔ i = p.1 ∨ i = p.2 := by
  constructor
  · intro h
    have hcontains : (coveringPair π i).1 = i ∨ (coveringPair π i).2 = i :=
      coveringPair_contains π i
    rcases hcontains with h1 | h2
    · exact Or.inl (by simpa [h] using h1.symm)
    · exact Or.inr (by simpa [h] using h2.symm)
  · intro hi
    have hpContains : p.1 = i ∨ p.2 = i := by
      rcases hi with hi1 | hi2
      · exact Or.inl hi1.symm
      · exact Or.inr hi2.symm
    exact coveringPair_eq_of_mem_contains π i p hpMem hpContains

/-- If `(i, j)` is an edge of `π`, then it is exactly the incident pair at `i`. -/
theorem incidentPair_eq_of_mem_left
    (π : Pairing r) (i j : Fin r) (hij : (i, j) ∈ π.pairs) :
    π.incidentPair i = (i, j) := by
  unfold incidentPair
  exact coveringPair_eq_of_mem_contains π i (i, j) hij (Or.inl rfl)

/-- If `(j, i)` is an edge of `π`, then it is exactly the incident pair at `i`. -/
theorem incidentPair_eq_of_mem_right
    (π : Pairing r) (i j : Fin r) (hji : (j, i) ∈ π.pairs) :
    π.incidentPair i = (j, i) := by
  unfold incidentPair
  exact coveringPair_eq_of_mem_contains π i (j, i) hji (Or.inr rfl)

/-- If `(i, j)` is an edge of `π`, then `j` is the partner of `i`. -/
theorem partner_eq_of_mem_left
    (π : Pairing r) (i j : Fin r) (hij : (i, j) ∈ π.pairs) :
    π.partner i = j := by
  have hpair : π.incidentPair i = (i, j) := incidentPair_eq_of_mem_left π i j hij
  unfold partner
  simp [hpair]

/-- If `(j, i)` is an edge of `π`, then `j` is the partner of `i`. -/
theorem partner_eq_of_mem_right
    (π : Pairing r) (i j : Fin r) (hji : (j, i) ∈ π.pairs) :
    π.partner i = j := by
  have hpair : π.incidentPair i = (j, i) := incidentPair_eq_of_mem_right π i j hji
  have hneq : j ≠ i := ne_of_lt (π.ordered (j, i) hji)
  unfold partner
  simp [hpair, hneq]

/-- The partner map is an involution on any pairing. -/
theorem partner_partner (π : Pairing r) (i : Fin r) :
    π.partner (π.partner i) = i := by
  rcases pair_partner_mem_or_partner_pair_mem π i with hij | hji
  · let j : Fin r := π.partner i
    have hmem : (i, j) ∈ π.pairs := by simpa [j] using hij
    have hpartner : π.partner j = i :=
      partner_eq_of_mem_right π j i hmem
    simpa [j] using hpartner
  · let j : Fin r := π.partner i
    have hmem : (j, i) ∈ π.pairs := by simpa [j] using hji
    have hpartner : π.partner j = i :=
      partner_eq_of_mem_left π j i hmem
    simpa [j] using hpartner

/-- Any edge in `π.pairs` that contains `i` is the incident pair of `i`. -/
theorem pair_eq_incidentPair_of_mem_contains
    (π : Pairing r) (i : Fin r) (p : Fin r × Fin r)
    (hpMem : p ∈ π.pairs) (hpContains : p.1 = i ∨ p.2 = i) :
    p = π.incidentPair i := by
  have hcov : π.incidentPair i = p := by
    unfold incidentPair
    exact coveringPair_eq_of_mem_contains π i p hpMem hpContains
  exact hcov.symm

/-- Characterization of the unique edge containing `i` in `π.pairs`. -/
theorem mem_filter_contains_iff_eq_incidentPair
    (π : Pairing r) (i : Fin r) (p : Fin r × Fin r) :
    p ∈ π.pairs.filter (fun q => q.1 = i ∨ q.2 = i) ↔ p = π.incidentPair i := by
  constructor
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨hpMem, hpContains⟩
    exact pair_eq_incidentPair_of_mem_contains π i p hpMem hpContains
  · intro hp
    subst hp
    exact Finset.mem_filter.mpr ⟨π.incidentPair_mem i, π.incidentPair_contains i⟩

/-- Exactly one edge of `π.pairs` contains a given vertex `i`. -/
theorem card_filter_pairs_containing_eq_one
    (π : Pairing r) (i : Fin r) :
    (π.pairs.filter (fun p => p.1 = i ∨ p.2 = i)).card = 1 := by
  have hEq :
      π.pairs.filter (fun p => p.1 = i ∨ p.2 = i) = {π.incidentPair i} := by
    ext p
    simpa [Finset.mem_singleton] using
      (mem_filter_contains_iff_eq_incidentPair π i p)
  rw [hEq, Finset.card_singleton]

/-- Erasing the incident pair drops the pair count by one. -/
theorem card_erase_incidentPair
    (π : Pairing r) (i : Fin r) :
    (π.pairs.erase (π.incidentPair i)).card + 1 = π.pairs.card := by
  simpa using Finset.card_erase_add_one (π.incidentPair_mem i)

/-- Equivalent subtraction form of `card_erase_incidentPair`. -/
theorem card_erase_incidentPair_eq_sub_one
    (π : Pairing r) (i : Fin r) :
    (π.pairs.erase (π.incidentPair i)).card = π.pairs.card - 1 := by
  exact Finset.card_erase_of_mem (π.incidentPair_mem i)

/-- The incident pair at `i` also contains `partner i`. -/
theorem incidentPair_contains_partner (π : Pairing r) (i : Fin r) :
    (π.incidentPair i).1 = π.partner i ∨ (π.incidentPair i).2 = π.partner i := by
  rcases π.incidentPair_eq_pair_partner_or_partner_pair i with hpair | hpair
  · right
    simp [hpair]
  · left
    simp [hpair]

/-- `i` and `partner i` share the same incident pair. -/
theorem incidentPair_partner_eq (π : Pairing r) (i : Fin r) :
    π.incidentPair (π.partner i) = π.incidentPair i := by
  have hEq :
      π.incidentPair i = π.incidentPair (π.partner i) :=
    pair_eq_incidentPair_of_mem_contains π (π.partner i) (π.incidentPair i)
      (π.incidentPair_mem i) (π.incidentPair_contains_partner i)
  exact hEq.symm

/-- Endpoint characterization for `incidentPair i`:
    a vertex appears in this pair iff it is `i` or `partner i`. -/
theorem incidentPair_contains_iff_eq_self_or_partner
    (π : Pairing r) (i v : Fin r) :
    ((π.incidentPair i).1 = v ∨ (π.incidentPair i).2 = v) ↔
      (v = i ∨ v = π.partner i) := by
  rcases π.incidentPair_eq_pair_partner_or_partner_pair i with hpair | hpair
  · constructor <;> intro h <;>
      simpa [hpair, eq_comm, or_comm, or_left_comm, or_assoc] using h
  · constructor <;> intro h <;>
      simpa [hpair, eq_comm, or_comm, or_left_comm, or_assoc] using h

/-- Any edge in `erase (incidentPair i)` cannot still contain `i`. -/
theorem not_mem_erase_incidentPair_contains
    (π : Pairing r) (i : Fin r) (p : Fin r × Fin r)
    (hp : p ∈ π.pairs.erase (π.incidentPair i)) :
    ¬ (p.1 = i ∨ p.2 = i) := by
  intro hpContains
  rcases Finset.mem_erase.mp hp with ⟨hpNe, hpMem⟩
  exact hpNe (pair_eq_incidentPair_of_mem_contains π i p hpMem hpContains)

/-- Any edge in `erase (incidentPair i)` cannot contain `partner i`. -/
theorem not_mem_erase_incidentPair_contains_partner
    (π : Pairing r) (i : Fin r) (p : Fin r × Fin r)
    (hp : p ∈ π.pairs.erase (π.incidentPair i)) :
    ¬ (p.1 = π.partner i ∨ p.2 = π.partner i) := by
  intro hpContains
  rcases Finset.mem_erase.mp hp with ⟨hpNe, hpMem⟩
  have hpEqPartner :
      p = π.incidentPair (π.partner i) :=
    pair_eq_incidentPair_of_mem_contains π (π.partner i) p hpMem hpContains
  exact hpNe (hpEqPartner.trans (π.incidentPair_partner_eq i))

/-- Erasing the incident pair removes all edges containing `i`. -/
theorem filter_erase_incidentPair_contains_eq_empty
    (π : Pairing r) (i : Fin r) :
    (π.pairs.erase (π.incidentPair i)).filter (fun p => p.1 = i ∨ p.2 = i) = ∅ := by
  ext p
  constructor
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨hpErase, hpContains⟩
    exact (π.not_mem_erase_incidentPair_contains i p hpErase hpContains).elim
  · intro hp
    simp at hp

/-- Erasing the incident pair removes all edges containing `partner i`. -/
theorem filter_erase_incidentPair_contains_partner_eq_empty
    (π : Pairing r) (i : Fin r) :
    (π.pairs.erase (π.incidentPair i)).filter
        (fun p => p.1 = π.partner i ∨ p.2 = π.partner i) = ∅ := by
  ext p
  constructor
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨hpErase, hpContains⟩
    exact (π.not_mem_erase_incidentPair_contains_partner i p hpErase hpContains).elim
  · intro hp
    simp at hp

private lemma card_endpoint_eq_two
    (π : Pairing r) (p : Fin r × Fin r) (hpMem : p ∈ π.pairs) :
    ({i : Fin r | i = p.1 ∨ i = p.2} : Finset (Fin r)).card = 2 := by
  have hpne : p.1 ≠ p.2 := ne_of_lt (π.ordered p hpMem)
  have hEq :
      ({i : Fin r | i = p.1 ∨ i = p.2} : Finset (Fin r)) = ({p.1, p.2} : Finset (Fin r)) := by
    ext i
    simp
  simp [hEq, hpne]

/-- In any pairing on `r` labels, each pair covers exactly two labels, so
    `2 * |pairs| = r`. -/
theorem two_mul_pairs_card (π : Pairing r) : 2 * π.pairs.card = r := by
  classical
  have hMaps :
      ((Finset.univ : Finset (Fin r)) : Set (Fin r)).MapsTo
        (coveringPair π) (π.pairs : Set (Fin r × Fin r)) := by
    intro i hi
    exact coveringPair_mem π i
  have hCount := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin r)))
    (t := π.pairs)
    (f := coveringPair π)
    hMaps
  have hFiber : ∀ p ∈ π.pairs,
      ({i : Fin r | coveringPair π i = p} : Finset (Fin r)).card = 2 := by
    intro p hp
    have hEq :
        ({i : Fin r | coveringPair π i = p} : Finset (Fin r))
          = ({i : Fin r | i = p.1 ∨ i = p.2} : Finset (Fin r)) := by
      ext i
      simp [coveringPair_eq_iff_endpoint, hp]
    calc
      ({i : Fin r | coveringPair π i = p} : Finset (Fin r)).card
          = ({i : Fin r | i = p.1 ∨ i = p.2} : Finset (Fin r)).card := by simp [hEq]
      _ = 2 := card_endpoint_eq_two π p hp
  have hCount2 : r = ∑ b ∈ π.pairs, 2 := by
    calc
      r = ∑ b ∈ π.pairs, ({a : Fin r | coveringPair π a = b} : Finset (Fin r)).card := by
            simpa [Finset.card_univ] using hCount
      _ = ∑ b ∈ π.pairs, 2 := by
            refine Finset.sum_congr rfl ?_
            intro b hb
            exact hFiber b hb
  have hCount' : r = 2 * π.pairs.card := by
    calc
      r = ∑ b ∈ π.pairs, 2 := hCount2
      _ = π.pairs.card * 2 := by simp
      _ = 2 * π.pairs.card := by omega
  exact hCount'.symm

/-- Any pairing on `r` labels forces `r` to be even. -/
theorem even_card (π : Pairing r) : Even r := by
  refine ⟨π.pairs.card, ?_⟩
  simpa [two_mul] using (two_mul_pairs_card π).symm

/-- The number of pairs is half the number of labels. -/
theorem pairs_card_eq_half (π : Pairing r) :
    π.pairs.card = r / 2 := by
  rcases even_card π with ⟨m, hm⟩
  have h2 : 2 * π.pairs.card = m + m := by
    simpa [hm, two_mul] using two_mul_pairs_card π
  have hcard : π.pairs.card = m := by
    omega
  calc
    π.pairs.card = m := hcard
    _ = (m + m) / 2 := by omega
    _ = r / 2 := by simp [hm]

/-- The erased pair-set has endpoint count identity `2 * |E\\{eᵢ}| = r - 2`. -/
theorem two_mul_card_erase_incidentPair
    (π : Pairing r) (i : Fin r) :
    2 * (π.pairs.erase (π.incidentPair i)).card = r - 2 := by
  rcases even_card π with ⟨m, hm⟩
  have hcard : π.pairs.card = m := by
    have h2 : 2 * π.pairs.card = m + m := by
      simpa [hm, two_mul] using two_mul_pairs_card π
    omega
  have hErase : (π.pairs.erase (π.incidentPair i)).card = m - 1 := by
    simpa [hcard] using card_erase_incidentPair_eq_sub_one π i
  calc
    2 * (π.pairs.erase (π.incidentPair i)).card = 2 * (m - 1) := by simp [hErase]
    _ = m + m - 2 := by omega
    _ = r - 2 := by simp [hm]

/-- Half-cardinality form of `two_mul_card_erase_incidentPair`. -/
theorem card_erase_incidentPair_eq_half_sub_two
    (π : Pairing r) (i : Fin r) :
    (π.pairs.erase (π.incidentPair i)).card = (r - 2) / 2 := by
  have hdiv := congrArg (fun n : ℕ => n / 2) (π.two_mul_card_erase_incidentPair i)
  simpa [Nat.mul_div_right] using hdiv

end Pairing

/-! ## Counting pairings: the double factorial formula

The number of perfect matchings on `2n` labels is `(2n-1)!!`.
The proof is by induction: any pairing on `2(n+1)` labels is determined by
the partner of label `0` (one of `2n+1` choices) and a pairing on the
remaining `2n` labels. -/

/-- Compress `Fin (n+2)` minus two elements `0` and `j` (with `0 < j`) into `Fin n`.
    Elements below `j` are shifted down by 1; elements above `j` by 2. -/
private def compressFin (n : ℕ) (j : Fin (n + 2)) (hj : 0 < j.val)
    (k : Fin (n + 2)) (hk0 : k.val ≠ 0) (hkj : k ≠ j) : Fin n :=
  ⟨if k.val < j.val then k.val - 1 else k.val - 2, by
    have hkj' : k.val ≠ j.val := fun h => hkj (Fin.ext h)
    split_ifs with h <;> omega⟩

/-- Expand `Fin n` back into `Fin (n+2)` avoiding `0` and `j` (with `0 < j`). -/
private def expandFin (n : ℕ) (j : Fin (n + 2)) (_hj : 0 < j.val)
    (k : Fin n) : Fin (n + 2) :=
  if _ : k.val + 1 < j.val then
    ⟨k.val + 1, by omega⟩
  else
    ⟨k.val + 2, by omega⟩

private lemma expandFin_ne_zero (n : ℕ) (j : Fin (n + 2)) (hj : 0 < j.val)
    (k : Fin n) : (expandFin n j hj k).val ≠ 0 := by
  unfold expandFin
  split_ifs <;> simp

private lemma expandFin_ne_j (n : ℕ) (j : Fin (n + 2)) (hj : 0 < j.val)
    (k : Fin n) : expandFin n j hj k ≠ j := by
  unfold expandFin
  intro h
  have hval := congrArg Fin.val h
  split_ifs at hval
  · simp at hval; omega
  · simp at hval; omega

private lemma compressFin_expandFin (n : ℕ) (j : Fin (n + 2)) (hj : 0 < j.val)
    (k : Fin n) :
    compressFin n j hj (expandFin n j hj k)
      (expandFin_ne_zero n j hj k) (expandFin_ne_j n j hj k) = k := by
  unfold expandFin
  split_ifs with h1
  · -- expandFin = ⟨k.val + 1, _⟩
    show compressFin n j hj ⟨k.val + 1, _⟩ _ _ = k
    unfold compressFin; ext
    change (if k.val + 1 < j.val then k.val + 1 - 1 else k.val + 1 - 2) = k.val
    split_ifs; all_goals omega
  · -- expandFin = ⟨k.val + 2, _⟩
    show compressFin n j hj ⟨k.val + 2, _⟩ _ _ = k
    unfold compressFin; ext
    change (if k.val + 2 < j.val then k.val + 2 - 1 else k.val + 2 - 2) = k.val
    split_ifs; all_goals omega

private lemma expandFin_compressFin (n : ℕ) (j : Fin (n + 2)) (hj : 0 < j.val)
    (k : Fin (n + 2)) (hk0 : k.val ≠ 0) (hkj : k ≠ j) :
    expandFin n j hj (compressFin n j hj k hk0 hkj) = k := by
  have hkj' : k.val ≠ j.val := fun h => hkj (Fin.ext h)
  by_cases hk : k.val < j.val
  · -- compressFin = ⟨k.val - 1, _⟩
    have hcomp : compressFin n j hj k hk0 hkj = ⟨k.val - 1, by omega⟩ := by
      unfold compressFin; ext; simp [hk]
    rw [hcomp]; unfold expandFin
    rw [dif_pos (show (⟨k.val - 1, _⟩ : Fin n).val + 1 < j.val from by show k.val - 1 + 1 < j.val; omega)]
    ext; change k.val - 1 + 1 = k.val; omega
  · -- compressFin = ⟨k.val - 2, _⟩
    have hcomp : compressFin n j hj k hk0 hkj = ⟨k.val - 2, by omega⟩ := by
      unfold compressFin; ext; simp [hk]
    rw [hcomp]; unfold expandFin
    rw [dif_neg (show ¬((⟨k.val - 2, _⟩ : Fin n).val + 1 < j.val) from by show ¬(k.val - 2 + 1 < j.val); omega)]
    ext; change k.val - 2 + 2 = k.val; omega

/-- Compress a pair of `Fin (n+2)` values (both ≠ 0, ≠ j) into `Fin n`. -/
private def compressPair (n : ℕ) (j : Fin (n + 2)) (hj : 0 < j.val)
    (p : Fin (n + 2) × Fin (n + 2))
    (hp1_ne0 : p.1.val ≠ 0) (hp1_nej : p.1 ≠ j)
    (hp2_ne0 : p.2.val ≠ 0) (hp2_nej : p.2 ≠ j) :
    Fin n × Fin n :=
  (compressFin n j hj p.1 hp1_ne0 hp1_nej,
   compressFin n j hj p.2 hp2_ne0 hp2_nej)

/-- Expand a pair of `Fin n` values into `Fin (n+2)`. -/
private def expandPair (n : ℕ) (j : Fin (n + 2)) (hj : 0 < j.val)
    (p : Fin n × Fin n) : Fin (n + 2) × Fin (n + 2) :=
  (expandFin n j hj p.1, expandFin n j hj p.2)


/-- compressFin preserves strict order. -/
private lemma compressFin_lt (n : ℕ) (j : Fin (n + 2)) (hj : 0 < j.val)
    (a b : Fin (n + 2))
    (ha0 : a.val ≠ 0) (haj : a ≠ j) (hb0 : b.val ≠ 0) (hbj : b ≠ j)
    (hab : a < b) :
    compressFin n j hj a ha0 haj < compressFin n j hj b hb0 hbj := by
  unfold compressFin
  simp only [Fin.lt_def]
  have haj' : a.val ≠ j.val := fun h => haj (Fin.ext h)
  have hbj' : b.val ≠ j.val := fun h => hbj (Fin.ext h)
  split_ifs <;> omega

/-- compressFin is injective. -/
private lemma compressFin_injective (n : ℕ) (j : Fin (n + 2)) (hj : 0 < j.val)
    (a b : Fin (n + 2))
    (ha0 : a.val ≠ 0) (haj : a ≠ j) (hb0 : b.val ≠ 0) (hbj : b ≠ j)
    (h : compressFin n j hj a ha0 haj = compressFin n j hj b hb0 hbj) :
    a = b := by
  have hval := congrArg Fin.val h
  unfold compressFin at hval
  simp only [] at hval
  have haj' : a.val ≠ j.val := fun h => haj (Fin.ext h)
  have hbj' : b.val ≠ j.val := fun h => hbj (Fin.ext h)
  ext; split_ifs at hval <;> omega

/-- For remaining pairs (after erasing pair at 0), endpoints are ≠ 0 and ≠ partner(0). -/
private lemma remaining_endpoints_valid (n : ℕ) (π : Pairing (2 * n + 2))
    (p : Fin (2 * n + 2) × Fin (2 * n + 2))
    (hp : p ∈ π.pairs.erase (π.incidentPair ⟨0, by omega⟩)) :
    p.1.val ≠ 0 ∧ p.1 ≠ π.partner ⟨0, by omega⟩ ∧
    p.2.val ≠ 0 ∧ p.2 ≠ π.partner ⟨0, by omega⟩ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h; exact π.not_mem_erase_incidentPair_contains ⟨0, by omega⟩ p hp
      (Or.inl (Fin.ext (by omega)))
  · intro h; exact π.not_mem_erase_incidentPair_contains_partner ⟨0, by omega⟩ p hp
      (Or.inl h)
  · intro h; exact π.not_mem_erase_incidentPair_contains ⟨0, by omega⟩ p hp
      (Or.inr (Fin.ext (by omega)))
  · intro h; exact π.not_mem_erase_incidentPair_contains_partner ⟨0, by omega⟩ p hp
      (Or.inr h)

/-- If incidentPairs at i and j are the same, then i shares a vertex with j's pair. -/
private lemma incidentPair_ne_of_no_common_vertex
    {r : ℕ} (π : Pairing r) (i j : Fin r)
    (hi : i ≠ j) (hip : i ≠ π.partner j) :
    π.incidentPair i ≠ π.incidentPair j := by
  intro h
  have := π.incidentPair_contains i
  rw [h] at this
  rw [π.incidentPair_contains_iff_eq_self_or_partner j i] at this
  rcases this with rfl | rfl
  · exact hi rfl
  · exact hip rfl

/-- Total compression: compresses k avoiding 0 and j, with default for invalid inputs.
    Requires `0 < n` for the junk default on invalid inputs. -/
private def compressFinTotal (n : ℕ) (hn : 0 < n) (j : Fin (n + 2)) (hj : 0 < j.val)
    (k : Fin (n + 2)) : Fin n :=
  if hk0 : k.val = 0 then ⟨0, hn⟩
  else if hkj : k = j then ⟨0, hn⟩
  else compressFin n j hj k hk0 hkj

/-- For valid inputs, compressFinTotal equals compressFin. -/
private lemma compressFinTotal_eq_compressFin
    (n : ℕ) (hn : 0 < n) (j : Fin (n + 2)) (hj : 0 < j.val)
    (k : Fin (n + 2)) (hk0 : k.val ≠ 0) (hkj : k ≠ j) :
    compressFinTotal n hn j hj k = compressFin n j hj k hk0 hkj := by
  unfold compressFinTotal; simp [hk0, hkj]

/-- Total pair compression. -/
private def compressPairTotal (n : ℕ) (hn : 0 < n) (j : Fin (n + 2)) (hj : 0 < j.val)
    (p : Fin (n + 2) × Fin (n + 2)) : Fin n × Fin n :=
  (compressFinTotal n hn j hj p.1, compressFinTotal n hn j hj p.2)

/-- compressFinTotal composed with expandFin is the identity. -/
private lemma compressFinTotal_expandFin (n : ℕ) (hn : 0 < n)
    (j : Fin (n + 2)) (hj : 0 < j.val) (k : Fin n) :
    compressFinTotal n hn j hj (expandFin n j hj k) = k := by
  unfold compressFinTotal
  rw [dif_neg (expandFin_ne_zero n j hj k), dif_neg (expandFin_ne_j n j hj k)]
  exact compressFin_expandFin n j hj k

/-- compressFinTotal is injective on valid inputs (those ≠ 0 and ≠ j). -/
private lemma compressFinTotal_injective_valid (n : ℕ) (hn : 0 < n)
    (j : Fin (n + 2)) (hj : 0 < j.val) (a b : Fin (n + 2))
    (ha0 : a.val ≠ 0) (haj : a ≠ j) (hb0 : b.val ≠ 0) (hbj : b ≠ j)
    (h : compressFinTotal n hn j hj a = compressFinTotal n hn j hj b) : a = b := by
  unfold compressFinTotal at h
  rw [dif_neg ha0, dif_neg haj, dif_neg hb0, dif_neg hbj] at h
  exact compressFin_injective n j hj a b ha0 haj hb0 hbj h

/-- expandFin is injective (requires `0 < n` for the compressFinTotal round-trip). -/
private lemma expandFin_injective (n : ℕ) (hn : 0 < n)
    (j : Fin (n + 2)) (hj : 0 < j.val) (a b : Fin n)
    (h : expandFin n j hj a = expandFin n j hj b) : a = b := by
  calc a = compressFinTotal n hn j hj (expandFin n j hj a) := (compressFinTotal_expandFin n hn j hj a).symm
    _ = compressFinTotal n hn j hj (expandFin n j hj b) := congrArg _ h
    _ = b := compressFinTotal_expandFin n hn j hj b

/-- The compressed pairing on `2n` elements after removing the pair at vertex 0
    from a pairing on `2n+2` elements. -/
noncomputable def compressedPairing (n : ℕ) (π : Pairing (2 * n + 2)) :
    Pairing (2 * n) := by
  by_cases hn : n = 0
  · subst hn
    exact ⟨∅, fun i => Fin.elim0 i, fun p hp => absurd hp (Finset.notMem_empty p)⟩
  · have h2n : 0 < 2 * n := by omega
    exact {
      pairs :=
        let zero : Fin (2 * n + 2) := ⟨0, by omega⟩
        let j := π.partner zero
        let hj : 0 < j.val := by
          have h := π.partner_ne_self zero
          have : j.val ≠ 0 := fun heq => h (Fin.ext heq)
          omega
        let remaining := π.pairs.erase (π.incidentPair zero)
        remaining.image (compressPairTotal (2 * n) h2n j hj)
      covers := by
        intro k
        classical
        let zero : Fin (2 * n + 2) := ⟨0, by omega⟩
        let j := π.partner zero
        have hj : 0 < j.val := by
          have h := π.partner_ne_self zero
          have : j.val ≠ 0 := fun heq => h (Fin.ext heq)
          omega
        let remaining := π.pairs.erase (π.incidentPair zero)
        -- k' = expandFin(k) is the preimage in Fin(2n+2)
        let k' := expandFin (2 * n) j hj k
        have hk'0 : k'.val ≠ 0 := expandFin_ne_zero (2 * n) j hj k
        have hk'j : k' ≠ j := expandFin_ne_j (2 * n) j hj k
        -- The incident pair at k' in π
        let q := π.incidentPair k'
        -- q ≠ incidentPair(0) since k' ≠ 0, k' ≠ partner(0) = j
        have hq_ne : q ≠ π.incidentPair zero :=
          incidentPair_ne_of_no_common_vertex π k' zero
            (by intro h; exact hk'0 (congrArg Fin.val h))
            (by intro h; exact hk'j h)
        -- So q ∈ remaining
        have hq_mem : q ∈ remaining :=
          Finset.mem_erase.mpr ⟨hq_ne, π.incidentPair_mem k'⟩
        have hvalid := remaining_endpoints_valid n π q hq_mem
        -- The compressed pair is the image of q
        let cq := compressPairTotal (2 * n) h2n j hj q
        have hcq_mem : cq ∈ remaining.image (compressPairTotal (2 * n) h2n j hj) :=
          Finset.mem_image.mpr ⟨q, hq_mem, rfl⟩
        -- cq covers k: use compressFinTotal_expandFin round-trip
        have hcq_covers : cq.1 = k ∨ cq.2 = k := by
          have hcovers := π.incidentPair_contains k'
          rcases hcovers with h1 | h2
          · left
            have : cq.1 = compressFinTotal (2 * n) h2n j hj k' := by
              change compressFinTotal (2 * n) h2n j hj q.1 = _; exact congr_arg _ h1
            rw [this, show k' = expandFin (2 * n) j hj k from rfl,
                compressFinTotal_expandFin]
          · right
            have : cq.2 = compressFinTotal (2 * n) h2n j hj k' := by
              change compressFinTotal (2 * n) h2n j hj q.2 = _; exact congr_arg _ h2
            rw [this, show k' = expandFin (2 * n) j hj k from rfl,
                compressFinTotal_expandFin]
        -- Existence + uniqueness
        refine ⟨cq, ⟨hcq_mem, hcq_covers⟩, ?_⟩
        -- Uniqueness: any other pair in the image covering k must equal cq
        intro p' ⟨hp'_mem, hp'_covers⟩
        rw [Finset.mem_image] at hp'_mem
        obtain ⟨q', hq'_mem, hq'_eq⟩ := hp'_mem
        have hvalid' := remaining_endpoints_valid n π q' hq'_mem
        -- One component of q' compresses to k, so that component = k' = expandFin k
        have hq'_contains_k' : q'.1 = k' ∨ q'.2 = k' := by
          rcases hp'_covers with hfst | hsnd
          · left
            have h1 : compressFinTotal (2 * n) h2n j hj q'.1 = k := by
              have : p'.1 = k := hfst
              rw [← hq'_eq] at this; exact this
            have h2 : compressFinTotal (2 * n) h2n j hj k' = k :=
              compressFinTotal_expandFin (2 * n) h2n j hj k
            exact compressFinTotal_injective_valid (2 * n) h2n j hj q'.1 k'
              hvalid'.1 hvalid'.2.1 hk'0 hk'j (by rw [h1, h2])
          · right
            have h1 : compressFinTotal (2 * n) h2n j hj q'.2 = k := by
              have : p'.2 = k := hsnd
              rw [← hq'_eq] at this; exact this
            have h2 : compressFinTotal (2 * n) h2n j hj k' = k :=
              compressFinTotal_expandFin (2 * n) h2n j hj k
            exact compressFinTotal_injective_valid (2 * n) h2n j hj q'.2 k'
              hvalid'.2.2.1 hvalid'.2.2.2 hk'0 hk'j (by rw [h1, h2])
        -- q' contains k' and is in π.pairs, so q' = incidentPair k' = q
        have hq'_in_pairs : q' ∈ π.pairs := Finset.mem_of_mem_erase hq'_mem
        have hq'_eq_q : q' = q :=
          π.pair_eq_incidentPair_of_mem_contains k' q' hq'_in_pairs hq'_contains_k'
        rw [← hq'_eq, hq'_eq_q]
      ordered := by
        intro p hp
        rw [Finset.mem_image] at hp
        obtain ⟨q, hq_mem, hq_eq⟩ := hp
        have hord := π.ordered q (Finset.mem_of_mem_erase hq_mem)
        have hvalid := remaining_endpoints_valid n π q hq_mem
        subst hq_eq
        simp only [compressPairTotal, compressFinTotal, dif_neg hvalid.1, dif_neg hvalid.2.1,
          dif_neg hvalid.2.2.1, dif_neg hvalid.2.2.2]
        exact compressFin_lt (2*n) (π.partner ⟨0, by omega⟩)
          (by have h := π.partner_ne_self (⟨0, by omega⟩ : Fin (2*n+2))
              have : (π.partner ⟨0, by omega⟩).val ≠ 0 := fun heq => h (Fin.ext heq)
              omega)
          q.1 q.2 hvalid.1 hvalid.2.1 hvalid.2.2.1 hvalid.2.2.2 hord
    }

/-- Construct a pairing on `2*(n+1)` from a partner choice `j` for vertex 0
    and a pairing `σ` on the remaining `2n` vertices. -/
noncomputable def expandedPairing (n : ℕ) (j : Fin (2 * n + 1)) (σ : Pairing (2 * n)) :
    Pairing (2 * n + 2) := by
  -- j' is the actual partner of 0 in Fin(2n+2): shift j by 1 since j ∈ Fin(2n+1)
  let j' : Fin (2 * n + 2) := ⟨j.val + 1, by omega⟩
  have hj' : (0 : ℕ) < j'.val := by show 0 < j.val + 1; omega
  let zero : Fin (2 * n + 2) := ⟨0, by omega⟩
  -- Build the pair set: {(0, j')} ∪ image of σ.pairs under expandPair
  let ep : Fin (2*n) × Fin (2*n) → Fin (2*n+2) × Fin (2*n+2) :=
    fun q => (expandFin (2*n) j' hj' q.1, expandFin (2*n) j' hj' q.2)
  exact {
    pairs :=
      {(zero, j')} ∪ σ.pairs.image ep
    covers := by
      intro k
      -- unfold ep in all subgoals so types mention expandFin directly
      change ∀ _, _ at *
      by_cases hk0 : k.val = 0
      · refine ⟨(zero, j'), ⟨Finset.mem_union_left _ (Finset.mem_singleton_self _),
          Or.inl (show zero = k from Fin.ext hk0.symm)⟩, ?_⟩
        intro p ⟨hp_mem, hp_covers⟩
        rcases Finset.mem_union.mp hp_mem with hp_new | hp_old
        · exact Finset.mem_singleton.mp hp_new
        · rcases Finset.mem_image.mp hp_old with ⟨q, _, hq_eq⟩
          subst hq_eq; simp only [ep] at hp_covers
          rcases hp_covers with h1 | h2
          · exfalso; exact expandFin_ne_zero (2*n) j' hj' q.1 (by rw [congrArg Fin.val h1, hk0])
          · exfalso; exact expandFin_ne_zero (2*n) j' hj' q.2 (by rw [congrArg Fin.val h2, hk0])
      · by_cases hkj : k = j'
        · subst hkj
          refine ⟨(zero, j'), ⟨Finset.mem_union_left _ (Finset.mem_singleton_self _),
            Or.inr rfl⟩, ?_⟩
          intro p ⟨hp_mem, hp_covers⟩
          rcases Finset.mem_union.mp hp_mem with hp_new | hp_old
          · exact Finset.mem_singleton.mp hp_new
          · rcases Finset.mem_image.mp hp_old with ⟨q, _, hq_eq⟩
            subst hq_eq; simp only [ep] at hp_covers
            rcases hp_covers with h1 | h2
            · exfalso; exact expandFin_ne_j (2*n) j' hj' q.1 h1
            · exfalso; exact expandFin_ne_j (2*n) j' hj' q.2 h2
        · -- k ≠ 0, k ≠ j': covered by the expanded σ
          have hk0' : k.val ≠ 0 := hk0
          have hkj' : k ≠ j' := hkj
          let k' := compressFin (2*n) j' hj' k hk0' hkj'
          obtain ⟨q, ⟨hq_mem, hq_covers⟩, hq_uniq⟩ := σ.covers k'
          refine ⟨ep q, ⟨Finset.mem_union_right _ (Finset.mem_image.mpr ⟨q, hq_mem, rfl⟩), ?_⟩, ?_⟩
          · simp only [ep]
            rcases hq_covers with h1 | h2
            · left
              rw [← expandFin_compressFin (2*n) j' hj' k hk0' hkj']
              exact congrArg _ h1
            · right
              rw [← expandFin_compressFin (2*n) j' hj' k hk0' hkj']
              exact congrArg _ h2
          · intro p' ⟨hp'_mem, hp'_covers⟩
            rcases Finset.mem_union.mp hp'_mem with hp'_new | hp'_old
            · have hp'_eq := Finset.mem_singleton.mp hp'_new
              subst hp'_eq
              rcases hp'_covers with h1 | h2
              · exact absurd (congrArg Fin.val h1).symm hk0
              · exact absurd h2.symm hkj
            · rcases Finset.mem_image.mp hp'_old with ⟨q', hq'_mem, hq'_eq⟩
              subst hq'_eq; simp only [ep] at hp'_covers
              have h2n_pos : 0 < 2 * n := by
                rcases Nat.eq_zero_or_pos n with rfl | hn
                · -- n=0: k ∈ Fin 2, k.val≠0 so k.val=1, but j∈Fin 1 so j'=⟨1,_⟩=k
                  exfalso; exact hkj' (Fin.ext (by omega))
                · omega
              have hq'_covers_k' : q'.1 = k' ∨ q'.2 = k' := by
                rcases hp'_covers with h1 | h2
                · left
                  exact expandFin_injective (2*n) h2n_pos j' hj' q'.1 k' (by
                    rw [h1, expandFin_compressFin])
                · right
                  exact expandFin_injective (2*n) h2n_pos j' hj' q'.2 k' (by
                    rw [h2, expandFin_compressFin])
              have : q' = q := hq_uniq q' ⟨hq'_mem, hq'_covers_k'⟩
              subst this; rfl
    ordered := by
      intro p hp
      rcases Finset.mem_union.mp hp with hp_new | hp_old
      · have := Finset.mem_singleton.mp hp_new
        subst this; show zero < j'
        exact Fin.mk_lt_mk.mpr hj'
      · rcases Finset.mem_image.mp hp_old with ⟨q, hq_mem, hq_eq⟩
        subst hq_eq; simp only [ep]
        show expandFin (2*n) j' hj' q.1 < expandFin (2*n) j' hj' q.2
        have hord := σ.ordered q hq_mem
        unfold expandFin
        split_ifs with h1 h2
        all_goals exact Fin.mk_lt_mk.mpr (by omega)
  }

@[ext]
theorem Pairing.ext' {r : ℕ} {π₁ π₂ : Pairing r} (h : π₁.pairs = π₂.pairs) : π₁ = π₂ := by
  cases π₁; cases π₂; congr

/-- The pair `(0, j+1)` is in the expanded pairing. -/
private lemma expandedPairing_zero_pair_mem (n : ℕ) (j : Fin (2 * n + 1))
    (σ : Pairing (2 * n)) :
    ((⟨0, by omega⟩ : Fin (2 * n + 2)), (⟨j.val + 1, by omega⟩ : Fin (2 * n + 2))) ∈
      (expandedPairing n j σ).pairs := by
  unfold expandedPairing
  exact Finset.mem_union_left _ (Finset.mem_singleton_self _)

/-- The partner of 0 in the expanded pairing is `⟨j.val+1, _⟩`. -/
private lemma expandedPairing_partner_zero (n : ℕ) (j : Fin (2 * n + 1))
    (σ : Pairing (2 * n)) :
    (expandedPairing n j σ).partner ⟨0, by omega⟩ = ⟨j.val + 1, by omega⟩ :=
  Pairing.partner_eq_of_mem_left _ _ _ (expandedPairing_zero_pair_mem n j σ)

/-- The partner index: maps `partner(0)` from `Fin(2n+2)` to `Fin(2n+1)` by subtracting 1.
    Since `partner(0) ∈ {1,...,2n+1}`, this gives a valid `Fin(2n+1)` index. -/
noncomputable def partnerIdx (n : ℕ) (π : Pairing (2 * n + 2)) : Fin (2 * n + 1) :=
  ⟨(π.partner ⟨0, by omega⟩).val - 1, by
    have h := π.partner_ne_self (⟨0, by omega⟩ : Fin (2 * n + 2))
    have hlt := (π.partner ⟨0, by omega⟩).isLt
    have hne : (π.partner ⟨0, by omega⟩).val ≠ 0 := fun heq => h (Fin.ext heq)
    omega⟩

/-- The forward decomposition map: a pairing on `2(n+1)` labels determines
    a partner choice for vertex 0 and a pairing on the remaining `2n` labels. -/
noncomputable def decompPairing (n : ℕ) (π : Pairing (2 * n + 2)) :
    Fin (2 * n + 1) × Pairing (2 * n) :=
  (partnerIdx n π, compressedPairing n π)

/-- The partnerIdx of the expanded pairing recovers `j`. -/
private lemma expandedPairing_partnerIdx (n : ℕ) (j : Fin (2 * n + 1))
    (σ : Pairing (2 * n)) :
    partnerIdx n (expandedPairing n j σ) = j := by
  unfold partnerIdx
  have hp := expandedPairing_partner_zero n j σ
  ext
  simp only [hp]
  omega

/-- The forward map is injective: if two pairings decompose identically,
    they are equal. -/
-- Helper: incidentPair(0) = (0, partner(0)) for pairings on 2n+2 elements
private lemma incidentPair_zero_eq (n : ℕ) (π : Pairing (2 * n + 2)) :
    π.incidentPair ⟨0, by omega⟩ = (⟨0, by omega⟩, π.partner ⟨0, by omega⟩) := by
  have hmem : (⟨0, by omega⟩, π.partner ⟨0, by omega⟩) ∈ π.pairs := by
    rcases π.pair_partner_mem_or_partner_pair_mem ⟨0, by omega⟩ with h | h
    · exact h
    · exfalso
      have hord := π.ordered _ h
      have hne := π.partner_ne_self ⟨0, by omega⟩
      simp only [Fin.lt_def] at hord
      omega
  exact π.incidentPair_eq_of_mem_left _ _ hmem

-- Helper: expandPair ∘ compressPair = id on valid remaining pairs
private lemma expand_compress_remaining {n : ℕ} (π : Pairing (2 * n + 2)) (hn : n ≠ 0)
    (q : Fin (2 * n + 2) × Fin (2 * n + 2))
    (hq : q ∈ π.pairs.erase (π.incidentPair ⟨0, by omega⟩)) :
    let j := π.partner ⟨0, by omega⟩
    let hj : 0 < j.val := by
      have h := π.partner_ne_self (⟨0, by omega⟩ : Fin (2 * n + 2))
      have : j.val ≠ 0 := fun heq => h (Fin.ext heq)
      omega
    (expandFin (2*n) j hj (compressFinTotal (2*n) (by omega) j hj q.1),
     expandFin (2*n) j hj (compressFinTotal (2*n) (by omega) j hj q.2)) = q := by
  have hvalid := remaining_endpoints_valid n π q hq
  have hj : 0 < (π.partner ⟨0, by omega⟩).val := by
    have h := π.partner_ne_self (⟨0, by omega⟩ : Fin (2 * n + 2))
    have : (π.partner ⟨0, by omega⟩).val ≠ 0 := fun heq => h (Fin.ext heq)
    omega
  ext
  · rw [compressFinTotal_eq_compressFin (2*n) (by omega) _ hj q.1 hvalid.1 hvalid.2.1]
    exact congrArg Fin.val (expandFin_compressFin (2*n) _ hj q.1 hvalid.1 hvalid.2.1)
  · rw [compressFinTotal_eq_compressFin (2*n) (by omega) _ hj q.2 hvalid.2.2.1 hvalid.2.2.2]
    exact congrArg Fin.val (expandFin_compressFin (2*n) _ hj q.2 hvalid.2.2.1 hvalid.2.2.2)

private theorem decompPairing_injective (n : ℕ) :
    Function.Injective (decompPairing n) := by
  intro π₁ π₂ h
  have hj : partnerIdx n π₁ = partnerIdx n π₂ := congrArg Prod.fst h
  have hσ : compressedPairing n π₁ = compressedPairing n π₂ := congrArg Prod.snd h
  -- Step 1: same partner(0)
  have hpartner : π₁.partner ⟨0, by omega⟩ = π₂.partner ⟨0, by omega⟩ := by
    apply Fin.ext
    have h1 := congrArg (fun x : Fin (2*n+1) => x.val) hj
    simp only [partnerIdx] at h1
    have hne1 : (π₁.partner ⟨0, by omega⟩).val ≠ 0 :=
      fun heq => π₁.partner_ne_self ⟨0, by omega⟩ (Fin.ext heq)
    have hne2 : (π₂.partner ⟨0, by omega⟩).val ≠ 0 :=
      fun heq => π₂.partner_ne_self ⟨0, by omega⟩ (Fin.ext heq)
    omega
  -- Step 2: same incidentPair(0)
  have hincident : π₁.incidentPair ⟨0, by omega⟩ = π₂.incidentPair ⟨0, by omega⟩ := by
    rw [incidentPair_zero_eq n π₁, incidentPair_zero_eq n π₂, hpartner]
  -- Step 3: show pairs are equal
  apply Pairing.ext'
  rw [← Finset.insert_erase (π₁.incidentPair_mem ⟨0, by omega⟩),
      ← Finset.insert_erase (π₂.incidentPair_mem ⟨0, by omega⟩)]
  rw [hincident]
  congr 1
  -- Need: remaining₁ = remaining₂
  -- Goal: π₁.pairs.erase (π₂.incidentPair ...) = π₂.pairs.erase (π₂.incidentPair ...)
  by_cases hn : n = 0
  · -- n = 0: Pairing 2 has exactly one pair, erasing it gives ∅ on both sides
    subst hn
    -- For Pairing 2, pairs = {incidentPair 0} since every pair must have p.1 = 0
    have hsing : ∀ (π : Pairing (2 * 0 + 2)),
        π.pairs = {π.incidentPair ⟨0, by omega⟩} := by
      intro π
      apply Finset.eq_singleton_iff_unique_mem.mpr
      exact ⟨π.incidentPair_mem ⟨0, by omega⟩, fun p hp =>
        π.pair_eq_incidentPair_of_mem_contains ⟨0, by omega⟩ p hp
          (Or.inl (Fin.ext (by
            have hord := π.ordered p hp; simp only [Fin.lt_def] at hord
            change p.1.val = 0; have := p.1.isLt; have := p.2.isLt; omega)))⟩
    rw [hsing π₁, hsing π₂, hincident]
  · -- n > 0: factor out one-direction subset proof and apply symmetrically
    have hσ_pairs := congrArg Pairing.pairs hσ
    -- Prove: for any two pairings with same partner/incidentPair/compressed,
    -- the remaining pairs of the first are a subset of those of the second
    suffices hsub : ∀ (πa πb : Pairing (2*n+2)),
        πa.partner ⟨0, by omega⟩ = πb.partner ⟨0, by omega⟩ →
        πa.incidentPair ⟨0, by omega⟩ = πb.incidentPair ⟨0, by omega⟩ →
        (compressedPairing n πa).pairs = (compressedPairing n πb).pairs →
        πa.pairs.erase (πb.incidentPair ⟨0, by omega⟩) ⊆
          πb.pairs.erase (πb.incidentPair ⟨0, by omega⟩) by
      exact Finset.Subset.antisymm
        (hsub π₁ π₂ hpartner hincident hσ_pairs)
        (by rw [← hincident]; exact hsub π₂ π₁ hpartner.symm hincident.symm hσ_pairs.symm)
    intro πa πb hpab hinab hσab q hq
    have hq_ne : q ≠ πb.incidentPair ⟨0, by omega⟩ := Finset.ne_of_mem_erase hq
    -- q is also in πa's remaining (using hinab)
    have hqa : q ∈ πa.pairs.erase (πa.incidentPair ⟨0, by omega⟩) := by rwa [hinab]
    -- compress_a(q) ∈ (compressedPairing n πa).pairs
    have hja : 0 < (πa.partner ⟨0, by omega⟩).val := by
      have h := πa.partner_ne_self (⟨0, by omega⟩ : Fin (2*n+2))
      exact Nat.pos_of_ne_zero (fun heq => h (Fin.ext heq))
    have hcq_a : compressPairTotal (2*n) (by omega) (πa.partner ⟨0, by omega⟩) hja q ∈
        (compressedPairing n πa).pairs := by
      unfold compressedPairing; simp only [dif_neg hn]
      exact Finset.mem_image_of_mem _ hqa
    -- By hσab, it's in (compressedPairing n πb).pairs
    rw [hσab] at hcq_a
    -- Unfold to get q' ∈ remaining_b with compress_b(q') = compress_a(q)
    have hjb : 0 < (πb.partner ⟨0, by omega⟩).val := by
      have h := πb.partner_ne_self (⟨0, by omega⟩ : Fin (2*n+2))
      exact Nat.pos_of_ne_zero (fun heq => h (Fin.ext heq))
    unfold compressedPairing at hcq_a; simp only [dif_neg hn] at hcq_a
    rw [Finset.mem_image] at hcq_a
    obtain ⟨q', hq'_mem, hq'_eq⟩ := hcq_a
    -- hq'_eq : compress_b(q') = compress_a(q)
    -- Since πa.partner = πb.partner, rewrite compress_a to compress_b
    simp_rw [hpab] at hq'_eq
    -- Now hq'_eq : compress_b(q') = compress_b(q)
    -- By injectivity of compressFinTotal on valid inputs: q' = q
    have hvalid_a := remaining_endpoints_valid n πa q hqa
    have hvalid_b := remaining_endpoints_valid n πb q' hq'_mem
    -- Rewrite πa.partner to πb.partner in hvalid_a
    rw [hpab] at hvalid_a
    have hq_eq : q' = q := by
      have h1 : (compressPairTotal (2*n) (by omega) (πb.partner ⟨0, by omega⟩) hjb q').1 =
          (compressPairTotal (2*n) (by omega) (πb.partner ⟨0, by omega⟩) hjb q).1 :=
        congrArg Prod.fst hq'_eq
      have h2 : (compressPairTotal (2*n) (by omega) (πb.partner ⟨0, by omega⟩) hjb q').2 =
          (compressPairTotal (2*n) (by omega) (πb.partner ⟨0, by omega⟩) hjb q).2 :=
        congrArg Prod.snd hq'_eq
      simp only [compressPairTotal] at h1 h2
      exact Prod.ext
        (compressFinTotal_injective_valid (2*n) (by omega) _ hjb q'.1 q.1
          hvalid_b.1 hvalid_b.2.1 hvalid_a.1 hvalid_a.2.1 h1)
        (compressFinTotal_injective_valid (2*n) (by omega) _ hjb q'.2 q.2
          hvalid_b.2.2.1 hvalid_b.2.2.2 hvalid_a.2.2.1 hvalid_a.2.2.2 h2)
    rw [← hq_eq]; exact hq'_mem

/-- The incidentPair at 0 in the expanded pairing is `(0, j+1)`. -/
private lemma expandedPairing_incidentPair_zero (n : ℕ) (j : Fin (2 * n + 1))
    (σ : Pairing (2 * n)) :
    (expandedPairing n j σ).incidentPair ⟨0, by omega⟩ =
      ((⟨0, by omega⟩ : Fin (2 * n + 2)), (⟨j.val + 1, by omega⟩ : Fin (2 * n + 2))) :=
  Pairing.incidentPair_eq_of_mem_left _ _ _ (expandedPairing_zero_pair_mem n j σ)

private lemma expandedPairing_compressedPairing (n : ℕ) (j : Fin (2 * n + 1))
    (σ : Pairing (2 * n)) :
    compressedPairing n (expandedPairing n j σ) = σ := by
  by_cases hn : n = 0
  · -- n = 0: both sides are the unique empty pairing
    subst hn
    apply Pairing.ext'
    have hσ : σ.pairs = ∅ := Finset.eq_empty_iff_forall_notMem.mpr
      (fun ⟨⟨a, ha⟩, _⟩ => (Nat.not_lt_zero a ha).elim)
    simp only [compressedPairing, hσ, dif_pos trivial]
  · -- n > 0: show the pairs match
    apply Pairing.ext'
    set π := expandedPairing n j σ with hπ_def
    have hj'pos : (0 : ℕ) < (⟨j.val + 1, by omega⟩ : Fin (2*n+2)).val := by
      show 0 < j.val + 1; omega
    have hpartner : π.partner ⟨0, by omega⟩ = ⟨j.val + 1, by omega⟩ :=
      expandedPairing_partner_zero n j σ
    have hincident : π.incidentPair ⟨0, by omega⟩ =
        ((⟨0, by omega⟩ : Fin (2*n+2)), (⟨j.val + 1, by omega⟩ : Fin (2*n+2))) :=
      expandedPairing_incidentPair_zero n j σ
    have hpairs : π.pairs =
        {((⟨0, by omega⟩ : Fin (2*n+2)), (⟨j.val + 1, by omega⟩ : Fin (2*n+2)))} ∪
        σ.pairs.image (fun q => (expandFin (2*n) ⟨j.val+1, by omega⟩ hj'pos q.1,
                                  expandFin (2*n) ⟨j.val+1, by omega⟩ hj'pos q.2)) := by
      simp only [hπ_def]; unfold expandedPairing; rfl
    -- Unfold compressedPairing for n ≠ 0
    unfold compressedPairing
    simp only [dif_neg hn, hincident, hpairs]
    -- Simplify the erase: {a} ∪ s).erase a = s when a ∉ s
    rw [Finset.singleton_union, Finset.erase_insert_eq_erase]
    have hnotmem : ((⟨0, by omega⟩ : Fin (2*n+2)), (⟨j.val+1, by omega⟩ : Fin (2*n+2))) ∉
        σ.pairs.image (fun q => (expandFin (2*n) ⟨j.val+1, by omega⟩ hj'pos q.1,
                                  expandFin (2*n) ⟨j.val+1, by omega⟩ hj'pos q.2)) := by
      intro hmem
      rw [Finset.mem_image] at hmem
      obtain ⟨q, _, hq_eq⟩ := hmem
      exact expandFin_ne_zero (2*n) ⟨j.val+1, by omega⟩ hj'pos q.1
        (congrArg (fun p : Fin (2*n+2) × Fin (2*n+2) => p.1.val) hq_eq)
    rw [Finset.erase_eq_of_notMem hnotmem]
    -- Helper: compress ∘ expand = id, using nat-level reasoning to avoid dependent type issues
    have hval : (π.partner ⟨0, by omega⟩).val = j.val + 1 := congrArg Fin.val hpartner
    have compress_expand : ∀ (k : Fin (2*n)),
        compressFinTotal (2*n) (by omega) (π.partner ⟨0, by omega⟩)
          (by have h := π.partner_ne_self (⟨0, by omega⟩ : Fin (2*n+2))
              have : (π.partner ⟨0, by omega⟩).val ≠ 0 := fun heq => h (Fin.ext heq)
              omega)
          (expandFin (2*n) ⟨j.val+1, by omega⟩ hj'pos k) = k := by
      intro k
      unfold compressFinTotal
      rw [dif_neg (expandFin_ne_zero (2*n) ⟨j.val+1, by omega⟩ hj'pos k)]
      rw [dif_neg (show expandFin (2*n) ⟨j.val+1, by omega⟩ hj'pos k ≠
          π.partner ⟨0, by omega⟩ by rw [hpartner]; exact expandFin_ne_j _ _ _ _)]
      unfold expandFin
      split_ifs with h1
      · show compressFin (2*n) (π.partner ⟨0, _⟩) _ ⟨k.val + 1, _⟩ _ _ = k
        unfold compressFin; ext
        change (if k.val + 1 < (π.partner ⟨0, _⟩).val then k.val + 1 - 1
                else k.val + 1 - 2) = k.val
        rw [hval]; split_ifs <;> omega
      · show compressFin (2*n) (π.partner ⟨0, _⟩) _ ⟨k.val + 2, _⟩ _ _ = k
        unfold compressFin; ext
        change (if k.val + 2 < (π.partner ⟨0, _⟩).val then k.val + 2 - 1
                else k.val + 2 - 2) = k.val
        rw [hval]; split_ifs <;> omega
    -- Now: image (compressPairTotal ...) (σ.pairs.image ep) = σ.pairs
    ext p
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨q, ⟨q', hq'_mem, hq'_eq⟩, hq_compress⟩
      subst hq'_eq
      have hcomp : (compressPairTotal (2*n) (by omega) (π.partner ⟨0, by omega⟩)
          (by rw [hval]; omega)
          (expandFin (2*n) ⟨j.val+1, by omega⟩ hj'pos q'.1,
           expandFin (2*n) ⟨j.val+1, by omega⟩ hj'pos q'.2)) = q' := by
        unfold compressPairTotal; ext1 <;> exact compress_expand _
      rw [hcomp] at hq_compress; rw [← hq_compress]; exact hq'_mem
    · intro hp_mem
      refine ⟨(expandFin (2*n) ⟨j.val+1, by omega⟩ hj'pos p.1,
               expandFin (2*n) ⟨j.val+1, by omega⟩ hj'pos p.2),
              ⟨p, hp_mem, rfl⟩, ?_⟩
      unfold compressPairTotal; ext1 <;> exact compress_expand _

private theorem decompPairing_surjective (n : ℕ) :
    Function.Surjective (decompPairing n) := by
  intro ⟨j, σ⟩
  exact ⟨expandedPairing n j σ, by
    simp only [decompPairing, Prod.mk.injEq]
    exact ⟨expandedPairing_partnerIdx n j σ, expandedPairing_compressedPairing n j σ⟩⟩

/-- The cardinality recursion: `|Pairing(2(n+1))| = (2n+1) * |Pairing(2n)|`. -/
theorem pairing_card_succ (n : ℕ) :
    Fintype.card (Pairing (2 * (n + 1))) = (2 * n + 1) * Fintype.card (Pairing (2 * n)) := by
  have h2n2 : 2 * (n + 1) = 2 * n + 2 := by omega
  rw [h2n2]
  have hbij : Function.Bijective (decompPairing n) :=
    ⟨decompPairing_injective n, decompPairing_surjective n⟩
  have := Fintype.card_congr (Equiv.ofBijective _ hbij)
  rw [this, Fintype.card_prod, Fintype.card_fin]

/-- The base case: there is exactly one pairing on 0 elements. -/
theorem pairing_zero_card : Fintype.card (Pairing 0) = 1 := by
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨∅, fun i => Fin.elim0 i, fun p hp => by simp_all⟩, ?_⟩
  intro ⟨pairs, covers, ordered⟩
  have hpairs : pairs = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro ⟨⟨a, ha⟩, b⟩
    exact (Nat.not_lt_zero a ha).elim
  subst hpairs; rfl

/-- The double factorial formula: `|Pairing(2n)| = (2n-1)!!`. -/
theorem pairing_card_eq_doubleFactorial (n : ℕ) :
    Fintype.card (Pairing (2 * n)) = Nat.doubleFactorial (2 * n - 1) := by
  induction n with
  | zero => simp [pairing_zero_card]
  | succ n ih =>
    rw [pairing_card_succ n, ih]
    show (2 * n + 1) * Nat.doubleFactorial (2 * n - 1) =
      Nat.doubleFactorial (2 * (n + 1) - 1)
    have h : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
    rw [h]
    conv_rhs => rw [Nat.doubleFactorial.eq_def]
    rcases n with _ | n
    · simp
    · -- 2*(n+1)+1 = (2*n+1).succ.succ
      show (2 * (n + 1) + 1) * (2 * (n + 1) - 1).doubleFactorial =
        (2 * n + 1 + 2) * (2 * n + 1).doubleFactorial
      congr 1

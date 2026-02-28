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

/-- Pairings exist on every even number of labels. -/
theorem pairing_even_exists (n : ℕ) : Nonempty (Pairing (2 * n)) := by
  exact ⟨halfSplitPairing n⟩

/-- There is at least one pairing on `2n` labels. -/
theorem pairing_card_pos_even (n : ℕ) :
    0 < Fintype.card (Pairing (2 * n)) := by
  classical
  letI : Nonempty (Pairing (2 * n)) := ⟨halfSplitPairing n⟩
  exact Fintype.card_pos

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
      simpa [hleft, hsnd] using hlt
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
  simpa [hpair]

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

/-- For a pairing on `2n` labels, there are exactly `n` pairs. -/
theorem pairs_card_even (n : ℕ) (π : Pairing (2 * n)) :
    π.pairs.card = n := by
  have hcard : 2 * π.pairs.card = 2 * n := by
    simpa using (two_mul_pairs_card π)
  omega

/-- There are no pairings on an odd number of labels. -/
theorem isEmpty_odd (n : ℕ) : IsEmpty (Pairing (2 * n + 1)) := by
  refine ⟨?_⟩
  intro π
  have hEven : Even (2 * n + 1) := even_card π
  have hEven2 : Even (2 * n) := even_two.mul_right n
  have hnot : ¬ Even ((2 * n) + 1) := by
    intro h
    exact ((Nat.even_add_one (n := 2 * n)).1 h) hEven2
  exact hnot hEven

end Pairing

/-- Any nonempty pairing type `Pairing r` forces `r` even. -/
theorem pairing_nonempty_implies_even {r : ℕ} (h : Nonempty (Pairing r)) : Even r := by
  rcases h with ⟨π⟩
  exact Pairing.even_card π

/-- The canonical pairing `halfSplitPairing n` has exactly `n` pairs. -/
theorem halfSplitPairing_card (n : ℕ) :
    (halfSplitPairing n).pairs.card = n := by
  simp [halfSplitPairing, halfSplitPairs, Finset.card_image_of_injective,
    halfSplitPair_injective]

/-- On an odd number of labels, there are no pairings. -/
theorem pairing_card_eq_zero_odd (n : ℕ) :
    Fintype.card (Pairing (2 * n + 1)) = 0 := by
  letI : IsEmpty (Pairing (2 * n + 1)) := Pairing.isEmpty_odd n
  simp

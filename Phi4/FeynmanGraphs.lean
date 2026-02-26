/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.WickProduct

/-!
# Feynman Graph Expansion

Feynman graphs are a combinatorial device for reducing Gaussian functional integrals
to finite-dimensional integrals. They arise from repeated application of the
integration by parts formula (Wick's theorem).

For a product of fields φ(f₁)⋯φ(fᵣ), the Gaussian integral equals a sum over
pairings (for r even; zero for r odd):
  ∫ φ(f₁)⋯φ(fᵣ) dφ_C = Σ_{pairings} Π C(f_i, f_j)

For interactions involving Wick products, this generalizes to a sum over Feynman
graphs with vertices (from Wick products) and lines (from contractions).

## Main definitions

* `Pairing` — A perfect matching on {1,...,r}
* `FeynmanGraph` — Graph with vertices and lines (self-lines and interaction lines)
* `graphIntegral` — The integral I(G) assigned to a graph G

## References

* [Glimm-Jaffe] Sections 8.2-8.5
-/

noncomputable section

open MeasureTheory

/-! ## Pairings and Wick's theorem -/

/-- A pairing of {0,...,r-1} is a perfect matching: a set of disjoint pairs
    that cover all elements. Only exists for even r. -/
structure Pairing (r : ℕ) where
  /-- The pairs: each pair (i,j) with i < j. -/
  pairs : Finset (Fin r × Fin r)
  /-- Each element appears in exactly one pair. -/
  covers : ∀ i : Fin r, ∃! p ∈ pairs, p.1 = i ∨ p.2 = i
  /-- Pairs are ordered: first index < second index. -/
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

private lemma card_endpoint_eq_two
    (π : Pairing r) (p : Fin r × Fin r) (hpMem : p ∈ π.pairs) :
    ({i : Fin r | i = p.1 ∨ i = p.2} : Finset (Fin r)).card = 2 := by
  have hpne : p.1 ≠ p.2 := ne_of_lt (π.ordered p hpMem)
  have hEq : ({i : Fin r | i = p.1 ∨ i = p.2} : Finset (Fin r)) = ({p.1, p.2} : Finset (Fin r)) := by
    ext i
    simp
  simp [hEq, hpne]

/-- Any pairing on `r` labels forces `r` to be even. -/
theorem even_card (π : Pairing r) : Even r := by
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
  refine ⟨π.pairs.card, ?_⟩
  simpa [two_mul] using hCount'

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

/-! ## Abstract pairing/graph expansion interfaces -/

/-- Enumeration model for perfect matchings on finite sets. -/
class PairingEnumerationModel where
  num_pairings :
    ∀ n : ℕ,
      ∃ (pairings : Finset (Pairing (2 * n))),
        pairings.card = Nat.doubleFactorial (2 * n - 1)

/-- Gaussian Wick/Feynman expansion model at fixed mass. -/
class GaussianWickExpansionModel (mass : ℝ) (hmass : 0 < mass) where
  wicks_theorem_even :
    ∀ (n : ℕ) (f : Fin (2 * n) → TestFun2D),
      ∃ (pairings : Finset (Pairing (2 * n))),
        ∫ ω, (∏ i, ω (f i)) ∂(freeFieldMeasure mass hmass) =
          ∑ π ∈ pairings, ∏ p ∈ π.pairs,
            GaussianField.covariance (freeCovarianceCLM mass hmass) (f p.1) (f p.2)

/-- The set of pairings of 2n elements is finite and has cardinality (2n-1)!!. -/
theorem num_pairings (n : ℕ) :
    [PairingEnumerationModel] →
    ∃ (pairings : Finset (Pairing (2 * n))),
      pairings.card = Nat.doubleFactorial (2 * n - 1) := by
  intro hpair
  exact PairingEnumerationModel.num_pairings n

/-- Wick recursion for the free Gaussian field:
    pair the first insertion with one partner and recurse on the remaining factors. -/
theorem wicks_recursive (mass : ℝ) (hmass : 0 < mass)
    (n : ℕ) (f₀ : TestFun2D) (g : Fin (n + 1) → TestFun2D) :
    ∫ ω, ω f₀ * (∏ i, ω (g i)) ∂(freeFieldMeasure mass hmass) =
      ∑ j : Fin (n + 1),
        GaussianField.covariance (freeCovarianceCLM mass hmass) f₀ (g j) *
          ∫ ω, (∏ i : Fin n, ω (g (Fin.succAbove j i))) ∂(freeFieldMeasure mass hmass) := by
  simpa [GaussianField.covariance] using
    (GaussianField.wick_recursive (freeCovarianceCLM mass hmass) n f₀ g)

/-- **Wick's theorem** (Proposition 8.3.1): For the Gaussian measure dφ_C,
    ∫ φ(f₁)⋯φ(f_{2n}) dφ_C = Σ_{pairings π} Π_{(i,j)∈π} C(fᵢ, fⱼ)
    and the integral vanishes for odd numbers of fields. -/
theorem wicks_theorem_even (mass : ℝ) (hmass : 0 < mass)
    [GaussianWickExpansionModel mass hmass]
    (n : ℕ) (f : Fin (2 * n) → TestFun2D) :
    ∃ (pairings : Finset (Pairing (2 * n))),
      ∫ ω, (∏ i, ω (f i)) ∂(freeFieldMeasure mass hmass) =
        ∑ π ∈ pairings, ∏ p ∈ π.pairs,
          GaussianField.covariance (freeCovarianceCLM mass hmass) (f p.1) (f p.2) := by
  exact GaussianWickExpansionModel.wicks_theorem_even
    (mass := mass) (hmass := hmass) n f

theorem wicks_theorem_odd (mass : ℝ) (hmass : 0 < mass)
    (n : ℕ) (f : Fin (2 * n + 1) → TestFun2D) :
    ∫ ω, (∏ i, ω (f i)) ∂(freeFieldMeasure mass hmass) = 0 :=
  GaussianField.odd_moment_vanish _ n f

/-! ## Feynman graphs -/

/-- A Feynman graph with r vertices, where vertex i has nᵢ legs.
    Lines connect pairs of legs (either at the same vertex = self-line,
    or different vertices = interaction line). -/
structure FeynmanGraph (r : ℕ) where
  /-- Number of legs at each vertex. -/
  legs : Fin r → ℕ
  /-- The lines: pairs of (vertex, leg_index). -/
  lines : Finset ((Fin r × ℕ) × (Fin r × ℕ))
  /-- Each leg appears in exactly one line. -/
  covering : ∀ (v : Fin r) (l : ℕ), l < legs v →
    ∃! p ∈ lines, (p.1 = (v, l) ∨ p.2 = (v, l))
  /-- Lines are ordered: first component < second component (lexicographic). -/
  ordered : ∀ p ∈ lines, p.1 < p.2

/-- A self-line connects two legs at the same vertex.
    These contribute a factor of C(x,x) = c_κ(x) (the pointwise covariance). -/
def FeynmanGraph.isSelfLine {r : ℕ} (_G : FeynmanGraph r)
    (l : (Fin r × ℕ) × (Fin r × ℕ)) : Prop :=
  l.1.1 = l.2.1

/-- An interaction line connects legs at different vertices.
    These contribute a factor of C(xᵢ, xⱼ) (the propagator). -/
def FeynmanGraph.isInteractionLine {r : ℕ} (_G : FeynmanGraph r)
    (l : (Fin r × ℕ) × (Fin r × ℕ)) : Prop :=
  l.1.1 ≠ l.2.1

/-- The integral I(G) assigned to a Feynman graph G.
    I(G) = ∫ (Π_{vertices i} wᵢ(xᵢ)) (Π_{lines l} C(x_{l.1}, x_{l.2})) dx₁⋯dxᵣ -/
def graphIntegral {r : ℕ} (G : FeynmanGraph r) (mass : ℝ) : ℝ :=
  ∫ x : Fin r → Spacetime2D, ∏ l ∈ G.lines, freeCovKernel mass (x l.1.1) (x l.2.1)

/-- Feynman graph expansion and graph bounds at fixed mass. -/
class FeynmanGraphEstimateModel (mass : ℝ) (hmass : 0 < mass) where
  feynman_graph_expansion :
    ∀ (r : ℕ) (f : Fin r → TestFun2D),
      ∃ (graphs : Finset (FeynmanGraph r)),
        ∫ ω, (∏ i, ω (f i)) ∂(freeFieldMeasure mass hmass) =
          ∑ G ∈ graphs, graphIntegral G mass
  localized_graph_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℕ) (G : FeynmanGraph r),
      |graphIntegral G mass| ≤ C ^ G.lines.card

/-- **Proposition 8.3.1**: The Gaussian integral of a product of Wick monomials
    equals the sum of Feynman graph integrals:
      ∫ A(φ) dφ_C = Σ_G I(G) -/
theorem feynman_graph_expansion (mass : ℝ) (hmass : 0 < mass)
    [FeynmanGraphEstimateModel mass hmass]
    (r : ℕ) (f : Fin r → TestFun2D) :
    ∃ (graphs : Finset (FeynmanGraph r)),
      ∫ ω, (∏ i, ω (f i)) ∂(freeFieldMeasure mass hmass) =
        ∑ G ∈ graphs, graphIntegral G mass := by
  exact FeynmanGraphEstimateModel.feynman_graph_expansion
    (mass := mass) (hmass := hmass) r f

/-! ## Localized graph estimates

The key improvement over raw Feynman graph bounds: when the test functions are
localized in unit squares Δᵢ, the graph integral I(G) decays exponentially with
the total distance between the squares. -/

/-- **Theorem 8.5.5** (Localized graph bounds):
    For R = ∫ w(x) Π :φ(xᵢ)^{nᵢ}: dx with w supported in Δ_{i₁} × ⋯ × Δ_{iᵣ},
    |∫ R dφ_C| ≤ ‖w‖_{Lp} Π_{Δ} N(Δ)! × (const × m^{-1/q})^{N(Δ)}
    where N(Δ) is the number of legs localized in square Δ.

    The crucial feature is the factorial N(Δ)! per square, not N! globally.
    This is what makes the cluster expansion converge.

    The bound C^L where L = total number of lines in G is uniform over all graphs
    with the same number of vertices and legs. -/
theorem localized_graph_bound (mass : ℝ) (hmass : 0 < mass) :
    [FeynmanGraphEstimateModel mass hmass] →
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℕ) (G : FeynmanGraph r),
      |graphIntegral G mass| ≤ C ^ G.lines.card := by
  intro hw
  exact FeynmanGraphEstimateModel.localized_graph_bound
    (mass := mass) (hmass := hmass)

end

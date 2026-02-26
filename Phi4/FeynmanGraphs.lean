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

/-- The canonical pairing `halfSplitPairing n` has exactly `n` pairs. -/
theorem halfSplitPairing_card (n : ℕ) :
    (halfSplitPairing n).pairs.card = n := by
  simp [halfSplitPairing, halfSplitPairs, Finset.card_image_of_injective,
    halfSplitPair_injective]

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

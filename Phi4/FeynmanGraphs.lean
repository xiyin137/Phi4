/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.WickProduct
import Phi4.Combinatorics.PerfectMatchings

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
-- Reusable pairing combinatorics is defined in
-- `Phi4.Combinatorics.PerfectMatchings`.

/-! ## Canonical finite enumeration of pairings -/

/-- Canonical finite enumeration of pairings on `2n` labels. -/
def allPairings (n : ℕ) : Finset (Pairing (2 * n)) := Finset.univ

/-! ## Pairing/graph expansion frontiers -/

/-- Honest theorem-level frontier: the number of perfect matchings on `2n`
    labels equals the double factorial `(2n-1)!!`. -/
theorem gap_pairing_card :
    ∀ n : ℕ, Fintype.card (Pairing (2 * n)) = Nat.doubleFactorial (2 * n - 1) :=
  pairing_card_eq_doubleFactorial

/-- Honest theorem-level frontier: Wick's theorem for even moments under
    the free Gaussian measure. -/
theorem gap_wicks_theorem_even (mass : ℝ) (hmass : 0 < mass) :
    ∀ (n : ℕ) (f : Fin (2 * n) → TestFun2D),
      ∃ (pairings : Finset (Pairing (2 * n))),
        ∫ ω, (∏ i, ω (f i)) ∂(freeFieldMeasure mass hmass) =
          ∑ π ∈ pairings, ∏ p ∈ π.pairs,
            GaussianField.covariance (freeCovarianceCLM mass hmass) (f p.1) (f p.2) := by
  sorry

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
  /-- Every line endpoint is an actual leg of its vertex. -/
  line_valid : ∀ p ∈ lines,
    p.1.2 < legs p.1.1 ∧ p.2.2 < legs p.2.1
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

/-- The smeared graph amplitude A(G, f) for a Feynman graph G with test functions f.
    For Wick's theorem, this is the product over lines of covariance pairings:
    A(G, f) = Π_{lines (i,j)} C(fᵢ, fⱼ) = Π_{lines (i,j)} ∫∫ fᵢ(x) C(x,y) fⱼ(y) dx dy -/
def graphAmplitude {r : ℕ} (G : FeynmanGraph r) (mass : ℝ) (hmass : 0 < mass)
    (f : Fin r → TestFun2D) : ℝ :=
  ∏ l ∈ G.lines,
    GaussianField.covariance (freeCovarianceCLM mass hmass) (f l.1.1) (f l.2.1)

/-- The position-space integral I(G) for a Feynman graph G (no test-function smearing).
    I(G) = ∫ (Π_{lines l} C(x_{l.1}, x_{l.2})) dx₁⋯dxᵣ -/
def graphIntegral {r : ℕ} (G : FeynmanGraph r) (mass : ℝ) : ℝ :=
  ∫ x : Fin r → Spacetime2D, ∏ l ∈ G.lines, freeCovKernel mass (x l.1.1) (x l.2.1)

/-- Graph integral localized by unit balls around prescribed vertex centers.
    This is the natural quantity for distance-decay estimates: each vertex
    variable is constrained to remain within unit distance of its assigned
    center. -/
def localizedGraphIntegral {r : ℕ} (G : FeynmanGraph r) (mass : ℝ)
    (centers : Fin r → Spacetime2D) : ℝ :=
  ∫ x : Fin r → Spacetime2D,
      (∏ i, (Metric.closedBall (centers i) (1 : ℝ)).indicator (fun _ => (1 : ℝ)) (x i)) *
        (∏ l ∈ G.lines, freeCovKernel mass (x l.1.1) (x l.2.1))

/-- Honest theorem-level frontier: Feynman graph expansion of Gaussian
    moments as a sum over graph amplitudes. -/
theorem gap_feynman_graph_expansion (mass : ℝ) (hmass : 0 < mass) :
    ∀ (r : ℕ) (f : Fin r → TestFun2D),
      ∃ (graphs : Finset (FeynmanGraph r)),
        ∫ ω, (∏ i, ω (f i)) ∂(freeFieldMeasure mass hmass) =
          ∑ G ∈ graphs, graphAmplitude G mass hmass f := by
  sorry

/-! ## Localized graph estimates

The key improvement over raw Feynman graph bounds is a distance-decay estimate
for graph integrals localized near prescribed vertex positions.

Note: the simple bound `|graphIntegral G mass| ≤ C ^ G.lines.card` is already
established in `LocalizedBounds.lean` via `localized_graph_bound_of_phi4_weighted_family`
and does not require a gap frontier. The true missing localized bound is the
exponential decay with separation distance for a genuinely localized integral,
stated below.

At present `LocalizedBounds.lean` controls the raw `graphIntegral`; a further
bridge from that infrastructure to `localizedGraphIntegral` is still missing. -/

/-- Honest theorem-level frontier: exponential decay of localized graph integrals
    with separation distance. Here the localization is part of the left-hand
    side through `localizedGraphIntegral`, so the decay bound depends on the
    chosen vertex centers in a mathematically meaningful way. -/
theorem gap_localized_graph_exponential_decay (mass : ℝ) (hmass : 0 < mass) :
    ∃ (C : ℝ) (m : ℝ), 0 < C ∧ 0 < m ∧
      ∀ (r : ℕ) (G : FeynmanGraph r) (centers : Fin r → Spacetime2D),
        |localizedGraphIntegral G mass centers| ≤
          C ^ G.lines.card *
            Real.exp (-m * ∑ l ∈ G.lines, dist (centers l.1.1) (centers l.2.1)) := by
  sorry

end

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

/-- The set of pairings of 2n elements is finite and has cardinality (2n-1)!!. -/
theorem num_pairings (n : ℕ) :
    ∃ (pairings : Finset (Pairing (2 * n))),
      pairings.card = Nat.doubleFactorial (2 * n - 1) := by
  sorry

/-- **Wick's theorem** (Proposition 8.3.1): For the Gaussian measure dφ_C,
    ∫ φ(f₁)⋯φ(f_{2n}) dφ_C = Σ_{pairings π} Π_{(i,j)∈π} C(fᵢ, fⱼ)
    and the integral vanishes for odd numbers of fields. -/
theorem wicks_theorem_even (mass : ℝ) (hmass : 0 < mass)
    (n : ℕ) (f : Fin (2 * n) → TestFun2D) :
    ∃ (pairings : Finset (Pairing (2 * n))),
      ∫ ω, (∏ i, ω (f i)) ∂(freeFieldMeasure mass hmass) =
        ∑ π ∈ pairings, ∏ p ∈ π.pairs,
          GaussianField.covariance (freeCovarianceCLM mass hmass) (f p.1) (f p.2) := by
  sorry

theorem wicks_theorem_odd (mass : ℝ) (hmass : 0 < mass)
    (n : ℕ) (f : Fin (2 * n + 1) → TestFun2D) :
    ∫ ω, (∏ i, ω (f i)) ∂(freeFieldMeasure mass hmass) = 0 := by
  sorry

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
def FeynmanGraph.isSelfLine {r : ℕ} (G : FeynmanGraph r)
    (l : (Fin r × ℕ) × (Fin r × ℕ)) : Prop :=
  l.1.1 = l.2.1

/-- An interaction line connects legs at different vertices.
    These contribute a factor of C(xᵢ, xⱼ) (the propagator). -/
def FeynmanGraph.isInteractionLine {r : ℕ} (G : FeynmanGraph r)
    (l : (Fin r × ℕ) × (Fin r × ℕ)) : Prop :=
  l.1.1 ≠ l.2.1

/-- The integral I(G) assigned to a Feynman graph G.
    I(G) = ∫ (Π_{vertices i} wᵢ(xᵢ)) (Π_{lines l} C(x_{l.1}, x_{l.2})) dx₁⋯dxᵣ -/
def graphIntegral {r : ℕ} (G : FeynmanGraph r) (mass : ℝ) : ℝ := by
  sorry

/-- **Proposition 8.3.1**: The Gaussian integral of a product of Wick monomials
    equals the sum of Feynman graph integrals:
      ∫ A(φ) dφ_C = Σ_G I(G) -/
theorem feynman_graph_expansion (mass : ℝ) (hmass : 0 < mass)
    (r : ℕ) (f : Fin r → TestFun2D) :
    ∃ (graphs : Finset (FeynmanGraph r)),
      ∫ ω, (∏ i, ω (f i)) ∂(freeFieldMeasure mass hmass) =
        ∑ G ∈ graphs, graphIntegral G mass := by
  sorry

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
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℕ) (G : FeynmanGraph r),
      |graphIntegral G mass| ≤ C ^ G.lines.card := by
  sorry

end

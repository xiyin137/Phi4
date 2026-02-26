/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.MultipleReflections
import Phi4.CorrelationInequalities

/-!
# Infinite Volume Limit

The infinite volume limit is the construction of the φ⁴₂ measure on S'(ℝ²) as the
limit of finite-volume measures dμ_Λ as Λ ↗ ℝ².

The proof strategy (Glimm-Jaffe Chapter 11) combines:
1. **Monotone convergence**: Schwinger functions S_n^Λ are monotone increasing in Λ
   (for non-negative test functions), by the GKS second inequality.
2. **Uniform upper bounds**: S_n^Λ ≤ C uniform in Λ, by the multiple reflection bounds.

Together, monotone + bounded ⟹ convergent.

The interaction is P = λφ⁴ (even polynomial + possibly linear term), and we use
Dirichlet boundary conditions.

## Main results

* `schwinger_monotone_in_volume` — S_n^Λ increases with Λ
* `schwinger_uniformly_bounded` — S_n^Λ bounded uniformly in Λ
* `infinite_volume_schwinger_exists` — lim_{Λ↗ℝ²} S_n^Λ(f) exists
* `infiniteVolumeMeasure` — the φ⁴₂ probability measure on S'(ℝ²)

## References

* [Glimm-Jaffe] Chapter 11
-/

noncomputable section

open MeasureTheory

/-! ## Monotone convergence of Schwinger functions -/

/-- The sequence of rectangles Λₙ = [-n, n] × [-n, n] exhausting ℝ².
    These serve as the volume cutoffs for the infinite volume limit. -/
def exhaustingRectangles (n : ℕ) (hn : 0 < n) : Rectangle :=
  Rectangle.symmetric n n (Nat.cast_pos.mpr hn) (Nat.cast_pos.mpr hn)

/-- Monotonicity of the exhausting rectangles as sets. -/
private lemma exhaustingRectangles_mono_toSet
    (n₁ n₂ : ℕ) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (h : n₁ ≤ n₂) :
    (exhaustingRectangles n₁ hn₁).toSet ⊆ (exhaustingRectangles n₂ hn₂).toSet := by
  intro x hx
  rcases hx with ⟨hx0min, hx0max, hx1min, hx1max⟩
  have hcast : (n₁ : ℝ) ≤ (n₂ : ℝ) := by exact_mod_cast h
  have hx0min' : (-(n₁ : ℝ)) ≤ x 0 := by
    simpa [exhaustingRectangles, Rectangle.symmetric] using hx0min
  have hx0max' : x 0 ≤ (n₁ : ℝ) := by
    simpa [exhaustingRectangles, Rectangle.symmetric] using hx0max
  have hx1min' : (-(n₁ : ℝ)) ≤ x 1 := by
    simpa [exhaustingRectangles, Rectangle.symmetric] using hx1min
  have hx1max' : x 1 ≤ (n₁ : ℝ) := by
    simpa [exhaustingRectangles, Rectangle.symmetric] using hx1max
  have hx0min2 : (-(n₂ : ℝ)) ≤ x 0 := by linarith
  have hx0max2 : x 0 ≤ (n₂ : ℝ) := by linarith
  have hx1min2 : (-(n₂ : ℝ)) ≤ x 1 := by linarith
  have hx1max2 : x 1 ≤ (n₂ : ℝ) := by linarith
  simpa [Rectangle.toSet, exhaustingRectangles, Rectangle.symmetric] using
    (show (-(n₂ : ℝ) ≤ x 0 ∧ x 0 ≤ (n₂ : ℝ) ∧
        -(n₂ : ℝ) ≤ x 1 ∧ x 1 ≤ (n₂ : ℝ)) from
      ⟨hx0min2, hx0max2, hx1min2, hx1max2⟩)

/-- **Monotone convergence**: The 2-point Schwinger function increases with volume.
    For Λ₁ ⊂ Λ₂ and non-negative test functions f, g ≥ 0:
      S₂^{Λ₁}(f,g) ≤ S₂^{Λ₂}(f,g)

    Proof: Combines Dirichlet monotonicity (enlarging Λ relaxes the BC,
    increasing the covariance) with GKS-II (the 2-point function is
    monotone in the covariance for the φ⁴ interaction). -/
theorem schwinger_monotone_in_volume (params : Phi4Params)
    [CorrelationInequalityModel params]
    (n₁ n₂ : ℕ) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (h : n₁ ≤ n₂)
    (f g : TestFun2D) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupp : ∀ x ∉ (exhaustingRectangles n₁ hn₁).toSet, f x = 0)
    (hgsupp : ∀ x ∉ (exhaustingRectangles n₁ hn₁).toSet, g x = 0) :
    schwingerTwo params (exhaustingRectangles n₁ hn₁) f g ≤
      schwingerTwo params (exhaustingRectangles n₂ hn₂) f g := by
  exact schwinger_two_monotone params
    (exhaustingRectangles n₁ hn₁) (exhaustingRectangles n₂ hn₂)
    (exhaustingRectangles_mono_toSet n₁ n₂ hn₁ hn₂ h)
    f g hf hg hfsupp hgsupp

/-- Lattice-bridge variant of two-point monotonicity in volume. -/
theorem schwinger_monotone_in_volume_from_lattice (params : Phi4Params)
    [LatticeSchwingerTwoMonotoneModel params]
    (n₁ n₂ : ℕ) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (h : n₁ ≤ n₂)
    (f g : TestFun2D) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupp : ∀ x ∉ (exhaustingRectangles n₁ hn₁).toSet, f x = 0)
    (hgsupp : ∀ x ∉ (exhaustingRectangles n₁ hn₁).toSet, g x = 0) :
    schwingerTwo params (exhaustingRectangles n₁ hn₁) f g ≤
      schwingerTwo params (exhaustingRectangles n₂ hn₂) f g := by
  exact schwinger_two_monotone_from_lattice params
    (exhaustingRectangles n₁ hn₁) (exhaustingRectangles n₂ hn₂)
    (exhaustingRectangles_mono_toSet n₁ n₂ hn₁ hn₂ h)
    f g hf hg hfsupp hgsupp

/-- Monotonicity of the `n = 2` Schwinger function in `schwingerN` form. -/
theorem schwingerN_monotone_in_volume_two (params : Phi4Params)
    [CorrelationInequalityModel params]
    (n₁ n₂ : ℕ) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (h : n₁ ≤ n₂)
    (f : Fin 2 → TestFun2D) (hf : ∀ i, ∀ x, 0 ≤ f i x)
    (hfsupp : ∀ i, ∀ x ∉ (exhaustingRectangles n₁ hn₁).toSet, f i x = 0) :
    schwingerN params (exhaustingRectangles n₁ hn₁) 2 f ≤
      schwingerN params (exhaustingRectangles n₂ hn₂) 2 f := by
  have hmono := schwinger_monotone_in_volume params n₁ n₂ hn₁ hn₂ h
    (f 0) (f 1) (hf 0) (hf 1) (hfsupp 0) (hfsupp 1)
  simpa [schwingerN_two_eq_schwingerTwo] using hmono

/-- Lattice-bridge variant of `k = 2` monotonicity in `schwingerN` form. -/
theorem schwingerN_monotone_in_volume_two_from_lattice (params : Phi4Params)
    [LatticeSchwingerTwoMonotoneModel params]
    (n₁ n₂ : ℕ) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (h : n₁ ≤ n₂)
    (f : Fin 2 → TestFun2D) (hf : ∀ i, ∀ x, 0 ≤ f i x)
    (hfsupp : ∀ i, ∀ x ∉ (exhaustingRectangles n₁ hn₁).toSet, f i x = 0) :
    schwingerN params (exhaustingRectangles n₁ hn₁) 2 f ≤
      schwingerN params (exhaustingRectangles n₂ hn₂) 2 f := by
  have hmono := schwinger_monotone_in_volume_from_lattice params n₁ n₂ hn₁ hn₂ h
    (f 0) (f 1) (hf 0) (hf 1) (hfsupp 0) (hfsupp 1)
  simpa [schwingerN_two_eq_schwingerTwo] using hmono

/-- Monotonicity for `schwingerN` in the currently established case `k = 2`,
    reduced to `schwinger_monotone_in_volume`. -/
theorem schwingerN_monotone_in_volume (params : Phi4Params)
    [CorrelationInequalityModel params]
    (n₁ n₂ : ℕ) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (h : n₁ ≤ n₂)
    (k : ℕ) (f : Fin k → TestFun2D) (hf : ∀ i, ∀ x, 0 ≤ f i x)
    (hfsupp : ∀ i, ∀ x ∉ (exhaustingRectangles n₁ hn₁).toSet, f i x = 0)
    (hk : k = 2) :
    schwingerN params (exhaustingRectangles n₁ hn₁) k f ≤
      schwingerN params (exhaustingRectangles n₂ hn₂) k f := by
  subst hk
  exact schwingerN_monotone_in_volume_two params n₁ n₂ hn₁ hn₂ h f hf hfsupp

/-- Lattice-bridge variant of `schwingerN` monotonicity in the established case `k = 2`. -/
theorem schwingerN_monotone_in_volume_from_lattice (params : Phi4Params)
    [LatticeSchwingerTwoMonotoneModel params]
    (n₁ n₂ : ℕ) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (h : n₁ ≤ n₂)
    (k : ℕ) (f : Fin k → TestFun2D) (hf : ∀ i, ∀ x, 0 ≤ f i x)
    (hfsupp : ∀ i, ∀ x ∉ (exhaustingRectangles n₁ hn₁).toSet, f i x = 0)
    (hk : k = 2) :
    schwingerN params (exhaustingRectangles n₁ hn₁) k f ≤
      schwingerN params (exhaustingRectangles n₂ hn₂) k f := by
  subst hk
  exact schwingerN_monotone_in_volume_two_from_lattice
    params n₁ n₂ hn₁ hn₂ h f hf hfsupp

private lemma support_zero_outside_of_subset
    (f : TestFun2D) {A B : Set Spacetime2D}
    (hAB : A ⊆ B)
    (hfA : ∀ x ∉ A, f x = 0) :
    ∀ x ∉ B, f x = 0 := by
  intro x hxB
  exact hfA x (fun hxA => hxB (hAB hxA))

private theorem tendsto_iSup_of_monotone_abs_bounded
    (a : ℕ → ℝ)
    (hmono : Monotone a)
    (hbound : ∃ C : ℝ, ∀ n : ℕ, |a n| ≤ C) :
    Filter.Tendsto a Filter.atTop (nhds (⨆ n : ℕ, a n)) := by
  rcases hbound with ⟨C, hC⟩
  have hbdd : BddAbove (Set.range a) := by
    refine ⟨C, ?_⟩
    rintro y ⟨n, rfl⟩
    exact le_trans (le_abs_self _) (hC n)
  exact tendsto_atTop_ciSup hmono hbdd

/-- Convergence of the two-point finite-volume sequence from:
    1. positivity-preserving test functions with support in a base rectangle,
    2. volume monotonicity (`CorrelationInequalityModel`), and
    3. an explicit uniform absolute bound.

    The limit is identified with the supremum over the exhaustion sequence. -/
theorem schwingerTwo_tendsto_iSup_of_monotone_bounded
    (params : Phi4Params)
    [CorrelationInequalityModel params]
    (n0 : ℕ)
    (f g : TestFun2D) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupp0 : ∀ x ∉ (exhaustingRectangles (n0 + 1) (Nat.succ_pos n0)).toSet, f x = 0)
    (hgsupp0 : ∀ x ∉ (exhaustingRectangles (n0 + 1) (Nat.succ_pos n0)).toSet, g x = 0)
    (hbound : ∃ C : ℝ, ∀ n : ℕ,
      |schwingerTwo params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) f g| ≤ C) :
    Filter.Tendsto
      (fun n : ℕ => schwingerTwo params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) f g)
      Filter.atTop
      (nhds (⨆ n : ℕ,
        schwingerTwo params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) f g)) := by
  have hmono : Monotone (fun n : ℕ =>
      schwingerTwo params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) f g) := by
    intro n m hnm
    have hle : n + n0 + 1 ≤ m + n0 + 1 := by
      exact Nat.add_le_add_right hnm (n0 + 1)
    have hsub0n :
        (exhaustingRectangles (n0 + 1) (Nat.succ_pos n0)).toSet ⊆
          (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)).toSet :=
      exhaustingRectangles_mono_toSet
        (n0 + 1) (n + n0 + 1)
        (Nat.succ_pos n0) (Nat.succ_pos (n + n0)) (by omega)
    have hfsuppn :
        ∀ x ∉ (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)).toSet, f x = 0 :=
      support_zero_outside_of_subset f hsub0n hfsupp0
    have hgsuppn :
        ∀ x ∉ (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)).toSet, g x = 0 :=
      support_zero_outside_of_subset g hsub0n hgsupp0
    exact schwinger_monotone_in_volume params
      (n + n0 + 1) (m + n0 + 1)
      (Nat.succ_pos (n + n0)) (Nat.succ_pos (m + n0)) hle
      f g hf hg hfsuppn hgsuppn
  exact tendsto_iSup_of_monotone_abs_bounded
    (fun n : ℕ => schwingerTwo params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) f g)
    hmono hbound

/-- Lattice-bridge variant of monotone-bounded convergence for the finite-volume
    two-point sequence. -/
theorem schwingerTwo_tendsto_iSup_of_lattice_monotone_bounded
    (params : Phi4Params)
    [LatticeSchwingerTwoMonotoneModel params]
    (n0 : ℕ)
    (f g : TestFun2D) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupp0 : ∀ x ∉ (exhaustingRectangles (n0 + 1) (Nat.succ_pos n0)).toSet, f x = 0)
    (hgsupp0 : ∀ x ∉ (exhaustingRectangles (n0 + 1) (Nat.succ_pos n0)).toSet, g x = 0)
    (hbound : ∃ C : ℝ, ∀ n : ℕ,
      |schwingerTwo params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) f g| ≤ C) :
    Filter.Tendsto
      (fun n : ℕ => schwingerTwo params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) f g)
      Filter.atTop
      (nhds (⨆ n : ℕ,
        schwingerTwo params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) f g)) := by
  have hmono : Monotone (fun n : ℕ =>
      schwingerTwo params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) f g) := by
    intro n m hnm
    have hle : n + n0 + 1 ≤ m + n0 + 1 := by
      exact Nat.add_le_add_right hnm (n0 + 1)
    have hsub0n :
        (exhaustingRectangles (n0 + 1) (Nat.succ_pos n0)).toSet ⊆
          (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)).toSet :=
      exhaustingRectangles_mono_toSet
        (n0 + 1) (n + n0 + 1)
        (Nat.succ_pos n0) (Nat.succ_pos (n + n0)) (by omega)
    have hfsuppn :
        ∀ x ∉ (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)).toSet, f x = 0 :=
      support_zero_outside_of_subset f hsub0n hfsupp0
    have hgsuppn :
        ∀ x ∉ (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)).toSet, g x = 0 :=
      support_zero_outside_of_subset g hsub0n hgsupp0
    exact schwinger_monotone_in_volume_from_lattice params
      (n + n0 + 1) (m + n0 + 1)
      (Nat.succ_pos (n + n0)) (Nat.succ_pos (m + n0)) hle
      f g hf hg hfsuppn hgsuppn
  exact tendsto_iSup_of_monotone_abs_bounded
    (fun n : ℕ => schwingerTwo params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) f g)
    hmono hbound

/-- Existence form of `schwingerTwo_tendsto_iSup_of_monotone_bounded`. -/
theorem schwingerTwo_limit_exists_of_monotone_bounded
    (params : Phi4Params)
    [CorrelationInequalityModel params]
    (n0 : ℕ)
    (f g : TestFun2D) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupp0 : ∀ x ∉ (exhaustingRectangles (n0 + 1) (Nat.succ_pos n0)).toSet, f x = 0)
    (hgsupp0 : ∀ x ∉ (exhaustingRectangles (n0 + 1) (Nat.succ_pos n0)).toSet, g x = 0)
    (hbound : ∃ C : ℝ, ∀ n : ℕ,
      |schwingerTwo params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) f g| ≤ C) :
    ∃ S : ℝ,
      Filter.Tendsto
        (fun n : ℕ => schwingerTwo params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) f g)
        Filter.atTop (nhds S) := by
  refine ⟨⨆ n : ℕ, schwingerTwo params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) f g, ?_⟩
  exact schwingerTwo_tendsto_iSup_of_monotone_bounded
    params n0 f g hf hg hfsupp0 hgsupp0 hbound

/-- `schwingerN` (`k = 2`) form of monotone-bounded convergence. -/
theorem schwingerN_two_tendsto_iSup_of_monotone_bounded
    (params : Phi4Params)
    [CorrelationInequalityModel params]
    (n0 : ℕ)
    (f : Fin 2 → TestFun2D)
    (hf : ∀ i, ∀ x, 0 ≤ f i x)
    (hfsupp0 : ∀ i,
      ∀ x ∉ (exhaustingRectangles (n0 + 1) (Nat.succ_pos n0)).toSet, f i x = 0)
    (hbound : ∃ C : ℝ, ∀ n : ℕ,
      |schwingerN params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) 2 f| ≤ C) :
    Filter.Tendsto
      (fun n : ℕ => schwingerN params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) 2 f)
      Filter.atTop
      (nhds (⨆ n : ℕ,
        schwingerN params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) 2 f)) := by
  have hboundTwo : ∃ C : ℝ, ∀ n : ℕ,
      |schwingerTwo params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) (f 0) (f 1)| ≤ C := by
    rcases hbound with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro n
    simpa [schwingerN_two_eq_schwingerTwo] using hC n
  have hTwo := schwingerTwo_tendsto_iSup_of_monotone_bounded
    params n0 (f 0) (f 1) (hf 0) (hf 1) (hfsupp0 0) (hfsupp0 1) hboundTwo
  simpa [schwingerN_two_eq_schwingerTwo] using hTwo

/-- Lattice-bridge `schwingerN` (`k = 2`) form of monotone-bounded convergence. -/
theorem schwingerN_two_tendsto_iSup_of_lattice_monotone_bounded
    (params : Phi4Params)
    [LatticeSchwingerTwoMonotoneModel params]
    (n0 : ℕ)
    (f : Fin 2 → TestFun2D)
    (hf : ∀ i, ∀ x, 0 ≤ f i x)
    (hfsupp0 : ∀ i,
      ∀ x ∉ (exhaustingRectangles (n0 + 1) (Nat.succ_pos n0)).toSet, f i x = 0)
    (hbound : ∃ C : ℝ, ∀ n : ℕ,
      |schwingerN params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) 2 f| ≤ C) :
    Filter.Tendsto
      (fun n : ℕ => schwingerN params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) 2 f)
      Filter.atTop
      (nhds (⨆ n : ℕ,
        schwingerN params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) 2 f)) := by
  have hboundTwo : ∃ C : ℝ, ∀ n : ℕ,
      |schwingerTwo params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) (f 0) (f 1)| ≤ C := by
    rcases hbound with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro n
    simpa [schwingerN_two_eq_schwingerTwo] using hC n
  have hTwo := schwingerTwo_tendsto_iSup_of_lattice_monotone_bounded
    params n0 (f 0) (f 1) (hf 0) (hf 1) (hfsupp0 0) (hfsupp0 1) hboundTwo
  simpa [schwingerN_two_eq_schwingerTwo] using hTwo

/-- Existence form of `schwingerN_two_tendsto_iSup_of_monotone_bounded`. -/
theorem schwingerN_two_limit_exists_of_monotone_bounded
    (params : Phi4Params)
    [CorrelationInequalityModel params]
    (n0 : ℕ)
    (f : Fin 2 → TestFun2D)
    (hf : ∀ i, ∀ x, 0 ≤ f i x)
    (hfsupp0 : ∀ i,
      ∀ x ∉ (exhaustingRectangles (n0 + 1) (Nat.succ_pos n0)).toSet, f i x = 0)
    (hbound : ∃ C : ℝ, ∀ n : ℕ,
      |schwingerN params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) 2 f| ≤ C) :
    ∃ S : ℝ,
      Filter.Tendsto
        (fun n : ℕ => schwingerN params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) 2 f)
        Filter.atTop (nhds S) := by
  refine ⟨⨆ n : ℕ, schwingerN params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) 2 f, ?_⟩
  exact schwingerN_two_tendsto_iSup_of_monotone_bounded params n0 f hf hfsupp0 hbound

/-! ## Uniform upper bounds -/

/-- Model of infinite-volume existence data: uniform bounds, limiting Schwinger
    functions, and a representing infinite-volume measure. -/
class InfiniteVolumeLimitModel (params : Phi4Params) where
  schwinger_uniformly_bounded :
    ∀ (k : ℕ) (f : Fin k → TestFun2D),
      ∃ C : ℝ, ∀ (n : ℕ) (hn : 0 < n),
        |schwingerN params (exhaustingRectangles n hn) k f| ≤ C
  infiniteVolumeSchwinger : ∀ (k : ℕ), (Fin k → TestFun2D) → ℝ
  infiniteVolumeSchwinger_tendsto :
    ∀ (k : ℕ) (f : Fin k → TestFun2D),
      Filter.Tendsto
        (fun n : ℕ =>
          if h : 0 < n then schwingerN params (exhaustingRectangles n h) k f else 0)
        Filter.atTop
        (nhds (infiniteVolumeSchwinger k f))
  infiniteVolumeMeasure :
    @Measure FieldConfig2D GaussianField.instMeasurableSpaceConfiguration
  infiniteVolumeMeasure_isProbability :
    IsProbabilityMeasure infiniteVolumeMeasure
  infiniteVolumeSchwinger_is_moment :
    ∀ (k : ℕ) (f : Fin k → TestFun2D),
      infiniteVolumeSchwinger k f =
        ∫ ω, (∏ i, ω (f i)) ∂infiniteVolumeMeasure

/-- **Uniform upper bound**: The Schwinger functions are bounded uniformly in Λ:
    |S_n^Λ(f₁,...,fₙ)| ≤ C(f₁,...,fₙ)
    for all Λ (with Dirichlet BC).

    This combines:
    - Chessboard estimates (multiple reflections) to reduce to unit-square expectations
    - The Lᵖ bounds from Theorem 8.6.2 for each unit square
    - Exponential decay of the propagator for cross-square contributions -/
theorem schwinger_uniformly_bounded (params : Phi4Params)
    [InfiniteVolumeLimitModel params]
    (k : ℕ) (f : Fin k → TestFun2D) :
    ∃ C : ℝ, ∀ (n : ℕ) (hn : 0 < n),
      |schwingerN params (exhaustingRectangles n hn) k f| ≤ C := by
  exact InfiniteVolumeLimitModel.schwinger_uniformly_bounded
    (params := params) k f

/-! ## Existence of the infinite volume limit -/

/-- **Existence of infinite volume Schwinger functions** (Theorem 11.2.1):
    For non-negative test functions, the limit
      S_k(f₁,...,fₖ) := lim_{n→∞} S_k^{Λₙ}(f₁,...,fₖ)
    exists (as a real number).

    For general (signed) test functions, existence follows by decomposing
    f = f⁺ - f⁻ and using multilinearity. -/
theorem infinite_volume_schwinger_exists (params : Phi4Params)
    [InfiniteVolumeLimitModel params]
    (k : ℕ) (f : Fin k → TestFun2D) :
    ∃ S : ℝ, Filter.Tendsto
      (fun n : ℕ => if h : 0 < n then schwingerN params (exhaustingRectangles n h) k f else 0)
      Filter.atTop (nhds S) := by
  refine ⟨InfiniteVolumeLimitModel.infiniteVolumeSchwinger (params := params) k f, ?_⟩
  exact InfiniteVolumeLimitModel.infiniteVolumeSchwinger_tendsto
    (params := params) k f

/-- The infinite volume Schwinger function. -/
def infiniteVolumeSchwinger (params : Phi4Params)
    [InfiniteVolumeLimitModel params]
    (k : ℕ)
    (f : Fin k → TestFun2D) : ℝ :=
  InfiniteVolumeLimitModel.infiniteVolumeSchwinger (params := params) k f

/-- Connected (truncated) 2-point function in infinite volume:
    `S₂(f,g) - S₁(f)S₁(g)`. -/
def connectedTwoPoint (params : Phi4Params)
    [InfiniteVolumeLimitModel params]
    (f g : TestFun2D) : ℝ :=
  infiniteVolumeSchwinger params 2 ![f, g] -
    infiniteVolumeSchwinger params 1 ![f] *
      infiniteVolumeSchwinger params 1 ![g]

@[simp] theorem connectedTwoPoint_eq (params : Phi4Params)
    [InfiniteVolumeLimitModel params] (f g : TestFun2D) :
    connectedTwoPoint params f g =
      infiniteVolumeSchwinger params 2 ![f, g] -
        infiniteVolumeSchwinger params 1 ![f] *
          infiniteVolumeSchwinger params 1 ![g] := rfl

/-- Symmetry of the infinite-volume 2-point Schwinger function from
    moment representation. -/
theorem infiniteVolumeSchwinger_two_symm (params : Phi4Params)
    [InfiniteVolumeLimitModel params] (f g : TestFun2D) :
    infiniteVolumeSchwinger params 2 ![f, g] =
      infiniteVolumeSchwinger params 2 ![g, f] := by
  simp [infiniteVolumeSchwinger, InfiniteVolumeLimitModel.infiniteVolumeSchwinger_is_moment,
    Fin.prod_univ_two, mul_comm]

/-- Symmetry of the infinite-volume connected 2-point function. -/
theorem connectedTwoPoint_symm (params : Phi4Params)
    [InfiniteVolumeLimitModel params] (f g : TestFun2D) :
    connectedTwoPoint params f g = connectedTwoPoint params g f := by
  unfold connectedTwoPoint
  rw [infiniteVolumeSchwinger_two_symm]
  ring

/-- Along the exhausting rectangles, the finite-volume connected two-point
    function converges to the infinite-volume connected two-point function. -/
theorem connectedSchwingerTwo_tendsto_infinite
    (params : Phi4Params)
    [InfiniteVolumeLimitModel params]
    (f g : TestFun2D) :
    Filter.Tendsto
      (fun n : ℕ => if h : 0 < n then
        connectedSchwingerTwo params (exhaustingRectangles n h) f g
      else 0)
      Filter.atTop
      (nhds (connectedTwoPoint params f g)) := by
  have h2 := InfiniteVolumeLimitModel.infiniteVolumeSchwinger_tendsto
    (params := params) 2 (![f, g] : Fin 2 → TestFun2D)
  have h1f := InfiniteVolumeLimitModel.infiniteVolumeSchwinger_tendsto
    (params := params) 1 (![f] : Fin 1 → TestFun2D)
  have h1g := InfiniteVolumeLimitModel.infiniteVolumeSchwinger_tendsto
    (params := params) 1 (![g] : Fin 1 → TestFun2D)
  have hmul :
      Filter.Tendsto
        (fun n : ℕ =>
          (if h : 0 < n then schwingerN params (exhaustingRectangles n h) 1 ![f] else 0) *
          (if h : 0 < n then schwingerN params (exhaustingRectangles n h) 1 ![g] else 0))
        Filter.atTop
        (nhds (infiniteVolumeSchwinger params 1 ![f] *
          infiniteVolumeSchwinger params 1 ![g])) :=
    h1f.mul h1g
  have hsub :
      Filter.Tendsto
        (fun n : ℕ =>
          (if h : 0 < n then schwingerN params (exhaustingRectangles n h) 2
            (![f, g] : Fin 2 → TestFun2D) else 0) -
          ((if h : 0 < n then schwingerN params (exhaustingRectangles n h) 1 ![f] else 0) *
            (if h : 0 < n then schwingerN params (exhaustingRectangles n h) 1 ![g] else 0)))
        Filter.atTop
        (nhds (infiniteVolumeSchwinger params 2 (![f, g] : Fin 2 → TestFun2D) -
          infiniteVolumeSchwinger params 1 ![f] *
            infiniteVolumeSchwinger params 1 ![g])) :=
    h2.sub hmul
  have hEqFun :
      (fun n : ℕ => if h : 0 < n then
        connectedSchwingerTwo params (exhaustingRectangles n h) f g
      else 0)
      =
      (fun n : ℕ =>
        (if h : 0 < n then schwingerN params (exhaustingRectangles n h) 2
          (![f, g] : Fin 2 → TestFun2D) else 0) -
        ((if h : 0 < n then schwingerN params (exhaustingRectangles n h) 1 ![f] else 0) *
          (if h : 0 < n then schwingerN params (exhaustingRectangles n h) 1 ![g] else 0))) := by
    funext n
    by_cases h : 0 < n
    · simp [connectedSchwingerTwo, schwingerN_two_eq_schwingerTwo, h]
    · simp [h]
  have hEqLim :
      connectedTwoPoint params f g =
      infiniteVolumeSchwinger params 2 (![f, g] : Fin 2 → TestFun2D) -
        infiniteVolumeSchwinger params 1 ![f] *
          infiniteVolumeSchwinger params 1 ![g] := by
    simp [connectedTwoPoint]
  rw [hEqFun, hEqLim]
  exact hsub

/-- If finite-volume FKG inequalities are available, the infinite-volume connected
    two-point function is nonnegative. -/
theorem connectedTwoPoint_nonneg
    (params : Phi4Params)
    [InfiniteVolumeLimitModel params]
    [CorrelationInequalityModel params]
    (f g : TestFun2D) :
    0 ≤ connectedTwoPoint params f g := by
  have hlim := connectedSchwingerTwo_tendsto_infinite params f g
  have hnonneg : ∀ n : ℕ,
      0 ≤
        (if h : 0 < n then
          connectedSchwingerTwo params (exhaustingRectangles n h) f g
        else 0) := by
    intro n
    by_cases h : 0 < n
    · have hConn := connectedSchwingerTwo_nonneg params (exhaustingRectangles n h) f g
      unfold connectedSchwingerTwo at hConn
      simp [h]
      linarith
    · simp [h]
  exact ge_of_tendsto' hlim hnonneg

/-- The infinite volume φ⁴₂ probability measure on S'(ℝ²).
    This is the weak limit of dμ_{Λₙ} as Λₙ ↗ ℝ². -/
def infiniteVolumeMeasure (params : Phi4Params)
    [InfiniteVolumeLimitModel params] :
    @Measure FieldConfig2D GaussianField.instMeasurableSpaceConfiguration :=
  InfiniteVolumeLimitModel.infiniteVolumeMeasure (params := params)

/-- The infinite volume measure is a probability measure. -/
theorem infiniteVolumeMeasure_isProbability (params : Phi4Params)
    [InfiniteVolumeLimitModel params] :
    IsProbabilityMeasure (infiniteVolumeMeasure params) := by
  simpa [infiniteVolumeMeasure] using
    (InfiniteVolumeLimitModel.infiniteVolumeMeasure_isProbability
      (params := params))

/-- The infinite volume Schwinger functions are the moments of the
    infinite volume measure. -/
theorem infiniteVolumeSchwinger_is_moment (params : Phi4Params)
    [InfiniteVolumeLimitModel params]
    (k : ℕ) (f : Fin k → TestFun2D) :
    infiniteVolumeSchwinger params k f =
      ∫ ω, (∏ i, ω (f i)) ∂(infiniteVolumeMeasure params) := by
  simpa [infiniteVolumeSchwinger, infiniteVolumeMeasure] using
    (InfiniteVolumeLimitModel.infiniteVolumeSchwinger_is_moment
      (params := params) k f)

/-- Zeroth infinite-volume Schwinger function normalization:
    `S_0 = 1` for any choice of the unique `Fin 0 → TestFun2D`. -/
theorem infiniteVolumeSchwinger_zero (params : Phi4Params)
    [InfiniteVolumeLimitModel params]
    (f : Fin 0 → TestFun2D) :
    infiniteVolumeSchwinger params 0 f = 1 := by
  have hprob : IsProbabilityMeasure (infiniteVolumeMeasure params) :=
    infiniteVolumeMeasure_isProbability params
  letI : IsProbabilityMeasure (infiniteVolumeMeasure params) := hprob
  rw [infiniteVolumeSchwinger_is_moment]
  change ∫ ω : FieldConfig2D, (1 : ℝ) ∂(infiniteVolumeMeasure params) = 1
  rw [integral_const]
  simp

end

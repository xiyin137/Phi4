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
    [CorrelationTwoPointModel params]
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

/-- Monotonicity of finite-volume `k`-point Schwinger moments along the
    exhausting rectangles, under a `SchwingerNMonotoneModel` interface. -/
theorem schwingerN_monotone_in_volume_of_model (params : Phi4Params)
    (k : ℕ)
    [SchwingerNMonotoneModel params k]
    (n₁ n₂ : ℕ) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (h : n₁ ≤ n₂)
    (f : Fin k → TestFun2D) (hf : ∀ i, ∀ x, 0 ≤ f i x)
    (hfsupp : ∀ i, ∀ x ∉ (exhaustingRectangles n₁ hn₁).toSet, f i x = 0) :
    schwingerN params (exhaustingRectangles n₁ hn₁) k f ≤
      schwingerN params (exhaustingRectangles n₂ hn₂) k f := by
  exact schwingerN_monotone_of_interface params k
    (exhaustingRectangles n₁ hn₁) (exhaustingRectangles n₂ hn₂)
    (exhaustingRectangles_mono_toSet n₁ n₂ hn₁ hn₂ h)
    f hf hfsupp

/-- Monotonicity of the `n = 2` Schwinger function in `schwingerN` form. -/
theorem schwingerN_monotone_in_volume_two (params : Phi4Params)
    [CorrelationTwoPointModel params]
    (n₁ n₂ : ℕ) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (h : n₁ ≤ n₂)
    (f : Fin 2 → TestFun2D) (hf : ∀ i, ∀ x, 0 ≤ f i x)
    (hfsupp : ∀ i, ∀ x ∉ (exhaustingRectangles n₁ hn₁).toSet, f i x = 0) :
    schwingerN params (exhaustingRectangles n₁ hn₁) 2 f ≤
      schwingerN params (exhaustingRectangles n₂ hn₂) 2 f := by
  exact schwingerN_monotone_in_volume_of_model
    (params := params) (k := 2) n₁ n₂ hn₁ hn₂ h f hf hfsupp

/-- Lattice-bridge variant of `k = 2` monotonicity in `schwingerN` form. -/
theorem schwingerN_monotone_in_volume_two_from_lattice (params : Phi4Params)
    [LatticeSchwingerTwoMonotoneModel params]
    (n₁ n₂ : ℕ) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (h : n₁ ≤ n₂)
    (f : Fin 2 → TestFun2D) (hf : ∀ i, ∀ x, 0 ≤ f i x)
    (hfsupp : ∀ i, ∀ x ∉ (exhaustingRectangles n₁ hn₁).toSet, f i x = 0) :
    schwingerN params (exhaustingRectangles n₁ hn₁) 2 f ≤
      schwingerN params (exhaustingRectangles n₂ hn₂) 2 f := by
  rcases schwingerNMonotoneModel_two_nonempty_of_lattice (params := params) with ⟨hmono⟩
  letI : SchwingerNMonotoneModel params 2 := hmono
  exact schwingerN_monotone_in_volume_of_model
    (params := params) (k := 2) n₁ n₂ hn₁ hn₂ h f hf hfsupp

/-- Monotonicity for `schwingerN` in the currently established case `k = 2`,
    reduced to `schwinger_monotone_in_volume`. -/
theorem schwingerN_monotone_in_volume (params : Phi4Params)
    [CorrelationTwoPointModel params]
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

/-- Exhausting rectangles are time-symmetric. -/
private lemma exhaustingRectangles_isTimeSymmetric
    (n : ℕ) (hn : 0 < n) :
    (exhaustingRectangles n hn).IsTimeSymmetric := by
  simp [Rectangle.IsTimeSymmetric, exhaustingRectangles, Rectangle.symmetric]

/-- Uniform absolute bound for exhausting-sequence Schwinger moments:
    if a test-family is supported in a fixed base rectangle, then its finite-volume
    moments along the standard exhaustion are uniformly bounded. -/
theorem schwingerN_uniformly_bounded_on_exhaustion
    (params : Phi4Params)
    [MultipleReflectionModel params]
    (n0 : ℕ)
    (k : ℕ)
    (f : Fin k → TestFun2D)
    (hfsupp0 :
      ∀ i, ∀ x ∉ (exhaustingRectangles (n0 + 1) (Nat.succ_pos n0)).toSet, f i x = 0) :
    ∃ C : ℝ, ∀ n : ℕ,
      |schwingerN params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) k f| ≤ C := by
  rcases schwinger_uniform_bound params k f with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro n
  let Λn : Rectangle := exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)
  have hsub0n :
      (exhaustingRectangles (n0 + 1) (Nat.succ_pos n0)).toSet ⊆ Λn.toSet := by
    simpa [Λn] using
      (exhaustingRectangles_mono_toSet
        (n0 + 1) (n + n0 + 1)
        (Nat.succ_pos n0) (Nat.succ_pos (n + n0)) (by omega))
  have hfsuppn : ∀ i, ∀ x ∉ Λn.toSet, f i x = 0 := by
    intro i x hx
    exact support_zero_outside_of_subset (f i) hsub0n (hfsupp0 i) x hx
  exact hC Λn (exhaustingRectangles_isTimeSymmetric _ (Nat.succ_pos _)) hfsuppn

/-- Monotone-convergence form for finite-volume `k`-point moments along the
    exhausting rectangles, under:
    1. `SchwingerNMonotoneModel params k` for volume monotonicity, and
    2. `MultipleReflectionModel params` for uniform absolute bounds. -/
theorem schwingerN_tendsto_iSup_of_models
    (params : Phi4Params)
    (k : ℕ)
    [SchwingerNMonotoneModel params k]
    [MultipleReflectionModel params]
    (n0 : ℕ)
    (f : Fin k → TestFun2D)
    (hf : ∀ i, ∀ x, 0 ≤ f i x)
    (hfsupp0 : ∀ i,
      ∀ x ∉ (exhaustingRectangles (n0 + 1) (Nat.succ_pos n0)).toSet, f i x = 0) :
    Filter.Tendsto
      (fun n : ℕ => schwingerN params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) k f)
      Filter.atTop
      (nhds (⨆ n : ℕ,
        schwingerN params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) k f)) := by
  have hbound := schwingerN_uniformly_bounded_on_exhaustion params n0 k f hfsupp0
  have hmono : Monotone (fun n : ℕ =>
      schwingerN params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) k f) := by
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
        ∀ i,
          ∀ x ∉ (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)).toSet, f i x = 0 := by
      intro i x hx
      exact support_zero_outside_of_subset (f i) hsub0n (hfsupp0 i) x hx
    exact schwingerN_monotone_in_volume_of_model
      (params := params) (k := k)
      (n + n0 + 1) (m + n0 + 1)
      (Nat.succ_pos (n + n0)) (Nat.succ_pos (m + n0))
      hle f hf hfsuppn
  exact tendsto_iSup_of_monotone_abs_bounded
    (fun n : ℕ => schwingerN params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) k f)
    hmono hbound

/-- Existence form of `schwingerN_tendsto_iSup_of_models`. -/
theorem schwingerN_limit_exists_of_models
    (params : Phi4Params)
    (k : ℕ)
    [SchwingerNMonotoneModel params k]
    [MultipleReflectionModel params]
    (n0 : ℕ)
    (f : Fin k → TestFun2D)
    (hf : ∀ i, ∀ x, 0 ≤ f i x)
    (hfsupp0 : ∀ i,
      ∀ x ∉ (exhaustingRectangles (n0 + 1) (Nat.succ_pos n0)).toSet, f i x = 0) :
    ∃ S : ℝ,
      Filter.Tendsto
        (fun n : ℕ => schwingerN params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) k f)
        Filter.atTop (nhds S) := by
  refine ⟨⨆ n : ℕ, schwingerN params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) k f, ?_⟩
  exact schwingerN_tendsto_iSup_of_models params k n0 f hf hfsupp0

/-- Existence of the interface-shaped exhausting-sequence limit
    `if h : 0 < n then S_k^{Λₙ}(f) else 0` from:
    1. `SchwingerNMonotoneModel params k`, and
    2. `MultipleReflectionModel params`. -/
theorem schwingerN_limit_exists_if_exhaustion_of_models
    (params : Phi4Params)
    (k : ℕ)
    [SchwingerNMonotoneModel params k]
    [MultipleReflectionModel params]
    (f : Fin k → TestFun2D)
    (hf : ∀ i, ∀ x, 0 ≤ f i x)
    (hfsupp : ∀ i, ∀ x ∉ (exhaustingRectangles 1 (Nat.succ_pos 0)).toSet, f i x = 0) :
    ∃ S : ℝ,
      Filter.Tendsto
        (fun n : ℕ =>
          if h : 0 < n then schwingerN params (exhaustingRectangles n h) k f else 0)
        Filter.atTop (nhds S) := by
  let S : ℝ := ⨆ n : ℕ,
    schwingerN params (exhaustingRectangles (n + 1) (Nat.succ_pos n)) k f
  have hshift :
      Filter.Tendsto
        (fun n : ℕ => schwingerN params (exhaustingRectangles (n + 1) (Nat.succ_pos n)) k f)
        Filter.atTop (nhds S) := by
    simpa [S, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (schwingerN_tendsto_iSup_of_models
        (params := params) (k := k) (n0 := 0) f hf hfsupp)
  let a : ℕ → ℝ := fun n =>
    if h : 0 < n then schwingerN params (exhaustingRectangles n h) k f else 0
  have hshiftA : Filter.Tendsto (fun n : ℕ => a (n + 1)) Filter.atTop (nhds S) := by
    simpa [a] using hshift
  have ha : Filter.Tendsto a Filter.atTop (nhds S) :=
    (Filter.tendsto_add_atTop_iff_nat (f := a) 1).1 hshiftA
  exact ⟨S, ha⟩

/-- Uniform absolute bound for the exhausting-sequence two-point function,
    obtained from the multiple-reflection uniform bound and support-in-base-volume
    assumptions. -/
theorem schwingerTwo_uniformly_bounded_on_exhaustion
    (params : Phi4Params)
    [MultipleReflectionModel params]
    (n0 : ℕ)
    (f g : TestFun2D)
    (hfsupp0 : ∀ x ∉ (exhaustingRectangles (n0 + 1) (Nat.succ_pos n0)).toSet, f x = 0)
    (hgsupp0 : ∀ x ∉ (exhaustingRectangles (n0 + 1) (Nat.succ_pos n0)).toSet, g x = 0) :
    ∃ C : ℝ, ∀ n : ℕ,
      |schwingerTwo params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) f g| ≤ C := by
  have hfgsupp0 :
      ∀ i, ∀ x ∉ (exhaustingRectangles (n0 + 1) (Nat.succ_pos n0)).toSet,
        (![f, g] : Fin 2 → TestFun2D) i x = 0 := by
    intro i x hx
    fin_cases i
    · simpa using hfsupp0 x hx
    · simpa using hgsupp0 x hx
  rcases schwingerN_uniformly_bounded_on_exhaustion
      params n0 2 (![f, g] : Fin 2 → TestFun2D) hfgsupp0 with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro n
  simpa [schwingerN_two_eq_schwingerTwo] using hC n

/-- Convergence of the two-point finite-volume sequence from:
    1. positivity-preserving test functions with support in a base rectangle,
    2. volume monotonicity (`CorrelationTwoPointModel`), and
    3. an explicit uniform absolute bound.

    The limit is identified with the supremum over the exhaustion sequence. -/
theorem schwingerTwo_tendsto_iSup_of_monotone_bounded
    (params : Phi4Params)
    [CorrelationTwoPointModel params]
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

/-- Monotone-convergence form for the two-point exhausting sequence, with the
    absolute bound discharged by `MultipleReflectionModel`. -/
theorem schwingerTwo_tendsto_iSup_of_models
    (params : Phi4Params)
    [CorrelationTwoPointModel params]
    [MultipleReflectionModel params]
    (n0 : ℕ)
    (f g : TestFun2D) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupp0 : ∀ x ∉ (exhaustingRectangles (n0 + 1) (Nat.succ_pos n0)).toSet, f x = 0)
    (hgsupp0 : ∀ x ∉ (exhaustingRectangles (n0 + 1) (Nat.succ_pos n0)).toSet, g x = 0) :
    Filter.Tendsto
      (fun n : ℕ => schwingerTwo params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) f g)
      Filter.atTop
      (nhds (⨆ n : ℕ,
        schwingerTwo params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) f g)) := by
  have hbound := schwingerTwo_uniformly_bounded_on_exhaustion
    params n0 f g hfsupp0 hgsupp0
  exact schwingerTwo_tendsto_iSup_of_monotone_bounded
    params n0 f g hf hg hfsupp0 hgsupp0 hbound

/-- Existence form of `schwingerTwo_tendsto_iSup_of_models`. -/
theorem schwingerTwo_limit_exists_of_models
    (params : Phi4Params)
    [CorrelationTwoPointModel params]
    [MultipleReflectionModel params]
    (n0 : ℕ)
    (f g : TestFun2D) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupp0 : ∀ x ∉ (exhaustingRectangles (n0 + 1) (Nat.succ_pos n0)).toSet, f x = 0)
    (hgsupp0 : ∀ x ∉ (exhaustingRectangles (n0 + 1) (Nat.succ_pos n0)).toSet, g x = 0) :
    ∃ S : ℝ,
      Filter.Tendsto
        (fun n : ℕ => schwingerTwo params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) f g)
        Filter.atTop (nhds S) := by
  refine ⟨⨆ n : ℕ, schwingerTwo params
    (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) f g, ?_⟩
  exact schwingerTwo_tendsto_iSup_of_models
    params n0 f g hf hg hfsupp0 hgsupp0

/-- Convergence of the interface-shaped exhausting sequence
    `if h : 0 < n then S₂^{Λₙ}(f,g) else 0`, with monotonicity from
    `CorrelationTwoPointModel` and absolute bounds from `MultipleReflectionModel`. -/
theorem schwingerTwo_tendsto_if_exhaustion_of_models
    (params : Phi4Params)
    [CorrelationTwoPointModel params]
    [MultipleReflectionModel params]
    (f g : TestFun2D)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupp : ∀ x ∉ (exhaustingRectangles 1 (Nat.succ_pos 0)).toSet, f x = 0)
    (hgsupp : ∀ x ∉ (exhaustingRectangles 1 (Nat.succ_pos 0)).toSet, g x = 0) :
    Filter.Tendsto
      (fun n : ℕ => if h : 0 < n then schwingerTwo params (exhaustingRectangles n h) f g else 0)
      Filter.atTop
      (nhds (⨆ n : ℕ, if h : 0 < n then schwingerTwo params (exhaustingRectangles n h) f g else 0)) := by
  let a : ℕ → ℝ := fun n =>
    if h : 0 < n then schwingerTwo params (exhaustingRectangles n h) f g else 0
  have hmono : Monotone a := by
    intro n m hnm
    by_cases hn : 0 < n
    · have hm : 0 < m := lt_of_lt_of_le hn hnm
      have hsub :
          (exhaustingRectangles 1 (Nat.succ_pos 0)).toSet ⊆
            (exhaustingRectangles n hn).toSet :=
        exhaustingRectangles_mono_toSet 1 n (Nat.succ_pos 0) hn hn
      have hfsuppn : ∀ x ∉ (exhaustingRectangles n hn).toSet, f x = 0 :=
        support_zero_outside_of_subset f hsub hfsupp
      have hgsuppn : ∀ x ∉ (exhaustingRectangles n hn).toSet, g x = 0 :=
        support_zero_outside_of_subset g hsub hgsupp
      have hmono_nm := schwinger_monotone_in_volume params n m hn hm hnm f g hf hg hfsuppn hgsuppn
      simpa [a, hn, hm] using hmono_nm
    · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
      by_cases hm : 0 < m
      · have hnonneg : 0 ≤ schwingerTwo params (exhaustingRectangles m hm) f g :=
          griffiths_first params (exhaustingRectangles m hm) f g hf hg
        simpa [a, hn0, hm] using hnonneg
      · have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
        subst hn0
        subst hm0
        simp [a]
  rcases schwingerTwo_uniformly_bounded_on_exhaustion
      params 0 f g hfsupp hgsupp with ⟨C, hC⟩
  let Cmax : ℝ := max C 0
  have hbound : ∀ n : ℕ, |a n| ≤ Cmax := by
    intro n
    by_cases hn : 0 < n
    · rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn) with ⟨k, rfl⟩
      have hk : |schwingerTwo params (exhaustingRectangles (k + 1) (Nat.succ_pos k)) f g| ≤ C := hC k
      have hk' : |a (k + 1)| ≤ C := by simpa [a] using hk
      exact le_trans hk' (le_max_left _ _)
    · have hzero : a n = 0 := by simp [a, hn]
      rw [hzero]
      have hCmax_nonneg : 0 ≤ Cmax := le_trans (le_refl 0) (le_max_right C 0)
      simpa [abs_of_nonneg hCmax_nonneg]
  have hbdd : BddAbove (Set.range a) := by
    refine ⟨Cmax, ?_⟩
    rintro y ⟨n, rfl⟩
    exact le_trans (le_abs_self _) (hbound n)
  exact tendsto_atTop_ciSup hmono hbdd

/-- Existence form of `schwingerTwo_tendsto_if_exhaustion_of_models`. -/
theorem schwingerTwo_limit_exists_if_exhaustion_of_models
    (params : Phi4Params)
    [CorrelationTwoPointModel params]
    [MultipleReflectionModel params]
    (f g : TestFun2D)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupp : ∀ x ∉ (exhaustingRectangles 1 (Nat.succ_pos 0)).toSet, f x = 0)
    (hgsupp : ∀ x ∉ (exhaustingRectangles 1 (Nat.succ_pos 0)).toSet, g x = 0) :
    ∃ S : ℝ,
      Filter.Tendsto
        (fun n : ℕ => if h : 0 < n then schwingerTwo params (exhaustingRectangles n h) f g else 0)
        Filter.atTop (nhds S) := by
  refine ⟨⨆ n : ℕ, if h : 0 < n then schwingerTwo params (exhaustingRectangles n h) f g else 0, ?_⟩
  exact schwingerTwo_tendsto_if_exhaustion_of_models params f g hf hg hfsupp hgsupp

/-- Lattice-bridge `n + 1`-shifted exhaustion form of two-point convergence. -/
theorem schwingerTwo_tendsto_if_exhaustion_of_lattice_models
    (params : Phi4Params)
    [LatticeSchwingerTwoMonotoneModel params]
    [MultipleReflectionModel params]
    (f g : TestFun2D)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupp : ∀ x ∉ (exhaustingRectangles 1 (Nat.succ_pos 0)).toSet, f x = 0)
    (hgsupp : ∀ x ∉ (exhaustingRectangles 1 (Nat.succ_pos 0)).toSet, g x = 0) :
    Filter.Tendsto
      (fun n : ℕ =>
        schwingerTwo params (exhaustingRectangles (n + 1) (Nat.succ_pos n)) f g)
      Filter.atTop
      (nhds (⨆ n : ℕ,
        schwingerTwo params (exhaustingRectangles (n + 1) (Nat.succ_pos n)) f g)) := by
  rcases schwingerNMonotoneModel_two_nonempty_of_lattice (params := params) with ⟨hmono⟩
  letI : SchwingerNMonotoneModel params 2 := hmono
  have hfvec : ∀ i, ∀ x, 0 ≤ (![f, g] : Fin 2 → TestFun2D) i x := by
    intro i x
    fin_cases i
    · simpa using hf x
    · simpa using hg x
  have hsuppvec :
      ∀ i, ∀ x ∉ (exhaustingRectangles (0 + 1) (Nat.succ_pos 0)).toSet,
        (![f, g] : Fin 2 → TestFun2D) i x = 0 := by
    intro i x hx
    fin_cases i
    · simpa using hfsupp x hx
    · simpa using hgsupp x hx
  have hlim := schwingerN_tendsto_iSup_of_models
    (params := params) (k := 2) (n0 := 0) (![f, g] : Fin 2 → TestFun2D)
    hfvec hsuppvec
  simpa [schwingerN_two_eq_schwingerTwo] using hlim

/-- Existence form of `schwingerTwo_tendsto_if_exhaustion_of_lattice_models`. -/
theorem schwingerTwo_limit_exists_if_exhaustion_of_lattice_models
    (params : Phi4Params)
    [LatticeSchwingerTwoMonotoneModel params]
    [MultipleReflectionModel params]
    (f g : TestFun2D)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupp : ∀ x ∉ (exhaustingRectangles 1 (Nat.succ_pos 0)).toSet, f x = 0)
    (hgsupp : ∀ x ∉ (exhaustingRectangles 1 (Nat.succ_pos 0)).toSet, g x = 0) :
    ∃ S : ℝ,
      Filter.Tendsto
        (fun n : ℕ => if h : 0 < n then schwingerTwo params (exhaustingRectangles n h) f g else 0)
        Filter.atTop (nhds S) := by
  rcases schwingerNMonotoneModel_two_nonempty_of_lattice (params := params) with ⟨hmono⟩
  letI : SchwingerNMonotoneModel params 2 := hmono
  have hfvec : ∀ i, ∀ x, 0 ≤ (![f, g] : Fin 2 → TestFun2D) i x := by
    intro i x
    fin_cases i
    · simpa using hf x
    · simpa using hg x
  have hsuppvec :
      ∀ i, ∀ x ∉ (exhaustingRectangles 1 (Nat.succ_pos 0)).toSet,
        (![f, g] : Fin 2 → TestFun2D) i x = 0 := by
    intro i x hx
    fin_cases i
    · simpa using hfsupp x hx
    · simpa using hgsupp x hx
  rcases schwingerN_limit_exists_if_exhaustion_of_models
      (params := params) (k := 2) (![f, g] : Fin 2 → TestFun2D) hfvec hsuppvec with
      ⟨S, hS⟩
  refine ⟨S, ?_⟩
  simpa [schwingerN_two_eq_schwingerTwo] using hS

/-- `schwingerN` (`k = 2`) form of
    `schwingerTwo_tendsto_if_exhaustion_of_models`. -/
theorem schwingerN_two_tendsto_if_exhaustion_of_models
    (params : Phi4Params)
    [CorrelationTwoPointModel params]
    [MultipleReflectionModel params]
    (f g : TestFun2D)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupp : ∀ x ∉ (exhaustingRectangles 1 (Nat.succ_pos 0)).toSet, f x = 0)
    (hgsupp : ∀ x ∉ (exhaustingRectangles 1 (Nat.succ_pos 0)).toSet, g x = 0) :
    Filter.Tendsto
      (fun n : ℕ =>
        if h : 0 < n then schwingerN params (exhaustingRectangles n h) 2
          (![f, g] : Fin 2 → TestFun2D) else 0)
      Filter.atTop
      (nhds (⨆ n : ℕ,
        if h : 0 < n then schwingerN params (exhaustingRectangles n h) 2
          (![f, g] : Fin 2 → TestFun2D) else 0)) := by
  let a : ℕ → ℝ := fun n =>
    if h : 0 < n then schwingerTwo params (exhaustingRectangles n h) f g else 0
  let b : ℕ → ℝ := fun n =>
    if h : 0 < n then schwingerN params (exhaustingRectangles n h) 2
      (![f, g] : Fin 2 → TestFun2D) else 0
  have hab : a = b := by
    funext n
    by_cases h : 0 < n
    · simp [a, b, h, schwingerN_two_eq_schwingerTwo]
    · simp [a, b, h]
  have hlimA := schwingerTwo_tendsto_if_exhaustion_of_models
    params f g hf hg hfsupp hgsupp
  simpa [a, b, hab] using hlimA

/-- Existence form of `schwingerN_two_tendsto_if_exhaustion_of_models`. -/
theorem schwingerN_two_limit_exists_if_exhaustion_of_models
    (params : Phi4Params)
    [CorrelationTwoPointModel params]
    [MultipleReflectionModel params]
    (f g : TestFun2D)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupp : ∀ x ∉ (exhaustingRectangles 1 (Nat.succ_pos 0)).toSet, f x = 0)
    (hgsupp : ∀ x ∉ (exhaustingRectangles 1 (Nat.succ_pos 0)).toSet, g x = 0) :
    ∃ S : ℝ,
      Filter.Tendsto
        (fun n : ℕ =>
          if h : 0 < n then schwingerN params (exhaustingRectangles n h) 2
            (![f, g] : Fin 2 → TestFun2D) else 0)
        Filter.atTop (nhds S) := by
  refine ⟨⨆ n : ℕ,
    if h : 0 < n then schwingerN params (exhaustingRectangles n h) 2
      (![f, g] : Fin 2 → TestFun2D) else 0, ?_⟩
  exact schwingerN_two_tendsto_if_exhaustion_of_models
    params f g hf hg hfsupp hgsupp

/-- Lattice-bridge `schwingerN` (`k = 2`) shifted-exhaustion convergence form. -/
theorem schwingerN_two_tendsto_if_exhaustion_of_lattice_models
    (params : Phi4Params)
    [LatticeSchwingerTwoMonotoneModel params]
    [MultipleReflectionModel params]
    (f g : TestFun2D)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupp : ∀ x ∉ (exhaustingRectangles 1 (Nat.succ_pos 0)).toSet, f x = 0)
    (hgsupp : ∀ x ∉ (exhaustingRectangles 1 (Nat.succ_pos 0)).toSet, g x = 0) :
    Filter.Tendsto
      (fun n : ℕ =>
        schwingerN params (exhaustingRectangles (n + 1) (Nat.succ_pos n)) 2
          (![f, g] : Fin 2 → TestFun2D))
      Filter.atTop
      (nhds (⨆ n : ℕ,
        schwingerN params (exhaustingRectangles (n + 1) (Nat.succ_pos n)) 2
          (![f, g] : Fin 2 → TestFun2D))) := by
  have hlimA := schwingerTwo_tendsto_if_exhaustion_of_lattice_models
    params f g hf hg hfsupp hgsupp
  simpa [schwingerN_two_eq_schwingerTwo] using hlimA

/-- Existence form of `schwingerN_two_tendsto_if_exhaustion_of_lattice_models`. -/
theorem schwingerN_two_limit_exists_if_exhaustion_of_lattice_models
    (params : Phi4Params)
    [LatticeSchwingerTwoMonotoneModel params]
    [MultipleReflectionModel params]
    (f g : TestFun2D)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupp : ∀ x ∉ (exhaustingRectangles 1 (Nat.succ_pos 0)).toSet, f x = 0)
    (hgsupp : ∀ x ∉ (exhaustingRectangles 1 (Nat.succ_pos 0)).toSet, g x = 0) :
    ∃ S : ℝ,
      Filter.Tendsto
        (fun n : ℕ =>
          if h : 0 < n then schwingerN params (exhaustingRectangles n h) 2
            (![f, g] : Fin 2 → TestFun2D) else 0)
        Filter.atTop (nhds S) := by
  rcases schwingerNMonotoneModel_two_nonempty_of_lattice (params := params) with ⟨hmono⟩
  letI : SchwingerNMonotoneModel params 2 := hmono
  have hfvec : ∀ i, ∀ x, 0 ≤ (![f, g] : Fin 2 → TestFun2D) i x := by
    intro i x
    fin_cases i
    · simpa using hf x
    · simpa using hg x
  have hsuppvec :
      ∀ i, ∀ x ∉ (exhaustingRectangles 1 (Nat.succ_pos 0)).toSet,
        (![f, g] : Fin 2 → TestFun2D) i x = 0 := by
    intro i x hx
    fin_cases i
    · simpa using hfsupp x hx
    · simpa using hgsupp x hx
  exact schwingerN_limit_exists_if_exhaustion_of_models
    (params := params) (k := 2) (![f, g] : Fin 2 → TestFun2D) hfvec hsuppvec

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

/-- Lattice-bridge monotone-convergence form with the absolute bound discharged by
    `MultipleReflectionModel`. -/
theorem schwingerTwo_tendsto_iSup_of_lattice_models
    (params : Phi4Params)
    [LatticeSchwingerTwoMonotoneModel params]
    [MultipleReflectionModel params]
    (n0 : ℕ)
    (f g : TestFun2D) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupp0 : ∀ x ∉ (exhaustingRectangles (n0 + 1) (Nat.succ_pos n0)).toSet, f x = 0)
    (hgsupp0 : ∀ x ∉ (exhaustingRectangles (n0 + 1) (Nat.succ_pos n0)).toSet, g x = 0) :
    Filter.Tendsto
      (fun n : ℕ => schwingerTwo params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) f g)
      Filter.atTop
      (nhds (⨆ n : ℕ,
        schwingerTwo params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) f g)) := by
  have hbound := schwingerTwo_uniformly_bounded_on_exhaustion
    params n0 f g hfsupp0 hgsupp0
  exact schwingerTwo_tendsto_iSup_of_lattice_monotone_bounded
    params n0 f g hf hg hfsupp0 hgsupp0 hbound

/-- Existence form of `schwingerTwo_tendsto_iSup_of_lattice_models`. -/
theorem schwingerTwo_limit_exists_of_lattice_models
    (params : Phi4Params)
    [LatticeSchwingerTwoMonotoneModel params]
    [MultipleReflectionModel params]
    (n0 : ℕ)
    (f g : TestFun2D) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupp0 : ∀ x ∉ (exhaustingRectangles (n0 + 1) (Nat.succ_pos n0)).toSet, f x = 0)
    (hgsupp0 : ∀ x ∉ (exhaustingRectangles (n0 + 1) (Nat.succ_pos n0)).toSet, g x = 0) :
    ∃ S : ℝ,
      Filter.Tendsto
        (fun n : ℕ => schwingerTwo params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) f g)
        Filter.atTop (nhds S) := by
  refine ⟨⨆ n : ℕ, schwingerTwo params
    (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) f g, ?_⟩
  exact schwingerTwo_tendsto_iSup_of_lattice_models
    params n0 f g hf hg hfsupp0 hgsupp0

/-- Existence form of `schwingerTwo_tendsto_iSup_of_monotone_bounded`. -/
theorem schwingerTwo_limit_exists_of_monotone_bounded
    (params : Phi4Params)
    [CorrelationTwoPointModel params]
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
    [CorrelationTwoPointModel params]
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

/-- `schwingerN` (`k = 2`) monotone-convergence form with absolute bounds
    supplied by `MultipleReflectionModel`. -/
theorem schwingerN_two_tendsto_iSup_of_models
    (params : Phi4Params)
    [CorrelationTwoPointModel params]
    [MultipleReflectionModel params]
    (n0 : ℕ)
    (f : Fin 2 → TestFun2D)
    (hf : ∀ i, ∀ x, 0 ≤ f i x)
    (hfsupp0 : ∀ i,
      ∀ x ∉ (exhaustingRectangles (n0 + 1) (Nat.succ_pos n0)).toSet, f i x = 0) :
    Filter.Tendsto
      (fun n : ℕ => schwingerN params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) 2 f)
      Filter.atTop
      (nhds (⨆ n : ℕ,
        schwingerN params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) 2 f)) := by
  exact schwingerN_tendsto_iSup_of_models
    (params := params) (k := 2) n0 f hf hfsupp0

/-- Lattice-bridge `schwingerN` (`k = 2`) monotone-convergence form with
    absolute bounds supplied by `MultipleReflectionModel`. -/
theorem schwingerN_two_tendsto_iSup_of_lattice_models
    (params : Phi4Params)
    [LatticeSchwingerTwoMonotoneModel params]
    [MultipleReflectionModel params]
    (n0 : ℕ)
    (f : Fin 2 → TestFun2D)
    (hf : ∀ i, ∀ x, 0 ≤ f i x)
    (hfsupp0 : ∀ i,
      ∀ x ∉ (exhaustingRectangles (n0 + 1) (Nat.succ_pos n0)).toSet, f i x = 0) :
    Filter.Tendsto
      (fun n : ℕ => schwingerN params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) 2 f)
      Filter.atTop
      (nhds (⨆ n : ℕ,
        schwingerN params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) 2 f)) := by
  rcases schwingerNMonotoneModel_two_nonempty_of_lattice (params := params) with ⟨hmono⟩
  letI : SchwingerNMonotoneModel params 2 := hmono
  exact schwingerN_tendsto_iSup_of_models
    (params := params) (k := 2) n0 f hf hfsupp0

/-- Existence form of `schwingerN_two_tendsto_iSup_of_monotone_bounded`. -/
theorem schwingerN_two_limit_exists_of_monotone_bounded
    (params : Phi4Params)
    [CorrelationTwoPointModel params]
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

/-- Existence form of `schwingerN_two_tendsto_iSup_of_models`. -/
theorem schwingerN_two_limit_exists_of_models
    (params : Phi4Params)
    [CorrelationTwoPointModel params]
    [MultipleReflectionModel params]
    (n0 : ℕ)
    (f : Fin 2 → TestFun2D)
    (hf : ∀ i, ∀ x, 0 ≤ f i x)
    (hfsupp0 : ∀ i,
      ∀ x ∉ (exhaustingRectangles (n0 + 1) (Nat.succ_pos n0)).toSet, f i x = 0) :
    ∃ S : ℝ,
      Filter.Tendsto
        (fun n : ℕ => schwingerN params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) 2 f)
        Filter.atTop (nhds S) := by
  refine ⟨⨆ n : ℕ, schwingerN params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) 2 f, ?_⟩
  exact schwingerN_two_tendsto_iSup_of_models params n0 f hf hfsupp0

/-- Existence form of `schwingerN_two_tendsto_iSup_of_lattice_models`. -/
theorem schwingerN_two_limit_exists_of_lattice_models
    (params : Phi4Params)
    [LatticeSchwingerTwoMonotoneModel params]
    [MultipleReflectionModel params]
    (n0 : ℕ)
    (f : Fin 2 → TestFun2D)
    (hf : ∀ i, ∀ x, 0 ≤ f i x)
    (hfsupp0 : ∀ i,
      ∀ x ∉ (exhaustingRectangles (n0 + 1) (Nat.succ_pos n0)).toSet, f i x = 0) :
    ∃ S : ℝ,
      Filter.Tendsto
        (fun n : ℕ => schwingerN params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) 2 f)
        Filter.atTop (nhds S) := by
  refine ⟨⨆ n : ℕ, schwingerN params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) 2 f, ?_⟩
  exact schwingerN_two_tendsto_iSup_of_lattice_models params n0 f hf hfsupp0

/-! ## Uniform upper bounds -/

/-- Infinite-volume Schwinger data: uniform bounds, limiting moments, and
    convergence along the standard rectangle exhaustion. -/
class InfiniteVolumeSchwingerModel (params : Phi4Params) where
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

/-- Uniform finite-volume bounds used in infinite-volume Schwinger
    construction. -/
class SchwingerUniformBoundModel (params : Phi4Params) where
  schwinger_uniformly_bounded :
    ∀ (k : ℕ) (f : Fin k → TestFun2D),
      ∃ C : ℝ, ∀ (n : ℕ) (hn : 0 < n),
        |schwingerN params (exhaustingRectangles n hn) k f| ≤ C

/-- Limiting Schwinger moments and convergence along the standard exhaustion. -/
class SchwingerLimitModel (params : Phi4Params) where
  infiniteVolumeSchwinger : ∀ (k : ℕ), (Fin k → TestFun2D) → ℝ
  infiniteVolumeSchwinger_tendsto :
    ∀ (k : ℕ) (f : Fin k → TestFun2D),
      Filter.Tendsto
        (fun n : ℕ =>
          if h : 0 < n then schwingerN params (exhaustingRectangles n h) k f else 0)
        Filter.atTop
        (nhds (infiniteVolumeSchwinger k f))

/-- Construct `SchwingerUniformBoundModel` from explicit uniform-bound data. -/
theorem schwingerUniformBoundModel_nonempty_of_data (params : Phi4Params)
    (hbound : ∀ (k : ℕ) (f : Fin k → TestFun2D),
      ∃ C : ℝ, ∀ (n : ℕ) (hn : 0 < n),
        |schwingerN params (exhaustingRectangles n hn) k f| ≤ C) :
    Nonempty (SchwingerUniformBoundModel params) := by
  exact ⟨{ schwinger_uniformly_bounded := hbound }⟩

/-- Construct `SchwingerLimitModel` from explicit limiting moments and
    convergence data along the standard exhaustion sequence. -/
theorem schwingerLimitModel_nonempty_of_data (params : Phi4Params)
    (S : ∀ (k : ℕ), (Fin k → TestFun2D) → ℝ)
    (hlim : ∀ (k : ℕ) (f : Fin k → TestFun2D),
      Filter.Tendsto
        (fun n : ℕ =>
          if h : 0 < n then schwingerN params (exhaustingRectangles n h) k f else 0)
        Filter.atTop
        (nhds (S k f))) :
    Nonempty (SchwingerLimitModel params) := by
  exact ⟨{
    infiniteVolumeSchwinger := S
    infiniteVolumeSchwinger_tendsto := hlim
  }⟩

/-- Construct `SchwingerLimitModel` from existence-form limit data by choosing
    a limiting moment for each `(k,f)`. -/
theorem schwingerLimitModel_nonempty_of_limit_data (params : Phi4Params)
    (hlim : ∀ (k : ℕ) (f : Fin k → TestFun2D),
      ∃ S : ℝ, Filter.Tendsto
        (fun n : ℕ =>
          if h : 0 < n then schwingerN params (exhaustingRectangles n h) k f else 0)
        Filter.atTop (nhds S)) :
    Nonempty (SchwingerLimitModel params) := by
  classical
  refine schwingerLimitModel_nonempty_of_data params
    (fun k f => (hlim k f).choose) ?_
  intro k f
  exact (hlim k f).choose_spec

/-- Any full infinite-volume Schwinger model provides the uniform-bound
    subinterface. -/
instance (priority := 100) schwingerUniformBoundModel_of_infiniteVolumeSchwinger
    (params : Phi4Params)
    [InfiniteVolumeSchwingerModel params] :
    SchwingerUniformBoundModel params where
  schwinger_uniformly_bounded :=
    InfiniteVolumeSchwingerModel.schwinger_uniformly_bounded (params := params)

/-- Any full infinite-volume Schwinger model provides the limit-data
    subinterface. -/
instance (priority := 100) schwingerLimitModel_of_infiniteVolumeSchwinger
    (params : Phi4Params)
    [InfiniteVolumeSchwingerModel params] :
    SchwingerLimitModel params where
  infiniteVolumeSchwinger :=
    InfiniteVolumeSchwingerModel.infiniteVolumeSchwinger (params := params)
  infiniteVolumeSchwinger_tendsto :=
    InfiniteVolumeSchwingerModel.infiniteVolumeSchwinger_tendsto (params := params)

/-- Uniform-bound and limit-data subinterfaces reconstruct
    `InfiniteVolumeSchwingerModel`. -/
instance (priority := 100) infiniteVolumeSchwingerModel_of_submodels
    (params : Phi4Params)
    [SchwingerUniformBoundModel params]
    [SchwingerLimitModel params] :
    InfiniteVolumeSchwingerModel params where
  schwinger_uniformly_bounded :=
    SchwingerUniformBoundModel.schwinger_uniformly_bounded (params := params)
  infiniteVolumeSchwinger :=
    SchwingerLimitModel.infiniteVolumeSchwinger (params := params)
  infiniteVolumeSchwinger_tendsto :=
    SchwingerLimitModel.infiniteVolumeSchwinger_tendsto (params := params)

/-- Infinite-volume measure representation data (measure + probability). -/
class InfiniteVolumeMeasureModel (params : Phi4Params) where
  infiniteVolumeMeasure :
    @Measure FieldConfig2D GaussianField.instMeasurableSpaceConfiguration
  infiniteVolumeMeasure_isProbability :
    IsProbabilityMeasure infiniteVolumeMeasure

/-- Infinite-volume moment representation linking Schwinger functions to
    moments of `infiniteVolumeMeasure`. -/
class InfiniteVolumeMomentModel (params : Phi4Params)
    [InfiniteVolumeSchwingerModel params]
    [InfiniteVolumeMeasureModel params] where
  infiniteVolumeSchwinger_is_moment :
    ∀ (k : ℕ) (f : Fin k → TestFun2D),
      InfiniteVolumeSchwingerModel.infiniteVolumeSchwinger (params := params) k f =
        ∫ ω, (∏ i, ω (f i)) ∂(InfiniteVolumeMeasureModel.infiniteVolumeMeasure (params := params))

/-- Model of infinite-volume existence data: Schwinger convergence/bounds and a
    representing probability measure. -/
class InfiniteVolumeLimitModel (params : Phi4Params)
    extends InfiniteVolumeSchwingerModel params where
  infiniteVolumeMeasure :
    @Measure FieldConfig2D GaussianField.instMeasurableSpaceConfiguration
  infiniteVolumeMeasure_isProbability :
    IsProbabilityMeasure infiniteVolumeMeasure
  infiniteVolumeSchwinger_is_moment :
    ∀ (k : ℕ) (f : Fin k → TestFun2D),
      infiniteVolumeSchwinger k f =
        ∫ ω, (∏ i, ω (f i)) ∂infiniteVolumeMeasure

/-- Any full infinite-volume model provides the measure-representation subinterface. -/
instance (priority := 100) infiniteVolumeMeasureModel_of_limit
    (params : Phi4Params)
    [InfiniteVolumeLimitModel params] :
    InfiniteVolumeMeasureModel params where
  infiniteVolumeMeasure := InfiniteVolumeLimitModel.infiniteVolumeMeasure (params := params)
  infiniteVolumeMeasure_isProbability :=
    InfiniteVolumeLimitModel.infiniteVolumeMeasure_isProbability (params := params)

/-- Any full infinite-volume model provides the moment-representation subinterface. -/
instance (priority := 100) infiniteVolumeMomentModel_of_limit
    (params : Phi4Params)
    [InfiniteVolumeLimitModel params] :
    InfiniteVolumeMomentModel params where
  infiniteVolumeSchwinger_is_moment :=
    InfiniteVolumeLimitModel.infiniteVolumeSchwinger_is_moment (params := params)

/-- Schwinger + measure subinterfaces reconstruct `InfiniteVolumeLimitModel`. -/
instance (priority := 100) infiniteVolumeLimitModel_of_submodels
    (params : Phi4Params)
    [InfiniteVolumeSchwingerModel params]
    [InfiniteVolumeMeasureModel params]
    [InfiniteVolumeMomentModel params] :
    InfiniteVolumeLimitModel params where
  schwinger_uniformly_bounded :=
    InfiniteVolumeSchwingerModel.schwinger_uniformly_bounded (params := params)
  infiniteVolumeSchwinger :=
    InfiniteVolumeSchwingerModel.infiniteVolumeSchwinger (params := params)
  infiniteVolumeSchwinger_tendsto :=
    InfiniteVolumeSchwingerModel.infiniteVolumeSchwinger_tendsto (params := params)
  infiniteVolumeMeasure :=
    InfiniteVolumeMeasureModel.infiniteVolumeMeasure (params := params)
  infiniteVolumeMeasure_isProbability :=
    InfiniteVolumeMeasureModel.infiniteVolumeMeasure_isProbability (params := params)
  infiniteVolumeSchwinger_is_moment :=
    InfiniteVolumeMomentModel.infiniteVolumeSchwinger_is_moment (params := params)

/-- **Uniform upper bound**: The Schwinger functions are bounded uniformly in Λ:
    |S_n^Λ(f₁,...,fₙ)| ≤ C(f₁,...,fₙ)
    for all Λ (with Dirichlet BC).

    This combines:
    - Chessboard estimates (multiple reflections) to reduce to unit-square expectations
    - The Lᵖ bounds from Theorem 8.6.2 for each unit square
    - Exponential decay of the propagator for cross-square contributions -/
theorem schwinger_uniformly_bounded_of_interface (params : Phi4Params)
    [SchwingerUniformBoundModel params]
    (k : ℕ) (f : Fin k → TestFun2D) :
    ∃ C : ℝ, ∀ (n : ℕ) (hn : 0 < n),
      |schwingerN params (exhaustingRectangles n hn) k f| ≤ C := by
  exact SchwingerUniformBoundModel.schwinger_uniformly_bounded
    (params := params) k f

/-! ## Honest frontiers for infinite-volume package construction -/

/-- Construct `InfiniteVolumeSchwingerModel` from explicit uniform bounds and
    convergence data along the standard exhaustion sequence. -/
theorem infiniteVolumeSchwingerModel_nonempty_of_limit_data (params : Phi4Params)
    (hbound : ∀ (k : ℕ) (f : Fin k → TestFun2D),
      ∃ C : ℝ, ∀ (n : ℕ) (hn : 0 < n),
        |schwingerN params (exhaustingRectangles n hn) k f| ≤ C)
    (hlim : ∀ (k : ℕ) (f : Fin k → TestFun2D),
      ∃ S : ℝ, Filter.Tendsto
        (fun n : ℕ =>
          if h : 0 < n then schwingerN params (exhaustingRectangles n h) k f else 0)
        Filter.atTop (nhds S)) :
    Nonempty (InfiniteVolumeSchwingerModel params) := by
  rcases schwingerUniformBoundModel_nonempty_of_data params hbound with ⟨hboundModel⟩
  rcases schwingerLimitModel_nonempty_of_limit_data params hlim with ⟨hlimModel⟩
  letI : SchwingerUniformBoundModel params := hboundModel
  letI : SchwingerLimitModel params := hlimModel
  exact ⟨inferInstance⟩

/-- Honest frontier: construct the infinite-volume Schwinger package from
    correlation inequalities and multiple-reflection bounds. -/
theorem gap_infiniteVolumeSchwingerModel_nonempty (params : Phi4Params)
    (hbound : ∀ (k : ℕ) (f : Fin k → TestFun2D),
      ∃ C : ℝ, ∀ (n : ℕ) (hn : 0 < n),
        |schwingerN params (exhaustingRectangles n hn) k f| ≤ C)
    (hlim : ∀ (k : ℕ) (f : Fin k → TestFun2D),
      ∃ S : ℝ, Filter.Tendsto
        (fun n : ℕ =>
          if h : 0 < n then schwingerN params (exhaustingRectangles n h) k f else 0)
        Filter.atTop (nhds S)) :
    Nonempty (InfiniteVolumeSchwingerModel params) := by
  exact infiniteVolumeSchwingerModel_nonempty_of_limit_data params hbound hlim

/-- Public uniform-bound endpoint via explicit theorem-level frontier gap. -/
theorem schwinger_uniformly_bounded (params : Phi4Params)
    (hbound : ∀ (k : ℕ) (f : Fin k → TestFun2D),
      ∃ C : ℝ, ∀ (n : ℕ) (hn : 0 < n),
        |schwingerN params (exhaustingRectangles n hn) k f| ≤ C)
    (hlim : ∀ (k : ℕ) (f : Fin k → TestFun2D),
      ∃ S : ℝ, Filter.Tendsto
        (fun n : ℕ =>
          if h : 0 < n then schwingerN params (exhaustingRectangles n h) k f else 0)
        Filter.atTop (nhds S))
    (k : ℕ) (f : Fin k → TestFun2D) :
    ∃ C : ℝ, ∀ (n : ℕ) (hn : 0 < n),
      |schwingerN params (exhaustingRectangles n hn) k f| ≤ C := by
  classical
  rcases gap_infiniteVolumeSchwingerModel_nonempty params hbound hlim with ⟨hiv⟩
  letI : InfiniteVolumeSchwingerModel params := hiv
  exact schwinger_uniformly_bounded_of_interface params k f

/-! ## Existence of the infinite volume limit -/

/-- Interface-level existence of infinite-volume Schwinger functions from
    `InfiniteVolumeSchwingerModel`. -/
theorem infinite_volume_schwinger_exists_of_interface (params : Phi4Params)
    [SchwingerLimitModel params]
    (k : ℕ) (f : Fin k → TestFun2D) :
    ∃ S : ℝ, Filter.Tendsto
      (fun n : ℕ => if h : 0 < n then schwingerN params (exhaustingRectangles n h) k f else 0)
      Filter.atTop (nhds S) := by
  refine ⟨SchwingerLimitModel.infiniteVolumeSchwinger (params := params) k f, ?_⟩
  exact SchwingerLimitModel.infiniteVolumeSchwinger_tendsto
    (params := params) k f

/-- **Existence of infinite volume Schwinger functions** (Theorem 11.2.1):
    For non-negative test functions, the limit
      S_k(f₁,...,fₖ) := lim_{n→∞} S_k^{Λₙ}(f₁,...,fₖ)
    exists (as a real number).

    For general (signed) test functions, existence follows by decomposing
    f = f⁺ - f⁻ and using multilinearity. -/
theorem infinite_volume_schwinger_exists (params : Phi4Params)
    (hbound : ∀ (k : ℕ) (f : Fin k → TestFun2D),
      ∃ C : ℝ, ∀ (n : ℕ) (hn : 0 < n),
        |schwingerN params (exhaustingRectangles n hn) k f| ≤ C)
    (hlim : ∀ (k : ℕ) (f : Fin k → TestFun2D),
      ∃ S : ℝ, Filter.Tendsto
        (fun n : ℕ =>
          if h : 0 < n then schwingerN params (exhaustingRectangles n h) k f else 0)
        Filter.atTop (nhds S))
    (k : ℕ) (f : Fin k → TestFun2D) :
    ∃ S : ℝ, Filter.Tendsto
      (fun n : ℕ => if h : 0 < n then schwingerN params (exhaustingRectangles n h) k f else 0)
      Filter.atTop (nhds S) := by
  classical
  rcases gap_infiniteVolumeSchwingerModel_nonempty params hbound hlim with ⟨hiv⟩
  letI : InfiniteVolumeSchwingerModel params := hiv
  exact infinite_volume_schwinger_exists_of_interface params k f

/-- Constructive infinite-volume Schwinger existence in interface-sequence form
    for fixed arity `k`, from `k`-point monotonicity and multiple-reflection
    bounds. -/
theorem infinite_volume_schwinger_exists_k_of_models (params : Phi4Params)
    (k : ℕ)
    [SchwingerNMonotoneModel params k]
    [MultipleReflectionModel params]
    (f : Fin k → TestFun2D)
    (hf : ∀ i, ∀ x, 0 ≤ f i x)
    (hfsupp : ∀ i, ∀ x ∉ (exhaustingRectangles 1 (Nat.succ_pos 0)).toSet, f i x = 0) :
    ∃ S : ℝ, Filter.Tendsto
      (fun n : ℕ =>
        if h : 0 < n then schwingerN params (exhaustingRectangles n h) k f else 0)
      Filter.atTop (nhds S) := by
  exact schwingerN_limit_exists_if_exhaustion_of_models
    (params := params) (k := k) f hf hfsupp

/-- All-arity existence endpoint under family-level monotonicity and
    multiple-reflection bounds. -/
theorem infinite_volume_schwinger_exists_all_k_of_family_models
    (params : Phi4Params)
    [SchwingerNMonotoneFamilyModel params]
    [MultipleReflectionModel params] :
    ∀ (k : ℕ) (f : Fin k → TestFun2D),
      (∀ i, ∀ x, 0 ≤ f i x) →
      (∀ i, ∀ x ∉ (exhaustingRectangles 1 (Nat.succ_pos 0)).toSet, f i x = 0) →
      ∃ S : ℝ, Filter.Tendsto
        (fun n : ℕ =>
          if h : 0 < n then schwingerN params (exhaustingRectangles n h) k f else 0)
        Filter.atTop (nhds S) := by
  intro k f hf hfsupp
  exact infinite_volume_schwinger_exists_k_of_models
    (params := params) (k := k) f hf hfsupp

/-- All-arity existence endpoint from family-level lattice monotonicity and
    multiple-reflection bounds. -/
theorem infinite_volume_schwinger_exists_all_k_of_lattice_family_models
    (params : Phi4Params)
    [LatticeSchwingerNMonotoneFamilyModel params]
    [MultipleReflectionModel params] :
    ∀ (k : ℕ) (f : Fin k → TestFun2D),
      (∀ i, ∀ x, 0 ≤ f i x) →
      (∀ i, ∀ x ∉ (exhaustingRectangles 1 (Nat.succ_pos 0)).toSet, f i x = 0) →
      ∃ S : ℝ, Filter.Tendsto
        (fun n : ℕ =>
          if h : 0 < n then schwingerN params (exhaustingRectangles n h) k f else 0)
        Filter.atTop (nhds S) := by
  intro k f hf hfsupp
  exact infinite_volume_schwinger_exists_k_of_models
    (params := params) (k := k) f hf hfsupp

/-- Constructive infinite-volume Schwinger existence in interface-sequence form
    for fixed arity `k`, from lattice `k`-point monotonicity infrastructure and
    multiple-reflection bounds. -/
theorem infinite_volume_schwinger_exists_k_of_lattice_models (params : Phi4Params)
    (k : ℕ)
    [LatticeSchwingerNMonotoneModel params k]
    [MultipleReflectionModel params]
    (f : Fin k → TestFun2D)
    (hf : ∀ i, ∀ x, 0 ≤ f i x)
    (hfsupp : ∀ i, ∀ x ∉ (exhaustingRectangles 1 (Nat.succ_pos 0)).toSet, f i x = 0) :
    ∃ S : ℝ, Filter.Tendsto
      (fun n : ℕ =>
        if h : 0 < n then schwingerN params (exhaustingRectangles n h) k f else 0)
      Filter.atTop (nhds S) := by
  exact infinite_volume_schwinger_exists_k_of_models
    (params := params) (k := k) f hf hfsupp

/-- Constructive `k = 4` infinite-volume Schwinger existence in the
    interface sequence form `if h : 0 < n then ... else 0`, from explicit
    four-point monotonicity and multiple-reflection bounds. -/
theorem infinite_volume_schwinger_exists_four_of_models (params : Phi4Params)
    [CorrelationFourPointModel params]
    [MultipleReflectionModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x)
    (hf₁supp : ∀ x ∉ (exhaustingRectangles 1 (Nat.succ_pos 0)).toSet, f₁ x = 0)
    (hf₂supp : ∀ x ∉ (exhaustingRectangles 1 (Nat.succ_pos 0)).toSet, f₂ x = 0)
    (hf₃supp : ∀ x ∉ (exhaustingRectangles 1 (Nat.succ_pos 0)).toSet, f₃ x = 0)
    (hf₄supp : ∀ x ∉ (exhaustingRectangles 1 (Nat.succ_pos 0)).toSet, f₄ x = 0) :
    ∃ S : ℝ, Filter.Tendsto
      (fun n : ℕ =>
        if h : 0 < n then schwingerN params (exhaustingRectangles n h) 4
          (![f₁, f₂, f₃, f₄] : Fin 4 → TestFun2D) else 0)
      Filter.atTop (nhds S) := by
  exact infinite_volume_schwinger_exists_k_of_models
    (params := params) (k := 4) (![f₁, f₂, f₃, f₄] : Fin 4 → TestFun2D)
    (by
      intro i x
      fin_cases i
      · exact hf₁ x
      · exact hf₂ x
      · exact hf₃ x
      · exact hf₄ x)
    (by
      intro i x hx
      fin_cases i
      · simpa using hf₁supp x hx
      · simpa using hf₂supp x hx
      · simpa using hf₃supp x hx
      · simpa using hf₄supp x hx)

/-- Lattice-bridge counterpart of
    `infinite_volume_schwinger_exists_four_of_models`. -/
theorem infinite_volume_schwinger_exists_four_of_lattice_models
    (params : Phi4Params)
    [LatticeSchwingerNMonotoneModel params 4]
    [MultipleReflectionModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x)
    (hf₁supp : ∀ x ∉ (exhaustingRectangles 1 (Nat.succ_pos 0)).toSet, f₁ x = 0)
    (hf₂supp : ∀ x ∉ (exhaustingRectangles 1 (Nat.succ_pos 0)).toSet, f₂ x = 0)
    (hf₃supp : ∀ x ∉ (exhaustingRectangles 1 (Nat.succ_pos 0)).toSet, f₃ x = 0)
    (hf₄supp : ∀ x ∉ (exhaustingRectangles 1 (Nat.succ_pos 0)).toSet, f₄ x = 0) :
    ∃ S : ℝ, Filter.Tendsto
      (fun n : ℕ =>
        if h : 0 < n then schwingerN params (exhaustingRectangles n h) 4
          (![f₁, f₂, f₃, f₄] : Fin 4 → TestFun2D) else 0)
      Filter.atTop (nhds S) := by
  exact infinite_volume_schwinger_exists_k_of_lattice_models
    (params := params) (k := 4) (![f₁, f₂, f₃, f₄] : Fin 4 → TestFun2D)
    (by
      intro i x
      fin_cases i
      · exact hf₁ x
      · exact hf₂ x
      · exact hf₃ x
      · exact hf₄ x)
    (by
      intro i x hx
      fin_cases i
      · simpa using hf₁supp x hx
      · simpa using hf₂supp x hx
      · simpa using hf₃supp x hx
      · simpa using hf₄supp x hx)

/-- Constructive `k = 2` infinite-volume Schwinger existence in the
    interface sequence form `if h : 0 < n then ... else 0`, under explicit
    two-point monotonicity and multiple-reflection bounds. -/
theorem infinite_volume_schwinger_exists_two_of_models (params : Phi4Params)
    [CorrelationTwoPointModel params]
    [MultipleReflectionModel params]
    (f g : TestFun2D)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupp : ∀ x ∉ (exhaustingRectangles 1 (Nat.succ_pos 0)).toSet, f x = 0)
    (hgsupp : ∀ x ∉ (exhaustingRectangles 1 (Nat.succ_pos 0)).toSet, g x = 0) :
    ∃ S : ℝ, Filter.Tendsto
      (fun n : ℕ =>
        if h : 0 < n then schwingerN params (exhaustingRectangles n h) 2
          (![f, g] : Fin 2 → TestFun2D) else 0)
      Filter.atTop (nhds S) := by
  exact infinite_volume_schwinger_exists_k_of_models
    (params := params) (k := 2) (![f, g] : Fin 2 → TestFun2D)
    (by
      intro i x
      fin_cases i
      · exact hf x
      · exact hg x)
    (by
      intro i x hx
      fin_cases i
      · simpa using hfsupp x hx
      · simpa using hgsupp x hx)

/-- Lattice-bridge counterpart of `infinite_volume_schwinger_exists_two_of_models`. -/
theorem infinite_volume_schwinger_exists_two_of_lattice_models (params : Phi4Params)
    [LatticeSchwingerTwoMonotoneModel params]
    [MultipleReflectionModel params]
    (f g : TestFun2D)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupp : ∀ x ∉ (exhaustingRectangles 1 (Nat.succ_pos 0)).toSet, f x = 0)
    (hgsupp : ∀ x ∉ (exhaustingRectangles 1 (Nat.succ_pos 0)).toSet, g x = 0) :
    ∃ S : ℝ, Filter.Tendsto
      (fun n : ℕ =>
        if h : 0 < n then schwingerN params (exhaustingRectangles n h) 2
          (![f, g] : Fin 2 → TestFun2D) else 0)
      Filter.atTop (nhds S) := by
  rcases latticeSchwingerNMonotoneModel_two_nonempty_of_latticeTwo
      (params := params) with ⟨hmonoN⟩
  letI : LatticeSchwingerNMonotoneModel params 2 := hmonoN
  exact infinite_volume_schwinger_exists_k_of_lattice_models
    (params := params) (k := 2) (![f, g] : Fin 2 → TestFun2D)
    (by
      intro i x
      fin_cases i
      · exact hf x
      · exact hg x)
    (by
      intro i x hx
      fin_cases i
      · simpa using hfsupp x hx
      · simpa using hgsupp x hx)

/-- The infinite volume Schwinger function. -/
def infiniteVolumeSchwinger (params : Phi4Params)
    [SchwingerLimitModel params]
    (k : ℕ)
    (f : Fin k → TestFun2D) : ℝ :=
  SchwingerLimitModel.infiniteVolumeSchwinger (params := params) k f

/-- Connected (truncated) 2-point function in infinite volume:
    `S₂(f,g) - S₁(f)S₁(g)`. -/
def connectedTwoPoint (params : Phi4Params)
    [SchwingerLimitModel params]
    (f g : TestFun2D) : ℝ :=
  infiniteVolumeSchwinger params 2 ![f, g] -
    infiniteVolumeSchwinger params 1 ![f] *
      infiniteVolumeSchwinger params 1 ![g]

@[simp] theorem connectedTwoPoint_eq (params : Phi4Params)
    [SchwingerLimitModel params] (f g : TestFun2D) :
    connectedTwoPoint params f g =
      infiniteVolumeSchwinger params 2 ![f, g] -
        infiniteVolumeSchwinger params 1 ![f] *
          infiniteVolumeSchwinger params 1 ![g] := rfl

/-- Permutation symmetry of infinite-volume Schwinger functions, inherited from
    finite-volume permutation symmetry along the standard exhaustion. -/
theorem infiniteVolumeSchwinger_perm (params : Phi4Params)
    [SchwingerLimitModel params]
    (n : ℕ) (f : Fin n → TestFun2D) (σ : Equiv.Perm (Fin n)) :
    infiniteVolumeSchwinger params n (f ∘ σ) =
      infiniteVolumeSchwinger params n f := by
  let a : ℕ → ℝ := fun m =>
    if h : 0 < m then schwingerN params (exhaustingRectangles m h) n (f ∘ σ) else 0
  let b : ℕ → ℝ := fun m =>
    if h : 0 < m then schwingerN params (exhaustingRectangles m h) n f else 0
  have ha : Filter.Tendsto a Filter.atTop (nhds (infiniteVolumeSchwinger params n (f ∘ σ))) := by
    simpa [a] using
      (SchwingerLimitModel.infiniteVolumeSchwinger_tendsto
        (params := params) n (f ∘ σ))
  have hb : Filter.Tendsto b Filter.atTop (nhds (infiniteVolumeSchwinger params n f)) := by
    simpa [b] using
      (SchwingerLimitModel.infiniteVolumeSchwinger_tendsto
        (params := params) n f)
  have hab : a = b := by
    funext m
    by_cases hm : 0 < m
    · simp [a, b, hm, schwingerN_perm]
    · simp [a, b, hm]
  rw [hab] at ha
  exact tendsto_nhds_unique ha hb

/-- Symmetry of the infinite-volume 2-point Schwinger function from the
    finite-volume symmetry and convergence along the exhausting rectangles. -/
theorem infiniteVolumeSchwinger_two_symm (params : Phi4Params)
    [SchwingerLimitModel params]
    (f g : TestFun2D) :
    infiniteVolumeSchwinger params 2 ![f, g] =
      infiniteVolumeSchwinger params 2 ![g, f] := by
  let σ : Equiv.Perm (Fin 2) := Equiv.swap 0 1
  have hperm := infiniteVolumeSchwinger_perm
    (params := params) 2 (![f, g] : Fin 2 → TestFun2D) σ
  have hswap : (![f, g] : Fin 2 → TestFun2D) ∘ σ = (![g, f] : Fin 2 → TestFun2D) := by
    funext i
    fin_cases i <;> simp [σ]
  calc
    infiniteVolumeSchwinger params 2 ![f, g]
        = infiniteVolumeSchwinger params 2 ((![f, g] : Fin 2 → TestFun2D) ∘ σ) := by
            simpa using hperm.symm
    _ = infiniteVolumeSchwinger params 2 (![g, f] : Fin 2 → TestFun2D) := by rw [hswap]

/-- Symmetry of the infinite-volume connected 2-point function. -/
theorem connectedTwoPoint_symm (params : Phi4Params)
    [SchwingerLimitModel params]
    (f g : TestFun2D) :
    connectedTwoPoint params f g = connectedTwoPoint params g f := by
  unfold connectedTwoPoint
  rw [infiniteVolumeSchwinger_two_symm]
  ring

/-! ### Infinite-volume 4-point cumulant -/

/-- Fully pairing-subtracted 4-point cumulant in infinite volume:
    `S₄ - (S₂(12)S₂(34) + S₂(13)S₂(24) + S₂(14)S₂(23))`. -/
def infiniteCumulantFourPoint (params : Phi4Params)
    [SchwingerLimitModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D) : ℝ :=
  infiniteVolumeSchwinger params 4 ![f₁, f₂, f₃, f₄] -
    (infiniteVolumeSchwinger params 2 ![f₁, f₂] *
      infiniteVolumeSchwinger params 2 ![f₃, f₄] +
      infiniteVolumeSchwinger params 2 ![f₁, f₃] *
      infiniteVolumeSchwinger params 2 ![f₂, f₄] +
      infiniteVolumeSchwinger params 2 ![f₁, f₄] *
      infiniteVolumeSchwinger params 2 ![f₂, f₃])

@[simp] theorem infiniteCumulantFourPoint_eq (params : Phi4Params)
    [SchwingerLimitModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D) :
    infiniteCumulantFourPoint params f₁ f₂ f₃ f₄ =
      infiniteVolumeSchwinger params 4 ![f₁, f₂, f₃, f₄] -
        (infiniteVolumeSchwinger params 2 ![f₁, f₂] *
          infiniteVolumeSchwinger params 2 ![f₃, f₄] +
          infiniteVolumeSchwinger params 2 ![f₁, f₃] *
          infiniteVolumeSchwinger params 2 ![f₂, f₄] +
          infiniteVolumeSchwinger params 2 ![f₁, f₄] *
          infiniteVolumeSchwinger params 2 ![f₂, f₃]) := rfl

/-- Along the exhausting rectangles, the finite-volume 4-point cumulant converges
    to the infinite-volume 4-point cumulant. -/
theorem cumulantFourPoint_tendsto_infinite
    (params : Phi4Params)
    [SchwingerLimitModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D) :
    Filter.Tendsto
      (fun n : ℕ => if h : 0 < n then
        cumulantFourPoint params (exhaustingRectangles n h) f₁ f₂ f₃ f₄
      else 0)
      Filter.atTop
      (nhds (infiniteCumulantFourPoint params f₁ f₂ f₃ f₄)) := by
  have h4 := SchwingerLimitModel.infiniteVolumeSchwinger_tendsto
    (params := params) 4 (![f₁, f₂, f₃, f₄] : Fin 4 → TestFun2D)
  have h12 := SchwingerLimitModel.infiniteVolumeSchwinger_tendsto
    (params := params) 2 (![f₁, f₂] : Fin 2 → TestFun2D)
  have h34 := SchwingerLimitModel.infiniteVolumeSchwinger_tendsto
    (params := params) 2 (![f₃, f₄] : Fin 2 → TestFun2D)
  have h13 := SchwingerLimitModel.infiniteVolumeSchwinger_tendsto
    (params := params) 2 (![f₁, f₃] : Fin 2 → TestFun2D)
  have h24 := SchwingerLimitModel.infiniteVolumeSchwinger_tendsto
    (params := params) 2 (![f₂, f₄] : Fin 2 → TestFun2D)
  have h14 := SchwingerLimitModel.infiniteVolumeSchwinger_tendsto
    (params := params) 2 (![f₁, f₄] : Fin 2 → TestFun2D)
  have h23 := SchwingerLimitModel.infiniteVolumeSchwinger_tendsto
    (params := params) 2 (![f₂, f₃] : Fin 2 → TestFun2D)
  have hprod12 := h12.mul h34
  have hprod13 := h13.mul h24
  have hprod14 := h14.mul h23
  have hsum := (hprod12.add hprod13).add hprod14
  have hsub := h4.sub hsum
  have hEqFun :
      (fun n : ℕ => if h : 0 < n then
        cumulantFourPoint params (exhaustingRectangles n h) f₁ f₂ f₃ f₄
      else 0)
      =
      (fun n : ℕ =>
        (if h : 0 < n then schwingerN params (exhaustingRectangles n h) 4
          (![f₁, f₂, f₃, f₄] : Fin 4 → TestFun2D) else 0) -
        ((if h : 0 < n then schwingerN params (exhaustingRectangles n h) 2
          (![f₁, f₂] : Fin 2 → TestFun2D) else 0) *
         (if h : 0 < n then schwingerN params (exhaustingRectangles n h) 2
          (![f₃, f₄] : Fin 2 → TestFun2D) else 0) +
         (if h : 0 < n then schwingerN params (exhaustingRectangles n h) 2
          (![f₁, f₃] : Fin 2 → TestFun2D) else 0) *
         (if h : 0 < n then schwingerN params (exhaustingRectangles n h) 2
          (![f₂, f₄] : Fin 2 → TestFun2D) else 0) +
         (if h : 0 < n then schwingerN params (exhaustingRectangles n h) 2
          (![f₁, f₄] : Fin 2 → TestFun2D) else 0) *
         (if h : 0 < n then schwingerN params (exhaustingRectangles n h) 2
          (![f₂, f₃] : Fin 2 → TestFun2D) else 0))) := by
    funext n
    by_cases h : 0 < n
    · simp [cumulantFourPoint, schwingerN_two_eq_schwingerTwo, h]
    · simp [h]
  have hEqLim :
      infiniteCumulantFourPoint params f₁ f₂ f₃ f₄
      =
      infiniteVolumeSchwinger params 4 (![f₁, f₂, f₃, f₄] : Fin 4 → TestFun2D) -
        (infiniteVolumeSchwinger params 2 (![f₁, f₂] : Fin 2 → TestFun2D) *
          infiniteVolumeSchwinger params 2 (![f₃, f₄] : Fin 2 → TestFun2D) +
          infiniteVolumeSchwinger params 2 (![f₁, f₃] : Fin 2 → TestFun2D) *
          infiniteVolumeSchwinger params 2 (![f₂, f₄] : Fin 2 → TestFun2D) +
          infiniteVolumeSchwinger params 2 (![f₁, f₄] : Fin 2 → TestFun2D) *
          infiniteVolumeSchwinger params 2 (![f₂, f₃] : Fin 2 → TestFun2D)) := by
    simp [infiniteCumulantFourPoint]
  rw [hEqFun, hEqLim]
  exact hsub

/-- Nonpositivity of the infinite-volume 4-point cumulant, inherited from the
    finite-volume Lebowitz inequality. -/
theorem infiniteCumulantFourPoint_nonpos
    (params : Phi4Params)
    [SchwingerLimitModel params]
    [CorrelationFourPointModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    infiniteCumulantFourPoint params f₁ f₂ f₃ f₄ ≤ 0 := by
  have hlim := cumulantFourPoint_tendsto_infinite params f₁ f₂ f₃ f₄
  have hnonpos : ∀ n : ℕ,
      (if h : 0 < n then
        cumulantFourPoint params (exhaustingRectangles n h) f₁ f₂ f₃ f₄
      else 0) ≤ 0 := by
    intro n
    by_cases h : 0 < n
    · have hfin := cumulantFourPoint_nonpos params (exhaustingRectangles n h)
        f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
      simpa [h] using hfin
    · simp [h]
  exact le_of_tendsto' hlim hnonpos

/-- Infinite-volume absolute-value control of the fully connected 4-point cumulant:
    `|U₄|` is bounded by the sum of the two nontrivial pairing channels. -/
theorem infiniteCumulantFourPoint_abs_bound
    (params : Phi4Params)
    [SchwingerLimitModel params]
    [CorrelationFourPointModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    |infiniteCumulantFourPoint params f₁ f₂ f₃ f₄| ≤
      infiniteVolumeSchwinger params 2 ![f₁, f₃] *
        infiniteVolumeSchwinger params 2 ![f₂, f₄] +
      infiniteVolumeSchwinger params 2 ![f₁, f₄] *
        infiniteVolumeSchwinger params 2 ![f₂, f₃] := by
  have hA := cumulantFourPoint_tendsto_infinite params f₁ f₂ f₃ f₄
  have h13 := SchwingerLimitModel.infiniteVolumeSchwinger_tendsto
    (params := params) 2 (![f₁, f₃] : Fin 2 → TestFun2D)
  have h24 := SchwingerLimitModel.infiniteVolumeSchwinger_tendsto
    (params := params) 2 (![f₂, f₄] : Fin 2 → TestFun2D)
  have h14 := SchwingerLimitModel.infiniteVolumeSchwinger_tendsto
    (params := params) 2 (![f₁, f₄] : Fin 2 → TestFun2D)
  have h23 := SchwingerLimitModel.infiniteVolumeSchwinger_tendsto
    (params := params) 2 (![f₂, f₃] : Fin 2 → TestFun2D)
  have hB : Filter.Tendsto
      (fun n : ℕ =>
        (if h : 0 < n then schwingerN params (exhaustingRectangles n h) 2
          (![f₁, f₃] : Fin 2 → TestFun2D) else 0) *
        (if h : 0 < n then schwingerN params (exhaustingRectangles n h) 2
          (![f₂, f₄] : Fin 2 → TestFun2D) else 0) +
        (if h : 0 < n then schwingerN params (exhaustingRectangles n h) 2
          (![f₁, f₄] : Fin 2 → TestFun2D) else 0) *
        (if h : 0 < n then schwingerN params (exhaustingRectangles n h) 2
          (![f₂, f₃] : Fin 2 → TestFun2D) else 0))
      Filter.atTop
      (nhds (infiniteVolumeSchwinger params 2 (![f₁, f₃] : Fin 2 → TestFun2D) *
        infiniteVolumeSchwinger params 2 (![f₂, f₄] : Fin 2 → TestFun2D) +
        infiniteVolumeSchwinger params 2 (![f₁, f₄] : Fin 2 → TestFun2D) *
        infiniteVolumeSchwinger params 2 (![f₂, f₃] : Fin 2 → TestFun2D))) := by
    exact (h13.mul h24).add (h14.mul h23)
  have hpointwise : ∀ n : ℕ,
      |(if h : 0 < n then
          cumulantFourPoint params (exhaustingRectangles n h) f₁ f₂ f₃ f₄
        else 0)|
      ≤
      (if h : 0 < n then schwingerN params (exhaustingRectangles n h) 2
        (![f₁, f₃] : Fin 2 → TestFun2D) else 0) *
      (if h : 0 < n then schwingerN params (exhaustingRectangles n h) 2
        (![f₂, f₄] : Fin 2 → TestFun2D) else 0) +
      (if h : 0 < n then schwingerN params (exhaustingRectangles n h) 2
        (![f₁, f₄] : Fin 2 → TestFun2D) else 0) *
      (if h : 0 < n then schwingerN params (exhaustingRectangles n h) 2
        (![f₂, f₃] : Fin 2 → TestFun2D) else 0) := by
    intro n
    by_cases h : 0 < n
    · have hfin := cumulantFourPoint_abs_bound params (exhaustingRectangles n h)
        f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
      simpa [schwingerN_two_eq_schwingerTwo, h] using hfin
    · simp [h]
  exact le_of_tendsto_of_tendsto' hA.abs hB hpointwise

/-- Three channel-wise lower bounds on the infinite-volume fully connected
    4-point cumulant, inherited from finite-volume GKS-II channels. -/
theorem infiniteCumulantFourPoint_lower_bounds_all_channels
    (params : Phi4Params)
    [SchwingerLimitModel params]
    [CorrelationFourPointModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    -(infiniteVolumeSchwinger params 2 ![f₁, f₃] *
      infiniteVolumeSchwinger params 2 ![f₂, f₄] +
      infiniteVolumeSchwinger params 2 ![f₁, f₄] *
      infiniteVolumeSchwinger params 2 ![f₂, f₃])
      ≤ infiniteCumulantFourPoint params f₁ f₂ f₃ f₄ ∧
    -(infiniteVolumeSchwinger params 2 ![f₁, f₂] *
      infiniteVolumeSchwinger params 2 ![f₃, f₄] +
      infiniteVolumeSchwinger params 2 ![f₁, f₄] *
      infiniteVolumeSchwinger params 2 ![f₂, f₃])
      ≤ infiniteCumulantFourPoint params f₁ f₂ f₃ f₄ ∧
    -(infiniteVolumeSchwinger params 2 ![f₁, f₂] *
      infiniteVolumeSchwinger params 2 ![f₃, f₄] +
      infiniteVolumeSchwinger params 2 ![f₁, f₃] *
      infiniteVolumeSchwinger params 2 ![f₂, f₄])
      ≤ infiniteCumulantFourPoint params f₁ f₂ f₃ f₄ := by
  have hA := cumulantFourPoint_tendsto_infinite params f₁ f₂ f₃ f₄
  have h12 := SchwingerLimitModel.infiniteVolumeSchwinger_tendsto
    (params := params) 2 (![f₁, f₂] : Fin 2 → TestFun2D)
  have h34 := SchwingerLimitModel.infiniteVolumeSchwinger_tendsto
    (params := params) 2 (![f₃, f₄] : Fin 2 → TestFun2D)
  have h13 := SchwingerLimitModel.infiniteVolumeSchwinger_tendsto
    (params := params) 2 (![f₁, f₃] : Fin 2 → TestFun2D)
  have h24 := SchwingerLimitModel.infiniteVolumeSchwinger_tendsto
    (params := params) 2 (![f₂, f₄] : Fin 2 → TestFun2D)
  have h14 := SchwingerLimitModel.infiniteVolumeSchwinger_tendsto
    (params := params) 2 (![f₁, f₄] : Fin 2 → TestFun2D)
  have h23 := SchwingerLimitModel.infiniteVolumeSchwinger_tendsto
    (params := params) 2 (![f₂, f₃] : Fin 2 → TestFun2D)
  have hB12 :
      Filter.Tendsto
        (fun n : ℕ =>
          -((if h : 0 < n then schwingerN params (exhaustingRectangles n h) 2
              (![f₁, f₃] : Fin 2 → TestFun2D) else 0) *
            (if h : 0 < n then schwingerN params (exhaustingRectangles n h) 2
              (![f₂, f₄] : Fin 2 → TestFun2D) else 0) +
            (if h : 0 < n then schwingerN params (exhaustingRectangles n h) 2
              (![f₁, f₄] : Fin 2 → TestFun2D) else 0) *
            (if h : 0 < n then schwingerN params (exhaustingRectangles n h) 2
              (![f₂, f₃] : Fin 2 → TestFun2D) else 0)))
        Filter.atTop
        (nhds (-(infiniteVolumeSchwinger params 2 (![f₁, f₃] : Fin 2 → TestFun2D) *
          infiniteVolumeSchwinger params 2 (![f₂, f₄] : Fin 2 → TestFun2D) +
          infiniteVolumeSchwinger params 2 (![f₁, f₄] : Fin 2 → TestFun2D) *
          infiniteVolumeSchwinger params 2 (![f₂, f₃] : Fin 2 → TestFun2D)))) := by
    exact ((h13.mul h24).add (h14.mul h23)).neg
  have hB13 :
      Filter.Tendsto
        (fun n : ℕ =>
          -((if h : 0 < n then schwingerN params (exhaustingRectangles n h) 2
              (![f₁, f₂] : Fin 2 → TestFun2D) else 0) *
            (if h : 0 < n then schwingerN params (exhaustingRectangles n h) 2
              (![f₃, f₄] : Fin 2 → TestFun2D) else 0) +
            (if h : 0 < n then schwingerN params (exhaustingRectangles n h) 2
              (![f₁, f₄] : Fin 2 → TestFun2D) else 0) *
            (if h : 0 < n then schwingerN params (exhaustingRectangles n h) 2
              (![f₂, f₃] : Fin 2 → TestFun2D) else 0)))
        Filter.atTop
        (nhds (-(infiniteVolumeSchwinger params 2 (![f₁, f₂] : Fin 2 → TestFun2D) *
          infiniteVolumeSchwinger params 2 (![f₃, f₄] : Fin 2 → TestFun2D) +
          infiniteVolumeSchwinger params 2 (![f₁, f₄] : Fin 2 → TestFun2D) *
          infiniteVolumeSchwinger params 2 (![f₂, f₃] : Fin 2 → TestFun2D)))) := by
    exact ((h12.mul h34).add (h14.mul h23)).neg
  have hB14 :
      Filter.Tendsto
        (fun n : ℕ =>
          -((if h : 0 < n then schwingerN params (exhaustingRectangles n h) 2
              (![f₁, f₂] : Fin 2 → TestFun2D) else 0) *
            (if h : 0 < n then schwingerN params (exhaustingRectangles n h) 2
              (![f₃, f₄] : Fin 2 → TestFun2D) else 0) +
            (if h : 0 < n then schwingerN params (exhaustingRectangles n h) 2
              (![f₁, f₃] : Fin 2 → TestFun2D) else 0) *
            (if h : 0 < n then schwingerN params (exhaustingRectangles n h) 2
              (![f₂, f₄] : Fin 2 → TestFun2D) else 0)))
        Filter.atTop
        (nhds (-(infiniteVolumeSchwinger params 2 (![f₁, f₂] : Fin 2 → TestFun2D) *
          infiniteVolumeSchwinger params 2 (![f₃, f₄] : Fin 2 → TestFun2D) +
          infiniteVolumeSchwinger params 2 (![f₁, f₃] : Fin 2 → TestFun2D) *
          infiniteVolumeSchwinger params 2 (![f₂, f₄] : Fin 2 → TestFun2D)))) := by
    exact ((h12.mul h34).add (h13.mul h24)).neg
  have hpoint12 : ∀ n : ℕ,
      -((if h : 0 < n then schwingerN params (exhaustingRectangles n h) 2
          (![f₁, f₃] : Fin 2 → TestFun2D) else 0) *
        (if h : 0 < n then schwingerN params (exhaustingRectangles n h) 2
          (![f₂, f₄] : Fin 2 → TestFun2D) else 0) +
        (if h : 0 < n then schwingerN params (exhaustingRectangles n h) 2
          (![f₁, f₄] : Fin 2 → TestFun2D) else 0) *
        (if h : 0 < n then schwingerN params (exhaustingRectangles n h) 2
          (![f₂, f₃] : Fin 2 → TestFun2D) else 0))
      ≤
      (if h : 0 < n then
        cumulantFourPoint params (exhaustingRectangles n h) f₁ f₂ f₃ f₄
      else 0) := by
    intro n
    by_cases h : 0 < n
    · have hfin := cumulantFourPoint_lower_bounds_all_channels
        params (exhaustingRectangles n h) f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
      rcases hfin with ⟨h12c, _, _⟩
      simpa [schwingerN_two_eq_schwingerTwo, h] using h12c
    · simp [h]
  have hpoint13 : ∀ n : ℕ,
      -((if h : 0 < n then schwingerN params (exhaustingRectangles n h) 2
          (![f₁, f₂] : Fin 2 → TestFun2D) else 0) *
        (if h : 0 < n then schwingerN params (exhaustingRectangles n h) 2
          (![f₃, f₄] : Fin 2 → TestFun2D) else 0) +
        (if h : 0 < n then schwingerN params (exhaustingRectangles n h) 2
          (![f₁, f₄] : Fin 2 → TestFun2D) else 0) *
        (if h : 0 < n then schwingerN params (exhaustingRectangles n h) 2
          (![f₂, f₃] : Fin 2 → TestFun2D) else 0))
      ≤
      (if h : 0 < n then
        cumulantFourPoint params (exhaustingRectangles n h) f₁ f₂ f₃ f₄
      else 0) := by
    intro n
    by_cases h : 0 < n
    · have hfin := cumulantFourPoint_lower_bounds_all_channels
        params (exhaustingRectangles n h) f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
      rcases hfin with ⟨_, h13c, _⟩
      simpa [schwingerN_two_eq_schwingerTwo, h] using h13c
    · simp [h]
  have hpoint14 : ∀ n : ℕ,
      -((if h : 0 < n then schwingerN params (exhaustingRectangles n h) 2
          (![f₁, f₂] : Fin 2 → TestFun2D) else 0) *
        (if h : 0 < n then schwingerN params (exhaustingRectangles n h) 2
          (![f₃, f₄] : Fin 2 → TestFun2D) else 0) +
        (if h : 0 < n then schwingerN params (exhaustingRectangles n h) 2
          (![f₁, f₃] : Fin 2 → TestFun2D) else 0) *
        (if h : 0 < n then schwingerN params (exhaustingRectangles n h) 2
          (![f₂, f₄] : Fin 2 → TestFun2D) else 0))
      ≤
      (if h : 0 < n then
        cumulantFourPoint params (exhaustingRectangles n h) f₁ f₂ f₃ f₄
      else 0) := by
    intro n
    by_cases h : 0 < n
    · have hfin := cumulantFourPoint_lower_bounds_all_channels
        params (exhaustingRectangles n h) f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
      rcases hfin with ⟨_, _, h14c⟩
      simpa [schwingerN_two_eq_schwingerTwo, h] using h14c
    · simp [h]
  have hlim12 :
      -(infiniteVolumeSchwinger params 2 ![f₁, f₃] *
        infiniteVolumeSchwinger params 2 ![f₂, f₄] +
        infiniteVolumeSchwinger params 2 ![f₁, f₄] *
        infiniteVolumeSchwinger params 2 ![f₂, f₃]) ≤
      infiniteCumulantFourPoint params f₁ f₂ f₃ f₄ := by
    exact le_of_tendsto_of_tendsto' hB12 hA hpoint12
  have hlim13 :
      -(infiniteVolumeSchwinger params 2 ![f₁, f₂] *
        infiniteVolumeSchwinger params 2 ![f₃, f₄] +
        infiniteVolumeSchwinger params 2 ![f₁, f₄] *
        infiniteVolumeSchwinger params 2 ![f₂, f₃]) ≤
      infiniteCumulantFourPoint params f₁ f₂ f₃ f₄ := by
    exact le_of_tendsto_of_tendsto' hB13 hA hpoint13
  have hlim14 :
      -(infiniteVolumeSchwinger params 2 ![f₁, f₂] *
        infiniteVolumeSchwinger params 2 ![f₃, f₄] +
        infiniteVolumeSchwinger params 2 ![f₁, f₃] *
        infiniteVolumeSchwinger params 2 ![f₂, f₄]) ≤
      infiniteCumulantFourPoint params f₁ f₂ f₃ f₄ := by
    exact le_of_tendsto_of_tendsto' hB14 hA hpoint14
  exact ⟨hlim12, hlim13, hlim14⟩

/-- Alternative absolute-value bound on the infinite-volume cumulant using the
    `(13)(24)` lower channel. -/
theorem infiniteCumulantFourPoint_abs_bound_alt13
    (params : Phi4Params)
    [SchwingerLimitModel params]
    [CorrelationFourPointModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    |infiniteCumulantFourPoint params f₁ f₂ f₃ f₄| ≤
      infiniteVolumeSchwinger params 2 ![f₁, f₂] *
        infiniteVolumeSchwinger params 2 ![f₃, f₄] +
      infiniteVolumeSchwinger params 2 ![f₁, f₄] *
        infiniteVolumeSchwinger params 2 ![f₂, f₃] := by
  have hnonpos := infiniteCumulantFourPoint_nonpos params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  have hLowerAll := infiniteCumulantFourPoint_lower_bounds_all_channels
    params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  rcases hLowerAll with ⟨_, h13, _⟩
  rw [abs_of_nonpos hnonpos]
  linarith

/-- Alternative absolute-value bound on the infinite-volume cumulant using the
    `(14)(23)` lower channel. -/
theorem infiniteCumulantFourPoint_abs_bound_alt14
    (params : Phi4Params)
    [SchwingerLimitModel params]
    [CorrelationFourPointModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    |infiniteCumulantFourPoint params f₁ f₂ f₃ f₄| ≤
      infiniteVolumeSchwinger params 2 ![f₁, f₂] *
        infiniteVolumeSchwinger params 2 ![f₃, f₄] +
      infiniteVolumeSchwinger params 2 ![f₁, f₃] *
        infiniteVolumeSchwinger params 2 ![f₂, f₄] := by
  have hnonpos := infiniteCumulantFourPoint_nonpos params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  have hLowerAll := infiniteCumulantFourPoint_lower_bounds_all_channels
    params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  rcases hLowerAll with ⟨_, _, h14⟩
  rw [abs_of_nonpos hnonpos]
  linarith

/-- Infinite-volume analog of the finite-volume all-channel 4-point bounds:
    each GKS-II channel gives a lower bound and Lebowitz gives the upper bound. -/
theorem infiniteSchwinger_four_bounds_all_channels
    (params : Phi4Params)
    [SchwingerLimitModel params]
    [CorrelationFourPointModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    max (infiniteVolumeSchwinger params 2 ![f₁, f₂] *
      infiniteVolumeSchwinger params 2 ![f₃, f₄])
      (max (infiniteVolumeSchwinger params 2 ![f₁, f₃] *
        infiniteVolumeSchwinger params 2 ![f₂, f₄])
        (infiniteVolumeSchwinger params 2 ![f₁, f₄] *
          infiniteVolumeSchwinger params 2 ![f₂, f₃]))
      ≤ infiniteVolumeSchwinger params 4 ![f₁, f₂, f₃, f₄] ∧
    infiniteVolumeSchwinger params 4 ![f₁, f₂, f₃, f₄] ≤
      infiniteVolumeSchwinger params 2 ![f₁, f₂] *
        infiniteVolumeSchwinger params 2 ![f₃, f₄] +
      infiniteVolumeSchwinger params 2 ![f₁, f₃] *
        infiniteVolumeSchwinger params 2 ![f₂, f₄] +
      infiniteVolumeSchwinger params 2 ![f₁, f₄] *
        infiniteVolumeSchwinger params 2 ![f₂, f₃] := by
  have hnonpos := infiniteCumulantFourPoint_nonpos params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  have hlower := infiniteCumulantFourPoint_lower_bounds_all_channels
    params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  rcases hlower with ⟨h12, h13, h14⟩
  have hA :
      infiniteVolumeSchwinger params 2 ![f₁, f₂] *
        infiniteVolumeSchwinger params 2 ![f₃, f₄] ≤
      infiniteVolumeSchwinger params 4 ![f₁, f₂, f₃, f₄] := by
    unfold infiniteCumulantFourPoint at h12
    linarith
  have hB :
      infiniteVolumeSchwinger params 2 ![f₁, f₃] *
        infiniteVolumeSchwinger params 2 ![f₂, f₄] ≤
      infiniteVolumeSchwinger params 4 ![f₁, f₂, f₃, f₄] := by
    unfold infiniteCumulantFourPoint at h13
    linarith
  have hC :
      infiniteVolumeSchwinger params 2 ![f₁, f₄] *
        infiniteVolumeSchwinger params 2 ![f₂, f₃] ≤
      infiniteVolumeSchwinger params 4 ![f₁, f₂, f₃, f₄] := by
    unfold infiniteCumulantFourPoint at h14
    linarith
  have hUpper :
      infiniteVolumeSchwinger params 4 ![f₁, f₂, f₃, f₄] ≤
      infiniteVolumeSchwinger params 2 ![f₁, f₂] *
        infiniteVolumeSchwinger params 2 ![f₃, f₄] +
      infiniteVolumeSchwinger params 2 ![f₁, f₃] *
        infiniteVolumeSchwinger params 2 ![f₂, f₄] +
      infiniteVolumeSchwinger params 2 ![f₁, f₄] *
        infiniteVolumeSchwinger params 2 ![f₂, f₃] := by
    unfold infiniteCumulantFourPoint at hnonpos
    linarith
  constructor
  · exact max_le hA (max_le hB hC)
  · exact hUpper

/-! ### Infinite-volume pairing-subtracted 4-point channels -/

/-- The infinite-volume `(12)(34)` pairing-subtracted 4-point quantity
    `S₄^∞ - S₂^∞(12)S₂^∞(34)`. -/
def infiniteTruncatedFourPoint12 (params : Phi4Params)
    [SchwingerLimitModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D) : ℝ :=
  infiniteVolumeSchwinger params 4 ![f₁, f₂, f₃, f₄] -
    infiniteVolumeSchwinger params 2 ![f₁, f₂] *
      infiniteVolumeSchwinger params 2 ![f₃, f₄]

/-- The infinite-volume `(13)(24)` pairing-subtracted 4-point quantity
    `S₄^∞ - S₂^∞(13)S₂^∞(24)`. -/
def infiniteTruncatedFourPoint13 (params : Phi4Params)
    [SchwingerLimitModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D) : ℝ :=
  infiniteVolumeSchwinger params 4 ![f₁, f₂, f₃, f₄] -
    infiniteVolumeSchwinger params 2 ![f₁, f₃] *
      infiniteVolumeSchwinger params 2 ![f₂, f₄]

/-- The infinite-volume `(14)(23)` pairing-subtracted 4-point quantity
    `S₄^∞ - S₂^∞(14)S₂^∞(23)`. -/
def infiniteTruncatedFourPoint14 (params : Phi4Params)
    [SchwingerLimitModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D) : ℝ :=
  infiniteVolumeSchwinger params 4 ![f₁, f₂, f₃, f₄] -
    infiniteVolumeSchwinger params 2 ![f₁, f₄] *
      infiniteVolumeSchwinger params 2 ![f₂, f₃]

/-- Nonnegativity of the infinite-volume `(12)(34)` pairing-subtracted channel. -/
theorem infiniteTruncatedFourPoint12_nonneg
    (params : Phi4Params)
    [SchwingerLimitModel params]
    [CorrelationFourPointModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    0 ≤ infiniteTruncatedFourPoint12 params f₁ f₂ f₃ f₄ := by
  have hlower := infiniteCumulantFourPoint_lower_bounds_all_channels
    params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  rcases hlower with ⟨h12, _, _⟩
  unfold infiniteTruncatedFourPoint12
  unfold infiniteCumulantFourPoint at h12
  linarith

/-- Nonnegativity of the infinite-volume `(13)(24)` pairing-subtracted channel. -/
theorem infiniteTruncatedFourPoint13_nonneg
    (params : Phi4Params)
    [SchwingerLimitModel params]
    [CorrelationFourPointModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    0 ≤ infiniteTruncatedFourPoint13 params f₁ f₂ f₃ f₄ := by
  have hlower := infiniteCumulantFourPoint_lower_bounds_all_channels
    params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  rcases hlower with ⟨_, h13, _⟩
  unfold infiniteTruncatedFourPoint13
  unfold infiniteCumulantFourPoint at h13
  linarith

/-- Nonnegativity of the infinite-volume `(14)(23)` pairing-subtracted channel. -/
theorem infiniteTruncatedFourPoint14_nonneg
    (params : Phi4Params)
    [SchwingerLimitModel params]
    [CorrelationFourPointModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    0 ≤ infiniteTruncatedFourPoint14 params f₁ f₂ f₃ f₄ := by
  have hlower := infiniteCumulantFourPoint_lower_bounds_all_channels
    params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  rcases hlower with ⟨_, _, h14⟩
  unfold infiniteTruncatedFourPoint14
  unfold infiniteCumulantFourPoint at h14
  linarith

/-- Upper bound on the infinite-volume `(12)(34)` pairing-subtracted channel. -/
theorem infiniteTruncatedFourPoint12_upper
    (params : Phi4Params)
    [SchwingerLimitModel params]
    [CorrelationFourPointModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    infiniteTruncatedFourPoint12 params f₁ f₂ f₃ f₄ ≤
      infiniteVolumeSchwinger params 2 ![f₁, f₃] *
        infiniteVolumeSchwinger params 2 ![f₂, f₄] +
      infiniteVolumeSchwinger params 2 ![f₁, f₄] *
        infiniteVolumeSchwinger params 2 ![f₂, f₃] := by
  have hbounds := infiniteSchwinger_four_bounds_all_channels
    params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  rcases hbounds with ⟨_, hupper⟩
  unfold infiniteTruncatedFourPoint12
  linarith

/-- Upper bound on the infinite-volume `(13)(24)` pairing-subtracted channel. -/
theorem infiniteTruncatedFourPoint13_upper
    (params : Phi4Params)
    [SchwingerLimitModel params]
    [CorrelationFourPointModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    infiniteTruncatedFourPoint13 params f₁ f₂ f₃ f₄ ≤
      infiniteVolumeSchwinger params 2 ![f₁, f₂] *
        infiniteVolumeSchwinger params 2 ![f₃, f₄] +
      infiniteVolumeSchwinger params 2 ![f₁, f₄] *
        infiniteVolumeSchwinger params 2 ![f₂, f₃] := by
  have hbounds := infiniteSchwinger_four_bounds_all_channels
    params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  rcases hbounds with ⟨_, hupper⟩
  unfold infiniteTruncatedFourPoint13
  linarith

/-- Upper bound on the infinite-volume `(14)(23)` pairing-subtracted channel. -/
theorem infiniteTruncatedFourPoint14_upper
    (params : Phi4Params)
    [SchwingerLimitModel params]
    [CorrelationFourPointModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    infiniteTruncatedFourPoint14 params f₁ f₂ f₃ f₄ ≤
      infiniteVolumeSchwinger params 2 ![f₁, f₂] *
        infiniteVolumeSchwinger params 2 ![f₃, f₄] +
      infiniteVolumeSchwinger params 2 ![f₁, f₃] *
        infiniteVolumeSchwinger params 2 ![f₂, f₄] := by
  have hbounds := infiniteSchwinger_four_bounds_all_channels
    params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  rcases hbounds with ⟨_, hupper⟩
  unfold infiniteTruncatedFourPoint14
  linarith

/-- Absolute-value bound for the infinite-volume `(12)(34)` pairing-subtracted
    4-point channel. -/
theorem infiniteTruncatedFourPoint12_abs_bound
    (params : Phi4Params)
    [SchwingerLimitModel params]
    [CorrelationFourPointModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    |infiniteTruncatedFourPoint12 params f₁ f₂ f₃ f₄| ≤
      infiniteVolumeSchwinger params 2 ![f₁, f₃] *
        infiniteVolumeSchwinger params 2 ![f₂, f₄] +
      infiniteVolumeSchwinger params 2 ![f₁, f₄] *
        infiniteVolumeSchwinger params 2 ![f₂, f₃] := by
  have hnonneg := infiniteTruncatedFourPoint12_nonneg params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  have hupper := infiniteTruncatedFourPoint12_upper params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  simpa [abs_of_nonneg hnonneg] using hupper

/-- Absolute-value bound for the infinite-volume `(13)(24)` pairing-subtracted
    4-point channel. -/
theorem infiniteTruncatedFourPoint13_abs_bound
    (params : Phi4Params)
    [SchwingerLimitModel params]
    [CorrelationFourPointModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    |infiniteTruncatedFourPoint13 params f₁ f₂ f₃ f₄| ≤
      infiniteVolumeSchwinger params 2 ![f₁, f₂] *
        infiniteVolumeSchwinger params 2 ![f₃, f₄] +
      infiniteVolumeSchwinger params 2 ![f₁, f₄] *
        infiniteVolumeSchwinger params 2 ![f₂, f₃] := by
  have hnonneg := infiniteTruncatedFourPoint13_nonneg params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  have hupper := infiniteTruncatedFourPoint13_upper params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  simpa [abs_of_nonneg hnonneg] using hupper

/-- Absolute-value bound for the infinite-volume `(14)(23)` pairing-subtracted
    4-point channel. -/
theorem infiniteTruncatedFourPoint14_abs_bound
    (params : Phi4Params)
    [SchwingerLimitModel params]
    [CorrelationFourPointModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    |infiniteTruncatedFourPoint14 params f₁ f₂ f₃ f₄| ≤
      infiniteVolumeSchwinger params 2 ![f₁, f₂] *
        infiniteVolumeSchwinger params 2 ![f₃, f₄] +
      infiniteVolumeSchwinger params 2 ![f₁, f₃] *
        infiniteVolumeSchwinger params 2 ![f₂, f₄] := by
  have hnonneg := infiniteTruncatedFourPoint14_nonneg params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  have hupper := infiniteTruncatedFourPoint14_upper params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  simpa [abs_of_nonneg hnonneg] using hupper

/-- Two-sided bounds for the infinite-volume `(12)(34)` pairing-subtracted
    4-point channel. -/
theorem infiniteTruncatedFourPoint12_bounds
    (params : Phi4Params)
    [SchwingerLimitModel params]
    [CorrelationFourPointModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    0 ≤ infiniteTruncatedFourPoint12 params f₁ f₂ f₃ f₄ ∧
      infiniteTruncatedFourPoint12 params f₁ f₂ f₃ f₄ ≤
        infiniteVolumeSchwinger params 2 ![f₁, f₃] *
          infiniteVolumeSchwinger params 2 ![f₂, f₄] +
        infiniteVolumeSchwinger params 2 ![f₁, f₄] *
          infiniteVolumeSchwinger params 2 ![f₂, f₃] := by
  constructor
  · exact infiniteTruncatedFourPoint12_nonneg params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  · exact infiniteTruncatedFourPoint12_upper params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄

/-- Two-sided bounds for the infinite-volume `(13)(24)` pairing-subtracted
    4-point channel. -/
theorem infiniteTruncatedFourPoint13_bounds
    (params : Phi4Params)
    [SchwingerLimitModel params]
    [CorrelationFourPointModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    0 ≤ infiniteTruncatedFourPoint13 params f₁ f₂ f₃ f₄ ∧
      infiniteTruncatedFourPoint13 params f₁ f₂ f₃ f₄ ≤
        infiniteVolumeSchwinger params 2 ![f₁, f₂] *
          infiniteVolumeSchwinger params 2 ![f₃, f₄] +
        infiniteVolumeSchwinger params 2 ![f₁, f₄] *
          infiniteVolumeSchwinger params 2 ![f₂, f₃] := by
  constructor
  · exact infiniteTruncatedFourPoint13_nonneg params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  · exact infiniteTruncatedFourPoint13_upper params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄

/-- Two-sided bounds for the infinite-volume `(14)(23)` pairing-subtracted
    4-point channel. -/
theorem infiniteTruncatedFourPoint14_bounds
    (params : Phi4Params)
    [SchwingerLimitModel params]
    [CorrelationFourPointModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    0 ≤ infiniteTruncatedFourPoint14 params f₁ f₂ f₃ f₄ ∧
      infiniteTruncatedFourPoint14 params f₁ f₂ f₃ f₄ ≤
        infiniteVolumeSchwinger params 2 ![f₁, f₂] *
          infiniteVolumeSchwinger params 2 ![f₃, f₄] +
        infiniteVolumeSchwinger params 2 ![f₁, f₃] *
          infiniteVolumeSchwinger params 2 ![f₂, f₄] := by
  constructor
  · exact infiniteTruncatedFourPoint14_nonneg params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  · exact infiniteTruncatedFourPoint14_upper params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄

/-- Combined two-sided bounds for all three infinite-volume pairing-subtracted
    4-point channels. -/
theorem infiniteTruncatedFourPoint_bounds_all_channels
    (params : Phi4Params)
    [SchwingerLimitModel params]
    [CorrelationFourPointModel params]
    (f₁ f₂ f₃ f₄ : TestFun2D)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (hf₃ : ∀ x, 0 ≤ f₃ x) (hf₄ : ∀ x, 0 ≤ f₄ x) :
    0 ≤ infiniteTruncatedFourPoint12 params f₁ f₂ f₃ f₄ ∧
      infiniteTruncatedFourPoint12 params f₁ f₂ f₃ f₄ ≤
        infiniteVolumeSchwinger params 2 ![f₁, f₃] *
          infiniteVolumeSchwinger params 2 ![f₂, f₄] +
        infiniteVolumeSchwinger params 2 ![f₁, f₄] *
          infiniteVolumeSchwinger params 2 ![f₂, f₃] ∧
    0 ≤ infiniteTruncatedFourPoint13 params f₁ f₂ f₃ f₄ ∧
      infiniteTruncatedFourPoint13 params f₁ f₂ f₃ f₄ ≤
        infiniteVolumeSchwinger params 2 ![f₁, f₂] *
          infiniteVolumeSchwinger params 2 ![f₃, f₄] +
        infiniteVolumeSchwinger params 2 ![f₁, f₄] *
          infiniteVolumeSchwinger params 2 ![f₂, f₃] ∧
    0 ≤ infiniteTruncatedFourPoint14 params f₁ f₂ f₃ f₄ ∧
      infiniteTruncatedFourPoint14 params f₁ f₂ f₃ f₄ ≤
        infiniteVolumeSchwinger params 2 ![f₁, f₂] *
          infiniteVolumeSchwinger params 2 ![f₃, f₄] +
        infiniteVolumeSchwinger params 2 ![f₁, f₃] *
          infiniteVolumeSchwinger params 2 ![f₂, f₄] := by
  constructor
  · exact infiniteTruncatedFourPoint12_nonneg params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
  · constructor
    · exact infiniteTruncatedFourPoint12_upper params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
    · constructor
      · exact infiniteTruncatedFourPoint13_nonneg params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
      · constructor
        · exact infiniteTruncatedFourPoint13_upper params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
        · constructor
          · exact infiniteTruncatedFourPoint14_nonneg params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄
          · exact infiniteTruncatedFourPoint14_upper params f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄

/-- Along the exhausting rectangles, the finite-volume connected two-point
    function converges to the infinite-volume connected two-point function. -/
theorem connectedSchwingerTwo_tendsto_infinite
    (params : Phi4Params)
    [SchwingerLimitModel params]
    (f g : TestFun2D) :
    Filter.Tendsto
      (fun n : ℕ => if h : 0 < n then
        connectedSchwingerTwo params (exhaustingRectangles n h) f g
      else 0)
      Filter.atTop
      (nhds (connectedTwoPoint params f g)) := by
  have h2 := SchwingerLimitModel.infiniteVolumeSchwinger_tendsto
    (params := params) 2 (![f, g] : Fin 2 → TestFun2D)
  have h1f := SchwingerLimitModel.infiniteVolumeSchwinger_tendsto
    (params := params) 1 (![f] : Fin 1 → TestFun2D)
  have h1g := SchwingerLimitModel.infiniteVolumeSchwinger_tendsto
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

private theorem connectedSchwingerTwo_add_left
    (params : Phi4Params) [InteractionWeightModel params]
    (Λ : Rectangle) (f₁ f₂ g : TestFun2D) :
    connectedSchwingerTwo params Λ (f₁ + f₂) g =
      connectedSchwingerTwo params Λ f₁ g +
        connectedSchwingerTwo params Λ f₂ g := by
  unfold connectedSchwingerTwo
  rw [schwingerTwo_add_left, schwingerOne_add]
  ring

private theorem connectedSchwingerTwo_smul_left
    (params : Phi4Params) [InteractionWeightModel params]
    (Λ : Rectangle) (c : ℝ) (f g : TestFun2D) :
    connectedSchwingerTwo params Λ (c • f) g =
      c * connectedSchwingerTwo params Λ f g := by
  unfold connectedSchwingerTwo
  rw [schwingerTwo_smul_left, schwingerOne_smul]
  ring

/-- Additivity in the first argument of the infinite-volume connected two-point
    function, transferred from finite volume by convergence along the exhaustion. -/
theorem connectedTwoPoint_add_left
    (params : Phi4Params)
    [SchwingerLimitModel params]
    [InteractionWeightModel params]
    (f₁ f₂ g : TestFun2D) :
    connectedTwoPoint params (f₁ + f₂) g =
      connectedTwoPoint params f₁ g + connectedTwoPoint params f₂ g := by
  let A : ℕ → ℝ := fun n =>
    if h : 0 < n then connectedSchwingerTwo params (exhaustingRectangles n h) (f₁ + f₂) g else 0
  let B : ℕ → ℝ := fun n =>
    if h : 0 < n then connectedSchwingerTwo params (exhaustingRectangles n h) f₁ g else 0
  let C : ℕ → ℝ := fun n =>
    if h : 0 < n then connectedSchwingerTwo params (exhaustingRectangles n h) f₂ g else 0
  have hA : Filter.Tendsto A Filter.atTop (nhds (connectedTwoPoint params (f₁ + f₂) g)) := by
    simpa [A] using connectedSchwingerTwo_tendsto_infinite params (f₁ + f₂) g
  have hB : Filter.Tendsto B Filter.atTop (nhds (connectedTwoPoint params f₁ g)) := by
    simpa [B] using connectedSchwingerTwo_tendsto_infinite params f₁ g
  have hC : Filter.Tendsto C Filter.atTop (nhds (connectedTwoPoint params f₂ g)) := by
    simpa [C] using connectedSchwingerTwo_tendsto_infinite params f₂ g
  have hBC : Filter.Tendsto (fun n => B n + C n) Filter.atTop
      (nhds (connectedTwoPoint params f₁ g + connectedTwoPoint params f₂ g)) :=
    hB.add hC
  have hEq : A = fun n => B n + C n := by
    funext n
    by_cases hn : 0 < n
    · have hconn :
        connectedSchwingerTwo params (exhaustingRectangles n hn) (f₁ + f₂) g =
          connectedSchwingerTwo params (exhaustingRectangles n hn) f₁ g +
            connectedSchwingerTwo params (exhaustingRectangles n hn) f₂ g :=
        connectedSchwingerTwo_add_left params (exhaustingRectangles n hn) f₁ f₂ g
      simpa [A, B, C, hn] using hconn
    · simp [A, B, C, hn]
  rw [hEq] at hA
  exact tendsto_nhds_unique hA hBC

/-- Scalar linearity in the first argument of the infinite-volume connected
    two-point function, transferred from finite volume by convergence. -/
theorem connectedTwoPoint_smul_left
    (params : Phi4Params)
    [SchwingerLimitModel params]
    [InteractionWeightModel params]
    (c : ℝ) (f g : TestFun2D) :
    connectedTwoPoint params (c • f) g = c * connectedTwoPoint params f g := by
  let A : ℕ → ℝ := fun n =>
    if h : 0 < n then connectedSchwingerTwo params (exhaustingRectangles n h) (c • f) g else 0
  let B : ℕ → ℝ := fun n =>
    if h : 0 < n then connectedSchwingerTwo params (exhaustingRectangles n h) f g else 0
  have hA : Filter.Tendsto A Filter.atTop (nhds (connectedTwoPoint params (c • f) g)) := by
    simpa [A] using connectedSchwingerTwo_tendsto_infinite params (c • f) g
  have hB : Filter.Tendsto B Filter.atTop (nhds (connectedTwoPoint params f g)) := by
    simpa [B] using connectedSchwingerTwo_tendsto_infinite params f g
  have hcB : Filter.Tendsto (fun n => c * B n) Filter.atTop (nhds (c * connectedTwoPoint params f g)) :=
    hB.const_mul c
  have hEq : A = fun n => c * B n := by
    funext n
    by_cases hn : 0 < n
    · have hconn :
        connectedSchwingerTwo params (exhaustingRectangles n hn) (c • f) g =
          c * connectedSchwingerTwo params (exhaustingRectangles n hn) f g :=
        connectedSchwingerTwo_smul_left params (exhaustingRectangles n hn) c f g
      simpa [A, B, hn] using hconn
    · simp [A, B, hn]
  rw [hEq] at hA
  exact tendsto_nhds_unique hA hcB

/-- Additivity in the second argument of the infinite-volume connected two-point
    function. -/
theorem connectedTwoPoint_add_right
    (params : Phi4Params)
    [SchwingerLimitModel params]
    [InteractionWeightModel params]
    (f g₁ g₂ : TestFun2D) :
    connectedTwoPoint params f (g₁ + g₂) =
      connectedTwoPoint params f g₁ + connectedTwoPoint params f g₂ := by
  calc
    connectedTwoPoint params f (g₁ + g₂)
        = connectedTwoPoint params (g₁ + g₂) f := connectedTwoPoint_symm params f (g₁ + g₂)
    _ = connectedTwoPoint params g₁ f + connectedTwoPoint params g₂ f :=
          connectedTwoPoint_add_left params g₁ g₂ f
    _ = connectedTwoPoint params f g₁ + connectedTwoPoint params f g₂ := by
          rw [connectedTwoPoint_symm params g₁ f, connectedTwoPoint_symm params g₂ f]

/-- Scalar linearity in the second argument of the infinite-volume connected
    two-point function. -/
theorem connectedTwoPoint_smul_right
    (params : Phi4Params)
    [SchwingerLimitModel params]
    [InteractionWeightModel params]
    (c : ℝ) (f g : TestFun2D) :
    connectedTwoPoint params f (c • g) = c * connectedTwoPoint params f g := by
  calc
    connectedTwoPoint params f (c • g)
        = connectedTwoPoint params (c • g) f := connectedTwoPoint_symm params f (c • g)
    _ = c * connectedTwoPoint params g f := connectedTwoPoint_smul_left params c g f
    _ = c * connectedTwoPoint params f g := by rw [connectedTwoPoint_symm params g f]

/-- Infinite-volume connected two-point function as a bilinear map. -/
def connectedTwoPointBilinear (params : Phi4Params)
    [SchwingerLimitModel params]
    [InteractionWeightModel params] :
    TestFun2D →ₗ[ℝ] TestFun2D →ₗ[ℝ] ℝ where
  toFun f :=
    { toFun := fun g => connectedTwoPoint params f g
      map_add' := by
        intro g₁ g₂
        exact connectedTwoPoint_add_right params f g₁ g₂
      map_smul' := by
        intro c g
        exact connectedTwoPoint_smul_right params c f g }
  map_add' := by
    intro f₁ f₂
    ext g
    exact connectedTwoPoint_add_left params f₁ f₂ g
  map_smul' := by
    intro c f
    ext g
    exact connectedTwoPoint_smul_left params c f g

/-- Symmetry of the infinite-volume connected two-point bilinear form. -/
theorem connectedTwoPointBilinear_symm (params : Phi4Params)
    [SchwingerLimitModel params]
    [InteractionWeightModel params]
    (f g : TestFun2D) :
    connectedTwoPointBilinear params f g =
      connectedTwoPointBilinear params g f := by
  simpa [connectedTwoPointBilinear] using
    connectedTwoPoint_symm params f g

/-- Diagonal connected two-point nonnegativity in infinite volume, obtained from
    finite-volume variance positivity and convergence along the exhaustion. -/
theorem connectedTwoPoint_self_nonneg
    (params : Phi4Params)
    [SchwingerLimitModel params]
    [InteractionWeightModel params]
    (f : TestFun2D) :
    0 ≤ connectedTwoPoint params f f := by
  have hlim := connectedSchwingerTwo_tendsto_infinite params f f
  have hnonneg : ∀ n : ℕ,
      0 ≤
        (if h : 0 < n then
          connectedSchwingerTwo params (exhaustingRectangles n h) f f
        else 0) := by
    intro n
    by_cases h : 0 < n
    · have hConn :=
        connectedSchwingerTwo_self_nonneg params (exhaustingRectangles n h) f
      simpa [h] using hConn
    · simp [h]
  exact ge_of_tendsto' hlim hnonneg

/-- Diagonal nonnegativity of the infinite-volume connected two-point bilinear
    form. -/
theorem connectedTwoPointBilinear_self_nonneg (params : Phi4Params)
    [SchwingerLimitModel params]
    [InteractionWeightModel params]
    (f : TestFun2D) :
    0 ≤ connectedTwoPointBilinear params f f := by
  simpa [connectedTwoPointBilinear] using
    connectedTwoPoint_self_nonneg params f

/-- Diagonal connected two-point nonnegativity in infinite volume, obtained
    directly from finite-volume FKG positivity for nonnegative test functions. -/
theorem connectedTwoPoint_self_nonneg_of_fkg
    (params : Phi4Params)
    [SchwingerLimitModel params]
    [CorrelationFKGModel params]
    (f : TestFun2D)
    (hf : ∀ x, 0 ≤ f x) :
    0 ≤ connectedTwoPoint params f f := by
  have hlim := connectedSchwingerTwo_tendsto_infinite params f f
  have hnonneg : ∀ n : ℕ,
      0 ≤
        (if h : 0 < n then
          connectedSchwingerTwo params (exhaustingRectangles n h) f f
        else 0) := by
    intro n
    by_cases h : 0 < n
    · have hConn := connectedSchwingerTwo_nonneg params (exhaustingRectangles n h) f f hf hf
      unfold connectedSchwingerTwo at hConn
      simp [h]
      linarith
    · simp [h]
  exact ge_of_tendsto' hlim hnonneg

/-- Cauchy-Schwarz inequality for the infinite-volume connected two-point function,
    transferred from finite volume via convergence along the exhausting rectangles. -/
theorem connectedTwoPoint_sq_le_mul_diag
    (params : Phi4Params)
    [SchwingerLimitModel params]
    [InteractionWeightModel params]
    (f g : TestFun2D) :
    (connectedTwoPoint params f g) ^ 2 ≤
      connectedTwoPoint params f f * connectedTwoPoint params g g := by
  let A : ℕ → ℝ := fun n =>
    if h : 0 < n then connectedSchwingerTwo params (exhaustingRectangles n h) f g else 0
  let Df : ℕ → ℝ := fun n =>
    if h : 0 < n then connectedSchwingerTwo params (exhaustingRectangles n h) f f else 0
  let Dg : ℕ → ℝ := fun n =>
    if h : 0 < n then connectedSchwingerTwo params (exhaustingRectangles n h) g g else 0
  have hA : Filter.Tendsto A Filter.atTop (nhds (connectedTwoPoint params f g)) := by
    simpa [A] using connectedSchwingerTwo_tendsto_infinite params f g
  have hDf : Filter.Tendsto Df Filter.atTop (nhds (connectedTwoPoint params f f)) := by
    simpa [Df] using connectedSchwingerTwo_tendsto_infinite params f f
  have hDg : Filter.Tendsto Dg Filter.atTop (nhds (connectedTwoPoint params g g)) := by
    simpa [Dg] using connectedSchwingerTwo_tendsto_infinite params g g
  have hA_sq : Filter.Tendsto (fun n => (A n) ^ 2) Filter.atTop
      (nhds ((connectedTwoPoint params f g) ^ 2)) :=
    hA.pow 2
  have hDiag_mul : Filter.Tendsto (fun n => Df n * Dg n) Filter.atTop
      (nhds (connectedTwoPoint params f f * connectedTwoPoint params g g)) :=
    hDf.mul hDg
  have hpointwise : ∀ n : ℕ, (A n) ^ 2 ≤ Df n * Dg n := by
    intro n
    by_cases h : 0 < n
    · simpa [A, Df, Dg, h] using
        (connectedSchwingerTwo_sq_le_mul_diag params (exhaustingRectangles n h) f g)
    · simp [A, Df, Dg, h]
  exact le_of_tendsto_of_tendsto' hA_sq hDiag_mul hpointwise

/-- Positive-semidefinite quadratic form statement for finite families in infinite
    volume: the connected two-point kernel is nonnegative on real finite linear
    combinations. -/
theorem connectedTwoPoint_quadratic_nonneg
    (params : Phi4Params)
    [SchwingerLimitModel params]
    [InteractionWeightModel params]
    {ι : Type*} (s : Finset ι)
    (f : ι → TestFun2D) (c : ι → ℝ) :
    0 ≤ Finset.sum s (fun i =>
      c i * Finset.sum s (fun j => c j * connectedTwoPoint params (f j) (f i))) := by
  let B := connectedTwoPointBilinear params
  let v : TestFun2D := Finset.sum s (fun i => c i • f i)
  have hvv :
      B v v =
        Finset.sum s (fun i => c i * Finset.sum s (fun j => c j * B (f j) (f i))) := by
    simp [B, v, Finset.sum_apply]
  have hnonneg : 0 ≤ B v v :=
    connectedTwoPointBilinear_self_nonneg params v
  rw [hvv] at hnonneg
  simpa [B] using hnonneg

/-- Standard-index-order form of `connectedTwoPoint_quadratic_nonneg`. -/
theorem connectedTwoPoint_quadratic_nonneg_standard
    (params : Phi4Params)
    [SchwingerLimitModel params]
    [InteractionWeightModel params]
    {ι : Type*} (s : Finset ι)
    (f : ι → TestFun2D) (c : ι → ℝ) :
    0 ≤ Finset.sum s (fun i => Finset.sum s (fun j =>
      c i * c j * connectedTwoPoint params (f i) (f j))) := by
  have hbase := connectedTwoPoint_quadratic_nonneg params s f c
  have hEq :
      Finset.sum s (fun i =>
        c i * Finset.sum s (fun j => c j * connectedTwoPoint params (f j) (f i)))
      =
      Finset.sum s (fun i => Finset.sum s (fun j =>
        c i * c j * connectedTwoPoint params (f i) (f j))) := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [connectedTwoPoint_symm params (f j) (f i)]
    ring
  rw [hEq] at hbase
  exact hbase

/-- Geometric-mean bound from infinite-volume connected two-point
    Cauchy-Schwarz:
    `|Cᶜ_∞(f,g)| ≤ √(Cᶜ_∞(f,f) Cᶜ_∞(g,g))`. -/
theorem connectedTwoPoint_abs_le_sqrt_diag_mul
    (params : Phi4Params)
    [SchwingerLimitModel params]
    [InteractionWeightModel params]
    (f g : TestFun2D) :
    |connectedTwoPoint params f g| ≤
      Real.sqrt (connectedTwoPoint params f f * connectedTwoPoint params g g) := by
  let x : ℝ := connectedTwoPoint params f g
  let y : ℝ := connectedTwoPoint params f f * connectedTwoPoint params g g
  have hx2 : x ^ 2 ≤ y := by
    simpa [x, y] using connectedTwoPoint_sq_le_mul_diag params f g
  have hy_nonneg : 0 ≤ y := by
    have hff : 0 ≤ connectedTwoPoint params f f := connectedTwoPoint_self_nonneg params f
    have hgg : 0 ≤ connectedTwoPoint params g g := connectedTwoPoint_self_nonneg params g
    exact mul_nonneg hff hgg
  have hxy_sq : (|x|) ^ 2 ≤ (Real.sqrt y) ^ 2 := by
    have h1 : |x| ^ 2 ≤ y := by
      simpa [sq_abs] using hx2
    have h2 : y = (Real.sqrt y) ^ 2 := by
      symm
      exact Real.sq_sqrt hy_nonneg
    linarith
  have hxy_abs : |(|x|)| ≤ |Real.sqrt y| := (sq_le_sq).1 hxy_sq
  have hxy : |x| ≤ Real.sqrt y := by
    simpa [abs_abs, abs_of_nonneg (Real.sqrt_nonneg y)] using hxy_abs
  simpa [x, y] using hxy

/-- Infinite-volume half-diagonal bound:
    `|Cᶜ_∞(f,g)| ≤ (Cᶜ_∞(f,f) + Cᶜ_∞(g,g))/2`. -/
theorem connectedTwoPoint_abs_le_half_diag_sum
    (params : Phi4Params)
    [SchwingerLimitModel params]
    [InteractionWeightModel params]
    (f g : TestFun2D) :
    |connectedTwoPoint params f g| ≤
      (connectedTwoPoint params f f + connectedTwoPoint params g g) / 2 := by
  let x : ℝ := connectedTwoPoint params f g
  let a : ℝ := connectedTwoPoint params f f
  let b : ℝ := connectedTwoPoint params g g
  have hx2 : x ^ 2 ≤ a * b := by
    simpa [x, a, b] using connectedTwoPoint_sq_le_mul_diag params f g
  have ha : 0 ≤ a := by
    simpa [a] using connectedTwoPoint_self_nonneg params f
  have hb : 0 ≤ b := by
    simpa [b] using connectedTwoPoint_self_nonneg params g
  have hsq : (2 * |x|) ^ 2 ≤ (a + b) ^ 2 := by
    have hsq_nonneg : 0 ≤ (a - b) ^ 2 := sq_nonneg (a - b)
    nlinarith [hx2, hsq_nonneg, sq_abs x]
  have h2le : 2 * |x| ≤ a + b := by
    have hAbs : abs (2 * |x|) ≤ abs (a + b) := (sq_le_sq).1 hsq
    have hleft : 0 ≤ 2 * |x| := by positivity
    have hright : 0 ≤ a + b := add_nonneg ha hb
    simpa [abs_of_nonneg hleft, abs_of_nonneg hright] using hAbs
  have hxbound : |x| ≤ (a + b) / 2 := by
    nlinarith [h2le]
  simpa [x, a, b] using hxbound

/-- If finite-volume FKG inequalities are available, the infinite-volume connected
    two-point function is nonnegative for nonnegative test functions. -/
theorem connectedTwoPoint_nonneg
    (params : Phi4Params)
    [SchwingerLimitModel params]
    [CorrelationFKGModel params]
    (f g : TestFun2D)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) :
    0 ≤ connectedTwoPoint params f g := by
  have hlim := connectedSchwingerTwo_tendsto_infinite params f g
  have hnonneg : ∀ n : ℕ,
      0 ≤
        (if h : 0 < n then
          connectedSchwingerTwo params (exhaustingRectangles n h) f g
        else 0) := by
    intro n
    by_cases h : 0 < n
    · have hConn := connectedSchwingerTwo_nonneg params (exhaustingRectangles n h) f g hf hg
      unfold connectedSchwingerTwo at hConn
      simp [h]
      linarith
    · simp [h]
  exact ge_of_tendsto' hlim hnonneg

/-- The infinite volume φ⁴₂ probability measure on S'(ℝ²).
    This is the weak limit of dμ_{Λₙ} as Λₙ ↗ ℝ². -/
def infiniteVolumeMeasure (params : Phi4Params)
    [InfiniteVolumeMeasureModel params] :
    @Measure FieldConfig2D GaussianField.instMeasurableSpaceConfiguration :=
  InfiniteVolumeMeasureModel.infiniteVolumeMeasure (params := params)

/-- The infinite volume measure is a probability measure. -/
theorem infiniteVolumeMeasure_isProbability (params : Phi4Params)
    [InfiniteVolumeMeasureModel params] :
    IsProbabilityMeasure (infiniteVolumeMeasure params) := by
  simpa [infiniteVolumeMeasure] using
    (InfiniteVolumeMeasureModel.infiniteVolumeMeasure_isProbability
      (params := params))

/-- The infinite volume Schwinger functions are the moments of the
    infinite volume measure. -/
theorem infiniteVolumeSchwinger_is_moment (params : Phi4Params)
    [InfiniteVolumeSchwingerModel params]
    [InfiniteVolumeMeasureModel params]
    [InfiniteVolumeMomentModel params]
    (k : ℕ) (f : Fin k → TestFun2D) :
    infiniteVolumeSchwinger params k f =
      ∫ ω, (∏ i, ω (f i)) ∂(infiniteVolumeMeasure params) := by
  simpa [infiniteVolumeSchwinger, infiniteVolumeMeasure] using
    (InfiniteVolumeMomentModel.infiniteVolumeSchwinger_is_moment
      (params := params) k f)

/-- Zeroth infinite-volume Schwinger function normalization:
    `S_0 = 1` for any choice of the unique `Fin 0 → TestFun2D`. -/
theorem infiniteVolumeSchwinger_zero (params : Phi4Params)
    [SchwingerLimitModel params]
    [InteractionWeightModel params]
    (f : Fin 0 → TestFun2D) :
    infiniteVolumeSchwinger params 0 f = 1 := by
  have hlim :=
    SchwingerLimitModel.infiniteVolumeSchwinger_tendsto
      (params := params) 0 f
  have hlim' :
      Filter.Tendsto
        (fun n : ℕ =>
          if h : 0 < n then schwingerN params (exhaustingRectangles n h) 0 f else 0)
        Filter.atTop
        (nhds (infiniteVolumeSchwinger params 0 f)) := by
    simpa [infiniteVolumeSchwinger] using hlim
  have hconst :
      Filter.Tendsto
        (fun n : ℕ =>
          if h : 0 < n then schwingerN params (exhaustingRectangles n h) 0 f else 0)
        Filter.atTop (nhds (1 : ℝ)) := by
    refine (tendsto_const_nhds :
      Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds (1 : ℝ))).congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
    have hn' : 0 < n := hn
    simp [hn', schwingerN_zero params (exhaustingRectangles n hn') f]
  exact tendsto_nhds_unique hlim' hconst

/-- Measure-representation proof of zeroth infinite-volume Schwinger
    normalization (`S_0 = 1`). -/
theorem infiniteVolumeSchwinger_zero_of_moment (params : Phi4Params)
    [InfiniteVolumeSchwingerModel params]
    [InfiniteVolumeMeasureModel params]
    [InfiniteVolumeMomentModel params]
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

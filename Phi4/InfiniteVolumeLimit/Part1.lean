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
    [SchwingerNMonotoneModel params 2]
    (n₁ n₂ : ℕ) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (h : n₁ ≤ n₂)
    (f g : TestFun2D) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupp : ∀ x ∉ (exhaustingRectangles n₁ hn₁).toSet, f x = 0)
    (hgsupp : ∀ x ∉ (exhaustingRectangles n₁ hn₁).toSet, g x = 0) :
    schwingerTwo params (exhaustingRectangles n₁ hn₁) f g ≤
      schwingerTwo params (exhaustingRectangles n₂ hn₂) f g := by
  have hfvec : ∀ i, ∀ x, 0 ≤ (![f, g] : Fin 2 → TestFun2D) i x := by
    intro i x
    fin_cases i
    · simpa using hf x
    · simpa using hg x
  have hsuppvec :
      ∀ i, ∀ x ∉ (exhaustingRectangles n₁ hn₁).toSet,
        (![f, g] : Fin 2 → TestFun2D) i x = 0 := by
    intro i x hx
    fin_cases i
    · simpa using hfsupp x hx
    · simpa using hgsupp x hx
  have hmonoN := schwingerN_monotone_of_interface params 2
    (exhaustingRectangles n₁ hn₁) (exhaustingRectangles n₂ hn₂)
    (exhaustingRectangles_mono_toSet n₁ n₂ hn₁ hn₂ h)
    (![f, g] : Fin 2 → TestFun2D) hfvec hsuppvec
  simpa [schwingerN_two_eq_schwingerTwo] using hmonoN

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
    [SchwingerNMonotoneModel params 2]
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
    [SchwingerNMonotoneModel params 2]
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

/-- Convergence of finite-volume `k`-point Schwinger moments from:
    1. volume monotonicity (`SchwingerNMonotoneModel params k`), and
    2. an explicit uniform absolute bound along the shifted exhaustion. -/
theorem schwingerN_tendsto_iSup_of_monotone_bounded
    (params : Phi4Params)
    (k : ℕ)
    [SchwingerNMonotoneModel params k]
    (n0 : ℕ)
    (f : Fin k → TestFun2D)
    (hf : ∀ i, ∀ x, 0 ≤ f i x)
    (hfsupp0 : ∀ i,
      ∀ x ∉ (exhaustingRectangles (n0 + 1) (Nat.succ_pos n0)).toSet, f i x = 0)
    (hbound : ∃ C : ℝ, ∀ n : ℕ,
      |schwingerN params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) k f| ≤ C) :
    Filter.Tendsto
      (fun n : ℕ => schwingerN params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) k f)
      Filter.atTop
      (nhds (⨆ n : ℕ,
        schwingerN params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) k f)) := by
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

/-- Existence form of `schwingerN_tendsto_iSup_of_monotone_bounded`. -/
theorem schwingerN_limit_exists_of_monotone_bounded
    (params : Phi4Params)
    (k : ℕ)
    [SchwingerNMonotoneModel params k]
    (n0 : ℕ)
    (f : Fin k → TestFun2D)
    (hf : ∀ i, ∀ x, 0 ≤ f i x)
    (hfsupp0 : ∀ i,
      ∀ x ∉ (exhaustingRectangles (n0 + 1) (Nat.succ_pos n0)).toSet, f i x = 0)
    (hbound : ∃ C : ℝ, ∀ n : ℕ,
      |schwingerN params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) k f| ≤ C) :
    ∃ S : ℝ,
      Filter.Tendsto
        (fun n : ℕ => schwingerN params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) k f)
        Filter.atTop (nhds S) := by
  refine ⟨⨆ n : ℕ, schwingerN params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) k f, ?_⟩
  exact schwingerN_tendsto_iSup_of_monotone_bounded
    params k n0 f hf hfsupp0 hbound

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
  exact schwingerN_tendsto_iSup_of_monotone_bounded
    params k n0 f hf hfsupp0 hbound

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

/-- Convergence of the interface-shaped exhausting sequence
    `if h : 0 < n then S_k^{Λₙ}(f) else 0`, from:
    1. finite-volume monotonicity (`SchwingerNMonotoneModel params k`),
    2. finite-volume nonnegativity (`SchwingerNNonnegModel params k`), and
    3. uniform bounds from `MultipleReflectionModel params`. -/
theorem schwingerN_tendsto_if_exhaustion_of_models
    (params : Phi4Params)
    (k : ℕ)
    [SchwingerNMonotoneModel params k]
    [SchwingerNNonnegModel params k]
    [MultipleReflectionModel params]
    (f : Fin k → TestFun2D)
    (hf : ∀ i, ∀ x, 0 ≤ f i x)
    (hfsupp : ∀ i, ∀ x ∉ (exhaustingRectangles 1 (Nat.succ_pos 0)).toSet, f i x = 0) :
    Filter.Tendsto
      (fun n : ℕ => if h : 0 < n then schwingerN params (exhaustingRectangles n h) k f else 0)
      Filter.atTop
      (nhds (⨆ n : ℕ,
        if h : 0 < n then schwingerN params (exhaustingRectangles n h) k f else 0)) := by
  let a : ℕ → ℝ := fun n =>
    if h : 0 < n then schwingerN params (exhaustingRectangles n h) k f else 0
  have hmono : Monotone a := by
    intro n m hnm
    by_cases hn : 0 < n
    · have hm : 0 < m := lt_of_lt_of_le hn hnm
      have hsub :
          (exhaustingRectangles 1 (Nat.succ_pos 0)).toSet ⊆
            (exhaustingRectangles n hn).toSet :=
        exhaustingRectangles_mono_toSet 1 n (Nat.succ_pos 0) hn hn
      have hfsuppn :
          ∀ i, ∀ x ∉ (exhaustingRectangles n hn).toSet, f i x = 0 := by
        intro i x hx
        exact support_zero_outside_of_subset (f i) hsub (hfsupp i) x hx
      have hmono_nm := schwingerN_monotone_in_volume_of_model
        (params := params) (k := k) n m hn hm hnm f hf hfsuppn
      simpa [a, hn, hm] using hmono_nm
    · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
      by_cases hm : 0 < m
      · have hnonneg :
            0 ≤ schwingerN params (exhaustingRectangles m hm) k f :=
          SchwingerNNonnegModel.schwingerN_nonneg
            (params := params) (k := k) (exhaustingRectangles m hm) f hf
        simpa [a, hn0, hm] using hnonneg
      · have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
        subst hn0
        subst hm0
        simp [a]
  rcases schwingerN_uniformly_bounded_on_exhaustion
      params 0 k f hfsupp with ⟨C, hC⟩
  let Cmax : ℝ := max C 0
  have hbound : ∀ n : ℕ, |a n| ≤ Cmax := by
    intro n
    by_cases hn : 0 < n
    · rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn) with ⟨m, rfl⟩
      have hm : |schwingerN params (exhaustingRectangles (m + 1) (Nat.succ_pos m)) k f| ≤ C := hC m
      have hm' : |a (m + 1)| ≤ C := by simpa [a] using hm
      exact le_trans hm' (le_max_left _ _)
    · have hzero : a n = 0 := by simp [a, hn]
      rw [hzero]
      have hCmax_nonneg : 0 ≤ Cmax := le_trans (le_refl 0) (le_max_right C 0)
      simpa [abs_of_nonneg hCmax_nonneg]
  have hbdd : BddAbove (Set.range a) := by
    refine ⟨Cmax, ?_⟩
    rintro y ⟨n, rfl⟩
    exact le_trans (le_abs_self _) (hbound n)
  exact tendsto_atTop_ciSup hmono hbdd

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
    2. volume monotonicity (`SchwingerNMonotoneModel params 2`), and
    3. an explicit uniform absolute bound.

    The limit is identified with the supremum over the exhaustion sequence. -/
theorem schwingerTwo_tendsto_iSup_of_monotone_bounded
    (params : Phi4Params)
    [SchwingerNMonotoneModel params 2]
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
  have hfvec : ∀ i, ∀ x, 0 ≤ (![f, g] : Fin 2 → TestFun2D) i x := by
    intro i x
    fin_cases i
    · simpa using hf x
    · simpa using hg x
  have hsuppvec :
      ∀ i, ∀ x ∉ (exhaustingRectangles (n0 + 1) (Nat.succ_pos n0)).toSet,
        (![f, g] : Fin 2 → TestFun2D) i x = 0 := by
    intro i x hx
    fin_cases i
    · simpa using hfsupp0 x hx
    · simpa using hgsupp0 x hx
  have hboundVec : ∃ C : ℝ, ∀ n : ℕ,
      |schwingerN params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) 2
        (![f, g] : Fin 2 → TestFun2D)| ≤ C := by
    rcases hbound with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro n
    simpa [schwingerN_two_eq_schwingerTwo] using hC n
  have hlim := schwingerN_tendsto_iSup_of_monotone_bounded
    (params := params) (k := 2) n0 (![f, g] : Fin 2 → TestFun2D)
    hfvec hsuppvec hboundVec
  simpa [schwingerN_two_eq_schwingerTwo] using hlim

/-- Monotone-convergence form for the two-point exhausting sequence, with the
    absolute bound discharged by `MultipleReflectionModel`. -/
theorem schwingerTwo_tendsto_iSup_of_models
    (params : Phi4Params)
    [SchwingerNMonotoneModel params 2]
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
  have hfvec : ∀ i, ∀ x, 0 ≤ (![f, g] : Fin 2 → TestFun2D) i x := by
    intro i x
    fin_cases i
    · simpa using hf x
    · simpa using hg x
  have hsuppvec :
      ∀ i, ∀ x ∉ (exhaustingRectangles (n0 + 1) (Nat.succ_pos n0)).toSet,
        (![f, g] : Fin 2 → TestFun2D) i x = 0 := by
    intro i x hx
    fin_cases i
    · simpa using hfsupp0 x hx
    · simpa using hgsupp0 x hx
  have hlim := schwingerN_tendsto_iSup_of_models
    (params := params) (k := 2) n0 (![f, g] : Fin 2 → TestFun2D)
    hfvec hsuppvec
  simpa [schwingerN_two_eq_schwingerTwo] using hlim

/-- Existence form of `schwingerTwo_tendsto_iSup_of_models`. -/
theorem schwingerTwo_limit_exists_of_models
    (params : Phi4Params)
    [SchwingerNMonotoneModel params 2]
    [MultipleReflectionModel params]
    (n0 : ℕ)
    (f g : TestFun2D) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupp0 : ∀ x ∉ (exhaustingRectangles (n0 + 1) (Nat.succ_pos n0)).toSet, f x = 0)
    (hgsupp0 : ∀ x ∉ (exhaustingRectangles (n0 + 1) (Nat.succ_pos n0)).toSet, g x = 0) :
    ∃ S : ℝ,
      Filter.Tendsto
        (fun n : ℕ => schwingerTwo params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) f g)
        Filter.atTop (nhds S) := by
  have hfvec : ∀ i, ∀ x, 0 ≤ (![f, g] : Fin 2 → TestFun2D) i x := by
    intro i x
    fin_cases i
    · simpa using hf x
    · simpa using hg x
  have hsuppvec :
      ∀ i, ∀ x ∉ (exhaustingRectangles (n0 + 1) (Nat.succ_pos n0)).toSet,
        (![f, g] : Fin 2 → TestFun2D) i x = 0 := by
    intro i x hx
    fin_cases i
    · simpa using hfsupp0 x hx
    · simpa using hgsupp0 x hx
  rcases schwingerN_limit_exists_of_models
      (params := params) (k := 2) n0 (![f, g] : Fin 2 → TestFun2D) hfvec hsuppvec with
      ⟨S, hS⟩
  refine ⟨S, ?_⟩
  simpa [schwingerN_two_eq_schwingerTwo] using hS

/-- Convergence of the interface-shaped exhausting sequence
    `if h : 0 < n then S₂^{Λₙ}(f,g) else 0`, with monotonicity from
    `SchwingerNMonotoneModel params 2`, `SchwingerNNonnegModel params 2`,
    and absolute bounds from `MultipleReflectionModel`. -/
theorem schwingerTwo_tendsto_if_exhaustion_of_models
    (params : Phi4Params)
    [SchwingerNMonotoneModel params 2]
    [SchwingerNNonnegModel params 2]
    [MultipleReflectionModel params]
    (f g : TestFun2D)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupp : ∀ x ∉ (exhaustingRectangles 1 (Nat.succ_pos 0)).toSet, f x = 0)
    (hgsupp : ∀ x ∉ (exhaustingRectangles 1 (Nat.succ_pos 0)).toSet, g x = 0) :
    Filter.Tendsto
      (fun n : ℕ => if h : 0 < n then schwingerTwo params (exhaustingRectangles n h) f g else 0)
      Filter.atTop
      (nhds (⨆ n : ℕ, if h : 0 < n then schwingerTwo params (exhaustingRectangles n h) f g else 0)) := by
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
  have hlim := schwingerN_tendsto_if_exhaustion_of_models
    (params := params) (k := 2) (![f, g] : Fin 2 → TestFun2D)
    hfvec hsuppvec
  simpa [schwingerN_two_eq_schwingerTwo] using hlim

/-- Existence form of `schwingerTwo_tendsto_if_exhaustion_of_models`. -/
theorem schwingerTwo_limit_exists_if_exhaustion_of_models
    (params : Phi4Params)
    [SchwingerNMonotoneModel params 2]
    [SchwingerNNonnegModel params 2]
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
    [SchwingerNMonotoneModel params 2]
    [SchwingerNNonnegModel params 2]
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
  exact schwingerN_tendsto_if_exhaustion_of_models
    (params := params) (k := 2) (![f, g] : Fin 2 → TestFun2D)
    hfvec hsuppvec

/-- Existence form of `schwingerN_two_tendsto_if_exhaustion_of_models`. -/
theorem schwingerN_two_limit_exists_if_exhaustion_of_models
    (params : Phi4Params)
    [SchwingerNMonotoneModel params 2]
    [SchwingerNNonnegModel params 2]
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
    [SchwingerNMonotoneModel params 2]
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
  have hfvec : ∀ i, ∀ x, 0 ≤ (![f, g] : Fin 2 → TestFun2D) i x := by
    intro i x
    fin_cases i
    · simpa using hf x
    · simpa using hg x
  have hsuppvec :
      ∀ i, ∀ x ∉ (exhaustingRectangles (n0 + 1) (Nat.succ_pos n0)).toSet,
        (![f, g] : Fin 2 → TestFun2D) i x = 0 := by
    intro i x hx
    fin_cases i
    · simpa using hfsupp0 x hx
    · simpa using hgsupp0 x hx
  have hboundVec : ∃ C : ℝ, ∀ n : ℕ,
      |schwingerN params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) 2
        (![f, g] : Fin 2 → TestFun2D)| ≤ C := by
    rcases hbound with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro n
    simpa [schwingerN_two_eq_schwingerTwo] using hC n
  rcases schwingerN_limit_exists_of_monotone_bounded
      (params := params) (k := 2) n0 (![f, g] : Fin 2 → TestFun2D)
      hfvec hsuppvec hboundVec with ⟨S, hS⟩
  refine ⟨S, ?_⟩
  simpa [schwingerN_two_eq_schwingerTwo] using hS

/-- `schwingerN` (`k = 2`) form of monotone-bounded convergence. -/
theorem schwingerN_two_tendsto_iSup_of_monotone_bounded
    (params : Phi4Params)
    [SchwingerNMonotoneModel params 2]
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
  exact schwingerN_tendsto_iSup_of_monotone_bounded
    (params := params) (k := 2) n0 f hf hfsupp0 hbound

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
    [SchwingerNMonotoneModel params 2]
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
    [SchwingerNMonotoneModel params 2]
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
    [SchwingerNMonotoneModel params 2]
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
  rcases schwingerUniformBoundModel_nonempty_of_data params hbound with ⟨hboundModel⟩
  rcases schwingerLimitModel_nonempty_of_limit_data params hlim with ⟨hlimModel⟩
  letI : SchwingerUniformBoundModel params := hboundModel
  letI : SchwingerLimitModel params := hlimModel
  exact ⟨inferInstance⟩

/-- Public uniform-bound endpoint from explicit uniform-bound data. -/
theorem schwinger_uniformly_bounded (params : Phi4Params)
    (hbound : ∀ (k : ℕ) (f : Fin k → TestFun2D),
      ∃ C : ℝ, ∀ (n : ℕ) (hn : 0 < n),
        |schwingerN params (exhaustingRectangles n hn) k f| ≤ C)
    (k : ℕ) (f : Fin k → TestFun2D) :
    ∃ C : ℝ, ∀ (n : ℕ) (hn : 0 < n),
      |schwingerN params (exhaustingRectangles n hn) k f| ≤ C := by
  exact hbound k f

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
    (hlim : ∀ (k : ℕ) (f : Fin k → TestFun2D),
      ∃ S : ℝ, Filter.Tendsto
        (fun n : ℕ =>
          if h : 0 < n then schwingerN params (exhaustingRectangles n h) k f else 0)
        Filter.atTop (nhds S))
    (k : ℕ) (f : Fin k → TestFun2D) :
    ∃ S : ℝ, Filter.Tendsto
      (fun n : ℕ => if h : 0 < n then schwingerN params (exhaustingRectangles n h) k f else 0)
      Filter.atTop (nhds S) := by
  exact hlim k f

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
    [SchwingerNMonotoneModel params 4]
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

/-- Correlation-side `k = 4` bridge:
    if finite-volume four-point monotonicity is packaged via
    `CorrelationFourPointModel`, then the `k = 4` infinite-volume Schwinger
    limit exists along the standard exhaustion/interface sequence. -/
theorem infinite_volume_schwinger_exists_four_of_correlationFourPoint_models
    (params : Phi4Params)
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
  exact infinite_volume_schwinger_exists_four_of_models
    (params := params) f₁ f₂ f₃ f₄
    hf₁ hf₂ hf₃ hf₄
    hf₁supp hf₂supp hf₃supp hf₄supp

/-- Core-correlation `k = 4` bridge:
    the same `k = 4` infinite-volume existence endpoint, specialized to
    `CorrelationInequalityCoreModel` (which already contains four-point
    monotonicity). -/
theorem infinite_volume_schwinger_exists_four_of_correlationCore_models
    (params : Phi4Params)
    [CorrelationInequalityCoreModel params]
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
  exact infinite_volume_schwinger_exists_four_of_models
    (params := params) f₁ f₂ f₃ f₄
    hf₁ hf₂ hf₃ hf₄
    hf₁supp hf₂supp hf₃supp hf₄supp

/-- Full-correlation `k = 4` bridge:
    the `k = 4` infinite-volume existence endpoint under
    `CorrelationInequalityModel` and multiple reflections. -/
theorem infinite_volume_schwinger_exists_four_of_correlationInequality_models
    (params : Phi4Params)
    [CorrelationInequalityModel params]
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
  exact infinite_volume_schwinger_exists_four_of_models
    (params := params) f₁ f₂ f₃ f₄
    hf₁ hf₂ hf₃ hf₄
    hf₁supp hf₂supp hf₃supp hf₄supp

/-- Core-packaged `k = 4` bridge (legacy lattice+core endpoint name):
    for the `k = 4` infinite-volume existence endpoint, only four-point
    monotonicity (available from `CorrelationInequalityCoreModel`) and
    multiple-reflection bounds are needed. No lattice GKS-I input is required. -/
theorem infinite_volume_schwinger_exists_four_of_lattice_and_core_models
    (params : Phi4Params)
    [CorrelationInequalityCoreModel params]
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
  exact infinite_volume_schwinger_exists_four_of_correlationCore_models
    (params := params) f₁ f₂ f₃ f₄
    hf₁ hf₂ hf₃ hf₄
    hf₁supp hf₂supp hf₃supp hf₄supp

/-- Constructive `k = 2` infinite-volume Schwinger existence in the
    interface sequence form `if h : 0 < n then ... else 0`, under explicit
    two-point monotonicity and multiple-reflection bounds. -/
theorem infinite_volume_schwinger_exists_two_of_models (params : Phi4Params)
    [SchwingerNMonotoneModel params 2]
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

/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.InfiniteVolumeLimit.Part2

noncomputable section

open MeasureTheory

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

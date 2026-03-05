/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.InfiniteVolumeLimit.Part1

noncomputable section

open MeasureTheory

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
    [CorrelationGKSSecondModel params]
    [CorrelationLebowitzModel params]
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
    [CorrelationGKSSecondModel params]
    [CorrelationLebowitzModel params]
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
    [CorrelationGKSSecondModel params]
    [CorrelationLebowitzModel params]
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

/-- Infinite-volume analog of the finite-volume all-channel 4-point bounds:
    each GKS-II channel gives a lower bound and Lebowitz gives the upper bound. -/
theorem infiniteSchwinger_four_bounds_all_channels
    (params : Phi4Params)
    [SchwingerLimitModel params]
    [CorrelationGKSSecondModel params]
    [CorrelationLebowitzModel params]
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

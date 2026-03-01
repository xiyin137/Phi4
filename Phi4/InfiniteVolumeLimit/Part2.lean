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

/-- Alternative absolute-value bound on the infinite-volume cumulant using the
    `(13)(24)` lower channel. -/
theorem infiniteCumulantFourPoint_abs_bound_alt13
    (params : Phi4Params)
    [SchwingerLimitModel params]
    [CorrelationGKSSecondModel params]
    [CorrelationLebowitzModel params]
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
    [CorrelationGKSSecondModel params]
    [CorrelationLebowitzModel params]
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
    [CorrelationGKSSecondModel params]
    [CorrelationLebowitzModel params]
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
    [CorrelationGKSSecondModel params]
    [CorrelationLebowitzModel params]
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
    [CorrelationGKSSecondModel params]
    [CorrelationLebowitzModel params]
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
    [CorrelationGKSSecondModel params]
    [CorrelationLebowitzModel params]
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
    [CorrelationGKSSecondModel params]
    [CorrelationLebowitzModel params]
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
    [CorrelationGKSSecondModel params]
    [CorrelationLebowitzModel params]
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
    [CorrelationGKSSecondModel params]
    [CorrelationLebowitzModel params]
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
    [CorrelationGKSSecondModel params]
    [CorrelationLebowitzModel params]
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
    [CorrelationGKSSecondModel params]
    [CorrelationLebowitzModel params]
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
    [CorrelationGKSSecondModel params]
    [CorrelationLebowitzModel params]
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
    [CorrelationGKSSecondModel params]
    [CorrelationLebowitzModel params]
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
    [CorrelationGKSSecondModel params]
    [CorrelationLebowitzModel params]
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
    [CorrelationGKSSecondModel params]
    [CorrelationLebowitzModel params]
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


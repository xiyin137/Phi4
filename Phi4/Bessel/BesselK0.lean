/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.Bessel.BesselK1

/-!
# Modified Bessel Function K₀

The modified Bessel function K₀(z) is defined via the integral representation
  K₀(z) = ∫₀^∞ exp(-z cosh(t)) dt

This is the Green's function kernel for the 2D massive scalar field:
  C(x,y) = (2π)⁻¹ K₀(m|x-y|)

## Main definitions

* `besselK0` - K₀(z) = ∫₀^∞ exp(-z cosh(t)) dt

## Main results

* `besselK0_pos` - K₀(z) > 0 for z > 0
* `besselK0_integrand_integrableOn` - integrability of the K₀ integrand
* `schwingerIntegral2D_eq_besselK0` - ∫₀^∞ (1/t) exp(-m²t - r²/(4t)) dt = 2K₀(mr)

## References

* Abramowitz-Stegun, Chapter 9
* [Glimm-Jaffe] Section 7.1 (the free covariance in d=2)
-/

open MeasureTheory Set Filter Real

noncomputable section

/-- The modified Bessel function K₀(z) via cosh integral representation.
    K₀(z) = ∫₀^∞ exp(-z cosh(t)) dt
    This is well-defined and positive for z > 0. -/
def besselK0 (z : ℝ) : ℝ :=
  ∫ t : ℝ in Ici 0, exp (-z * cosh t)

/-- The integrand for K₀ is integrable on [0,∞) for z > 0.
    Proof: For t ≥ 0, cosh(t) ≥ 1 + t²/2, so exp(-z cosh t) ≤ exp(-z) exp(-zt²/2).
    The Gaussian exp(-zt²/2) is integrable on [0,∞). -/
lemma besselK0_integrand_integrableOn (z : ℝ) (hz : 0 < z) :
    IntegrableOn (fun t => exp (-z * cosh t)) (Ici 0) volume := by
  sorry

/-- K₀(z) is positive for z > 0.
    The integrand exp(-z cosh t) is strictly positive and integrable, so the integral is positive. -/
lemma besselK0_pos (z : ℝ) (hz : 0 < z) : 0 < besselK0 z := by
  sorry

/-- K₀ is bounded by K₁: K₀(z) ≤ K₁(z) for z > 0.
    Proof: exp(-z cosh t) ≤ exp(-z cosh t) * cosh t since cosh t ≥ 1. -/
lemma besselK0_le_besselK1 (z : ℝ) (hz : 0 < z) : besselK0 z ≤ besselK1 z := by
  unfold besselK0 besselK1
  exact setIntegral_mono
    (hf := besselK0_integrand_integrableOn z hz)
    (hg := by sorry)  -- K₁ integrand integrability
    (fun t => le_mul_of_one_le_right (exp_nonneg _) (one_le_cosh t))

/-- The 2D Schwinger integral identity:
    ∫₀^∞ (1/t) exp(-m²t - r²/(4t)) dt = 2K₀(mr)

    This connects the heat kernel representation of the 2D Green's function
    to the Bessel function K₀. The proof uses the substitution t = (r/(2m)) exp(u).

    Combined with the definition of freeCovKernel, this gives:
    C(x,y) = (4π)⁻¹ · 2K₀(m|x-y|) = (2π)⁻¹ K₀(m|x-y|). -/
lemma schwingerIntegral2D_eq_besselK0 (m r : ℝ) (hm : 0 < m) (hr : 0 < r) :
    ∫ t in Ioi 0, (1 / t) * exp (-m^2 * t - r^2 / (4 * t)) =
    2 * besselK0 (m * r) := by
  sorry

/-- K₀ is continuous on (0, ∞). -/
lemma besselK0_continuousOn : ContinuousOn besselK0 (Ioi 0) := by
  sorry

/-- K₀ is monotone decreasing for z > 0. -/
lemma besselK0_antitone : AntitoneOn besselK0 (Ioi 0) := by
  sorry

end

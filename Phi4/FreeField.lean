/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.Defs

/-!
# Free Euclidean Field in 2D

The free Euclidean field is the centered Gaussian measure on S'(ℝ²) with covariance
C = (-Δ + m²)⁻¹. This is the starting point for the φ⁴₂ construction.

The Gaussian measure is constructed using the `GaussianField.measure` from the
gaussian-field library, which works for any nuclear Fréchet space E and any
continuous linear map T : E →L[ℝ] H to a Hilbert space H. The covariance is
then C(f,g) = ⟨T(f), T(g)⟩_H.

## Main definitions

* `freeEigenvalue` — Eigenvalues λₘ of (-Δ + m²) in the Hermite basis
* `freeSingularValue` — Singular values σₘ = λₘ⁻¹/² of the covariance
* `freeCovarianceCLM` — The CLM T : S(ℝ²) →L[ℝ] ℓ² encoding the free covariance
* `freeFieldMeasure` — The Gaussian probability measure dφ_C on S'(ℝ²)

## References

* [Glimm-Jaffe] Sections 6.2, 7.1-7.2
* gaussian-field library: `GaussianField.measure`, `GaussianField.Properties`
-/

noncomputable section

open MeasureTheory GaussianField
open scoped NNReal

/-! ## Eigenvalue spectrum of (-Δ + x² + m²) on ℝ²

The Hermite functions provide an eigenbasis for the harmonic oscillator H = -Δ + x²
on ℝ. The operator H + m² has discrete spectrum and compact resolvent.
For ℝ², in the tensor Hermite basis ψ_{n₁} ⊗ ψ_{n₂}, the eigenvalues of
(H₁ + H₂ + m²) = (-∂₁² + x₁² - ∂₂² + x₂² + m²) are
(2n₁ + 1) + (2n₂ + 1) + m².

Note: These are eigenvalues of the harmonic oscillator (-Δ + x² + m²), NOT of
the flat-space operator (-Δ + m²). The latter has continuous spectrum [m², ∞).
We use the harmonic oscillator basis because it gives a nuclear embedding
S(ℝ²) ↪ L²(ℝ²) via the Dynin-Mityagin theorem, which is required for the
Gaussian measure construction. The covariance C = (-Δ + m²)⁻¹ is then
represented in this basis with matrix elements ⟨ψₘ, (-Δ+m²)⁻¹ ψₙ⟩. -/

/-- Eigenvalue of the harmonic oscillator (-Δ + x² + m²) for the m-th
    Hermite basis function (Cantor-paired index).
    λₘ = (2n₁ + 1) + (2n₂ + 1) + mass², where (n₁, n₂) = unpair(m).

    These are NOT eigenvalues of (-Δ + m²); they index the Hermite eigenbasis
    used for the nuclear embedding S(ℝ²) ↪ L²(ℝ²). -/
def freeEigenvalue (mass : ℝ) (m : ℕ) : ℝ :=
  let nk := m.unpair
  (2 * nk.1 + 1 : ℝ) + (2 * nk.2 + 1 : ℝ) + mass ^ 2

/-- The eigenvalues are positive for positive mass. -/
theorem freeEigenvalue_pos (mass : ℝ) (hmass : 0 < mass) (m : ℕ) :
    0 < freeEigenvalue mass m := by
  unfold freeEigenvalue
  positivity

/-- Singular value σₘ = λₘ⁻¹/² of the free covariance.
    These are the diagonal entries of T in the adapted basis. -/
def freeSingularValue (mass : ℝ) (m : ℕ) : ℝ :=
  (freeEigenvalue mass m)⁻¹ ^ (1/2 : ℝ)

/-- The singular values are summable (nuclear trace class condition).
    This is the key d=2 fact: Σₘ σₘ < ∞ because eigenvalues grow linearly in m. -/
theorem free_singular_values_summable (mass : ℝ) (hmass : 0 < mass) :
    Summable (fun m => freeSingularValue mass m) := by
  sorry

/-- The singular values are bounded (needed for spectralCLM). -/
theorem free_singular_values_bounded (mass : ℝ) (hmass : 0 < mass) :
    ∃ C : ℝ, ∀ m : ℕ, |freeSingularValue mass m| ≤ C := by
  sorry

/-! ## Free covariance CLM and Gaussian measure -/

/-- The covariance CLM T : S(ℝ²) →L[ℝ] ℓ² for the free field.
    This maps test functions to sequences via the Hermite expansion,
    weighted by the singular values σₘ. -/
def freeCovarianceCLM (mass : ℝ) (hmass : 0 < mass) :
    TestFun2D →L[ℝ] GaussianField.ell2' := by
  sorry -- spectralCLM applied to freeSingularValue

/-- The free Gaussian field measure dφ_C on S'(ℝ²).
    This is the centered Gaussian probability measure with covariance
    C(f,g) = ⟨T(f), T(g)⟩_{ℓ²} = Σₘ σₘ² ĉₘ(f) ĉₘ(g)
    where ĉₘ are the Hermite coefficients. -/
def freeFieldMeasure (mass : ℝ) (hmass : 0 < mass) :
    @Measure FieldConfig2D GaussianField.instMeasurableSpaceConfiguration :=
  GaussianField.measure (freeCovarianceCLM mass hmass)

/-! ## Properties of the free field measure

These follow directly from `GaussianField.Properties`. -/

/-- The free field measure is a probability measure. -/
theorem freeFieldMeasure_isProbability (mass : ℝ) (hmass : 0 < mass) :
    IsProbabilityMeasure (freeFieldMeasure mass hmass) :=
  GaussianField.measure_isProbability _

/-- The free field is centered: E[ω(f)] = 0 for all test functions f.
    Proof: `GaussianField.measure_centered`. -/
theorem freeField_centered (mass : ℝ) (hmass : 0 < mass) (f : TestFun2D) :
    ∫ ω, ω f ∂(freeFieldMeasure mass hmass) = 0 :=
  GaussianField.measure_centered _ f

/-- Two-point function: E[ω(f)ω(g)] = C(f,g).
    This is the free propagator C(f,g) = ∫ f(x) (-Δ+m²)⁻¹(x,y) g(y) dx dy.
    Proof: `GaussianField.cross_moment_eq_covariance`. -/
theorem freeField_two_point (mass : ℝ) (hmass : 0 < mass) (f g : TestFun2D) :
    ∫ ω, ω f * ω g ∂(freeFieldMeasure mass hmass) =
      GaussianField.covariance (freeCovarianceCLM mass hmass) f g :=
  GaussianField.cross_moment_eq_covariance _ f g

/-- Pairing ω(f) is in Lᵖ for all finite p (Fernique-type bound).
    Proof: `GaussianField.pairing_memLp`. -/
theorem freeField_pairing_memLp (mass : ℝ) (hmass : 0 < mass)
    (f : TestFun2D) (p : ℝ≥0) :
    MemLp (fun ω : FieldConfig2D => ω f) p (freeFieldMeasure mass hmass) :=
  GaussianField.pairing_memLp (freeCovarianceCLM mass hmass) f p

/-! ## The free covariance as a kernel

The covariance C(x,y) = (-Δ + m²)⁻¹(x,y) has an explicit integral kernel
in d=2. It is the modified Bessel function K₀(m|x-y|) up to normalization:
  C(x,y) = (2π)⁻¹ K₀(m|x-y|)

Key properties:
- C(x,y) ~ -(2π)⁻¹ ln|x-y| as |x-y| → 0 (logarithmic divergence in d=2)
- C(x,y) ~ const × |x-y|⁻¹/² e^{-m|x-y|} as |x-y| → ∞ (exponential decay)
-/

/-- The pointwise covariance C(x,y) = (-Δ+m²)⁻¹(x,y) as a function on ℝ² × ℝ².
    This is the Green's function / Euclidean propagator. -/
def freeCovKernel (mass : ℝ) (x y : Spacetime2D) : ℝ := by
  sorry

/-- The covariance kernel is symmetric. -/
theorem freeCovKernel_symm (mass : ℝ) (x y : Spacetime2D) :
    freeCovKernel mass x y = freeCovKernel mass y x := by
  sorry

/-- The covariance kernel is positive definite. -/
theorem freeCovKernel_pos_def (mass : ℝ) (hmass : 0 < mass) :
    ∀ (n : ℕ) (x : Fin n → Spacetime2D) (c : Fin n → ℝ),
      0 ≤ ∑ i, ∑ j, c i * c j * freeCovKernel mass (x i) (x j) := by
  sorry

/-- The UV-regularized covariance c_κ(x) = C_κ(x,x), where C_κ is the
    covariance smeared at scale 1/κ.
    In d=2: c_κ(x) ~ (2π)⁻¹ ln κ + O(1) as κ → ∞. -/
def regularizedPointCovariance (mass : ℝ) (κ : UVCutoff) : ℝ := by
  sorry

/-- The logarithmic divergence: c_κ ~ (2π)⁻¹ ln κ in d=2. -/
theorem regularizedPointCovariance_log_divergence (mass : ℝ) (hmass : 0 < mass) :
    ∃ C₁ C₂ : ℝ, ∀ κ : UVCutoff,
      |regularizedPointCovariance mass κ - (2 * Real.pi)⁻¹ * Real.log κ.κ| ≤ C₁ + C₂ := by
  sorry

end

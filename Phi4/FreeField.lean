/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.Defs
import HeatKernel
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

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
    These are the diagonal entries of T in the adapted basis.
    Convention matches GaussianField.qftSingularValue: λ ^ (-1/2). -/
def freeSingularValue (mass : ℝ) (m : ℕ) : ℝ :=
  (freeEigenvalue mass m)⁻¹ ^ ((1 : ℝ)/2)

/-- The eigenvalues have a uniform lower bound: λₘ ≥ 2 + mass². -/
theorem freeEigenvalue_lower_bound (mass : ℝ) (m : ℕ) :
    2 + mass ^ 2 ≤ freeEigenvalue mass m := by
  unfold freeEigenvalue
  have h1 : (0 : ℝ) ≤ (m.unpair.1 : ℝ) := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ (m.unpair.2 : ℝ) := Nat.cast_nonneg _
  linarith

/-- The singular values are nonneg. -/
theorem freeSingularValue_nonneg (mass : ℝ) (hmass : 0 < mass) (m : ℕ) :
    0 ≤ freeSingularValue mass m :=
  Real.rpow_nonneg (inv_nonneg.mpr (le_of_lt (freeEigenvalue_pos mass hmass m))) _

/-- The singular values are bounded (needed for spectralCLM).
    Since λₘ ≥ 2 + mass² > 0, we have σₘ = λₘ⁻¹/² ≤ (2+mass²)⁻¹/². -/
theorem free_singular_values_bounded (mass : ℝ) (hmass : 0 < mass) :
    ∃ C : ℝ, ∀ m : ℕ, |freeSingularValue mass m| ≤ C := by
  use (2 + mass ^ 2)⁻¹ ^ ((1 : ℝ)/2)
  intro m
  rw [abs_of_nonneg (freeSingularValue_nonneg mass hmass m)]
  unfold freeSingularValue
  have hev_pos := freeEigenvalue_pos mass hmass m
  apply Real.rpow_le_rpow (inv_nonneg.mpr hev_pos.le)
  · exact (inv_le_inv₀ hev_pos (by positivity)).mpr (freeEigenvalue_lower_bound mass m)
  · positivity

/-- The singular values form a bounded sequence (IsBoundedSeq form for spectralCLM). -/
theorem free_singular_values_isBoundedSeq (mass : ℝ) (hmass : 0 < mass) :
    GaussianField.IsBoundedSeq (fun m => freeSingularValue mass m) :=
  free_singular_values_bounded mass hmass

/-! ## Free covariance CLM and Gaussian measure -/

/-- The covariance CLM T : S(ℝ²) →L[ℝ] ℓ² for the free field.
    This maps test functions to sequences via the Hermite expansion,
    weighted by the singular values σₘ:
      T(f)ₘ = σₘ · coeffₘ(f)
    where coeffₘ are the Schauder coefficients from the DyninMityagin basis. -/
def freeCovarianceCLM (mass : ℝ) (hmass : 0 < mass) :
    TestFun2D →L[ℝ] GaussianField.ell2' :=
  GaussianField.spectralCLM
    (fun m => freeSingularValue mass m)
    (free_singular_values_isBoundedSeq mass hmass)

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

/-- Exponential moments of linear pairings under the free field measure. -/
theorem freeField_pairing_exp_integrable (mass : ℝ) (hmass : 0 < mass)
    (f : TestFun2D) (t : ℝ) :
    Integrable (fun ω : FieldConfig2D => Real.exp (t * ω f))
      (freeFieldMeasure mass hmass) := by
  let T := freeCovarianceCLM mass hmass
  have hgauss := GaussianField.pairing_is_gaussian T f
  have hgaussInt :
      Integrable (fun x : ℝ => Real.exp (t * x))
        (ProbabilityTheory.gaussianReal 0
          ((@inner ℝ GaussianField.ell2' _ (T f) (T f) : ℝ).toNNReal)) :=
    ProbabilityTheory.integrable_exp_mul_gaussianReal (μ := 0)
      (v := ((@inner ℝ GaussianField.ell2' _ (T f) (T f) : ℝ).toNNReal)) t
  have hmapInt :
      Integrable (fun x : ℝ => Real.exp (t * x))
        ((freeFieldMeasure mass hmass).map (fun ω : FieldConfig2D => ω f)) := by
    simpa [freeFieldMeasure, T] using (hgauss.symm ▸ hgaussInt)
  simpa [Function.comp] using
    hmapInt.comp_measurable (GaussianField.configuration_eval_measurable f)

/-! ## The free covariance as a kernel

The covariance C(x,y) = (-Δ + m²)⁻¹(x,y) has an explicit integral kernel
in d=2. It is the modified Bessel function K₀(m|x-y|) up to normalization:
  C(x,y) = (2π)⁻¹ K₀(m|x-y|)

Key properties:
- C(x,y) ~ -(2π)⁻¹ ln|x-y| as |x-y| → 0 (logarithmic divergence in d=2)
- C(x,y) ~ const × |x-y|⁻¹/² e^{-m|x-y|} as |x-y| → ∞ (exponential decay)
-/

/-- The pointwise covariance C(x,y) = (-Δ+m²)⁻¹(x,y) as a function on ℝ² × ℝ².
    This is the Green's function / Euclidean propagator.

    Defined via the heat kernel representation:
      C(x,y) = ∫₀^∞ (4πt)⁻¹ exp(-m²t - |x-y|²/(4t)) dt

    This integral converges for mass > 0 and equals (2π)⁻¹ K₀(m|x-y|)
    where K₀ is the modified Bessel function of the second kind. -/
def freeCovKernel (mass : ℝ) (x y : Spacetime2D) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ),
    (4 * Real.pi * t)⁻¹ * Real.exp (-(mass ^ 2 * t + ‖x - y‖ ^ 2 / (4 * t)))

/-- Interface identifying the Hilbert-space covariance used by
    `freeFieldMeasure` with the Green-kernel bilinear form.
    This is the sound bridge between the `freeCovarianceCLM` representation
    and the explicit kernel `freeCovKernel`. -/
class FreeCovarianceKernelModel (mass : ℝ) (hmass : 0 < mass) where
  covariance_eq_kernel :
    ∀ (f g : TestFun2D),
      GaussianField.covariance (freeCovarianceCLM mass hmass) f g =
        ∫ x, ∫ y, f x * freeCovKernel mass x y * g y

/-- Construct `FreeCovarianceKernelModel` from an explicit covariance-kernel
    bridge theorem. -/
theorem freeCovarianceKernelModel_nonempty_of_data (mass : ℝ) (hmass : 0 < mass)
    (hcov :
      ∀ (f g : TestFun2D),
        GaussianField.covariance (freeCovarianceCLM mass hmass) f g =
          ∫ x, ∫ y, f x * freeCovKernel mass x y * g y) :
    Nonempty (FreeCovarianceKernelModel mass hmass) := by
  exact ⟨{ covariance_eq_kernel := hcov }⟩

/-- Bridge theorem: free-field covariance equals the Green-kernel bilinear form. -/
theorem freeCovariance_eq_kernel (mass : ℝ) (hmass : 0 < mass)
    [FreeCovarianceKernelModel mass hmass]
    (f g : TestFun2D) :
    GaussianField.covariance (freeCovarianceCLM mass hmass) f g =
      ∫ x, ∫ y, f x * freeCovKernel mass x y * g y := by
  exact FreeCovarianceKernelModel.covariance_eq_kernel
    (mass := mass) (hmass := hmass) f g

/-- Kernel-form two-point identity for the free field:
    `E[ω(f)ω(g)] = ∬ f(x) C(x,y) g(y) dx dy`. -/
theorem freeField_two_point_kernel (mass : ℝ) (hmass : 0 < mass)
    [FreeCovarianceKernelModel mass hmass]
    (f g : TestFun2D) :
    ∫ ω, ω f * ω g ∂(freeFieldMeasure mass hmass) =
      ∫ x, ∫ y, f x * freeCovKernel mass x y * g y := by
  rw [freeField_two_point]
  exact freeCovariance_eq_kernel mass hmass f g

/-- The covariance kernel is symmetric. -/
theorem freeCovKernel_symm (mass : ℝ) (x y : Spacetime2D) :
    freeCovKernel mass x y = freeCovKernel mass y x := by
  simp only [freeCovKernel, norm_sub_rev]

/-- Positivity of the free covariance as a smeared quadratic form.
    This is the mathematically sound positivity statement used by the Gaussian
    construction: for any finite family of test functions, the covariance matrix
    is positive semidefinite. -/
theorem freeCovKernel_pos_def (mass : ℝ) (hmass : 0 < mass) :
    ∀ (n : ℕ) (f : Fin n → TestFun2D) (c : Fin n → ℝ),
      0 ≤ ∑ i, ∑ j, c i * c j *
        GaussianField.covariance (freeCovarianceCLM mass hmass) (f i) (f j) := by
  intro n f c
  let T := freeCovarianceCLM mass hmass
  have h_expand :
      @inner ℝ GaussianField.ell2' _
        (∑ i, c i • T (f i)) (∑ j, c j • T (f j))
      = ∑ i, ∑ j, c i * c j * GaussianField.covariance T (f i) (f j) := by
    calc
      @inner ℝ GaussianField.ell2' _ (∑ i, c i • T (f i)) (∑ j, c j • T (f j))
          = ∑ i, @inner ℝ GaussianField.ell2' _ (c i • T (f i)) (∑ j, c j • T (f j)) := by
              simpa using
                (sum_inner (s := Finset.univ)
                  (f := fun i : Fin n => c i • T (f i))
                  (x := ∑ j, c j • T (f j)))
      _ = ∑ i, ∑ j, @inner ℝ GaussianField.ell2' _ (c i • T (f i)) (c j • T (f j)) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            simpa using
              (inner_sum (s := Finset.univ)
                (f := fun j : Fin n => c j • T (f j))
                (x := c i • T (f i)))
      _ = ∑ i, ∑ j, c i * c j * GaussianField.covariance T (f i) (f j) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            refine Finset.sum_congr rfl ?_
            intro j _
            simp [GaussianField.covariance, real_inner_smul_left, real_inner_smul_right]
            ring
  have h_nonneg :
      0 ≤ @inner ℝ GaussianField.ell2' _
        (∑ i, c i • T (f i)) (∑ i, c i • T (f i)) :=
    real_inner_self_nonneg
  calc
    0 ≤ @inner ℝ GaussianField.ell2' _
        (∑ i, c i • T (f i)) (∑ i, c i • T (f i)) := h_nonneg
    _ = ∑ i, ∑ j, c i * c j * GaussianField.covariance T (f i) (f j) := by
      simpa using h_expand

/-- Positive-semidefiniteness of the free covariance in kernel form. -/
theorem freeCovKernel_pos_def_integral (mass : ℝ) (hmass : 0 < mass)
    [FreeCovarianceKernelModel mass hmass] :
    ∀ (n : ℕ) (f : Fin n → TestFun2D) (c : Fin n → ℝ),
      0 ≤ ∑ i, ∑ j, c i * c j *
        (∫ x, ∫ y, f i x * freeCovKernel mass x y * f j y) := by
  intro n f c
  have hcov := freeCovKernel_pos_def mass hmass n f c
  have hrewrite :
      (∑ i, ∑ j, c i * c j * GaussianField.covariance (freeCovarianceCLM mass hmass) (f i) (f j))
        =
      (∑ i, ∑ j, c i * c j * (∫ x, ∫ y, f i x * freeCovKernel mass x y * f j y)) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [freeCovariance_eq_kernel mass hmass (f i) (f j)]
  rw [hrewrite] at hcov
  exact hcov

/-- UV mollifier: a smooth bump function centered at x with support of radius ~1/κ.
    This is the approximate delta function δ_{κ,x} used for UV regularization.
    The function is C^∞, compactly supported in a ball of radius κ⁻¹ around x,
    and equals 1 on a ball of radius (2κ)⁻¹ around x.

    The exact choice of mollifier does not affect the UV limit (κ → ∞),
    only the intermediate regularized quantities. -/
def uvMollifier (κ : UVCutoff) (x : Spacetime2D) : TestFun2D :=
  let bump : ContDiffBump x :=
    ⟨(2 * κ.κ)⁻¹, κ.κ⁻¹,
     inv_pos.mpr (mul_pos two_pos κ.hκ),
     by rw [inv_lt_inv₀ (mul_pos two_pos κ.hκ) κ.hκ]; linarith [κ.hκ]⟩
  bump.hasCompactSupport.toSchwartzMap bump.contDiff

/-- The UV-regularized covariance c_κ = Cov(δ_{κ,0}, δ_{κ,0}), where δ_{κ,0} is
    the UV mollifier centered at the origin.
    This is the variance of the regularized field: c_κ = E[φ_κ(0)²].
    In d=2 one expects logarithmic UV growth; we only use the variance
    definition here. -/
def regularizedPointCovariance (mass : ℝ) (κ : UVCutoff) : ℝ :=
  if h : 0 < mass then
    GaussianField.covariance (freeCovarianceCLM mass h) (uvMollifier κ 0) (uvMollifier κ 0)
  else 0

/-- The regularized point covariance is nonnegative for positive mass. -/
theorem regularizedPointCovariance_nonneg (mass : ℝ) (hmass : 0 < mass) (κ : UVCutoff) :
    0 ≤ regularizedPointCovariance mass κ := by
  simp [regularizedPointCovariance, hmass, GaussianField.covariance]

end

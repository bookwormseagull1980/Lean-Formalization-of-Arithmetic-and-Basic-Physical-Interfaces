module

public import GeneratedFoundations.Operations.FiniteEigenbasisCore

/-!
# Quadratic forms on the full closed spectral domain

The coefficient identity for a closed spectral multiplier determines its
quadratic form by Parseval. A uniform coefficient lower bound therefore
holds on the full closed domain, with no finite-cutoff constant. This lemma
is used after the differential operator and its complete field basis have
been constructed.
-/

@[expose] public section

noncomputable section

open scoped ComplexConjugate LinearPMap

namespace GeneratedFoundations.Operations.SpectralFormLowerBound

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] (B : HilbertBasis ι ℂ E) (eigenvalue : ι → ℝ)

private theorem coefficient_real (c : ℂ) (a : ℝ) :
    (conj c * ((a : ℂ) * c)).re = a * ‖c‖ ^ 2 := by
  have h : conj c * ((a : ℂ) * c) =
      (a : ℂ) * (c * conj c) := by ring
  rw [h, Complex.mul_conj']
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]

omit [CompleteSpace E] in
/-- Parseval's norm identity in the original field metric. -/
theorem hasSum_norm_sq (x : E) :
    HasSum (fun i => ‖inner ℂ (B i) x‖ ^ 2) (‖x‖ ^ 2) := by
  have h := (B.hasSum_inner_mul_inner x x).mapL Complex.reCLM
  convert h using 1
  · funext i
    change ‖inner ℂ (B i) x‖ ^ 2 =
      (inner ℂ x (B i) * inner ℂ (B i) x).re
    rw [← inner_conj_symm (𝕜 := ℂ) x (B i)]
    simpa only [Complex.ofReal_one, one_mul] using
      (coefficient_real (inner ℂ (B i) x) 1).symm
  · exact norm_sq_eq_re_inner (𝕜 := ℂ) x

/-- The real quadratic form of the unique closed multiplier is the sum of
its actual energy coefficients. -/
theorem hasSum_quadratic
    (x : (FiniteEigenbasisCore.finiteMultiplier B eigenvalue).closure.domain) :
    HasSum (fun i => eigenvalue i * ‖inner ℂ (B i) (x : E)‖ ^ 2)
      (inner ℂ (x : E)
        ((FiniteEigenbasisCore.finiteMultiplier B eigenvalue).closure x)).re := by
  have h := (B.hasSum_inner_mul_inner (x : E)
    ((FiniteEigenbasisCore.finiteMultiplier B eigenvalue).closure x)).mapL
      Complex.reCLM
  convert h using 1
  · funext i
    change _ = (inner ℂ (x : E) (B i) *
      inner ℂ (B i)
        ((FiniteEigenbasisCore.finiteMultiplier B eigenvalue).closure x)).re
    rw [FiniteEigenbasisCore.closure_coefficients,
      ← inner_conj_symm (𝕜 := ℂ) (x : E) (B i)]
    exact (coefficient_real (inner ℂ (B i) (x : E)) (eigenvalue i)).symm
  · rfl

/-- No boundedness assumption on the multiplier is needed. The estimate
uses the full closed domain and the original Hilbert norm. -/
theorem closed_quadratic_lower_bound (g : ℝ)
    (hg : ∀ i, g ≤ eigenvalue i)
    (x : (FiniteEigenbasisCore.finiteMultiplier B eigenvalue).closure.domain) :
    g * ‖(x : E)‖ ^ 2 ≤
      (inner ℂ (x : E)
        ((FiniteEigenbasisCore.finiteMultiplier B eigenvalue).closure x)).re := by
  apply hasSum_le (fun i => mul_le_mul_of_nonneg_right (hg i) (sq_nonneg _))
    ((hasSum_norm_sq B (x : E)).mul_left g) (hasSum_quadratic B eigenvalue x)

/-- Parseval applied to the differentiated field, on the full closed domain.
This identity also applies when the real eigenvalues have both signs. -/
theorem hasSum_image_norm_sq
    (x : (FiniteEigenbasisCore.finiteMultiplier B eigenvalue).closure.domain) :
    HasSum (fun i => eigenvalue i ^ 2 * ‖inner ℂ (B i) (x : E)‖ ^ 2)
      (‖(FiniteEigenbasisCore.finiteMultiplier B eigenvalue).closure x‖ ^ 2) := by
  have h := hasSum_norm_sq B
    ((FiniteEigenbasisCore.finiteMultiplier B eigenvalue).closure x)
  simpa only [FiniteEigenbasisCore.closure_coefficients, norm_mul, mul_pow,
    Complex.norm_real, Real.norm_eq_abs, sq_abs] using h

theorem closed_norm_lower_bound (g : ℝ)
    (hg : ∀ i, g ≤ eigenvalue i ^ 2)
    (x : (FiniteEigenbasisCore.finiteMultiplier B eigenvalue).closure.domain) :
    g * ‖(x : E)‖ ^ 2 ≤
      ‖(FiniteEigenbasisCore.finiteMultiplier B eigenvalue).closure x‖ ^ 2 := by
  apply hasSum_le (fun i => mul_le_mul_of_nonneg_right (hg i) (sq_nonneg _))
    ((hasSum_norm_sq B (x : E)).mul_left g) (hasSum_image_norm_sq B eigenvalue x)

end GeneratedFoundations.Operations.SpectralFormLowerBound

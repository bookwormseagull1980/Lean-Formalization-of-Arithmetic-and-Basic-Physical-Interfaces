module

public import GeneratedFoundations.Operations.HermiteSpan

/-! Exponential moments of a Gaussian-weighted orthogonal vector

An arbitrary Lebesgue `L²` vector is multiplied by the same positive Gaussian
that generates the Hermite family. Its moments vanish when the vector is
orthogonal to that family. Completing the square and the `L²` product estimate
give absolute exponential moments of every order. No continuity of an `L²`
representative, and no completeness of the Hermite family, is assumed.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped SchwartzMap ComplexConjugate
open GeneratedFoundations.Correlation.GaussianCorrelation
open GeneratedFoundations.Correlation.ComplexGaussianStates
open GeneratedFoundations.Operations.HermiteSource
open GeneratedFoundations.Operations.GaussianAffineLadder
open GeneratedFoundations.Operations.HermiteSpan

namespace GeneratedFoundations.Operations.HermiteMoments

def weightedSource (b : ℝ) (F : ComplexL2) (x : ℝ) : ℂ :=
  (groundProfile b x : ℂ) * F x

theorem weightedSource_integrable {b : ℝ} (hb : 0 < b) (F : ComplexL2) :
    Integrable (weightedSource b F) volume := by
  exact ((groundProfile_memLp hb).ofReal :
    MemLp (fun x => (groundProfile b x : ℂ)) 2 volume).integrable_mul (Lp.memLp F)

theorem weightedSource_moment_integrable {b : ℝ} (hb : 0 < b)
    (F : ComplexL2) (n : ℕ) :
    Integrable (fun x : ℝ => (x : ℂ) ^ n * weightedSource b F x) volume := by
  have h := ((monomialGaussian hb n).memLp 2 volume).integrable_mul (Lp.memLp F)
  change Integrable (fun x : ℝ => monomialGaussian hb n x * F x) volume at h
  simpa only [monomialGaussian_apply, weightedSource, mul_assoc] using h

/-- The moment is the actual `L²` inner product with a monomial Gaussian. -/
theorem monomial_inner_eq_moment {b : ℝ} (hb : 0 < b) (F : ComplexL2) (n : ℕ) :
    inner ℂ (embedding (monomialGaussian hb n)) F =
      ∫ x : ℝ, (x : ℂ) ^ n * weightedSource b F x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(monomialGaussian hb n).coeFn_toLp 2 volume] with x hx
  change inner ℂ (((monomialGaussian hb n).toLp 2 volume) x) (F x) = _
  rw [hx, monomialGaussian_apply]
  simp only [RCLike.inner_apply, map_mul, map_pow, Complex.conj_ofReal, weightedSource]
  ring

theorem weightedSource_moments_eq_zero {b : ℝ} (hb : 0 < b) (F : ComplexL2)
    (hF : ∀ n, inner ℂ (HermiteFamily.state hb n) F = 0) (n : ℕ) :
    (∫ x : ℝ, (x : ℂ) ^ n * weightedSource b F x) = 0 := by
  rw [← monomial_inner_eq_moment hb F n]
  exact inner_eq_zero_of_mem_span hb F hF (monomialGaussian_mem_span hb n)

def exponentialProfile (b r x : ℝ) : ℝ := groundProfile b x * Real.exp (r * |x|)

theorem exponentialProfile_continuous (b r : ℝ) : Continuous (exponentialProfile b r) :=
  (groundProfile_continuous b).mul
    (Real.continuous_exp.comp (continuous_const.mul continuous_abs))

theorem exponentialProfile_sq {b : ℝ} (hb : 0 < b) (r x : ℝ) :
    exponentialProfile b r x ^ 2 =
      Real.exp (-x ^ 2 / b ^ 2 + 2 * r * |x|) / normalizationMass (sourceWidth b) := by
  have hm := normalizationMass_pos (sourceWidth_pos hb)
  have he : Real.exp (-(x ^ 2 / (2 * b ^ 2))) ^ 2 = Real.exp (-x ^ 2 / b ^ 2) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hr : Real.exp (r * |x|) ^ 2 = Real.exp (2 * r * |x|) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [exponentialProfile, mul_pow, groundProfile_eq, div_pow, Real.sq_sqrt hm.le,
    he, hr, div_mul_eq_mul_div, ← Real.exp_add]

/-- A uniform Gaussian majorant follows from the square-completion inequality. -/
theorem exponentialProfile_sq_le {b : ℝ} (hb : 0 < b) (r x : ℝ) :
    exponentialProfile b r x ^ 2 ≤
      (Real.exp (2 * r ^ 2 * b ^ 2) / normalizationMass (sourceWidth b)) *
        Real.exp (-(1 / (2 * b ^ 2)) * x ^ 2) := by
  have hm := normalizationMass_pos (sourceWidth_pos hb)
  have hy : 2 * r * |x| - 2 * r ^ 2 * b ^ 2 ≤ x ^ 2 / (2 * b ^ 2) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * b ^ 2)).mpr
    nlinarith [sq_nonneg (|x| - 2 * r * b ^ 2), sq_abs x]
  have hdiv : x ^ 2 / b ^ 2 = 2 * (x ^ 2 / (2 * b ^ 2)) := by ring
  have harg : -x ^ 2 / b ^ 2 + 2 * r * |x| ≤
      2 * r ^ 2 * b ^ 2 - x ^ 2 / (2 * b ^ 2) := by
    rw [neg_div]
    nlinarith
  rw [exponentialProfile_sq hb]
  calc
    Real.exp (-x ^ 2 / b ^ 2 + 2 * r * |x|) / normalizationMass (sourceWidth b) ≤
        Real.exp (2 * r ^ 2 * b ^ 2 - x ^ 2 / (2 * b ^ 2)) /
          normalizationMass (sourceWidth b) :=
      div_le_div_of_nonneg_right (Real.exp_le_exp.mpr harg) hm.le
    _ = _ := by
      rw [sub_eq_add_neg, Real.exp_add]
      have hexp : -(x ^ 2 / (2 * b ^ 2)) = -(1 / (2 * b ^ 2)) * x ^ 2 := by ring
      rw [hexp]
      ring

theorem exponentialProfile_memLp {b : ℝ} (hb : 0 < b) (r : ℝ) :
    MemLp (exponentialProfile b r) 2 volume := by
  have hc := exponentialProfile_continuous b r
  apply (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).mpr
  have hg := integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < 1 / (2 * b ^ 2))
  apply (hg.const_mul
    (Real.exp (2 * r ^ 2 * b ^ 2) / normalizationMass (sourceWidth b))).mono'
      (hc.pow 2).aestronglyMeasurable
  filter_upwards [] with x
  simpa only [Pi.pow_apply, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg (exponentialProfile b r x))]
    using exponentialProfile_sq_le hb r x

/-- Every exponential absolute moment is finite, for arbitrary `L²` representatives. -/
theorem weightedSource_exponential_integrable {b : ℝ} (hb : 0 < b)
    (F : ComplexL2) (r : ℝ) :
    Integrable (fun x : ℝ => ‖weightedSource b F x‖ * Real.exp (r * |x|)) volume := by
  have h := (exponentialProfile_memLp hb r).integrable_mul (Lp.memLp F).norm
  convert h using 1
  funext x
  simp only [weightedSource, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (groundProfile_pos hb x).le, Pi.mul_apply, exponentialProfile]
  ring

/-- Strict positivity of the same Gaussian removes the weight almost everywhere. -/
theorem eq_zero_of_weightedSource_ae_zero {b : ℝ} (hb : 0 < b) (F : ComplexL2)
    (h : weightedSource b F =ᵐ[volume] 0) : F = 0 := by
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [h] with x hx
  change (groundProfile b x : ℂ) * F x = 0 at hx
  have hg : (groundProfile b x : ℂ) ≠ 0 := by exact_mod_cast (groundProfile_pos hb x).ne'
  exact (mul_eq_zero.mp hx).resolve_left hg

end GeneratedFoundations.Operations.HermiteMoments

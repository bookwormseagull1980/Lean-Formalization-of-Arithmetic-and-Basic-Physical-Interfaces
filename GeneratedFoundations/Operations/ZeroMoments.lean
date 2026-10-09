module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Tactic.Ring

/-!
# Uniqueness from vanishing moments with exponential control

An integrable complex function with every absolute exponential moment is
determined by its polynomial moments. Absolute domination justifies the
exponential series inside the integral. Fourier inversion is applied only to
Schwartz test functions; no continuity of the original function is assumed.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform
open scoped FourierTransform SchwartzMap RealInnerProductSpace

namespace GeneratedFoundations.Operations.ZeroMoments

theorem integral_exp_mul_eq_zero {q : ℝ → ℂ} (hq : Integrable q)
    (hexp : ∀ r : ℝ, 0 ≤ r → Integrable (fun x => ‖q x‖ * Real.exp (r * |x|)))
    (hmom : ∀ n : ℕ, ∫ x : ℝ, (x : ℂ) ^ n * q x = 0) (z : ℂ) :
    ∫ x : ℝ, Complex.exp (z * x) * q x = 0 := by
  let term : ℕ → ℝ → ℂ := fun n x => (z * x) ^ n / n.factorial * q x
  let bound : ℕ → ℝ → ℝ := fun n x =>
    (‖z‖ * |x|) ^ n / n.factorial * ‖q x‖
  have hbound (x : ℝ) : HasSum (fun n => bound n x)
      (Real.exp (‖z‖ * |x|) * ‖q x‖) := by
    simpa only [bound, ← Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp (‖z‖ * |x|)).mul_right ‖q x‖
  have hnorm (n : ℕ) (x : ℝ) : ‖term n x‖ = bound n x := by
    simp [term, bound, norm_pow]
  have hs : HasSum (fun n => ∫ x : ℝ, term n x)
      (∫ x : ℝ, Complex.exp (z * x) * q x) := by
    apply hasSum_integral_of_dominated_convergence bound
    · intro n
      exact (by fun_prop : Continuous (fun x : ℝ => (z * x) ^ n / (n.factorial : ℂ))).aestronglyMeasurable.mul hq.aestronglyMeasurable
    · intro n
      exact Filter.Eventually.of_forall (fun x => (hnorm n x).le)
    · exact Filter.Eventually.of_forall (fun x => (hbound x).summable)
    · have he : (fun x : ℝ => ∑' n, bound n x) =
          fun x => ‖q x‖ * Real.exp (‖z‖ * |x|) := by
        funext x
        exact (hbound x).tsum_eq.trans (mul_comm _ _)
      rw [he]
      exact hexp ‖z‖ (norm_nonneg z)
    · apply Filter.Eventually.of_forall
      intro x
      simpa only [term, ← Complex.exp_eq_exp_ℂ] using
        (NormedSpace.expSeries_div_hasSum_exp (z * (x : ℂ))).mul_right (q x)
  have hterm (n : ℕ) : (∫ x : ℝ, term n x) = 0 := by
    calc
      _ = (z ^ n / (n.factorial : ℂ)) * (∫ x : ℝ, (x : ℂ) ^ n * q x) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro x
        simp only [term, mul_pow]
        ring
      _ = 0 := by rw [hmom, mul_zero]
  have hzero : (fun n => ∫ x : ℝ, term n x) = fun _ => (0 : ℂ) := funext hterm
  rw [hzero] at hs
  exact hs.unique hasSum_zero

theorem fourier_eq_zero_of_moments {q : ℝ → ℂ} (hq : Integrable q)
    (hexp : ∀ r : ℝ, 0 ≤ r → Integrable (fun x => ‖q x‖ * Real.exp (r * |x|)))
    (hmom : ∀ n : ℕ, ∫ x : ℝ, (x : ℂ) ^ n * q x = 0) :
    ∀ ξ : ℝ, 𝓕 q ξ = 0 := by
  intro ξ
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hz := integral_exp_mul_eq_zero hq hexp hmom
    ((-2 * Real.pi * ξ : ℝ) * Complex.I)
  convert hz using 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  simp only [smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_neg,
    Complex.ofReal_ofNat]
  congr 2
  ring

/-- Fourier uniqueness for integrable functions, without pointwise regularity. -/
theorem ae_eq_zero_of_fourier_eq_zero {q : ℝ → ℂ} (hq : Integrable q)
    (hzero : ∀ ξ : ℝ, 𝓕 q ξ = 0) : ∀ᵐ x, q x = 0 := by
  have htest (φ : 𝓢(ℝ, ℂ)) : (∫ x : ℝ, φ x * q x) = 0 := by
    let ψ : 𝓢(ℝ, ℂ) := 𝓕⁻ φ
    have hflip : (innerₗ ℝ).flip = innerₗ ℝ := flip_innerₗ ℝ
    have hswap := VectorFourier.integral_fourierIntegral_smul_eq_flip
      (e := Real.fourierChar) (μ := volume) (ν := volume) (L := innerₗ ℝ)
      Real.continuous_fourierChar continuous_inner hq ψ.integrable
    rw [hflip] at hswap
    change (∫ ξ : ℝ, 𝓕 q ξ * ψ ξ) =
      ∫ x : ℝ, q x * 𝓕 (ψ : ℝ → ℂ) x at hswap
    have hψ : 𝓕 (ψ : ℝ → ℂ) = (φ : ℝ → ℂ) := by
      change ((𝓕 ψ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) = _
      simp [ψ]
    rw [hψ] at hswap
    simpa only [hzero, zero_mul, integral_zero, mul_comm] using hswap.symm
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hq.locallyIntegrable
  intro g hg hsupp
  have hc : HasCompactSupport (Complex.ofRealCLM ∘ g) := hsupp.comp_left rfl
  let φ : 𝓢(ℝ, ℂ) := hc.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hg)
  change (∫ x : ℝ, (g x : ℂ) * q x) = 0
  exact htest φ

theorem ae_eq_zero_of_all_moments_eq_zero {q : ℝ → ℂ} (hq : Integrable q)
    (hexp : ∀ r : ℝ, 0 ≤ r → Integrable (fun x => ‖q x‖ * Real.exp (r * |x|)))
    (hmom : ∀ n : ℕ, ∫ x : ℝ, (x : ℂ) ^ n * q x = 0) :
    ∀ᵐ x, q x = 0 :=
  ae_eq_zero_of_fourier_eq_zero hq (fourier_eq_zero_of_moments hq hexp hmom)

end GeneratedFoundations.Operations.ZeroMoments

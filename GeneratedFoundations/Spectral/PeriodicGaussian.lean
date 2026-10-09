module

public import GeneratedFoundations.Correlation.GaussianCorrelation
public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

/-!
# Periodization of the generated Gaussian density

The density is the normalized change kernel of the compositional Gaussian
source. Its periodization is an actual locally absolutely convergent sum of
translates. Poisson summation identifies its Fourier coefficients with the
characteristic function of that source.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Asymptotics TopologicalSpace
open scoped FourierTransform Topology NNReal

namespace GeneratedFoundations.Spectral.PeriodicGaussian

open GeneratedFoundations.Correlation.GaussianCorrelation

/-- The continuous complex-valued representative of the generated density. -/
def density (b : ℝ) : C(ℝ, ℂ) :=
  ⟨fun x => (changeKernel b x : ℂ),
    Complex.continuous_ofReal.comp ((profile_continuous b).div_const _)⟩

theorem density_apply (b x : ℝ) : density b x = (changeKernel b x : ℂ) := rfl

theorem density_pos {b : ℝ} (hb : 0 < b) (x : ℝ) :
    0 < (density b x).re := by
  change 0 < changeKernel b x
  exact div_pos (profile_pos b x) (mul_pos (Real.sqrt_pos.mpr (by positivity)) hb)

theorem density_even (b x : ℝ) : density b (-x) = density b x := by
  simp only [density_apply, changeKernel, profile_even]

theorem density_eq_exp (b x : ℝ) :
    density b x = ((Real.sqrt (2 * Real.pi) * b : ℝ) : ℂ)⁻¹ *
      Complex.exp (-((1 / (2 * b ^ 2) : ℝ) : ℂ) * (x : ℂ) ^ 2) := by
  rw [density_apply]
  unfold changeKernel profile
  rw [Complex.ofReal_div, Complex.ofReal_exp, div_eq_mul_inv, mul_comm]
  congr 1
  congr 1
  push_cast
  ring

/-- The Fourier transform is derived from the Gaussian probability law. -/
theorem density_fourier {b : ℝ} (hb : 0 < b) (ξ : ℝ) :
    𝓕 (density b : ℝ → ℂ) ξ =
      (Real.exp (-2 * Real.pi ^ 2 * b ^ 2 * ξ ^ 2) : ℂ) := by
  let v : ℝ≥0 := ⟨b ^ 2, sq_nonneg b⟩
  have hv : v ≠ 0 := by
    apply ne_of_gt
    change 0 < b ^ 2
    positivity
  have hchar := ProbabilityTheory.charFun_gaussianReal (μ := 0) (v := v)
    (-2 * Real.pi * ξ)
  rw [charFun_apply_real, ProbabilityTheory.integral_gaussianReal_eq_integral_smul hv]
    at hchar
  calc
    𝓕 (density b : ℝ → ℂ) ξ =
        ∫ x : ℝ, ProbabilityTheory.gaussianPDFReal 0 v x •
          Complex.exp (((-2 * Real.pi * ξ : ℝ) : ℂ) * x * Complex.I) := by
      rw [Real.fourier_real_eq_integral_exp_smul]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [density_apply, changeKernel_eq_gaussianPDFReal hb]
      rw [smul_eq_mul, Complex.real_smul, mul_comm]
      congr 1
      congr 1
      push_cast
      ring
    _ = Complex.exp (((-2 * Real.pi * ξ : ℝ) : ℂ) * 0 * Complex.I -
        (v : ℂ) * ((-2 * Real.pi * ξ : ℝ) : ℂ) ^ 2 / 2) := hchar
    _ = (Real.exp (-2 * Real.pi ^ 2 * b ^ 2 * ξ ^ 2) : ℂ) := by
      rw [Complex.ofReal_exp]
      congr 1
      change _ - ((b ^ 2 : ℝ) : ℂ) * _ / 2 = _
      push_cast
      ring

theorem density_decay {b : ℝ} (hb : 0 < b) :
    (density b : ℝ → ℂ) =O[cocompact ℝ] (fun x : ℝ => |x| ^ (-(2 : ℝ))) := by
  have ha : 0 < (((1 / (2 * b ^ 2) : ℝ) : ℂ)).re := by
    simp only [Complex.ofReal_re]
    positivity
  have h := (isLittleO_exp_neg_mul_sq_cocompact ha (-2)).isBigO.const_mul_left
    (((Real.sqrt (2 * Real.pi) * b : ℝ) : ℂ)⁻¹)
  change (fun x : ℝ => density b x) =O[cocompact ℝ] (fun x : ℝ => |x| ^ (-(2 : ℝ)))
  simpa only [density_eq_exp] using h

/-- Absolute convergence is uniform on every compact real interval. -/
theorem density_locally_summable {b : ℝ} (hb : 0 < b) :
    ∀ K : Compacts ℝ,
      Summable (fun n : ℤ =>
        ‖((density b).comp (ContinuousMap.addRight n)).restrict K‖) := by
  intro K
  exact summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num : 1 < (2 : ℝ)))
    ((isBigO_norm_restrict_cocompact (density b) (by norm_num : 0 < (2 : ℝ))
      (density_decay hb) K).comp_tendsto Int.tendsto_coe_cofinite)

theorem density_translates_summable {b : ℝ} (hb : 0 < b) :
    Summable (fun n : ℤ => (density b).comp (ContinuousMap.addRight n)) :=
  ContinuousMap.summable_of_locally_summable_norm (density_locally_summable hb)

theorem density_pointwise_summable {b : ℝ} (hb : 0 < b) (x : ℝ) :
    Summable (fun n : ℤ => density b (x + n)) := by
  exact (ContinuousMap.hasSum_apply (density_translates_summable hb).hasSum x).summable

/-- The periodized density, as a continuous function on the unit circle. -/
def kernel (b : ℝ) : C(UnitAddCircle, ℂ) :=
  ⟨((density b).periodic_tsum_comp_add_zsmul 1).lift,
    continuous_coinduced_dom.mpr (map_continuous _)⟩

theorem kernel_coe {b : ℝ} (hb : 0 < b) (x : ℝ) :
    kernel b (x : UnitAddCircle) = ∑' n : ℤ, density b (x + n) := by
  change ((density b).periodic_tsum_comp_add_zsmul 1).lift (x : UnitAddCircle) = _
  rw [Function.Periodic.lift_coe]
  simpa only [zsmul_one, ContinuousMap.comp_apply, ContinuousMap.coe_addRight] using
    (ContinuousMap.hasSum_apply (density_translates_summable hb).hasSum x).tsum_eq.symm

/-- Fourier coefficients of the actual image sum, with probability Haar measure. -/
theorem kernel_fourierCoeff {b : ℝ} (hb : 0 < b) (n : ℤ) :
    fourierCoeff (kernel b) n =
      (Real.exp (-2 * Real.pi ^ 2 * b ^ 2 * (n : ℝ) ^ 2) : ℂ) := by
  exact (Real.fourierCoeff_tsum_comp_add (density_locally_summable hb) n).trans
    (density_fourier hb n)

theorem kernel_integral {b : ℝ} (hb : 0 < b) :
    (∫ x : UnitAddCircle, kernel b x ∂AddCircle.haarAddCircle) = 1 := by
  have h := kernel_fourierCoeff hb 0
  simpa [fourierCoeff] using h

theorem kernel_coe_real {b : ℝ} (hb : 0 < b) (x : ℝ) :
    kernel b (x : UnitAddCircle) =
      ((∑' n : ℤ, changeKernel b (x + n) : ℝ) : ℂ) := by
  rw [kernel_coe hb, Complex.ofReal_tsum]
  rfl

theorem changeKernel_translates_summable {b : ℝ} (hb : 0 < b) (x : ℝ) :
    Summable (fun n : ℤ => changeKernel b (x + n)) :=
  Complex.summable_ofReal.mp (density_pointwise_summable hb x)

theorem kernel_re_pos {b : ℝ} (hb : 0 < b) (x : UnitAddCircle) :
    0 < (kernel b x).re := by
  induction x using QuotientAddGroup.induction_on with
  | H x =>
    rw [kernel_coe_real hb, Complex.ofReal_re]
    have hnonneg (n : ℤ) : 0 ≤ changeKernel b (x + n) :=
      (density_pos hb (x + n)).le
    exact lt_of_lt_of_le (density_pos hb (x + (0 : ℤ)))
      ((changeKernel_translates_summable hb x).le_tsum 0 (fun n _ => hnonneg n))

theorem kernel_im_eq_zero {b : ℝ} (hb : 0 < b) (x : UnitAddCircle) :
    (kernel b x).im = 0 := by
  induction x using QuotientAddGroup.induction_on with
  | H x => rw [kernel_coe_real hb, Complex.ofReal_im]

theorem kernel_even {b : ℝ} (hb : 0 < b) (x : UnitAddCircle) :
    kernel b (-x) = kernel b x := by
  induction x using QuotientAddGroup.induction_on with
  | H x =>
    change kernel b ((-x : ℝ) : UnitAddCircle) = kernel b (x : UnitAddCircle)
    rw [kernel_coe hb, kernel_coe hb]
    calc
      (∑' n : ℤ, density b (-x + n)) = ∑' n : ℤ, density b (-x + (-n : ℤ)) :=
        (Equiv.neg ℤ).tsum_eq _ |>.symm
      _ = ∑' n : ℤ, density b (x + n) := by
        apply tsum_congr
        intro n
        push_cast
        rw [← neg_add, density_even]

end GeneratedFoundations.Spectral.PeriodicGaussian

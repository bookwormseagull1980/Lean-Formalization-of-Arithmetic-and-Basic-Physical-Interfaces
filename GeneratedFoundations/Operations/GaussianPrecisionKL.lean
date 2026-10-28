module

public import GeneratedFoundations.Operations.ScalarPrecisionComparison
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Moments.Variance
public import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Relative entropy of the Gaussian precision comparison

The law at precision `p > 0` is the centred real Gaussian of variance
`1 / p`. The likelihood ratio is calculated from its actual density and
Radon--Nikodym derivative. Integrating it gives half the compensated
precision comparison. Thus a real coordinate contributes a factor `1/2`;
doubling the number of real coordinates is a separate multiplicity.
-/

@[expose] public section
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace GeneratedFoundations.Operations.GaussianPrecisionKL

def variance (p : ℝ) : ℝ≥0 := Real.toNNReal p⁻¹

theorem variance_coe {p : ℝ} (hp : 0 < p) : (variance p : ℝ) = p⁻¹ :=
  Real.coe_toNNReal _ (inv_pos.mpr hp).le

def law (p : ℝ) : Measure ℝ := gaussianReal 0 (variance p)

instance (p : ℝ) : IsProbabilityMeasure (law p) := by
  unfold law
  infer_instance

theorem variance_ne_zero {p : ℝ} (hp : 0 < p) : variance p ≠ 0 := by
  intro h
  have hz := congrArg (fun v : ℝ≥0 => (v : ℝ)) h
  rw [variance_coe hp] at hz
  exact (inv_ne_zero hp.ne') hz

theorem law_absolutelyContinuous {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    law p ≪ law q :=
  (gaussianReal_absolutelyContinuous 0 (variance_ne_zero hp)).trans
    (gaussianReal_absolutelyContinuous' 0 (variance_ne_zero hq))

theorem density_log {p : ℝ} (hp : 0 < p) (x : ℝ) :
    Real.log (gaussianPDFReal 0 (variance p) x) =
      (Real.log p - Real.log (2 * Real.pi)) / 2 - p * x ^ 2 / 2 := by
  have hv : (0 : ℝ) < (variance p : ℝ) := by rw [variance_coe hp]; positivity
  have hc : 0 < 2 * Real.pi * (variance p : ℝ) := by positivity
  rw [gaussianPDFReal, Real.log_mul (inv_ne_zero (Real.sqrt_pos.mpr hc).ne')
      (Real.exp_pos _).ne', Real.log_inv, Real.log_sqrt hc.le, Real.log_exp]
  rw [Real.log_mul (by positivity : (2 * Real.pi : ℝ) ≠ 0) (ne_of_gt hv)]
  rw [variance_coe hp]
  change -((Real.log (2 * Real.pi) + Real.log p⁻¹) / 2) +
    (-(x - 0) ^ 2 / (2 * p⁻¹)) = _
  rw [Real.log_inv]
  field_simp
  ring

theorem density_log_ratio {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (x : ℝ) :
    Real.log (gaussianPDFReal 0 (variance p) x / gaussianPDFReal 0 (variance q) x) =
      Real.log (p / q) / 2 + (q - p) * x ^ 2 / 2 := by
  rw [Real.log_div (gaussianPDFReal_pos _ _ _ (variance_ne_zero hp)).ne'
      (gaussianPDFReal_pos _ _ _ (variance_ne_zero hq)).ne',
    density_log hp, density_log hq, Real.log_div hp.ne' hq.ne']
  ring

theorem llr_eq {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    llr (law p) (law q) =ᵐ[law p]
      fun x => Real.log (p / q) / 2 + (q - p) * x ^ 2 / 2 := by
  have hpv := gaussianReal_absolutelyContinuous 0 (variance_ne_zero hp)
  have hqv := gaussianReal_absolutelyContinuous 0 (variance_ne_zero hq)
  have hratio := (law_absolutelyContinuous hp hq).ae_le (Measure.rnDeriv_eq_div hpv hqv)
  have hpd := hpv.ae_le (rnDeriv_gaussianReal 0 (variance p))
  have hqd := hpv.ae_le (rnDeriv_gaussianReal 0 (variance q))
  filter_upwards [hratio, hpd, hqd] with x hx hpx hqx
  change Real.log ((law p).rnDeriv (law q) x).toReal = _
  change (law p).rnDeriv (law q) x =
    (law p).rnDeriv volume x / (law q).rnDeriv volume x at hx
  change (law p).rnDeriv volume x = gaussianPDF 0 (variance p) x at hpx
  change (law q).rnDeriv volume x = gaussianPDF 0 (variance q) x at hqx
  rw [hx, hpx, hqx, ENNReal.toReal_div]
  simp only [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _)]
  exact density_log_ratio hp hq x

theorem square_integrable (p : ℝ) : Integrable (fun x : ℝ => x ^ 2) (law p) :=
  (memLp_id_gaussianReal' (μ := 0) (v := variance p) 2 (by norm_num)).integrable_sq

theorem square_integral {p : ℝ} (hp : 0 < p) : (∫ x : ℝ, x ^ 2 ∂law p) = p⁻¹ := by
  have h := variance_eq_sub
    (memLp_id_gaussianReal' (μ := 0) (v := variance p) 2 (by norm_num))
  simpa [law, variance_coe hp] using h.symm

theorem llr_integrable {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    Integrable (llr (law p) (law q)) (law p) := by
  apply Integrable.congr
    ((integrable_const (Real.log (p / q) / 2)).add
      (((square_integrable p).const_mul (q - p)).div_const 2))
  exact (llr_eq hp hq).symm

theorem integral_llr {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    (∫ x, llr (law p) (law q) x ∂law p) =
      (q / p - 1 - Real.log (q / p)) / 2 := by
  rw [integral_congr_ae (llr_eq hp hq),
    integral_add (integrable_const _)
      (((square_integrable p).const_mul (q - p)).div_const 2),
    integral_const, integral_div, integral_const_mul, square_integral hp]
  simp only [probReal_univ, one_smul]
  rw [Real.log_div hp.ne' hq.ne', Real.log_div hq.ne' hp.ne']
  field_simp
  ring

theorem klDiv_eq {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    InformationTheory.klDiv (law p) (law q) =
      ENNReal.ofReal ((q / p - 1 - Real.log (q / p)) / 2) := by
  rw [InformationTheory.klDiv_of_ac_of_integrable
    (law_absolutelyContinuous hp hq) (llr_integrable hp hq), integral_llr hp hq]
  simp

theorem klDiv_toReal {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    (InformationTheory.klDiv (law p) (law q)).toReal =
      (q / p - 1 - Real.log (q / p)) / 2 := by
  rw [InformationTheory.toReal_klDiv_of_measure_eq
    (law_absolutelyContinuous hp hq) (by simp)]
  exact integral_llr hp hq

/-- Precision variation is evaluated on the same Gaussian law, before any
finite-window averaging or choice of an endpoint normalization. -/
theorem varied_precision {p k z : ℝ} (hp : 0 < p) (hq : 0 < p + z * k) :
    (InformationTheory.klDiv (law p) (law (p + z * k))).toReal =
      ScalarPrecisionComparison.cost (k / p) z / 2 := by
  rw [klDiv_toReal hp hq, ScalarPrecisionComparison.relative_precision hp.ne']
  unfold ScalarPrecisionComparison.cost
  ring

end GeneratedFoundations.Operations.GaussianPrecisionKL

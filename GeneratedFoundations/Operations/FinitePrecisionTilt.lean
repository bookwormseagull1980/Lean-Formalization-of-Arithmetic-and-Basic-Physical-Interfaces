module

public import GeneratedFoundations.Operations.FinitePrecisionGaussian
public import Mathlib.Probability.Independence.Integration

/-!
# The Gaussian partition of a common quadratic vertex

The partition is the integral of the exponential of the complete score in
one joint Gaussian state. Its product formula follows from the already
proved joint law; no independence assumption is supplied. Precision changes
by the actual vertex coefficient, including any Gaussian filter in that
coefficient. The same varied precision determines the entire Gaussian law
uniquely, and the logarithmic partition derivatives recover its score moments.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace GeneratedFoundations.Operations.FinitePrecisionTilt

open GaussianPrecisionKL (variance)
open FinitePrecisionGaussian (Space score)

/-- Exact density identity, also valid for negative coupling while the
resulting precision remains positive. -/
theorem scalar_density_tilt {p q z : ℝ} (hp : 0 < p) (hz : 0 < p + z * q) (x : ℝ) :
    gaussianPDFReal 0 (variance p) x * Real.exp (-z * (q / 2 * x ^ 2)) =
      Real.exp (Real.log (p / (p + z * q)) / 2) *
        gaussianPDFReal 0 (variance (p + z * q)) x := by
  have hpv := gaussianPDFReal_pos 0 (variance p) x (GaussianPrecisionKL.variance_ne_zero hp)
  have hzv := gaussianPDFReal_pos 0 (variance (p + z * q)) x
    (GaussianPrecisionKL.variance_ne_zero hz)
  conv_lhs => rw [← Real.exp_log hpv]
  conv_rhs => rw [← Real.exp_log hzv]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [GaussianPrecisionKL.density_log hp, GaussianPrecisionKL.density_log hz,
    Real.log_div hp.ne' hz.ne']
  ring

theorem scalar_partition {p q z : ℝ} (hp : 0 < p) (hz : 0 < p + z * q) :
    (∫ x : ℝ, Real.exp (-z * (q / 2 * x ^ 2)) ∂GaussianPrecisionKL.law p) =
      Real.exp (Real.log (p / (p + z * q)) / 2) := by
  unfold GaussianPrecisionKL.law
  rw [integral_gaussianReal_eq_integral_smul (GaussianPrecisionKL.variance_ne_zero hp)]
  simp only [smul_eq_mul, scalar_density_tilt hp hz]
  rw [integral_const_mul, integral_gaussianPDFReal_eq_one 0
    (GaussianPrecisionKL.variance_ne_zero hz), mul_one]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def variedPrecision (p q : ι → ℝ) (z : ℝ) : ι → ℝ := fun i => p i + z * q i

def partition (p q : ι → ℝ) (z : ℝ) : ℝ :=
  ∫ x : Space ι, Real.exp (-z * score q x) ∂FinitePrecisionGaussian.law p

def logPartition (p q : ι → ℝ) (z : ℝ) : ℝ :=
  -(∑ i, Real.log (1 + z * (q i / p i))) / 2

omit [Fintype ι] [DecidableEq ι] in
theorem relative_pos {p q : ι → ℝ} {z : ℝ} (hp : ∀ i, 0 < p i)
    (hz : ∀ i, 0 < variedPrecision p q z i) (i : ι) :
    0 < 1 + z * (q i / p i) := by
  rw [← ScalarPrecisionComparison.relative_precision (hp i).ne']
  exact div_pos (hz i) (hp i)

/-- The complete score is exponentiated before integration. -/
theorem partition_eq_exp {p q : ι → ℝ} {z : ℝ} (hp : ∀ i, 0 < p i)
    (hz : ∀ i, 0 < variedPrecision p q z i) :
    partition p q z = Real.exp (logPartition p q z) := by
  have he (x : Space ι) : Real.exp (-z * score q x) =
      ∏ i, Real.exp (-z * (q i / 2 * (x i) ^ 2)) := by
    rw [score, Finset.mul_sum, Real.exp_sum]
    rfl
  simp_rw [partition, he]
  rw [(FinitePrecisionGaussian.coordinates_independent hp).integral_fun_prod_comp
    (f := fun i t => Real.exp (-z * (q i / 2 * t ^ 2)))
    (fun i => by fun_prop) (fun i => by fun_prop)]
  have hm (i : ι) :
      (∫ x : Space ι, Real.exp (-z * (q i / 2 * (x i) ^ 2))
        ∂FinitePrecisionGaussian.law p) =
        Real.exp (Real.log (p i / (p i + z * q i)) / 2) := by
    calc
      _ = ∫ y : ℝ, Real.exp (-z * (q i / 2 * y ^ 2))
          ∂(FinitePrecisionGaussian.law p).map (fun x : Space ι => x i) :=
        (integral_map (by fun_prop) (by fun_prop)).symm
      _ = _ := by
        rw [(FinitePrecisionGaussian.coordinate_marginal hp i).map_eq]
        exact scalar_partition (hp i) (hz i)
  simp_rw [hm]
  rw [← Real.exp_sum]
  congr 1
  unfold logPartition
  rw [← Finset.sum_div]
  congr 1
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hrel := ScalarPrecisionComparison.relative_precision (hp i).ne' (q i) z
  have hzi : p i + z * q i ≠ 0 := (hz i).ne'
  rw [← hrel, Real.log_div (hp i).ne' hzi, Real.log_div hzi (hp i).ne']
  ring

theorem partition_pos {p q : ι → ℝ} {z : ℝ} (hp : ∀ i, 0 < p i)
    (hz : ∀ i, 0 < variedPrecision p q z i) : 0 < partition p q z := by
  rw [partition_eq_exp hp hz]
  exact Real.exp_pos _

theorem log_partition {p q : ι → ℝ} {z : ℝ} (hp : ∀ i, 0 < p i)
    (hz : ∀ i, 0 < variedPrecision p q z i) :
    Real.log (partition p q z) = logPartition p q z := by
  rw [partition_eq_exp hp hz, Real.log_exp]

def mean (p q : ι → ℝ) (z : ℝ) : ℝ := ∑ i, q i / (2 * variedPrecision p q z i)

def susceptibility (p q : ι → ℝ) (z : ℝ) : ℝ :=
  ∑ i, (q i) ^ 2 / (2 * (variedPrecision p q z i) ^ 2)

theorem score_mean {p q : ι → ℝ} {z : ℝ}
    (hz : ∀ i, 0 < variedPrecision p q z i) :
    (∫ x, score q x ∂FinitePrecisionGaussian.law (variedPrecision p q z)) = mean p q z :=
  FinitePrecisionGaussian.score_mean hz q

theorem score_variance {p q : ι → ℝ} {z : ℝ}
    (hz : ∀ i, 0 < variedPrecision p q z i) :
    Var[score q; FinitePrecisionGaussian.law (variedPrecision p q z)] =
      susceptibility p q z := FinitePrecisionGaussian.score_variance hz q

omit [DecidableEq ι] in
theorem logPartition_hasDerivAt {p q : ι → ℝ} {z : ℝ} (hp : ∀ i, 0 < p i)
    (hz : ∀ i, 0 < variedPrecision p q z i) :
    HasDerivAt (logPartition p q) (-mean p q z) z := by
  have hd := ((HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    (((hasDerivAt_id z).mul_const (q i / p i)).const_add 1).log
      (relative_pos hp hz i).ne')).neg).div_const 2
  convert! hd using 1
  · funext t
    simp [logPartition, Finset.sum_apply]
  · unfold mean variedPrecision
    simp only [id_eq, one_mul]
    rw [neg_div, Finset.sum_div]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    field_simp [(hp i).ne', (hz i).ne']

omit [DecidableEq ι] in
theorem negativeMean_hasDerivAt {p q : ι → ℝ} {z : ℝ}
    (hz : ∀ i, 0 < variedPrecision p q z i) :
    HasDerivAt (fun t => -mean p q t) (susceptibility p q z) z := by
  have hd := (HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    ((hasDerivAt_const z (q i)).div
      ((((hasDerivAt_id z).mul_const (q i)).const_add (p i)).const_mul 2)
      (mul_ne_zero (by norm_num) (hz i).ne')))).neg
  convert! hd using 1
  · funext t
    simp [mean, variedPrecision, Finset.sum_apply]
  · unfold susceptibility variedPrecision
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [id_eq, one_mul, zero_mul, zero_sub]
    field_simp [(hz i).ne']

/-- At the varied precision the comparison still includes every centred
Gaussian competitor, including arbitrary off-diagonal covariances. -/
theorem varied_law_existsUnique {p q : ι → ℝ} {z : ℝ}
    (hz : ∀ i, 0 < variedPrecision p q z i) :
    ∃! ν : Measure (Space ι), IsGaussian ν ∧ (∫ x, x ∂ν) = 0 ∧
      FinitePrecisionGaussian.precisionMatrix (variedPrecision p q z) *
        FinitePrecisionGaussian.coordinateCovariance ν = 1 :=
  FinitePrecisionGaussian.law_existsUnique hz

end GeneratedFoundations.Operations.FinitePrecisionTilt

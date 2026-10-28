module

public import GeneratedFoundations.Operations.FinitePrecisionTilt

/-!
# Exact Gaussian response along a nonlinear precision path

The partition is taken in one fixed reference Gaussian law. Its exponent
is the difference of the complete quadratic actions. No new normalization
is chosen at each parameter value. Differentiation therefore includes both
the fluctuation of the first precision derivative and the expectation of
the second precision derivative. A positive score variance alone does not
fix the sign of a geometric response.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace GeneratedFoundations.Operations.FinitePrecisionPath

open FinitePrecisionGaussian (Space score)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def partition (p : ℝ → ι → ℝ) (r c : ℝ) : ℝ :=
  ∫ x : Space ι, Real.exp (-(score (p c) x - score (p r) x))
    ∂FinitePrecisionGaussian.law (p r)

def logPartition (p : ℝ → ι → ℝ) (r c : ℝ) : ℝ :=
  (∑ i, (Real.log (p r i) - Real.log (p c i))) / 2

def force (p v : ℝ → ι → ℝ) (c : ℝ) : ℝ :=
  ∑ i, v c i / (2 * p c i)

def curvature (p v a : ℝ → ι → ℝ) (c : ℝ) : ℝ :=
  ∑ i, (a c i / p c i - (v c i / p c i) ^ 2) / 2

theorem partition_eq_exp {p : ℝ → ι → ℝ} {r c : ℝ}
    (hr : ∀ i, 0 < p r i) (hc : ∀ i, 0 < p c i) :
    partition p r c = Real.exp (logPartition p r c) := by
  have hprec (i : ι) :
      FinitePrecisionTilt.variedPrecision (p r) (fun j => p c j - p r j) 1 i = p c i := by
    simp [FinitePrecisionTilt.variedPrecision]
  have hscore (x : Space ι) :
      score (fun i => p c i - p r i) x = score (p c) x - score (p r) x := by
    simp only [score, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    unfold GaussianPrecisionMoments.score
    ring
  have he : partition p r c =
      FinitePrecisionTilt.partition (p r) (fun i => p c i - p r i) 1 := by
    simp only [partition, FinitePrecisionTilt.partition, hscore, neg_mul, one_mul]
  rw [he, FinitePrecisionTilt.partition_eq_exp hr (fun i => by rw [hprec]; exact hc i)]
  congr 1
  unfold FinitePrecisionTilt.logPartition logPartition
  rw [← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hrel : 1 + 1 * ((p c i - p r i) / p r i) = p c i / p r i := by
    field_simp [(hr i).ne']
    ring
  rw [hrel, Real.log_div (hc i).ne' (hr i).ne']
  ring

theorem partition_pos {p : ℝ → ι → ℝ} {r c : ℝ}
    (hr : ∀ i, 0 < p r i) (hc : ∀ i, 0 < p c i) : 0 < partition p r c := by
  rw [partition_eq_exp hr hc]
  exact Real.exp_pos _

theorem log_partition {p : ℝ → ι → ℝ} {r c : ℝ}
    (hr : ∀ i, 0 < p r i) (hc : ∀ i, 0 < p c i) :
    Real.log (partition p r c) = logPartition p r c := by
  rw [partition_eq_exp hr hc, Real.log_exp]

omit [DecidableEq ι] in
theorem negative_logPartition_eq {p : ℝ → ι → ℝ} {r c : ℝ}
    (hr : ∀ i, 0 < p r i) (hc : ∀ i, 0 < p c i) :
    -logPartition p r c = ∑ i, Real.log (p c i / p r i) / 2 := by
  unfold logPartition
  rw [← neg_div, ← Finset.sum_neg_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [Real.log_div (hc i).ne' (hr i).ne']
  ring

omit [DecidableEq ι] in
theorem logPartition_hasDerivAt {p v : ℝ → ι → ℝ} {r c : ℝ}
    (hc : ∀ i, 0 < p c i) (hv : ∀ i, HasDerivAt (fun t => p t i) (v c i) c) :
    HasDerivAt (logPartition p r) (-force p v c) c := by
  have hd := (HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    (hasDerivAt_const c (Real.log (p r i))).sub ((hv i).log (hc i).ne'))).div_const 2
  convert! hd using 1
  · funext t
    simp [logPartition, Finset.sum_apply]
  · simp only [force, zero_sub, Finset.sum_neg_distrib, neg_div, Finset.sum_div]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

omit [DecidableEq ι] in
theorem force_hasDerivAt {p v a : ℝ → ι → ℝ} {c : ℝ}
    (hc : ∀ i, 0 < p c i)
    (hv : ∀ i, HasDerivAt (fun t => p t i) (v c i) c)
    (ha : ∀ i, HasDerivAt (fun t => v t i) (a c i) c) :
    HasDerivAt (force p v) (curvature p v a c) c := by
  have hd := HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    (ha i).div ((hv i).const_mul 2) (mul_ne_zero (by norm_num) (hc i).ne'))
  convert! hd using 1
  · funext t
    simp [force, Finset.sum_apply]
  · unfold curvature
    apply Finset.sum_congr rfl
    intro i _
    field_simp [(hc i).ne']

/-- The force is the expectation of the actual first derivative of the
quadratic action in the same varied state. -/
theorem force_eq_mean {p v : ℝ → ι → ℝ} {c : ℝ}
    (hc : ∀ i, 0 < p c i) :
    force p v c = ∫ x, score (v c) x ∂FinitePrecisionGaussian.law (p c) :=
  (FinitePrecisionGaussian.score_mean hc _).symm

/-- In a nonlinear geometric path the direct second derivative remains.
Neither term is discarded before their common difference is evaluated. -/
theorem curvature_eq_mean_sub_variance {p v a : ℝ → ι → ℝ} {c : ℝ}
    (hc : ∀ i, 0 < p c i) :
    curvature p v a c =
      (∫ x, score (a c) x ∂FinitePrecisionGaussian.law (p c)) -
        Var[score (v c); FinitePrecisionGaussian.law (p c)] := by
  rw [FinitePrecisionGaussian.score_mean hc _, FinitePrecisionGaussian.score_variance hc _,
    ← Finset.sum_sub_distrib]
  unfold curvature
  apply Finset.sum_congr rfl
  intro i _
  field_simp [(hc i).ne']

/-- The entire centred Gaussian competitor class is retained at every
point. No diagonal-covariance restriction is imposed on competitors. -/
theorem law_existsUnique {p : ℝ → ι → ℝ} {c : ℝ} (hc : ∀ i, 0 < p c i) :
    ∃! ν : Measure (Space ι), IsGaussian ν ∧ (∫ x, x ∂ν) = 0 ∧
      FinitePrecisionGaussian.precisionMatrix (p c) *
        FinitePrecisionGaussian.coordinateCovariance ν = 1 :=
  FinitePrecisionGaussian.law_existsUnique hc

end GeneratedFoundations.Operations.FinitePrecisionPath

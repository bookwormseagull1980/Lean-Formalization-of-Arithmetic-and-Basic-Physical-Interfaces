module

public import GeneratedFoundations.Operations.GaussianPrecisionMoments
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!
# The joint Gaussian state of a finite positive precision

The law is formed on the entire real coefficient space. Its precision is
the diagonalization of the original positive quadratic form; this does not
assume that an arbitrary comparison state has diagonal covariance.
Among centred Gaussian laws, the complete precision equation determines
the law uniquely. Coordinate independence is then a theorem about this
joint law. In particular, the variance of a diagonal quadratic vertex is
calculated before any averaging over spectral labels.

This is a quadratic-state construction. It does not evaluate the measure
of an action with additional cubic or quartic interactions.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace

namespace GeneratedFoundations.Operations.FinitePrecisionGaussian

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev Space (ι : Type*) [Fintype ι] := EuclideanSpace ℝ ι

def precisionMatrix (p : ι → ℝ) : Matrix ι ι ℝ := Matrix.diagonal p

def covarianceMatrix (p : ι → ℝ) : Matrix ι ι ℝ :=
  Matrix.diagonal fun i => (p i)⁻¹

def law (p : ι → ℝ) : Measure (Space ι) :=
  multivariateGaussian 0 (covarianceMatrix p)

instance (p : ι → ℝ) : IsGaussian (law p) := by
  unfold law
  infer_instance

instance (p : ι → ℝ) : IsProbabilityMeasure (law p) := inferInstance

omit [Fintype ι] in
theorem covariance_posDef {p : ι → ℝ} (hp : ∀ i, 0 < p i) :
    (covarianceMatrix p).PosDef := by
  rw [covarianceMatrix, Matrix.posDef_diagonal_iff]
  exact fun i => inv_pos.mpr (hp i)

omit [Fintype ι] in
theorem covariance_posSemidef {p : ι → ℝ} (hp : ∀ i, 0 < p i) :
    (covarianceMatrix p).PosSemidef := (covariance_posDef hp).posSemidef

theorem precision_mul_covariance {p : ι → ℝ} (hp : ∀ i, 0 < p i) :
    precisionMatrix p * covarianceMatrix p = 1 := by
  unfold precisionMatrix covarianceMatrix
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_inv_cancel₀ (hp i).ne'

theorem covariance_mul_precision {p : ι → ℝ} (hp : ∀ i, 0 < p i) :
    covarianceMatrix p * precisionMatrix p = 1 := by
  unfold precisionMatrix covarianceMatrix
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact inv_mul_cancel₀ (hp i).ne'

theorem covariance_unique {p : ι → ℝ} (hp : ∀ i, 0 < p i)
    (C : Matrix ι ι ℝ) (hC : precisionMatrix p * C = 1) : C = covarianceMatrix p := by
  calc
    C = (covarianceMatrix p * precisionMatrix p) * C := by
      rw [covariance_mul_precision hp, one_mul]
    _ = covarianceMatrix p := by rw [Matrix.mul_assoc, hC, mul_one]

@[simp] theorem mean_zero (p : ι → ℝ) : (∫ x, x ∂law p) = 0 :=
  integral_id_multivariateGaussian

def coordinateCovariance (ν : Measure (Space ι)) : Matrix ι ι ℝ :=
  fun i j => cov[fun x => x i, fun x => x j; ν]

theorem coordinateCovariance_eq {p : ι → ℝ} (hp : ∀ i, 0 < p i) :
    coordinateCovariance (law p) = covarianceMatrix p := by
  ext i j
  exact covariance_eval_multivariateGaussian (covariance_posSemidef hp) i j

/-- The comparison is with every centred Gaussian law whose full covariance
satisfies the original precision equation, not only product competitors. -/
theorem law_unique {p : ι → ℝ} (hp : ∀ i, 0 < p i)
    (ν : Measure (Space ι)) [IsGaussian ν]
    (hmean : (∫ x, x ∂ν) = 0)
    (hprecision : precisionMatrix p * coordinateCovariance ν = 1) : ν = law p := by
  have hC := covariance_unique hp (coordinateCovariance ν) hprecision
  apply IsGaussian.ext (hmean.trans (mean_zero p).symm)
  rw [← ContinuousLinearMap.toBilinForm_inj]
  refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun ι ℝ).toBasis fun i j => ?_
  rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply,
    covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
    covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id]
  change cov[fun x : Space ι => inner ℝ (EuclideanSpace.basisFun ι ℝ i) x,
    fun x => inner ℝ (EuclideanSpace.basisFun ι ℝ j) x; ν] =
      cov[fun x : Space ι => inner ℝ (EuclideanSpace.basisFun ι ℝ i) x,
        fun x => inner ℝ (EuclideanSpace.basisFun ι ℝ j) x; law p]
  simpa only [EuclideanSpace.basisFun_inner, coordinateCovariance] using
    (congrFun (congrFun hC i) j).trans
      (congrFun (congrFun (coordinateCovariance_eq hp) i) j).symm

theorem law_existsUnique {p : ι → ℝ} (hp : ∀ i, 0 < p i) :
    ∃! ν : Measure (Space ι), IsGaussian ν ∧ (∫ x, x ∂ν) = 0 ∧
      precisionMatrix p * coordinateCovariance ν = 1 := by
  refine ⟨law p, ⟨inferInstance, mean_zero p, ?_⟩, ?_⟩
  · rw [coordinateCovariance_eq hp]
    exact precision_mul_covariance hp
  · intro ν hν
    let : IsGaussian ν := hν.1
    exact law_unique hp ν hν.2.1 hν.2.2

/-- Each marginal is the already constructed real precision Gaussian. -/
theorem coordinate_marginal {p : ι → ℝ} (hp : ∀ i, 0 < p i) (i : ι) :
    MeasurePreserving (fun x : Space ι => x i) (law p) (GaussianPrecisionKL.law (p i)) := by
  have h := measurePreserving_eval_multivariateGaussian (μ := 0)
    (covariance_posSemidef hp) (i := i)
  simpa [law, covarianceMatrix, GaussianPrecisionKL.law, GaussianPrecisionKL.variance] using h

theorem coordinates_independent {p : ι → ℝ} (hp : ∀ i, 0 < p i) :
    iIndepFun (fun i (x : Space ι) => x i) (law p) := by
  have hG : HasGaussianLaw (fun x : Space ι => fun i => x i) (law p) :=
    IsGaussian.hasGaussianLaw_id.map_equiv
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ))
  apply hG.iIndepFun_of_covariance_eq_zero
  intro i j hij
  change coordinateCovariance (law p) i j = 0
  rw [coordinateCovariance_eq hp]
  simp [covarianceMatrix, hij]

def score (q : ι → ℝ) (x : Space ι) : ℝ :=
  ∑ i, GaussianPrecisionMoments.score (q i) (x i)

theorem coordinate_score_memLp {p : ι → ℝ} (hp : ∀ i, 0 < p i)
    (q : ι → ℝ) (i : ι) :
    MemLp (fun x : Space ι => GaussianPrecisionMoments.score (q i) (x i)) 2 (law p) := by
  exact ((GaussianPrecisionMoments.square_memLp_two (p i)).const_mul (q i / 2)).comp_measurePreserving
    (coordinate_marginal hp i)

theorem score_mean {p : ι → ℝ} (hp : ∀ i, 0 < p i) (q : ι → ℝ) :
    (∫ x, score q x ∂law p) = ∑ i, q i / (2 * p i) := by
  change (∫ x : Space ι, ∑ i, GaussianPrecisionMoments.score (q i) (x i) ∂law p) = _
  rw [integral_finsetSum _ (fun i _ => (coordinate_score_memLp hp q i).integrable
    (by norm_num))]
  apply Finset.sum_congr rfl
  intro i _
  calc
    (∫ x : Space ι, GaussianPrecisionMoments.score (q i) (x i) ∂law p) =
        ∫ y : ℝ, GaussianPrecisionMoments.score (q i) y
          ∂(law p).map (fun x : Space ι => x i) :=
      (integral_map (by fun_prop) (by unfold GaussianPrecisionMoments.score; fun_prop)).symm
    _ = q i / (2 * p i) := by
      rw [(coordinate_marginal hp i).map_eq]
      exact GaussianPrecisionMoments.score_mean (hp i) _

/-- All cross-coordinate score covariances vanish as a consequence of the
same joint Gaussian law. No independent-input hypothesis is supplied. -/
theorem coordinate_score_covariance_zero {p : ι → ℝ} (hp : ∀ i, 0 < p i)
    (q r : ι → ℝ) {i j : ι} (hij : i ≠ j) :
    cov[fun x : Space ι => GaussianPrecisionMoments.score (q i) (x i),
      fun x => GaussianPrecisionMoments.score (r j) (x j); law p] = 0 := by
  exact (((coordinates_independent hp).indepFun hij).comp
    (φ := GaussianPrecisionMoments.score (q i))
    (ψ := GaussianPrecisionMoments.score (r j))
    (by unfold GaussianPrecisionMoments.score; fun_prop)
    (by unfold GaussianPrecisionMoments.score; fun_prop)).covariance_eq_zero
      (coordinate_score_memLp hp q i) (coordinate_score_memLp hp r j)

theorem score_variance {p : ι → ℝ} (hp : ∀ i, 0 < p i) (q : ι → ℝ) :
    Var[score q; law p] = ∑ i, (q i) ^ 2 / (2 * (p i) ^ 2) := by
  have hvar := IndepFun.variance_sum (s := Finset.univ)
    (fun i _ => coordinate_score_memLp hp q i)
    (fun i _ j _ hij => ((coordinates_independent hp).indepFun hij).comp
      (φ := GaussianPrecisionMoments.score (q i))
      (ψ := GaussianPrecisionMoments.score (q j))
      (by unfold GaussianPrecisionMoments.score; fun_prop)
      (by unfold GaussianPrecisionMoments.score; fun_prop))
  have hs : Var[score q; law p] =
      ∑ i, Var[fun x : Space ι => GaussianPrecisionMoments.score (q i) (x i); law p] := by
    rw [show score q = ∑ i, fun x : Space ι => GaussianPrecisionMoments.score (q i) (x i) by
      funext x
      simp only [score, Finset.sum_apply]]
    exact hvar
  rw [hs]
  apply Finset.sum_congr rfl
  intro i _
  rw [(coordinate_marginal hp i).variance_fun_comp
    (by unfold GaussianPrecisionMoments.score; fun_prop)]
  exact GaussianPrecisionMoments.score_variance (hp i) _

end GeneratedFoundations.Operations.FinitePrecisionGaussian

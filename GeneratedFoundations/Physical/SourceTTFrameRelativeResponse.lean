module

public import GeneratedFoundations.Physical.SourceTTFrameComparison
public import GeneratedFoundations.Operations.FinitePrecisionPath
public import GeneratedFoundations.Operations.FinitePrecisionEquilibrium

/-!
# Relative response along the actual tensor-frame path

The unit plus polarization varies the three row precisions quadratically.
The reference-state expectation of this complete action difference is kept
in the relative likelihood. Its second vertex cancels the direct term in
the logarithmic partition, leaving the Fisher covariance in the relative
entropy Hessian. The negative logarithmic partition by itself retains the
direct second vertex and is a different response.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace GeneratedFoundations.Physical.SourceTTFrameRelativeResponse

open SourceTTFrameComparison
open Operations
open Operations.FinitePrecisionGaussian (Space score)

/-- The three eigenvalues of the existing affine frame comparison. -/
def pathPrecision (p t : ℝ) : Fin 3 → ℝ :=
  ![p - 4 * t + t ^ 2, p + 4 * t + t ^ 2, p + 2 * t ^ 2]

def pathVelocity (_p t : ℝ) : Fin 3 → ℝ := ![-4 + 2 * t, 4 + 2 * t, 4 * t]

def pathAcceleration (_p _t : ℝ) : Fin 3 → ℝ := ![2, 2, 4]

theorem comparisonPrecision_diagonal (p t : ℝ) :
    comparisonPrecision p (Geometry.SourceAxisTT.ttMatrix 1 0) t =
      Matrix.diagonal (pathPrecision p t) := by
  rw [comparisonPrecision_expansion]
  simp only [secondVertex, vertex_formula]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pathPrecision, Geometry.SourceAxisTT.ttMatrix, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.trace, Fin.sum_univ_three] <;> ring

theorem comparisonPrecision_det (p t : ℝ) :
    Matrix.det (comparisonPrecision p (Geometry.SourceAxisTT.ttMatrix 1 0) t) =
      p ^ 3 + (4 * p ^ 2 - 16 * p) * t ^ 2 +
        (5 * p - 32) * t ^ 4 + 2 * t ^ 6 := by
  rw [comparisonPrecision_diagonal, Matrix.det_diagonal]
  simp [pathPrecision, Fin.prod_univ_three]
  ring

theorem pathPrecision_pos {p : ℝ} (hp : 4 < p) (t : ℝ) (i : Fin 3) :
    0 < pathPrecision p t i := by
  fin_cases i <;> simp [pathPrecision]
  all_goals nlinarith [sq_nonneg t, sq_nonneg (t - 2), sq_nonneg (t + 2)]

@[simp] theorem pathPrecision_zero (p : ℝ) (i : Fin 3) : pathPrecision p 0 i = p := by
  fin_cases i <;> simp [pathPrecision]

theorem pathPrecision_hasDerivAt (p t : ℝ) (i : Fin 3) :
    HasDerivAt (fun s => pathPrecision p s i) (pathVelocity p t i) t := by
  fin_cases i
  · change HasDerivAt (fun s => p - 4 * s + s ^ 2) (-4 + 2 * t) t
    convert! ((hasDerivAt_const t p).sub ((hasDerivAt_id t).const_mul 4)).add
      ((hasDerivAt_id t).pow 2) using 1; dsimp; ring
  · change HasDerivAt (fun s => p + 4 * s + s ^ 2) (4 + 2 * t) t
    convert! ((hasDerivAt_const t p).add ((hasDerivAt_id t).const_mul 4)).add
      ((hasDerivAt_id t).pow 2) using 1; dsimp; ring
  · change HasDerivAt (fun s => p + 2 * s ^ 2) (4 * t) t
    convert! (hasDerivAt_const t p).add (((hasDerivAt_id t).pow 2).const_mul 2)
      using 1; dsimp; ring

theorem pathVelocity_hasDerivAt (p t : ℝ) (i : Fin 3) :
    HasDerivAt (fun s => pathVelocity p s i) (pathAcceleration p t i) t := by
  fin_cases i
  · change HasDerivAt (fun s => -4 + 2 * s) 2 t
    simpa using ((hasDerivAt_id t).const_mul 2).const_add (-4)
  · change HasDerivAt (fun s => 4 + 2 * s) 2 t
    simpa using ((hasDerivAt_id t).const_mul 2).const_add 4
  · change HasDerivAt (fun s => 4 * s) 4 t
    simpa using (hasDerivAt_id t).const_mul 4

def negativeLogPartition (p t : ℝ) : ℝ :=
  -FinitePrecisionPath.logPartition (pathPrecision p) 0 t

theorem negativeLogPartition_eq_original_partition {p : ℝ} (hp : 4 < p) (t : ℝ) :
    negativeLogPartition p t =
      -Real.log (FinitePrecisionPath.partition (pathPrecision p) 0 t) := by
  rw [FinitePrecisionPath.log_partition (pathPrecision_pos hp 0) (pathPrecision_pos hp t)]
  rfl

/-- The complete quadratic-action difference, averaged in the original
reference law. No varied-state expectation is substituted here. -/
def referenceActionMean (p t : ℝ) : ℝ :=
  ∫ x : Space (Fin 3),
    score (fun i => pathPrecision p t i - p) x
      ∂FinitePrecisionGaussian.law (fun _ => p)

theorem referenceActionMean_eq {p : ℝ} (hp : 0 < p) (t : ℝ) :
    referenceActionMean p t = 2 * t ^ 2 / p := by
  rw [referenceActionMean, FinitePrecisionGaussian.score_mean (fun _ => hp)]
  simp [pathPrecision, Fin.sum_univ_three]
  field_simp
  ring

/-- Integrated relative log likelihood of all three original real
coordinates, equivalently their full compensated precision comparison. -/
def relativeResponse (p t : ℝ) : ℝ :=
  referenceActionMean p t - negativeLogPartition p t

def relativeForce (p t : ℝ) : ℝ :=
  4 * t / p - FinitePrecisionPath.force (pathPrecision p) (pathVelocity p) t

theorem negativeLogPartition_eq_logdet {p : ℝ} (hp : 4 < p) (t : ℝ) :
    negativeLogPartition p t =
      Real.log (Matrix.det (comparisonPrecision p (Geometry.SourceAxisTT.ttMatrix 1 0) t) /
        p ^ 3) / 2 := by
  have hp0 : 0 < p := by linarith
  rw [negativeLogPartition, FinitePrecisionPath.negative_logPartition_eq
    (fun i => by simpa using hp0) (pathPrecision_pos hp t), comparisonPrecision_diagonal,
    Matrix.det_diagonal]
  simp only [pathPrecision_zero]
  rw [← Finset.sum_div, ← Real.log_prod (fun i _ =>
    (div_pos (pathPrecision_pos hp t i) hp0).ne')]
  congr 2
  simp [Finset.prod_div_distrib, Fin.prod_univ_three]

theorem relativeResponse_eq_marginal_kl {p : ℝ} (hp : 4 < p) (t : ℝ) :
    relativeResponse p t =
      ∑ i : Fin 3, (InformationTheory.klDiv (GaussianPrecisionKL.law p)
        (GaussianPrecisionKL.law (pathPrecision p t i))).toReal := by
  have hp0 : 0 < p := by linarith
  simp_rw [GaussianPrecisionKL.klDiv_toReal hp0 (pathPrecision_pos hp t _)]
  rw [relativeResponse, referenceActionMean_eq hp0, negativeLogPartition,
    FinitePrecisionPath.negative_logPartition_eq (fun i => by simpa using hp0)
      (pathPrecision_pos hp t)]
  simp [pathPrecision, Fin.sum_univ_three]
  field_simp
  ring

/-- Diagonalization is a calculation on the original full matrix law.
Its product representation follows from the already derived Gaussian
coordinate independence. -/
theorem comparison_law_eq_product {p : ℝ} (hp : 4 < p) (t : ℝ) :
    FiniteMatrixGaussian.law
      (comparisonPrecision p (Geometry.SourceAxisTT.ttMatrix 1 0) t) =
      (Measure.pi (fun i : Fin 3 => GaussianPrecisionKL.law (pathPrecision p t i))).map
        (WithLp.toLp 2) := by
  rw [FinitePrecisionEquilibrium.law_eq_product (pathPrecision_pos hp t),
    comparisonPrecision_diagonal]
  unfold FiniteMatrixGaussian.law FinitePrecisionGaussian.law
    FinitePrecisionGaussian.covarianceMatrix
  congr 1
  apply Matrix.inv_eq_left_inv
  rw [Matrix.diagonal_mul_diagonal]
  have he : (fun i => (pathPrecision p t i)⁻¹ * pathPrecision p t i) =
      (fun _ : Fin 3 => (1 : ℝ)) := by
    funext i
    exact inv_mul_cancel₀ (pathPrecision_pos hp t i).ne'
  rw [he, Matrix.diagonal_one]

def rowLogLikelihood (p t : ℝ) (x : Space (Fin 3)) : ℝ :=
  Real.log ((∏ i : Fin 3, gaussianPDFReal 0 (GaussianPrecisionKL.variance p) (x i)) /
    ∏ i : Fin 3, gaussianPDFReal 0 (GaussianPrecisionKL.variance (pathPrecision p t i)) (x i))

theorem rowLogLikelihood_eq {p : ℝ} (hp : 4 < p) (t : ℝ) (x : Space (Fin 3)) :
    rowLogLikelihood p t x = score (fun i => pathPrecision p t i - p) x +
      FinitePrecisionPath.logPartition (pathPrecision p) 0 t := by
  have hp0 : 0 < p := by linarith
  have hbase (i : Fin 3) :
      gaussianPDFReal 0 (GaussianPrecisionKL.variance p) (x i) ≠ 0 :=
    (gaussianPDFReal_pos _ _ _ (GaussianPrecisionKL.variance_ne_zero hp0)).ne'
  have hvaried (i : Fin 3) :
      gaussianPDFReal 0 (GaussianPrecisionKL.variance (pathPrecision p t i)) (x i) ≠ 0 :=
    (gaussianPDFReal_pos _ _ _
      (GaussianPrecisionKL.variance_ne_zero (pathPrecision_pos hp t i))).ne'
  rw [rowLogLikelihood, Real.log_div
    (Finset.prod_ne_zero_iff.mpr (fun i _ => hbase i))
    (Finset.prod_ne_zero_iff.mpr (fun i _ => hvaried i)),
    Real.log_prod (fun i _ => hbase i), Real.log_prod (fun i _ => hvaried i)]
  simp_rw [GaussianPrecisionKL.density_log hp0,
    GaussianPrecisionKL.density_log (pathPrecision_pos hp t _)]
  simp [FinitePrecisionGaussian.score, GaussianPrecisionMoments.score,
    FinitePrecisionPath.logPartition, pathPrecision, Fin.sum_univ_three]
  ring

/-- The compensated response is the integral of the actual joint product
log likelihood in the original three-coordinate Gaussian state. -/
theorem relativeResponse_eq_logLikelihood_integral {p : ℝ} (hp : 4 < p) (t : ℝ) :
    relativeResponse p t =
      ∫ x : Space (Fin 3), rowLogLikelihood p t x
        ∂FinitePrecisionGaussian.law (fun _ => p) := by
  have hp0 : 0 < p := by linarith
  have hi : Integrable (score (fun i => pathPrecision p t i - p))
      (FinitePrecisionGaussian.law (fun _ : Fin 3 => p)) := by
    exact integrable_finsetSum _ (fun i _ =>
      (FinitePrecisionGaussian.coordinate_score_memLp (fun _ => hp0)
        (fun i => pathPrecision p t i - p) i).integrable (by norm_num))
  rw [show rowLogLikelihood p t = fun x => score (fun i => pathPrecision p t i - p) x +
      FinitePrecisionPath.logPartition (pathPrecision p) 0 t by
    funext x; exact rowLogLikelihood_eq hp t x]
  rw [integral_add hi (integrable_const _), integral_const]
  simp only [probReal_univ, one_smul, relativeResponse, negativeLogPartition,
    referenceActionMean, sub_neg_eq_add]

theorem negativeLogPartition_hasDerivAt {p : ℝ} (hp : 4 < p) (t : ℝ) :
    HasDerivAt (negativeLogPartition p)
      (FinitePrecisionPath.force (pathPrecision p) (pathVelocity p) t) t := by
  simpa only [negativeLogPartition, neg_neg] using!
    (FinitePrecisionPath.logPartition_hasDerivAt (pathPrecision_pos hp t)
      (pathPrecision_hasDerivAt p t)).neg

theorem relativeResponse_hasDerivAt {p : ℝ} (hp : 4 < p) (t : ℝ) :
    HasDerivAt (relativeResponse p) (relativeForce p t) t := by
  have hp0 : 0 < p := by linarith
  have hd := ((((hasDerivAt_id t).pow 2).const_mul 2).div_const p).sub
    (negativeLogPartition_hasDerivAt hp t)
  convert! hd using 1
  · funext s
    simp only [relativeResponse, referenceActionMean_eq hp0, Pi.sub_apply,
      Pi.pow_apply, id_eq]
  · simp only [relativeForce, id_eq]
    ring

/-- The logarithmic partition keeps its direct second vertex. -/
theorem negativeLogPartition_secondDeriv_zero {p : ℝ} (hp : 4 < p) :
    HasDerivAt (fun t => deriv (negativeLogPartition p) t)
      (4 / p - 16 / p ^ 2) 0 := by
  have hp0 : 0 < p := by linarith
  have hd := FinitePrecisionPath.force_hasDerivAt
    (p := pathPrecision p) (v := pathVelocity p) (a := pathAcceleration p)
    (pathPrecision_pos hp 0) (pathPrecision_hasDerivAt p 0) (pathVelocity_hasDerivAt p 0)
  have he : FinitePrecisionPath.curvature
      (pathPrecision p) (pathVelocity p) (pathAcceleration p) 0 = 4 / p - 16 / p ^ 2 := by
    simp [FinitePrecisionPath.curvature, pathPrecision, pathVelocity, pathAcceleration,
      Fin.sum_univ_three]
    field_simp
    ring
  rw [he] at hd
  exact hd.congr_of_eventuallyEq (Eventually.of_forall fun t =>
    (negativeLogPartition_hasDerivAt hp t).deriv)

/-- In the same-source relative entropy the reference action cancels the
direct second vertex, leaving the original Gaussian score covariance. -/
theorem relativeResponse_secondDeriv_zero {p : ℝ} (hp : 4 < p) :
    HasDerivAt (fun t => deriv (relativeResponse p) t) (16 / p ^ 2) 0 := by
  have hd := (((hasDerivAt_id (0 : ℝ)).const_mul 4).div_const p).sub
    (negativeLogPartition_secondDeriv_zero hp)
  have he : HasDerivAt (relativeForce p) (16 / p ^ 2) 0 := by
    convert! hd using 1
    · funext t
      simp only [relativeForce, Pi.sub_apply, id_eq,
        (negativeLogPartition_hasDerivAt hp t).deriv]
    · ring
  exact he.congr_of_eventuallyEq (Eventually.of_forall fun t =>
    (relativeResponse_hasDerivAt hp t).deriv)

theorem partition_hessian_eq_rowHessian {p : ℝ} (hp : 4 < p) :
    4 / p - 16 / p ^ 2 = rowHessian p 1 0 1 0 := by
  rw [rowHessian_eq (by linarith : 0 < p)]
  field_simp
  ring

theorem relative_hessian_eq_covariance {p : ℝ} (hp : 4 < p) :
    16 / p ^ 2 =
      cov[FiniteMatrixGaussian.score (vertex (Geometry.SourceAxisTT.ttMatrix 1 0)),
        FiniteMatrixGaussian.score (vertex (Geometry.SourceAxisTT.ttMatrix 1 0));
        FiniteMatrixGaussian.law (precision p)] := by
  rw [row_covariance (by linarith : 0 < p)]
  ring

/-- Every generated shell precision is in the exact unit-polarization
path domain, including the pure-kinetic point `omega = m2 = 0`. -/
theorem shellPrecision_gt_four {omega m2 : ℝ} (hm : 0 ≤ m2) :
    4 < shellPrecision omega m2 := by
  unfold shellPrecision
  nlinarith [sq_nonneg omega]

theorem shell_relativeResponse_secondDeriv_zero {omega m2 : ℝ} (hm : 0 ≤ m2) :
    HasDerivAt (fun t => deriv (relativeResponse (shellPrecision omega m2)) t)
      (16 / (shellPrecision omega m2) ^ 2) 0 :=
  relativeResponse_secondDeriv_zero (shellPrecision_gt_four hm)

/-- Twice the relative entropy of all three actual rows has precisely
the connected shell response already computed from their original law. -/
theorem shell_relative_hessian_eq_tensor_response {omega m2 : ℝ} (hm : 0 ≤ m2) :
    3 * 2 * (16 / (shellPrecision omega m2) ^ 2) = shellTensorResponse omega m2 := by
  rw [shellTensorResponse_eq hm]
  unfold shellPrecision
  ring

end GeneratedFoundations.Physical.SourceTTFrameRelativeResponse

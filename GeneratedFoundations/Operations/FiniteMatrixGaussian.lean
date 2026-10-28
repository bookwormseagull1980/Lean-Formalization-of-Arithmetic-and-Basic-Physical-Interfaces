module

public import GeneratedFoundations.Operations.FinitePrecisionGaussian
public import Mathlib.Analysis.Matrix.PosDef

/-!
# Full precision Gaussians and quadratic insertions

A positive real matrix determines a centred Gaussian on the entire
coefficient space. Its covariance is the full inverse matrix, including
off-diagonal entries. Uniqueness is among all centred Gaussian measures
satisfying the precision equation. No coordinate independence is imposed.

Quadratic insertions are evaluated on this law. Fourth moments are derived
from the one-dimensional Gaussian fourth moment by exact polarization.
All pairings are retained before taking any bound.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace Matrix NNReal ENNReal

namespace GeneratedFoundations.Operations.FiniteMatrixGaussian

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev Space (ι : Type*) [Fintype ι] := EuclideanSpace ℝ ι

def law (P : Matrix ι ι ℝ) : Measure (Space ι) := multivariateGaussian 0 P⁻¹

instance (P : Matrix ι ι ℝ) : IsGaussian (law P) := by unfold law; infer_instance
instance (P : Matrix ι ι ℝ) : IsProbabilityMeasure (law P) := inferInstance

@[simp] theorem mean_zero (P : Matrix ι ι ℝ) : (∫ x, x ∂law P) = 0 :=
  integral_id_multivariateGaussian

theorem precision_mul_inverse {P : Matrix ι ι ℝ} (hP : P.PosDef) : P * P⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (P.isUnit_iff_isUnit_det.mp hP.isUnit)

theorem inverse_mul_precision {P : Matrix ι ι ℝ} (hP : P.PosDef) : P⁻¹ * P = 1 :=
  Matrix.nonsing_inv_mul _ (P.isUnit_iff_isUnit_det.mp hP.isUnit)

theorem coordinateCovariance_eq {P : Matrix ι ι ℝ} (hP : P.PosDef) :
    FinitePrecisionGaussian.coordinateCovariance (law P) = P⁻¹ := by
  ext i j
  exact covariance_eval_multivariateGaussian hP.inv.posSemidef i j

theorem covariance_unique {P : Matrix ι ι ℝ} (hP : P.PosDef)
    (C : Matrix ι ι ℝ) (hC : P * C = 1) : C = P⁻¹ := by
  calc
    C = (P⁻¹ * P) * C := by rw [inverse_mul_precision hP, Matrix.one_mul]
    _ = P⁻¹ := by rw [Matrix.mul_assoc, hC, Matrix.mul_one]

/-- Arbitrary Gaussian competitors may have correlated coordinates. -/
theorem law_unique {P : Matrix ι ι ℝ} (hP : P.PosDef)
    (ν : Measure (Space ι)) [IsGaussian ν] (hmean : (∫ x, x ∂ν) = 0)
    (hprecision : P * FinitePrecisionGaussian.coordinateCovariance ν = 1) : ν = law P := by
  have hC := covariance_unique hP (FinitePrecisionGaussian.coordinateCovariance ν) hprecision
  apply IsGaussian.ext (hmean.trans (mean_zero P).symm)
  rw [← ContinuousLinearMap.toBilinForm_inj]
  refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun ι ℝ).toBasis fun i j => ?_
  rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply,
    covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
    covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id]
  change cov[fun x : Space ι => inner ℝ (EuclideanSpace.basisFun ι ℝ i) x,
    fun x => inner ℝ (EuclideanSpace.basisFun ι ℝ j) x; ν] =
      cov[fun x : Space ι => inner ℝ (EuclideanSpace.basisFun ι ℝ i) x,
        fun x => inner ℝ (EuclideanSpace.basisFun ι ℝ j) x; law P]
  simpa only [EuclideanSpace.basisFun_inner, FinitePrecisionGaussian.coordinateCovariance] using
    (congrFun (congrFun hC i) j).trans
      (congrFun (congrFun (coordinateCovariance_eq hP) i) j).symm

theorem law_existsUnique {P : Matrix ι ι ℝ} (hP : P.PosDef) :
    ∃! ν : Measure (Space ι), IsGaussian ν ∧ (∫ x, x ∂ν) = 0 ∧
      P * FinitePrecisionGaussian.coordinateCovariance ν = 1 := by
  refine ⟨law P, ⟨inferInstance, mean_zero P, ?_⟩, ?_⟩
  · rw [coordinateCovariance_eq hP]; exact precision_mul_inverse hP
  · intro ν hν
    let : IsGaussian ν := hν.1
    exact law_unique hP ν hν.2.1 hν.2.2

theorem linear_mean (P : Matrix ι ι ℝ) (L : StrongDual ℝ (Space ι)) :
    (∫ x, L x ∂law P) = 0 := by
  calc
    (∫ x, L x ∂law P) = L (∫ x, x ∂law P) :=
      L.integral_comp_comm IsGaussian.integrable_id
    _ = 0 := by rw [mean_zero, map_zero]

theorem linear_memLp (P : Matrix ι ι ℝ) (L : StrongDual ℝ (Space ι))
    (p : ℝ≥0∞) (hp : p ≠ ∞) : MemLp L p (law P) := IsGaussian.memLp_dual _ _ _ hp

theorem linear_product_memLp_two (P : Matrix ι ι ℝ) (L M : StrongDual ℝ (Space ι)) :
    MemLp (fun x => L x * M x) 2 (law P) := by
  have : ENNReal.HolderTriple 4 4 2 := ⟨by
    change ((4 : ℝ≥0) : ℝ≥0∞)⁻¹ + ((4 : ℝ≥0) : ℝ≥0∞)⁻¹ = ((2 : ℝ≥0) : ℝ≥0∞)⁻¹
    rw [← ENNReal.coe_inv (by norm_num : (4 : ℝ≥0) ≠ 0),
      ← ENNReal.coe_inv (by norm_num : (2 : ℝ≥0) ≠ 0), ← ENNReal.coe_add]
    norm_num⟩
  exact (linear_memLp P L 4 (by norm_num)).mul (linear_memLp P M 4 (by norm_num))

theorem linear_fourth (P : Matrix ι ι ℝ) (L : StrongDual ℝ (Space ι)) :
    (∫ x, (L x) ^ 4 ∂law P) = 3 * Var[L; law P] ^ 2 := by
  have hm := IsGaussian.map_eq_gaussianReal (μ := law P) L
  rw [linear_mean] at hm
  calc
    (∫ x, (L x) ^ 4 ∂law P) = ∫ y : ℝ, y ^ 4 ∂(law P).map L :=
      (integral_map (μ := law P) (φ := L) (f := fun y : ℝ => y ^ 4)
        (by fun_prop) (by fun_prop)).symm
    _ = 3 * Var[L; law P] ^ 2 := by
      rw [hm, GaussianPrecisionMoments.centered_fourth_integral,
        Real.coe_toNNReal _ (variance_nonneg _ _)]

theorem linear_fourth_integrable (P : Matrix ι ι ℝ) (L : StrongDual ℝ (Space ι)) :
    Integrable (fun x => (L x) ^ 4) (law P) := by
  convert (linear_product_memLp_two P L L).integrable_mul
    (linear_product_memLp_two P L L) using 1
  ext x
  simp only [Pi.mul_apply]
  ring

theorem linear_square_product (P : Matrix ι ι ℝ) (L M : StrongDual ℝ (Space ι)) :
    (∫ x, (L x) ^ 2 * (M x) ^ 2 ∂law P) =
      Var[L; law P] * Var[M; law P] + 2 * cov[L, M; law P] ^ 2 := by
  have hLM : Integrable (fun x => (L x) ^ 2 * (M x) ^ 2) (law P) := by
    convert (linear_product_memLp_two P L L).integrable_mul
      (linear_product_memLp_two P M M) using 1
    ext x
    simp only [Pi.mul_apply]
    ring
  have he : (fun x => ((L + M) x) ^ 4 + ((L - M) x) ^ 4) =
      fun x => 2 * (L x) ^ 4 + 12 * ((L x) ^ 2 * (M x) ^ 2) + 2 * (M x) ^ 4 := by
    funext x
    change (L x + M x) ^ 4 + (L x - M x) ^ 4 = _
    ring
  have hi := congrArg (fun f : Space ι → ℝ => ∫ x, f x ∂law P) he
  rw [integral_add (linear_fourth_integrable P (L + M))
    (linear_fourth_integrable P (L - M)),
    integral_add (f := fun x => 2 * (L x) ^ 4 + 12 * ((L x) ^ 2 * (M x) ^ 2))
      ((linear_fourth_integrable P L).const_mul 2 |>.add (hLM.const_mul 12))
      ((linear_fourth_integrable P M).const_mul 2),
    integral_add ((linear_fourth_integrable P L).const_mul 2) (hLM.const_mul 12),
    integral_const_mul, integral_const_mul, integral_const_mul,
    linear_fourth, linear_fourth, linear_fourth, linear_fourth] at hi
  have ha : Var[L + M; law P] = Var[L; law P] + 2 * cov[L, M; law P] + Var[M; law P] :=
    variance_add (linear_memLp P L 2 (by norm_num)) (linear_memLp P M 2 (by norm_num))
  have hs : Var[L - M; law P] = Var[L; law P] - 2 * cov[L, M; law P] + Var[M; law P] :=
    variance_sub (linear_memLp P L 2 (by norm_num)) (linear_memLp P M 2 (by norm_num))
  rw [ha, hs] at hi
  nlinarith [hi]

/-- The normalization agrees with the original quadratic action. -/
def score (V : Matrix ι ι ℝ) (x : Space ι) : ℝ :=
  ∑ i, ∑ j, (V i j / 2) * (x i * x j)

omit [DecidableEq ι] in
theorem score_eq_dotProduct (V : Matrix ι ι ℝ) (x : Space ι) :
    score V x = (x ⬝ᵥ V *ᵥ x) / 2 := by
  simp only [score, dotProduct, Matrix.mulVec, Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem coordinate_mean (P : Matrix ι ι ℝ) (i : ι) :
    (∫ x : Space ι, x i ∂law P) = 0 := linear_mean P (EuclideanSpace.proj i)

theorem coordinate_product_mean {P : Matrix ι ι ℝ} (hP : P.PosDef) (i j : ι) :
    (∫ x : Space ι, x i * x j ∂law P) = P⁻¹ i j := by
  have h := congrFun (congrFun (coordinateCovariance_eq hP) i) j
  change (∫ x : Space ι,
    (x i - ∫ y : Space ι, y i ∂law P) * (x j - ∫ y : Space ι, y j ∂law P) ∂law P) = P⁻¹ i j at h
  simpa only [coordinate_mean, sub_zero] using h

theorem coordinate_product_memLp_two (P : Matrix ι ι ℝ) (i j : ι) :
    MemLp (fun x : Space ι => x i * x j) 2 (law P) := by
  simpa only [EuclideanSpace.coe_proj] using
    linear_product_memLp_two P (EuclideanSpace.proj i) (EuclideanSpace.proj j)

theorem score_memLp_two (P V : Matrix ι ι ℝ) : MemLp (score V) 2 (law P) := by
  unfold score
  apply memLp_finsetSum
  intro i _
  apply memLp_finsetSum
  intro j _
  exact (coordinate_product_memLp_two P i j).const_mul (V i j / 2)

theorem score_mean {P : Matrix ι ι ℝ} (hP : P.PosDef) (V : Matrix ι ι ℝ) :
    (∫ x, score V x ∂law P) = ∑ i, ∑ j, V i j * P⁻¹ i j / 2 := by
  unfold score
  have hm (i j : ι) : MemLp (fun x : Space ι => (V i j / 2) * (x i * x j)) 2 (law P) :=
    (coordinate_product_memLp_two P i j).const_mul _
  have hr (i : ι) : MemLp (fun x : Space ι => ∑ j, (V i j / 2) * (x i * x j)) 2 (law P) :=
    memLp_finsetSum _ (fun j _ => hm i j)
  rw [integral_finsetSum _ (fun i _ => (hr i).integrable (by norm_num))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => (hm i j).integrable (by norm_num))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul, coordinate_product_mean hP]
  ring

theorem score_mean_trace {P : Matrix ι ι ℝ} (hP : P.PosDef) (V : Matrix ι ι ℝ) :
    (∫ x, score V x ∂law P) = Matrix.trace (P⁻¹ * V) / 2 := by
  rw [score_mean hP]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hs := hP.inv.isHermitian.apply i j
  simp only [star_trivial] at hs
  rw [hs]
  ring

end GeneratedFoundations.Operations.FiniteMatrixGaussian

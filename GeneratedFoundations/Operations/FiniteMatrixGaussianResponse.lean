module

public import GeneratedFoundations.Operations.FiniteMatrixGaussian

/-!
# Connected responses of full quadratic Gaussian insertions

The two covariance contractions are derived on the same full Gaussian
law. This calculation neither diagonalizes the insertions separately nor
sets distinct channels orthogonal. The four linear factors may coincide.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace Matrix

namespace GeneratedFoundations.Operations.FiniteMatrixGaussian

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
private theorem linear_coe_add (L M : StrongDual ℝ (Space ι)) :
    (⇑(L + M) : Space ι → ℝ) = (L : Space ι → ℝ) + (M : Space ι → ℝ) := rfl

theorem linear_square_mean (P : Matrix ι ι ℝ) (L : StrongDual ℝ (Space ι)) :
    (∫ x, (L x) ^ 2 ∂law P) = Var[L; law P] := by
  have h := variance_eq_sub (linear_memLp P L 2 (by norm_num))
  simpa only [linear_mean, zero_pow (by decide : 2 ≠ 0), sub_zero, Pi.pow_apply] using h.symm

theorem linear_square_covariance (P : Matrix ι ι ℝ) (L M : StrongDual ℝ (Space ι)) :
    cov[fun x => (L x) ^ 2, fun x => (M x) ^ 2; law P] =
      2 * cov[L, M; law P] ^ 2 := by
  have hL : MemLp (fun x => (L x) ^ 2) 2 (law P) := by
    simpa only [pow_two] using linear_product_memLp_two P L L
  have hM : MemLp (fun x => (M x) ^ 2) 2 (law P) := by
    simpa only [pow_two] using linear_product_memLp_two P M M
  rw [covariance_eq_sub hL hM]
  change (∫ x, (L x) ^ 2 * (M x) ^ 2 ∂law P) -
    (∫ x, (L x) ^ 2 ∂law P) * (∫ x, (M x) ^ 2 ∂law P) = _
  rw [linear_square_product, linear_square_mean, linear_square_mean]
  ring

theorem linear_product_square_covariance (P : Matrix ι ι ℝ)
    (L M Z : StrongDual ℝ (Space ι)) :
    cov[fun x => L x * M x, fun x => (Z x) ^ 2; law P] =
      2 * cov[L, Z; law P] * cov[M, Z; law P] := by
  have hS (V : StrongDual ℝ (Space ι)) : MemLp (fun x => (V x) ^ 2) 2 (law P) := by
    simpa only [pow_two] using linear_product_memLp_two P V V
  have he : (fun x => ((L + M) x) ^ 2) =
      (fun x => (L x) ^ 2) + (fun x => 2 * (L x * M x)) + (fun x => (M x) ^ 2) := by
    funext x
    change (L x + M x) ^ 2 = (L x) ^ 2 + 2 * (L x * M x) + (M x) ^ 2
    ring
  have hi := linear_square_covariance P (L + M) Z
  rw [he, covariance_add_left ((hS L).add ((linear_product_memLp_two P L M).const_mul 2))
    (hS M) (hS Z), covariance_add_left (hS L)
      ((linear_product_memLp_two P L M).const_mul 2) (hS Z),
    covariance_const_mul_left, linear_square_covariance, linear_square_covariance,
    linear_coe_add,
    covariance_add_left (linear_memLp P L 2 (by norm_num))
      (linear_memLp P M 2 (by norm_num)) (linear_memLp P Z 2 (by norm_num))] at hi
  nlinarith [hi]

/-- Wick's connected four-factor identity, proved without an independence
hypothesis or a diagonal covariance restriction. -/
theorem linear_product_covariance (P : Matrix ι ι ℝ)
    (L M Z W : StrongDual ℝ (Space ι)) :
    cov[fun x => L x * M x, fun x => Z x * W x; law P] =
      cov[L, Z; law P] * cov[M, W; law P] +
        cov[L, W; law P] * cov[M, Z; law P] := by
  have hS (V : StrongDual ℝ (Space ι)) : MemLp (fun x => (V x) ^ 2) 2 (law P) := by
    simpa only [pow_two] using linear_product_memLp_two P V V
  have he : (fun x => ((Z + W) x) ^ 2) =
      (fun x => (Z x) ^ 2) + (fun x => 2 * (Z x * W x)) + (fun x => (W x) ^ 2) := by
    funext x
    change (Z x + W x) ^ 2 = (Z x) ^ 2 + 2 * (Z x * W x) + (W x) ^ 2
    ring
  have hi := linear_product_square_covariance P L M (Z + W)
  rw [he, covariance_add_right (linear_product_memLp_two P L M)
    ((hS Z).add ((linear_product_memLp_two P Z W).const_mul 2)) (hS W),
    covariance_add_right (linear_product_memLp_two P L M) (hS Z)
      ((linear_product_memLp_two P Z W).const_mul 2), covariance_const_mul_right,
    linear_product_square_covariance, linear_product_square_covariance, linear_coe_add,
    covariance_add_right (linear_memLp P L 2 (by norm_num))
      (linear_memLp P Z 2 (by norm_num)) (linear_memLp P W 2 (by norm_num)),
    covariance_add_right (linear_memLp P M 2 (by norm_num))
      (linear_memLp P Z 2 (by norm_num)) (linear_memLp P W 2 (by norm_num))] at hi
  nlinarith [hi]

theorem coordinate_product_covariance {P : Matrix ι ι ℝ} (hP : P.PosDef) (i j k l : ι) :
    cov[fun x : Space ι => x i * x j, fun x => x k * x l; law P] =
      P⁻¹ i k * P⁻¹ j l + P⁻¹ i l * P⁻¹ j k := by
  have h := linear_product_covariance P (EuclideanSpace.proj i) (EuclideanSpace.proj j)
    (EuclideanSpace.proj k) (EuclideanSpace.proj l)
  have hc (a b : ι) : cov[fun x : Space ι => x a, fun x => x b; law P] = P⁻¹ a b :=
    congrFun (congrFun (coordinateCovariance_eq hP) a) b
  simpa only [EuclideanSpace.coe_proj, hc] using h

/-- Full four-index contraction. Both connected pairings and all original
matrix entries occur in the same expression. -/
theorem score_covariance {P : Matrix ι ι ℝ} (hP : P.PosDef) (V W : Matrix ι ι ℝ) :
    cov[score V, score W; law P] =
      ∑ i, ∑ k, ∑ j, ∑ l, (V i j * W k l / 4) *
        (P⁻¹ i k * P⁻¹ j l + P⁻¹ i l * P⁻¹ j k) := by
  have hm (V : Matrix ι ι ℝ) (i j : ι) :
      MemLp (fun x : Space ι => (V i j / 2) * (x i * x j)) 2 (law P) :=
    (coordinate_product_memLp_two P i j).const_mul _
  have he (V : Matrix ι ι ℝ) : score V =
      fun x : Space ι => ∑ i, ∑ j, (V i j / 2) * (x i * x j) := by
    funext x
    rfl
  rw [he V, he W,
    covariance_fun_sum_fun_sum (fun i => memLp_finsetSum _ (fun j _ => hm V i j))
      (fun k => memLp_finsetSum _ (fun l _ => hm W k l))]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  rw [covariance_fun_sum_fun_sum (hm V i) (hm W k)]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  rw [covariance_const_mul_left, covariance_const_mul_right, coordinate_product_covariance hP]
  ring

theorem score_variance {P : Matrix ι ι ℝ} (hP : P.PosDef) (V : Matrix ι ι ℝ) :
    Var[score V; law P] =
      ∑ i, ∑ k, ∑ j, ∑ l, (V i j * V k l / 4) *
        (P⁻¹ i k * P⁻¹ j l + P⁻¹ i l * P⁻¹ j k) := by
  rw [← covariance_self (score_memLp_two P V).aemeasurable, score_covariance hP]

end GeneratedFoundations.Operations.FiniteMatrixGaussian

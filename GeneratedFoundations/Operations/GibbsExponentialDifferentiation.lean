module

public import GeneratedFoundations.Operations.PreparedTraceForm
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The exponential derivative at a real diagonal matrix

Analyticity gives the Fréchet derivative of the matrix exponential. Its value
on a commutator follows by differentiating an exponential conjugation curve.
Together with differentiation in commuting directions, this determines its
value on every matrix unit, including repeated diagonal entries. The resulting
entrywise multiplier is the positive divided difference of the real exponential.
-/

@[expose] public section

noncomputable section

open Filter
open scoped BigOperators Topology Matrix.Norms.Operator

namespace GeneratedFoundations.Operations.GibbsExponentialDifferentiation

open PreparedTraceForm (Mat)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def expDerivative (A : Mat ι) : Mat ι →L[ℝ] Mat ι :=
  fderiv ℝ NormedSpace.exp A

theorem exp_hasFDerivAt (A : Mat ι) :
    HasFDerivAt NormedSpace.exp (expDerivative A) A :=
  (NormedSpace.exp_analytic (𝕂 := ℝ) A).differentiableAt.hasFDerivAt

theorem exp_line_hasDerivAt_zero (K : Mat ι) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • K)) K 0 := by
  have hK : HasDerivAt (fun t : ℝ => t • K) K 0 := by
    convert! (hasDerivAt_id (0 : ℝ)).smul_const K using 1
    simp only [one_smul]
  convert! (_root_.hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := Mat ι)).comp_hasDerivAt_of_eq
    0 hK (by simp) using 1

theorem exp_conjugation_curve (A E : Mat ι) (t : ℝ) :
    NormedSpace.exp (NormedSpace.exp (t • E) * A * NormedSpace.exp (t • (-E))) =
      NormedSpace.exp (t • E) * NormedSpace.exp A * NormedSpace.exp (t • (-E)) := by
  simpa only [smul_neg, Matrix.exp_neg] using
    Matrix.exp_conj (NormedSpace.exp (t • E)) A (Matrix.isUnit_exp _)

theorem conjugation_curve_hasDerivAt_zero (A E : Mat ι) :
    HasDerivAt
      (fun t : ℝ => NormedSpace.exp (t • E) * A * NormedSpace.exp (t • (-E)))
      (E * A - A * E) 0 := by
  convert! ((exp_line_hasDerivAt_zero E).mul_const A).mul
    (exp_line_hasDerivAt_zero (-E)) using 1
  simp only [zero_smul, NormedSpace.exp_zero, one_mul, mul_one, mul_neg, sub_eq_add_neg]

/-- The derivative intertwines infinitesimal conjugation. -/
theorem expDerivative_commutator (A E : Mat ι) :
    expDerivative A (E * A - A * E) =
      E * NormedSpace.exp A - NormedSpace.exp A * E := by
  have hleft : HasDerivAt
      (fun t : ℝ => NormedSpace.exp
        (NormedSpace.exp (t • E) * A * NormedSpace.exp (t • (-E))))
      (expDerivative A (E * A - A * E)) 0 := by
    convert! (exp_hasFDerivAt A).comp_hasDerivAt_of_eq 0
      (conjugation_curve_hasDerivAt_zero A E) (by simp) using 1
  have hright : HasDerivAt
      (fun t : ℝ => NormedSpace.exp
        (NormedSpace.exp (t • E) * A * NormedSpace.exp (t • (-E))))
      (E * NormedSpace.exp A - NormedSpace.exp A * E) 0 := by
    apply (conjugation_curve_hasDerivAt_zero (NormedSpace.exp A) E).congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (exp_conjugation_curve A E)
  exact hleft.unique hright

/-- In a commuting direction the derivative is left multiplication by `exp A`. -/
theorem expDerivative_of_commute (A K : Mat ι) (h : Commute A K) :
    expDerivative A K = NormedSpace.exp A * K := by
  have hline : HasDerivAt (fun t : ℝ => A + t • K) K 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).smul_const K).const_add A using 1
    simp only [one_smul]
  have hleft : HasDerivAt (fun t : ℝ => NormedSpace.exp (A + t • K))
      (expDerivative A K) 0 := by
    convert! (exp_hasFDerivAt A).comp_hasDerivAt_of_eq 0 hline (by simp) using 1
  have hright : HasDerivAt (fun t : ℝ => NormedSpace.exp (A + t • K))
      (NormedSpace.exp A * K) 0 := by
    apply ((exp_line_hasDerivAt_zero K).const_mul (NormedSpace.exp A)).congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun t =>
      Matrix.exp_add_of_commute A (t • K) (h.smul_right t)
  exact hleft.unique hright

def realDiagonal (a : ι → ℝ) : Mat ι := Matrix.diagonal fun i => (a i : ℂ)

@[simp] theorem exp_realDiagonal (a : ι → ℝ) :
    NormedSpace.exp (realDiagonal a) = realDiagonal (fun i => Real.exp (a i)) := by
  simp only [realDiagonal, Matrix.exp_diagonal, Pi.exp_def,
    ← Complex.exp_eq_exp_ℂ, ← Complex.ofReal_exp]

theorem realDiagonal_mul_single (a : ι → ℝ) (i j : ι) (z : ℂ) :
    realDiagonal a * Matrix.single i j z = a i • Matrix.single i j z := by
  ext k l
  by_cases hik : i = k <;> by_cases hjl : j = l <;>
    simp [realDiagonal, Matrix.single, hik, hjl, Complex.real_smul, mul_comm]

theorem single_mul_realDiagonal (a : ι → ℝ) (i j : ι) (z : ℂ) :
    Matrix.single i j z * realDiagonal a = a j • Matrix.single i j z := by
  ext k l
  by_cases hik : i = k <;> by_cases hjl : j = l <;>
    simp [realDiagonal, Matrix.single, hik, hjl, Complex.real_smul, mul_comm]

/-- The continuous divided difference, with the derivative on the diagonal. -/
def expDividedDifference (a b : ℝ) : ℝ :=
  if a = b then Real.exp a else (Real.exp b - Real.exp a) / (b - a)

@[simp] theorem expDividedDifference_self (a : ℝ) :
    expDividedDifference a a = Real.exp a := by simp [expDividedDifference]

theorem expDividedDifference_symm (a b : ℝ) :
    expDividedDifference a b = expDividedDifference b a := by
  by_cases h : a = b
  · subst b
    rfl
  · simp only [expDividedDifference, h, Ne.symm h, ↓reduceIte]
    rw [← neg_sub (Real.exp a) (Real.exp b), ← neg_sub a b, neg_div_neg_eq]

theorem expDividedDifference_pos (a b : ℝ) : 0 < expDividedDifference a b := by
  rcases lt_trichotomy a b with h | h | h
  · rw [expDividedDifference, ite_eq_right (ne_of_lt h)]
    exact div_pos (sub_pos.mpr (Real.exp_lt_exp.mpr h)) (sub_pos.mpr h)
  · subst b
    simpa only [expDividedDifference_self] using Real.exp_pos a
  · rw [expDividedDifference, ite_eq_right (ne_of_gt h)]
    exact div_pos_of_neg_of_neg
      (sub_neg.mpr (Real.exp_lt_exp.mpr h)) (sub_neg.mpr h)

/-- Every matrix unit is an eigenvector of the derivative, also at repeated entries. -/
theorem expDerivative_realDiagonal_single (a : ι → ℝ) (i j : ι) (z : ℂ) :
    expDerivative (realDiagonal a) (Matrix.single i j z) =
      expDividedDifference (a i) (a j) • Matrix.single i j z := by
  by_cases h : a i = a j
  · have hc : Commute (realDiagonal a) (Matrix.single i j z) := by
      change realDiagonal a * Matrix.single i j z = Matrix.single i j z * realDiagonal a
      rw [realDiagonal_mul_single, single_mul_realDiagonal, h]
    rw [expDerivative_of_commute _ _ hc, exp_realDiagonal, realDiagonal_mul_single]
    simp only [expDividedDifference, h, ↓reduceIte]
  · have hc := expDerivative_commutator (realDiagonal a) (Matrix.single i j z)
    rw [single_mul_realDiagonal, realDiagonal_mul_single, ← sub_smul, map_smul,
      exp_realDiagonal, single_mul_realDiagonal, realDiagonal_mul_single, ← sub_smul] at hc
    have hd : a j - a i ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    have hi := congrArg (fun M : Mat ι => (a j - a i)⁻¹ • M) hc
    simpa only [smul_smul, inv_mul_cancel₀ hd, one_smul, expDividedDifference, h,
      ↓reduceIte, div_eq_mul_inv, mul_comm] using hi

def diagonalDerivative (a : ι → ℝ) : Mat ι →L[ℝ] Mat ι :=
  LinearMap.toContinuousLinearMap
    { toFun := fun K i j => expDividedDifference (a i) (a j) • K i j
      map_add' := by
        intro K L
        ext i j
        exact smul_add _ _ _
      map_smul' := by
        intro r K
        ext i j
        change expDividedDifference (a i) (a j) • (r • K i j) =
          r • (expDividedDifference (a i) (a j) • K i j)
        exact smul_comm (expDividedDifference (a i) (a j)) (r : ℝ) (K i j) }

omit [DecidableEq ι] in
@[simp] theorem diagonalDerivative_apply (a : ι → ℝ) (K : Mat ι) (i j : ι) :
    diagonalDerivative a K i j = expDividedDifference (a i) (a j) • K i j := rfl

theorem diagonalDerivative_single (a : ι → ℝ) (i j : ι) (z : ℂ) :
    diagonalDerivative a (Matrix.single i j z) =
      expDividedDifference (a i) (a j) • Matrix.single i j z := by
  ext k l
  by_cases hik : i = k <;> by_cases hjl : j = l <;>
    simp [diagonalDerivative_apply, Matrix.single, hik, hjl]

/-- The entrywise formula determines the full real Fréchet derivative. -/
theorem expDerivative_realDiagonal (a : ι → ℝ) :
    expDerivative (realDiagonal a) = diagonalDerivative a := by
  apply ContinuousLinearMap.ext
  intro K
  rw [Matrix.matrix_eq_sum_single K]
  simp only [map_sum, expDerivative_realDiagonal_single, diagonalDerivative_single]

theorem exp_realDiagonal_hasFDerivAt (a : ι → ℝ) :
    HasFDerivAt NormedSpace.exp (diagonalDerivative a) (realDiagonal a) := by
  rw [← expDerivative_realDiagonal]
  exact exp_hasFDerivAt _

theorem exp_fderiv_realDiagonal_apply (a : ι → ℝ) (K : Mat ι) (i j : ι) :
    fderiv ℝ NormedSpace.exp (realDiagonal a) K i j =
      expDividedDifference (a i) (a j) • K i j := by
  rw [(exp_realDiagonal_hasFDerivAt a).fderiv, diagonalDerivative_apply]

omit [DecidableEq ι] in
theorem diagonalDerivative_injective (a : ι → ℝ) :
    Function.Injective (diagonalDerivative a) := by
  intro K L h
  ext i j
  have hij := congrArg (fun M : Mat ι => M i j) h
  have hw := ne_of_gt (expDividedDifference_pos (a i) (a j))
  have hi := congrArg (fun z : ℂ => (expDividedDifference (a i) (a j))⁻¹ • z) hij
  simpa only [diagonalDerivative_apply, smul_smul, inv_mul_cancel₀ hw, one_smul] using hi

omit [DecidableEq ι] in
theorem diagonalDerivative_surjective (a : ι → ℝ) :
    Function.Surjective (diagonalDerivative a) := by
  intro K
  refine ⟨(fun i j => (expDividedDifference (a i) (a j))⁻¹ • K i j : Mat ι), ?_⟩
  apply Matrix.ext
  intro i j
  have hw := ne_of_gt (expDividedDifference_pos (a i) (a j))
  change expDividedDifference (a i) (a j) •
    ((expDividedDifference (a i) (a j))⁻¹ • K i j) = K i j
  rw [smul_smul, mul_inv_cancel₀ hw, one_smul]

omit [DecidableEq ι] in
theorem diagonalDerivative_isHermitian (a : ι → ℝ) {K : Mat ι} (hK : K.IsHermitian) :
    (diagonalDerivative a K).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [diagonalDerivative_apply, star_smul, star_trivial,
    expDividedDifference_symm (a j) (a i), hK.apply i j]

theorem exp_fderiv_realDiagonal_isHermitian (a : ι → ℝ) {K : Mat ι}
    (hK : K.IsHermitian) :
    (fderiv ℝ NormedSpace.exp (realDiagonal a) K).IsHermitian := by
  rw [(exp_realDiagonal_hasFDerivAt a).fderiv]
  exact diagonalDerivative_isHermitian a hK

end GeneratedFoundations.Operations.GibbsExponentialDifferentiation

module

public import GeneratedFoundations.Operations.FiniteMatrixGaussianMarginal

/-!
# Collective vertices in an observed Gaussian source

Restriction of the precision and marginalization of its Gaussian law are
different operations. The latter differentiates the inverse of a retained
covariance. Its insertion therefore contains the complete inverse precision
on both sides of the original insertion. The mixed direct insertion also
contains the derivative of this return, even when the original insertion
is affine. All matrices below are full matrices of the same source.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace GeneratedFoundations.Operations.FiniteMatrixGaussian

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

private def compress (e : κ → ι) : Matrix ι ι ℝ →L[ℝ] Matrix κ κ ℝ :=
  ({ toFun := fun M => M.submatrix e e
     map_add' := by intros; rfl
     map_smul' := by intros; rfl } :
    Matrix ι ι ℝ →ₗ[ℝ] Matrix κ κ ℝ).toContinuousLinearMap

/-- The compressed full covariance response, not a compressed bare
precision insertion. -/
def retainedCovarianceInsertion (P V : Matrix ι ι ℝ) (e : κ → ι) : Matrix κ κ ℝ :=
  (P⁻¹ * V * P⁻¹).submatrix e e

def retainedInsertion (P V : Matrix ι ι ℝ) (e : κ → ι) : Matrix κ κ ℝ :=
  retainedPrecision P e * retainedCovarianceInsertion P V e * retainedPrecision P e

/-- The derivative of the same retained insertion. The middle summand
retains the original direct insertion and both inverse-precision returns.
The outer summands retain both variations of the effective precision. -/
def retainedDirect (P V Y W : Matrix ι ι ℝ) (e : κ → ι) : Matrix κ κ ℝ :=
  retainedInsertion P Y e * retainedCovarianceInsertion P V e * retainedPrecision P e +
    retainedPrecision P e *
      (P⁻¹ * W * P⁻¹ - P⁻¹ * Y * P⁻¹ * V * P⁻¹ -
        P⁻¹ * V * P⁻¹ * Y * P⁻¹).submatrix e e * retainedPrecision P e +
    retainedPrecision P e * retainedCovarianceInsertion P V e * retainedInsertion P Y e

omit [DecidableEq κ] in
theorem retainedCovariance_hasDerivAt {P : ℝ → Matrix ι ι ℝ}
    {Y : Matrix ι ι ℝ} {t : ℝ} (e : κ → ι)
    (hP : (P t).PosDef) (hY : HasDerivAt P Y t) :
    HasDerivAt (fun s => retainedCovariance (P s) e)
      (-retainedCovarianceInsertion (P t) Y e) t := by
  have h := (compress e).hasFDerivAt.comp_hasDerivAt t (inverse_hasDerivAt hP hY)
  simpa only [compress, ContinuousLinearMap.coe_mk', LinearMap.coe_mk,
    AddHom.coe_mk, retainedCovariance, retainedCovarianceInsertion,
    Matrix.neg_mul, Matrix.submatrix_neg] using! h

theorem retainedPrecision_hasDerivAt {P : ℝ → Matrix ι ι ℝ}
    {Y : Matrix ι ι ℝ} {t : ℝ} {e : κ → ι}
    (hP : (P t).PosDef) (he : Function.Injective e) (hY : HasDerivAt P Y t) :
    HasDerivAt (fun s => retainedPrecision (P s) e)
      (retainedInsertion (P t) Y e) t := by
  have h := inverse_hasDerivAt (retainedCovariance_posDef hP he)
    (retainedCovariance_hasDerivAt e hP hY)
  simpa only [retainedPrecision, retainedInsertion, Matrix.neg_mul, Matrix.mul_neg,
    neg_neg] using h

theorem retainedInsertion_symmetric {P : Matrix ι ι ℝ} (hP : P.PosDef)
    {e : κ → ι} (he : Function.Injective e) {Y : Matrix ι ι ℝ} (hY : Y.IsSymm) :
    (retainedInsertion P Y e).IsSymm := by
  have hC : (P⁻¹).transpose = P⁻¹ := hP.inv.isHermitian.isSymm.eq
  have hS : (retainedPrecision P e).transpose = retainedPrecision P e :=
    (retainedPrecision_posDef hP he).isHermitian.isSymm.eq
  have hM : (retainedCovarianceInsertion P Y e).transpose =
      retainedCovarianceInsertion P Y e := by
    simp only [retainedCovarianceInsertion, Matrix.transpose_submatrix,
      Matrix.transpose_mul, hC, hY.eq, Matrix.mul_assoc]
  change (retainedInsertion P Y e).transpose = retainedInsertion P Y e
  simp only [retainedInsertion, Matrix.transpose_mul, hS, hM, Matrix.mul_assoc]

theorem retainedInsertion_hasDerivAt
    {P V : ℝ → Matrix ι ι ℝ} {Y W : Matrix ι ι ℝ} {t : ℝ} {e : κ → ι}
    (hP : (P t).PosDef) (he : Function.Injective e)
    (hY : HasDerivAt P Y t) (hW : HasDerivAt V W t) :
    HasDerivAt (fun s => retainedInsertion (P s) (V s) e)
      (retainedDirect (P t) (V t) Y W e) t := by
  have hC := inverse_hasDerivAt hP hY
  have hS := retainedPrecision_hasDerivAt hP he hY
  have hM := (compress e).hasFDerivAt.comp_hasDerivAt t ((hC.mul hW).mul hC)
  have hM' : HasDerivAt (fun s => retainedCovarianceInsertion (P s) (V s) e)
      (((P t)⁻¹ * W * (P t)⁻¹ - (P t)⁻¹ * Y * (P t)⁻¹ * V t * (P t)⁻¹ -
        (P t)⁻¹ * V t * (P t)⁻¹ * Y * (P t)⁻¹).submatrix e e) t := by
    change HasDerivAt (fun s => retainedCovarianceInsertion (P s) (V s) e)
      (((-(P t)⁻¹ * Y * (P t)⁻¹ * V t + (P t)⁻¹ * W) * (P t)⁻¹ +
        ((P t)⁻¹ * V t) * (-(P t)⁻¹ * Y * (P t)⁻¹)).submatrix e e) t at hM
    apply hM.congr_deriv
    congr 1
    simp only [Matrix.add_mul, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
    abel
  exact ((hS.mul hM').mul hS).congr_deriv (by
    simp only [retainedInsertion, retainedDirect, Pi.mul_apply,
      Matrix.add_mul, Matrix.mul_assoc])

/-- The exact fluctuation--response identity after the observation is
formed. In particular the direct return correction is not discarded. -/
theorem retained_mean_hasDerivAt
    (P V : ℝ → Matrix ι ι ℝ) (t : ℝ) (Y W : Matrix ι ι ℝ)
    {e : κ → ι} (he : Function.Injective e) (hP : ∀ s, (P s).PosDef)
    (hY : HasDerivAt P Y t) (hW : HasDerivAt V W t) (hYs : Y.IsSymm) :
    HasDerivAt (fun s => ∫ x, score (retainedInsertion (P s) (V s) e) x
      ∂law (retainedPrecision (P s) e))
      ((∫ x, score (retainedDirect (P t) (V t) Y W e) x
        ∂law (retainedPrecision (P t) e)) -
      cov[score (retainedInsertion (P t) (V t) e),
        score (retainedInsertion (P t) Y e); law (retainedPrecision (P t) e)]) t := by
  exact varying_mean_hasDerivAt _ _ t _ _
    (fun s => retainedPrecision_posDef (hP s) he)
    (retainedPrecision_hasDerivAt (hP t) he hY)
    (retainedInsertion_hasDerivAt (hP t) he hY hW)
    (retainedInsertion_symmetric (hP t) he hYs)

/-- Covariance carried by the reconstructed retained coordinates. -/
def returnCovariance (P : Matrix ι ι ℝ) (e : κ → ι) : Matrix ι ι ℝ :=
  P⁻¹.submatrix id e * retainedPrecision P e * P⁻¹.submatrix e id

/-- The complementary covariance in the same complete source. -/
def conditionalCovariance (P : Matrix ι ι ℝ) (e : κ → ι) : Matrix ι ι ℝ :=
  P⁻¹ - returnCovariance P e

theorem retained_mean_eq_return_trace {P : Matrix ι ι ℝ} (hP : P.PosDef)
    {e : κ → ι} (he : Function.Injective e) (V : Matrix ι ι ℝ) :
    (∫ x, score (retainedInsertion P V e) x ∂law (retainedPrecision P e)) =
      Matrix.trace (returnCovariance P e * V) / 2 := by
  have hGS : retainedCovariance P e * retainedPrecision P e = 1 :=
    precision_mul_inverse (retainedCovariance_posDef hP he)
  have hM : retainedCovarianceInsertion P V e =
      P⁻¹.submatrix e id * V * P⁻¹.submatrix id e := by
    unfold retainedCovarianceInsertion
    rw [Matrix.submatrix_mul _ _ e id e Function.bijective_id,
      Matrix.submatrix_mul _ _ e id id Function.bijective_id]
    rfl
  rw [score_mean_trace (retainedPrecision_posDef hP he), retainedPrecision_inverse hP he]
  simp only [retainedInsertion, ← Matrix.mul_assoc, hGS, Matrix.one_mul]
  rw [hM]
  congr 1
  unfold returnCovariance
  simpa only [Matrix.mul_assoc] using
    Matrix.trace_mul_comm (P⁻¹.submatrix e id * V)
      (P⁻¹.submatrix id e * retainedPrecision P e)

/-- Complete first-response balance across a genuine observation. The
unresolved term uses the conditional covariance of the same source;
no absolute bound or vanishing mixed block is used. -/
theorem full_mean_eq_retained_add_conditional {P : Matrix ι ι ℝ} (hP : P.PosDef)
    {e : κ → ι} (he : Function.Injective e) (V : Matrix ι ι ℝ) :
    (∫ x, score V x ∂law P) =
      (∫ x, score (retainedInsertion P V e) x ∂law (retainedPrecision P e)) +
        Matrix.trace (conditionalCovariance P e * V) / 2 := by
  rw [score_mean_trace hP, retained_mean_eq_return_trace hP he]
  simp only [conditionalCovariance, Matrix.sub_mul, Matrix.trace_sub]
  ring

end GeneratedFoundations.Operations.FiniteMatrixGaussian

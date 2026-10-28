module

public import GeneratedFoundations.Operations.FiniteMatrixGaussianResponse
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Variation of a full Gaussian quadratic mean

The covariance is differentiated as the full inverse precision. The mean
of a varying quadratic insertion therefore has a direct insertion term
and the complete connected fluctuation. The matrices need not commute,
and every Gaussian state in the path retains its original covariance.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace GeneratedFoundations.Operations.FiniteMatrixGaussian

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The two connected pairings combine into one trace only after symmetry
of the actual quadratic insertion has been used. -/
theorem score_covariance_trace {P : Matrix ι ι ℝ} (hP : P.PosDef)
    (V W : Matrix ι ι ℝ) (hW : W.IsSymm) :
    cov[score V, score W; law P] = Matrix.trace (P⁻¹ * V * P⁻¹ * W) / 2 := by
  let C := P⁻¹
  have hC (i j : ι) : C j i = C i j := by
    simpa only [star_trivial] using hP.inv.isHermitian.apply i j
  have hp : (∑ i, ∑ j, ∑ k, ∑ l, V i j * W k l * C i k * C j l) =
      ∑ i, ∑ j, ∑ k, ∑ l, V i j * W k l * C i l * C j k := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    rw [hW.apply k l]
  have ht : Matrix.trace (V * (C * (W * C))) =
      ∑ i, ∑ j, ∑ k, ∑ l, V i j * W k l * C i l * C j k := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    rw [hC i l]
    ring
  have ho (f : ι → ι → ι → ι → ℝ) :
      (∑ i, ∑ k, ∑ j, ∑ l, f i j k l) = ∑ i, ∑ j, ∑ k, ∑ l, f i j k l := by
    apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_comm
  have he : Matrix.trace (P⁻¹ * V * P⁻¹ * W) = Matrix.trace (V * (C * (W * C))) := by
    simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm P⁻¹ (V * (P⁻¹ * W))]
    simp only [Matrix.mul_assoc, C]
  rw [score_covariance hP, ho, he, ht]
  have hd : (∑ i, ∑ j, ∑ k, ∑ l,
      (V i j * W k l / 4) * (C i k * C j l + C i l * C j k)) =
      (∑ i, ∑ j, ∑ k, ∑ l, V i j * W k l * C i k * C j l) / 4 +
        (∑ i, ∑ j, ∑ k, ∑ l, V i j * W k l * C i l * C j k) / 4 := by
    simp only [Finset.sum_div, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  change (∑ i, ∑ j, ∑ k, ∑ l,
    (V i j * W k l / 4) * (C i k * C j l + C i l * C j k)) = _
  rw [hd, hp]
  ring

private def traceMap : Matrix ι ι ℝ →L[ℝ] ℝ :=
  (Matrix.traceLinearMap ι ℝ ℝ).toContinuousLinearMap

theorem inverse_hasDerivAt {P : ℝ → Matrix ι ι ℝ} {V : Matrix ι ι ℝ} {t : ℝ}
    (hP : (P t).PosDef) (hV : HasDerivAt P V t) :
    HasDerivAt (fun s => (P s)⁻¹) (-(P t)⁻¹ * V * (P t)⁻¹) t := by
  let a := hP.isUnit.unit
  have ha : (a : Matrix ι ι ℝ) = P t := hP.isUnit.unit_spec
  have hi : (↑a⁻¹ : Matrix ι ι ℝ) = (P t)⁻¹ := by
    apply covariance_unique hP
    rw [← ha]
    exact a.mul_inv
  have hd := hasFDerivAt_ringInverse (𝕜 := ℝ) a
  rw [ha] at hd
  have h := hd.comp_hasDerivAt t hV
  simpa only [Function.comp_def, neg_apply,
    ContinuousLinearMap.mulLeftRight_apply, hi, ← Matrix.nonsing_inv_eq_ringInverse,
    Matrix.neg_mul] using! h

/-- The derivative is taken in the actual varied Gaussian state. It is
not a definition of a response or a fixed-state covariance proxy. -/
theorem varying_mean_hasDerivAt
    (P V : ℝ → Matrix ι ι ℝ) (t : ℝ) (Y W : Matrix ι ι ℝ)
    (hP : ∀ s, (P s).PosDef)
    (hY : HasDerivAt P Y t) (hW : HasDerivAt V W t) (hYs : Y.IsSymm) :
    HasDerivAt (fun s => ∫ x, score (V s) x ∂law (P s))
      ((∫ x, score W x ∂law (P t)) -
        cov[score (V t), score Y; law (P t)]) t := by
  have hi := inverse_hasDerivAt (hP t) hY
  have hd := ((traceMap (ι := ι)).hasFDerivAt.comp_hasDerivAt t (hi.mul hW)).div_const 2
  have he (s : ℝ) : (∫ x, score (V s) x ∂law (P s)) =
      Matrix.trace ((P s)⁻¹ * V s) / 2 := score_mean_trace (hP s) _
  simp only [he, score_mean_trace (hP t), score_covariance_trace (hP t) _ _ hYs]
  convert hd using 1
  · rfl
  change (Matrix.trace ((P t)⁻¹ * W) / 2 -
      Matrix.trace ((P t)⁻¹ * V t * (P t)⁻¹ * Y) / 2) =
    Matrix.trace ((-(P t)⁻¹ * Y * (P t)⁻¹) * V t + (P t)⁻¹ * W) / 2
  simp only [Matrix.trace_add, Matrix.neg_mul, Matrix.trace_neg]
  have hc : Matrix.trace ((P t)⁻¹ * Y * (P t)⁻¹ * V t) =
      Matrix.trace ((P t)⁻¹ * V t * (P t)⁻¹ * Y) := by
    simpa only [Matrix.mul_assoc] using
      Matrix.trace_mul_comm ((P t)⁻¹ * Y) ((P t)⁻¹ * V t)
  rw [hc]
  ring

/-- The mean of the original quadratic energy counts the full real
coefficient space, independently of non-diagonal precision changes. -/
theorem precision_score_mean {P : Matrix ι ι ℝ} (hP : P.PosDef) :
    (∫ x, score P x ∂law P) = (Fintype.card ι : ℝ) / 2 := by
  rw [score_mean_trace hP, inverse_mul_precision hP, Matrix.trace_one]

theorem precision_score_variance {P : Matrix ι ι ℝ} (hP : P.PosDef) :
    Var[score P; law P] = (Fintype.card ι : ℝ) / 2 := by
  rw [← covariance_self (score_memLp_two P P).aemeasurable,
    score_covariance_trace hP P P hP.isHermitian.isSymm,
    inverse_mul_precision hP, Matrix.one_mul, inverse_mul_precision hP, Matrix.trace_one]

end GeneratedFoundations.Operations.FiniteMatrixGaussian

module

public import GeneratedFoundations.Arithmetic.HistoryHaarSectionConnectionResponse
public import GeneratedFoundations.Arithmetic.HistoryHaarSectionGeometricVariation

/-!
# Joint connection and geometric response of the original section action

The observation direction has a connection component and a logarithmic
spatial-metric component. Both act on the same full precision matrix.
The mixed direct insertion is differentiated before any covariance is
taken; its connection--geometry terms and all off-diagonal entries remain.

The spatial homothety is that of the original Haar action. Its scalar
precision is `c * Gram(D_A) + c^3 * C_F`. Frequency-window motion is not
identified with this spatial homothety. The statements below hold on one
original finite support; the separate moving-window boundary must be
included when that support changes.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace GeneratedFoundations.Arithmetic.HistoryHaarSectionCollectiveResponse

open HistoryHaarMatrixCurvature (Coefficients)
open HistoryHaarSectionAction
open HistoryHaarSectionConnectionGaussian (RealIndex Space realSection sourceSection)
open HistoryHaarSectionConnectionResponse (currentMatrix secondMatrix)
open Operations.FiniteMatrixGaussian (score)

local instance (N : ℕ) (B : ℝ) : DecidableEq (RealIndex N B 0) := Classical.decEq _
local instance (N : ℕ) : InnerProductSpace ℝ (DerivativeFields N) :=
  InnerProductSpace.complexToReal
local instance (N : ℕ) : InnerProductSpace ℝ (StateFields N) :=
  InnerProductSpace.complexToReal

def kineticMatrix (N : ℕ) (B : ℝ) (A : Coefficients N) :
    Matrix (RealIndex N B 0) (RealIndex N B 0) ℝ :=
  Matrix.gram ℝ (fun i => covariantDerivative N A (realSection N B 0 i))

def precision (N : ℕ) (B : ℝ) (A : Coefficients N) (c : ℝ) :
    Matrix (RealIndex N B 0) (RealIndex N B 0) ℝ :=
  c • kineticMatrix N B A + (c ^ 3 * HistoryDefiningResponse.coefficient N) • 1

theorem precision_posDef (N : ℕ) (B : ℝ) (A : Coefficients N)
    {c : ℝ} (hc : 0 < c) : (precision N B A c).PosDef := by
  exact Matrix.PosDef.posSemidef_add ((Matrix.posSemidef_gram ℝ _).smul hc.le)
    (Matrix.PosDef.one.smul (mul_pos (pow_pos hc _) (HistoryDefiningResponse.coefficient_pos N)))

/-- This precision is the section part of the original geometrically
varied action, with the original curvature contribution left explicit. -/
theorem score_eq_original (N : ℕ) (B : ℝ) (A : Coefficients N)
    {c : ℝ} (hc : 0 < c) (x : Space N B 0) :
    HistoryHaarSectionGeometricVariation.geometricAction N A (sourceSection N B 0 x) c =
      HistoryHaarMatrixCurvature.action N A / c + score (precision N B A c) x := by
  have hf : x ⬝ᵥ x = ‖sectionField N (sourceSection N B 0 x)‖ ^ 2 := by
    have hg := Matrix.star_dotProduct_gram_mulVec
      (fun i : RealIndex N B 0 => sectionField N (realSection N B 0 i))
      (fun i => x i) (fun i => x i)
    simp only [star_trivial, HistoryHaarSectionConnectionGaussian.realSection_field_gram,
      Matrix.one_mulVec, real_inner_self_eq_norm_sq] at hg
    rw [HistoryHaarSectionConnectionGaussian.section_field]
    exact hg
  have hs : score (precision N B A c) x =
      c * ‖covariantDerivative N A (sourceSection N B 0 x)‖ ^ 2 / 2 +
        c ^ 3 * HistoryDefiningResponse.coefficient N *
          ‖sectionField N (sourceSection N B 0 x)‖ ^ 2 / 2 := by
    rw [Operations.FiniteMatrixGaussian.score_eq_dotProduct, precision,
      Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    have hg := Matrix.star_dotProduct_gram_mulVec
      (fun i : RealIndex N B 0 => covariantDerivative N A (realSection N B 0 i))
      (fun i => x i) (fun i => x i)
    simp only [star_trivial, real_inner_self_eq_norm_sq] at hg
    have hk : x ⬝ᵥ kineticMatrix N B A *ᵥ x =
        ‖covariantDerivative N A (sourceSection N B 0 x)‖ ^ 2 := by
      rw [HistoryHaarSectionConnectionGaussian.section_covariant]
      exact hg
    rw [hk, hf]
    ring
  rw [hs, HistoryHaarSectionGeometricVariation.geometricAction_exact N A _ hc.ne']
  unfold HistoryHaarSectionGeometricVariation.curvatureEnergy
    HistoryHaarSectionGeometricVariation.kineticEnergy
    HistoryHaarSectionGeometricVariation.restoringEnergy
  ring

/-- The component `v` differentiates log spatial scale, so a positive
initial geometry remains positive along the entire actual path. -/
def scalePath (c v t : ℝ) : ℝ := c * Real.exp (v * t)

def firstMatrix (N : ℕ) (B : ℝ) (A X : Coefficients N) (c v : ℝ) :
    Matrix (RealIndex N B 0) (RealIndex N B 0) ℝ :=
  c • currentMatrix N B 0 A X + (v * c) • kineticMatrix N B A +
    (3 * v * c ^ 3 * HistoryDefiningResponse.coefficient N) • 1

def directMatrix (N : ℕ) (B : ℝ) (A X Y : Coefficients N) (c v w : ℝ) :
    Matrix (RealIndex N B 0) (RealIndex N B 0) ℝ :=
  c • secondMatrix N B 0 X Y +
    (w * c) • currentMatrix N B 0 A X + (v * c) • currentMatrix N B 0 A Y +
    (v * w * c) • kineticMatrix N B A +
    (9 * v * w * c ^ 3 * HistoryDefiningResponse.coefficient N) • 1

private theorem scalePath_hasDerivAt (c v : ℝ) :
    HasDerivAt (scalePath c v) (v * c) 0 := by
  have h := (((hasDerivAt_id (0 : ℝ)).const_mul v).exp).const_mul c
  simpa [scalePath, mul_comm, mul_left_comm, mul_assoc] using! h

private theorem kineticMatrix_hasDerivAt (N : ℕ) (B : ℝ) (A Y : Coefficients N) :
    HasDerivAt (fun t : ℝ => kineticMatrix N B (A + (t : ℂ) • Y))
      (currentMatrix N B 0 A Y) 0 := by
  have h := (HistoryHaarSectionConnectionResponse.realPrecision_hasDerivAt N B 0 A Y).sub_const
    ((HistoryDefiningResponse.coefficient N) • (1 : Matrix (RealIndex N B 0) _ ℝ))
  simpa only [HistoryHaarSectionConnectionGaussian.realPrecision, zero_pow (by decide : 2 ≠ 0),
    add_zero, add_sub_cancel_right, kineticMatrix] using h

theorem precision_collective_hasDerivAt (N : ℕ) (B : ℝ) (A Y : Coefficients N) (c w : ℝ) :
    HasDerivAt (fun t : ℝ => precision N B (A + (t : ℂ) • Y) (scalePath c w t))
      (firstMatrix N B A Y c w) 0 := by
  have hc := scalePath_hasDerivAt c w
  have hk := kineticMatrix_hasDerivAt N B A Y
  have h := (hc.smul hk).add
    (((hc.pow 3).mul_const (HistoryDefiningResponse.coefficient N)).smul_const
      (1 : Matrix (RealIndex N B 0) _ ℝ))
  change HasDerivAt (fun t : ℝ => precision N B (A + (t : ℂ) • Y) (scalePath c w t)) _ 0 at h
  apply h.congr_deriv
  simp only [scalePath, mul_zero, Real.exp_zero, mul_one, Complex.ofReal_zero,
    zero_smul, add_zero, firstMatrix]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem firstMatrix_collective_hasDerivAt (N : ℕ) (B : ℝ)
    (A X Y : Coefficients N) (c v w : ℝ) :
    HasDerivAt (fun t : ℝ => firstMatrix N B (A + (t : ℂ) • Y) X (scalePath c w t) v)
      (directMatrix N B A X Y c v w) 0 := by
  have hc := scalePath_hasDerivAt c w
  have hv := HistoryHaarSectionConnectionResponse.currentMatrix_hasDerivAt N B 0 A X Y 0
  have hk := kineticMatrix_hasDerivAt N B A Y
  have h := ((hc.smul hv).add ((hc.const_mul v).smul hk)).add
    ((((hc.pow 3).const_mul (3 * v)).mul_const (HistoryDefiningResponse.coefficient N)).smul_const
      (1 : Matrix (RealIndex N B 0) _ ℝ))
  change HasDerivAt
    (fun t : ℝ => firstMatrix N B (A + (t : ℂ) • Y) X (scalePath c w t) v) _ 0 at h
  apply h.congr_deriv
  simp only [scalePath, mul_zero, Real.exp_zero, mul_one, Complex.ofReal_zero,
    zero_smul, add_zero, directMatrix]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem firstMatrix_symmetric (N : ℕ) (B : ℝ) (A X : Coefficients N) (c v : ℝ) :
    (firstMatrix N B A X c v).IsSymm := by
  exact (((HistoryHaarSectionConnectionResponse.currentMatrix_symmetric N B 0 A X).smul c).add
    ((Matrix.posSemidef_gram ℝ _).isHermitian.isSymm.smul (v * c))).add
      (Matrix.isSymm_one.smul _)

def law (N : ℕ) (B : ℝ) (A : Coefficients N) (c : ℝ) : Measure (Space N B 0) :=
  Operations.FiniteMatrixGaussian.law (precision N B A c)

private def scoreMap (N : ℕ) (B : ℝ) (x : Space N B 0) :
    Matrix (RealIndex N B 0) (RealIndex N B 0) ℝ →L[ℝ] ℝ :=
  ({ toFun := fun P => score P x
     map_add' := by
       intro P Q
       simp only [score, Matrix.add_apply, add_div, add_mul, Finset.sum_add_distrib]
     map_smul' := by
       intro r P
       simp only [score, Matrix.smul_apply, smul_eq_mul, mul_div_assoc,
         mul_assoc, ← Finset.mul_sum, RingHom.id_apply] } :
    Matrix (RealIndex N B 0) (RealIndex N B 0) ℝ →ₗ[ℝ] ℝ).toContinuousLinearMap

/-- In particular the collective insertion is an actual action derivative,
not a covariance selected for a favorable sign. -/
theorem score_collective_hasDerivAt (N : ℕ) (B : ℝ)
    (A Y : Coefficients N) (c w : ℝ) (x : Space N B 0) :
    HasDerivAt (fun t : ℝ => score
      (precision N B (A + (t : ℂ) • Y) (scalePath c w t)) x)
      (score (firstMatrix N B A Y c w) x) 0 := by
  exact (scoreMap N B x).hasFDerivAt.comp_hasDerivAt 0
    (precision_collective_hasDerivAt N B A Y c w)

/-- The current derivative is evaluated in the jointly varied original
Gaussian. Both collective directions enter its connected covariance. -/
theorem collective_mean_hasDerivAt (N : ℕ) (B : ℝ) (A X Y : Coefficients N)
    {c : ℝ} (hc : 0 < c) (v w : ℝ) :
    HasDerivAt (fun t : ℝ => ∫ x,
      score (firstMatrix N B (A + (t : ℂ) • Y) X (scalePath c w t) v) x
        ∂law N B (A + (t : ℂ) • Y) (scalePath c w t))
      ((∫ x, score (directMatrix N B A X Y c v w) x ∂law N B A c) -
        cov[score (firstMatrix N B A X c v), score (firstMatrix N B A Y c w); law N B A c]) 0 := by
  have h := Operations.FiniteMatrixGaussian.varying_mean_hasDerivAt
    (fun t => precision N B (A + (t : ℂ) • Y) (scalePath c w t))
    (fun t => firstMatrix N B (A + (t : ℂ) • Y) X (scalePath c w t) v) 0
    (firstMatrix N B A Y c w) (directMatrix N B A X Y c v w)
    (fun t => precision_posDef N B _ (mul_pos hc (Real.exp_pos _)))
    (precision_collective_hasDerivAt N B A Y c w)
    (firstMatrix_collective_hasDerivAt N B A X Y c v w)
    (firstMatrix_symmetric N B A Y c w)
  simpa only [scalePath, mul_zero, Real.exp_zero, mul_one, Complex.ofReal_zero,
    zero_smul, add_zero, law] using! h

def curvatureCurrent (N : ℕ) (X : Coefficients N) (c v t : ℝ) : ℝ :=
  HistoryHaarMatrixCurvature.rayDerivative N X t / scalePath c v t -
    v * HistoryHaarMatrixCurvature.action N ((t : ℂ) • X) / scalePath c v t

private theorem scalePath_derivative (c v t : ℝ) :
    HasDerivAt (scalePath c v) (v * scalePath c v t) t := by
  have h := (((hasDerivAt_id t).const_mul v).exp).const_mul c
  simpa [scalePath, mul_comm, mul_left_comm, mul_assoc] using! h

theorem curvatureCurrent_is_action_derivative (N : ℕ) (X : Coefficients N)
    {c : ℝ} (hc : 0 < c) (v t : ℝ) :
    HasDerivAt (fun s : ℝ => HistoryHaarMatrixCurvature.action N ((s : ℂ) • X) /
      scalePath c v s) (curvatureCurrent N X c v t) t := by
  have hn : scalePath c v t ≠ 0 := (mul_pos hc (Real.exp_pos _)).ne'
  apply ((HistoryHaarMatrixCurvature.action_hasDerivAt N X t).div
    (scalePath_derivative c v t) hn).congr_deriv
  unfold curvatureCurrent
  field_simp

theorem curvatureCurrent_hasDerivAt_zero (N : ℕ) (X : Coefficients N)
    {c : ℝ} (hc : 0 < c) (v : ℝ) :
    HasDerivAt (curvatureCurrent N X c v)
      (‖HistoryHaarMatrixCurvature.differentiated N X‖ ^ 2 / c) 0 := by
  have hd : HasDerivAt (HistoryHaarMatrixCurvature.rayDerivative N X)
      (‖HistoryHaarMatrixCurvature.differentiated N X‖ ^ 2) 0 := by
    convert HistoryHaarMatrixCurvature.secondDeriv_zero N X using 1
    funext t
    exact (HistoryHaarMatrixCurvature.action_hasDerivAt N X t).deriv.symm
  have ha := HistoryHaarMatrixCurvature.action_hasDerivAt N X 0
  have hs := scalePath_hasDerivAt c v
  have hn : scalePath c v 0 ≠ 0 := by simpa [scalePath] using hc.ne'
  have h := (hd.div hs hn).sub ((ha.div hs hn).const_mul v)
  change HasDerivAt (fun t => HistoryHaarMatrixCurvature.rayDerivative N X t / scalePath c v t -
    v * (HistoryHaarMatrixCurvature.action N ((t : ℂ) • X) / scalePath c v t)) _ 0 at h
  have he : (fun t => HistoryHaarMatrixCurvature.rayDerivative N X t / scalePath c v t -
      v * (HistoryHaarMatrixCurvature.action N ((t : ℂ) • X) / scalePath c v t)) =
      curvatureCurrent N X c v := by
    funext t
    unfold curvatureCurrent
    ring
  rw [he] at h
  apply h.congr_deriv
  have hz : HistoryHaarMatrixCurvature.action N 0 = 0 :=
    HistoryHaarSectionGeometricVariation.curvatureEnergy_zero N
  simp only [scalePath, mul_zero, Real.exp_zero, mul_one,
    HistoryHaarMatrixCurvature.rayDerivative, zero_mul, zero_pow (by decide : 2 ≠ 0),
    zero_pow (by decide : 3 ≠ 0), add_zero, Complex.ofReal_zero, zero_smul,
    hz, zero_div, sub_zero]
  field_simp

/-- The full diagonal collective response at the vacuum background keeps
the original curvature Hessian as well as the complete scalar response.
Neither geometric--connection interference nor direct insertions are
removed from the scalar term. -/
theorem full_collective_mean_hasDerivAt_zero (N : ℕ) (B : ℝ)
    (X : Coefficients N) {c : ℝ} (hc : 0 < c) (v : ℝ) :
    HasDerivAt (fun t : ℝ => curvatureCurrent N X c v t + ∫ x,
      score (firstMatrix N B ((t : ℂ) • X) X (scalePath c v t) v) x
        ∂law N B ((t : ℂ) • X) (scalePath c v t))
      (‖HistoryHaarMatrixCurvature.differentiated N X‖ ^ 2 / c +
        ((∫ x, score (directMatrix N B 0 X X c v v) x ∂law N B 0 c) -
          cov[score (firstMatrix N B 0 X c v), score (firstMatrix N B 0 X c v);
            law N B 0 c])) 0 := by
  have hs := collective_mean_hasDerivAt N B 0 X X hc v v
  simp only [zero_add] at hs
  exact (curvatureCurrent_hasDerivAt_zero N X hc v).add hs

structure Conclusions : Prop where
  original_action : ∀ N B A c, 0 < c → ∀ x,
    HistoryHaarSectionGeometricVariation.geometricAction N A (sourceSection N B 0 x) c =
      HistoryHaarMatrixCurvature.action N A / c + score (precision N B A c) x
  collective_response : ∀ N B A X Y c, 0 < c → ∀ v w,
    HasDerivAt (fun t : ℝ => ∫ x,
      score (firstMatrix N B (A + (t : ℂ) • Y) X (scalePath c w t) v) x
        ∂law N B (A + (t : ℂ) • Y) (scalePath c w t))
      ((∫ x, score (directMatrix N B A X Y c v w) x ∂law N B A c) -
        cov[score (firstMatrix N B A X c v), score (firstMatrix N B A Y c w); law N B A c]) 0

theorem generated : Conclusions where
  original_action := fun N B A _ hc x => score_eq_original N B A hc x
  collective_response := fun N B A X Y _ hc v w => collective_mean_hasDerivAt N B A X Y hc v w

end GeneratedFoundations.Arithmetic.HistoryHaarSectionCollectiveResponse

module

public import GeneratedFoundations.Arithmetic.HistoryHaarSectionConnectionGaussian
public import GeneratedFoundations.Operations.FiniteMatrixGaussianVariation

/-!
# Common responses of the original connection current

Both insertion matrices are obtained from the connection variation of the
original action. Their expectations and connected covariance are taken in
one full real Gaussian law at that same connection. Differentiating the
actual current mean in the varied state gives the direct second mean
minus the full connected fluctuation.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ComplexConjugate Matrix Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace GeneratedFoundations.Arithmetic.HistoryHaarSectionConnectionResponse

open HistoryHaarMatrixCurvature (Coefficients)
open HistoryHaarSectionAction
open HistoryHaarSectionConnectionVariation
open HistoryHaarSectionConnectionGaussian (RealIndex Space realSection sourceSection realPrecision law)
open Operations.FiniteMatrixGaussian (score)

local instance (N : ℕ) (B u : ℝ) : DecidableEq (RealIndex N B u) := Classical.decEq _

local instance (N : ℕ) : InnerProductSpace ℝ (DerivativeFields N) :=
  InnerProductSpace.complexToReal

private theorem inner_real_sum {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (v w : ι → E) (x : ι → ℝ) :
    inner ℝ (∑ i, x i • v i) (∑ j, x j • w j) =
      ∑ i, ∑ j, (x i * x j) * inner ℝ (v i) (w j) := by
  simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem section_connection (N : ℕ) (B u : ℝ) (X : Coefficients N) (x : Space N B u) :
    connectionDerivative N X (sourceSection N B u x) =
      ∑ i, x i • connectionDerivative N X (realSection N B u i) := by
  change connectionLinear N X _ = _
  simp only [HistoryHaarSectionConnectionGaussian.sourceSection, map_sum, map_smul,
    connectionLinear, Complex.coe_smul]
  rfl

def currentMatrix (N : ℕ) (B u : ℝ) (A X : Coefficients N) :
    Matrix (RealIndex N B u) (RealIndex N B u) ℝ := fun i j =>
  (firstVertex N A X (realSection N B u i) (realSection N B u j)).re

def secondMatrix (N : ℕ) (B u : ℝ) (X Y : Coefficients N) :
    Matrix (RealIndex N B u) (RealIndex N B u) ℝ := fun i j =>
  (secondVertex N X Y (realSection N B u i) (realSection N B u j)).re

def current (N : ℕ) (B u : ℝ) (A X : Coefficients N) : Space N B u → ℝ :=
  score (currentMatrix N B u A X)

def directSecond (N : ℕ) (B u : ℝ) (X Y : Coefficients N) : Space N B u → ℝ :=
  score (secondMatrix N B u X Y)

/-- The finite quadratic insertion is precisely the original current on
the recombined complex section. Both quadratures participate. -/
theorem current_eq_original (N : ℕ) (B u : ℝ) (A X : Coefficients N)
    (x : Space N B u) :
    current N B u A X x =
      (firstVertex N A X (sourceSection N B u x) (sourceSection N B u x)).re / 2 := by
  classical
  unfold current currentMatrix score
  change (∑ i, ∑ j, ((inner ℝ
    (covariantDerivative N A (realSection N B u i))
    (connectionDerivative N X (realSection N B u j)) + inner ℝ
    (connectionDerivative N X (realSection N B u i))
    (covariantDerivative N A (realSection N B u j))) / 2) * (x i * x j)) =
      (inner ℝ (covariantDerivative N A (sourceSection N B u x))
        (connectionDerivative N X (sourceSection N B u x)) +
       inner ℝ (connectionDerivative N X (sourceSection N B u x))
        (covariantDerivative N A (sourceSection N B u x))) / 2
  have hDK : inner ℝ (covariantDerivative N A (sourceSection N B u x))
      (connectionDerivative N X (sourceSection N B u x)) =
      ∑ i, ∑ j, (x i * x j) * inner ℝ
        (covariantDerivative N A (realSection N B u i))
        (connectionDerivative N X (realSection N B u j)) := by
    rw [HistoryHaarSectionConnectionGaussian.section_covariant, section_connection]
    exact inner_real_sum _ _ (fun i => x i)
  have hKD : inner ℝ (connectionDerivative N X (sourceSection N B u x))
      (covariantDerivative N A (sourceSection N B u x)) =
      ∑ i, ∑ j, (x i * x j) * inner ℝ
        (connectionDerivative N X (realSection N B u i))
        (covariantDerivative N A (realSection N B u j)) := by
    rw [HistoryHaarSectionConnectionGaussian.section_covariant, section_connection]
    exact inner_real_sum _ _ (fun i => x i)
  rw [hDK, hKD]
  simp only [← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem directSecond_eq_original (N : ℕ) (B u : ℝ) (X Y : Coefficients N)
    (x : Space N B u) :
    directSecond N B u X Y x =
      (secondVertex N X Y (sourceSection N B u x) (sourceSection N B u x)).re / 2 := by
  classical
  unfold directSecond secondMatrix score
  change (∑ i, ∑ j, ((inner ℝ
    (connectionDerivative N X (realSection N B u i))
    (connectionDerivative N Y (realSection N B u j)) + inner ℝ
    (connectionDerivative N Y (realSection N B u i))
    (connectionDerivative N X (realSection N B u j))) / 2) * (x i * x j)) =
      (inner ℝ (connectionDerivative N X (sourceSection N B u x))
        (connectionDerivative N Y (sourceSection N B u x)) +
       inner ℝ (connectionDerivative N Y (sourceSection N B u x))
        (connectionDerivative N X (sourceSection N B u x))) / 2
  have hXY : inner ℝ (connectionDerivative N X (sourceSection N B u x))
      (connectionDerivative N Y (sourceSection N B u x)) =
      ∑ i, ∑ j, (x i * x j) * inner ℝ
        (connectionDerivative N X (realSection N B u i))
        (connectionDerivative N Y (realSection N B u j)) := by
    rw [section_connection, section_connection]
    exact inner_real_sum _ _ (fun i => x i)
  have hYX : inner ℝ (connectionDerivative N Y (sourceSection N B u x))
      (connectionDerivative N X (sourceSection N B u x)) =
      ∑ i, ∑ j, (x i * x j) * inner ℝ
        (connectionDerivative N Y (realSection N B u i))
        (connectionDerivative N X (realSection N B u j)) := by
    rw [section_connection, section_connection]
    exact inner_real_sum _ _ (fun i => x i)
  rw [hXY, hYX]
  simp only [← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem current_is_action_derivative (N : ℕ) (B u : ℝ) (A X : Coefficients N)
    (x : Space N B u) :
    HasDerivAt (fun t : ℝ => sectionAction N (A + (t : ℂ) • X) (sourceSection N B u x))
      (current N B u A X x) 0 := by
  rw [current_eq_original]
  simpa only [zero_mul, add_zero] using
    sectionAction_hasDerivAt N A X (sourceSection N B u x) 0

theorem directSecond_is_current_derivative (N : ℕ) (B u : ℝ) (A X Y : Coefficients N)
    (x : Space N B u) :
    HasDerivAt (fun t : ℝ => current N B u (A + (t : ℂ) • Y) X x)
      (directSecond N B u X Y x) 0 := by
  simp only [current_eq_original, directSecond_eq_original]
  exact firstVertex_hasDerivAt N A X Y _ _ 0

theorem currentMatrix_symmetric (N : ℕ) (B u : ℝ) (A X : Coefficients N) :
    (currentMatrix N B u A X).IsSymm := by
  ext i j
  have h := congrArg Complex.re
    (firstVertex_hermitian N A X (realSection N B u i) (realSection N B u j))
  simpa only [currentMatrix, Matrix.transpose_apply, Complex.conj_re] using h

theorem secondMatrix_symmetric (N : ℕ) (B u : ℝ) (X Y : Coefficients N) :
    (secondMatrix N B u X Y).IsSymm := by
  ext i j
  have h := congrArg Complex.re
    (secondVertex_hermitian N X Y (realSection N B u i) (realSection N B u j))
  simpa only [secondMatrix, Matrix.transpose_apply, Complex.conj_re] using h

theorem current_mean (N : ℕ) (B u : ℝ) (A X : Coefficients N) :
    (∫ x, current N B u A X x ∂law N B u A) =
      Matrix.trace ((realPrecision N B u A)⁻¹ * currentMatrix N B u A X) / 2 :=
  Operations.FiniteMatrixGaussian.score_mean_trace
    (HistoryHaarSectionConnectionGaussian.realPrecision_posDef N B u A) _

theorem directSecond_mean (N : ℕ) (B u : ℝ) (A X Y : Coefficients N) :
    (∫ x, directSecond N B u X Y x ∂law N B u A) =
      Matrix.trace ((realPrecision N B u A)⁻¹ * secondMatrix N B u X Y) / 2 :=
  Operations.FiniteMatrixGaussian.score_mean_trace
    (HistoryHaarSectionConnectionGaussian.realPrecision_posDef N B u A) _

def connected (N : ℕ) (B u : ℝ) (A X Y : Coefficients N) : ℝ :=
  cov[current N B u A X, current N B u A Y; law N B u A]

/-- All off-diagonal inverse entries, both Wick pairings and both actual
vertices occur under one finite sum. -/
theorem connected_eq (N : ℕ) (B u : ℝ) (A X Y : Coefficients N) :
    connected N B u A X Y =
      ∑ i, ∑ k, ∑ j, ∑ l,
        (currentMatrix N B u A X i j * currentMatrix N B u A Y k l / 4) *
          ((realPrecision N B u A)⁻¹ i k * (realPrecision N B u A)⁻¹ j l +
            (realPrecision N B u A)⁻¹ i l * (realPrecision N B u A)⁻¹ j k) :=
  Operations.FiniteMatrixGaussian.score_covariance
    (HistoryHaarSectionConnectionGaussian.realPrecision_posDef N B u A) _ _

theorem connected_diagonal_nonneg (N : ℕ) (B u : ℝ) (A X : Coefficients N) :
    0 ≤ connected N B u A X X := by
  rw [connected, covariance_self]
  · exact variance_nonneg _ _
  · exact (Operations.FiniteMatrixGaussian.score_memLp_two
      (realPrecision N B u A) (currentMatrix N B u A X)).aemeasurable

/-- The full response expression retains the direct term. It is not
identified with the nonnegative connected fluctuation alone. -/
def response (N : ℕ) (B u : ℝ) (A X Y : Coefficients N) : ℝ :=
  (∫ x, directSecond N B u X Y x ∂law N B u A) - connected N B u A X Y

theorem response_eq (N : ℕ) (B u : ℝ) (A X Y : Coefficients N) :
    response N B u A X Y =
      Matrix.trace ((realPrecision N B u A)⁻¹ * secondMatrix N B u X Y) / 2 -
        connected N B u A X Y := by
  rw [response, directSecond_mean]

/-- The original precision changes quadratically, with every mixed entry
retained. This is an exact connection path, not a truncated expansion. -/
theorem realPrecision_connection_ray (N : ℕ) (B u : ℝ)
    (A Y : Coefficients N) (t : ℝ) :
    realPrecision N B u (A + (t : ℂ) • Y) = realPrecision N B u A +
      t • currentMatrix N B u A Y + t ^ 2 • Matrix.gram ℝ
        (fun i : RealIndex N B u => connectionDerivative N Y (realSection N B u i)) := by
  have hg (ψ ξ : Sections N) :
      inner ℝ (covariantDerivative N (A + (t : ℂ) • Y) ψ)
        (covariantDerivative N (A + (t : ℂ) • Y) ξ) =
      inner ℝ (covariantDerivative N A ψ) (covariantDerivative N A ξ) +
        t * (firstVertex N A Y ψ ξ).re +
        t ^ 2 * inner ℝ (connectionDerivative N Y ψ) (connectionDerivative N Y ξ) := by
    change (inner ℂ (covariantDerivative N (A + (t : ℂ) • Y) ψ)
      (covariantDerivative N (A + (t : ℂ) • Y) ξ)).re = _
    simp only [covariantDerivative_connection_ray, inner_add_left, inner_add_right,
      inner_smul_left (𝕜 := ℂ), inner_smul_right (𝕜 := ℂ), Complex.conj_ofReal,
      Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, firstVertex]
    change _ = (inner ℂ (covariantDerivative N A ψ) (covariantDerivative N A ξ)).re +
      t * ((inner ℂ (covariantDerivative N A ψ) (connectionDerivative N Y ξ) +
        inner ℂ (connectionDerivative N Y ψ) (covariantDerivative N A ξ)).re) +
      t ^ 2 * (inner ℂ (connectionDerivative N Y ψ) (connectionDerivative N Y ξ)).re
    simp only [Complex.add_re]
    ring
  ext i j
  simp only [realPrecision, Matrix.add_apply, Matrix.smul_apply, Matrix.gram_apply,
    smul_eq_mul, currentMatrix, hg]
  ring

theorem currentMatrix_connection_ray (N : ℕ) (B u : ℝ)
    (A X Y : Coefficients N) (t : ℝ) :
    currentMatrix N B u (A + (t : ℂ) • Y) X =
      currentMatrix N B u A X + t • secondMatrix N B u X Y := by
  ext i j
  simp only [currentMatrix, firstVertex_connection_ray, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, secondMatrix, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem realPrecision_hasDerivAt (N : ℕ) (B u : ℝ) (A Y : Coefficients N) :
    HasDerivAt (fun t : ℝ => realPrecision N B u (A + (t : ℂ) • Y))
      (currentMatrix N B u A Y) 0 := by
  have h := ((hasDerivAt_const (0 : ℝ) (realPrecision N B u A)).add
    ((hasDerivAt_id (0 : ℝ)).smul_const (currentMatrix N B u A Y))).add
      (((hasDerivAt_id (0 : ℝ)).pow 2).smul_const (Matrix.gram ℝ
        (fun i : RealIndex N B u => connectionDerivative N Y (realSection N B u i))))
  simp only [realPrecision_connection_ray]
  simpa using! h

theorem currentMatrix_hasDerivAt (N : ℕ) (B u : ℝ)
    (A X Y : Coefficients N) (t : ℝ) :
    HasDerivAt (fun s : ℝ => currentMatrix N B u (A + (s : ℂ) • Y) X)
      (secondMatrix N B u X Y) t := by
  have h := (hasDerivAt_const t (currentMatrix N B u A X)).add
    ((hasDerivAt_id t).smul_const (secondMatrix N B u X Y))
  simpa only [currentMatrix_connection_ray, id_eq, one_smul, zero_add] using! h

theorem connected_trace (N : ℕ) (B u : ℝ) (A X Y : Coefficients N) :
    connected N B u A X Y = Matrix.trace
      ((realPrecision N B u A)⁻¹ * currentMatrix N B u A X *
        (realPrecision N B u A)⁻¹ * currentMatrix N B u A Y) / 2 :=
  Operations.FiniteMatrixGaussian.score_covariance_trace
    (HistoryHaarSectionConnectionGaussian.realPrecision_posDef N B u A) _ _
    (currentMatrix_symmetric N B u A Y)

/-- The complete response is the actual change of the current mean,
including the change of the original Gaussian state. -/
theorem current_mean_hasDerivAt (N : ℕ) (B u : ℝ) (A X Y : Coefficients N) :
    HasDerivAt (fun t : ℝ => ∫ x,
      current N B u (A + (t : ℂ) • Y) X x ∂law N B u (A + (t : ℂ) • Y))
      (response N B u A X Y) 0 := by
  have h := Operations.FiniteMatrixGaussian.varying_mean_hasDerivAt
    (fun t => realPrecision N B u (A + (t : ℂ) • Y))
    (fun t => currentMatrix N B u (A + (t : ℂ) • Y) X) 0
    (currentMatrix N B u A Y) (secondMatrix N B u X Y)
    (fun _ => HistoryHaarSectionConnectionGaussian.realPrecision_posDef _ _ _ _)
    (realPrecision_hasDerivAt N B u A Y) (currentMatrix_hasDerivAt N B u A X Y 0)
    (currentMatrix_symmetric N B u A Y)
  simpa only [Complex.ofReal_zero, zero_smul, add_zero, response, connected,
    current, directSecond, HistoryHaarSectionConnectionGaussian.law] using! h

theorem response_symmetric (N : ℕ) (B u : ℝ) (A X Y : Coefficients N) :
    response N B u A X Y = response N B u A Y X := by
  have hd : directSecond N B u X Y = directSecond N B u Y X := by
    unfold directSecond secondMatrix secondVertex
    simp only [add_comm]
  rw [response, response, hd, connected, connected, covariance_comm]

/-- The direct connection contribution is the derivative of the original
curvature square. It is not an externally supplied comparison constant. -/
def fullRayCurrent (N : ℕ) (B u : ℝ) (X : Coefficients N)
    (t : ℝ) (x : Space N B u) : ℝ :=
  HistoryHaarMatrixCurvature.rayDerivative N X t +
    current N B u ((t : ℂ) • X) X x

theorem fullRayCurrent_is_action_derivative (N : ℕ) (B u : ℝ)
    (X : Coefficients N) (t : ℝ) (x : Space N B u) :
    HasDerivAt (fun s : ℝ => HistoryHaarSectionAction.action N ((s : ℂ) • X)
      (sourceSection N B u x)) (fullRayCurrent N B u X t x) t := by
  have hs := sectionAction_hasDerivAt N 0 X (sourceSection N B u x) t
  have hj : current N B u ((t : ℂ) • X) X x =
      (firstVertex N 0 X (sourceSection N B u x) (sourceSection N B u x)).re / 2 +
        t * ‖connectionDerivative N X (sourceSection N B u x)‖ ^ 2 := by
    rw [current_eq_original]
    have h := firstVertex_connection_ray N 0 X X
      (sourceSection N B u x) (sourceSection N B u x) t
    simp only [zero_add] at h
    rw [h]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, secondVertex_diagonal]
    ring
  simp only [zero_add] at hs
  rw [← hj] at hs
  have h := (HistoryHaarMatrixCurvature.action_hasDerivAt N X t).add hs
  unfold fullRayCurrent
  convert h using 1
  funext s
  rw [original_action_eq]
  rfl

def fullMeanRayCurrent (N : ℕ) (B u : ℝ) (X : Coefficients N) (t : ℝ) : ℝ :=
  HistoryHaarMatrixCurvature.rayDerivative N X t +
    ∫ x, current N B u ((t : ℂ) • X) X x ∂law N B u ((t : ℂ) • X)

theorem fullMeanRayCurrent_eq_mean (N : ℕ) (B u : ℝ)
    (X : Coefficients N) (t : ℝ) :
    fullMeanRayCurrent N B u X t =
      ∫ x, fullRayCurrent N B u X t x ∂law N B u ((t : ℂ) • X) := by
  have hi : Integrable (current N B u ((t : ℂ) • X) X)
      (law N B u ((t : ℂ) • X)) :=
    (Operations.FiniteMatrixGaussian.score_memLp_two
      (realPrecision N B u ((t : ℂ) • X)) (currentMatrix N B u ((t : ℂ) • X) X)).integrable
        (by norm_num)
  unfold fullMeanRayCurrent fullRayCurrent
  rw [integral_add (integrable_const _) hi]
  simp only [integral_const, probReal_univ, one_smul]

theorem fullMeanRayCurrent_hasDerivAt (N : ℕ) (B u : ℝ) (X : Coefficients N) :
    HasDerivAt (fullMeanRayCurrent N B u X)
      (‖HistoryHaarMatrixCurvature.differentiated N X‖ ^ 2 +
        response N B u 0 X X) 0 := by
  have hc : HasDerivAt (HistoryHaarMatrixCurvature.rayDerivative N X)
      (‖HistoryHaarMatrixCurvature.differentiated N X‖ ^ 2) 0 := by
    convert HistoryHaarMatrixCurvature.secondDeriv_zero N X using 1
    funext t
    exact (HistoryHaarMatrixCurvature.action_hasDerivAt N X t).deriv.symm
  have hs := current_mean_hasDerivAt N B u 0 X X
  simp only [zero_add] at hs
  exact hc.add hs

/-- Both real quadratures contribute exactly one unit per original
complex mode. The identity holds for every actual connection. -/
theorem original_energy_mean (N : ℕ) (B u : ℝ) (A : Coefficients N) :
    (∫ x, (sectionAction N A (sourceSection N B u x) +
      u ^ 2 * ‖sectionField N (sourceSection N B u x)‖ ^ 2 / 2) ∂law N B u A) =
      (Fintype.card (WindowIndex N B u) : ℝ) := by
  simp_rw [← HistoryHaarSectionConnectionGaussian.score_eq_original_action]
  unfold HistoryHaarSectionConnectionGaussian.law
  rw [Operations.FiniteMatrixGaussian.precision_score_mean
    (HistoryHaarSectionConnectionGaussian.realPrecision_posDef N B u A)]
  simp [RealIndex, Fintype.card_prod]

theorem original_energy_variance (N : ℕ) (B u : ℝ) (A : Coefficients N) :
    Var[fun x => sectionAction N A (sourceSection N B u x) +
      u ^ 2 * ‖sectionField N (sourceSection N B u x)‖ ^ 2 / 2; law N B u A] =
      (Fintype.card (WindowIndex N B u) : ℝ) := by
  simp_rw [← HistoryHaarSectionConnectionGaussian.score_eq_original_action]
  unfold HistoryHaarSectionConnectionGaussian.law
  rw [Operations.FiniteMatrixGaussian.precision_score_variance
    (HistoryHaarSectionConnectionGaussian.realPrecision_posDef N B u A)]
  simp [RealIndex, Fintype.card_prod]

structure Conclusions : Prop where
  original_quadratic_action : ∀ N B u A x,
    score (realPrecision N B u A) x = sectionAction N A (sourceSection N B u x) +
      u ^ 2 * ‖sectionField N (sourceSection N B u x)‖ ^ 2 / 2
  positive_full_precision : ∀ N B u A, (realPrecision N B u A).PosDef
  unique_full_state : ∀ N B u A,
    ∃! ν : Measure (Space N B u), IsGaussian ν ∧ (∫ x, x ∂ν) = 0 ∧
      realPrecision N B u A * Operations.FinitePrecisionGaussian.coordinateCovariance ν = 1
  original_current : ∀ N B u A X x,
    HasDerivAt (fun t : ℝ => sectionAction N (A + (t : ℂ) • X) (sourceSection N B u x))
      (current N B u A X x) 0
  original_direct_second : ∀ N B u A X Y x,
    HasDerivAt (fun t : ℝ => current N B u (A + (t : ℂ) • Y) X x)
      (directSecond N B u X Y x) 0
  actual_current_mean : ∀ N B u A X,
    (∫ x, current N B u A X x ∂law N B u A) =
      Matrix.trace ((realPrecision N B u A)⁻¹ * currentMatrix N B u A X) / 2
  complete_connected_response : ∀ N B u A X Y,
    connected N B u A X Y =
      ∑ i, ∑ k, ∑ j, ∑ l,
        (currentMatrix N B u A X i j * currentMatrix N B u A Y k l / 4) *
          ((realPrecision N B u A)⁻¹ i k * (realPrecision N B u A)⁻¹ j l +
            (realPrecision N B u A)⁻¹ i l * (realPrecision N B u A)⁻¹ j k)
  retained_direct_mean : ∀ N B u A X Y,
    (∫ x, directSecond N B u X Y x ∂law N B u A) =
      Matrix.trace ((realPrecision N B u A)⁻¹ * secondMatrix N B u X Y) / 2
  actual_state_response : ∀ N B u A X Y,
    HasDerivAt (fun t : ℝ => ∫ x,
      current N B u (A + (t : ℂ) • Y) X x ∂law N B u (A + (t : ℂ) • Y))
      (response N B u A X Y) 0
  symmetric_response : ∀ N B u A X Y,
    response N B u A X Y = response N B u A Y X
  full_action_current : ∀ N B u X t x,
    HasDerivAt (fun s : ℝ => HistoryHaarSectionAction.action N ((s : ℂ) • X)
      (sourceSection N B u x)) (fullRayCurrent N B u X t x) t
  full_source_mean_response : ∀ N B u X,
    HasDerivAt (fullMeanRayCurrent N B u X)
      (‖HistoryHaarMatrixCurvature.differentiated N X‖ ^ 2 +
        response N B u 0 X X) 0
  original_energy_capacity : ∀ N B u A,
    (∫ x, (sectionAction N A (sourceSection N B u x) +
      u ^ 2 * ‖sectionField N (sourceSection N B u x)‖ ^ 2 / 2) ∂law N B u A) =
      (Fintype.card (WindowIndex N B u) : ℝ)

theorem generated : Conclusions where
  original_quadratic_action := HistoryHaarSectionConnectionGaussian.score_eq_original_action
  positive_full_precision := HistoryHaarSectionConnectionGaussian.realPrecision_posDef
  unique_full_state := HistoryHaarSectionConnectionGaussian.law_existsUnique
  original_current := current_is_action_derivative
  original_direct_second := directSecond_is_current_derivative
  actual_current_mean := current_mean
  complete_connected_response := connected_eq
  retained_direct_mean := directSecond_mean
  actual_state_response := current_mean_hasDerivAt
  symmetric_response := response_symmetric
  full_action_current := fullRayCurrent_is_action_derivative
  full_source_mean_response := fullMeanRayCurrent_hasDerivAt
  original_energy_capacity := original_energy_mean

end GeneratedFoundations.Arithmetic.HistoryHaarSectionConnectionResponse

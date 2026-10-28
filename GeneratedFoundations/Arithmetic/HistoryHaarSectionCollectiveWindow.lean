module

public import GeneratedFoundations.Arithmetic.HistoryHaarSectionCollectiveResponse
public import GeneratedFoundations.Arithmetic.HistoryHaarSectionConnectionMarginal
public import GeneratedFoundations.Operations.FiniteMatrixGaussianMarginalVariation

/-!
# Original collective response through an actual change of window

The connection and geometric directions act on one original source
precision. Observation of a smaller spectral window takes its Gaussian
marginal. The resulting collective insertion and mixed direct insertion
are derived by differentiating that very marginal, rather than replacing
them by the principal blocks of the original vertices.

The last identity retains the response carried by unresolved modes. It is
valid between any two nested original supports, including newly admitted
shells, with all return correlations present. It is a finite observation
identity, not an assertion that a Gaussian tail selects a stopping level.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace GeneratedFoundations.Arithmetic.HistoryHaarSectionCollectiveWindow

open HistoryHaarMatrixCurvature (Coefficients)
open HistoryHaarSectionConnectionGaussian (RealIndex Space)
open HistoryHaarSectionCollectiveResponse (precision firstMatrix directMatrix scalePath)
open HistoryHaarSectionConnectionMarginal (embed embed_injective)
open Operations.FiniteMatrixGaussian (score retainedPrecision retainedInsertion retainedDirect)

local instance (N : ℕ) (B : ℝ) : DecidableEq (RealIndex N B 0) := Classical.decEq _
local instance (N : ℕ) : InnerProductSpace ℝ (HistoryHaarSectionAction.DerivativeFields N) :=
  InnerProductSpace.complexToReal

/-- Original action restriction, distinguished from the integrated
effective precision defined next. -/
theorem original_precision_restrict (N : ℕ) {B C : ℝ} (hBC : B ≤ C)
    (A : Coefficients N) (c : ℝ) :
    (precision N C A c).submatrix (embed N hBC 0) (embed N hBC 0) =
      precision N B A c := by
  ext i j
  have he : embed N hBC 0 i = embed N hBC 0 j ↔ i = j :=
    (embed_injective N hBC 0).eq_iff
  simp only [precision, HistoryHaarSectionCollectiveResponse.kineticMatrix,
    Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.gram_apply, Matrix.one_apply, he]
  rfl

def effectivePrecision (N : ℕ) {B C : ℝ} (hBC : B ≤ C)
    (A : Coefficients N) (c : ℝ) : Matrix (RealIndex N B 0) (RealIndex N B 0) ℝ :=
  retainedPrecision (precision N C A c) (embed N hBC 0)

def observedLaw (N : ℕ) {B C : ℝ} (hBC : B ≤ C)
    (A : Coefficients N) (c : ℝ) : Measure (Space N B 0) :=
  (HistoryHaarSectionCollectiveResponse.law N C A c).map
    (Operations.FiniteMatrixGaussian.select (embed N hBC 0))

def effectiveFirst (N : ℕ) {B C : ℝ} (hBC : B ≤ C)
    (A X : Coefficients N) (c v : ℝ) : Matrix (RealIndex N B 0) (RealIndex N B 0) ℝ :=
  retainedInsertion (precision N C A c) (firstMatrix N C A X c v) (embed N hBC 0)

def effectiveDirect (N : ℕ) {B C : ℝ} (hBC : B ≤ C)
    (A X Y : Coefficients N) (c v w : ℝ) : Matrix (RealIndex N B 0) (RealIndex N B 0) ℝ :=
  retainedDirect (precision N C A c) (firstMatrix N C A X c v)
    (firstMatrix N C A Y c w) (directMatrix N C A X Y c v w) (embed N hBC 0)

theorem observedLaw_eq (N : ℕ) {B C : ℝ} (hBC : B ≤ C)
    (A : Coefficients N) {c : ℝ} (hc : 0 < c) :
    observedLaw N hBC A c = Operations.FiniteMatrixGaussian.law (effectivePrecision N hBC A c) :=
  Operations.FiniteMatrixGaussian.selected_law
    (HistoryHaarSectionCollectiveResponse.precision_posDef N C A hc) (embed_injective N hBC 0)

/-- First collective vertex of the actual observed law. -/
theorem effectivePrecision_hasDerivAt (N : ℕ) {B C : ℝ} (hBC : B ≤ C)
    (A Y : Coefficients N) {c : ℝ} (hc : 0 < c) (w : ℝ) :
    HasDerivAt (fun t : ℝ => effectivePrecision N hBC
      (A + (t : ℂ) • Y) (scalePath c w t)) (effectiveFirst N hBC A Y c w) 0 := by
  have hp := HistoryHaarSectionCollectiveResponse.precision_collective_hasDerivAt N C A Y c w
  have h0 : precision N C (A + ((0 : ℝ) : ℂ) • Y) (scalePath c w 0) = precision N C A c := by
    simp [scalePath]
  have h := Operations.FiniteMatrixGaussian.retainedPrecision_hasDerivAt
    (e := embed N hBC 0) (h0 ▸ HistoryHaarSectionCollectiveResponse.precision_posDef N C A hc)
    (embed_injective N hBC 0) hp
  simpa only [h0, effectivePrecision, effectiveFirst] using h

/-- The mixed direct insertion includes differentiation of all the
eliminated-mode returns, in addition to the original direct insertion. -/
theorem effectiveFirst_hasDerivAt (N : ℕ) {B C : ℝ} (hBC : B ≤ C)
    (A X Y : Coefficients N) {c : ℝ} (hc : 0 < c) (v w : ℝ) :
    HasDerivAt (fun t : ℝ => effectiveFirst N hBC
      (A + (t : ℂ) • Y) X (scalePath c w t) v) (effectiveDirect N hBC A X Y c v w) 0 := by
  have h := Operations.FiniteMatrixGaussian.retainedInsertion_hasDerivAt
    (P := fun t : ℝ => precision N C (A + (t : ℂ) • Y) (scalePath c w t))
    (V := fun t : ℝ => firstMatrix N C (A + (t : ℂ) • Y) X (scalePath c w t) v)
    (t := 0)
    (e := embed N hBC 0)
    (by simpa [scalePath] using HistoryHaarSectionCollectiveResponse.precision_posDef N C A hc)
    (embed_injective N hBC 0)
    (HistoryHaarSectionCollectiveResponse.precision_collective_hasDerivAt N C A Y c w)
    (HistoryHaarSectionCollectiveResponse.firstMatrix_collective_hasDerivAt N C A X Y c v w)
  simpa only [scalePath, mul_zero, Real.exp_zero, mul_one, Complex.ofReal_zero,
    zero_smul, add_zero, effectiveFirst, effectiveDirect] using h

theorem observed_collective_mean_hasDerivAt (N : ℕ) {B C : ℝ} (hBC : B ≤ C)
    (A X Y : Coefficients N) {c : ℝ} (hc : 0 < c) (v w : ℝ) :
    HasDerivAt (fun t : ℝ => ∫ x,
      score (effectiveFirst N hBC (A + (t : ℂ) • Y) X (scalePath c w t) v) x
        ∂observedLaw N hBC (A + (t : ℂ) • Y) (scalePath c w t))
      ((∫ x, score (effectiveDirect N hBC A X Y c v w) x ∂observedLaw N hBC A c) -
        cov[score (effectiveFirst N hBC A X c v), score (effectiveFirst N hBC A Y c w);
          observedLaw N hBC A c]) 0 := by
  have h := Operations.FiniteMatrixGaussian.retained_mean_hasDerivAt
    (fun t => precision N C (A + (t : ℂ) • Y) (scalePath c w t))
    (fun t => firstMatrix N C (A + (t : ℂ) • Y) X (scalePath c w t) v)
    0 (firstMatrix N C A Y c w) (directMatrix N C A X Y c v w)
    (e := embed N hBC 0) (embed_injective N hBC 0)
    (fun t => HistoryHaarSectionCollectiveResponse.precision_posDef N C _
      (mul_pos hc (Real.exp_pos _)))
    (HistoryHaarSectionCollectiveResponse.precision_collective_hasDerivAt N C A Y c w)
    (HistoryHaarSectionCollectiveResponse.firstMatrix_collective_hasDerivAt N C A X Y c v w)
    (HistoryHaarSectionCollectiveResponse.firstMatrix_symmetric N C A Y c w)
  have hpos (t : ℝ) : 0 < scalePath c w t := mul_pos hc (Real.exp_pos _)
  simp only [scalePath, mul_zero, Real.exp_zero, mul_one, Complex.ofReal_zero,
    zero_smul, add_zero] at h
  simp_rw [observedLaw_eq N hBC _ (hpos _), observedLaw_eq N hBC _ hc]
  simpa only [effectivePrecision, effectiveFirst, effectiveDirect, scalePath] using! h

/-- One same-source balance valid even when the larger support contains
newly born shells. Its conditional covariance contains every return from
the modes that the smaller observation does not display. -/
theorem full_current_balance (N : ℕ) {B C : ℝ} (hBC : B ≤ C)
    (A X : Coefficients N) {c : ℝ} (hc : 0 < c) (v : ℝ) :
    (∫ x, score (firstMatrix N C A X c v) x
      ∂HistoryHaarSectionCollectiveResponse.law N C A c) =
      (∫ x, score (effectiveFirst N hBC A X c v) x ∂observedLaw N hBC A c) +
        Matrix.trace (Operations.FiniteMatrixGaussian.conditionalCovariance
          (precision N C A c) (embed N hBC 0) * firstMatrix N C A X c v) / 2 := by
  rw [observedLaw_eq N hBC A hc]
  exact Operations.FiniteMatrixGaussian.full_mean_eq_retained_add_conditional
    (HistoryHaarSectionCollectiveResponse.precision_posDef N C A hc) (embed_injective N hBC 0) _

private theorem currentMatrix_zero (N : ℕ) (B : ℝ) (A : Coefficients N) :
    HistoryHaarSectionConnectionResponse.currentMatrix N B 0 A 0 = 0 := by
  have hd := HistoryHaarSectionConnectionResponse.realPrecision_hasDerivAt N B 0 A 0
  have hz : HasDerivAt (fun t : ℝ =>
      HistoryHaarSectionConnectionGaussian.realPrecision N B 0 (A + (t : ℂ) • 0)) 0 0 := by
    simpa only [smul_zero, add_zero] using
      hasDerivAt_const (0 : ℝ) (HistoryHaarSectionConnectionGaussian.realPrecision N B 0 A)
  exact hd.unique hz

/-- The actual logarithmic geometric insertion counts the retained real
coordinates and their full, connection-dependent restoring covariance. -/
theorem geometric_current_mean (N : ℕ) (B : ℝ) (A : Coefficients N)
    {c : ℝ} (hc : 0 < c) :
    (∫ x, score (firstMatrix N B A 0 c 1) x
      ∂HistoryHaarSectionCollectiveResponse.law N B A c) =
      (Fintype.card (RealIndex N B 0) : ℝ) / 2 +
        c ^ 3 * HistoryDefiningResponse.coefficient N * Matrix.trace ((precision N B A c)⁻¹) := by
  have he : firstMatrix N B A 0 c 1 = precision N B A c +
      (2 * c ^ 3 * HistoryDefiningResponse.coefficient N) • 1 := by
    rw [firstMatrix, currentMatrix_zero]
    ext i j
    simp only [precision, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.zero_apply]
    ring
  rw [he, HistoryHaarSectionCollectiveResponse.law,
    Operations.FiniteMatrixGaussian.score_mean_trace
    (HistoryHaarSectionCollectiveResponse.precision_posDef N B A hc)]
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one,
    Operations.FiniteMatrixGaussian.inverse_mul_precision
      (HistoryHaarSectionCollectiveResponse.precision_posDef N B A hc),
    Matrix.trace_add, Matrix.trace_one, Matrix.trace_smul]
  simp only [smul_eq_mul]
  ring

def geometricMean (N : ℕ) (B : ℝ) (A : Coefficients N) (c : ℝ) : ℝ :=
  -HistoryHaarMatrixCurvature.action N A / c +
    ∫ x, score (firstMatrix N B A 0 c 1) x ∂HistoryHaarSectionCollectiveResponse.law N B A c

/-- The insertion used in the compatibility equation is the derivative
of the original full action on the actual positive geometric path. -/
theorem original_geometric_hasDerivAt (N : ℕ) (B : ℝ) (A : Coefficients N)
    {c : ℝ} (hc : 0 < c) (x : Space N B 0) :
    HasDerivAt (fun t : ℝ => HistoryHaarSectionGeometricVariation.geometricAction N A
      (HistoryHaarSectionConnectionGaussian.sourceSection N B 0 x) (scalePath c 1 t))
      (-HistoryHaarMatrixCurvature.action N A / c + score (firstMatrix N B A 0 c 1) x) 0 := by
  have hp : HasDerivAt (scalePath c 1) c 0 := by
    change HasDerivAt (fun t : ℝ => c * Real.exp (1 * t)) c 0
    simpa only [id_eq, one_mul, Real.exp_zero, mul_one] using
      ((hasDerivAt_id (0 : ℝ)).exp).const_mul c
  have hy : HasDerivAt (fun t : ℝ => HistoryHaarMatrixCurvature.action N A / scalePath c 1 t)
      (-HistoryHaarMatrixCurvature.action N A / c) 0 := by
    have h := (hasDerivAt_const (0 : ℝ) (HistoryHaarMatrixCurvature.action N A)).div hp
      (by simpa [scalePath] using hc.ne')
    apply h.congr_deriv
    simp only [scalePath, mul_zero, Real.exp_zero, mul_one, zero_mul, zero_sub]
    field_simp
  have hs := HistoryHaarSectionCollectiveResponse.score_collective_hasDerivAt N B A 0 c 1 x
  simp only [smul_zero, add_zero] at hs
  apply (hy.add hs).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun t =>
    HistoryHaarSectionCollectiveResponse.score_eq_original N B A
      (mul_pos hc (Real.exp_pos _)) x

/-- Native content compatibility for the actual connection background.
It retains the original curvature and the full inverse precision. -/
theorem geometricMean_zero_iff (N : ℕ) (B : ℝ) (A : Coefficients N)
    {c : ℝ} (hc : 0 < c) :
    geometricMean N B A c = 0 ↔
      HistoryHaarMatrixCurvature.action N A / c =
        (Fintype.card (RealIndex N B 0) : ℝ) / 2 +
          c ^ 3 * HistoryDefiningResponse.coefficient N * Matrix.trace ((precision N B A c)⁻¹) := by
  rw [geometricMean, geometric_current_mean N B A hc]
  rw [neg_div, neg_add_eq_sub, sub_eq_zero, eq_comm]

/-- The same compatibility equation expressed through a smaller observed
window. The unresolved return is part of the equation, not a tail dropped
before stationarity is tested. -/
theorem geometricMean_observed_balance (N : ℕ) {B C : ℝ} (hBC : B ≤ C)
    (A : Coefficients N) {c : ℝ} (hc : 0 < c) :
    geometricMean N C A c =
      -HistoryHaarMatrixCurvature.action N A / c +
      (∫ x, score (effectiveFirst N hBC A 0 c 1) x ∂observedLaw N hBC A c) +
        Matrix.trace (Operations.FiniteMatrixGaussian.conditionalCovariance
          (precision N C A c) (embed N hBC 0) * firstMatrix N C A 0 c 1) / 2 := by
  rw [geometricMean, full_current_balance N hBC A 0 hc 1]
  ring

structure Conclusions : Prop where
  observed_variational_response : ∀ N B C (hBC : B ≤ C) A X Y c, 0 < c → ∀ v w,
    HasDerivAt (fun t : ℝ => ∫ x,
      score (effectiveFirst N hBC (A + (t : ℂ) • Y) X (scalePath c w t) v) x
        ∂observedLaw N hBC (A + (t : ℂ) • Y) (scalePath c w t))
      ((∫ x, score (effectiveDirect N hBC A X Y c v w) x ∂observedLaw N hBC A c) -
        cov[score (effectiveFirst N hBC A X c v), score (effectiveFirst N hBC A Y c w);
          observedLaw N hBC A c]) 0
  native_geometric_content : ∀ N B A c, 0 < c →
    (geometricMean N B A c = 0 ↔ HistoryHaarMatrixCurvature.action N A / c =
      (Fintype.card (RealIndex N B 0) : ℝ) / 2 +
        c ^ 3 * HistoryDefiningResponse.coefficient N * Matrix.trace ((precision N B A c)⁻¹))
  complete_window_ledger : ∀ N B C (hBC : B ≤ C) A X c, 0 < c → ∀ v,
    (∫ x, score (firstMatrix N C A X c v) x
      ∂HistoryHaarSectionCollectiveResponse.law N C A c) =
      (∫ x, score (effectiveFirst N hBC A X c v) x ∂observedLaw N hBC A c) +
        Matrix.trace (Operations.FiniteMatrixGaussian.conditionalCovariance
          (precision N C A c) (embed N hBC 0) * firstMatrix N C A X c v) / 2

theorem generated : Conclusions where
  observed_variational_response := fun N _ _ hBC A X Y _ hc v w =>
    observed_collective_mean_hasDerivAt N hBC A X Y hc v w
  native_geometric_content := fun N B A _ hc => geometricMean_zero_iff N B A hc
  complete_window_ledger := fun N _ _ hBC A X _ hc v => full_current_balance N hBC A X hc v

end GeneratedFoundations.Arithmetic.HistoryHaarSectionCollectiveWindow

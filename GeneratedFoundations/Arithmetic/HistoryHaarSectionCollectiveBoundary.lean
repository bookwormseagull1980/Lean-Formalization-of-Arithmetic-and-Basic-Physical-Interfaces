module

public import GeneratedFoundations.Arithmetic.HistoryHaarSectionFrequencyCollective
public import GeneratedFoundations.Arithmetic.HistoryHaarSectionBoundary

/-!
# The moving Gaussian observation of the full collective current

The finite preparation is held fixed while its observation window varies.
Each original scalar eigenline retains both real quadratures, its Gaussian
weight and its actual frequency edge. A row contribution contains an
entire row of the inverse precision and insertion; it is not a diagonal
approximation to either matrix. Their sum recovers the full current mean.

The moving-boundary formula below is therefore a formula for the native
collective current, not for the earlier kinetic-square comparison. Its
edge coefficients remain signed. A stationary endpoint or a stopping
rule is not inserted into this observation derivative.

This is a row-weighted observation after Gaussian expectation. It is not
identified with applying a field filter on both legs of the original
action. `HistoryHaarSectionFilteredCollective` proves their exact
non-diagonal difference and derives that second observation separately.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Matrix Matrix.Norms.Operator Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace GeneratedFoundations.Arithmetic.HistoryHaarSectionCollectiveBoundary

open HistoryHaarMatrixCurvature (Coefficients)
open HistoryHaarSectionConnectionGaussian (RealIndex Space)
open HistoryHaarSectionFrequencyCollective (precision precision_posDef firstMatrix law)
open Operations.FiniteMatrixGaussian (score)

local instance (N : ℕ) (C u₀ : ℝ) : DecidableEq (RealIndex N C u₀) := Classical.decEq _

def rowInsertion {ι : Type*} [DecidableEq ι] (i : ι) (V : Matrix ι ι ℝ) :
    Matrix ι ι ℝ := fun j k => if j = i then V j k else 0

private def rowMap {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    Matrix ι ι ℝ →L[ℝ] Matrix ι ι ℝ :=
  ({ toFun := rowInsertion i
     map_add' := by intros; ext j k; by_cases h : j = i <;> simp [rowInsertion, h]
     map_smul' := by intros; ext j k; by_cases h : j = i <;> simp [rowInsertion, h] } :
    Matrix ι ι ℝ →ₗ[ℝ] Matrix ι ι ℝ).toContinuousLinearMap

theorem sum_rowInsertion {ι : Type*} [Fintype ι] [DecidableEq ι] (V : Matrix ι ι ℝ) :
    ∑ i, rowInsertion i V = V := by
  ext j k
  simp [Matrix.sum_apply, rowInsertion]

def rowMean (N : ℕ) (C u₀ : ℝ) (A X : Coefficients N) (c v r u : ℝ)
    (i : RealIndex N C u₀) : ℝ :=
  Matrix.trace ((precision N C u₀ A c u)⁻¹ *
    rowInsertion i (firstMatrix N C u₀ A X c u v r)) / 2

/-- Every covariance--insertion cross entry in this row is retained. -/
theorem rowMean_eq_actual (N : ℕ) (C u₀ : ℝ) (A X : Coefficients N)
    {c : ℝ} (hc : 0 < c) (v r u : ℝ) (i : RealIndex N C u₀) :
    rowMean N C u₀ A X c v r u i =
      ∫ x, score (rowInsertion i (firstMatrix N C u₀ A X c u v r)) x
        ∂law N C u₀ A c u :=
  (Operations.FiniteMatrixGaussian.score_mean_trace (precision_posDef N C u₀ A hc u) _).symm

theorem sum_rowMean (N : ℕ) (C u₀ : ℝ) (A X : Coefficients N)
    {c : ℝ} (hc : 0 < c) (v r u : ℝ) :
    (∑ i, rowMean N C u₀ A X c v r u i) =
      ∫ x, score (firstMatrix N C u₀ A X c u v r) x ∂law N C u₀ A c u := by
  simp only [law]
  rw [Operations.FiniteMatrixGaussian.score_mean_trace (precision_posDef N C u₀ A hc u)]
  simp only [rowMean, ← Finset.sum_div, ← Matrix.trace_sum, ← Finset.mul_sum,
    sum_rowInsertion]

theorem rowMean_continuous (N : ℕ) (C u₀ : ℝ) (A X : Coefficients N)
    {c : ℝ} (hc : 0 < c) (v r : ℝ) (i : RealIndex N C u₀) :
    Continuous (fun u => rowMean N C u₀ A X c v r u i) := by
  have hp (u : ℝ) : DifferentiableAt ℝ (fun t => precision N C u₀ A c t) u := by
    unfold precision
    fun_prop
  have hi : Continuous (fun u => (precision N C u₀ A c u)⁻¹) := by
    apply continuous_iff_continuousAt.mpr
    intro u
    exact (Operations.FiniteMatrixGaussian.inverse_hasDerivAt
      (precision_posDef N C u₀ A hc u) (hp u).hasDerivAt).continuousAt
  have hv : Continuous (fun u => firstMatrix N C u₀ A X c u v r) := by
    unfold firstMatrix
    fun_prop
  have hr := (rowMap i).continuous.comp hv
  have ht := (Matrix.traceLinearMap (RealIndex N C u₀) ℝ ℝ).toContinuousLinearMap.continuous
  exact (ht.comp (hi.mul hr)).div_const 2

def kinetic (N : ℕ) (C u₀ : ℝ) (i : RealIndex N C u₀) : ℝ :=
  HistoryHaarSectionWindow.kinetic N (Sum.inr i.1.val)

/-- A preparation containing the proposed observation cutoff enumerates
every original scalar label visible at every frequency in that window. -/
theorem actual_rows_in_preparation (N : ℕ) {B C u : ℝ} (hBC : B ≤ C)
    (a : HistoryHaarSectionHessian.Index N)
    (ha : u ^ 2 + Geometry.SourceCasimirClosure.energy a.2.val.1 < B) :
    a ∈ HistoryHaarSectionConnectionVariation.scalarSupport N C 0 := by
  rw [HistoryHaarSectionConnectionVariation.mem_scalarSupport,
    HistoryHaarSectionWindow.mem_support]
  change Geometry.SourceCasimirClosure.energy a.2.val.1 < C - (0 : ℝ) ^ 2
  nlinarith [sq_nonneg u]

def integrand (N : ℕ) (C u₀ : ℝ) (A X : Coefficients N) (c v r : ℝ)
    (i : RealIndex N C u₀) (u : ℝ) : ℝ :=
  HistoryHaarSectionComparison.weight N (Sum.inr i.1.val) u *
    rowMean N C u₀ A X c v r u i

theorem integrand_continuous (N : ℕ) (C u₀ : ℝ) (A X : Coefficients N)
    {c : ℝ} (hc : 0 < c) (v r : ℝ) (i : RealIndex N C u₀) :
    Continuous (integrand N C u₀ A X c v r i) :=
  (HistoryHaarSectionComparison.weight_continuous N (Sum.inr i.1.val)).mul
    (rowMean_continuous N C u₀ A X hc v r i)

def branchIntegral (N : ℕ) (C u₀ : ℝ) (A X : Coefficients N) (c v r B : ℝ)
    (i : RealIndex N C u₀) : ℝ :=
  ∫ u in (0 : ℝ)..Real.sqrt (B - kinetic N C u₀ i), integrand N C u₀ A X c v r i u

def response (N : ℕ) (C u₀ : ℝ) (A X : Coefficients N) (c v r B : ℝ) : ℝ :=
  ∑ i, branchIntegral N C u₀ A X c v r B i

def edge (N : ℕ) (C u₀ : ℝ) (A X : Coefficients N) (c v r B : ℝ)
    (i : RealIndex N C u₀) : ℝ :=
  if kinetic N C u₀ i < B then
    rowMean N C u₀ A X c v r (Real.sqrt (B - kinetic N C u₀ i)) i /
      (2 * Real.sqrt (B - kinetic N C u₀ i)) else 0

theorem branchIntegral_continuous (N : ℕ) (C u₀ : ℝ) (A X : Coefficients N)
    {c : ℝ} (hc : 0 < c) (v r : ℝ) (i : RealIndex N C u₀) :
    Continuous (fun B => branchIntegral N C u₀ A X c v r B i) :=
  (intervalIntegral.differentiable_integral_of_continuous
    (integrand_continuous N C u₀ A X hc v r i)).continuous.comp
      (Real.continuous_sqrt.comp (continuous_id.sub continuous_const))

/-- New rows have zero integrated length at their actual birth value. -/
theorem branchIntegral_at_birth (N : ℕ) (C u₀ : ℝ) (A X : Coefficients N)
    (c v r : ℝ) (i : RealIndex N C u₀) :
    branchIntegral N C u₀ A X c v r (kinetic N C u₀ i) i = 0 := by
  simp only [branchIntegral, sub_self, Real.sqrt_zero, intervalIntegral.integral_same]

theorem branchIntegral_hasDerivAt (N : ℕ) (C u₀ : ℝ) (A X : Coefficients N)
    {c : ℝ} (hc : 0 < c) (v r : ℝ) (i : RealIndex N C u₀) {B : ℝ}
    (hB : kinetic N C u₀ i ≠ B) :
    HasDerivAt (fun b => branchIntegral N C u₀ A X c v r b i)
      (Real.exp (-B) * edge N C u₀ A X c v r B i) B := by
  have hf := integrand_continuous N C u₀ A X hc v r i
  by_cases h : kinetic N C u₀ i < B
  · have hs := ((hasDerivAt_id B).sub_const (kinetic N C u₀ i)).sqrt (sub_pos.mpr h).ne'
    have hi := intervalIntegral.integral_hasDerivAt_right
      (hf.intervalIntegrable 0 (Real.sqrt (B - kinetic N C u₀ i)))
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
    have he : HistoryHaarSectionComparison.weight N (Sum.inr i.1.val)
        (Real.sqrt (B - kinetic N C u₀ i)) = Real.exp (-B) :=
      HistoryHaarSectionBoundary.weight_at_edge N (Sum.inr i.1.val) h
    convert! hi.comp B hs using 1
    simp only [edge, ite_eq_left h, integrand, he, id_eq, mul_one_div]
    ring
  · have hl : B < kinetic N C u₀ i := lt_of_le_of_ne (le_of_not_gt h) hB.symm
    have hz : HasDerivAt (fun b => branchIntegral N C u₀ A X c v r b i) 0 B := by
      apply (hasDerivAt_const B (0 : ℝ)).congr_of_eventuallyEq
      filter_upwards [isOpen_Iio.mem_nhds hl] with b hb
      simp only [branchIntegral, Real.sqrt_eq_zero'.mpr (sub_nonpos.mpr hb.le),
        intervalIntegral.integral_same]
    simpa only [edge, ite_eq_right h, mul_zero] using! hz

theorem response_continuous (N : ℕ) (C u₀ : ℝ) (A X : Coefficients N)
    {c : ℝ} (hc : 0 < c) (v r : ℝ) : Continuous (response N C u₀ A X c v r) :=
  continuous_finsetSum _ (fun i _ => branchIntegral_continuous N C u₀ A X hc v r i)

/-- The common Gaussian boundary factor multiplies the full signed
collective edge. No entry of the inverse precision or vertex is removed. -/
theorem response_hasDerivAt (N : ℕ) (C u₀ : ℝ) (A X : Coefficients N)
    {c : ℝ} (hc : 0 < c) (v r : ℝ) {B : ℝ}
    (hregular : ∀ i : RealIndex N C u₀, kinetic N C u₀ i ≠ B) :
    HasDerivAt (response N C u₀ A X c v r)
      (Real.exp (-B) * ∑ i, edge N C u₀ A X c v r B i) B := by
  have h := HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => branchIntegral_hasDerivAt N C u₀ A X hc v r i (hregular i))
  simpa only [response, Finset.mul_sum] using! h

private def submatrixMap {ι κ η : Type*} [Fintype ι] [Fintype κ] [Fintype η]
    (e : κ → ι) (f : η → ι) : Matrix ι ι ℝ →L[ℝ] Matrix κ η ℝ :=
  ({ toFun := fun M => M.submatrix e f
     map_add' := by intros; rfl
     map_smul' := by intros; rfl } :
    Matrix ι ι ℝ →ₗ[ℝ] Matrix κ η ℝ).toContinuousLinearMap

def retainedRowMean (N : ℕ) {D C : ℝ} (hDC : D ≤ C) (u₀ : ℝ)
    (A X : Coefficients N) (c v r u : ℝ) (i : RealIndex N C u₀) : ℝ :=
  Matrix.trace (Operations.FiniteMatrixGaussian.returnCovariance (precision N C u₀ A c u)
    (HistoryHaarSectionConnectionMarginal.embed N hDC u₀) *
      rowInsertion i (firstMatrix N C u₀ A X c u v r)) / 2

def conditionalRowMean (N : ℕ) {D C : ℝ} (hDC : D ≤ C) (u₀ : ℝ)
    (A X : Coefficients N) (c v r u : ℝ) (i : RealIndex N C u₀) : ℝ :=
  Matrix.trace (Operations.FiniteMatrixGaussian.conditionalCovariance
    (precision N C u₀ A c u) (HistoryHaarSectionConnectionMarginal.embed N hDC u₀) *
      rowInsertion i (firstMatrix N C u₀ A X c u v r)) / 2

theorem retainedRowMean_eq_actual (N : ℕ) {D C : ℝ} (hDC : D ≤ C) (u₀ : ℝ)
    (A X : Coefficients N) {c : ℝ} (hc : 0 < c) (v r u : ℝ)
    (i : RealIndex N C u₀) :
    retainedRowMean N hDC u₀ A X c v r u i =
      ∫ x, score (Operations.FiniteMatrixGaussian.retainedInsertion (precision N C u₀ A c u)
        (rowInsertion i (firstMatrix N C u₀ A X c u v r))
        (HistoryHaarSectionConnectionMarginal.embed N hDC u₀)) x
        ∂HistoryHaarSectionFrequencyCollective.observedLaw N hDC u₀ A c u :=
  (Operations.FiniteMatrixGaussian.retained_mean_eq_return_trace (precision_posDef N C u₀ A hc u)
    (HistoryHaarSectionConnectionMarginal.embed_injective N hDC u₀) _).symm

theorem rowMean_return_balance (N : ℕ) {D C : ℝ} (hDC : D ≤ C) (u₀ : ℝ)
    (A X : Coefficients N) (c v r u : ℝ) (i : RealIndex N C u₀) :
    rowMean N C u₀ A X c v r u i = retainedRowMean N hDC u₀ A X c v r u i +
      conditionalRowMean N hDC u₀ A X c v r u i := by
  simp only [rowMean, retainedRowMean, conditionalRowMean,
    Operations.FiniteMatrixGaussian.conditionalCovariance, Matrix.sub_mul, Matrix.trace_sub]
  ring

theorem retainedRowMean_continuous (N : ℕ) {D C : ℝ} (hDC : D ≤ C) (u₀ : ℝ)
    (A X : Coefficients N) {c : ℝ} (hc : 0 < c) (v r : ℝ)
    (i : RealIndex N C u₀) :
    Continuous (fun u => retainedRowMean N hDC u₀ A X c v r u i) := by
  let e := HistoryHaarSectionConnectionMarginal.embed N hDC u₀
  have hp (u : ℝ) : DifferentiableAt ℝ (fun t => precision N C u₀ A c t) u := by
    unfold precision
    fun_prop
  have hi : Continuous (fun u => (precision N C u₀ A c u)⁻¹) := by
    apply continuous_iff_continuousAt.mpr
    intro u
    exact (Operations.FiniteMatrixGaussian.inverse_hasDerivAt
      (precision_posDef N C u₀ A hc u) (hp u).hasDerivAt).continuousAt
  have hs : Continuous (fun u => Operations.FiniteMatrixGaussian.retainedPrecision
      (precision N C u₀ A c u) e) := by
    apply continuous_iff_continuousAt.mpr
    intro u
    exact (Operations.FiniteMatrixGaussian.retainedPrecision_hasDerivAt
      (precision_posDef N C u₀ A hc u)
      (HistoryHaarSectionConnectionMarginal.embed_injective N hDC u₀) (hp u).hasDerivAt).continuousAt
  have hl := (submatrixMap id e).continuous.comp hi
  have hr := (submatrixMap e id).continuous.comp hi
  have hv : Continuous (fun u => firstMatrix N C u₀ A X c u v r) := by
    unfold firstMatrix
    fun_prop
  have hrow := (rowMap i).continuous.comp hv
  have ht := (Matrix.traceLinearMap (RealIndex N C u₀) ℝ ℝ).toContinuousLinearMap.continuous
  exact (ht.comp (((hl.matrix_mul hs).matrix_mul hr).mul hrow)).div_const 2

theorem conditionalRowMean_continuous (N : ℕ) {D C : ℝ} (hDC : D ≤ C) (u₀ : ℝ)
    (A X : Coefficients N) {c : ℝ} (hc : 0 < c) (v r : ℝ)
    (i : RealIndex N C u₀) :
    Continuous (fun u => conditionalRowMean N hDC u₀ A X c v r u i) := by
  have he : (fun u => conditionalRowMean N hDC u₀ A X c v r u i) =
      fun u => rowMean N C u₀ A X c v r u i - retainedRowMean N hDC u₀ A X c v r u i := by
    funext u
    linarith [rowMean_return_balance N hDC u₀ A X c v r u i]
  rw [he]
  exact (rowMean_continuous N C u₀ A X hc v r i).sub
    (retainedRowMean_continuous N hDC u₀ A X hc v r i)

def retainedResponse (N : ℕ) {D C : ℝ} (hDC : D ≤ C) (u₀ : ℝ)
    (A X : Coefficients N) (c v r B : ℝ) : ℝ :=
  ∑ i, ∫ u in (0 : ℝ)..Real.sqrt (B - kinetic N C u₀ i),
    HistoryHaarSectionComparison.weight N (Sum.inr i.1.val) u *
      retainedRowMean N hDC u₀ A X c v r u i

def conditionalResponse (N : ℕ) {D C : ℝ} (hDC : D ≤ C) (u₀ : ℝ)
    (A X : Coefficients N) (c v r B : ℝ) : ℝ :=
  ∑ i, ∫ u in (0 : ℝ)..Real.sqrt (B - kinetic N C u₀ i),
    HistoryHaarSectionComparison.weight N (Sum.inr i.1.val) u *
      conditionalRowMean N hDC u₀ A X c v r u i

/-- Window marginalization commutes with this complete frequency ledger.
The response lost from the explicit marginal is retained in the same
source's conditional covariance, with the original weights and birth edges. -/
theorem response_return_balance (N : ℕ) {D C : ℝ} (hDC : D ≤ C) (u₀ : ℝ)
    (A X : Coefficients N) {c : ℝ} (hc : 0 < c) (v r B : ℝ) :
    response N C u₀ A X c v r B = retainedResponse N hDC u₀ A X c v r B +
      conditionalResponse N hDC u₀ A X c v r B := by
  unfold response branchIntegral retainedResponse conditionalResponse
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hw := HistoryHaarSectionComparison.weight_continuous N (Sum.inr i.1.val)
  have hsum := intervalIntegral.integral_add (μ := volume)
    ((hw.mul (retainedRowMean_continuous N hDC u₀ A X hc v r i)).intervalIntegrable
      0 (Real.sqrt (B - kinetic N C u₀ i)))
    ((hw.mul (conditionalRowMean_continuous N hDC u₀ A X hc v r i)).intervalIntegrable
      0 (Real.sqrt (B - kinetic N C u₀ i)))
  calc
    _ = ∫ u in (0 : ℝ)..Real.sqrt (B - kinetic N C u₀ i),
        (HistoryHaarSectionComparison.weight N (Sum.inr i.1.val) u *
          retainedRowMean N hDC u₀ A X c v r u i +
        HistoryHaarSectionComparison.weight N (Sum.inr i.1.val) u *
          conditionalRowMean N hDC u₀ A X c v r u i) := by
      apply intervalIntegral.integral_congr
      intro u _
      unfold integrand
      rw [rowMean_return_balance N hDC u₀ A X c v r u i, mul_add]
    _ = _ := by simpa only [Pi.add_apply, Pi.mul_apply] using! hsum

structure Conclusions : Prop where
  exact_collective_mean : ∀ N C u₀ A X c, 0 < c → ∀ v r u,
    (∑ i, rowMean N C u₀ A X c v r u i) =
      ∫ x, score (firstMatrix N C u₀ A X c u v r) x ∂law N C u₀ A c u
  actual_boundary : ∀ N C u₀ A X c, 0 < c → ∀ v r B,
    (∀ i : RealIndex N C u₀, kinetic N C u₀ i ≠ B) →
    HasDerivAt (response N C u₀ A X c v r)
      (Real.exp (-B) * ∑ i, edge N C u₀ A X c v r B i) B
  continuous_births : ∀ N C u₀ A X c, 0 < c → ∀ v r,
    Continuous (response N C u₀ A X c v r)
  complete_frequency_window_ledger : ∀ N D C (hDC : D ≤ C) u₀ A X c, 0 < c → ∀ v r B,
    response N C u₀ A X c v r B = retainedResponse N hDC u₀ A X c v r B +
      conditionalResponse N hDC u₀ A X c v r B

theorem generated : Conclusions where
  exact_collective_mean := fun N C u₀ A X _ hc v r u => sum_rowMean N C u₀ A X hc v r u
  actual_boundary := fun N C u₀ A X _ hc v r _ h => response_hasDerivAt N C u₀ A X hc v r h
  continuous_births := fun N C u₀ A X _ hc v r => response_continuous N C u₀ A X hc v r
  complete_frequency_window_ledger := fun N _ _ hDC u₀ A X _ hc v r B =>
    response_return_balance N hDC u₀ A X hc v r B

end GeneratedFoundations.Arithmetic.HistoryHaarSectionCollectiveBoundary

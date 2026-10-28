module

public import GeneratedFoundations.Arithmetic.HistoryHaarSectionCollectiveBoundary

/-!
# The Gaussian filter on both legs of the original collective action

A field filter acts on both arguments of its quadratic action. With a
non-diagonal original precision, weighting an inverse-precision/insertion
row after taking its mean is a different observation. The difference is
computed below with every covariance and insertion entry retained.

The frequency in the original Gaussian filter varies with the frequency
in the action. Its first and direct second insertions therefore include
the derivatives of that filter as well as the original collective
vertices. Expectations are taken in the original varied source law.
No endpoint equation or stopping rule is supplied by this construction.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Operator Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace GeneratedFoundations.Arithmetic.HistoryHaarSectionFilteredCollective

open HistoryHaarMatrixCurvature (Coefficients)
open HistoryHaarSectionConnectionGaussian (RealIndex Space sourceSection)
open HistoryHaarSectionFrequencyCollective (precision firstMatrix directMatrix law precision_posDef)
open HistoryHaarSectionCollectiveResponse (scalePath)
open Operations.FiniteMatrixGaussian (score)

local instance (N : ℕ) (C u₀ : ℝ) : DecidableEq (RealIndex N C u₀) := Classical.decEq _

def kinetic (N : ℕ) (C u₀ : ℝ) (i : RealIndex N C u₀) : ℝ :=
  HistoryHaarSectionCollectiveBoundary.kinetic N C u₀ i

def angularFilter (N : ℕ) (C u₀ : ℝ) : Matrix (RealIndex N C u₀) (RealIndex N C u₀) ℝ :=
  Matrix.diagonal fun i => Real.exp (-kinetic N C u₀ i / 2)

def filterMatrix (N : ℕ) (C u₀ u : ℝ) :
    Matrix (RealIndex N C u₀) (RealIndex N C u₀) ℝ :=
  Real.exp (-u ^ 2 / 2) • angularFilter N C u₀

def filterField (N : ℕ) (C u₀ u : ℝ) (x : Space N C u₀) : Space N C u₀ :=
  WithLp.toLp 2 fun i => Real.exp (-(u ^ 2 + kinetic N C u₀ i) / 2) * x i

def filteredMatrix (N : ℕ) (C u₀ u : ℝ)
    (V : Matrix (RealIndex N C u₀) (RealIndex N C u₀) ℝ) :
    Matrix (RealIndex N C u₀) (RealIndex N C u₀) ℝ :=
  Real.exp (-u ^ 2) • (angularFilter N C u₀ * V * angularFilter N C u₀)

theorem filteredMatrix_apply (N : ℕ) (C u₀ u : ℝ)
    (V : Matrix (RealIndex N C u₀) (RealIndex N C u₀) ℝ)
    (i j : RealIndex N C u₀) :
    filteredMatrix N C u₀ u V i j =
      Real.exp (-(u ^ 2 + kinetic N C u₀ i) / 2) * V i j *
        Real.exp (-(u ^ 2 + kinetic N C u₀ j) / 2) := by
  simp only [filteredMatrix, angularFilter, Matrix.smul_apply, smul_eq_mul,
    Matrix.diagonal_mul, Matrix.mul_diagonal]
  have he : Real.exp (-u ^ 2) * Real.exp (-kinetic N C u₀ i / 2) *
      Real.exp (-kinetic N C u₀ j / 2) =
      Real.exp (-(u ^ 2 + kinetic N C u₀ i) / 2) *
        Real.exp (-(u ^ 2 + kinetic N C u₀ j) / 2) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    _ = (Real.exp (-u ^ 2) * Real.exp (-kinetic N C u₀ i / 2) *
        Real.exp (-kinetic N C u₀ j / 2)) * V i j := by ring
    _ = _ := by rw [he]; ring

theorem filtered_score_eq_original (N : ℕ) (C u₀ u : ℝ)
    (V : Matrix (RealIndex N C u₀) (RealIndex N C u₀) ℝ) (x : Space N C u₀) :
    score (filteredMatrix N C u₀ u V) x = score V (filterField N C u₀ u x) := by
  simp only [score, filteredMatrix_apply, filterField, WithLp.ofLp_toLp]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The filter is applied to the actual field in the original action. -/
theorem filtered_action_eq_original (N : ℕ) (C u₀ : ℝ) (A : Coefficients N)
    {c : ℝ} (hc : 0 < c) (u : ℝ) (x : Space N C u₀) :
    HistoryHaarSectionGeometricVariation.geometricAction N A
        (sourceSection N C u₀ (filterField N C u₀ u x)) c +
      c ^ 3 * u ^ 2 * ‖HistoryHaarSectionAction.sectionField N
        (sourceSection N C u₀ (filterField N C u₀ u x))‖ ^ 2 / 2 =
      HistoryHaarMatrixCurvature.action N A / c +
        score (filteredMatrix N C u₀ u (precision N C u₀ A c u)) x := by
  rw [filtered_score_eq_original]
  exact HistoryHaarSectionFrequencyCollective.score_eq_original N C u₀ A hc u _

def first (N : ℕ) (C u₀ : ℝ) (A X : Coefficients N) (c u v r : ℝ) :
    Matrix (RealIndex N C u₀) (RealIndex N C u₀) ℝ :=
  filteredMatrix N C u₀ u
    (firstMatrix N C u₀ A X c u v r - (2 * u * r) • precision N C u₀ A c u)

def direct (N : ℕ) (C u₀ : ℝ) (A X Y : Coefficients N)
    (c u v w r q : ℝ) : Matrix (RealIndex N C u₀) (RealIndex N C u₀) ℝ :=
  filteredMatrix N C u₀ u (directMatrix N C u₀ A X Y c u v w r q -
    (2 * u * q) • firstMatrix N C u₀ A X c u v r -
    (2 * u * r) • firstMatrix N C u₀ A Y c u w q +
    (4 * u ^ 2 * r * q - 2 * r * q) • precision N C u₀ A c u)

private theorem heat_hasDerivAt (u q : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (-(u + q * t) ^ 2))
      (-2 * u * q * Real.exp (-u ^ 2)) 0 := by
  have hu : HasDerivAt (fun t : ℝ => u + q * t) q 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul q).const_add u
  convert! (hu.pow 2).neg.exp using 1
  simp
  ring

theorem filtered_precision_hasDerivAt (N : ℕ) (C u₀ : ℝ)
    (A Y : Coefficients N) (c u w q : ℝ) :
    HasDerivAt (fun t : ℝ => filteredMatrix N C u₀ (u + q * t)
      (precision N C u₀ (A + (t : ℂ) • Y) (scalePath c w t) (u + q * t)))
      (first N C u₀ A Y c u w q) 0 := by
  let F := angularFilter N C u₀
  have hp := HistoryHaarSectionFrequencyCollective.precision_collective_hasDerivAt
    N C u₀ A Y c u w q
  have h := (heat_hasDerivAt u q).smul
    (((hasDerivAt_const (0 : ℝ) F).mul hp).mul (hasDerivAt_const (0 : ℝ) F))
  apply h.congr_deriv
  simp only [Pi.mul_apply, zero_mul, zero_add, mul_zero, add_zero,
    Complex.ofReal_zero, zero_smul, scalePath, Real.exp_zero, mul_one]
  ext i j
  simp only [first, filteredMatrix, F, angularFilter, Matrix.smul_apply,
    Matrix.add_apply, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, smul_eq_mul]
  ring

theorem filtered_first_hasDerivAt (N : ℕ) (C u₀ : ℝ)
    (A X Y : Coefficients N) (c u v w r q : ℝ) :
    HasDerivAt (fun t : ℝ => first N C u₀ (A + (t : ℂ) • Y) X
      (scalePath c w t) (u + q * t) v r)
      (direct N C u₀ A X Y c u v w r q) 0 := by
  let F := angularFilter N C u₀
  have hp := HistoryHaarSectionFrequencyCollective.precision_collective_hasDerivAt
    N C u₀ A Y c u w q
  have hv := HistoryHaarSectionFrequencyCollective.firstMatrix_collective_hasDerivAt
    N C u₀ A X Y c u v w r q
  have hu : HasDerivAt (fun t : ℝ => 2 * (u + q * t) * r) (2 * q * r) 0 := by
    convert! ((((hasDerivAt_id (0 : ℝ)).const_mul q).const_add u).const_mul 2).mul_const r
      using 1
    simp
  have h := (heat_hasDerivAt u q).smul
    (((hasDerivAt_const (0 : ℝ) F).mul (hv.sub (hu.smul hp))).mul
      (hasDerivAt_const (0 : ℝ) F))
  apply h.congr_deriv
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.smul_apply', zero_mul, zero_add, mul_zero,
    add_zero, Complex.ofReal_zero, zero_smul, scalePath, Real.exp_zero, mul_one]
  ext i j
  simp only [direct, filteredMatrix, F, angularFilter, Matrix.smul_apply,
    Matrix.add_apply, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, smul_eq_mul]
  ring

private def scoreMap (N : ℕ) (C u₀ : ℝ) (x : Space N C u₀) :
    Matrix (RealIndex N C u₀) (RealIndex N C u₀) ℝ →L[ℝ] ℝ :=
  ({ toFun := fun P => score P x
     map_add' := by intros; simp only [score, Matrix.add_apply, add_div,
       add_mul, Finset.sum_add_distrib]
     map_smul' := by intros; simp only [score, Matrix.smul_apply, smul_eq_mul,
       mul_div_assoc, mul_assoc, ← Finset.mul_sum, RingHom.id_apply] } :
    Matrix (RealIndex N C u₀) (RealIndex N C u₀) ℝ →ₗ[ℝ] ℝ).toContinuousLinearMap

theorem filtered_score_hasDerivAt (N : ℕ) (C u₀ : ℝ)
    (A Y : Coefficients N) (c u w q : ℝ) (x : Space N C u₀) :
    HasDerivAt (fun t : ℝ => score (filteredMatrix N C u₀ (u + q * t)
      (precision N C u₀ (A + (t : ℂ) • Y) (scalePath c w t) (u + q * t))) x)
      (score (first N C u₀ A Y c u w q) x) 0 :=
  (scoreMap N C u₀ x).hasFDerivAt.comp_hasDerivAt 0
    (filtered_precision_hasDerivAt N C u₀ A Y c u w q)

/-- The observable and the actual source law vary together. The second
leg of the covariance is the unfiltered derivative of that source law. -/
theorem actual_mean_hasDerivAt (N : ℕ) (C u₀ : ℝ)
    (A X Y : Coefficients N) {c : ℝ} (hc : 0 < c) (u v w r q : ℝ) :
    HasDerivAt (fun t : ℝ => ∫ x,
      score (first N C u₀ (A + (t : ℂ) • Y) X (scalePath c w t) (u + q * t) v r) x
        ∂law N C u₀ (A + (t : ℂ) • Y) (scalePath c w t) (u + q * t))
      ((∫ x, score (direct N C u₀ A X Y c u v w r q) x ∂law N C u₀ A c u) -
        cov[score (first N C u₀ A X c u v r),
          score (firstMatrix N C u₀ A Y c u w q); law N C u₀ A c u]) 0 := by
  have h := Operations.FiniteMatrixGaussian.varying_mean_hasDerivAt
    (fun t => precision N C u₀ (A + (t : ℂ) • Y) (scalePath c w t) (u + q * t))
    (fun t => first N C u₀ (A + (t : ℂ) • Y) X (scalePath c w t) (u + q * t) v r)
    0 (firstMatrix N C u₀ A Y c u w q) (direct N C u₀ A X Y c u v w r q)
    (fun t => precision_posDef N C u₀ _ (mul_pos hc (Real.exp_pos _)) _)
    (HistoryHaarSectionFrequencyCollective.precision_collective_hasDerivAt N C u₀ A Y c u w q)
    (filtered_first_hasDerivAt N C u₀ A X Y c u v w r q)
    (HistoryHaarSectionFrequencyCollective.firstMatrix_symmetric N C u₀ A Y c u w q)
  simpa only [scalePath, mul_zero, Real.exp_zero, mul_one, Complex.ofReal_zero,
    zero_smul, add_zero, law] using! h

/-- Exact difference between weighting an insertion row after taking its
mean and filtering the actual field on both quadratic legs. The entries
of the covariance--vertex product are not assumed to have one sign. -/
theorem row_filter_difference {ι : Type*} [Fintype ι]
    (K V : Matrix ι ι ℝ) (hK : K.IsSymm) (hV : V.IsSymm) (f : ι → ℝ) :
    (∑ i, ∑ j, K j i * V i j * f i ^ 2) / 2 -
        (∑ i, ∑ j, K j i * V i j * (f i * f j)) / 2 =
      (∑ i, ∑ j, K j i * V i j * (f i - f j) ^ 2) / 4 := by
  have hs : (∑ i, ∑ j, K j i * V i j * f j ^ 2) =
      ∑ i, ∑ j, K j i * V i j * f i ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hK.apply, hV.apply]
  have he : (∑ i, ∑ j, K j i * V i j * (f i - f j) ^ 2) =
      (∑ i, ∑ j, K j i * V i j * f i ^ 2) +
        (∑ i, ∑ j, K j i * V i j * f j ^ 2) -
          2 * (∑ i, ∑ j, K j i * V i j * (f i * f j)) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, hs]
  ring

private theorem row_trace {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K V : Matrix ι ι ℝ) (i : ι) :
    Matrix.trace (K * HistoryHaarSectionCollectiveBoundary.rowInsertion i V) =
      ∑ j, K j i * V i j := by
  simp [Matrix.trace, Matrix.mul_apply,
    HistoryHaarSectionCollectiveBoundary.rowInsertion, mul_ite]

def pairMean (N : ℕ) (C u₀ : ℝ) (A X : Coefficients N) (c v r u : ℝ)
    (i j : RealIndex N C u₀) : ℝ :=
  (precision N C u₀ A c u)⁻¹ j i *
    (firstMatrix N C u₀ A X c u v r - (2 * u * r) • precision N C u₀ A c u) i j / 2

def pairIntegrand (N : ℕ) (C u₀ : ℝ) (A X : Coefficients N) (c v r : ℝ)
    (i j : RealIndex N C u₀) (u : ℝ) : ℝ :=
  Real.exp (-u ^ 2 - (kinetic N C u₀ i + kinetic N C u₀ j) / 2) *
    pairMean N C u₀ A X c v r u i j

/-- The sum is over every pair, including all non-diagonal pairs. -/
theorem actual_mean_eq_pairSum (N : ℕ) (C u₀ : ℝ) (A X : Coefficients N)
    {c : ℝ} (hc : 0 < c) (u v r : ℝ) :
    (∫ x, score (first N C u₀ A X c u v r) x ∂law N C u₀ A c u) =
      ∑ i, ∑ j, pairIntegrand N C u₀ A X c v r i j u := by
  simp only [law]
  rw [Operations.FiniteMatrixGaussian.score_mean_trace (precision_posDef N C u₀ A hc u)]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [first, filteredMatrix_apply, pairIntegrand, pairMean]
  have he : Real.exp (-(u ^ 2 + kinetic N C u₀ i) / 2) *
      Real.exp (-(u ^ 2 + kinetic N C u₀ j) / 2) =
      Real.exp (-u ^ 2 - (kinetic N C u₀ i + kinetic N C u₀ j) / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = (Real.exp (-(u ^ 2 + kinetic N C u₀ i) / 2) *
      Real.exp (-(u ^ 2 + kinetic N C u₀ j) / 2)) *
      ((precision N C u₀ A c u)⁻¹ j i *
        (firstMatrix N C u₀ A X c u v r - (2 * u * r) • precision N C u₀ A c u) i j / 2) := by ring
    _ = _ := by rw [he]

/-- At fixed frequency the earlier row-weighted current and the actual
two-leg field-filtered current agree only up to this complete cross-entry
correction. Neither observation is discarded or called an endpoint law. -/
theorem original_row_mean_difference (N : ℕ) (C u₀ : ℝ) (A X : Coefficients N)
    {c : ℝ} (hc : 0 < c) (u v : ℝ) :
    (∑ i, HistoryHaarSectionCollectiveBoundary.integrand N C u₀ A X c v 0 i u) -
        (∫ x, score (first N C u₀ A X c u v 0) x ∂law N C u₀ A c u) =
      (∑ i, ∑ j, (precision N C u₀ A c u)⁻¹ j i *
        firstMatrix N C u₀ A X c u v 0 i j *
          (Real.exp (-(u ^ 2 + kinetic N C u₀ i) / 2) -
            Real.exp (-(u ^ 2 + kinetic N C u₀ j) / 2)) ^ 2) / 4 := by
  have h := row_filter_difference (precision N C u₀ A c u)⁻¹
    (firstMatrix N C u₀ A X c u v 0)
    (precision_posDef N C u₀ A hc u).inv.isHermitian.isSymm
    (HistoryHaarSectionFrequencyCollective.firstMatrix_symmetric N C u₀ A X c u v 0)
    (fun i => Real.exp (-(u ^ 2 + kinetic N C u₀ i) / 2))
  have he (i : RealIndex N C u₀) :
      Real.exp (-(u ^ 2 + kinetic N C u₀ i) / 2) ^ 2 =
        HistoryHaarSectionComparison.weight N (Sum.inr i.1.val) u := by
    rw [pow_two, ← Real.exp_add]
    unfold HistoryHaarSectionComparison.weight HistoryHaarSectionComparison.kineticPrecision
      kinetic HistoryHaarSectionCollectiveBoundary.kinetic
    congr 1
    ring
  have hl : (∑ i, HistoryHaarSectionCollectiveBoundary.integrand N C u₀ A X c v 0 i u) =
      (∑ i, ∑ j, (precision N C u₀ A c u)⁻¹ j i *
        firstMatrix N C u₀ A X c u v 0 i j *
          Real.exp (-(u ^ 2 + kinetic N C u₀ i) / 2) ^ 2) / 2 := by
    simp only [he, HistoryHaarSectionCollectiveBoundary.integrand,
      HistoryHaarSectionCollectiveBoundary.rowMean, row_trace, Finset.sum_div, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hr : (∫ x, score (first N C u₀ A X c u v 0) x ∂law N C u₀ A c u) =
      (∑ i, ∑ j, (precision N C u₀ A c u)⁻¹ j i *
        firstMatrix N C u₀ A X c u v 0 i j *
          (Real.exp (-(u ^ 2 + kinetic N C u₀ i) / 2) *
            Real.exp (-(u ^ 2 + kinetic N C u₀ j) / 2))) / 2 := by
    simp only [law]
    rw [Operations.FiniteMatrixGaussian.score_mean_trace (precision_posDef N C u₀ A hc u)]
    simp only [first, mul_zero, zero_smul, sub_zero, Matrix.trace,
      Matrix.diag, Matrix.mul_apply, filteredMatrix_apply]
    rw [Finset.sum_comm]
    apply congrArg (fun t : ℝ => t / 2)
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hl, hr]
  exact h

theorem pairIntegrand_continuous (N : ℕ) (C u₀ : ℝ) (A X : Coefficients N)
    {c : ℝ} (hc : 0 < c) (v r : ℝ) (i j : RealIndex N C u₀) :
    Continuous (pairIntegrand N C u₀ A X c v r i j) := by
  have hi : Continuous (fun u => (precision N C u₀ A c u)⁻¹) := by
    apply continuous_iff_continuousAt.mpr
    intro u
    have hp : DifferentiableAt ℝ (fun t => precision N C u₀ A c t) u := by
      unfold precision
      fun_prop
    exact (Operations.FiniteMatrixGaussian.inverse_hasDerivAt
      (precision_posDef N C u₀ A hc u) hp.hasDerivAt).continuousAt
  have hij : Continuous (fun u => (precision N C u₀ A c u)⁻¹ j i) :=
    (continuous_apply i).comp ((continuous_apply j).comp hi)
  unfold pairIntegrand pairMean
  apply Continuous.mul
  · fun_prop
  · apply Continuous.div_const
    apply hij.mul
    unfold firstMatrix precision
    fun_prop

/-- Both field legs must be present in the observation window. -/
def pairKinetic (N : ℕ) (C u₀ : ℝ) (i j : RealIndex N C u₀) : ℝ :=
  max (kinetic N C u₀ i) (kinetic N C u₀ j)

theorem pair_visible_iff (N : ℕ) (C u₀ u B : ℝ) (i j : RealIndex N C u₀) :
    u ^ 2 + pairKinetic N C u₀ i j < B ↔
      u ^ 2 + kinetic N C u₀ i < B ∧ u ^ 2 + kinetic N C u₀ j < B := by
  rw [pairKinetic, add_max, max_lt_iff]

def windowField (N : ℕ) (C u₀ u B : ℝ) (x : Space N C u₀) : Space N C u₀ :=
  WithLp.toLp 2 fun i => if u ^ 2 + kinetic N C u₀ i < B then
    Real.exp (-(u ^ 2 + kinetic N C u₀ i) / 2) * x i else 0

def windowInsertion (N : ℕ) (C u₀ u B : ℝ)
    (V : Matrix (RealIndex N C u₀) (RealIndex N C u₀) ℝ) :
    Matrix (RealIndex N C u₀) (RealIndex N C u₀) ℝ :=
  fun i j => if u ^ 2 + pairKinetic N C u₀ i j < B then
    filteredMatrix N C u₀ u V i j else 0

/-- Pair support is obtained by applying the actual finite observation
to the field, not by selecting covariance rows after expectation. -/
theorem window_score_eq_original (N : ℕ) (C u₀ u B : ℝ)
    (V : Matrix (RealIndex N C u₀) (RealIndex N C u₀) ℝ) (x : Space N C u₀) :
    score (windowInsertion N C u₀ u B V) x = score V (windowField N C u₀ u B x) := by
  simp only [score, windowField, WithLp.ofLp_toLp]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hi : u ^ 2 + kinetic N C u₀ i < B <;>
    by_cases hj : u ^ 2 + kinetic N C u₀ j < B
  all_goals simp [windowInsertion, pair_visible_iff, hi, hj, filteredMatrix_apply]
  ring

def pairIntegral (N : ℕ) (C u₀ : ℝ) (A X : Coefficients N) (c v r B : ℝ)
    (i j : RealIndex N C u₀) : ℝ :=
  ∫ u in (0 : ℝ)..Real.sqrt (B - pairKinetic N C u₀ i j),
    pairIntegrand N C u₀ A X c v r i j u

def response (N : ℕ) (C u₀ : ℝ) (A X : Coefficients N) (c v r B : ℝ) : ℝ :=
  ∑ i, ∑ j, pairIntegral N C u₀ A X c v r B i j

/-- Unequal angular energies retain their exact factor at the common
pair edge; replacing it by a common Gaussian factor alone loses data. -/
theorem pair_weight_at_edge (N : ℕ) (C u₀ B : ℝ) (i j : RealIndex N C u₀)
    (hB : pairKinetic N C u₀ i j < B) :
    Real.exp (-(Real.sqrt (B - pairKinetic N C u₀ i j)) ^ 2 -
      (kinetic N C u₀ i + kinetic N C u₀ j) / 2) =
      Real.exp (-B) * Real.exp (|kinetic N C u₀ i - kinetic N C u₀ j| / 2) := by
  rw [Real.sq_sqrt (sub_pos.mpr hB).le, ← Real.exp_add]
  congr 1
  unfold pairKinetic
  by_cases h : kinetic N C u₀ i ≤ kinetic N C u₀ j
  · rw [max_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [max_eq_left (le_of_not_ge h), abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge h))]
    ring

def pairEdge (N : ℕ) (C u₀ : ℝ) (A X : Coefficients N) (c v r B : ℝ)
    (i j : RealIndex N C u₀) : ℝ :=
  if pairKinetic N C u₀ i j < B then
    Real.exp (|kinetic N C u₀ i - kinetic N C u₀ j| / 2) *
      pairMean N C u₀ A X c v r (Real.sqrt (B - pairKinetic N C u₀ i j)) i j /
        (2 * Real.sqrt (B - pairKinetic N C u₀ i j)) else 0

theorem pairIntegral_at_birth (N : ℕ) (C u₀ : ℝ) (A X : Coefficients N)
    (c v r : ℝ) (i j : RealIndex N C u₀) :
    pairIntegral N C u₀ A X c v r (pairKinetic N C u₀ i j) i j = 0 := by
  simp only [pairIntegral, sub_self, Real.sqrt_zero, intervalIntegral.integral_same]

theorem pairIntegral_continuous (N : ℕ) (C u₀ : ℝ) (A X : Coefficients N)
    {c : ℝ} (hc : 0 < c) (v r : ℝ) (i j : RealIndex N C u₀) :
    Continuous (fun B => pairIntegral N C u₀ A X c v r B i j) :=
  (intervalIntegral.differentiable_integral_of_continuous
    (pairIntegrand_continuous N C u₀ A X hc v r i j)).continuous.comp
      (Real.continuous_sqrt.comp (continuous_id.sub continuous_const))

theorem pairIntegral_hasDerivAt (N : ℕ) (C u₀ : ℝ) (A X : Coefficients N)
    {c : ℝ} (hc : 0 < c) (v r : ℝ) (i j : RealIndex N C u₀) {B : ℝ}
    (hB : pairKinetic N C u₀ i j ≠ B) :
    HasDerivAt (fun b => pairIntegral N C u₀ A X c v r b i j)
      (Real.exp (-B) * pairEdge N C u₀ A X c v r B i j) B := by
  have hf := pairIntegrand_continuous N C u₀ A X hc v r i j
  by_cases h : pairKinetic N C u₀ i j < B
  · have hs := ((hasDerivAt_id B).sub_const (pairKinetic N C u₀ i j)).sqrt (sub_pos.mpr h).ne'
    have hi := intervalIntegral.integral_hasDerivAt_right
      (hf.intervalIntegrable 0 (Real.sqrt (B - pairKinetic N C u₀ i j)))
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
    have he := pair_weight_at_edge N C u₀ B i j h
    convert! hi.comp B hs using 1
    simp only [pairEdge, ite_eq_left h, pairIntegrand, he, id_eq, mul_one_div]
    ring
  · have hl : B < pairKinetic N C u₀ i j := lt_of_le_of_ne (le_of_not_gt h) hB.symm
    have hz : HasDerivAt (fun b => pairIntegral N C u₀ A X c v r b i j) 0 B := by
      apply (hasDerivAt_const B (0 : ℝ)).congr_of_eventuallyEq
      filter_upwards [isOpen_Iio.mem_nhds hl] with b hb
      simp only [pairIntegral, Real.sqrt_eq_zero'.mpr (sub_nonpos.mpr hb.le),
        intervalIntegral.integral_same]
    simpa only [pairEdge, ite_eq_right h, mul_zero] using! hz

theorem response_continuous (N : ℕ) (C u₀ : ℝ) (A X : Coefficients N)
    {c : ℝ} (hc : 0 < c) (v r : ℝ) : Continuous (response N C u₀ A X c v r) :=
  continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    pairIntegral_continuous N C u₀ A X hc v r i j

theorem response_hasDerivAt (N : ℕ) (C u₀ : ℝ) (A X : Coefficients N)
    {c : ℝ} (hc : 0 < c) (v r : ℝ) {B : ℝ}
    (hregular : ∀ i j : RealIndex N C u₀, pairKinetic N C u₀ i j ≠ B) :
    HasDerivAt (response N C u₀ A X c v r)
      (Real.exp (-B) * ∑ i, ∑ j, pairEdge N C u₀ A X c v r B i j) B := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
      pairIntegral_hasDerivAt N C u₀ A X hc v r i j (hregular i j)
  simpa only [response, Finset.mul_sum] using! h

/-- Marginalization retains the insertion filtered on both field legs,
and returns the entire conditional covariance, including its cross terms. -/
theorem full_mean_eq_retained_add_conditional (N : ℕ) {D C : ℝ} (hDC : D ≤ C)
    (u₀ : ℝ) (A X : Coefficients N) {c : ℝ} (hc : 0 < c) (u v r : ℝ) :
    (∫ x, score (first N C u₀ A X c u v r) x ∂law N C u₀ A c u) =
      (∫ x, score (Operations.FiniteMatrixGaussian.retainedInsertion
          (precision N C u₀ A c u) (first N C u₀ A X c u v r)
          (HistoryHaarSectionConnectionMarginal.embed N hDC u₀)) x
        ∂HistoryHaarSectionFrequencyCollective.observedLaw N hDC u₀ A c u) +
      Matrix.trace (Operations.FiniteMatrixGaussian.conditionalCovariance
        (precision N C u₀ A c u) (HistoryHaarSectionConnectionMarginal.embed N hDC u₀) *
          first N C u₀ A X c u v r) / 2 :=
  Operations.FiniteMatrixGaussian.full_mean_eq_retained_add_conditional
    (precision_posDef N C u₀ A hc u)
    (HistoryHaarSectionConnectionMarginal.embed_injective N hDC u₀) _

def retainedPairIntegrand (N : ℕ) {D C : ℝ} (hDC : D ≤ C) (u₀ : ℝ)
    (A X : Coefficients N) (c v r : ℝ) (i j : RealIndex N C u₀) (u : ℝ) : ℝ :=
  Real.exp (-u ^ 2 - (kinetic N C u₀ i + kinetic N C u₀ j) / 2) *
    (Operations.FiniteMatrixGaussian.returnCovariance (precision N C u₀ A c u)
      (HistoryHaarSectionConnectionMarginal.embed N hDC u₀) j i *
        (firstMatrix N C u₀ A X c u v r - (2 * u * r) • precision N C u₀ A c u) i j / 2)

def conditionalPairIntegrand (N : ℕ) {D C : ℝ} (hDC : D ≤ C) (u₀ : ℝ)
    (A X : Coefficients N) (c v r : ℝ) (i j : RealIndex N C u₀) (u : ℝ) : ℝ :=
  Real.exp (-u ^ 2 - (kinetic N C u₀ i + kinetic N C u₀ j) / 2) *
    (Operations.FiniteMatrixGaussian.conditionalCovariance (precision N C u₀ A c u)
      (HistoryHaarSectionConnectionMarginal.embed N hDC u₀) j i *
        (firstMatrix N C u₀ A X c u v r - (2 * u * r) • precision N C u₀ A c u) i j / 2)

theorem pair_return_balance (N : ℕ) {D C : ℝ} (hDC : D ≤ C) (u₀ : ℝ)
    (A X : Coefficients N) (c v r u : ℝ) (i j : RealIndex N C u₀) :
    pairIntegrand N C u₀ A X c v r i j u =
      retainedPairIntegrand N hDC u₀ A X c v r i j u +
        conditionalPairIntegrand N hDC u₀ A X c v r i j u := by
  simp only [pairIntegrand, pairMean, retainedPairIntegrand, conditionalPairIntegrand,
    Operations.FiniteMatrixGaussian.conditionalCovariance, Matrix.sub_apply]
  ring

private def submatrixMap {ι κ η : Type*} [Fintype ι] [Fintype κ] [Fintype η]
    (e : κ → ι) (f : η → ι) : Matrix ι ι ℝ →L[ℝ] Matrix κ η ℝ :=
  ({ toFun := fun M => M.submatrix e f
     map_add' := by intros; rfl
     map_smul' := by intros; rfl } :
    Matrix ι ι ℝ →ₗ[ℝ] Matrix κ η ℝ).toContinuousLinearMap

theorem retainedPairIntegrand_continuous (N : ℕ) {D C : ℝ} (hDC : D ≤ C) (u₀ : ℝ)
    (A X : Coefficients N) {c : ℝ} (hc : 0 < c) (v r : ℝ)
    (i j : RealIndex N C u₀) :
    Continuous (retainedPairIntegrand N hDC u₀ A X c v r i j) := by
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
  have hk := (hl.matrix_mul hs).matrix_mul hr
  have hji := (continuous_apply i).comp ((continuous_apply j).comp hk)
  unfold retainedPairIntegrand Operations.FiniteMatrixGaussian.returnCovariance
  apply Continuous.mul
  · fun_prop
  · apply Continuous.div_const
    apply hji.mul
    unfold firstMatrix precision
    fun_prop

theorem conditionalPairIntegrand_continuous (N : ℕ) {D C : ℝ} (hDC : D ≤ C) (u₀ : ℝ)
    (A X : Coefficients N) {c : ℝ} (hc : 0 < c) (v r : ℝ)
    (i j : RealIndex N C u₀) :
    Continuous (conditionalPairIntegrand N hDC u₀ A X c v r i j) := by
  have he : conditionalPairIntegrand N hDC u₀ A X c v r i j =
      fun u => pairIntegrand N C u₀ A X c v r i j u -
        retainedPairIntegrand N hDC u₀ A X c v r i j u := by
    funext u
    linarith [pair_return_balance N hDC u₀ A X c v r u i j]
  rw [he]
  exact (pairIntegrand_continuous N C u₀ A X hc v r i j).sub
    (retainedPairIntegrand_continuous N hDC u₀ A X hc v r i j)

def retainedResponse (N : ℕ) {D C : ℝ} (hDC : D ≤ C) (u₀ : ℝ)
    (A X : Coefficients N) (c v r B : ℝ) : ℝ :=
  ∑ i, ∑ j, ∫ u in (0 : ℝ)..Real.sqrt (B - pairKinetic N C u₀ i j),
    retainedPairIntegrand N hDC u₀ A X c v r i j u

def conditionalResponse (N : ℕ) {D C : ℝ} (hDC : D ≤ C) (u₀ : ℝ)
    (A X : Coefficients N) (c v r B : ℝ) : ℝ :=
  ∑ i, ∑ j, ∫ u in (0 : ℝ)..Real.sqrt (B - pairKinetic N C u₀ i j),
    conditionalPairIntegrand N hDC u₀ A X c v r i j u

/-- The actual two-leg moving window has its own complete Schur ledger.
The integration edge, Gaussian factor, and signed pair coefficient are
identical in the complete, retained, and conditional responses. -/
theorem response_return_balance (N : ℕ) {D C : ℝ} (hDC : D ≤ C) (u₀ : ℝ)
    (A X : Coefficients N) {c : ℝ} (hc : 0 < c) (v r B : ℝ) :
    response N C u₀ A X c v r B = retainedResponse N hDC u₀ A X c v r B +
      conditionalResponse N hDC u₀ A X c v r B := by
  unfold response pairIntegral retainedResponse conditionalResponse
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hsum := intervalIntegral.integral_add (μ := volume)
    ((retainedPairIntegrand_continuous N hDC u₀ A X hc v r i j).intervalIntegrable
      0 (Real.sqrt (B - pairKinetic N C u₀ i j)))
    ((conditionalPairIntegrand_continuous N hDC u₀ A X hc v r i j).intervalIntegrable
      0 (Real.sqrt (B - pairKinetic N C u₀ i j)))
  calc
    _ = ∫ u in (0 : ℝ)..Real.sqrt (B - pairKinetic N C u₀ i j),
        (retainedPairIntegrand N hDC u₀ A X c v r i j u +
          conditionalPairIntegrand N hDC u₀ A X c v r i j u) := by
      apply intervalIntegral.integral_congr
      intro u _
      exact pair_return_balance N hDC u₀ A X c v r u i j
    _ = _ := by simpa only [Pi.add_apply] using! hsum

structure Conclusions : Prop where
  original_field_filter : ∀ N C u₀ V u (x : Space N C u₀),
    score (filteredMatrix N C u₀ u V) x = score V (filterField N C u₀ u x)
  actual_filtered_response : ∀ N C u₀ A X Y c, 0 < c → ∀ u v w r q,
    HasDerivAt (fun t : ℝ => ∫ x,
      score (first N C u₀ (A + (t : ℂ) • Y) X (scalePath c w t) (u + q * t) v r) x
        ∂law N C u₀ (A + (t : ℂ) • Y) (scalePath c w t) (u + q * t))
      ((∫ x, score (direct N C u₀ A X Y c u v w r q) x ∂law N C u₀ A c u) -
        cov[score (first N C u₀ A X c u v r),
          score (firstMatrix N C u₀ A Y c u w q); law N C u₀ A c u]) 0
  all_pair_mean : ∀ N C u₀ A X c, 0 < c → ∀ u v r,
    (∫ x, score (first N C u₀ A X c u v r) x ∂law N C u₀ A c u) =
      ∑ i, ∑ j, pairIntegrand N C u₀ A X c v r i j u
  actual_pair_boundary : ∀ N C u₀ A X c, 0 < c → ∀ v r B,
    (∀ i j : RealIndex N C u₀, pairKinetic N C u₀ i j ≠ B) →
    HasDerivAt (response N C u₀ A X c v r)
      (Real.exp (-B) * ∑ i, ∑ j, pairEdge N C u₀ A X c v r B i j) B
  continuous_pair_births : ∀ N C u₀ A X c, 0 < c → ∀ v r,
    Continuous (response N C u₀ A X c v r)
  complete_pair_window_ledger : ∀ N D C (hDC : D ≤ C) u₀ A X c, 0 < c → ∀ v r B,
    response N C u₀ A X c v r B = retainedResponse N hDC u₀ A X c v r B +
      conditionalResponse N hDC u₀ A X c v r B

theorem generated : Conclusions where
  original_field_filter := fun N C u₀ V u x => filtered_score_eq_original N C u₀ u V x
  actual_filtered_response := fun N C u₀ A X Y _ hc u v w r q =>
    actual_mean_hasDerivAt N C u₀ A X Y hc u v w r q
  all_pair_mean := fun N C u₀ A X _ hc u v r => actual_mean_eq_pairSum N C u₀ A X hc u v r
  actual_pair_boundary := fun N C u₀ A X _ hc v r _ h => response_hasDerivAt N C u₀ A X hc v r h
  continuous_pair_births := fun N C u₀ A X _ hc v r => response_continuous N C u₀ A X hc v r
  complete_pair_window_ledger := fun N _ _ hDC u₀ A X _ hc v r B =>
    response_return_balance N hDC u₀ A X hc v r B

end GeneratedFoundations.Arithmetic.HistoryHaarSectionFilteredCollective

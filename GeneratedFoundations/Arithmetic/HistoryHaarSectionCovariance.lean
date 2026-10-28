module

public import GeneratedFoundations.Arithmetic.HistoryHaarSectionProbability
public import GeneratedFoundations.Operations.GaussianPrecisionMoments

/-!
# Unique covariance of the actual finite joint Gaussian precision

The original action fixes the joint Hessian. At a frequency `u`, the
observation keeps exactly the original labels with `u^2 + kinetic < B`.
The covariance is the inverse of that complete positive precision matrix.
Its uniqueness is proved among all matrices, without assuming diagonal
covariance or discarding cross-sector entries. Diagonality is a consequence
in the actual Hessian eigenbasis, not a constraint on the competitors.

Each real-coordinate variance is also the second moment of the existing
precision Gaussian. The total variance is its complete spectral sum; it
is not defined to equal a centre susceptibility or a component count.
An isotropic covariance is possible precisely when all retained precisions
coincide. Thus isotropic local-fibre normalization and full-field covariance
remain distinct objects.
-/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryHaarSectionCovariance

open HistoryHaarSectionJointHessian (Index)
open HistoryHaarSectionComparison (precision precision_pos)
open HistoryHaarSectionWindow (support kinetic)

local instance (N : ℕ) : DecidableEq (Index N) := Classical.decEq _

def frequencySupport (N : ℕ) (B u : ℝ) : Finset (Index N) := support N (B - u ^ 2)

theorem mem_frequencySupport (N : ℕ) (B u : ℝ) (i : Index N) :
    i ∈ frequencySupport N B u ↔ u ^ 2 + kinetic N i < B := by
  rw [frequencySupport, HistoryHaarSectionWindow.mem_support]
  constructor <;> intro h <;> linarith

abbrev WindowIndex (N : ℕ) (B u : ℝ) := ↥(frequencySupport N B u)
abbrev WindowMatrix (N : ℕ) (B u : ℝ) :=
  Matrix (WindowIndex N B u) (WindowIndex N B u) ℝ

def precisionMatrix (N : ℕ) (B u : ℝ) : WindowMatrix N B u :=
  Matrix.diagonal fun i => precision N i.val u

def covarianceMatrix (N : ℕ) (B u : ℝ) : WindowMatrix N B u :=
  Matrix.diagonal fun i => (precision N i.val u)⁻¹

theorem precision_mul_covariance (N : ℕ) (B u : ℝ) :
    precisionMatrix N B u * covarianceMatrix N B u = 1 := by
  unfold precisionMatrix covarianceMatrix
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst j
    simp [(precision_pos N i.val u).ne']
  · simp [h]

theorem covariance_mul_precision (N : ℕ) (B u : ℝ) :
    covarianceMatrix N B u * precisionMatrix N B u = 1 := by
  unfold precisionMatrix covarianceMatrix
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst j
    simp [(precision_pos N i.val u).ne']
  · simp [h]

/-- No isotropy or diagonality assumption is imposed on `C`. -/
theorem covariance_unique (N : ℕ) (B u : ℝ) (C : WindowMatrix N B u)
    (hC : precisionMatrix N B u * C = 1) : C = covarianceMatrix N B u := by
  calc
    C = (covarianceMatrix N B u * precisionMatrix N B u) * C := by
      rw [covariance_mul_precision, one_mul]
    _ = covarianceMatrix N B u := by rw [Matrix.mul_assoc, hC, mul_one]

theorem covariance_existsUnique (N : ℕ) (B u : ℝ) :
    ∃! C : WindowMatrix N B u, precisionMatrix N B u * C = 1 :=
  ⟨covarianceMatrix N B u, precision_mul_covariance N B u,
    fun C hC => covariance_unique N B u C hC⟩

theorem covariance_entry (N : ℕ) (B u : ℝ) (i j : WindowIndex N B u) :
    covarianceMatrix N B u i j =
      if i = j then (precision N i.val u)⁻¹ else 0 := rfl

theorem covariance_diagonal_pos (N : ℕ) (B u : ℝ) (i : WindowIndex N B u) :
    0 < covarianceMatrix N B u i i := by
  simp only [covarianceMatrix, Matrix.diagonal_apply_eq]
  exact inv_pos.mpr (precision_pos N i.val u)

theorem covariance_eq_second_moment (N : ℕ) (B u : ℝ) (i : WindowIndex N B u) :
    covarianceMatrix N B u i i =
      ∫ x : ℝ, x ^ 2 ∂Operations.GaussianPrecisionKL.law (precision N i.val u) := by
  rw [Operations.GaussianPrecisionKL.square_integral (precision_pos N i.val u)]
  simp [covarianceMatrix]

def totalVariance (N : ℕ) (B u : ℝ) : ℝ := Matrix.trace (covarianceMatrix N B u)

theorem totalVariance_eq (N : ℕ) (B u : ℝ) :
    totalVariance N B u =
      ∑ i ∈ frequencySupport N B u, (precision N i u)⁻¹ := by
  simp only [totalVariance, covarianceMatrix, Matrix.trace_diagonal]
  exact Finset.sum_attach (frequencySupport N B u) (fun i => (precision N i u)⁻¹)

theorem isotropic_iff_constant_precision (N : ℕ) (B u v : ℝ) :
    covarianceMatrix N B u = v • (1 : WindowMatrix N B u) ↔
      ∀ i : WindowIndex N B u, v = (precision N i.val u)⁻¹ := by
  constructor
  · intro h i
    have he := congrArg (fun C : WindowMatrix N B u => C i i) h
    simpa [covarianceMatrix] using he.symm
  · intro h
    ext i j
    by_cases hij : i = j
    · subst j
      simp [covarianceMatrix, h i]
    · simp [covarianceMatrix, hij]

/-- Distinct actual eigenvalues exclude isotropy in that same window. -/
theorem not_isotropic_of_distinct_precision (N : ℕ) (B u : ℝ)
    (i j : WindowIndex N B u) (hij : precision N i.val u ≠ precision N j.val u) :
    ¬ ∃ v : ℝ, covarianceMatrix N B u = v • (1 : WindowMatrix N B u) := by
  rintro ⟨v, hv⟩
  have he := (isotropic_iff_constant_precision N B u v).mp hv
  exact hij (inv_injective ((he i).symm.trans (he j)))

theorem defining_coefficient_ne_four (N : ℕ) : HistoryDefiningResponse.coefficient N ≠ 4 := by
  intro h
  have hd : 0 < (HistoryAdjointCasimir.dimension N : ℝ) :=
    Nat.cast_pos.mpr (HistoryAdjointCasimir.dimension_pos N)
  rw [HistoryDefiningResponse.coefficient_eq] at h
  have he : (HistoryAdjointCasimir.dimension N : ℝ) -
      (HistoryAdjointCasimir.dimension N : ℝ)⁻¹ = 8 := by linarith
  have hp := congrArg (fun t : ℝ => (HistoryAdjointCasimir.dimension N : ℝ) * t) he
  simp only [mul_sub, mul_inv_cancel₀ hd.ne'] at hp
  by_cases hs : HistoryAdjointCasimir.dimension N ≤ 8
  · have hr : (HistoryAdjointCasimir.dimension N : ℝ) ≤ 8 := by exact_mod_cast hs
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hd.le (sub_nonpos.mpr hr)]
  · have hn : 9 ≤ HistoryAdjointCasimir.dimension N := by omega
    have hr : 9 ≤ (HistoryAdjointCasimir.dimension N : ℝ) := by exact_mod_cast hn
    nlinarith [mul_nonneg (sub_nonneg.mpr hr) (by linarith :
      0 ≤ (HistoryAdjointCasimir.dimension N : ℝ) + 1)]

/-- Once both original lowest sectors are visible their unequal actual
precisions rule out a scalar covariance on the complete field window. -/
theorem actual_window_not_isotropic (N : ℕ) (B u : ℝ) (hB : u ^ 2 + 4 < B) :
    ¬ ∃ v : ℝ, covarianceMatrix N B u = v • (1 : WindowMatrix N B u) := by
  let i : Index N := .inl (HistoryHaarClosedHessian.minimizingIndex N)
  let j : Index N := .inr (HistoryHaarSectionHessian.minimizingIndex N)
  have hi : kinetic N i = 4 := HistoryHaarClosedHessian.eigenvalue_minimizingIndex N
  have hj : kinetic N j = 0 := by
    simp [j, kinetic, HistoryHaarSectionHessian.minimizingIndex,
      Geometry.SourceCasimirClosure.energy]
  let wi : WindowIndex N B u := ⟨i, (mem_frequencySupport N B u i).mpr (by rw [hi]; exact hB)⟩
  let wj : WindowIndex N B u := ⟨j, (mem_frequencySupport N B u j).mpr (by rw [hj]; linarith)⟩
  apply not_isotropic_of_distinct_precision N B u wi wj
  have he : HistoryHaarSectionJointHessian.eigenvalue N i = 4 :=
    HistoryHaarClosedHessian.eigenvalue_minimizingIndex N
  have hf : HistoryHaarSectionJointHessian.eigenvalue N j =
      HistoryDefiningResponse.coefficient N := HistoryHaarSectionHessian.eigenvalue_minimizingIndex N
  change u ^ 2 + HistoryHaarSectionJointHessian.eigenvalue N i ≠
    u ^ 2 + HistoryHaarSectionJointHessian.eigenvalue N j
  rw [he, hf]
  exact fun h => defining_coefficient_ne_four N (add_left_cancel h).symm

structure Conclusions : Prop where
  original_frequency_cutoff : ∀ N B u i,
    i ∈ frequencySupport N B u ↔ u ^ 2 + kinetic N i < B
  exact_precision_inverse : ∀ N B u,
    precisionMatrix N B u * covarianceMatrix N B u = 1
  unique_complete_covariance : ∀ N B u,
    ∃! C : WindowMatrix N B u, precisionMatrix N B u * C = 1
  original_gaussian_moments : ∀ N B u (i : WindowIndex N B u),
    covarianceMatrix N B u i i =
      ∫ x : ℝ, x ^ 2 ∂Operations.GaussianPrecisionKL.law (precision N i.val u)
  full_total_variance : ∀ N B u,
    totalVariance N B u =
      ∑ i ∈ frequencySupport N B u, (precision N i u)⁻¹
  isotropy_classification : ∀ N B u v,
    covarianceMatrix N B u = v • (1 : WindowMatrix N B u) ↔
      ∀ i : WindowIndex N B u, v = (precision N i.val u)⁻¹
  nonuniform_actual_window : ∀ N B u, u ^ 2 + 4 < B →
    ¬ ∃ v : ℝ, covarianceMatrix N B u = v • (1 : WindowMatrix N B u)

theorem generated : Conclusions where
  original_frequency_cutoff := mem_frequencySupport
  exact_precision_inverse := precision_mul_covariance
  unique_complete_covariance := covariance_existsUnique
  original_gaussian_moments := covariance_eq_second_moment
  full_total_variance := totalVariance_eq
  isotropy_classification := isotropic_iff_constant_precision
  nonuniform_actual_window := actual_window_not_isotropic

end GeneratedFoundations.Arithmetic.HistoryHaarSectionCovariance

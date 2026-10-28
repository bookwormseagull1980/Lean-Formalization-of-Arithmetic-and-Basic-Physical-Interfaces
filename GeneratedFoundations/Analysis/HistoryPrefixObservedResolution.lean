module

public import GeneratedFoundations.Analysis.HistoryPrefixNonlinearResponse
public import GeneratedFoundations.Analysis.HistoryPrefixResolutionResponse
public import GeneratedFoundations.Operations.GibbsSchurResponse

/-!
# Gaussian resolution at finite observations of the native prefix

A fixed finite diagonal observation multiplies each original positive
root--history--phase intensity by its exact likelihood. The actual Gaussian
resolution changes its log intensity by the same root-square energy as
before observation. The complete matrix Hessian, its mixed terms and the
recomputed Schur response therefore have an exact resolution ledger.

The observation is fixed, but its perturbation directions are arbitrary
Hermitian matrices. No commutativity of those directions is assumed. This
operation changes the Gaussian reference at fixed L; the separate nonlinear
heat compensation transports the observation as well.
-/

@[expose] public section
noncomputable section
open scoped BigOperators NNReal Matrix.Norms.Operator

namespace GeneratedFoundations.Analysis.HistoryPrefixObservedResolution

open Operations Operations.PreparedTraceForm
open GibbsExponentialDifferentiation (expDividedDifference)
open HistoryPrefixGibbsResponse
open HistoryPrefixNonlinearResponse (tiltedLog tiltedMean diagonal_hessian)
open HistoryPrefixResolutionResponse (rootEnergy rootEnergy_lower rootEnergy_nonneg)

def form (N : ℕ) (alpha L : ℝ) (f : Index N → ℝ) :
    LinearMap.BilinForm ℝ (Hermitian (Index N)) :=
  GibbsSchurResponse.form (tiltedLog N alpha L f)

def partition (N : ℕ) (alpha L : ℝ) (f : Index N → ℝ) : ℝ :=
  GibbsTraceForm.Z (tiltedLog N alpha L f)

def restored (N : ℕ) (alpha L : ℝ) (f : Index N → ℝ)
    (K J : Hermitian (Index N)) : ℝ := partition N alpha L f * form N alpha L f K J

def matrixMean (N : ℕ) (alpha L : ℝ) (f : Index N → ℝ)
    (K : Hermitian (Index N)) : ℝ := GibbsTraceForm.mean (tiltedLog N alpha L f) (K : Mat (Index N))

theorem partition_likelihood (N : ℕ) (alpha L : ℝ) (f : Index N → ℝ) :
    partition N alpha L f = ∑ i, intensity N alpha L i * Real.exp (f i) := by
  simp only [partition, GibbsTraceForm.Z, HistoryPrefixNonlinearResponse.exp_tiltedLog]

theorem form_hessian (N : ℕ) (alpha L : ℝ) (f : Index N → ℝ)
    (K J : Hermitian (Index N)) :
    form N alpha L f K J =
      fderiv ℝ (fderiv ℝ (response N alpha L)) (diagonalObservation f) K J :=
  (diagonal_hessian N alpha L f K J).symm

/-- Likelihoods are retained before comparing references. The conditional
fibre probability and the finite observation both cancel in this difference. -/
theorem tiltedLog_shift (N : ℕ) (alpha L t : ℝ) (f : Index N → ℝ) (i : Index N) :
    tiltedLog N (alpha + t) L f i = tiltedLog N alpha L f i - t * rootEnergy N L i := by
  simp only [tiltedLog, HistoryPrefixResolutionResponse.logIntensity_shift]
  ring

theorem tiltedLog_nonincreasing (N : ℕ) (alpha L : ℝ) (t : ℝ≥0)
    (f : Index N → ℝ) (i : Index N) :
    tiltedLog N (alpha + (t : ℝ)) L f i ≤ tiltedLog N alpha L f i := by
  rw [tiltedLog_shift]
  exact sub_le_self _ (mul_nonneg t.property (rootEnergy_nonneg N L i))

/-- Both the prefix size and the finite likelihood disappear from the
contraction factor, which remains the actual unit-root multiplier at L. -/
theorem complete_kernel_contraction (N : ℕ) (alpha L : ℝ) (t : ℝ≥0)
    (f : Index N → ℝ) (i j : Index N) :
    expDividedDifference (tiltedLog N (alpha + (t : ℝ)) L f i)
        (tiltedLog N (alpha + (t : ℝ)) L f j) ≤
      Real.exp (-(t : ℝ) / L ^ 2) *
        expDividedDifference (tiltedLog N alpha L f i) (tiltedLog N alpha L f j) := by
  have h (k : Index N) : tiltedLog N (alpha + (t : ℝ)) L f k ≤
      tiltedLog N alpha L f k - (t : ℝ) / L ^ 2 := by
    rw [tiltedLog_shift]
    have he := mul_le_mul_of_nonneg_left (rootEnergy_lower N L k) t.property
    simpa only [one_div, div_eq_mul_inv, one_mul] using!
      sub_le_sub_left he (tiltedLog N alpha L f k)
  simpa only [neg_div] using GibbsResolutionLedger.divided_difference_le_shift (h i) (h j)

def kernelLoss (N : ℕ) (alpha L : ℝ) (t : ℝ≥0) (f : Index N → ℝ)
    (K : Hermitian (Index N)) : ℝ :=
  GibbsResolutionLedger.kernelLoss (tiltedLog N alpha L f)
    (tiltedLog N (alpha + (t : ℝ)) L f) (K : Mat (Index N))

def meanLoss (N : ℕ) (alpha L : ℝ) (t : ℝ≥0) (f : Index N → ℝ)
    (K : Hermitian (Index N)) : ℝ :=
  partition N (alpha + (t : ℝ)) L f *
    (matrixMean N (alpha + (t : ℝ)) L f K - matrixMean N alpha L f K) ^ 2

/-- The mixed ledger retains the complete noncommuting perturbations in
the same observed state and its actual change of means. -/
theorem complete_mixed_ledger (N : ℕ) (alpha L : ℝ) (t : ℝ≥0)
    (f : Index N → ℝ) (K J : Hermitian (Index N)) :
    restored N alpha L f K J - restored N (alpha + (t : ℝ)) L f K J =
      GibbsTraceForm.responsePairing (tiltedLog N alpha L f)
        (GibbsTraceForm.centered (tiltedLog N alpha L f) (K : Mat (Index N)))
        (GibbsTraceForm.centered (tiltedLog N alpha L f) (J : Mat (Index N))) -
      GibbsTraceForm.responsePairing (tiltedLog N (alpha + (t : ℝ)) L f)
        (GibbsTraceForm.centered (tiltedLog N alpha L f) (K : Mat (Index N)))
        (GibbsTraceForm.centered (tiltedLog N alpha L f) (J : Mat (Index N))) +
      partition N (alpha + (t : ℝ)) L f *
        (matrixMean N (alpha + (t : ℝ)) L f K - matrixMean N alpha L f K) *
        (matrixMean N (alpha + (t : ℝ)) L f J - matrixMean N alpha L f J) :=
  GibbsResolutionLedger.restored_difference _ _ _ _

theorem complete_square_ledger (N : ℕ) (alpha L : ℝ) (t : ℝ≥0)
    (f : Index N → ℝ) (K : Hermitian (Index N)) :
    restored N alpha L f K K = restored N (alpha + (t : ℝ)) L f K K +
      kernelLoss N alpha L t f K + meanLoss N alpha L t f K :=
  GibbsResolutionLedger.restored_square_ledger (hermitian_isHermitian _ K)

theorem kernelLoss_nonneg (N : ℕ) (alpha L : ℝ) (t : ℝ≥0)
    (f : Index N → ℝ) (K : Hermitian (Index N)) : 0 ≤ kernelLoss N alpha L t f K :=
  GibbsResolutionLedger.kernelLoss_nonneg (tiltedLog_nonincreasing N alpha L t f) _

theorem meanLoss_nonneg (N : ℕ) (alpha L : ℝ) (t : ℝ≥0)
    (f : Index N → ℝ) (K : Hermitian (Index N)) : 0 ≤ meanLoss N alpha L t f K :=
  mul_nonneg (GibbsTraceForm.Z_pos _).le (sq_nonneg _)

theorem complete_response_contraction (N : ℕ) (alpha L : ℝ) (t : ℝ≥0)
    (f : Index N → ℝ) (K : Hermitian (Index N)) :
    restored N (alpha + (t : ℝ)) L f K K ≤
      Real.exp (-(t : ℝ) / L ^ 2) * restored N alpha L f K K :=
  GibbsResolutionLedger.restored_contraction (complete_kernel_contraction N alpha L t f)
    (hermitian_isHermitian _ K)

def residual (N : ℕ) (alpha L : ℝ) (f : Index N → ℝ)
    (K J : Hermitian (Index N)) : Hermitian (Index N) :=
  GibbsSchurResponse.residual (tiltedLog N alpha L f) K J

theorem schur_identity (N : ℕ) (alpha L : ℝ) (f : Index N → ℝ)
    (K J : Hermitian (Index N)) :
    form N alpha L f K K = form N alpha L f
        (residual N alpha L f K J) (residual N alpha L f K J) +
      form N alpha L f K J ^ 2 / form N alpha L f J J :=
  GibbsSchurResponse.schur_identity _ _ _

theorem reduced_response_contraction (N : ℕ) (alpha L : ℝ) (t : ℝ≥0)
    (f : Index N → ℝ) (K J : Hermitian (Index N)) :
    restored N (alpha + (t : ℝ)) L f
        (residual N (alpha + (t : ℝ)) L f K J)
        (residual N (alpha + (t : ℝ)) L f K J) ≤
      Real.exp (-(t : ℝ) / L ^ 2) *
        restored N alpha L f (residual N alpha L f K J) (residual N alpha L f K J) :=
  GibbsSchurResponse.reduced_contraction (complete_kernel_contraction N alpha L t f) K J

/-- The native Mobius/support block keeps its actual, possibly nonzero,
mean and its square-free support fraction at this finite observation. -/
theorem probe_support_ledger (N : ℕ) (alpha L : ℝ) (t : ℝ≥0) (f : Index N → ℝ) :
    restored N alpha L f
        (diagonalObservation (HistoryPrefixMobiusResponse.probe N))
        (diagonalObservation (HistoryPrefixMobiusResponse.support N)) -
      restored N (alpha + (t : ℝ)) L f
        (diagonalObservation (HistoryPrefixMobiusResponse.probe N))
        (diagonalObservation (HistoryPrefixMobiusResponse.support N)) =
      partition N alpha L f *
        (tiltedMean N alpha L f (HistoryPrefixMobiusResponse.probe N) *
          (1 - tiltedMean N alpha L f (HistoryPrefixMobiusResponse.support N))) -
      partition N (alpha + (t : ℝ)) L f *
        (tiltedMean N (alpha + (t : ℝ)) L f (HistoryPrefixMobiusResponse.probe N) *
          (1 - tiltedMean N (alpha + (t : ℝ)) L f (HistoryPrefixMobiusResponse.support N))) := by
  simp only [restored, form_hessian, HistoryPrefixNonlinearResponse.probe_support_curvature]

/-- Arbitrarily many successive resolution increments retain every
kernel-loss and re-centering term, with no repeated absolute-value budget. -/
theorem cumulative_ledger (N : ℕ) (alpha L : ℝ) (f : Index N → ℝ)
    (K : Hermitian (Index N)) (t : ℕ → ℝ≥0) (R : ℕ) :
    restored N alpha L f K K =
      restored N (alpha + ∑ r ∈ Finset.range R, (t r : ℝ)) L f K K +
        ∑ r ∈ Finset.range R,
          (kernelLoss N (alpha + ∑ k ∈ Finset.range r, (t k : ℝ)) L (t r) f K +
            meanLoss N (alpha + ∑ k ∈ Finset.range r, (t k : ℝ)) L (t r) f K) := by
  induction R with
  | zero => simp
  | succ R ih =>
    have hs := complete_square_ledger N (alpha + ∑ k ∈ Finset.range R, (t k : ℝ)) L (t R) f K
    simp only [Finset.sum_range_succ] at ⊢
    simp only [add_assoc] at hs ⊢
    linarith

structure Conclusions : Prop where
  actual_observed_direction : ∀ (N : ℕ) (alpha L t : ℝ) (f : Index N → ℝ) (i : Index N),
    tiltedLog N (alpha + t) L f i = tiltedLog N alpha L f i - t * rootEnergy N L i
  finite_observed_ledger : ∀ (N : ℕ) (alpha L : ℝ) (t : ℝ≥0)
      (f : Index N → ℝ) (K : Hermitian (Index N)),
    restored N alpha L f K K = restored N (alpha + (t : ℝ)) L f K K +
      kernelLoss N alpha L t f K + meanLoss N alpha L t f K
  observed_contraction : ∀ (N : ℕ) (alpha L : ℝ) (t : ℝ≥0)
      (f : Index N → ℝ) (K : Hermitian (Index N)),
    restored N (alpha + (t : ℝ)) L f K K ≤
      Real.exp (-(t : ℝ) / L ^ 2) * restored N alpha L f K K
  reoptimized_contraction : ∀ (N : ℕ) (alpha L : ℝ) (t : ℝ≥0)
      (f : Index N → ℝ) (K J : Hermitian (Index N)),
    restored N (alpha + (t : ℝ)) L f
        (residual N (alpha + (t : ℝ)) L f K J)
        (residual N (alpha + (t : ℝ)) L f K J) ≤
      Real.exp (-(t : ℝ) / L ^ 2) *
        restored N alpha L f (residual N alpha L f K J) (residual N alpha L f K J)

theorem generated : Conclusions where
  actual_observed_direction := tiltedLog_shift
  finite_observed_ledger := complete_square_ledger
  observed_contraction := complete_response_contraction
  reoptimized_contraction := reduced_response_contraction

end GeneratedFoundations.Analysis.HistoryPrefixObservedResolution

module

public import GeneratedFoundations.Analysis.HistoryPrefixBirthResponse
public import GeneratedFoundations.Analysis.HistoryPrefixResolutionResponse

/-!
# Compatible birth and resolution ledgers in the actual prefix

Natural-prefix birth and Gaussian resolution change different parts of the
same reference state. Their common ledger retains the actual new-root mass,
the old conditional mean, the complete matrix response and the resolution
loss. Neither update is replaced by an independently specified driving term.

The finite cumulative theorem allows resolution after every actual birth.
It follows from exact identities before any estimate of the accumulated
birth contribution. The root observations are read on the full positive
history--phase state; arbitrary matrix observations retain cross-birth entries.
-/

@[expose] public section
noncomputable section
open scoped BigOperators NNReal

namespace GeneratedFoundations.Analysis.HistoryPrefixBirthResolution

open Arithmetic Arithmetic.CompleteHistory
open Operations Operations.PreparedTraceForm
open HistoryPrefixGibbsResponse
open HistoryPrefixBirthResponse (rootObservation rootMean birthFraction birthBlock)
open HistoryPrefixResolutionResponse (restored responseLoss matrixMean)

/-- The original capacity-restored response of the root observation. -/
def rootResponse (N : ℕ) (alpha L : ℝ) (f : ℕ → ℝ) : ℝ :=
  restored N alpha L (diagonalObservation (rootObservation N f))
    (diagonalObservation (rootObservation N f))

/-- The actual birth fluctuation, including the persistent old mean. -/
def birthContribution (N : ℕ) (alpha L : ℝ) (f : ℕ → ℝ) : ℝ :=
  gaussianRootMass alpha L (N + 2) * (1 - birthFraction N alpha L) *
    (f (N + 2) - rootMean N alpha L f) ^ 2

/-- Both terms of the complete resolution loss are evaluated in the same
actual source, including the new reference mean. -/
def resolutionLoss (N : ℕ) (alpha L : ℝ) (t : ℝ≥0) (f : ℕ → ℝ) : ℝ :=
  responseLoss N alpha L t (diagonalObservation (rootObservation N f)) +
    GibbsTraceForm.Z (logIntensity N (alpha + (t : ℝ)) L) *
      (matrixMean N (alpha + (t : ℝ)) L (diagonalObservation (rootObservation N f)) -
        matrixMean N alpha L (diagonalObservation (rootObservation N f))) ^ 2

theorem birthContribution_nonneg (N : ℕ) (alpha L : ℝ) (f : ℕ → ℝ) :
    0 ≤ birthContribution N alpha L f :=
  mul_nonneg (mul_nonneg (gaussianRootMass_pos _ _ _).le
    (sub_pos.mpr (HistoryPrefixBirthResponse.birthFraction_lt_one N alpha L)).le)
    (sq_nonneg _)

theorem resolutionLoss_nonneg (N : ℕ) (alpha L : ℝ) (t : ℝ≥0) (f : ℕ → ℝ) :
    0 ≤ resolutionLoss N alpha L t f :=
  add_nonneg (HistoryPrefixResolutionResponse.responseLoss_nonneg _ _ _ _ _)
    (mul_nonneg (GibbsTraceForm.Z_pos _).le (sq_nonneg _))

theorem actual_birth_ledger (N : ℕ) (alpha L : ℝ) (f : ℕ → ℝ) :
    rootResponse (N + 1) alpha L f = rootResponse N alpha L f +
      birthContribution N alpha L f := by
  simpa only [rootResponse, restored, HistoryPrefixResponseReduction.form_hessian,
    birthContribution] using HistoryPrefixBirthResponse.restored_root_hessian_succ N alpha L f

theorem actual_resolution_ledger (N : ℕ) (alpha L : ℝ) (t : ℝ≥0) (f : ℕ → ℝ) :
    rootResponse N alpha L f = rootResponse N (alpha + (t : ℝ)) L f +
      resolutionLoss N alpha L t f := by
  simpa only [rootResponse, resolutionLoss, add_assoc] using
    HistoryPrefixResolutionResponse.complete_square_ledger N alpha L t
      (diagonalObservation (rootObservation N f))

/-- Birth first, then resolution, with its full actual response loss. -/
theorem joint_step_ledger (N : ℕ) (alpha L : ℝ) (t : ℝ≥0) (f : ℕ → ℝ) :
    rootResponse (N + 1) (alpha + (t : ℝ)) L f +
      resolutionLoss (N + 1) alpha L t f =
        rootResponse N alpha L f + birthContribution N alpha L f := by
  rw [← actual_resolution_ledger, actual_birth_ledger]

/-- The two update orders have the same endpoint. The change of the birth
fluctuation is compensated by the actual change of resolution loss. -/
theorem commuting_rectangle (N : ℕ) (alpha L : ℝ) (t : ℝ≥0) (f : ℕ → ℝ) :
    birthContribution N (alpha + (t : ℝ)) L f + resolutionLoss (N + 1) alpha L t f =
      birthContribution N alpha L f + resolutionLoss N alpha L t f := by
  have h := joint_step_ledger N alpha L t f
  rw [actual_birth_ledger] at h
  have h0 := actual_resolution_ledger N alpha L t f
  linarith

/-- The response bound applies to the whole birth, including its actual
between-birth fluctuation, rather than only to the old state. -/
theorem joint_step_contraction (N : ℕ) (alpha L : ℝ) (t : ℝ≥0) (f : ℕ → ℝ) :
    rootResponse (N + 1) (alpha + (t : ℝ)) L f ≤
      Real.exp (-(t : ℝ) / L ^ 2) *
        (rootResponse N alpha L f + birthContribution N alpha L f) := by
  rw [← actual_birth_ledger]
  exact HistoryPrefixResolutionResponse.complete_response_contraction (N + 1) alpha L t _

/-- All cross-birth matrix entries are retained in this common ledger.
Their original logarithmic-mean weights occur in the `off` response. -/
theorem complete_matrix_joint_ledger (N : ℕ) (alpha L : ℝ) (t : ℝ≥0)
    (K : Hermitian (Index (N + 1))) :
    restored (N + 1) alpha L (GibbsBlockResponse.block (birthBlock N) K)
        (GibbsBlockResponse.block (birthBlock N) K) +
      restored (N + 1) alpha L (GibbsBlockResponse.off (birthBlock N) K)
        (GibbsBlockResponse.off (birthBlock N) K) =
      restored (N + 1) (alpha + (t : ℝ)) L K K + responseLoss (N + 1) alpha L t K +
        GibbsTraceForm.Z (logIntensity (N + 1) (alpha + (t : ℝ)) L) *
          (matrixMean (N + 1) (alpha + (t : ℝ)) L K -
            matrixMean (N + 1) alpha L K) ^ 2 := by
  have hs := HistoryPrefixResolutionResponse.complete_square_ledger (N + 1) alpha L t K
  have hb := GibbsBlockResponse.response_decomposition
    (logIntensity (N + 1) alpha L) (birthBlock N) K
  change HistoryPrefixResponseReduction.form (N + 1) alpha L K K = _ at hb
  simpa only [restored, hb, mul_add] using! hs

/-- The mean of a cross-birth observation is zero at both references, so
its complete ledger has no omitted re-centering cost. -/
theorem cross_birth_resolution_ledger (N : ℕ) (alpha L : ℝ) (t : ℝ≥0)
    (K : Hermitian (Index (N + 1))) :
    restored (N + 1) alpha L (GibbsBlockResponse.off (birthBlock N) K)
        (GibbsBlockResponse.off (birthBlock N) K) =
      restored (N + 1) (alpha + (t : ℝ)) L (GibbsBlockResponse.off (birthBlock N) K)
        (GibbsBlockResponse.off (birthBlock N) K) +
      responseLoss (N + 1) alpha L t (GibbsBlockResponse.off (birthBlock N) K) := by
  simpa only [matrixMean, GibbsBlockResponse.mean_off, sub_self, zero_pow (by norm_num : 2 ≠ 0),
    mul_zero, add_zero] using
      HistoryPrefixResolutionResponse.complete_square_ledger (N + 1) alpha L t
        (GibbsBlockResponse.off (birthBlock N) K)

/-- The cross-birth response is the original weighted sum of every ordered
matrix entry between the old and the new full history--phase fibres. -/
theorem cross_birth_response_exact (N : ℕ) (alpha L : ℝ)
    (K : Hermitian (Index (N + 1))) :
    restored (N + 1) alpha L (GibbsBlockResponse.off (birthBlock N) K)
        (GibbsBlockResponse.off (birthBlock N) K) =
      ∑ i, ∑ j, if birthBlock N i = birthBlock N j then 0 else
        GibbsExponentialDifferentiation.expDividedDifference
          (logIntensity (N + 1) alpha L i) (logIntensity (N + 1) alpha L j) *
            Complex.normSq ((K : Mat (Index (N + 1))) i j) := by
  unfold restored
  change GibbsTraceForm.Z (logIntensity (N + 1) alpha L) *
    GibbsTraceForm.hermitianForm (logIntensity (N + 1) alpha L)
      (GibbsBlockResponse.off (birthBlock N) K) (GibbsBlockResponse.off (birthBlock N) K) = _
  rw [GibbsBlockResponse.off_response, mul_div_cancel₀ _ (GibbsTraceForm.Z_ne_zero _)]

/-- The Gaussian coordinate is accumulated from the actual chosen
observation increments, without a freely assigned loss or forcing. -/
def coordinate (alpha : ℝ) (t : ℕ → ℝ≥0) (N : ℕ) : ℝ :=
  alpha + ∑ r ∈ Finset.range N, (t r : ℝ)

@[simp] theorem coordinate_zero (alpha : ℝ) (t : ℕ → ℝ≥0) : coordinate alpha t 0 = alpha := by
  simp [coordinate]

theorem coordinate_succ (alpha : ℝ) (t : ℕ → ℝ≥0) (N : ℕ) :
    coordinate alpha t (N + 1) = coordinate alpha t N + (t N : ℝ) := by
  simp only [coordinate, Finset.sum_range_succ, add_assoc]

/-- Exact finite cumulative balance for the actual successive prefixes.
Both sums retain their computed birth and resolution terms. -/
theorem cumulative_ledger (R : ℕ) (alpha L : ℝ) (t : ℕ → ℝ≥0) (f : ℕ → ℝ) :
    rootResponse R (coordinate alpha t R) L f +
        ∑ r ∈ Finset.range R, resolutionLoss (r + 1) (coordinate alpha t r) L (t r) f =
      rootResponse 0 alpha L f +
        ∑ r ∈ Finset.range R, birthContribution r (coordinate alpha t r) L f := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [coordinate_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    have hs := joint_step_ledger R (coordinate alpha t R) L (t R) f
    linarith

/-- Positive losses can be retained or dropped only after the complete
finite-source balance has been assembled. -/
theorem cumulative_budget (R : ℕ) (alpha L : ℝ) (t : ℕ → ℝ≥0) (f : ℕ → ℝ) :
    rootResponse R (coordinate alpha t R) L f ≤ rootResponse 0 alpha L f +
      ∑ r ∈ Finset.range R, birthContribution r (coordinate alpha t r) L f := by
  have h := cumulative_ledger R alpha L t f
  have hp : 0 ≤ ∑ r ∈ Finset.range R,
      resolutionLoss (r + 1) (coordinate alpha t r) L (t r) f :=
    Finset.sum_nonneg (fun r _ => resolutionLoss_nonneg _ _ _ _ _)
  linarith

structure Conclusions : Prop where
  actual_joint_ledger : ∀ (N : ℕ) (alpha L : ℝ) (t : ℝ≥0) (f : ℕ → ℝ),
    rootResponse (N + 1) (alpha + (t : ℝ)) L f +
      resolutionLoss (N + 1) alpha L t f =
        rootResponse N alpha L f + birthContribution N alpha L f
  order_compatibility : ∀ (N : ℕ) (alpha L : ℝ) (t : ℝ≥0) (f : ℕ → ℝ),
    birthContribution N (alpha + (t : ℝ)) L f + resolutionLoss (N + 1) alpha L t f =
      birthContribution N alpha L f + resolutionLoss N alpha L t f
  finite_cumulative_balance : ∀ (R : ℕ) (alpha L : ℝ) (t : ℕ → ℝ≥0) (f : ℕ → ℝ),
    rootResponse R (coordinate alpha t R) L f +
        ∑ r ∈ Finset.range R, resolutionLoss (r + 1) (coordinate alpha t r) L (t r) f =
      rootResponse 0 alpha L f +
        ∑ r ∈ Finset.range R, birthContribution r (coordinate alpha t r) L f

theorem generated : Conclusions where
  actual_joint_ledger := joint_step_ledger
  order_compatibility := commuting_rectangle
  finite_cumulative_balance := cumulative_ledger

end GeneratedFoundations.Analysis.HistoryPrefixBirthResolution

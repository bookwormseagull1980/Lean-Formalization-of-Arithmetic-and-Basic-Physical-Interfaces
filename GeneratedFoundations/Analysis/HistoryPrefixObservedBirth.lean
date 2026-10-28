module

public import GeneratedFoundations.Analysis.HistoryPrefixObservedResolution
public import GeneratedFoundations.Analysis.HistoryPrefixBirthResolution

/-!
# Actual birth and resolution at a finite root observation

The same root observation is restricted to each successive natural prefix.
Its exact likelihood multiplies the existing Gaussian mass of a newborn
root; the full conditional history--phase fibre is preserved. Partition,
mixed covariance, birth fluctuation and resolution loss are computed in
that single state before their cumulative balance is formed.

Full Hermitian observations on the extended carrier also retain every
cross-birth matrix entry. Their response uses the complete observed
logarithmic-mean kernel, rather than only its diagonal covariance.
-/

@[expose] public section
noncomputable section
open scoped BigOperators NNReal

namespace GeneratedFoundations.Analysis.HistoryPrefixObservedBirth

open Arithmetic Arithmetic.CompleteHistory
open Operations Operations.PreparedTraceForm
open HistoryPrefixGibbsResponse
open HistoryPrefixBirthResponse (rootObservation birthBlock)
open HistoryPrefixNonlinearResponse (tiltedLog tiltedMean)
open HistoryPrefixObservedResolution (form partition restored kernelLoss meanLoss)

def rootPartition (N : ℕ) (alpha L : ℝ) (f : ℕ → ℝ) : ℝ :=
  partition N alpha L (rootObservation N f)

def rootMean (N : ℕ) (alpha L : ℝ) (f g : ℕ → ℝ) : ℝ :=
  tiltedMean N alpha L (rootObservation N f) (rootObservation N g)

def birthMass (N : ℕ) (alpha L : ℝ) (f : ℕ → ℝ) : ℝ :=
  gaussianRootMass alpha L (N + 2) * Real.exp (f (N + 2))

def birthFraction (N : ℕ) (alpha L : ℝ) (f : ℕ → ℝ) : ℝ :=
  birthMass N alpha L f / rootPartition (N + 1) alpha L f

theorem birthMass_pos (N : ℕ) (alpha L : ℝ) (f : ℕ → ℝ) :
    0 < birthMass N alpha L f := mul_pos (gaussianRootMass_pos _ _ _) (Real.exp_pos _)

theorem rootPartition_pos (N : ℕ) (alpha L : ℝ) (f : ℕ → ℝ) :
    0 < rootPartition N alpha L f := GibbsTraceForm.Z_pos _

theorem rootPartition_sum (N : ℕ) (alpha L : ℝ) (f : ℕ → ℝ) :
    rootPartition N alpha L f =
      ∑ b : Fin (N + 1), gaussianRootMass alpha L (b.val + 1) * Real.exp (f (b.val + 1)) := by
  rw [rootPartition, HistoryPrefixObservedResolution.partition_likelihood]
  change (∑ i : (Σ b : Fin (N + 1), HistoryPhaseBundle.Fiber b.val),
    HistoryPhaseResponse.intensity i.1.val alpha L i.2 * Real.exp (f (i.1.val + 1))) = _
  rw [Fintype.sum_sigma]
  simp only [HistoryPhaseResponse.intensity, ← Finset.sum_mul, ← Finset.mul_sum,
    HistoryPhaseBundle.probability_total, mul_one]

theorem partition_succ (N : ℕ) (alpha L : ℝ) (f : ℕ → ℝ) :
    rootPartition (N + 1) alpha L f = rootPartition N alpha L f + birthMass N alpha L f := by
  rw [rootPartition_sum, rootPartition_sum, Fin.sum_univ_castSucc]
  rfl

theorem birthFraction_pos (N : ℕ) (alpha L : ℝ) (f : ℕ → ℝ) :
    0 < birthFraction N alpha L f := div_pos (birthMass_pos _ _ _ _) (rootPartition_pos _ _ _ _)

theorem birthFraction_lt_one (N : ℕ) (alpha L : ℝ) (f : ℕ → ℝ) :
    birthFraction N alpha L f < 1 := by
  unfold birthFraction
  apply (div_lt_one (rootPartition_pos _ _ _ _)).mpr
  rw [partition_succ]
  linarith [rootPartition_pos N alpha L f]

theorem weighted_rootMean (N : ℕ) (alpha L : ℝ) (f g : ℕ → ℝ) :
    rootPartition N alpha L f * rootMean N alpha L f g =
      ∑ b : Fin (N + 1), gaussianRootMass alpha L (b.val + 1) *
        Real.exp (f (b.val + 1)) * g (b.val + 1) := by
  have hm : rootMean N alpha L f g =
      (∑ b : Fin (N + 1), gaussianRootMass alpha L (b.val + 1) *
        Real.exp (f (b.val + 1)) * g (b.val + 1)) / rootPartition N alpha L f := by
    have hp (b : Fin (N + 1)) :
        (∑ x : HistoryPhaseBundle.Fiber b.val,
          HistoryPrefixNonlinearResponse.tiltedProbability N alpha L
            (rootObservation N f) ⟨b, x⟩) =
          gaussianRootMass alpha L (b.val + 1) * Real.exp (f (b.val + 1)) /
            rootPartition N alpha L f := by
      simpa only [rootObservation, rootPartition, partition] using!
        HistoryPrefixNonlinearResponse.tiltedProbability_root_marginal N alpha L
          (fun b => f (b.val + 1)) b
    unfold rootMean tiltedMean
    change (∑ i : (Σ b : Fin (N + 1), HistoryPhaseBundle.Fiber b.val),
      HistoryPrefixNonlinearResponse.tiltedProbability N alpha L
        (rootObservation N f) i * g (i.1.val + 1)) = _
    rw [Fintype.sum_sigma]
    simp only [← Finset.sum_mul, hp, div_mul_eq_mul_div, Finset.sum_div]
  rw [hm, mul_div_cancel₀ _ (rootPartition_pos N alpha L f).ne']

theorem weighted_rootMean_succ (N : ℕ) (alpha L : ℝ) (f g : ℕ → ℝ) :
    rootPartition (N + 1) alpha L f * rootMean (N + 1) alpha L f g =
      rootPartition N alpha L f * rootMean N alpha L f g + birthMass N alpha L f * g (N + 2) := by
  rw [weighted_rootMean, weighted_rootMean, Fin.sum_univ_castSucc]
  rfl

theorem rootMean_succ (N : ℕ) (alpha L : ℝ) (f g : ℕ → ℝ) :
    rootMean (N + 1) alpha L f g =
      (1 - birthFraction N alpha L f) * rootMean N alpha L f g +
        birthFraction N alpha L f * g (N + 2) := by
  apply mul_left_cancel₀ (rootPartition_pos (N + 1) alpha L f).ne'
  rw [weighted_rootMean_succ]
  unfold birthFraction
  rw [partition_succ]
  have hz := (add_pos (rootPartition_pos N alpha L f) (birthMass_pos N alpha L f)).ne'
  field_simp [hz]
  ring

theorem root_joint_response (N : ℕ) (alpha L : ℝ) (f g h : ℕ → ℝ) :
    form N alpha L (rootObservation N f)
      (diagonalObservation (rootObservation N g)) (diagonalObservation (rootObservation N h)) =
        rootMean N alpha L f (fun n => g n * h n) -
          rootMean N alpha L f g * rootMean N alpha L f h := by
  rw [HistoryPrefixObservedResolution.form_hessian,
    HistoryPrefixNonlinearResponse.hessian_covariance]
  rfl

/-- Both mixed directions use the same actual newborn mass and old mean. -/
theorem root_joint_response_succ (N : ℕ) (alpha L : ℝ) (f g h : ℕ → ℝ) :
    form (N + 1) alpha L (rootObservation (N + 1) f)
      (diagonalObservation (rootObservation (N + 1) g))
      (diagonalObservation (rootObservation (N + 1) h)) =
      (1 - birthFraction N alpha L f) * form N alpha L (rootObservation N f)
        (diagonalObservation (rootObservation N g)) (diagonalObservation (rootObservation N h)) +
      birthFraction N alpha L f * (1 - birthFraction N alpha L f) *
        (g (N + 2) - rootMean N alpha L f g) * (h (N + 2) - rootMean N alpha L f h) := by
  rw [root_joint_response, root_joint_response,
    rootMean_succ N alpha L f (fun n => g n * h n),
    rootMean_succ N alpha L f g, rootMean_succ N alpha L f h]
  ring

theorem restored_old_capacity (N : ℕ) (alpha L : ℝ) (f : ℕ → ℝ) :
    rootPartition (N + 1) alpha L f * (1 - birthFraction N alpha L f) =
      rootPartition N alpha L f := by
  unfold birthFraction
  rw [mul_sub, mul_one, mul_div_cancel₀ _ (rootPartition_pos _ _ _ _).ne', partition_succ]
  ring

def rootResponse (N : ℕ) (alpha L : ℝ) (f g : ℕ → ℝ) : ℝ :=
  restored N alpha L (rootObservation N f)
    (diagonalObservation (rootObservation N g)) (diagonalObservation (rootObservation N g))

def birthContribution (N : ℕ) (alpha L : ℝ) (f g : ℕ → ℝ) : ℝ :=
  birthMass N alpha L f * (1 - birthFraction N alpha L f) *
    (g (N + 2) - rootMean N alpha L f g) ^ 2

def resolutionLoss (N : ℕ) (alpha L : ℝ) (t : ℝ≥0) (f g : ℕ → ℝ) : ℝ :=
  kernelLoss N alpha L t (rootObservation N f) (diagonalObservation (rootObservation N g)) +
    meanLoss N alpha L t (rootObservation N f) (diagonalObservation (rootObservation N g))

theorem birthContribution_nonneg (N : ℕ) (alpha L : ℝ) (f g : ℕ → ℝ) :
    0 ≤ birthContribution N alpha L f g :=
  mul_nonneg (mul_nonneg (birthMass_pos _ _ _ _).le
    (sub_pos.mpr (birthFraction_lt_one _ _ _ _)).le) (sq_nonneg _)

theorem resolutionLoss_nonneg (N : ℕ) (alpha L : ℝ) (t : ℝ≥0) (f g : ℕ → ℝ) :
    0 ≤ resolutionLoss N alpha L t f g :=
  add_nonneg (HistoryPrefixObservedResolution.kernelLoss_nonneg _ _ _ _ _ _)
    (HistoryPrefixObservedResolution.meanLoss_nonneg _ _ _ _ _ _)

theorem actual_birth_ledger (N : ℕ) (alpha L : ℝ) (f g : ℕ → ℝ) :
    rootResponse (N + 1) alpha L f g = rootResponse N alpha L f g +
      birthContribution N alpha L f g := by
  unfold rootResponse restored
  rw [root_joint_response_succ, mul_add]
  change rootPartition (N + 1) alpha L f *
      ((1 - birthFraction N alpha L f) * _) + _ = _
  rw [← mul_assoc (rootPartition (N + 1) alpha L f) (1 - birthFraction N alpha L f),
    restored_old_capacity]
  congr 1
  change rootPartition (N + 1) alpha L f *
      (birthFraction N alpha L f * (1 - birthFraction N alpha L f) *
        (g (N + 2) - rootMean N alpha L f g) * (g (N + 2) - rootMean N alpha L f g)) = _
  unfold birthContribution birthFraction
  have hz := (rootPartition_pos (N + 1) alpha L f).ne'
  field_simp [hz]

theorem actual_resolution_ledger (N : ℕ) (alpha L : ℝ) (t : ℝ≥0) (f g : ℕ → ℝ) :
    rootResponse N alpha L f g = rootResponse N (alpha + (t : ℝ)) L f g +
      resolutionLoss N alpha L t f g := by
  simpa only [rootResponse, resolutionLoss, add_assoc] using
    HistoryPrefixObservedResolution.complete_square_ledger N alpha L t
      (rootObservation N f) (diagonalObservation (rootObservation N g))

theorem joint_step_ledger (N : ℕ) (alpha L : ℝ) (t : ℝ≥0) (f g : ℕ → ℝ) :
    rootResponse (N + 1) (alpha + (t : ℝ)) L f g + resolutionLoss (N + 1) alpha L t f g =
      rootResponse N alpha L f g + birthContribution N alpha L f g := by
  rw [← actual_resolution_ledger, actual_birth_ledger]

theorem commuting_rectangle (N : ℕ) (alpha L : ℝ) (t : ℝ≥0) (f g : ℕ → ℝ) :
    birthContribution N (alpha + (t : ℝ)) L f g + resolutionLoss (N + 1) alpha L t f g =
      birthContribution N alpha L f g + resolutionLoss N alpha L t f g := by
  have h := joint_step_ledger N alpha L t f g
  rw [actual_birth_ledger] at h
  have h0 := actual_resolution_ledger N alpha L t f g
  linarith

theorem joint_step_contraction (N : ℕ) (alpha L : ℝ) (t : ℝ≥0) (f g : ℕ → ℝ) :
    rootResponse (N + 1) (alpha + (t : ℝ)) L f g ≤
      Real.exp (-(t : ℝ) / L ^ 2) *
        (rootResponse N alpha L f g + birthContribution N alpha L f g) := by
  rw [← actual_birth_ledger]
  exact HistoryPrefixObservedResolution.complete_response_contraction (N + 1) alpha L t _ _

/-- The complete observed matrix response includes both directions of every
old/new fibre pair with its original logarithmic-mean weight. -/
theorem full_birth_response (N : ℕ) (alpha L : ℝ) (f : Index (N + 1) → ℝ)
    (K : Hermitian (Index (N + 1))) :
    form (N + 1) alpha L f K K =
      form (N + 1) alpha L f (GibbsBlockResponse.block (birthBlock N) K)
        (GibbsBlockResponse.block (birthBlock N) K) +
      (∑ i, ∑ j, if birthBlock N i = birthBlock N j then 0 else
        GibbsExponentialDifferentiation.expDividedDifference
          (tiltedLog (N + 1) alpha L f i) (tiltedLog (N + 1) alpha L f j) *
            Complex.normSq ((K : Mat (Index (N + 1))) i j)) / partition (N + 1) alpha L f := by
  exact (GibbsBlockResponse.response_decomposition
    (tiltedLog (N + 1) alpha L f) (birthBlock N) K).trans
      (congrArg (fun r => form (N + 1) alpha L f
        (GibbsBlockResponse.block (birthBlock N) K) (GibbsBlockResponse.block (birthBlock N) K) + r)
          (GibbsBlockResponse.off_response (tiltedLog (N + 1) alpha L f) (birthBlock N) K))

theorem complete_matrix_joint_ledger (N : ℕ) (alpha L : ℝ) (t : ℝ≥0)
    (f : Index (N + 1) → ℝ) (K : Hermitian (Index (N + 1))) :
    restored (N + 1) alpha L f (GibbsBlockResponse.block (birthBlock N) K)
        (GibbsBlockResponse.block (birthBlock N) K) +
      restored (N + 1) alpha L f (GibbsBlockResponse.off (birthBlock N) K)
        (GibbsBlockResponse.off (birthBlock N) K) =
      restored (N + 1) (alpha + (t : ℝ)) L f K K +
        kernelLoss (N + 1) alpha L t f K + meanLoss (N + 1) alpha L t f K := by
  have hs := HistoryPrefixObservedResolution.complete_square_ledger (N + 1) alpha L t f K
  have hb := GibbsBlockResponse.response_decomposition
    (tiltedLog (N + 1) alpha L f) (birthBlock N) K
  change form (N + 1) alpha L f K K = _ at hb
  simpa only [restored, hb, mul_add] using! hs

theorem cross_birth_resolution_ledger (N : ℕ) (alpha L : ℝ) (t : ℝ≥0)
    (f : Index (N + 1) → ℝ) (K : Hermitian (Index (N + 1))) :
    restored (N + 1) alpha L f (GibbsBlockResponse.off (birthBlock N) K)
        (GibbsBlockResponse.off (birthBlock N) K) =
      restored (N + 1) (alpha + (t : ℝ)) L f (GibbsBlockResponse.off (birthBlock N) K)
        (GibbsBlockResponse.off (birthBlock N) K) +
      kernelLoss (N + 1) alpha L t f (GibbsBlockResponse.off (birthBlock N) K) := by
  simpa only [meanLoss, HistoryPrefixObservedResolution.matrixMean,
    GibbsBlockResponse.mean_off, sub_self, zero_pow (by norm_num : 2 ≠ 0), mul_zero, add_zero] using
      HistoryPrefixObservedResolution.complete_square_ledger (N + 1) alpha L t f
        (GibbsBlockResponse.off (birthBlock N) K)

open HistoryPrefixBirthResolution (coordinate coordinate_succ)

theorem cumulative_ledger (R : ℕ) (alpha L : ℝ) (t : ℕ → ℝ≥0) (f g : ℕ → ℝ) :
    rootResponse R (coordinate alpha t R) L f g +
        ∑ r ∈ Finset.range R, resolutionLoss (r + 1) (coordinate alpha t r) L (t r) f g =
      rootResponse 0 alpha L f g +
        ∑ r ∈ Finset.range R, birthContribution r (coordinate alpha t r) L f g := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [coordinate_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    have hs := joint_step_ledger R (coordinate alpha t R) L (t R) f g
    linarith

structure Conclusions : Prop where
  likelihood_birth : ∀ (N : ℕ) (alpha L : ℝ) (f : ℕ → ℝ),
    rootPartition (N + 1) alpha L f = rootPartition N alpha L f + birthMass N alpha L f
  mixed_birth_response : ∀ (N : ℕ) (alpha L : ℝ) (f g h : ℕ → ℝ),
    form (N + 1) alpha L (rootObservation (N + 1) f)
      (diagonalObservation (rootObservation (N + 1) g))
      (diagonalObservation (rootObservation (N + 1) h)) =
      (1 - birthFraction N alpha L f) * form N alpha L (rootObservation N f)
        (diagonalObservation (rootObservation N g)) (diagonalObservation (rootObservation N h)) +
      birthFraction N alpha L f * (1 - birthFraction N alpha L f) *
        (g (N + 2) - rootMean N alpha L f g) * (h (N + 2) - rootMean N alpha L f h)
  observed_joint_balance : ∀ (N : ℕ) (alpha L : ℝ) (t : ℝ≥0) (f g : ℕ → ℝ),
    rootResponse (N + 1) (alpha + (t : ℝ)) L f g + resolutionLoss (N + 1) alpha L t f g =
      rootResponse N alpha L f g + birthContribution N alpha L f g
  finite_observed_history : ∀ (R : ℕ) (alpha L : ℝ) (t : ℕ → ℝ≥0) (f g : ℕ → ℝ),
    rootResponse R (coordinate alpha t R) L f g +
        ∑ r ∈ Finset.range R, resolutionLoss (r + 1) (coordinate alpha t r) L (t r) f g =
      rootResponse 0 alpha L f g +
        ∑ r ∈ Finset.range R, birthContribution r (coordinate alpha t r) L f g

theorem generated : Conclusions where
  likelihood_birth := partition_succ
  mixed_birth_response := root_joint_response_succ
  observed_joint_balance := joint_step_ledger
  finite_observed_history := cumulative_ledger

end GeneratedFoundations.Analysis.HistoryPrefixObservedBirth

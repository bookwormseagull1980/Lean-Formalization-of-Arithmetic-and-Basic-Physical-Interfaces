module

public import GeneratedFoundations.Analysis.HistoryPrefixResolution
public import GeneratedFoundations.Analysis.HistoryPrefixMobiusResponse
public import GeneratedFoundations.Operations.GibbsResolutionLedger

/-!
# Full connected response ledger for the native Gaussian resolution

The actual log intensity moves in the direction of the existing root-square
energy. The complete logarithmic-mean kernel decreases accordingly. This
gives an exact response-loss ledger and an unnormalized contraction for every
Hermitian matrix on the original root-history-phase carrier. The observation
is held fixed; the partition and its re-centering cost remain explicit.

The resolution increment changes alpha at fixed L and fixed prefix. It is
not a bound uniform in a varying observation scale or a prime-birth update.
-/

@[expose] public section
noncomputable section
open scoped BigOperators NNReal Matrix.Norms.Operator

namespace GeneratedFoundations.Analysis.HistoryPrefixResolutionResponse

open Arithmetic Arithmetic.CompleteHistory
open Operations Operations.PreparedTraceForm
open GibbsExponentialDifferentiation (expDividedDifference)
open HistoryPrefixGibbsResponse
open HistoryPrefixResponseReduction (form)

def rootEnergy (N : ℕ) (L : ℝ) (i : Index N) : ℝ :=
  ((i.1.val + 1 : ℕ) : ℝ) ^ 2 / L ^ 2

theorem rootEnergy_nonneg (N : ℕ) (L : ℝ) (i : Index N) :
    0 ≤ rootEnergy N L i := div_nonneg (sq_nonneg _) (sq_nonneg _)

theorem rootEnergy_lower (N : ℕ) (L : ℝ) (i : Index N) :
    1 / L ^ 2 ≤ rootEnergy N L i := by
  have hi : (1 : ℝ) ≤ ((i.1.val + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  exact div_le_div_of_nonneg_right (by nlinarith) (sq_nonneg L)

/-- The scale direction comes from the actual log of the existing positive
source; the conditional history-phase law cancels without being changed. -/
theorem logIntensity_shift (N : ℕ) (alpha L t : ℝ) (i : Index N) :
    logIntensity N (alpha + t) L i = logIntensity N alpha L i - t * rootEnergy N L i := by
  simp only [logIntensity, intensity, HistoryPhaseResponse.intensity, gaussianRootMass,
    Real.log_mul (Real.exp_ne_zero _) (HistoryPhaseBundle.probability_pos i.2).ne', Real.log_exp]
  unfold rootEnergy
  push_cast
  ring

theorem logIntensity_nonincreasing (N : ℕ) (alpha L : ℝ) (t : ℝ≥0) (i : Index N) :
    logIntensity N (alpha + (t : ℝ)) L i ≤ logIntensity N alpha L i := by
  rw [logIntensity_shift]
  exact sub_le_self _ (mul_nonneg t.property (rootEnergy_nonneg N L i))

/-- The finite-prefix constant is independent of its size. Its scale
dependence is the actual native unit-root Gaussian multiplier. -/
theorem complete_kernel_contraction (N : ℕ) (alpha L : ℝ) (t : ℝ≥0) (i j : Index N) :
    expDividedDifference (logIntensity N (alpha + (t : ℝ)) L i)
        (logIntensity N (alpha + (t : ℝ)) L j) ≤
      Real.exp (-(t : ℝ) / L ^ 2) *
        expDividedDifference (logIntensity N alpha L i) (logIntensity N alpha L j) := by
  have h (k : Index N) : logIntensity N (alpha + (t : ℝ)) L k ≤
      logIntensity N alpha L k - (t : ℝ) / L ^ 2 := by
    rw [logIntensity_shift]
    have he := mul_le_mul_of_nonneg_left (rootEnergy_lower N L k) t.property
    simpa only [one_div, div_eq_mul_inv, one_mul] using!
      sub_le_sub_left he (logIntensity N alpha L k)
  simpa only [neg_div] using GibbsResolutionLedger.divided_difference_le_shift (h i) (h j)

def restored (N : ℕ) (alpha L : ℝ) (K J : Hermitian (Index N)) : ℝ :=
  GibbsTraceForm.Z (logIntensity N alpha L) * form N alpha L K J

def matrixMean (N : ℕ) (alpha L : ℝ) (K : Hermitian (Index N)) : ℝ :=
  GibbsTraceForm.mean (logIntensity N alpha L) (K : Mat (Index N))

def responseLoss (N : ℕ) (alpha L : ℝ) (t : ℝ≥0) (K : Hermitian (Index N)) : ℝ :=
  GibbsResolutionLedger.kernelLoss (logIntensity N alpha L)
    (logIntensity N (alpha + (t : ℝ)) L) (K : Mat (Index N))

theorem restored_hessian (N : ℕ) (alpha L : ℝ) (K J : Hermitian (Index N)) :
    restored N alpha L K J = GibbsTraceForm.Z (logIntensity N alpha L) *
      fderiv ℝ (fderiv ℝ (response N alpha L)) 0 K J := by
  rw [restored, HistoryPrefixResponseReduction.form_hessian]

/-- The mixed version keeps all cross-observable contributions. -/
theorem complete_mixed_ledger (N : ℕ) (alpha L : ℝ) (t : ℝ≥0)
    (K J : Hermitian (Index N)) :
    restored N alpha L K J - restored N (alpha + (t : ℝ)) L K J =
      GibbsTraceForm.responsePairing (logIntensity N alpha L)
          (GibbsTraceForm.centered (logIntensity N alpha L) (K : Mat (Index N)))
          (GibbsTraceForm.centered (logIntensity N alpha L) (J : Mat (Index N))) -
        GibbsTraceForm.responsePairing (logIntensity N (alpha + (t : ℝ)) L)
          (GibbsTraceForm.centered (logIntensity N alpha L) (K : Mat (Index N)))
          (GibbsTraceForm.centered (logIntensity N alpha L) (J : Mat (Index N))) +
        GibbsTraceForm.Z (logIntensity N (alpha + (t : ℝ)) L) *
          (matrixMean N (alpha + (t : ℝ)) L K - matrixMean N alpha L K) *
          (matrixMean N (alpha + (t : ℝ)) L J - matrixMean N alpha L J) :=
  GibbsResolutionLedger.restored_difference _ _ _ _

theorem complete_square_ledger (N : ℕ) (alpha L : ℝ) (t : ℝ≥0) (K : Hermitian (Index N)) :
    restored N alpha L K K = restored N (alpha + (t : ℝ)) L K K +
      responseLoss N alpha L t K +
        GibbsTraceForm.Z (logIntensity N (alpha + (t : ℝ)) L) *
          (matrixMean N (alpha + (t : ℝ)) L K - matrixMean N alpha L K) ^ 2 :=
  GibbsResolutionLedger.restored_square_ledger (hermitian_isHermitian _ K)

theorem responseLoss_nonneg (N : ℕ) (alpha L : ℝ) (t : ℝ≥0) (K : Hermitian (Index N)) :
    0 ≤ responseLoss N alpha L t K :=
  GibbsResolutionLedger.kernelLoss_nonneg (logIntensity_nonincreasing N alpha L t) _

theorem complete_response_contraction (N : ℕ) (alpha L : ℝ) (t : ℝ≥0)
    (K : Hermitian (Index N)) :
    restored N (alpha + (t : ℝ)) L K K ≤
      Real.exp (-(t : ℝ) / L ^ 2) * restored N alpha L K K :=
  GibbsResolutionLedger.restored_contraction (complete_kernel_contraction N alpha L t)
    (hermitian_isHermitian _ K)

/-- The optimal observation reduction is recomputed in the new reference;
its original coefficient is not frozen or silently reused. -/
theorem reduced_response_contraction (N : ℕ) (alpha L : ℝ) (t : ℝ≥0)
    (K J : Hermitian (Index N)) :
    restored N (alpha + (t : ℝ)) L
        (HistoryPrefixResponseReduction.residual (alpha + (t : ℝ)) L K J)
        (HistoryPrefixResponseReduction.residual (alpha + (t : ℝ)) L K J) ≤
      Real.exp (-(t : ℝ) / L ^ 2) * restored N alpha L
        (HistoryPrefixResponseReduction.residual alpha L K J)
        (HistoryPrefixResponseReduction.residual alpha L K J) := by
  let R := HistoryPrefixResponseReduction.residual alpha L K J
  have hm := HistoryPrefixResponseReduction.residual_minimality (alpha + (t : ℝ)) L K J
    (HistoryPrefixResponseReduction.coefficient alpha L K J)
  have hfirst : restored N (alpha + (t : ℝ)) L
      (HistoryPrefixResponseReduction.residual (alpha + (t : ℝ)) L K J)
      (HistoryPrefixResponseReduction.residual (alpha + (t : ℝ)) L K J) ≤
        restored N (alpha + (t : ℝ)) L R R := by
    exact mul_le_mul_of_nonneg_left hm (GibbsTraceForm.Z_pos _).le
  exact hfirst.trans (complete_response_contraction N alpha L t R)

/-- The actual Mobius/support Schur response, with its original positive
capacity restored at each endpoint of the resolution, obeys the same bound. -/
theorem native_transverse_contraction (N : ℕ) (alpha L : ℝ) (t : ℝ≥0) :
    CenterEndpointPotential.finiteSupportCapacity
        (gaussianRootMass (alpha + (t : ℝ)) L) (N + 1) -
      (SignedGaussianEnergy.rootSignedAmplitude (alpha + (t : ℝ)) L (N + 1)) ^ 2 /
        CenterEndpointPotential.finiteSupportCapacity
          (gaussianRootMass (alpha + (t : ℝ)) L) (N + 1) ≤
      Real.exp (-(t : ℝ) / L ^ 2) *
        (CenterEndpointPotential.finiteSupportCapacity (gaussianRootMass alpha L) (N + 1) -
          (SignedGaussianEnergy.rootSignedAmplitude alpha L (N + 1)) ^ 2 /
            CenterEndpointPotential.finiteSupportCapacity (gaussianRootMass alpha L) (N + 1)) := by
  have h := reduced_response_contraction N alpha L t
    (diagonalObservation (HistoryPrefixMobiusResponse.probe N))
    (diagonalObservation (HistoryPrefixMobiusResponse.support N))
  simpa only [restored, HistoryPrefixMobiusResponse.restored_schur_response] using h

/-- The native Mobius and support observations are evaluated in the same
complete response, not in a separate balanced state. -/
theorem native_probe_support_ledger (N : ℕ) (alpha L : ℝ) (t : ℝ≥0) :
    restored N alpha L
        (diagonalObservation (HistoryPrefixMobiusResponse.probe N))
        (diagonalObservation (HistoryPrefixMobiusResponse.support N)) -
      restored N (alpha + (t : ℝ)) L
        (diagonalObservation (HistoryPrefixMobiusResponse.probe N))
        (diagonalObservation (HistoryPrefixMobiusResponse.support N)) =
      GibbsTraceForm.Z (logIntensity N alpha L) *
          (HistoryPrefixMobiusResponse.signedMean N alpha L *
            (1 - HistoryPrefixMobiusResponse.supportFraction N alpha L)) -
        GibbsTraceForm.Z (logIntensity N (alpha + (t : ℝ)) L) *
          (HistoryPrefixMobiusResponse.signedMean N (alpha + (t : ℝ)) L *
            (1 - HistoryPrefixMobiusResponse.supportFraction N (alpha + (t : ℝ)) L)) := by
  simp only [restored_hessian, HistoryPrefixMobiusResponse.probe_support_hessian]

structure Conclusions : Prop where
  actual_scale_direction : ∀ (N : ℕ) (alpha L t : ℝ) (i : Index N),
    logIntensity N (alpha + t) L i = logIntensity N alpha L i - t * rootEnergy N L i
  complete_response_ledger : ∀ (N : ℕ) (alpha L : ℝ) (t : ℝ≥0) (K : Hermitian (Index N)),
    restored N alpha L K K = restored N (alpha + (t : ℝ)) L K K +
      responseLoss N alpha L t K +
        GibbsTraceForm.Z (logIntensity N (alpha + (t : ℝ)) L) *
          (matrixMean N (alpha + (t : ℝ)) L K - matrixMean N alpha L K) ^ 2
  positive_kernel_loss : ∀ (N : ℕ) (alpha L : ℝ) (t : ℝ≥0) (K : Hermitian (Index N)),
    0 ≤ responseLoss N alpha L t K
  native_resolution_contraction : ∀ (N : ℕ) (alpha L : ℝ) (t : ℝ≥0) (K : Hermitian (Index N)),
    restored N (alpha + (t : ℝ)) L K K ≤
      Real.exp (-(t : ℝ) / L ^ 2) * restored N alpha L K K

theorem generated : Conclusions where
  actual_scale_direction := logIntensity_shift
  complete_response_ledger := complete_square_ledger
  positive_kernel_loss := responseLoss_nonneg
  native_resolution_contraction := complete_response_contraction

end GeneratedFoundations.Analysis.HistoryPrefixResolutionResponse

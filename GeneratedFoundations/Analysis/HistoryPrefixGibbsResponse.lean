module

public import GeneratedFoundations.Arithmetic.HistoryCentralSectors
public import GeneratedFoundations.Analysis.HistoryPhaseResponse

/-!
# Connected response on the actual Gaussian root prefix

The carrier is the existing dependent sum of all history--phase fibres above
roots `1,...,N+1`. Its reference intensity is the persistent Gaussian root
mass times the uniquely generated conditional history--phase law. Summing
over a fibre recovers precisely its root mass; summing over the prefix gives
the actual finite Gaussian capacity. No uniform distribution on roots or
second copy of a central sector is inserted.

The response acts on the full Hermitian matrix algebra of this carrier.
Thus its Hessian contains cross-root, cross-history and cross-phase entries.
The fixed-root response is a conditional part of this construction, rather
than a replacement for the root-dependent Gaussian weights. `alpha` and `L`
index observations of the generated source, not additional source data.

The intrinsic central observation counts prime occupation with multiplicity.
It is defined on every positive root; its restriction to square-free roots
agrees with the exterior-occupation character. No such restriction is made
in this full-prefix construction.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Matrix.Norms.Operator

namespace GeneratedFoundations.Analysis.HistoryPrefixGibbsResponse

open Arithmetic Arithmetic.CompleteHistory
open Operations Operations.PreparedTraceForm
open GibbsExponentialDifferentiation (realDiagonal expDividedDifference)

abbrev Index (N : ℕ) := HistoryCentralSectors.Label N

noncomputable instance (N : ℕ) : DecidableEq (Index N) := Classical.decEq _

instance (N : ℕ) : Nonempty (Index N) :=
  ⟨⟨⟨0, by omega⟩, HistoryModuleRepresentation.base 0⟩⟩

def intensity (N : ℕ) (alpha L : ℝ) (i : Index N) : ℝ :=
  HistoryPhaseResponse.intensity i.1.val alpha L i.2

theorem intensity_pos (N : ℕ) (alpha L : ℝ) (i : Index N) :
    0 < intensity N alpha L i :=
  HistoryPhaseResponse.intensity_pos _ _ _ _

def logIntensity (N : ℕ) (alpha L : ℝ) (i : Index N) : ℝ :=
  Real.log (intensity N alpha L i)

@[simp] theorem exp_logIntensity (N : ℕ) (alpha L : ℝ) (i : Index N) :
    Real.exp (logIntensity N alpha L i) = intensity N alpha L i :=
  Real.exp_log (intensity_pos N alpha L i)

/-- The normalization is the actual finite Gaussian capacity, including
every root in the prefix with its own weight. -/
theorem partition_eq_prefix (N : ℕ) (alpha L : ℝ) :
    GibbsTraceForm.Z (logIntensity N alpha L) =
      ∑ b : Fin (N + 1), gaussianRootMass alpha L (b.val + 1) := by
  simp only [GibbsTraceForm.Z, exp_logIntensity]
  change (∑ i : (Σ b : Fin (N + 1), HistoryPhaseBundle.Fiber b.val),
    HistoryPhaseResponse.intensity i.1.val alpha L i.2) = _
  rw [Fintype.sum_sigma]
  simp only [HistoryPhaseResponse.intensity, ← Finset.mul_sum,
    HistoryPhaseBundle.probability_total, mul_one]

def probability (N : ℕ) (alpha L : ℝ) (i : Index N) : ℝ :=
  intensity N alpha L i / GibbsTraceForm.Z (logIntensity N alpha L)

theorem probability_pos (N : ℕ) (alpha L : ℝ) (i : Index N) :
    0 < probability N alpha L i :=
  div_pos (intensity_pos N alpha L i) (GibbsTraceForm.Z_pos _)

theorem probability_total (N : ℕ) (alpha L : ℝ) :
    (∑ i : Index N, probability N alpha L i) = 1 := by
  simp only [probability, ← Finset.sum_div]
  have hs : (∑ i : Index N, intensity N alpha L i) =
      GibbsTraceForm.Z (logIntensity N alpha L) := by
    simp only [GibbsTraceForm.Z, exp_logIntensity]
  rw [hs, div_self (GibbsTraceForm.Z_ne_zero _)]

/-- The conditional history--phase law is unchanged; its root marginal is
the actual Gaussian root mass divided by the complete prefix capacity. -/
theorem probability_root_marginal (N : ℕ) (alpha L : ℝ) (b : Fin (N + 1)) :
    (∑ x : HistoryPhaseBundle.Fiber b.val, probability N alpha L ⟨b, x⟩) =
      gaussianRootMass alpha L (b.val + 1) /
        GibbsTraceForm.Z (logIntensity N alpha L) := by
  simp only [probability, intensity, HistoryPhaseResponse.intensity,
    ← Finset.sum_div, ← Finset.mul_sum, HistoryPhaseBundle.probability_total,
    mul_one]

def mean (N : ℕ) (alpha L : ℝ) (f : Index N → ℝ) : ℝ :=
  ∑ i, probability N alpha L i * f i

@[simp] theorem mean_one (N : ℕ) (alpha L : ℝ) :
    mean N alpha L (fun _ => 1) = 1 := by
  simpa only [mean, mul_one] using probability_total N alpha L

def response (N : ℕ) (alpha L : ℝ) : Hermitian (Index N) → ℝ :=
  GibbsConnectedResponse.response (Index N) (logIntensity N alpha L)

theorem full_hessian (N : ℕ) (alpha L : ℝ) (K J : Hermitian (Index N)) :
    fderiv ℝ (fderiv ℝ (response N alpha L)) 0 K J =
      GibbsTraceForm.gibbsForm (logIntensity N alpha L)
        (K : Mat (Index N)) (J : Mat (Index N)) :=
  GibbsConnectedResponse.response_hessian_apply _ _ _ _

/-- The positive square formula is on all matrix entries, including those
between distinct roots. Its weights are the actual exponential divided
differences of the generated reference intensities. -/
theorem full_hessian_squares (N : ℕ) (alpha L : ℝ) (K : Hermitian (Index N)) :
    fderiv ℝ (fderiv ℝ (response N alpha L)) 0 K K =
      GibbsTraceForm.weightedNormSq (logIntensity N alpha L)
        (GibbsTraceForm.centered (logIntensity N alpha L) (K : Mat (Index N))) /
          GibbsTraceForm.Z (logIntensity N alpha L) := by
  rw [full_hessian]
  exact GibbsTraceForm.gibbsForm_self_normSq _ (hermitian_isHermitian _ K)

theorem hessian_nonneg (N : ℕ) (alpha L : ℝ) (K : Hermitian (Index N)) :
    0 ≤ fderiv ℝ (fderiv ℝ (response N alpha L)) 0 K K :=
  GibbsConnectedResponse.response_hessian_nonneg _ _ _

theorem hessian_kernel (N : ℕ) (alpha L : ℝ) (K : Hermitian (Index N)) :
    (∀ J : Hermitian (Index N), fderiv ℝ (fderiv ℝ (response N alpha L)) 0 K J = 0) ↔
      ∃ r : ℝ, (K : Mat (Index N)) = r • (1 : Mat (Index N)) :=
  GibbsConnectedResponse.response_hessian_kernel_iff _ _ _

theorem hessian_positive (N : ℕ) (alpha L : ℝ)
    (K : Traceless (Index N)) (hK : K ≠ 0) :
    0 < fderiv ℝ (fderiv ℝ (response N alpha L)) 0 K.val K.val :=
  GibbsConnectedResponse.response_hessian_traceless_pos _ _ K hK

theorem response_rank (N : ℕ) (alpha L : ℝ) :
    Module.finrank ℝ
      (LinearMap.range (fderiv ℝ (fderiv ℝ (response N alpha L)) 0).toLinearMap) =
        (Fintype.card (Index N)) ^ 2 - 1 :=
  GibbsConnectedResponse.response_hessian_range_finrank _ _

def diagonalObservation {N : ℕ} (f : Index N → ℝ) : Hermitian (Index N) :=
  ⟨realDiagonal f, by
    apply Matrix.IsHermitian.isSelfAdjoint
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro i
    change star (f i : ℂ) = (f i : ℂ)
    simp⟩

theorem diagonal_mean (N : ℕ) (alpha L : ℝ) (f : Index N → ℝ) :
    GibbsTraceForm.mean (logIntensity N alpha L)
      (diagonalObservation f : Mat (Index N)) = mean N alpha L f := by
  rw [GibbsTraceForm.mean_apply, GibbsTraceForm.weightedTrace_eq_sum]
  simp only [diagonalObservation, realDiagonal, Matrix.diagonal_apply_eq,
    Complex.ofReal_re, Finset.sum_div, mean, probability]
  apply Finset.sum_congr rfl
  intro i _
  rw [exp_logIntensity]
  ring

theorem diagonal_pairing (N : ℕ) (alpha L : ℝ) (f g : Index N → ℝ) :
    GibbsTraceForm.responsePairing (logIntensity N alpha L)
        (diagonalObservation f : Mat (Index N)) (diagonalObservation g : Mat (Index N)) /
      GibbsTraceForm.Z (logIntensity N alpha L) =
        mean N alpha L (fun i => f i * g i) := by
  rw [GibbsTraceForm.responsePairing_eq_sum]
  simp only [diagonalObservation, realDiagonal]
  have hs : (∑ i : Index N, ∑ j : Index N,
      expDividedDifference (logIntensity N alpha L i) (logIntensity N alpha L j) *
        ((Matrix.diagonal (fun h => (f h : ℂ))) i j *
          (Matrix.diagonal (fun h => (g h : ℂ))) j i).re) =
      ∑ i : Index N, Real.exp (logIntensity N alpha L i) * (f i * g i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single i]
    · simp [GibbsExponentialDifferentiation.expDividedDifference_self]
    · intro j _ hji
      simp [hji, Ne.symm hji]
    · simp
  rw [hs, Finset.sum_div]
  simp only [mean, probability, exp_logIntensity]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem hessian_covariance (N : ℕ) (alpha L : ℝ) (f g : Index N → ℝ) :
    fderiv ℝ (fderiv ℝ (response N alpha L)) 0
      (diagonalObservation f) (diagonalObservation g) =
        mean N alpha L (fun i => f i * g i) -
          mean N alpha L f * mean N alpha L g := by
  rw [full_hessian]
  change GibbsTraceForm.responsePairing (logIntensity N alpha L)
      (diagonalObservation f : Mat (Index N)) (diagonalObservation g : Mat (Index N)) /
        GibbsTraceForm.Z (logIntensity N alpha L) -
      GibbsTraceForm.mean (logIntensity N alpha L) (diagonalObservation f : Mat (Index N)) *
        GibbsTraceForm.mean (logIntensity N alpha L) (diagonalObservation g : Mat (Index N)) = _
  rw [diagonal_pairing, diagonal_mean, diagonal_mean]

/-- Root observables keep their true Gaussian marginal, rather than the
uniform average over roots or histories. -/
theorem mean_root_observation (N : ℕ) (alpha L : ℝ) (f : Fin (N + 1) → ℝ) :
    mean N alpha L (fun i => f i.1) =
      (∑ b : Fin (N + 1), gaussianRootMass alpha L (b.val + 1) * f b) /
        GibbsTraceForm.Z (logIntensity N alpha L) := by
  unfold mean
  change (∑ i : (Σ b : Fin (N + 1), HistoryPhaseBundle.Fiber b.val),
    probability N alpha L i * f i.1) = _
  rw [Fintype.sum_sigma]
  simp only [← Finset.sum_mul, probability_root_marginal, div_mul_eq_mul_div,
    Finset.sum_div]

def centre (N : ℕ) (i : Index N) : ℝ :=
  (-1) ^ GeneratedPrimeParity.rootPrimeCount (i.1.val + 1)

theorem centre_square (N : ℕ) (i : Index N) : centre N i * centre N i = 1 := by
  rcases neg_one_pow_eq_or ℝ (GeneratedPrimeParity.rootPrimeCount (i.1.val + 1)) with h | h <;>
    simp [centre, h]

/-- The center susceptibility belongs to this same prefix response. Its
mean is the actual weighted prime-occupation character, not an imposed zero. -/
theorem centre_hessian (N : ℕ) (alpha L : ℝ) :
    fderiv ℝ (fderiv ℝ (response N alpha L)) 0
      (diagonalObservation (centre N)) (diagonalObservation (centre N)) =
        1 - (mean N alpha L (centre N)) ^ 2 := by
  rw [hessian_covariance]
  simp only [centre_square, mean_one, pow_two]

/-- The finite-prefix response is constructed from the existing positive
source and matrix carrier; a caller supplies no state or positivity proof. -/
structure Conclusions : Prop where
  actual_partition : ∀ (N : ℕ) (alpha L : ℝ),
    GibbsTraceForm.Z (logIntensity N alpha L) =
      ∑ b : Fin (N + 1), gaussianRootMass alpha L (b.val + 1)
  root_marginal : ∀ (N : ℕ) (alpha L : ℝ) (b : Fin (N + 1)),
    (∑ x : HistoryPhaseBundle.Fiber b.val, probability N alpha L ⟨b, x⟩) =
      gaussianRootMass alpha L (b.val + 1) /
        GibbsTraceForm.Z (logIntensity N alpha L)
  complete_hessian : ∀ (N : ℕ) (alpha L : ℝ) (K J : Hermitian (Index N)),
    fderiv ℝ (fderiv ℝ (response N alpha L)) 0 K J =
      GibbsTraceForm.gibbsForm (logIntensity N alpha L)
        (K : Mat (Index N)) (J : Mat (Index N))
  complete_rank : ∀ (N : ℕ) (alpha L : ℝ),
    Module.finrank ℝ
      (LinearMap.range (fderiv ℝ (fderiv ℝ (response N alpha L)) 0).toLinearMap) =
        (Fintype.card (Index N)) ^ 2 - 1
  actual_centre_susceptibility : ∀ (N : ℕ) (alpha L : ℝ),
    fderiv ℝ (fderiv ℝ (response N alpha L)) 0
      (diagonalObservation (centre N)) (diagonalObservation (centre N)) =
        1 - (mean N alpha L (centre N)) ^ 2

theorem generated : Conclusions where
  actual_partition := partition_eq_prefix
  root_marginal := probability_root_marginal
  complete_hessian := full_hessian
  complete_rank := response_rank
  actual_centre_susceptibility := centre_hessian

end GeneratedFoundations.Analysis.HistoryPrefixGibbsResponse

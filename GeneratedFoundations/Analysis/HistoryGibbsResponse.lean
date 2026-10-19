module

public import GeneratedFoundations.Arithmetic.HistoryObservation
public import GeneratedFoundations.Operations.GibbsConnectedResponse

/-!
# The connected response of the complete finite history source

The diagonal reference is the logarithm of the actual positive Gaussian
history intensity.  Consequently its partition at zero perturbation is the
generated root mass, and its conditional weights are exactly the persistent
history law.  All Hermitian perturbations are retained: in particular the
connected Hessian below includes every off-diagonal direction.

`K` is an observation direction, and `alpha`, `L` index observations of the
already constructed source.  None is an additional root datum.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Matrix.Norms.Operator

namespace GeneratedFoundations.Analysis.HistoryGibbsResponse

open Arithmetic
open Arithmetic.CompleteHistory Arithmetic.HistoryObservation
open Operations.PreparedTraceForm (Mat Hermitian Traceless)
open Operations
open GibbsExponentialDifferentiation (realDiagonal expDividedDifference)

abbrev Index (n : ℕ) := History (n + 1)

noncomputable instance (n : ℕ) : DecidableEq (Index n) := Classical.decEq _

def logIntensity (n : ℕ) (alpha L : ℝ) (h : Index n) : ℝ :=
  Real.log (flatGaussianIntensity alpha L h)

@[simp] theorem exp_logIntensity (n : ℕ) (alpha L : ℝ) (h : Index n) :
    Real.exp (logIntensity n alpha L h) = flatGaussianIntensity alpha L h := by
  exact Real.exp_log (HistoryTiltedBalance.flatGaussianIntensity_pos alpha L h)

theorem partition_eq_root (n : ℕ) (alpha L : ℝ) :
    GibbsTraceForm.Z (logIntensity n alpha L) = gaussianRootMass alpha L (n + 1) := by
  simp only [GibbsTraceForm.Z, exp_logIntensity]
  exact flatGaussian_pushforward alpha L (n + 1) (by omega)

theorem conditional_weight (n : ℕ) (alpha L : ℝ) (h : Index n) :
    Real.exp (logIntensity n alpha L h) / GibbsTraceForm.Z (logIntensity n alpha L) =
      flatWeight h := by
  rw [exp_logIntensity, partition_eq_root, flatGaussianIntensity]
  exact mul_div_cancel_left₀ _ (ne_of_gt (gaussianRootMass_pos alpha L (n + 1)))

def response (n : ℕ) (alpha L : ℝ) : Hermitian (Index n) → ℝ :=
  GibbsConnectedResponse.response (Index n) (logIntensity n alpha L)

theorem response_zero (n : ℕ) (alpha L : ℝ) :
    response n alpha L 0 = Real.log (gaussianRootMass alpha L (n + 1)) := by
  rw [response, GibbsConnectedResponse.response,
    GibbsConnectedResponse.partition_zero, partition_eq_root]

theorem full_hessian (n : ℕ) (alpha L : ℝ) (K J : Hermitian (Index n)) :
    fderiv ℝ (fderiv ℝ (response n alpha L)) 0 K J =
      GibbsTraceForm.gibbsForm (logIntensity n alpha L) (K : Mat (Index n))
        (J : Mat (Index n)) :=
  GibbsConnectedResponse.response_hessian_apply _ _ _ _

theorem hessian_nonneg (n : ℕ) (alpha L : ℝ) (K : Hermitian (Index n)) :
    0 ≤ fderiv ℝ (fderiv ℝ (response n alpha L)) 0 K K :=
  GibbsConnectedResponse.response_hessian_nonneg _ _ _

theorem hessian_kernel (n : ℕ) (alpha L : ℝ) (K : Hermitian (Index n)) :
    (∀ J : Hermitian (Index n), fderiv ℝ (fderiv ℝ (response n alpha L)) 0 K J = 0) ↔
      ∃ r : ℝ, (K : Mat (Index n)) = r • (1 : Mat (Index n)) :=
  GibbsConnectedResponse.response_hessian_kernel_iff _ _ _

theorem hessian_positive_on_traceless (n : ℕ) (alpha L : ℝ)
    (K : Traceless (Index n)) (hK : K ≠ 0) :
    0 < fderiv ℝ (fderiv ℝ (response n alpha L)) 0 K.val K.val :=
  GibbsConnectedResponse.response_hessian_traceless_pos _ _ K hK

theorem response_rank (n : ℕ) (alpha L : ℝ) :
    Module.finrank ℝ
      (LinearMap.range (fderiv ℝ (fderiv ℝ (response n alpha L)) 0).toLinearMap) =
      (Fintype.card (Index n)) ^ 2 - 1 :=
  GibbsConnectedResponse.response_hessian_range_finrank _ _

/-- Diagonal observations are embedded in the full Hermitian response space. -/
def diagonalObservation {n : ℕ} (f : Index n → ℝ) : Hermitian (Index n) :=
  ⟨realDiagonal f, by
    apply Matrix.IsHermitian.isSelfAdjoint
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro i
    change star (f i : ℂ) = (f i : ℂ)
    simp⟩

theorem diagonal_mean (n : ℕ) (alpha L : ℝ) (f : Index n → ℝ) :
    GibbsTraceForm.mean (logIntensity n alpha L)
      (diagonalObservation f : Mat (Index n)) = HistoryObservation.mean f := by
  rw [GibbsTraceForm.mean_apply, GibbsTraceForm.weightedTrace_eq_sum]
  simp only [diagonalObservation, realDiagonal, Matrix.diagonal_apply_eq,
    Complex.ofReal_re, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro h _
  rw [← div_mul_eq_mul_div, conditional_weight]

theorem diagonal_pairing (n : ℕ) (alpha L : ℝ) (f g : Index n → ℝ) :
    GibbsTraceForm.responsePairing (logIntensity n alpha L)
        (diagonalObservation f : Mat (Index n)) (diagonalObservation g : Mat (Index n)) /
      GibbsTraceForm.Z (logIntensity n alpha L) =
        HistoryObservation.mean (fun h => f h * g h) := by
  rw [GibbsTraceForm.responsePairing_eq_sum]
  simp only [diagonalObservation, realDiagonal]
  have hs : (∑ i : Index n, ∑ j : Index n,
      expDividedDifference (logIntensity n alpha L i) (logIntensity n alpha L j) *
        ((Matrix.diagonal (fun h => (f h : ℂ))) i j *
          (Matrix.diagonal (fun h => (g h : ℂ))) j i).re) =
      ∑ i : Index n, Real.exp (logIntensity n alpha L i) * (f i * g i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single i]
    · simp [GibbsExponentialDifferentiation.expDividedDifference_self]
    · intro j _ hji
      simp [hji, Ne.symm hji]
    · simp
  rw [hs, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro h _
  rw [← div_mul_eq_mul_div, conditional_weight]

/-- The covariance uses the persistent history probabilities, with the
Gaussian root normalization cancelled by the proved partition identity. -/
theorem hessian_covariance (n : ℕ) (alpha L : ℝ) (f g : Index n → ℝ) :
    fderiv ℝ (fderiv ℝ (response n alpha L)) 0
      (diagonalObservation f) (diagonalObservation g) =
        HistoryObservation.mean (fun h => f h * g h) -
          HistoryObservation.mean f * HistoryObservation.mean g := by
  rw [full_hessian]
  change GibbsTraceForm.responsePairing (logIntensity n alpha L)
      (diagonalObservation f : Mat (Index n)) (diagonalObservation g : Mat (Index n)) /
      GibbsTraceForm.Z (logIntensity n alpha L) -
      GibbsTraceForm.mean (logIntensity n alpha L) (diagonalObservation f : Mat (Index n)) *
      GibbsTraceForm.mean (logIntensity n alpha L) (diagonalObservation g : Mat (Index n)) = _
  rw [diagonal_pairing, diagonal_mean, diagonal_mean]

theorem orientation_hessian (n : ℕ) (alpha L : ℝ) :
    fderiv ℝ (fderiv ℝ (response n alpha L)) 0
      (diagonalObservation (fun h => (CompleteHistoryGeometry.orientationScore h : ℝ)))
      (diagonalObservation (fun h => (CompleteHistoryGeometry.orientationScore h : ℝ))) =
        HistoryObservation.energy
          (fun h : Index n => (CompleteHistoryGeometry.orientationScore h : ℝ)) := by
  rw [hessian_covariance, orientation_mean_zero]
  simp only [zero_mul, sub_zero, HistoryObservation.energy, HistoryObservation.pairing]

/-- The same reference law that generates histories also generates its full
finite matrix response; positivity is proved, not a field supplied by a caller. -/
structure Conclusions : Prop where
  root_partition : ∀ (n : ℕ) (alpha L : ℝ),
    GibbsTraceForm.Z (logIntensity n alpha L) = gaussianRootMass alpha L (n + 1)
  source_weights : ∀ (n : ℕ) (alpha L : ℝ) (h : Index n),
    Real.exp (logIntensity n alpha L h) / GibbsTraceForm.Z (logIntensity n alpha L) =
      flatWeight h
  connected_positive : ∀ (n : ℕ) (alpha L : ℝ) (K : Hermitian (Index n)),
    0 ≤ fderiv ℝ (fderiv ℝ (response n alpha L)) 0 K K
  effective_rank : ∀ (n : ℕ) (alpha L : ℝ),
    Module.finrank ℝ
      (LinearMap.range (fderiv ℝ (fderiv ℝ (response n alpha L)) 0).toLinearMap) =
      (Fintype.card (Index n)) ^ 2 - 1
  actual_covariance : ∀ (n : ℕ) (alpha L : ℝ) (f g : Index n → ℝ),
    fderiv ℝ (fderiv ℝ (response n alpha L)) 0
      (diagonalObservation f) (diagonalObservation g) =
        HistoryObservation.mean (fun h => f h * g h) -
          HistoryObservation.mean f * HistoryObservation.mean g

theorem generated : Conclusions where
  root_partition := partition_eq_root
  source_weights := conditional_weight
  connected_positive := hessian_nonneg
  effective_rank := response_rank
  actual_covariance := hessian_covariance

end GeneratedFoundations.Analysis.HistoryGibbsResponse

module

public import GeneratedFoundations.Arithmetic.HistoryMatrixAlgebra
public import GeneratedFoundations.Operations.GibbsConnectedResponse

/-!
# The full matrix response of the complete history--phase fibre

The actual phase law is uniquely selected by its history marginal and phase
translation invariance in `HistoryPhaseBundle`.  Multiplying that law by the
same Gaussian root mass constructs the positive reference for this module.
Its partition is the original root mass, and the matrix response acts on all
history--phase coefficients, not merely on phase-blind observations.

The scalar kernel and the connected rank are obtained from the common Gibbs
theorem after proving the reference weights of this concrete fibre.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Matrix.Norms.Operator

namespace GeneratedFoundations.Analysis.HistoryPhaseResponse

open Arithmetic Arithmetic.CompleteHistory
open Operations Operations.PreparedTraceForm

abbrev Index (n : ℕ) := HistoryPhaseBundle.Fiber n

noncomputable instance (n : ℕ) : DecidableEq (Index n) := Classical.decEq _

instance (n : ℕ) : Nonempty (Index n) :=
  ⟨Classical.choice (HistoryObservation.history_nonempty (n + 1) (by omega)), 0⟩

def intensity (n : ℕ) (alpha L : ℝ) (x : Index n) : ℝ :=
  gaussianRootMass alpha L (n + 1) * HistoryPhaseBundle.probability x

theorem intensity_pos (n : ℕ) (alpha L : ℝ) (x : Index n) :
    0 < intensity n alpha L x :=
  mul_pos (gaussianRootMass_pos _ _ _) (HistoryPhaseBundle.probability_pos x)

def logIntensity (n : ℕ) (alpha L : ℝ) (x : Index n) : ℝ :=
  Real.log (intensity n alpha L x)

@[simp] theorem exp_logIntensity (n : ℕ) (alpha L : ℝ) (x : Index n) :
    Real.exp (logIntensity n alpha L x) = intensity n alpha L x :=
  Real.exp_log (intensity_pos n alpha L x)

theorem partition_eq_root (n : ℕ) (alpha L : ℝ) :
    GibbsTraceForm.Z (logIntensity n alpha L) = gaussianRootMass alpha L (n + 1) := by
  simp only [GibbsTraceForm.Z, exp_logIntensity, intensity, ← Finset.mul_sum,
    HistoryPhaseBundle.probability_total, mul_one]

theorem conditional_weight (n : ℕ) (alpha L : ℝ) (x : Index n) :
    Real.exp (logIntensity n alpha L x) / GibbsTraceForm.Z (logIntensity n alpha L) =
      HistoryPhaseBundle.probability x := by
  rw [exp_logIntensity, partition_eq_root, intensity]
  exact mul_div_cancel_left₀ _ (ne_of_gt (gaussianRootMass_pos _ _ _))

def response (n : ℕ) (alpha L : ℝ) : Hermitian (Index n) → ℝ :=
  GibbsConnectedResponse.response (Index n) (logIntensity n alpha L)

theorem full_hessian (n : ℕ) (alpha L : ℝ) (K J : Hermitian (Index n)) :
    fderiv ℝ (fderiv ℝ (response n alpha L)) 0 K J =
      GibbsTraceForm.gibbsForm (logIntensity n alpha L)
        (K : Mat (Index n)) (J : Mat (Index n)) :=
  GibbsConnectedResponse.response_hessian_apply _ _ _ _

theorem hessian_nonneg (n : ℕ) (alpha L : ℝ) (K : Hermitian (Index n)) :
    0 ≤ fderiv ℝ (fderiv ℝ (response n alpha L)) 0 K K :=
  GibbsConnectedResponse.response_hessian_nonneg _ _ _

theorem hessian_kernel (n : ℕ) (alpha L : ℝ) (K : Hermitian (Index n)) :
    (∀ J : Hermitian (Index n), fderiv ℝ (fderiv ℝ (response n alpha L)) 0 K J = 0) ↔
      ∃ r : ℝ, (K : Mat (Index n)) = r • (1 : Mat (Index n)) :=
  GibbsConnectedResponse.response_hessian_kernel_iff _ _ _

theorem hessian_positive (n : ℕ) (alpha L : ℝ)
    (K : Traceless (Index n)) (hK : K ≠ 0) :
    0 < fderiv ℝ (fderiv ℝ (response n alpha L)) 0 K.val K.val :=
  GibbsConnectedResponse.response_hessian_traceless_pos _ _ K hK

theorem response_rank (n : ℕ) (alpha L : ℝ) :
    Module.finrank ℝ
      (LinearMap.range (fderiv ℝ (fderiv ℝ (response n alpha L)) 0).toLinearMap) =
        (Fintype.card (Index n)) ^ 2 - 1 :=
  GibbsConnectedResponse.response_hessian_range_finrank _ _

structure Conclusions : Prop where
  same_root_partition : ∀ (n : ℕ) (alpha L : ℝ),
    GibbsTraceForm.Z (logIntensity n alpha L) = gaussianRootMass alpha L (n + 1)
  actual_source_weights : ∀ (n : ℕ) (alpha L : ℝ) (x : Index n),
    Real.exp (logIntensity n alpha L x) / GibbsTraceForm.Z (logIntensity n alpha L) =
      HistoryPhaseBundle.probability x
  complete_hessian : ∀ (n : ℕ) (alpha L : ℝ) (K J : Hermitian (Index n)),
    fderiv ℝ (fderiv ℝ (response n alpha L)) 0 K J =
      GibbsTraceForm.gibbsForm (logIntensity n alpha L) (K : Mat (Index n)) (J : Mat (Index n))
  complete_rank : ∀ (n : ℕ) (alpha L : ℝ),
    Module.finrank ℝ
      (LinearMap.range (fderiv ℝ (fderiv ℝ (response n alpha L)) 0).toLinearMap) =
        (Fintype.card (Index n)) ^ 2 - 1

theorem generated : Conclusions where
  same_root_partition := partition_eq_root
  actual_source_weights := conditional_weight
  complete_hessian := full_hessian
  complete_rank := response_rank

end GeneratedFoundations.Analysis.HistoryPhaseResponse

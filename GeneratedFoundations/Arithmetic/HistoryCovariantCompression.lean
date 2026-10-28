module

public import GeneratedFoundations.Arithmetic.HistoryJointConnector
public import GeneratedFoundations.Operations.CovariantCompression

/-!
# Retained phase response and its complete complement

The projection is the average of the actual generated finite phase action.
It is not selected to make the connection small. Every history remains in
its range, and every detail coefficient remains in its complement. The
projection commutes with the original source action and its connector.

Compression is applied to the complete covariant first jet. The Gram
identity retains the complement and both moving-readout interference terms.
-/

@[expose] public section
noncomputable section
open scoped Matrix
namespace GeneratedFoundations.Arithmetic.HistoryCovariantCompression

open HistoryJointCharge HistoryJointChargeLattice

def projection (n : ℕ) : Module.End ℂ (Space n) :=
  blocks n (fun _ => HistoryPhaseProjection.projection n)

def complement (n : ℕ) : Module.End ℂ (Space n) := 1 - projection n

theorem projection_square (n : ℕ) : projection n * projection n = projection n := by
  unfold projection
  rw [HistoryJointChargeQuotient.blocks_mul]
  congr 1
  funext s
  exact HistoryPhaseProjection.projection_idempotent n

theorem projection_adjoint (n : ℕ) : (projection n).adjoint = projection n := by
  symm
  apply (LinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  change (∑ s : Spin, inner ℂ (projection n x s) (y s)) =
    ∑ s : Spin, inner ℂ (x s) (projection n y s)
  simp only [projection, blocks_apply]
  exact Finset.sum_congr rfl fun s _ =>
    (LinearMap.eq_adjoint_iff _ _).mp (HistoryPhaseProjection.projection_adjoint n).symm
      (x s) (y s)

theorem projection_source (n : ℕ) (M : Operations.SourceCliffordConnector.ChiralMatrix) :
    projection n * HistoryJointSourceTransport.sourceAction n M =
      HistoryJointSourceTransport.sourceAction n M * projection n := by
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  intro s
  simp only [Module.End.mul_apply, projection, blocks_apply,
    HistoryJointSourceTransport.sourceAction_apply, map_sum, map_smul]

theorem projection_connector (n : ℕ) (H : Operations.ReversalRealConnector.Spinor) :
    projection n * HistoryJointConnector.scalarConnector n H =
      HistoryJointConnector.scalarConnector n H * projection n :=
  projection_source n _

theorem reconstruction (n : ℕ) (x : Space n) :
    projection n x + complement n x = x := by simp [complement]

theorem projection_complement (n : ℕ) : projection n * complement n = 0 := by
  rw [complement, mul_sub, mul_one, projection_square, sub_self]

theorem complement_projection (n : ℕ) : complement n * projection n = 0 := by
  rw [complement, sub_mul, one_mul, projection_square, sub_self]

/-- Every operation on the full detail subspace is retained, not just a
single distinguished mode. Its response on the invariant subspace is zero. -/
def detailResponse (n : ℕ) (T : Module.End ℂ (Space n)) : Module.End ℂ (Space n) :=
  complement n * T * complement n

theorem projection_detailResponse (n : ℕ) (T : Module.End ℂ (Space n)) :
    projection n * detailResponse n T = 0 := by
  rw [detailResponse, ← mul_assoc, ← mul_assoc, projection_complement, zero_mul, zero_mul]

theorem detailResponse_projection (n : ℕ) (T : Module.End ℂ (Space n)) :
    detailResponse n T * projection n = 0 := by
  rw [detailResponse, mul_assoc, complement_projection, mul_zero]

theorem projection_complement_inner (n : ℕ) (x y : Space n) :
    inner ℂ (projection n x) (complement n y) = 0 := by
  change (∑ s : Spin, inner ℂ (projection n x s) (complement n y s)) = 0
  simp only [complement, LinearMap.sub_apply, Module.End.one_apply,
    PiLp.sub_apply, projection, blocks_apply]
  simpa only [HistoryPhaseProjection.residual, LinearMap.sub_apply,
    Module.End.one_apply] using
    (Finset.sum_eq_zero fun (s : Spin) _ =>
      HistoryPhaseProjection.projection_residual_inner n (x s) (y s))

theorem norm_decomposition (n : ℕ) (x : Space n) :
    ‖x‖ ^ 2 = ‖projection n x‖ ^ 2 + ‖complement n x‖ ^ 2 := by
  have h := norm_add_sq (𝕜 := ℂ) (projection n x) (complement n x)
  rw [reconstruction, projection_complement_inner] at h
  simpa using h

theorem projectionMatrix_square (n : ℕ) :
    HistoryPhaseProjection.projectionMatrix n * HistoryPhaseProjection.projectionMatrix n =
      HistoryPhaseProjection.projectionMatrix n := by
  apply HistoryModuleRepresentation.representation_injective n
  simp only [map_mul, HistoryPhaseProjection.projection_matrix,
    HistoryPhaseProjection.projection_idempotent]

/-- Every column of the original covariant jet is retained in one of the
two complementary Gram blocks; no absolute-value budget is introduced. -/
theorem covariantJet_gram (n : ℕ) {κ : Type*} [Fintype κ]
    (J : Matrix (HistoryModuleRepresentation.Index n) κ ℂ) :
    Jᴴ * J = (HistoryPhaseProjection.projectionMatrix n * J)ᴴ *
      (HistoryPhaseProjection.projectionMatrix n * J) +
      ((1 - HistoryPhaseProjection.projectionMatrix n) * J)ᴴ *
      ((1 - HistoryPhaseProjection.projectionMatrix n) * J) :=
  Operations.CovariantCompression.projection_gram _ J
    (HistoryPhaseProjection.projectionMatrix_adjoint n) (projectionMatrix_square n)

structure Conclusions : Prop where
  actual_projection : ∀ n, projection n * projection n = projection n
  self_adjoint : ∀ n, (projection n).adjoint = projection n
  full_source_compatibility : ∀ n M,
    projection n * HistoryJointSourceTransport.sourceAction n M =
      HistoryJointSourceTransport.sourceAction n M * projection n
  full_connector_compatibility : ∀ n H,
    projection n * HistoryJointConnector.scalarConnector n H =
      HistoryJointConnector.scalarConnector n H * projection n
  complete_energy : ∀ n x,
    ‖x‖ ^ 2 = ‖projection n x‖ ^ 2 + ‖complement n x‖ ^ 2
  detail_left_zero : ∀ n T, projection n * detailResponse n T = 0
  detail_right_zero : ∀ n T, detailResponse n T * projection n = 0

theorem generated : Conclusions where
  actual_projection := projection_square
  self_adjoint := projection_adjoint
  full_source_compatibility := projection_source
  full_connector_compatibility := projection_connector
  complete_energy := norm_decomposition
  detail_left_zero := projection_detailResponse
  detail_right_zero := detailResponse_projection

end GeneratedFoundations.Arithmetic.HistoryCovariantCompression

module

public import GeneratedFoundations.Physical.SourceLocalizedFrames
public import GeneratedFoundations.Physical.SourceReversalIsometry

/-!
# Source reversal on overlapping Hermitian charts

Each actual local frame transports the fixed source antiunitary to its fiber.
Two such reversals agree exactly when the passive change of frame commutes
with the source reversal, equivalently when its source matrix belongs to SU(2).
The equivalence starts with arbitrary Hermitian charts, not with a prescribed
special-unitary transition.

Triple-overlap compatibility and uniqueness of the common fiber reversal follow
from this criterion. These are statements on chart domains and their overlaps;
no global trivialization or existence of a compatible Hermitian atlas is assumed
or inferred.
-/

@[expose] public section

noncomputable section

open scoped Bundle
open GeneratedFoundations.Physical.SourceJointResponse (S)
open GeneratedFoundations.Operations.SourceSpinCornerGroup (SU2)

namespace GeneratedFoundations.Physical.SourcePseudorealCharts

open SourceLocalizedFrames
open SourceReversalIsometry (sourceReversal PseudorealFrameChange)

theorem orthonormalCoordinates_frameMatrix {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (b : OrthonormalBasis (Fin 2) ℂ H) (g : H ≃ₗᵢ[ℂ] H) :
    LinearMap.toMatrixOrthonormal b g.toLinearEquiv.toLinearMap = frameMatrix b g := rfl

/-- The full source matrix is the matrix of the same map in the fixed orthonormal frame. -/
theorem sourceMatrix_eq_frameMatrix (g : S ≃ₗᵢ[ℂ] S) :
    SourceScalarConnector.sourceMatrix g.toLinearEquiv.toLinearMap =
      frameMatrix SourceChiralCarrier.spinBasis g := by
  have h := SourceChiralCarrier.spinMatrixCoordinates_spinAction
    (SourceScalarConnector.sourceMatrix g.toLinearEquiv.toLinearMap)
  have hh : SourceScalarConnector.sourceMatrix g.toLinearEquiv.toLinearMap =
      SourceChiralCarrier.spinMatrixCoordinates g.toLinearEquiv.toLinearMap := by
    simpa only [SourceScalarConnector.spinAction_sourceMatrix] using h.symm
  exact hh.trans (orthonormalCoordinates_frameMatrix SourceChiralCarrier.spinBasis g)

variable {M : Type*} [TopologicalSpace M]
  {E : M → Type*} [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℂ (E x)] [TopologicalSpace (Bundle.TotalSpace S E)]

variable (e f k : Bundle.Trivialization S (π S E))
  [e.IsLinear ℂ] [f.IsLinear ℂ] [k.IsLinear ℂ]

/-- A frame has direction `S → E x`; its inverse is the source coordinate map. -/
def localReversal (he : IsHermitianChart e) (x : M) (hx : x ∈ e.baseSet) :
    E x ≃ₗᵢ⋆[ℂ] E x :=
  SourceReversalIsometry.framedReversal (frame e he x hx).symm

@[simp] theorem localReversal_apply (he : IsHermitianChart e)
    (x : M) (hx : x ∈ e.baseSet) (v : E x) :
    localReversal e he x hx v =
      frame e he x hx (sourceReversal ((frame e he x hx).symm v)) := rfl

theorem localReversal_inner (he : IsHermitianChart e)
    (x : M) (hx : x ∈ e.baseSet) (u v : E x) :
    inner ℂ (localReversal e he x hx u) (localReversal e he x hx v) = inner ℂ v u :=
  SourceReversalIsometry.framedReversal_inner (frame e he x hx).symm u v

@[simp] theorem localReversal_square (he : IsHermitianChart e)
    (x : M) (hx : x ∈ e.baseSet) (v : E x) :
    localReversal e he x hx (localReversal e he x hx v) = -v :=
  SourceReversalIsometry.framedReversal_square (frame e he x hx).symm v

@[simp] theorem localReversal_frame (he : IsHermitianChart e)
    (x : M) (hx : x ∈ e.baseSet) (v : S) :
    localReversal e he x hx (frame e he x hx v) = frame e he x hx (sourceReversal v) := by
  rw [localReversal_apply, (frame e he x hx).symm_apply_apply]

theorem localReversal_other_frame (he : IsHermitianChart e) (hf : IsHermitianChart f)
    (x : M) (hx : x ∈ e.baseSet) (hy : x ∈ f.baseSet) (v : S) :
    localReversal e he x hx (frame f hf x hy v) =
      frame e he x hx (sourceReversal (transition e f he hf x hx hy v)) := rfl

/-- Agreement is tested on the actual common fiber, and is equivalent to source pseudoreality. -/
theorem localReversal_eq_iff_pseudoreal (he : IsHermitianChart e) (hf : IsHermitianChart f)
    (x : M) (hx : x ∈ e.baseSet) (hy : x ∈ f.baseSet) :
    localReversal e he x hx = localReversal f hf x hy ↔
      PseudorealFrameChange (transition e f he hf x hx hy) := by
  constructor
  · intro h v
    have hv := congrArg (fun J : E x ≃ₗᵢ⋆[ℂ] E x => J (frame f hf x hy v)) h
    rw [localReversal_other_frame, localReversal_frame] at hv
    apply (frame e he x hx).injective
    rw [frame_transition]
    exact hv.symm
  · intro hg
    apply LinearIsometryEquiv.ext
    intro w
    obtain ⟨v, rfl⟩ := (frame f hf x hy).surjective w
    rw [localReversal_other_frame, localReversal_frame, ← hg v, frame_transition]

/-- The condition concerns the complete matrix of an arbitrary chart transition. -/
theorem localReversal_eq_iff_specialUnitary
    (he : IsHermitianChart e) (hf : IsHermitianChart f)
    (x : M) (hx : x ∈ e.baseSet) (hy : x ∈ f.baseSet) :
    localReversal e he x hx = localReversal f hf x hy ↔
      frameMatrix SourceChiralCarrier.spinBasis (transition e f he hf x hx hy) ∈ SU2 := by
  rw [localReversal_eq_iff_pseudoreal,
    SourceReversalIsometry.pseudorealFrameChange_iff_specialUnitary,
    sourceMatrix_eq_frameMatrix]

/-- The same test may be written directly for the library's actual overlap operator. -/
theorem overlapOperator_reversal_iff
    (he : IsHermitianChart e) (hf : IsHermitianChart f)
    (x : M) (hx : x ∈ e.baseSet) (hy : x ∈ f.baseSet) :
    (∀ v, overlapOperator e f x (sourceReversal v) =
      sourceReversal (overlapOperator e f x v)) ↔
        localReversal e he x hx = localReversal f hf x hy := by
  rw [overlapOperator_eq_transition e f he hf x hx hy]
  exact (localReversal_eq_iff_pseudoreal e f he hf x hx hy).symm

theorem transition_pseudoreal_trans
    (he : IsHermitianChart e) (hf : IsHermitianChart f) (hk : IsHermitianChart k)
    (x : M) (hx : x ∈ e.baseSet) (hy : x ∈ f.baseSet) (hz : x ∈ k.baseSet)
    (hef : PseudorealFrameChange (transition e f he hf x hx hy))
    (hfk : PseudorealFrameChange (transition f k hf hk x hy hz)) :
    PseudorealFrameChange (transition e k he hk x hx hz) :=
  (localReversal_eq_iff_pseudoreal e k he hk x hx hz).mp
    (((localReversal_eq_iff_pseudoreal e f he hf x hx hy).mpr hef).trans
      ((localReversal_eq_iff_pseudoreal f k hf hk x hy hz).mpr hfk))

theorem transition_specialUnitary_trans
    (he : IsHermitianChart e) (hf : IsHermitianChart f) (hk : IsHermitianChart k)
    (x : M) (hx : x ∈ e.baseSet) (hy : x ∈ f.baseSet) (hz : x ∈ k.baseSet)
    (hef : frameMatrix SourceChiralCarrier.spinBasis (transition e f he hf x hx hy) ∈ SU2)
    (hfk : frameMatrix SourceChiralCarrier.spinBasis (transition f k hf hk x hy hz) ∈ SU2) :
    frameMatrix SourceChiralCarrier.spinBasis (transition e k he hk x hx hz) ∈ SU2 :=
  (localReversal_eq_iff_specialUnitary e k he hk x hx hz).mp
    (((localReversal_eq_iff_specialUnitary e f he hf x hx hy).mpr hef).trans
      ((localReversal_eq_iff_specialUnitary f k hf hk x hy hz).mpr hfk))

/-- One source frame determines its transported reversal on the entire fiber. -/
theorem localReversal_unique (he : IsHermitianChart e)
    (x : M) (hx : x ∈ e.baseSet) (J : E x ≃ₗᵢ⋆[ℂ] E x)
    (hJ : ∀ v, J (frame e he x hx v) = frame e he x hx (sourceReversal v)) :
    J = localReversal e he x hx := by
  apply LinearIsometryEquiv.ext
  intro w
  obtain ⟨v, rfl⟩ := (frame e he x hx).surjective w
  exact (hJ v).trans (localReversal_frame e he x hx v).symm

/-- Compatible charts determine one common antiunitary on their shared fiber. -/
theorem commonReversal_existsUnique
    (he : IsHermitianChart e) (hf : IsHermitianChart f)
    (x : M) (hx : x ∈ e.baseSet) (hy : x ∈ f.baseSet)
    (hg : PseudorealFrameChange (transition e f he hf x hx hy)) :
    ∃! J : E x ≃ₗᵢ⋆[ℂ] E x,
      (∀ v, J (frame e he x hx v) = frame e he x hx (sourceReversal v)) ∧
      (∀ v, J (frame f hf x hy v) = frame f hf x hy (sourceReversal v)) := by
  have heq := (localReversal_eq_iff_pseudoreal e f he hf x hx hy).mpr hg
  refine ⟨localReversal e he x hx, ⟨?_, ?_⟩, ?_⟩
  · exact localReversal_frame e he x hx
  · intro v
    rw [heq]
    exact localReversal_frame f hf x hy v
  · intro J hJ
    exact localReversal_unique e he x hx J hJ.1

end GeneratedFoundations.Physical.SourcePseudorealCharts

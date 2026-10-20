module

public import GeneratedFoundations.Physical.SourceChiralCarrier
public import GeneratedFoundations.Geometry.HermitianFrames

/-!
# Physical names for shared Hermitian frame comparisons

Chart transitions and complete matrix frame classification use the common
proofs. The colour specialization below retains its actual source carrier.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Physical.SourceLocalizedFrames

export GeneratedFoundations.Geometry.HermitianFrames (
  IsHermitianChart
  frame
  frameMatrix
  frameMatrix_existsUnique
  frameMatrix_frameOfMatrix
  frameMatrix_injective
  frameMatrix_specialUnitary_iff
  frameMatrix_unitary
  frameOfMatrix
  frame_apply
  frame_symm_apply
  frame_transition
  matrixOperator_unitary
  overlapOperator
  overlapOperator_continuousOn
  overlapOperator_eq_transition
  overlapOperator_inner
  passive_components
  transition
  transition_cocycle
  transition_inverse
  transition_self
  transition_unique
)

/-- The colour coordinates use the actual degree-two source Hilbert carrier. -/
def colourFrameMatrix (g : SourceJointResponse.W ≃ₗᵢ[ℂ] SourceJointResponse.W) :
    Matrix (Fin 3) (Fin 3) ℂ := frameMatrix SourceChiralCarrier.colourBasis g

theorem colourFrameMatrix_specialUnitary_iff
    (g : SourceJointResponse.W ≃ₗᵢ[ℂ] SourceJointResponse.W) :
    colourFrameMatrix g ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ ↔
      (colourFrameMatrix g).det = 1 :=
  frameMatrix_specialUnitary_iff SourceChiralCarrier.colourBasis g

end GeneratedFoundations.Physical.SourceLocalizedFrames

module

public import GeneratedFoundations.Geometry.SourceScalarResponse

/-!
# Complete matrix coordinates in the original Gaussian--Haar phase frame

These are orthonormal coordinates of the common degree-one source carrier.
The inverse matrix action and the Hilbert adjoint are taken on that actual
carrier. Both generated branches use the same ordered vacuum/excitation
basis, rather than choosing a new phase frame for a particular response.
-/

@[expose] public section

noncomputable section

open scoped Quaternion

namespace GeneratedFoundations.Geometry.SourceSpinCoordinates

open SourceSpinIdentification (S spinBasis spinAction)

def spinMatrixCoordinates : Module.End ℂ S ≃⋆ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  LinearMap.toMatrixOrthonormal spinBasis

theorem spinMatrixCoordinates_apply (h : Module.End ℂ S) (i j : Fin 2) :
    spinMatrixCoordinates h i j = inner ℂ (spinBasis i) (h (spinBasis j)) :=
  LinearMap.toMatrixOrthonormal_apply_apply spinBasis h i j

theorem spinMatrixCoordinates_adjoint (h : Module.End ℂ S) :
    spinMatrixCoordinates h.adjoint = (spinMatrixCoordinates h).conjTranspose := by
  exact map_star spinMatrixCoordinates h

theorem spinMatrixCoordinates_spinAction (M : Matrix (Fin 2) (Fin 2) ℂ) :
    spinMatrixCoordinates (spinAction M) = M := SourceSpinIdentification.spinAction_matrix M

theorem spinMatrixCoordinates_sourceOperator (U : Operations.SourceSpinCornerGroup.SU2) :
    spinMatrixCoordinates (SourceSymmetricUnitary.sourceOperator 1 U) =
      (U : Operations.SourceSpinCorner.Mat2) := by
  rw [← SourceSpinIdentification.spinAction_sourceOperator]
  exact spinMatrixCoordinates_spinAction _

/-- The algebraic inverse and the metric matrix coordinates coincide on every
source endomorphism, not only on unitary or reversal-real responses. -/
theorem sourceMatrix_eq (h : Module.End ℂ S) :
    SourceScalarResponse.sourceMatrix h = spinMatrixCoordinates h := by
  rw [← SourceScalarResponse.spinAction_sourceMatrix h, spinMatrixCoordinates_spinAction]
  simp

def quaternionSpin (q : ℍ) : Module.End ℂ S :=
  spinMatrixCoordinates.symm (SourceQuaternionAmplitude.matrixMap q)

theorem quaternionSpin_eq_sourceAction (q : ℍ) :
    quaternionSpin q = spinAction (SourceQuaternionAmplitude.matrixMap q) := by
  apply spinMatrixCoordinates.injective
  exact (spinMatrixCoordinates.apply_symm_apply _).trans
    (spinMatrixCoordinates_spinAction _).symm

end GeneratedFoundations.Geometry.SourceSpinCoordinates

module

public import GeneratedFoundations.Arithmetic.HistoryTracelessCoordinates
public import GeneratedFoundations.Arithmetic.HistoryDefiningResponse
public import GeneratedFoundations.Operations.MatrixHermitianFrame
public import GeneratedFoundations.Operations.OrthogonalQuadraticFrame

/-!
# Hermitian generators of the complete arithmetic response

The actual history--phase/source operation algebra is represented faithfully
on its full coefficient space. Hermitian symmetric and antisymmetric
centred units are transported through that same representation. Their
reconstruction retains every traceless operation and their calculated
quadratic sum agrees with the existing defining response.

This is a redundant Hermitian frame, not a copied eight-generator colour
basis. Unique coordinates and their positive Gram metric are supplied by
`HistoryTracelessCoordinates`; the frame sum has its own explicit half-trace
normalization. Neither the dimension nor the response coefficient is an
additional source input.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Matrix

namespace GeneratedFoundations.Arithmetic.HistoryHermitianResponse

open HistoryCliffordAction (Index Algebra Space action)
open Operations.MatrixHermitianFrame

def symmetricGenerator (N : ℕ) (i j : Index N) : Module.End ℂ (Space N) :=
  action N (symmetric i j)

def antisymmetricGenerator (N : ℕ) (i j : Index N) : Module.End ℂ (Space N) :=
  action N (antisymmetric i j)

theorem symmetricGenerator_adjoint (N : ℕ) (i j : Index N) :
    (symmetricGenerator N i j).adjoint = symmetricGenerator N i j := by
  rw [symmetricGenerator, HistoryCliffordAction.action_adjoint,
    (symmetric_hermitian i j).eq]

theorem antisymmetricGenerator_adjoint (N : ℕ) (i j : Index N) :
    (antisymmetricGenerator N i j).adjoint = antisymmetricGenerator N i j := by
  rw [antisymmetricGenerator, HistoryCliffordAction.action_adjoint,
    (antisymmetric_hermitian i j).eq]

theorem symmetricGenerator_trace (N : ℕ) (i j : Index N) :
    LinearMap.trace ℂ (Space N) (symmetricGenerator N i j) = 0 := by
  rw [symmetricGenerator, HistoryAdjointCasimir.trace_action, symmetric_trace]

theorem antisymmetricGenerator_trace (N : ℕ) (i j : Index N) :
    LinearMap.trace ℂ (Space N) (antisymmetricGenerator N i j) = 0 := by
  rw [antisymmetricGenerator, HistoryAdjointCasimir.trace_action, antisymmetric_trace]

theorem centred_reconstruction (N : ℕ) (i j : Index N) :
    symmetricGenerator N i j + Complex.I • antisymmetricGenerator N i j =
      HistoryDefiningResponse.generator N i j := by
  rw [symmetricGenerator, antisymmetricGenerator, ← map_smul, ← map_add,
    Operations.MatrixHermitianFrame.centred_reconstruction]
  rfl

/-- Completeness is proved on the actual source operation, before any
quadratic estimate. -/
theorem complete_expansion (N : ℕ) (X : Algebra N) (hX : Matrix.trace X = 0) :
    (∑ i, ∑ j, X i j •
      (symmetricGenerator N i j + Complex.I • antisymmetricGenerator N i j)) =
        action N X := by
  have h := congrArg (action N)
    (Operations.MatrixHermitianFrame.complete_expansion X hX)
  simpa only [map_sum, map_smul, map_add,
    symmetricGenerator, antisymmetricGenerator] using h

def response (N : ℕ) : Module.End ℂ (Space N) :=
  (1 / 2 : ℂ) • ∑ i, ∑ j,
    (symmetricGenerator N i j * symmetricGenerator N i j +
      antisymmetricGenerator N i j * antisymmetricGenerator N i j)

theorem response_eq (N : ℕ) : response N = HistoryDefiningResponse.response N := by
  have h := congrArg (action N)
    (Operations.MatrixHermitianFrame.response_eq_traceDual (ι := Index N))
  simpa only [Operations.MatrixHermitianFrame.response,
    Operations.MatrixDefiningCasimir.response, Operations.MatrixDefiningCasimir.quadraticSum,
    HistoryDefiningResponse.response, HistoryDefiningResponse.generator,
    response, symmetricGenerator, antisymmetricGenerator,
    map_sum, map_smul, map_add, map_mul] using h

theorem response_coefficient (N : ℕ) :
    response N = (HistoryDefiningResponse.coefficient N : ℂ) • 1 := by
  rw [response_eq, HistoryDefiningResponse.response_eq]

theorem response_adjoint (N : ℕ) : (response N).adjoint = response N := by
  rw [response_eq, HistoryDefiningResponse.response_adjoint]

theorem response_commutes (N : ℕ) (T : Module.End ℂ (Space N)) :
    response N * T = T * response N := by
  rw [response_eq]
  exact HistoryDefiningResponse.response_commutes N T

theorem response_energy (N : ℕ) (x : Space N) :
    (inner ℂ x (response N x)).re = HistoryDefiningResponse.coefficient N * ‖x‖ ^ 2 := by
  rw [response_eq]
  exact HistoryDefiningResponse.quadratic_eq N x

/-- The full normalized quadratic response is invariant under every change
of state coordinates, not only the original two source frame factors. -/
theorem response_conjugate (N : ℕ) (u : (Module.End ℂ (Space N))ˣ) :
    (↑u : Module.End ℂ (Space N)) * response N * (↑(u⁻¹) : Module.End ℂ (Space N)) =
      response N := by
  rw [response_coefficient]
  simp

/-- Both Hermitian parts of every centred matrix unit are retained. -/
abbrev FrameIndex (N : ℕ) := (Index N × Index N) ⊕ (Index N × Index N)

def frameGenerator (N : ℕ) : FrameIndex N → Module.End ℂ (Space N)
  | .inl ij => symmetricGenerator N ij.1 ij.2
  | .inr ij => antisymmetricGenerator N ij.1 ij.2

theorem frameGenerator_adjoint (N : ℕ) (a : FrameIndex N) :
    (frameGenerator N a).adjoint = frameGenerator N a := by
  cases a with
  | inl ij => exact symmetricGenerator_adjoint N ij.1 ij.2
  | inr ij => exact antisymmetricGenerator_adjoint N ij.1 ij.2

theorem response_eq_frame (N : ℕ) :
    response N = (1 / 2 : ℂ) •
      ∑ a : FrameIndex N, frameGenerator N a * frameGenerator N a := by
  simp only [response, Fintype.sum_sum_type, Fintype.sum_prod_type,
    frameGenerator, Finset.sum_add_distrib]

def rotatedGenerator (N : ℕ) (O : Matrix (FrameIndex N) (FrameIndex N) ℝ)
    (a : FrameIndex N) : Module.End ℂ (Space N) :=
  Operations.OrthogonalQuadraticFrame.rotated O (frameGenerator N) a

theorem rotated_response (N : ℕ) (O : Matrix (FrameIndex N) (FrameIndex N) ℝ)
    (hO : Operations.OrthogonalQuadraticFrame.OrthogonalChange O) :
    (1 / 2 : ℂ) • ∑ a, rotatedGenerator N O a * rotatedGenerator N O a =
      response N := by
  rw [response_eq_frame]
  exact congrArg ((1 / 2 : ℂ) • ·)
    (Operations.OrthogonalQuadraticFrame.quadratic_invariant O hO (frameGenerator N))

structure Conclusions : Prop where
  actual_symmetric_adjoint : ∀ N i j,
    (symmetricGenerator N i j).adjoint = symmetricGenerator N i j
  actual_antisymmetric_adjoint : ∀ N i j,
    (antisymmetricGenerator N i j).adjoint = antisymmetricGenerator N i j
  complete_reconstruction : ∀ N X, Matrix.trace X = 0 →
    (∑ i, ∑ j, X i j •
      (symmetricGenerator N i j + Complex.I • antisymmetricGenerator N i j)) = action N X
  same_response : ∀ N, response N = HistoryDefiningResponse.response N
  calculated_coefficient : ∀ N,
    response N = (HistoryDefiningResponse.coefficient N : ℂ) • 1
  full_covariance : ∀ N (u : (Module.End ℂ (Space N))ˣ),
    (↑u : Module.End ℂ (Space N)) * response N * (↑(u⁻¹) : Module.End ℂ (Space N)) = response N
  orthogonal_frame_invariance : ∀ N O,
    Operations.OrthogonalQuadraticFrame.OrthogonalChange O →
      (1 / 2 : ℂ) • ∑ a, rotatedGenerator N O a * rotatedGenerator N O a = response N

theorem generated : Conclusions where
  actual_symmetric_adjoint := symmetricGenerator_adjoint
  actual_antisymmetric_adjoint := antisymmetricGenerator_adjoint
  complete_reconstruction := complete_expansion
  same_response := response_eq
  calculated_coefficient := response_coefficient
  full_covariance := response_conjugate
  orthogonal_frame_invariance := rotated_response

end GeneratedFoundations.Arithmetic.HistoryHermitianResponse

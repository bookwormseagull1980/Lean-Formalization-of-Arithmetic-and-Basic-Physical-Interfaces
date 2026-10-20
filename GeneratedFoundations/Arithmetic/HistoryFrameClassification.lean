module

public import GeneratedFoundations.Arithmetic.HistoryFrameDeterminant
public import GeneratedFoundations.Arithmetic.HistoryResponseFrames
public import GeneratedFoundations.Geometry.SourcePhaseFrames
public import GeneratedFoundations.Geometry.SourceReversalIsometry

/-!
# Complete frame classifications for the generated arithmetic source

The full arithmetic coefficient fibre, the original alternating source line
and the original pseudoreal two-mode source are different carriers. Their
unitary classifications are retained on those respective carriers. The
effective source group is then represented faithfully on the complete
arithmetic response, with every matrix coefficient included.

In particular the arithmetic determinant phase uses its derived dimension;
the line has a unique circle phase; and preservation of the fixed source
reversal characterizes SU(2). These comparison theorems introduce no new
carrier or frame as a parameter of the canonical generated entry.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Arithmetic.HistoryFrameClassification

open HistoryModuleRepresentation (Space Index)
open Geometry.UnitaryDeterminantPhase (MatrixN SpecialUnitary)

structure Conclusions : Prop where
  arithmetic_unitary : ∀ n (g : Space n ≃ₗᵢ[ℂ] Space n),
    HistoryPhaseFrames.frameMatrix n g ∈ Matrix.unitaryGroup (Fin (Fintype.card (Index n))) ℂ
  arithmetic_specialUnitary : ∀ n (g : Space n ≃ₗᵢ[ℂ] Space n),
    HistoryPhaseFrames.frameMatrix n g ∈ Matrix.specialUnitaryGroup
      (Fin (Fintype.card (Index n))) ℂ ↔ (HistoryPhaseFrames.frameMatrix n g).det = 1
  arithmetic_realization : ∀ n (M : MatrixN (HistoryFrameDeterminant.dimension n)),
    M ∈ Matrix.unitaryGroup (Fin (HistoryFrameDeterminant.dimension n)) ℂ →
      ∃! g : Space n ≃ₗᵢ[ℂ] Space n, HistoryPhaseFrames.frameMatrix n g = M
  arithmetic_phase_decomposition : ∀ n (g : Space n ≃ₗᵢ[ℂ] Space n),
    ∃ (z : Circle) (U : SpecialUnitary (HistoryFrameDeterminant.dimension n)),
      HistoryPhaseFrames.frameMatrix n g =
        (z : ℂ) • (U : MatrixN (HistoryFrameDeterminant.dimension n)) ∧
      (z : ℂ) ^ HistoryFrameDeterminant.dimension n = (HistoryPhaseFrames.frameMatrix n g).det
  arithmetic_phase_ambiguity : ∀ n (g : Space n ≃ₗᵢ[ℂ] Space n) (z w : Circle)
    (U V : SpecialUnitary (HistoryFrameDeterminant.dimension n)),
    HistoryPhaseFrames.frameMatrix n g =
      (z : ℂ) • (U : MatrixN (HistoryFrameDeterminant.dimension n)) →
    HistoryPhaseFrames.frameMatrix n g =
      (w : ℂ) • (V : MatrixN (HistoryFrameDeterminant.dimension n)) →
    (w / z) ^ HistoryFrameDeterminant.dimension n = 1 ∧
      (V : MatrixN (HistoryFrameDeterminant.dimension n)) =
        (((w / z)⁻¹ : Circle) : ℂ) • (U : MatrixN (HistoryFrameDeterminant.dimension n))
  source_line_classification : ∀ g : Geometry.SourceJointResponse.L ≃ₗᵢ[ℂ]
    Geometry.SourceJointResponse.L, ∃! z : Circle, ∀ v, g v = (z : ℂ) • v
  source_pseudoreal_classification : ∀ g : Geometry.SourceJointResponse.S ≃ₗᵢ[ℂ]
    Geometry.SourceJointResponse.S, Geometry.SourceReversalIsometry.PseudorealFrameChange g ↔
      Geometry.SourceScalarResponse.sourceMatrix g.toLinearEquiv.toLinearMap ∈
        Operations.SourceSpinCornerGroup.SU2
  effective_response_faithful : ∀ N,
    Function.Injective (HistoryEffectiveResponseSpace.unitaryRepresentation N)

theorem generated : Conclusions where
  arithmetic_unitary := HistoryPhaseFrames.frameMatrix_unitary
  arithmetic_specialUnitary := HistoryPhaseFrames.frameMatrix_specialUnitary_iff
  arithmetic_realization := HistoryPhaseFrames.frameMatrix_existsUnique
  arithmetic_phase_decomposition := HistoryFrameDeterminant.frame_exists_phase_specialUnitary
  arithmetic_phase_ambiguity := HistoryFrameDeterminant.frame_decomposition_ambiguity
  source_line_classification := Geometry.SourcePhaseFrames.unitary_existsUnique_phase
  source_pseudoreal_classification :=
    Geometry.SourceReversalIsometry.pseudorealFrameChange_iff_specialUnitary
  effective_response_faithful := HistoryEffectiveResponseSpace.unitaryRepresentation_faithful

end GeneratedFoundations.Arithmetic.HistoryFrameClassification

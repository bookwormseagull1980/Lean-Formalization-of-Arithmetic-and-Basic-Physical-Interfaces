module

public import GeneratedFoundations.Arithmetic.HistoryPhaseFrames
public import GeneratedFoundations.Geometry.UnitaryDeterminantPhase

/-!
# Determinant phase of the complete arithmetic frame

The dimension in the phase equation is the cardinality of the generated
history--phase fibre. It is positive because the fibre contains its generated
base point. Every unitary of this actual fibre admits the pointwise phase
decomposition. The ambiguity is computed at this derived dimension rather
than copied from a three-dimensional physical comparison.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Arithmetic.HistoryFrameDeterminant

open HistoryModuleRepresentation (Index Space base)
open Geometry.UnitaryDeterminantPhase (MatrixN SpecialUnitary)

def dimension (n : ℕ) : ℕ := Fintype.card (Index n)

theorem dimension_pos (n : ℕ) : 0 < dimension n :=
  Fintype.card_pos_iff.mpr ⟨base n⟩

theorem frame_exists_phase_specialUnitary (n : ℕ) (g : Space n ≃ₗᵢ[ℂ] Space n) :
    ∃ (z : Circle) (U : SpecialUnitary (dimension n)),
      HistoryPhaseFrames.frameMatrix n g = (z : ℂ) • (U : MatrixN (dimension n)) ∧
        (z : ℂ) ^ dimension n = (HistoryPhaseFrames.frameMatrix n g).det :=
  Geometry.UnitaryDeterminantPhase.exists_phase_specialUnitary (dimension n)
    (dimension_pos n) _ (HistoryPhaseFrames.frameMatrix_unitary n g)

theorem frame_decomposition_ambiguity (n : ℕ) (g : Space n ≃ₗᵢ[ℂ] Space n)
    (z w : Circle) (U V : SpecialUnitary (dimension n))
    (hU : HistoryPhaseFrames.frameMatrix n g = (z : ℂ) • (U : MatrixN (dimension n)))
    (hV : HistoryPhaseFrames.frameMatrix n g = (w : ℂ) • (V : MatrixN (dimension n))) :
    (w / z) ^ dimension n = 1 ∧
      (V : MatrixN (dimension n)) =
        (((w / z)⁻¹ : Circle) : ℂ) • (U : MatrixN (dimension n)) :=
  Geometry.UnitaryDeterminantPhase.decomposition_ambiguity (dimension n) _ z w U V hU hV

structure Conclusions : Prop where
  actual_positive_dimension : ∀ n, 0 < dimension n
  all_unitary_frames : ∀ n (g : Space n ≃ₗᵢ[ℂ] Space n),
    ∃ (z : Circle) (U : SpecialUnitary (dimension n)),
      HistoryPhaseFrames.frameMatrix n g = (z : ℂ) • (U : MatrixN (dimension n)) ∧
        (z : ℂ) ^ dimension n = (HistoryPhaseFrames.frameMatrix n g).det
  exact_ambiguity : ∀ n (g : Space n ≃ₗᵢ[ℂ] Space n)
    (z w : Circle) (U V : SpecialUnitary (dimension n)),
    HistoryPhaseFrames.frameMatrix n g = (z : ℂ) • (U : MatrixN (dimension n)) →
    HistoryPhaseFrames.frameMatrix n g = (w : ℂ) • (V : MatrixN (dimension n)) →
      (w / z) ^ dimension n = 1 ∧ (V : MatrixN (dimension n)) =
        (((w / z)⁻¹ : Circle) : ℂ) • (U : MatrixN (dimension n))

theorem generated : Conclusions where
  actual_positive_dimension := dimension_pos
  all_unitary_frames := frame_exists_phase_specialUnitary
  exact_ambiguity := frame_decomposition_ambiguity

end GeneratedFoundations.Arithmetic.HistoryFrameDeterminant

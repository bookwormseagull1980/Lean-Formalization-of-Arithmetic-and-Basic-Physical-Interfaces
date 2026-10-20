module

public import GeneratedFoundations.Physical.SourceLocalizedFrames
public import GeneratedFoundations.Geometry.UnitaryDeterminantPhase
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.CStarAlgebra.Basic

/-!
# Colour-frame determinant and phase

Every unitary comparison of the actual three-dimensional colour carrier
has a scalar phase times a determinant-one representative. The phase is a
cube root of the determinant, and two such factorizations are related by
the displayed inverse scalar action of a cube root of unity.

These are pointwise frame statements. They do not choose a continuous
cube root on a base space, trivialize a determinant bundle, or identify the
colour phase with the common matter phase action.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Physical.SourceColourPhase

abbrev ColourMatrix := Matrix (Fin 3) (Fin 3) ℂ
abbrev ColourSpecialUnitary := Matrix.specialUnitaryGroup (Fin 3) ℂ

theorem phase_specialUnitary_det (z : Circle) (U : ColourSpecialUnitary) :
    ((z : ℂ) • (U : ColourMatrix)).det = (z : ℂ) ^ 3 :=
  Geometry.UnitaryDeterminantPhase.phase_specialUnitary_det 3 z U

/-- The determinant fixes the colour phase up to a cube root of unity. -/
theorem exists_phase_specialUnitary (M : ColourMatrix)
    (hM : M ∈ Matrix.unitaryGroup (Fin 3) ℂ) :
    ∃ (z : Circle) (U : ColourSpecialUnitary),
      M = (z : ℂ) • (U : ColourMatrix) ∧ (z : ℂ) ^ 3 = M.det :=
  Geometry.UnitaryDeterminantPhase.exists_phase_specialUnitary 3 (by decide) M hM

/-- Two decompositions carry opposite scalar changes in their two factors. -/
theorem decomposition_ambiguity (M : ColourMatrix) (z w : Circle)
    (U V : ColourSpecialUnitary)
    (hU : M = (z : ℂ) • (U : ColourMatrix))
    (hV : M = (w : ℂ) • (V : ColourMatrix)) :
    (w / z) ^ 3 = 1 ∧
      (V : ColourMatrix) = (((w / z)⁻¹ : Circle) : ℂ) • (U : ColourMatrix) :=
  Geometry.UnitaryDeterminantPhase.decomposition_ambiguity 3 M z w U V hU hV

/-- Applied to the orthonormal coordinates of the generated colour fiber. -/
theorem colourFrame_exists_phase_specialUnitary
    (g : SourceJointResponse.W ≃ₗᵢ[ℂ] SourceJointResponse.W) :
    ∃ (z : Circle) (U : ColourSpecialUnitary),
      SourceLocalizedFrames.colourFrameMatrix g = (z : ℂ) • (U : ColourMatrix) ∧
        (z : ℂ) ^ 3 = (SourceLocalizedFrames.colourFrameMatrix g).det :=
  exists_phase_specialUnitary _
    (SourceLocalizedFrames.frameMatrix_unitary SourceChiralCarrier.colourBasis g)

end GeneratedFoundations.Physical.SourceColourPhase

module

public import GeneratedFoundations.Physical.SourceLocalizedFrames
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

private theorem circle_mem_unitary (z : Circle) : (z : ℂ) ∈ unitary ℂ := by
  have hs : star (z : ℂ) = (z : ℂ)⁻¹ := by
    simpa only [Circle.coe_inv, Complex.star_def] using (Circle.coe_inv_eq_conj z).symm
  constructor
  · change star (z : ℂ) * (z : ℂ) = 1
    rw [hs, inv_mul_cancel₀ (Circle.coe_ne_zero z)]
  · change (z : ℂ) * star (z : ℂ) = 1
    rw [hs, mul_inv_cancel₀ (Circle.coe_ne_zero z)]

theorem phase_specialUnitary_det (z : Circle) (U : ColourSpecialUnitary) :
    ((z : ℂ) • (U : ColourMatrix)).det = (z : ℂ) ^ 3 := by
  have hdet : (U : ColourMatrix).det = 1 :=
    (Matrix.mem_specialUnitaryGroup_iff.mp U.property).2
  rw [Matrix.det_smul, Fintype.card_fin, hdet, mul_one]

/-- The determinant fixes the colour phase up to a cube root of unity. -/
theorem exists_phase_specialUnitary (M : ColourMatrix)
    (hM : M ∈ Matrix.unitaryGroup (Fin 3) ℂ) :
    ∃ (z : Circle) (U : ColourSpecialUnitary),
      M = (z : ℂ) • (U : ColourMatrix) ∧ (z : ℂ) ^ 3 = M.det := by
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq M.det (n := 3) (by decide)
  have hdetnorm : ‖M.det‖ = 1 :=
    CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary hM)
  have hnormpow : ‖a‖ ^ 3 = 1 := by
    rw [← norm_pow, ha, hdetnorm]
  have hnorm : ‖a‖ = 1 :=
    (pow_eq_one_iff_of_nonneg (norm_nonneg a) (by decide : (3 : ℕ) ≠ 0)).mp hnormpow
  let z : Circle := ⟨a, mem_sphere_zero_iff_norm.mpr hnorm⟩
  have hz : (z : ℂ) ^ 3 = M.det := ha
  have hdet_ne : M.det ≠ 0 := by
    rw [← hz]
    exact pow_ne_zero 3 (Circle.coe_ne_zero z)
  let A : ColourMatrix := ((z⁻¹ : Circle) : ℂ) • M
  have hA : A ∈ Matrix.unitaryGroup (Fin 3) ℂ :=
    Unitary.smul_mem_of_mem (circle_mem_unitary z⁻¹) hM
  have hAdet : A.det = 1 := by
    change (((z⁻¹ : Circle) : ℂ) • M).det = 1
    rw [Matrix.det_smul, Fintype.card_fin, Circle.coe_inv, inv_pow, hz,
      inv_mul_cancel₀ hdet_ne]
  refine ⟨z, ⟨A, Matrix.mem_specialUnitaryGroup_iff.mpr ⟨hA, hAdet⟩⟩, ?_, hz⟩
  change M = (z : ℂ) • (((z⁻¹ : Circle) : ℂ) • M)
  rw [smul_smul, Circle.coe_inv, mul_inv_cancel₀ (Circle.coe_ne_zero z), one_smul]

/-- Two decompositions carry opposite scalar changes in their two factors. -/
theorem decomposition_ambiguity (M : ColourMatrix) (z w : Circle)
    (U V : ColourSpecialUnitary)
    (hU : M = (z : ℂ) • (U : ColourMatrix))
    (hV : M = (w : ℂ) • (V : ColourMatrix)) :
    (w / z) ^ 3 = 1 ∧
      (V : ColourMatrix) = (((w / z)⁻¹ : Circle) : ℂ) • (U : ColourMatrix) := by
  have hcube : (w : ℂ) ^ 3 = (z : ℂ) ^ 3 := by
    calc
      (w : ℂ) ^ 3 = M.det := by rw [hV, phase_specialUnitary_det]
      _ = (z : ℂ) ^ 3 := by rw [hU, phase_specialUnitary_det]
  constructor
  · apply Circle.coe_injective
    simp only [Circle.coe_pow, Circle.coe_div, Circle.coe_one, div_pow, hcube,
      div_self (pow_ne_zero 3 (Circle.coe_ne_zero z))]
  · have he : (w : ℂ) • (V : ColourMatrix) = (z : ℂ) • (U : ColourMatrix) :=
      hV.symm.trans hU
    have hh := congrArg (fun A : ColourMatrix => (w : ℂ)⁻¹ • A) he
    have hc : (((w / z)⁻¹ : Circle) : ℂ) = (w : ℂ)⁻¹ * (z : ℂ) := by
      rw [Circle.coe_inv, Circle.coe_div, inv_div, div_eq_mul_inv, mul_comm]
    rw [hc]
    simpa only [smul_smul, inv_mul_cancel₀ (Circle.coe_ne_zero w), one_smul] using hh

/-- Applied to the orthonormal coordinates of the generated colour fiber. -/
theorem colourFrame_exists_phase_specialUnitary
    (g : SourceJointResponse.W ≃ₗᵢ[ℂ] SourceJointResponse.W) :
    ∃ (z : Circle) (U : ColourSpecialUnitary),
      SourceLocalizedFrames.colourFrameMatrix g = (z : ℂ) • (U : ColourMatrix) ∧
        (z : ℂ) ^ 3 = (SourceLocalizedFrames.colourFrameMatrix g).det :=
  exists_phase_specialUnitary _
    (SourceLocalizedFrames.frameMatrix_unitary SourceChiralCarrier.colourBasis g)

end GeneratedFoundations.Physical.SourceColourPhase

module

public import GeneratedFoundations.Operations.SourceVacuumTransport

/-!
# Determinant compensation on the transported source carrier

Tensoring with the source determinant line retains its determinant character.
The inverse character is the unique scalar correction that recovers the
original matrix action for every invertible source operation.
-/

@[expose] public section
noncomputable section

open GeneratedFoundations.Operations.SourceSpinCorner
open GeneratedFoundations.Operations.SourceSpinCornerGroup
open GeneratedFoundations.Operations.SourceVacuumTransport

namespace GeneratedFoundations.Physical.SourceDeterminantCompensation

variable {b : ℝ} (hb : 0 < b)

def relativeAction (M : Mat2) : Module.End ℂ (TwistedCarrier hb) :=
  M.det⁻¹ • twistedAction hb M

theorem relativeAction_eq_conjugatedAction (M : Mat2) (hM : M.det ≠ 0) :
    relativeAction hb M = conjugatedAction hb M := by
  rw [relativeAction, twistedAction_eq_det_smul_conjugatedAction, smul_smul,
    inv_mul_cancel₀ hM, one_smul]

theorem conjugatedAction_ne_zero (M : Mat2) (hM : M.det ≠ 0) :
    conjugatedAction hb M ≠ 0 := by
  intro hz
  have hm : M = 0 := by
    apply (sourceActionEquiv hb).injective
    apply ((transport hb).toLinearEquiv.conjAlgEquiv ℂ).injective
    simpa [conjugatedAction] using hz
  apply hM
  simp [hm]

theorem scalar_correction_unique (M : Mat2) (hM : M.det ≠ 0) (z : ℂ)
    (hz : z • twistedAction hb M = conjugatedAction hb M) :
    z = M.det⁻¹ := by
  rw [twistedAction_eq_det_smul_conjugatedAction, smul_smul] at hz
  have hscalar : z * M.det = 1 :=
    smul_left_injective ℂ (conjugatedAction_ne_zero hb M hM)
      (hz.trans (one_smul ℂ _).symm)
  simpa only [one_div] using (eq_div_iff hM).2 hscalar

theorem relativeAction_mul (M N : Mat2) (hM : M.det ≠ 0) (hN : N.det ≠ 0) :
    relativeAction hb (M * N) = relativeAction hb M * relativeAction hb N := by
  rw [relativeAction_eq_conjugatedAction hb _ (by simpa [Matrix.det_mul] using mul_ne_zero hM hN),
    relativeAction_eq_conjugatedAction hb _ hM,
    relativeAction_eq_conjugatedAction hb _ hN]
  exact map_mul ((sourceActionEquiv hb).trans
    ((transport hb).toLinearEquiv.conjAlgEquiv ℂ)) M N

theorem relativeAction_transport (M : Mat2) (hM : M.det ≠ 0) (v : V hb) :
    relativeAction hb M (transport hb v) = transport hb (sourceAction hb M v) := by
  rw [relativeAction_eq_conjugatedAction hb M hM, conjugatedAction_transport]

end GeneratedFoundations.Physical.SourceDeterminantCompensation

module

public import GeneratedFoundations.Geometry.SourceCentralObservations
public import Mathlib.Analysis.CStarAlgebra.GelfandDuality

/-!
# Characters of the complete centre-invariant source observations

The source invariant algebra is closed in the actual continuous-function
algebra and is therefore complete. Its isometric star-algebra descent to
the actual central quotient transports the character space of continuous
functions. Every character is evaluation on exactly one central orbit.

The character space here is mathlib's space of nonzero multiplicative
continuous linear functionals, with its weak-dual topology. It is not
defined to be the quotient. The choice to retain all centre-invariant
observations is unchanged; the full source observations can retain the
central sign. Identification of the quotient with real projective
three-space, metric descent and spectral parity are separate steps.
-/

@[expose] public section

noncomputable section

open Topology
open GeneratedFoundations.Operations.SourceSpinCornerGroup (SU2)
open GeneratedFoundations.Geometry.SourceSpinCentre
open GeneratedFoundations.Geometry.SourceCentralObservations

namespace GeneratedFoundations.Geometry.SourceObservationSpectrum

/-- Central invariance is a closed family of equalities of evaluation maps. -/
instance invariantAlgebra_isClosed : IsClosed (invariantAlgebra : Set C(SU2, ℂ)) := by
  change IsClosed {f : C(SU2, ℂ) | ∀ U, f (negativeIdentity * U) = f U}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun U =>
    isClosed_eq (continuous_eval_const (negativeIdentity * U)) (continuous_eval_const U)

instance invariantAlgebra_complete : CompleteSpace invariantAlgebra :=
  invariantAlgebra_isClosed.isComplete.completeSpace_coe

theorem descent_isometry : Isometry descentStarAlgEquiv := by
  apply AddMonoidHomClass.isometry_of_norm descentStarAlgEquiv
  intro f
  exact descent_norm f

theorem inverseDescent_isometry : Isometry descentStarAlgEquiv.symm := by
  apply AddMonoidHomClass.isometry_of_norm descentStarAlgEquiv.symm
  intro g
  exact pullback_norm g

theorem descent_continuous : Continuous descentStarAlgEquiv :=
  descent_isometry.continuous

theorem inverseDescent_continuous : Continuous descentStarAlgEquiv.symm :=
  inverseDescent_isometry.continuous

/-- Precomposition with the actual descent, on the existing character spaces. -/
def characterPullback :
    C(WeakDual.characterSpace ℂ C(CentralQuotient, ℂ),
      WeakDual.characterSpace ℂ invariantAlgebra) :=
  WeakDual.CharacterSpace.compContinuousMap descentStarAlgEquiv.toStarAlgHom

def characterDescend :
    C(WeakDual.characterSpace ℂ invariantAlgebra,
      WeakDual.characterSpace ℂ C(CentralQuotient, ℂ)) :=
  WeakDual.CharacterSpace.compContinuousMap descentStarAlgEquiv.symm.toStarAlgHom

@[simp] theorem characterPullback_apply
    (φ : WeakDual.characterSpace ℂ C(CentralQuotient, ℂ)) (f : invariantAlgebra) :
    characterPullback φ f = φ (descentStarAlgEquiv f) := rfl

@[simp] theorem characterDescend_apply
    (φ : WeakDual.characterSpace ℂ invariantAlgebra) (g : C(CentralQuotient, ℂ)) :
    characterDescend φ g = φ (descentStarAlgEquiv.symm g) := rfl

/-- The two continuous precomposition maps are inverse on every character. -/
def characterDescentHomeomorph :
    WeakDual.characterSpace ℂ C(CentralQuotient, ℂ) ≃ₜ
      WeakDual.characterSpace ℂ invariantAlgebra where
  toFun := characterPullback
  invFun := characterDescend
  left_inv φ := by
    apply WeakDual.CharacterSpace.ext
    intro g
    rw [characterDescend_apply, characterPullback_apply,
      descentStarAlgEquiv.apply_symm_apply]
  right_inv φ := by
    apply WeakDual.CharacterSpace.ext
    intro f
    rw [characterPullback_apply, characterDescend_apply,
      descentStarAlgEquiv.symm_apply_apply]
  continuous_toFun := characterPullback.continuous
  continuous_invFun := characterDescend.continuous

/-- All characters of the invariant algebra, not merely a chosen evaluation subspace. -/
def quotientCharacterHomeomorph :
    CentralQuotient ≃ₜ WeakDual.characterSpace ℂ invariantAlgebra :=
  (WeakDual.CharacterSpace.homeoEval CentralQuotient ℂ).trans characterDescentHomeomorph

@[simp] theorem quotientCharacterHomeomorph_apply
    (q : CentralQuotient) (f : invariantAlgebra) :
    quotientCharacterHomeomorph q f = descentStarAlgEquiv f q := rfl

@[simp] theorem quotientCharacterHomeomorph_apply_operation (U : SU2) (f : invariantAlgebra) :
    quotientCharacterHomeomorph (quotientContinuous U) f = f.val U := by
  rw [quotientCharacterHomeomorph_apply]
  exact descend_apply f.val f.property U

theorem character_eq_orbit_evaluation_unique
    (φ : WeakDual.characterSpace ℂ invariantAlgebra) :
    ∃! q : CentralQuotient, quotientCharacterHomeomorph q = φ := by
  obtain ⟨q, rfl⟩ := quotientCharacterHomeomorph.surjective φ
  exact ⟨q, rfl, fun r hr => quotientCharacterHomeomorph.injective hr⟩

/-- Every actual character has one and only one orbit on which it evaluates all observations. -/
theorem character_is_unique_orbit_evaluation
    (φ : WeakDual.characterSpace ℂ invariantAlgebra) :
    ∃! q : CentralQuotient, ∀ f : invariantAlgebra, φ f = descentStarAlgEquiv f q := by
  obtain ⟨q, hq, hunique⟩ := character_eq_orbit_evaluation_unique φ
  refine ⟨q, ?_, ?_⟩
  · intro f
    rw [← hq, quotientCharacterHomeomorph_apply]
  · intro r hr
    apply hunique r
    apply WeakDual.CharacterSpace.ext
    intro f
    rw [quotientCharacterHomeomorph_apply]
    exact (hr f).symm

/-- Evaluation at an actual source operation depends only on its central orbit. -/
def sourceCharacter (U : SU2) : WeakDual.characterSpace ℂ invariantAlgebra :=
  quotientCharacterHomeomorph (quotientContinuous U)

@[simp] theorem sourceCharacter_apply (U : SU2) (f : invariantAlgebra) :
    sourceCharacter U f = f.val U :=
  quotientCharacterHomeomorph_apply_operation U f

theorem sourceCharacter_continuous : Continuous sourceCharacter :=
  quotientCharacterHomeomorph.continuous.comp quotientContinuous.continuous

theorem sourceCharacter_surjective : Function.Surjective sourceCharacter := by
  intro φ
  obtain ⟨q, hq⟩ := quotientCharacterHomeomorph.surjective φ
  obtain ⟨U, rfl⟩ := quotientContinuous_surjective q
  exact ⟨U, hq⟩

theorem sourceCharacter_equal_iff (U V : SU2) :
    sourceCharacter U = sourceCharacter V ↔ U = V ∨ U = negativeIdentity * V := by
  change quotientCharacterHomeomorph (quotientContinuous U) =
    quotientCharacterHomeomorph (quotientContinuous V) ↔ _
  rw [quotientCharacterHomeomorph.injective.eq_iff]
  exact quotientMap_eq_iff U V

end GeneratedFoundations.Geometry.SourceObservationSpectrum

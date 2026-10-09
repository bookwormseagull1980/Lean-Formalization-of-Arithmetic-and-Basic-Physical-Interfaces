module

public import GeneratedFoundations.Source.CharacterDifferential
public import GeneratedFoundations.Source.ComplexStructure
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The representation differential and its trace metric

The representation differential is defined by differentiating the original
operator-valued action in its original Lie-group atlas. The same orthogonal
coordinate and character then identify this differential with a real scalar
multiple of the quarter-turn. The representation trace metric, rather than
the norm of a chart model, determines the two unit Lie generators.

The conclusions concern minimal orthogonal change data. The more general
trace-metric assertion for arbitrary faithful compact-group representations
is not required or asserted here.
-/

@[expose] public section

noncomputable section

open Function
open scoped Manifold ContDiff

namespace GeneratedFoundations.Source.RepresentationDifferential

variable (d : MinimalCarrier.OrthogonalChangeDatum)

/-- The original action, regarded as a map into continuous linear operators. -/
def actionMap : d.Changes → (d.Carrier →L[ℝ] d.Carrier) :=
  fun g => (d.action g).toLinearIsometry.toContinuousLinearMap

/-- The actual manifold derivative of the original representation. -/
def differential : GroupLieAlgebra (𝓡 d.groupDimension) d.Changes →L[ℝ]
    (d.Carrier →L[ℝ] d.Carrier) :=
  mfderiv (𝓡 d.groupDimension) 𝓘(ℝ, d.Carrier →L[ℝ] d.Carrier)
    (actionMap d) (1 : d.Changes)

def endomorphism (X : GroupLieAlgebra (𝓡 d.groupDimension) d.Changes) :
    Module.End ℝ d.Carrier :=
  (differential d X).toLinearMap

/-- The dimension-normalized trace form of the actual representation
differential, using the original real carrier. -/
def traceMetric (X Y : GroupLieAlgebra (𝓡 d.groupDimension) d.Changes) : ℝ :=
  -(LinearMap.trace ℝ d.Carrier (endomorphism d X * endomorphism d Y)) /
    (Module.finrank ℝ d.Carrier : ℝ)

variable (e : d.Carrier ≃ₗᵢ[ℝ] ℂ) (χ : d.Changes ≃* Circle)

/-- The existing complex scalar action expressed as a continuous linear
operator-valued map; the real carrier and its norm are unchanged. -/
def scalarOperator : ℂ →L[ℝ] (d.Carrier →L[ℝ] d.Carrier) :=
  Complex.reCLM.smulRight (ContinuousLinearMap.id ℝ d.Carrier) +
  Complex.imCLM.smulRight
    (LinearMap.toContinuousLinearMap (PlaneGenerator.generator e))

theorem scalarOperator_apply (z : ℂ) (v : d.Carrier) :
    scalarOperator d e z v = z.re • v + z.im • PlaneGenerator.generator e v := rfl

theorem scalarOperator_coordinate (z : ℂ) (v : d.Carrier) :
    e (scalarOperator d e z v) = z * e v := by
  simpa only [scalarOperator_apply, ComplexStructure.scalarAction,
    PlaneGenerator.complexScalarAction_apply] using
      ComplexStructure.scalarAction_coordinate e z v

def phaseDifferential : GroupLieAlgebra (𝓡 d.groupDimension) d.Changes →L[ℝ] ℝ :=
  Complex.imCLM.comp
    (CharacterDifferential.differential
      (E := EuclideanSpace ℝ (Fin d.groupDimension)) χ.toMonoidHom)

theorem actionMap_eq_scalarOperator
    (haction : ∀ g v, e (d.action g v) = (χ g : ℂ) * e v) :
    actionMap d = scalarOperator d e ∘ (fun g => (χ g : ℂ)) := by
  funext g
  apply ContinuousLinearMap.ext
  intro v
  apply e.injective
  exact (haction g v).trans (scalarOperator_coordinate d e (χ g : ℂ) v).symm

/-- Smoothness is a consequence of the original continuous character and
the orthogonal intertwining, not an extra assumption on the datum. -/
theorem actionMap_contMDiff (hχ : Continuous χ)
    (haction : ∀ g v, e (d.action g v) = (χ g : ℂ) * e v) :
    ContMDiff (𝓡 d.groupDimension) 𝓘(ℝ, d.Carrier →L[ℝ] d.Carrier) ∞
      (actionMap d) := by
  rw [actionMap_eq_scalarOperator d e χ haction]
  borelize d.Changes
  exact (scalarOperator d e).contMDiff.comp
    (SmoothCharacter.contMDiff_coe_character χ.toMonoidHom hχ)

set_option backward.isDefEq.respectTransparency false in
theorem differential_eq_scalarOperator (hχ : Continuous χ)
    (haction : ∀ g v, e (d.action g v) = (χ g : ℂ) * e v) :
    differential d = (scalarOperator d e).comp
      (CharacterDifferential.differential
        (E := EuclideanSpace ℝ (Fin d.groupDimension)) χ.toMonoidHom) := by
  unfold differential
  rw [actionMap_eq_scalarOperator d e χ haction]
  change mfderiv (𝓡 d.groupDimension) 𝓘(ℝ, d.Carrier →L[ℝ] d.Carrier)
    ((scalarOperator d e) ∘ (fun g => (χ.toMonoidHom g : ℂ))) (1 : d.Changes) = _
  rw [mfderiv_comp (1 : d.Changes) (scalarOperator d e).mdifferentiableAt
      (CharacterDifferential.character_mdifferentiable
        (E := EuclideanSpace ℝ (Fin d.groupDimension)) χ.toMonoidHom hχ _),
    (scalarOperator d e).mfderiv_eq]
  rfl

/-- The scalar multiple is obtained from the actual character differential. -/
theorem endomorphism_eq_smul_generator (hχ : Continuous χ)
    (haction : ∀ g v, e (d.action g v) = (χ g : ℂ) * e v)
    (X : GroupLieAlgebra (𝓡 d.groupDimension) d.Changes) :
    endomorphism d X = phaseDifferential d χ X • PlaneGenerator.generator e := by
  unfold endomorphism
  rw [differential_eq_scalarOperator d e χ hχ haction]
  apply LinearMap.ext
  intro v
  change scalarOperator d e
    (CharacterDifferential.differential
      (E := EuclideanSpace ℝ (Fin d.groupDimension)) χ.toMonoidHom X) v = _
  rw [scalarOperator_apply,
    CharacterDifferential.differential_re_eq_zero χ.toMonoidHom hχ X]
  simp [phaseDifferential]

theorem phaseDifferential_injective (hχ : Continuous χ) :
    Function.Injective (phaseDifferential d χ) :=
  CharacterDifferential.imaginary_differential_injective
    (E := EuclideanSpace ℝ (Fin d.groupDimension)) χ.toMonoidHom hχ χ.injective

theorem phaseDifferential_surjective (h : MinimalCarrier.IsMinimal d)
    (hχ : Continuous χ) : Function.Surjective (phaseDifferential d χ) := by
  let : FiniteDimensional ℝ (GroupLieAlgebra (𝓡 d.groupDimension) d.Changes) :=
    (tangentSpaceCastModel (𝓡 d.groupDimension) (1 : d.Changes)).symm.toLinearEquiv.finiteDimensional
  have hdim : Module.finrank ℝ (GroupLieAlgebra (𝓡 d.groupDimension) d.Changes) =
      Module.finrank ℝ ℝ := by
    rw [Module.finrank_self]
    exact (tangentSpaceCastModel (𝓡 d.groupDimension) (1 : d.Changes)).toLinearEquiv.finrank_eq.trans
      (finrank_euclideanSpace_fin.trans (CharacterDifferential.minimalCarrier_groupDimension_eq_one d h))
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
    (phaseDifferential_injective d χ hχ)

/-- The trace form agrees with the product of the actual phase differentials.
The denominator two is obtained from the real carrier's proved dimension. -/
theorem traceMetric_eq_phase (hχ : Continuous χ)
    (haction : ∀ g v, e (d.action g v) = (χ g : ℂ) * e v)
    (X Y : GroupLieAlgebra (𝓡 d.groupDimension) d.Changes) :
    traceMetric d X Y = phaseDifferential d χ X * phaseDifferential d χ Y := by
  unfold traceMetric
  rw [endomorphism_eq_smul_generator d e χ hχ haction X,
    endomorphism_eq_smul_generator d e χ hχ haction Y,
    PlaneGenerator.coordinate_finrank e]
  exact PlaneGenerator.tracePair_smul_generator e _ _

theorem traceMetric_symmetric (hχ : Continuous χ)
    (haction : ∀ g v, e (d.action g v) = (χ g : ℂ) * e v)
    (X Y : GroupLieAlgebra (𝓡 d.groupDimension) d.Changes) :
    traceMetric d X Y = traceMetric d Y X := by
  rw [traceMetric_eq_phase d e χ hχ haction, traceMetric_eq_phase d e χ hχ haction]
  exact mul_comm _ _

theorem traceMetric_positive (hχ : Continuous χ)
    (haction : ∀ g v, e (d.action g v) = (χ g : ℂ) * e v)
    (X : GroupLieAlgebra (𝓡 d.groupDimension) d.Changes) (hX : X ≠ 0) :
    0 < traceMetric d X X := by
  rw [traceMetric_eq_phase d e χ hχ haction]
  apply mul_self_pos.mpr
  intro hz
  apply hX
  apply phaseDifferential_injective d χ hχ
  simpa using hz

/-- Injectivity refers to the actual derivative of the original action. -/
theorem differential_injective (hχ : Continuous χ)
    (haction : ∀ g v, e (d.action g v) = (χ g : ℂ) * e v) :
    Function.Injective (differential d) := by
  intro X Y hXY
  by_contra hne
  have hz : endomorphism d (X - Y) = 0 := by
    unfold endomorphism
    rw [map_sub, hXY, sub_self]
    rfl
  have hp := traceMetric_positive d e χ hχ haction (X - Y) (sub_ne_zero.mpr hne)
  simp [traceMetric, hz] at hp

/-- The unit sphere is defined by the representation trace form, not by the
default norm on the model space of the original charts. -/
theorem two_unit_generators (h : MinimalCarrier.IsMinimal d) (hχ : Continuous χ)
    (haction : ∀ g v, e (d.action g v) = (χ g : ℂ) * e v) :
    ∃ Xplus : GroupLieAlgebra (𝓡 d.groupDimension) d.Changes,
      phaseDifferential d χ Xplus = 1 ∧ Xplus ≠ -Xplus ∧
      endomorphism d Xplus = PlaneGenerator.generator e ∧
      endomorphism d (-Xplus) = -PlaneGenerator.generator e ∧
      ∀ X, traceMetric d X X = 1 ↔ X = Xplus ∨ X = -Xplus := by
  obtain ⟨Xplus, hplus⟩ := phaseDifferential_surjective d χ h hχ 1
  have hdistinct : Xplus ≠ -Xplus := by
    intro heq
    have ht := congrArg (phaseDifferential d χ) heq
    rw [map_neg, hplus] at ht
    norm_num at ht
  refine ⟨Xplus, hplus, hdistinct, ?_, ?_, ?_⟩
  · rw [endomorphism_eq_smul_generator d e χ hχ haction, hplus, one_smul]
  · rw [endomorphism_eq_smul_generator d e χ hχ haction, map_neg, hplus, neg_one_smul]
  · intro X
    rw [traceMetric_eq_phase d e χ hχ haction]
    constructor
    · intro hunit
      have hs : phaseDifferential d χ X = 1 ∨ phaseDifferential d χ X = -1 := by
        apply (sq_eq_sq_iff_eq_or_eq_neg).mp
        nlinarith
      rcases hs with hs | hs
      · left
        exact phaseDifferential_injective d χ hχ (hs.trans hplus.symm)
      · right
        apply phaseDifferential_injective d χ hχ
        rw [map_neg, hplus]
        exact hs
    · rintro (rfl | rfl) <;> simp [hplus]

theorem unit_endomorphism_eq (h : MinimalCarrier.IsMinimal d) (hχ : Continuous χ)
    (haction : ∀ g v, e (d.action g v) = (χ g : ℂ) * e v)
    (X : GroupLieAlgebra (𝓡 d.groupDimension) d.Changes)
    (hunit : traceMetric d X X = 1) :
    endomorphism d X = PlaneGenerator.generator e ∨
      endomorphism d X = -PlaneGenerator.generator e := by
  obtain ⟨Xplus, _, _, hpos, hneg, hclass⟩ := two_unit_generators d e χ h hχ haction
  rcases (hclass X).mp hunit with rfl | rfl
  · exact Or.inl hpos
  · exact Or.inr hneg

/-- The actual images of trace-unit Lie vectors are skew, square to minus
the identity, and preserve the original real norm. -/
theorem unit_endomorphism_properties (h : MinimalCarrier.IsMinimal d) (hχ : Continuous χ)
    (haction : ∀ g v, e (d.action g v) = (χ g : ℂ) * e v)
    (X : GroupLieAlgebra (𝓡 d.groupDimension) d.Changes)
    (hunit : traceMetric d X X = 1) :
    PlaneGenerator.IsSkew (endomorphism d X) ∧
      endomorphism d X * endomorphism d X = -1 ∧
      ∀ v, ‖endomorphism d X v‖ = ‖v‖ := by
  rcases unit_endomorphism_eq d e χ h hχ haction X hunit with hp | hn
  · rw [hp]
    exact ⟨PlaneGenerator.generator_skew e, PlaneGenerator.generator_square e,
      PlaneGenerator.generator_isometry e⟩
  · rw [hn]
    refine ⟨?_, ?_, ?_⟩
    · intro v w
      simpa only [LinearMap.neg_apply, inner_neg_left, inner_neg_right, neg_neg] using
        congrArg Neg.neg (PlaneGenerator.generator_skew e v w)
    · simpa only [neg_mul_neg] using PlaneGenerator.generator_square e
    · intro v
      simpa using PlaneGenerator.generator_isometry e v

/-- The final assertion starts with the unmodified minimal datum. The
coordinate, character, trace positivity, and two unit generators are outputs. -/
theorem minimalCarrier_trace_generators (h : MinimalCarrier.IsMinimal d) :
    ∃ (e : d.Carrier ≃ₗᵢ[ℝ] ℂ) (χ : d.Changes ≃* Circle),
      Continuous χ ∧
      (∀ g v, e (d.action g v) = (χ g : ℂ) * e v) ∧
      ContMDiff (𝓡 d.groupDimension) 𝓘(ℝ, d.Carrier →L[ℝ] d.Carrier) ∞ (actionMap d) ∧
      (∀ X, X ≠ 0 → 0 < traceMetric d X X) ∧
      ∃ Xplus : GroupLieAlgebra (𝓡 d.groupDimension) d.Changes,
        Xplus ≠ -Xplus ∧ endomorphism d Xplus = PlaneGenerator.generator e ∧
        endomorphism d (-Xplus) = -PlaneGenerator.generator e ∧
        ∀ X, traceMetric d X X = 1 ↔ X = Xplus ∨ X = -Xplus := by
  obtain ⟨_, e, χ, hχ, _, haction⟩ := MinimalCarrier.minimalCarrier_classification d h
  obtain ⟨Xplus, _, hdistinct, hpos, hneg, hclass⟩ := two_unit_generators d e χ h hχ haction
  exact ⟨e, χ, hχ, haction, actionMap_contMDiff d e χ hχ haction,
    traceMetric_positive d e χ hχ haction, Xplus, hdistinct, hpos, hneg, hclass⟩

end GeneratedFoundations.Source.RepresentationDifferential

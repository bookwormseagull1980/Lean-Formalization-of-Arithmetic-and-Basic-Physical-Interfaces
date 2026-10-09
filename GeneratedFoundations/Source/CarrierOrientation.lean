module

public import GeneratedFoundations.Source.TraceLieGeometry
public import Mathlib.Analysis.InnerProductSpace.TwoDim

/-!
# Carrier orientations and the original unit Lie generators

An orientation of the minimal real carrier determines its positive quarter-turn
using the original inner product. The differential of the original group action
has a unique trace-unit preimage of this operator. Consequently carrier
orientations correspond bijectively to the unit vectors of the representation
trace metric. Coordinates and characters are used to prove existence, but are
not parameters of the resulting correspondence.

The sign is characterized geometrically by the oriented area of a vector and
its infinitesimal change. Reversing the carrier orientation reverses the Lie
vector and conjugates the induced scalar and Hermitian structures.
-/

@[expose] public section

noncomputable section

open Module Function
open scoped Manifold RealInnerProductSpace ComplexConjugate

namespace GeneratedFoundations.Source.CarrierOrientation

open TraceLieGeometry RepresentationDifferential

variable (d : MinimalCarrier.OrthogonalChangeDatum) (h : MinimalCarrier.IsMinimal d)

abbrev OrientationOnCarrier := Orientation ℝ d.Carrier (Fin 2)

/-- The positive quarter-turn determined by the original carrier orientation. -/
def carrierQuarterTurn (o : OrientationOnCarrier d) : Module.End ℝ d.Carrier := by
  letI : Fact (finrank ℝ d.Carrier = 2) :=
    ⟨(MinimalCarrier.minimal_iff_dimension_two d).mp h⟩
  exact o.rightAngleRotation.toLinearEquiv.toLinearMap

def carrierAreaForm (o : OrientationOnCarrier d) : d.Carrier →ₗ[ℝ] d.Carrier →ₗ[ℝ] ℝ := by
  letI : Fact (finrank ℝ d.Carrier = 2) :=
    ⟨(MinimalCarrier.minimal_iff_dimension_two d).mp h⟩
  exact o.areaForm

def coordinateOrientation (e : d.Carrier ≃ₗᵢ[ℝ] ℂ) : OrientationOnCarrier d :=
  (Orientation.map (Fin 2) e.toLinearEquiv).symm Complex.orientation

theorem coordinateOrientation_map (e : d.Carrier ≃ₗᵢ[ℝ] ℂ) :
    Orientation.map (Fin 2) e.toLinearEquiv (coordinateOrientation d e) =
      Complex.orientation :=
  (Orientation.map (Fin 2) e.toLinearEquiv).apply_symm_apply _

theorem carrierQuarterTurn_coordinate (e : d.Carrier ≃ₗᵢ[ℝ] ℂ) :
    carrierQuarterTurn d h (coordinateOrientation d e) = PlaneGenerator.generator e := by
  let : Fact (finrank ℝ d.Carrier = 2) :=
    ⟨(MinimalCarrier.minimal_iff_dimension_two d).mp h⟩
  ext v
  apply e.injective
  change e ((coordinateOrientation d e).rightAngleRotation v) =
    e (PlaneGenerator.generator e v)
  exact ((coordinateOrientation d e).rightAngleRotation_map_complex e
    (coordinateOrientation_map d e) v).trans (PlaneGenerator.generator_coordinate e v).symm

theorem carrierQuarterTurn_reverse (o : OrientationOnCarrier d) :
    carrierQuarterTurn d h (-o) = -carrierQuarterTurn d h o := by
  let : Fact (finrank ℝ d.Carrier = 2) :=
    ⟨(MinimalCarrier.minimal_iff_dimension_two d).mp h⟩
  ext v
  exact o.rightAngleRotation_neg_orientation v

theorem carrierQuarterTurn_square (o : OrientationOnCarrier d) :
    carrierQuarterTurn d h o * carrierQuarterTurn d h o = -1 := by
  let : Fact (finrank ℝ d.Carrier = 2) :=
    ⟨(MinimalCarrier.minimal_iff_dimension_two d).mp h⟩
  ext v
  exact o.rightAngleRotation_rightAngleRotation v

theorem carrierAreaForm_quarterTurn (o : OrientationOnCarrier d) (v : d.Carrier) :
    carrierAreaForm d h o v (carrierQuarterTurn d h o v) = ‖v‖ ^ 2 := by
  let : Fact (finrank ℝ d.Carrier = 2) :=
    ⟨(MinimalCarrier.minimal_iff_dimension_two d).mp h⟩
  exact (o.areaForm_rightAngleRotation_right v v).trans (real_inner_self_eq_norm_sq v)

theorem carrierQuarterTurn_ne_neg (o : OrientationOnCarrier d) :
    carrierQuarterTurn d h o ≠ -carrierQuarterTurn d h o := by
  intro heq
  obtain ⟨v, hv⟩ := exists_ne (0 : d.Carrier)
  have harea := congrArg
    (fun T : Module.End ℝ d.Carrier => carrierAreaForm d h o v (T v)) heq
  simp only [LinearMap.neg_apply, map_neg, carrierAreaForm_quarterTurn] at harea
  have hpos := sq_pos_of_pos (norm_pos_iff.mpr hv)
  linarith

include h in
theorem carrier_orientation_cases (o p : OrientationOnCarrier d) : o = p ∨ o = -p :=
  o.eq_or_eq_neg p (by
    rw [Fintype.card_fin, (MinimalCarrier.minimal_iff_dimension_two d).mp h])

theorem carrierQuarterTurn_injective : Function.Injective (carrierQuarterTurn d h) := by
  intro o p heq
  rcases carrier_orientation_cases d h o p with hop | hop
  · exact hop
  · rw [hop, carrierQuarterTurn_reverse] at heq
    exact False.elim (carrierQuarterTurn_ne_neg d h p heq.symm)

theorem tangentEndomorphism_neg (X : TraceLieSpace d h) :
    endomorphism d (-X).tangent = -endomorphism d X.tangent := by
  change (differential d (-X.tangent)).toLinearMap = -(differential d X.tangent).toLinearMap
  rw [map_neg]
  rfl

/-- Injectivity here is that of the original manifold derivative, transported
only through the trace-norm wrapper. -/
theorem tangentEndomorphism_injective :
    Function.Injective (fun X : TraceLieSpace d h => endomorphism d X.tangent) := by
  obtain ⟨_, e, χ, hχ, _, haction⟩ := MinimalCarrier.minimalCarrier_classification d h
  intro X Y hXY
  apply (underlyingLinearEquiv d h).injective
  apply differential_injective d e χ hχ haction
  apply ContinuousLinearMap.ext
  intro v
  exact congrArg (fun T : Module.End ℝ d.Carrier => T v) hXY

/-- The carrier orientation selects exactly one unit vector in the Lie algebra
of the original group, using the actual representation differential. -/
theorem carrierUnit_existsUnique (o : OrientationOnCarrier d) :
    ∃! X : TraceLieSpace d h, ‖X‖ = 1 ∧
      endomorphism d X.tangent = carrierQuarterTurn d h o := by
  suffices hex : ∃ X : TraceLieSpace d h, ‖X‖ = 1 ∧
      endomorphism d X.tangent = carrierQuarterTurn d h o by
    obtain ⟨X, hX⟩ := hex
    refine ⟨X, hX, ?_⟩
    intro Y hY
    exact tangentEndomorphism_injective d h (hY.2.trans hX.2.symm)
  obtain ⟨_, e, χ, hχ, _, haction⟩ := MinimalCarrier.minimalCarrier_classification d h
  rcases carrier_orientation_cases d h o (coordinateOrientation d e) with ho | ho
  · refine ⟨positiveUnit d h χ hχ, positiveUnit_norm d h e χ hχ haction, ?_⟩
    rw [positiveUnit_image d h e χ hχ haction, ho, carrierQuarterTurn_coordinate]
  · refine ⟨-positiveUnit d h χ hχ, ?_, ?_⟩
    · rw [norm_neg, positiveUnit_norm d h e χ hχ haction]
    · rw [tangentEndomorphism_neg, positiveUnit_image d h e χ hχ haction, ho,
        carrierQuarterTurn_reverse, carrierQuarterTurn_coordinate]

def carrierUnit (o : OrientationOnCarrier d) : TraceLieSpace d h :=
  Classical.choose (carrierUnit_existsUnique d h o)

theorem carrierUnit_norm (o : OrientationOnCarrier d) : ‖carrierUnit d h o‖ = 1 :=
  (Classical.choose_spec (carrierUnit_existsUnique d h o)).1.1

theorem carrierUnit_image (o : OrientationOnCarrier d) :
    endomorphism d (carrierUnit d h o).tangent = carrierQuarterTurn d h o :=
  (Classical.choose_spec (carrierUnit_existsUnique d h o)).1.2

theorem carrierUnit_coordinate (e : d.Carrier ≃ₗᵢ[ℝ] ℂ) (χ : d.Changes ≃* Circle)
    (hχ : Continuous χ) (haction : ∀ g v, e (d.action g v) = (χ g : ℂ) * e v) :
    carrierUnit d h (coordinateOrientation d e) = positiveUnit d h χ hχ := by
  apply tangentEndomorphism_injective d h
  dsimp only
  rw [carrierUnit_image, carrierQuarterTurn_coordinate, positiveUnit_image d h e χ hχ haction]

theorem carrierUnit_reverse (o : OrientationOnCarrier d) :
    carrierUnit d h (-o) = -carrierUnit d h o := by
  apply tangentEndomorphism_injective d h
  dsimp only
  rw [carrierUnit_image, tangentEndomorphism_neg, carrierUnit_image, carrierQuarterTurn_reverse]

theorem carrierUnit_injective : Function.Injective (carrierUnit d h) := by
  intro o p hop
  apply carrierQuarterTurn_injective d h
  rw [← carrierUnit_image, ← carrierUnit_image, hop]

theorem unit_carrierOrientation_existsUnique (X : TraceLieSpace d h) (hX : ‖X‖ = 1) :
    ∃! o : OrientationOnCarrier d, carrierUnit d h o = X := by
  obtain ⟨_, e, χ, hχ, _, haction⟩ := MinimalCarrier.minimalCarrier_classification d h
  rcases (norm_one_iff d h e χ hχ haction X).mp hX with hpos | hneg
  · refine ⟨coordinateOrientation d e, ?_, ?_⟩
    · exact (carrierUnit_coordinate d h e χ hχ haction).trans hpos.symm
    · intro p hp
      apply carrierUnit_injective d h
      exact hp.trans (hpos.trans (carrierUnit_coordinate d h e χ hχ haction).symm)
  · refine ⟨-coordinateOrientation d e, ?_, ?_⟩
    · dsimp only
      rw [carrierUnit_reverse, carrierUnit_coordinate d h e χ hχ haction]
      exact hneg.symm
    · intro p hp
      apply carrierUnit_injective d h
      rw [carrierUnit_reverse, carrierUnit_coordinate d h e χ hχ haction]
      exact hp.trans hneg

/-- The two actual carrier orientations and the trace-unit sphere correspond
without a choice of complex coordinate or character in the definition. -/
def carrierUnitEquiv : OrientationOnCarrier d ≃ {X : TraceLieSpace d h // ‖X‖ = 1} :=
  Equiv.ofBijective (fun o => ⟨carrierUnit d h o, carrierUnit_norm d h o⟩) (by
    constructor
    · intro o p hop
      exact carrierUnit_injective d h (congrArg Subtype.val hop)
    · intro X
      obtain ⟨o, ho, _⟩ := unit_carrierOrientation_existsUnique d h X.val X.property
      exact ⟨o, Subtype.ext ho⟩)

theorem unit_eq_or_neg_carrierUnit (o : OrientationOnCarrier d)
    (X : TraceLieSpace d h) (hX : ‖X‖ = 1) :
    X = carrierUnit d h o ∨ X = -carrierUnit d h o := by
  obtain ⟨p, hp, _⟩ := unit_carrierOrientation_existsUnique d h X hX
  rcases carrier_orientation_cases d h p o with hpos | hneg
  · left
    simpa only [hpos] using hp.symm
  · right
    simpa only [hneg, carrierUnit_reverse] using hp.symm

/-- A nonzero carrier vector detects the positive infinitesimal direction by
its oriented area with its image under the original action differential. -/
theorem carrierUnit_iff_area_pos (o : OrientationOnCarrier d)
    (X : TraceLieSpace d h) (hX : ‖X‖ = 1) (v : d.Carrier) (hv : v ≠ 0) :
    X = carrierUnit d h o ↔ 0 < carrierAreaForm d h o v (endomorphism d X.tangent v) := by
  constructor
  · rintro rfl
    rw [carrierUnit_image, carrierAreaForm_quarterTurn]
    exact sq_pos_of_pos (norm_pos_iff.mpr hv)
  · intro hpos
    rcases unit_eq_or_neg_carrierUnit d h o X hX with heq | heq
    · exact heq
    · rw [heq, tangentEndomorphism_neg, carrierUnit_image, LinearMap.neg_apply,
        map_neg, carrierAreaForm_quarterTurn] at hpos
      exact False.elim ((not_lt_of_ge (neg_nonpos.mpr (sq_nonneg ‖v‖))) hpos)

/-- The existing Lie-line orientation is determined by the same actual
representation relation as the carrier orientation. -/
theorem carrier_lieOrientation_existsUnique (e : d.Carrier ≃ₗᵢ[ℝ] ℂ)
    (χ : d.Changes ≃* Circle) (hχ : Continuous χ)
    (haction : ∀ g v, e (d.action g v) = (χ g : ℂ) * e v) (o : OrientationOnCarrier d) :
    ∃! p : Orientation ℝ (TraceLieSpace d h) (Fin 1),
      endomorphism d (orientedUnit d h χ hχ p).tangent = carrierQuarterTurn d h o := by
  obtain ⟨p, hp, hunique⟩ := unit_orientation_existsUnique d h e χ hχ haction
    (carrierUnit d h o) (carrierUnit_norm d h o)
  refine ⟨p, ?_, ?_⟩
  · dsimp only
    rw [hp, carrierUnit_image]
  · intro q hq
    apply hunique q
    apply tangentEndomorphism_injective d h
    exact hq.trans (carrierUnit_image d h o).symm

theorem carrier_lieOrientation_reverse (χ : d.Changes ≃* Circle) (hχ : Continuous χ)
    (o : OrientationOnCarrier d) (p : Orientation ℝ (TraceLieSpace d h) (Fin 1))
    (hcompat : endomorphism d (orientedUnit d h χ hχ p).tangent =
      carrierQuarterTurn d h o) :
    endomorphism d (orientedUnit d h χ hχ (-p)).tangent = carrierQuarterTurn d h (-o) := by
  rw [orientedUnit_reverse, tangentEndomorphism_neg, hcompat, carrierQuarterTurn_reverse]

theorem carrier_complexScalarAction_existsUnique (o : OrientationOnCarrier d) :
    ∃! F : ℂ →ₐ[ℝ] Module.End ℝ d.Carrier, F Complex.I = carrierQuarterTurn d h o :=
  PlaneGenerator.complexScalarAction_existsUnique (carrierQuarterTurn d h o)
    (carrierQuarterTurn_square d h o)

theorem carrier_complexScalarAction_reverse (o : OrientationOnCarrier d) (z : ℂ) :
    PlaneGenerator.complexScalarAction (carrierQuarterTurn d h (-o))
        (carrierQuarterTurn_square d h (-o)) z =
      PlaneGenerator.complexScalarAction (carrierQuarterTurn d h o)
        (carrierQuarterTurn_square d h o) (conj z) := by
  simpa only [carrierQuarterTurn_reverse] using
    PlaneGenerator.complexScalarAction_neg (carrierQuarterTurn d h o)
      (carrierQuarterTurn_square d h o) z

theorem carrier_sourceHermitian_reverse (o : OrientationOnCarrier d) (v w : d.Carrier) :
    ComplexStructure.sourceHermitian (carrierQuarterTurn d h (-o)) v w =
      conj (ComplexStructure.sourceHermitian (carrierQuarterTurn d h o) v w) := by
  rw [carrierQuarterTurn_reverse, ComplexStructure.sourceHermitian_neg]

end GeneratedFoundations.Source.CarrierOrientation

module

public import GeneratedFoundations.Arithmetic.TypedSourceModes
public import GeneratedFoundations.Spectral.NegativeOrientedLift

/-!
# Scalar observations of typed source modes

The scalar observation of a typed endomorphism is evaluated on its actual
source carrier. The normalized spectral coordinate identifies this function
with the continuous representative of the positive Neumann lift. Pulling the
oppositely oriented observation back along the source reversal identifies it
with the continuous representative of the negative lift of the same original
interval vector.

The almost-everywhere comparison uses the measure-preserving reflection of
the spectral circle. Pointwise identities concern the continuous observation
functions; no pointwise choice of an arbitrary L2 representative is asserted.
Both directions preserve the original normalized, endpoint-positive source
representative. Negative powers are not given an untyped composition law.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Topology ComplexConjugate
open GeneratedFoundations.Source GeneratedFoundations.Spectral
open GeneratedFoundations.Source.CarrierOrientation
open GeneratedFoundations.Source.GeneratedSpectralCircle

namespace GeneratedFoundations.Arithmetic.TypedModeObservations

open TypedSourceModes

variable (L : ℝ) [hL : Fact (0 < L)]

/-- Reflection transports an existing positive representative without changing
the original interval vector or imposing an index on its circle map. -/
theorem negativeLift_of_positiveRepresentative (f : ComplexIntervalL2 0 L)
    (u : Circle →ₜ* Circle)
    (hf : OrientedLift.lift L f =ᵐ[AddCircle.haarAddCircle]
      OrientedLift.endomorphismRepresentative L u) :
    NegativeOrientedLift.lift L f =ᵐ[AddCircle.haarAddCircle]
      NegativeOrientedLift.reversedRepresentative L u := by
  rw [NegativeOrientedLift.lift_reflection]
  have hneg : (fun z : AddCircle (2 * L) => OrientedLift.lift L f (-z))
      =ᵐ[AddCircle.haarAddCircle]
        fun z => OrientedLift.endomorphismRepresentative L u (-z) :=
    (Measure.measurePreserving_neg AddCircle.haarAddCircle).quasiMeasurePreserving.ae_eq_comp hf
  exact (haarCircleReflection_coe L (OrientedLift.lift L f)).trans hneg

variable (d : MinimalCarrier.OrthogonalChangeDatum) (h : MinimalCarrier.IsMinimal d)

/-- The normalized spectral point belongs to the actual typed source carrier. -/
def spectralPoint (o : OrientationOnCarrier d) :
    C(AddCircle (2 * L), Carrier d h o) where
  toFun z := (coordinate d h o).symm (AddCircle.toCircle z)
  continuous_toFun := (coordinate d h o).symm.continuous.comp AddCircle.continuous_toCircle

omit hL in
@[simp] theorem coordinate_spectralPoint (o : OrientationOnCarrier d)
    (z : AddCircle (2 * L)) :
    coordinate d h o (spectralPoint L d h o z) = AddCircle.toCircle z :=
  (coordinate d h o).apply_symm_apply _

/-- The spectral parametrization is inverse to the already derived coordinate
on the original change group. -/
theorem spectralPoint_sourceCoordinate (o : OrientationOnCarrier d) (g : d.Changes) :
    spectralPoint L d h o (spectralCoordinate d h L o g) = (forget d h o).symm g := by
  apply (coordinate d h o).injective
  rw [coordinate_spectralPoint, spectralCoordinate_phase]
  rfl

theorem spectralPoint_flow (o : OrientationOnCarrier d) (t : ℝ) :
    spectralPoint L d h o ((L / Real.pi * t : ℝ) : AddCircle (2 * L)) =
      typedFlow d h o t := by
  apply (coordinate d h o).injective
  rw [coordinate_spectralPoint, coordinate_typedFlow, covering_coordinate_phase]

omit hL in
/-- The source reversal and the actual spectral reflection commute. -/
theorem spectralPoint_reversal (o : OrientationOnCarrier d) (z : AddCircle (2 * L)) :
    spectralPoint L d h (-o) (-z) = reversal d h o (spectralPoint L d h o z) := by
  apply (coordinate d h (-o)).injective
  rw [coordinate_spectralPoint, coordinate_reversal, coordinate_spectralPoint,
    AddCircle.toCircle_neg]

/-- Scalar readout after applying an actual typed source endomorphism. -/
def scalarObservation (o : OrientationOnCarrier d) (u : Mode d h L o) :
    C(Carrier d h o, ℂ) where
  toFun x := (coordinate d h o (u x) : ℂ)
  continuous_toFun := continuous_subtype_val.comp
    ((coordinate d h o).continuous.comp u.val.continuous)

theorem scalarObservation_coordinate (o : OrientationOnCarrier d) (u : Mode d h L o)
    (x : Carrier d h o) :
    scalarObservation L d h o u x =
      ((toGenerated d h L o u).val (coordinate d h o x) : ℂ) := by
  change (coordinate d h o (u x) : ℂ) =
    (coordinate d h o (u ((coordinate d h o).symm (coordinate d h o x))) : ℂ)
  rw [ContinuousMulEquiv.symm_apply_apply]

theorem scalarObservation_flow (o : OrientationOnCarrier d) (u : Mode d h L o) (t : ℝ) :
    scalarObservation L d h o u (typedFlow d h o t) =
      ((toGenerated d h L o u).val (Circle.exp t) : ℂ) := by
  rw [scalarObservation_coordinate, coordinate_typedFlow]

/-- The scalar observation on the normalized spectral circle. -/
def positiveObservation (o : OrientationOnCarrier d) (u : Mode d h L o) :
    C(AddCircle (2 * L), ℂ) :=
  (scalarObservation L d h o u).comp (spectralPoint L d h o)

/-- The target observation pulled back along the typed source reversal. -/
def reversedObservation (o : OrientationOnCarrier d) (u : Mode d h L o) :
    C(AddCircle (2 * L), ℂ) where
  toFun z := scalarObservation L d h (-o) (reverseMode d h L o u)
    (reversal d h o (spectralPoint L d h o z))
  continuous_toFun := (scalarObservation L d h (-o) (reverseMode d h L o u)).continuous.comp
    ((reversal d h o).continuous.comp (spectralPoint L d h o).continuous)

theorem positiveObservation_eq (o : OrientationOnCarrier d) (u : Mode d h L o) :
    positiveObservation L d h o u =
      OrientedLift.endomorphismRepresentative L (toGenerated d h L o u).val := by
  ext z
  rfl

/-- This equality concerns the actual pulled-back function, before any
almost-everywhere identification of its Hilbert-space representative. -/
theorem reversedObservation_eq (o : OrientationOnCarrier d) (u : Mode d h L o) :
    reversedObservation L d h o u =
      NegativeOrientedLift.reversedRepresentative L (toGenerated d h L o u).val := by
  ext z
  change scalarObservation L d h (-o) (reverseMode d h L o u)
    (reversal d h o (spectralPoint L d h o z)) = _
  rw [← spectralPoint_reversal]
  change positiveObservation L d h (-o) (reverseMode d h L o u) (-z) =
    OrientedLift.endomorphismRepresentative L (toGenerated d h L o u).val (-z)
  rw [positiveObservation_eq, toGenerated_reverseMode]

theorem reversedObservation_reflection (o : OrientationOnCarrier d)
    (u : Mode d h L o) (z : AddCircle (2 * L)) :
    reversedObservation L d h o u z = positiveObservation L d h o u (-z) := by
  rw [reversedObservation_eq, positiveObservation_eq]
  rfl

theorem reversedObservation_conj (o : OrientationOnCarrier d)
    (u : Mode d h L o) (z : AddCircle (2 * L)) :
    reversedObservation L d h o u z = conj (positiveObservation L d h o u z) := by
  change (coordinate d h (-o)
    (reverseMode d h L o u (reversal d h o (spectralPoint L d h o z))) : ℂ) =
      conj (coordinate d h o (u (spectralPoint L d h o z)) : ℂ)
  rw [reverseMode_observation_pullback, Circle.coe_inv_eq_conj]

/-- This is the existing canonical vector of the original Neumann operator. -/
abbrev sourceRepresentative (o : OrientationOnCarrier d) (u : Mode d h L o) :
    (complexNeumannOperator hL.out).domain :=
  GeneratedModes.representative L (toGenerated d h L o u)

theorem sourceRepresentative_reverse (o : OrientationOnCarrier d) (u : Mode d h L o) :
    sourceRepresentative L d h (-o) (reverseMode d h L o u) =
      sourceRepresentative L d h o u :=
  representative_reversal d h L o u

theorem sourceRepresentative_unreverse (o : OrientationOnCarrier d)
    (u : Mode d h L (-o)) :
    sourceRepresentative L d h o (unreverseMode d h L o u) =
      sourceRepresentative L d h (-o) u := by
  unfold sourceRepresentative
  rw [toGenerated_unreverseMode]

theorem sourceRepresentative_positive_lift (o : OrientationOnCarrier d)
    (u : Mode d h L o) :
    OrientedLift.lift L (sourceRepresentative L d h o u : ComplexIntervalL2 0 L)
      =ᵐ[AddCircle.haarAddCircle] positiveObservation L d h o u := by
  rw [positiveObservation_eq]
  exact GeneratedModes.representative_lifts L (toGenerated d h L o u)

/-- The opposite observation is the negative lift of the same original source,
with no replacement of its eigenvector, endpoint normalization or phase. -/
theorem sourceRepresentative_negative_lift (o : OrientationOnCarrier d)
    (u : Mode d h L o) :
    NegativeOrientedLift.lift L (sourceRepresentative L d h o u : ComplexIntervalL2 0 L)
      =ᵐ[AddCircle.haarAddCircle] reversedObservation L d h o u := by
  rw [reversedObservation_eq]
  exact negativeLift_of_positiveRepresentative L _ _
    (GeneratedModes.representative_lifts L (toGenerated d h L o u))

/-- On its own oriented coordinate, the reversed source mode still has its
positive representative, and the interval source is identical. -/
theorem sourceRepresentative_reversed_positive_lift (o : OrientationOnCarrier d)
    (u : Mode d h L o) :
    OrientedLift.lift L (sourceRepresentative L d h o u : ComplexIntervalL2 0 L)
      =ᵐ[AddCircle.haarAddCircle]
        positiveObservation L d h (-o) (reverseMode d h L o u) := by
  have hrep := sourceRepresentative_positive_lift L d h (-o) (reverseMode d h L o u)
  rw [sourceRepresentative_reverse] at hrep
  exact hrep

theorem positiveObservation_unique (o : OrientationOnCarrier d) (u : Mode d h L o)
    (g : C(AddCircle (2 * L), ℂ))
    (hg : OrientedLift.lift L (sourceRepresentative L d h o u : ComplexIntervalL2 0 L)
      =ᵐ[AddCircle.haarAddCircle] g) : g = positiveObservation L d h o u := by
  apply ContinuousMap.coe_injective
  exact MeasureTheory.Measure.eq_of_ae_eq
    (hg.symm.trans (sourceRepresentative_positive_lift L d h o u))
    g.continuous (positiveObservation L d h o u).continuous

theorem reversedObservation_unique (o : OrientationOnCarrier d) (u : Mode d h L o)
    (g : C(AddCircle (2 * L), ℂ))
    (hg : NegativeOrientedLift.lift L (sourceRepresentative L d h o u : ComplexIntervalL2 0 L)
      =ᵐ[AddCircle.haarAddCircle] g) : g = reversedObservation L d h o u := by
  apply ContinuousMap.coe_injective
  exact MeasureTheory.Measure.eq_of_ae_eq
    (hg.symm.trans (sourceRepresentative_negative_lift L d h o u))
    g.continuous (reversedObservation L d h o u).continuous

/-- The inverse typed comparison also acts on actual scalar observations. -/
theorem unreverse_scalarObservation (o : OrientationOnCarrier d)
    (u : Mode d h L (-o)) (x : Carrier d h (-o)) :
    scalarObservation L d h o (unreverseMode d h L o u) ((reversal d h o).symm x) =
      conj (scalarObservation L d h (-o) u x) := by
  have heq := reverseMode_observation_pullback d h L o (unreverseMode d h L o u)
    ((reversal d h o).symm x)
  have hcancel : reverseMode d h L o (unreverseMode d h L o u) = u :=
    (reversalEquiv d h L o).apply_symm_apply u
  rw [hcancel, ContinuousMulEquiv.apply_symm_apply] at heq
  have hinv := congrArg (fun z : Circle => z⁻¹) heq
  rw [inv_inv] at hinv
  change (coordinate d h o (unreverseMode d h L o u ((reversal d h o).symm x)) : ℂ) =
    conj (coordinate d h (-o) (u x) : ℂ)
  rw [← hinv, Circle.coe_inv_eq_conj]

def backwardObservation (o : OrientationOnCarrier d) (u : Mode d h L (-o)) :
    C(AddCircle (2 * L), ℂ) where
  toFun z := scalarObservation L d h o (unreverseMode d h L o u)
    ((reversal d h o).symm (spectralPoint L d h (-o) z))
  continuous_toFun := (scalarObservation L d h o (unreverseMode d h L o u)).continuous.comp
    ((reversal d h o).symm.continuous.comp (spectralPoint L d h (-o)).continuous)

theorem backwardObservation_eq (o : OrientationOnCarrier d) (u : Mode d h L (-o)) :
    backwardObservation L d h o u =
      NegativeOrientedLift.reversedRepresentative L (toGenerated d h L (-o) u).val := by
  ext z
  change scalarObservation L d h o (unreverseMode d h L o u)
    ((reversal d h o).symm (spectralPoint L d h (-o) z)) = _
  rw [unreverse_scalarObservation, scalarObservation_coordinate, coordinate_spectralPoint]
  change conj ((toGenerated d h L (-o) u).val (AddCircle.toCircle z) : ℂ) =
    ((toGenerated d h L (-o) u).val (AddCircle.toCircle (-z)) : ℂ)
  rw [AddCircle.toCircle_neg, map_inv, Circle.coe_inv_eq_conj]

theorem sourceRepresentative_backward_lift (o : OrientationOnCarrier d)
    (u : Mode d h L (-o)) :
    NegativeOrientedLift.lift L (sourceRepresentative L d h (-o) u : ComplexIntervalL2 0 L)
      =ᵐ[AddCircle.haarAddCircle] backwardObservation L d h o u := by
  rw [backwardObservation_eq]
  exact negativeLift_of_positiveRepresentative L _ _
    (GeneratedModes.representative_lifts L (toGenerated d h L (-o) u))

theorem positiveObservation_flow (o : OrientationOnCarrier d) (u : Mode d h L o) (t : ℝ) :
    positiveObservation L d h o u ((L / Real.pi * t : ℝ) : AddCircle (2 * L)) =
      ((toGenerated d h L o u).val (Circle.exp t) : ℂ) := by
  change scalarObservation L d h o u
    (spectralPoint L d h o ((L / Real.pi * t : ℝ) : AddCircle (2 * L))) = _
  rw [spectralPoint_flow, scalarObservation_flow]

/-- The pullback along the same source flow reverses the actual flow parameter. -/
theorem reversedObservation_flow (o : OrientationOnCarrier d) (u : Mode d h L o) (t : ℝ) :
    reversedObservation L d h o u ((L / Real.pi * t : ℝ) : AddCircle (2 * L)) =
      ((toGenerated d h L o u).val (Circle.exp (-t)) : ℂ) := by
  change scalarObservation L d h (-o) (reverseMode d h L o u)
    (reversal d h o
      (spectralPoint L d h o ((L / Real.pi * t : ℝ) : AddCircle (2 * L)))) = _
  rw [spectralPoint_flow, reversal_typedFlow, scalarObservation_flow, toGenerated_reverseMode]

theorem reversedObservation_flow_conj (o : OrientationOnCarrier d)
    (u : Mode d h L o) (t : ℝ) :
    reversedObservation L d h o u ((L / Real.pi * t : ℝ) : AddCircle (2 * L)) =
      conj ((toGenerated d h L o u).val (Circle.exp t) : ℂ) := by
  rw [reversedObservation_flow, Circle.exp_neg, map_inv, Circle.coe_inv_eq_conj]

end GeneratedFoundations.Arithmetic.TypedModeObservations

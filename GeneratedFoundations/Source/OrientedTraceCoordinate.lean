module

public import GeneratedFoundations.Source.CarrierOrientation
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# The trace coordinate selected by the actual carrier orientation

The coordinate of a tangent vector is its trace inner product with the
previously constructed oriented carrier unit. Its inverse is multiplication
of that same unit by a real scalar. Classification is used only to verify
that the original trace Lie space is one-dimensional; no classification
coordinate enters the definition of the resulting map.

The coordinate is unique among linear isometric coordinates that send this
unit to `1`. Reversing the carrier orientation negates it. When a compatible
phase coordinate or oriented Lie basis is supplied, the comparison is proved
using its actual representation image rather than an unrelated sign choice.
-/

@[expose] public section

noncomputable section

open Module Function
open scoped RealInnerProductSpace

namespace GeneratedFoundations.Source.OrientedTraceCoordinate

open TraceLieGeometry CarrierOrientation RepresentationDifferential

variable (d : MinimalCarrier.OrthogonalChangeDatum) (h : MinimalCarrier.IsMinimal d)

theorem trace_finrank : finrank ℝ (TraceLieSpace d h) = 1 := by
  obtain ⟨_, _, χ, hχ, _, _⟩ := MinimalCarrier.minimalCarrier_classification d h
  exact (phaseLinearEquiv d h χ hχ).finrank_eq.trans (Module.finrank_self ℝ)

theorem carrierUnit_ne_zero (o : OrientationOnCarrier d) : carrierUnit d h o ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [carrierUnit_norm]
  exact one_ne_zero

/-- The original unit spans the actual trace Lie space. -/
theorem unit_decomposition (o : OrientationOnCarrier d) (X : TraceLieSpace d h) :
    inner ℝ (carrierUnit d h o) X • carrierUnit d h o = X := by
  obtain ⟨r, hr⟩ := exists_smul_eq_of_finrank_eq_one (trace_finrank d h)
    (carrierUnit_ne_zero d h o) X
  rw [← hr, inner_smul_right, real_inner_self_eq_norm_sq, carrierUnit_norm, one_pow, mul_one]

def coordinateLinearEquiv (o : OrientationOnCarrier d) : TraceLieSpace d h ≃ₗ[ℝ] ℝ where
  toFun X := inner ℝ (carrierUnit d h o) X
  invFun r := r • carrierUnit d h o
  left_inv := unit_decomposition d h o
  right_inv r := by
    change inner ℝ (carrierUnit d h o) (r • carrierUnit d h o) = r
    rw [inner_smul_right, real_inner_self_eq_norm_sq, carrierUnit_norm, one_pow, mul_one]
  map_add' X Y := inner_add_right _ _ _
  map_smul' r X := inner_smul_right _ _ _

/-- The function is the trace pairing with the actual oriented source unit. -/
def coordinate (o : OrientationOnCarrier d) : TraceLieSpace d h ≃ₗᵢ[ℝ] ℝ where
  toLinearEquiv := coordinateLinearEquiv d h o
  norm_map' X := by
    change ‖inner ℝ (carrierUnit d h o) X‖ = ‖X‖
    calc
      _ = ‖inner ℝ (carrierUnit d h o) X • carrierUnit d h o‖ := by
        rw [norm_smul, carrierUnit_norm, mul_one]
      _ = ‖X‖ := congrArg norm (unit_decomposition d h o X)

@[simp] theorem coordinate_apply (o : OrientationOnCarrier d) (X : TraceLieSpace d h) :
    coordinate d h o X = inner ℝ (carrierUnit d h o) X := rfl

theorem coordinate_apply_trace (o : OrientationOnCarrier d) (X : TraceLieSpace d h) :
    coordinate d h o X = traceMetric d (carrierUnit d h o).tangent X.tangent := rfl

@[simp] theorem coordinate_symm_apply (o : OrientationOnCarrier d) (r : ℝ) :
    (coordinate d h o).symm r = r • carrierUnit d h o := rfl

@[simp] theorem coordinate_unit (o : OrientationOnCarrier d) :
    coordinate d h o (carrierUnit d h o) = 1 := by
  rw [coordinate_apply, real_inner_self_eq_norm_sq, carrierUnit_norm, one_pow]

theorem coordinate_smul_unit (o : OrientationOnCarrier d) (r : ℝ) :
    coordinate d h o (r • carrierUnit d h o) = r := by
  rw [map_smul, coordinate_unit, smul_eq_mul, mul_one]

/-- Specifying the image of the actual positive unit fixes the entire map. -/
theorem coordinate_unique (o : OrientationOnCarrier d)
    (q : TraceLieSpace d h ≃ₗᵢ[ℝ] ℝ) (hq : q (carrierUnit d h o) = 1) :
    q = coordinate d h o := by
  apply LinearIsometryEquiv.ext
  intro X
  calc
    q X = q (inner ℝ (carrierUnit d h o) X • carrierUnit d h o) :=
      congrArg q (unit_decomposition d h o X).symm
    _ = inner ℝ (carrierUnit d h o) X := by
      rw [map_smul, hq, smul_eq_mul, mul_one]
    _ = coordinate d h o X := rfl

theorem coordinate_existsUnique (o : OrientationOnCarrier d) :
    ∃! q : TraceLieSpace d h ≃ₗᵢ[ℝ] ℝ, q (carrierUnit d h o) = 1 :=
  ⟨coordinate d h o, coordinate_unit d h o, fun q hq => coordinate_unique d h o q hq⟩

theorem coordinate_reverse_apply (o : OrientationOnCarrier d) (X : TraceLieSpace d h) :
    coordinate d h (-o) X = -coordinate d h o X := by
  simp only [coordinate_apply, carrierUnit_reverse, inner_neg_left]

theorem coordinate_reverse (o : OrientationOnCarrier d) :
    (coordinate d h (-o) : TraceLieSpace d h → ℝ) =
      fun X => -coordinate d h o X :=
  funext (coordinate_reverse_apply d h o)

theorem coordinate_reverse_symm_apply (o : OrientationOnCarrier d) (r : ℝ) :
    (coordinate d h (-o)).symm r = -(coordinate d h o).symm r := by
  simp only [coordinate_symm_apply, carrierUnit_reverse, smul_neg]

/-- A phase coordinate aligned with the same carrier orientation is the
same isometry, not merely another Gaussian coordinate. -/
theorem coordinate_eq_phaseIsometry (e : d.Carrier ≃ₗᵢ[ℝ] ℂ)
    (χ : d.Changes ≃* Circle) (hχ : Continuous χ)
    (haction : ∀ g v, e (d.action g v) = (χ g : ℂ) * e v) :
    coordinate d h (coordinateOrientation d e) = phaseIsometry d h e χ hχ haction := by
  symm
  apply coordinate_unique d h (coordinateOrientation d e)
  rw [carrierUnit_coordinate d h e χ hχ haction, phaseIsometry_apply, phase_positiveUnit]

theorem coordinate_eq_phaseDifferential (e : d.Carrier ≃ₗᵢ[ℝ] ℂ)
    (χ : d.Changes ≃* Circle) (hχ : Continuous χ)
    (haction : ∀ g v, e (d.action g v) = (χ g : ℂ) * e v) (X : TraceLieSpace d h) :
    coordinate d h (coordinateOrientation d e) X = phaseDifferential d χ X.tangent := by
  rw [coordinate_eq_phaseIsometry d h e χ hχ haction, phaseIsometry_apply]

/-- Compatibility of the old Lie-line orientation is exactly the value `1`
on its unit in the coordinate selected by the original carrier. -/
theorem coordinate_orientedUnit_eq_one_iff (o : OrientationOnCarrier d)
    (χ : d.Changes ≃* Circle) (hχ : Continuous χ)
    (p : Orientation ℝ (TraceLieSpace d h) (Fin 1)) :
    coordinate d h o (orientedUnit d h χ hχ p) = 1 ↔
      endomorphism d (orientedUnit d h χ hχ p).tangent = carrierQuarterTurn d h o := by
  constructor
  · intro hp
    have heq : orientedUnit d h χ hχ p = carrierUnit d h o :=
      (coordinate d h o).injective (hp.trans (coordinate_unit d h o).symm)
    rw [heq, carrierUnit_image]
  · intro hp
    have heq : orientedUnit d h χ hχ p = carrierUnit d h o :=
      tangentEndomorphism_injective d h (hp.trans (carrierUnit_image d h o).symm)
    rw [heq, coordinate_unit]

theorem compatible_lieOrientation_existsUnique (o : OrientationOnCarrier d)
    (e : d.Carrier ≃ₗᵢ[ℝ] ℂ) (χ : d.Changes ≃* Circle) (hχ : Continuous χ)
    (haction : ∀ g v, e (d.action g v) = (χ g : ℂ) * e v) :
    ∃! p : Orientation ℝ (TraceLieSpace d h) (Fin 1),
      coordinate d h o (orientedUnit d h χ hχ p) = 1 := by
  simpa only [coordinate_orientedUnit_eq_one_iff] using
    carrier_lieOrientation_existsUnique d h e χ hχ haction o

end GeneratedFoundations.Source.OrientedTraceCoordinate

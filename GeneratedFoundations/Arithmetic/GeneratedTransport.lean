module

public import GeneratedFoundations.Arithmetic.TypedArithmetic
public import GeneratedFoundations.Arithmetic.TypedModeObservations
public import GeneratedFoundations.Spectral.NeumannSpatialScale
public import GeneratedFoundations.Spectral.PhysicalWindowModes

/-!
# Canonical transport of the generated arithmetic and its actual sources

Two minimal change data, two orientations, and two positive interval lengths
are allowed. Their actual source endomorphisms are compared through the
previously derived oriented coordinates. The unique comparison preserving
zero and successor transports the same original Neumann representatives,
spectral projections, heat responses, and prime profiles.

The Hilbert comparison is the existing spatial unitary. Its original-domain
map and its affine formula on translated windows are identified with the
representatives of the transported source modes. Positive and negative
channel comparisons use the same interval unitary and commute with the
actual circle reflection. No independent spectral witnesses are selected.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Topology NNReal LinearPMap ComplexConjugate
open GeneratedFoundations.Source GeneratedFoundations.Spectral
open GeneratedFoundations.Source.CarrierOrientation
open GeneratedFoundations.Spectral.AngularSpectralChannels

namespace GeneratedFoundations.Arithmetic.GeneratedTransport

open TypedSourceModes

variable (d : MinimalCarrier.OrthogonalChangeDatum) (h : MinimalCarrier.IsMinimal d)
variable (L : ℝ) [hL : Fact (0 < L)] (o : OrientationOnCarrier d)

abbrev representative (u : Mode d h L o) : (complexNeumannOperator hL.out).domain :=
  TypedModeObservations.sourceRepresentative L d h o u

def component (u : Mode d h L o) : NeumannSpectralProjections.Component L :=
  GeneratedModes.component L (toGenerated d h L o u)

variable (e : MinimalCarrier.OrthogonalChangeDatum) (he : MinimalCarrier.IsMinimal e)
variable (M : ℝ) [hM : Fact (0 < M)] (p : OrientationOnCarrier e)

/-- The comparison uses the actual normalized source maps at both ends. -/
def transport : Mode d h L o ≃+* Mode e he M p :=
  ((generatedEquiv d h L o).trans (GeneratedModes.transport L M)).trans
    (generatedEquiv e he M p).symm

@[simp] theorem toGenerated_transport (u : Mode d h L o) :
    toGenerated e he M p (transport d h L o e he M p u) =
      GeneratedModes.transport L M (toGenerated d h L o u) :=
  (generatedEquiv e he M p).apply_symm_apply _

theorem transport_coordinateEnd (u : Mode d h L o) :
    coordinateEnd e he p (transport d h L o e he M p u).val =
      coordinateEnd d h o u.val :=
  congrArg Subtype.val (toGenerated_transport d h L o e he M p u)

@[simp] theorem transport_successor (u : Mode d h L o) :
    transport d h L o e he M p (successor d h L o u) =
      successor e he M p (transport d h L o e he M p u) := by
  simp only [successor, map_add, map_one]

theorem transport_unique (F : Mode d h L o → Mode e he M p)
    (hzero : F 0 = 0)
    (hstep : ∀ u, F (successor d h L o u) = successor e he M p (F u)) :
    F = transport d h L o e he M p := by
  funext u
  apply TypedArithmetic.successor_induction d h L o
    (P := fun v => F v = transport d h L o e he M p v) ?_ ?_ u
  · simpa only [map_zero] using hzero
  · intro v hv
    rw [hstep, transport_successor, hv]

theorem transport_existsUnique :
    ∃! F : Mode d h L o → Mode e he M p,
      F 0 = 0 ∧ ∀ u, F (successor d h L o u) = successor e he M p (F u) :=
  ⟨transport d h L o e he M p,
    ⟨map_zero _, transport_successor d h L o e he M p⟩,
    fun F hF => transport_unique d h L o e he M p F hF.1 hF.2⟩

theorem transport_sameDatum (q : OrientationOnCarrier d) :
    transport d h L o d h M q = TypedArithmetic.transport d h L o M q := rfl

/-- This comparison relates the two actual groups; it does not identify them
as types or assume that their underlying carriers coincide. -/
def carrierComparison : Carrier d h o ≃ₜ* Carrier e he p :=
  (coordinate d h o).trans (coordinate e he p).symm

theorem carrierComparison_coordinate (x : Carrier d h o) :
    coordinate e he p (carrierComparison d h o e he p x) = coordinate d h o x :=
  (coordinate e he p).apply_symm_apply _

theorem transport_apply_carrierComparison (u : Mode d h L o) (x : Carrier d h o) :
    transport d h L o e he M p u (carrierComparison d h o e he p x) =
      carrierComparison d h o e he p (u x) := by
  apply (coordinate e he p).injective
  rw [carrierComparison_coordinate]
  have hv := congrArg (fun v : Circle →ₜ* Circle => v (coordinate d h o x))
    (transport_coordinateEnd d h L o e he M p u)
  change coordinate e he p ((transport d h L o e he M p u)
      ((coordinate e he p).symm (coordinate d h o x))) =
    coordinate d h o (u ((coordinate d h o).symm (coordinate d h o x))) at hv
  rw [ContinuousMulEquiv.symm_apply_apply] at hv
  exact hv

theorem transport_le_iff (u v : Mode d h L o) :
    transport d h L o e he M p u ≤ transport d h L o e he M p v ↔ u ≤ v := by
  rw [TypedArithmetic.le_iff_coordinate, TypedArithmetic.le_iff_coordinate,
    toGenerated_transport, toGenerated_transport]
  exact GeneratedModes.transport_le_iff L M _ _

theorem transport_irreducible_iff (u : Mode d h L o) :
    TypedArithmetic.CompositionIrreducible e he M p (transport d h L o e he M p u) ↔
      TypedArithmetic.CompositionIrreducible d h L o u := by
  rw [TypedArithmetic.irreducible_iff_coordinate, TypedArithmetic.irreducible_iff_coordinate,
    toGenerated_transport]
  exact GeneratedModes.transport_irreducible_iff L M _

theorem transport_ne_zero {u : Mode d h L o} (hu : u ≠ 0) :
    transport d h L o e he M p u ≠ 0 := by
  intro hz
  exact hu ((transport d h L o e he M p).injective (hz.trans (map_zero _).symm))

def transportProfile : (Mode d h L o →₀ ℕ) ≃+ (Mode e he M p →₀ ℕ) :=
  Finsupp.domCongr (transport d h L o e he M p).toEquiv

@[simp] theorem transportProfile_apply (f : Mode d h L o →₀ ℕ) (u : Mode d h L o) :
    transportProfile d h L o e he M p f (transport d h L o e he M p u) = f u := by
  change f ((transport d h L o e he M p).symm ((transport d h L o e he M p) u)) = f u
  rw [RingEquiv.symm_apply_apply]

theorem transportProfile_prod (f : Mode d h L o →₀ ℕ) :
    (transportProfile d h L o e he M p f).prod (fun u n => u ^ n) =
      transport d h L o e he M p (f.prod (fun u n => u ^ n)) := by
  change (Finsupp.equivMapDomain (transport d h L o e he M p).toEquiv f).prod
    (fun u n => u ^ n) = _
  rw [Finsupp.prod_equivMapDomain, map_finsuppProd]
  apply Finsupp.prod_congr
  intro u hu
  exact (map_pow (transport d h L o e he M p) u (f u)).symm

theorem transportProfile_spec {x : Mode d h L o} {f : Mode d h L o →₀ ℕ}
    (hf : TypedArithmetic.IsPrimeProfile d h L o x f) :
    TypedArithmetic.IsPrimeProfile e he M p (transport d h L o e he M p x)
      (transportProfile d h L o e he M p f) := by
  constructor
  · intro q hq
    obtain ⟨u, rfl⟩ := (transport d h L o e he M p).surjective q
    apply (transport_irreducible_iff d h L o e he M p u).mpr
    apply hf.1 u
    simpa only [Finsupp.mem_support_iff, transportProfile_apply] using hq
  · rw [transportProfile_prod, hf.2]

theorem primeProfile_transport (x : Mode d h L o) (hx : x ≠ 0) :
    TypedArithmetic.primeProfile e he M p (transport d h L o e he M p x)
        (transport_ne_zero d h L o e he M p hx) =
      transportProfile d h L o e he M p (TypedArithmetic.primeProfile d h L o x hx) :=
  (TypedArithmetic.primeProfile_existsUnique e he M p
    (transport_ne_zero d h L o e he M p hx)).unique
      (TypedArithmetic.primeProfile_spec e he M p _ _)
      (transportProfile_spec d h L o e he M p (TypedArithmetic.primeProfile_spec d h L o x hx))

/-- Equality takes place in the original Sobolev domain, not just on labels. -/
theorem representative_transport (u : Mode d h L o) :
    NeumannScaleTransport.domainEquiv L M (representative d h L o u) =
      representative e he M p (transport d h L o e he M p u) := by
  apply Subtype.ext
  change NeumannScaleTransport.unitary L M
      (GeneratedModes.representative L (toGenerated d h L o u) : ComplexIntervalL2 0 L) =
    (GeneratedModes.representative M
      (toGenerated e he M p (transport d h L o e he M p u)) : ComplexIntervalL2 0 M)
  rw [toGenerated_transport]
  exact GeneratedModes.transport_representative L M _

theorem representative_space_transport (u : Mode d h L o) :
    NeumannScaleTransport.unitary L M (representative d h L o u : ComplexIntervalL2 0 L) =
      (representative e he M p (transport d h L o e he M p u) : ComplexIntervalL2 0 M) :=
  congrArg Subtype.val (representative_transport d h L o e he M p u)

/-- The same spatial map acts on the full original domain and on every
initial state; these statements are not restricted to finite source modes. -/
theorem full_dynamics_transport :
    (∀ f : ComplexIntervalL2 0 L,
      NeumannScaleTransport.unitary L M f ∈ (complexNeumannOperator hM.out).domain ↔
        f ∈ (complexNeumannOperator hL.out).domain) ∧
    (∀ f : (complexNeumannOperator hL.out).domain,
      NeumannScaleTransport.unitary L M
          ((NeumannScaleTransport.energyUnit L : ℂ)⁻¹ • complexNeumannOperator hL.out f) =
        (NeumannScaleTransport.energyUnit M : ℂ)⁻¹ •
          complexNeumannOperator hM.out (NeumannScaleTransport.domainEquiv L M f)) ∧
    (∀ (t : ℝ≥0) (f : ComplexIntervalL2 0 L),
      NeumannScaleTransport.unitary L M (NeumannHeatSemigroup.heat L t f) =
        NeumannHeatSemigroup.heat M (NeumannScaleTransport.changeParameter L M t)
          (NeumannScaleTransport.unitary L M f)) :=
  ⟨NeumannScaleTransport.unitary_mem_domain_iff L M,
    NeumannScaleTransport.normalized_operator_intertwining L M,
    NeumannScaleTransport.heat_intertwining L M⟩

theorem representative_operator_transport (u : Mode d h L o) :
    NeumannScaleTransport.unitary L M
        ((NeumannScaleTransport.energyUnit L : ℂ)⁻¹ •
          complexNeumannOperator hL.out (representative d h L o u)) =
      (NeumannScaleTransport.energyUnit M : ℂ)⁻¹ •
        complexNeumannOperator hM.out
          (representative e he M p (transport d h L o e he M p u)) := by
  have hi := NeumannScaleTransport.normalized_operator_intertwining L M
    (representative d h L o u)
  rwa [representative_transport d h L o e he M p u] at hi

theorem representative_heat_transport (t : ℝ≥0) (u : Mode d h L o) :
    NeumannScaleTransport.unitary L M
        (NeumannHeatSemigroup.heat L t (representative d h L o u)) =
      NeumannHeatSemigroup.heat M (NeumannScaleTransport.changeParameter L M t)
        (representative e he M p (transport d h L o e he M p u)) := by
  rw [NeumannScaleTransport.heat_intertwining,
    representative_space_transport d h L o e he M p u]

theorem component_transport (u : Mode d h L o) :
    component e he M p (transport d h L o e he M p u) =
      NeumannScaleTransport.componentTransport L M (component d h L o u) := by
  simp only [component, toGenerated_transport, GeneratedModes.transport_component]

theorem projection_transport (u : Mode d h L o) (f : ComplexIntervalL2 0 L) :
    NeumannScaleTransport.unitary L M ((component d h L o u).val f) =
      (component e he M p (transport d h L o e he M p u)).val
        (NeumannScaleTransport.unitary L M f) := by
  rw [component_transport]
  exact NeumannScaleTransport.componentTransport_intertwining L M _ f

theorem normalized_energy_transport (u : Mode d h L o) :
    NeumannSpectralProjections.energy M (component e he M p (transport d h L o e he M p u)) /
        NeumannScaleTransport.energyUnit M =
      NeumannSpectralProjections.energy L (component d h L o u) /
        NeumannScaleTransport.energyUnit L := by
  rw [component_transport]
  exact NeumannScaleTransport.componentTransport_normalized_energy L M _

theorem response_transport (u : Mode d h L o) (t : ℝ≥0) :
    NeumannSpectralProjections.response M (component e he M p (transport d h L o e he M p u))
        (NeumannScaleTransport.changeParameter L M t) =
      NeumannSpectralProjections.response L (component d h L o u) t := by
  rw [component_transport]
  exact NeumannScaleTransport.componentTransport_response L M _ t

/-- At one positive normalized parameter, the exact heat response identifies
every source mode. Hence response preservation alone forces the canonical
transport; no arithmetic-homomorphism or bijectivity premise is used. -/
theorem transport_unique_of_response (F : Mode d h L o → Mode e he M p)
    {t : ℝ≥0} (ht : 0 < t)
    (hresponse : ∀ u,
      NeumannSpectralProjections.response M
          (component e he M p (F u))
          (NeumannScaleTransport.changeParameter L M t) =
        NeumannSpectralProjections.response L (component d h L o u) t) :
    F = transport d h L o e he M p := by
  have hchanged : 0 < NeumannScaleTransport.changeParameter L M t := by
    apply NNReal.coe_pos.mp
    rw [NeumannScaleTransport.changeParameter_coe]
    exact mul_pos (NNReal.coe_pos.mpr ht)
      (div_pos (NeumannScaleTransport.energyUnit_pos L)
        (NeumannScaleTransport.energyUnit_pos M))
  funext u
  apply toGenerated_injective e he M p
  apply (GeneratedModes.componentEquiv M).injective
  apply NeumannSpectralProjections.response_injective M hchanged
  change NeumannSpectralProjections.response M (component e he M p (F u))
      (NeumannScaleTransport.changeParameter L M t) =
    NeumannSpectralProjections.response M
      (component e he M p (transport d h L o e he M p u))
      (NeumannScaleTransport.changeParameter L M t)
  rw [hresponse, response_transport]

theorem responseTransport_existsUnique {t : ℝ≥0} (ht : 0 < t) :
    ∃! F : Mode d h L o → Mode e he M p, ∀ u,
      NeumannSpectralProjections.response M
          (component e he M p (F u))
          (NeumannScaleTransport.changeParameter L M t) =
        NeumannSpectralProjections.response L (component d h L o u) t :=
  ⟨transport d h L o e he M p, fun u => response_transport d h L o e he M p u t,
    fun F hF => transport_unique_of_response d h L o e he M p F ht hF⟩

theorem positive_lift_transport (u : Mode d h L o) :
    OrientedLift.lift M
      (NeumannScaleTransport.unitary L M (representative d h L o u : ComplexIntervalL2 0 L))
      =ᵐ[AddCircle.haarAddCircle]
        TypedModeObservations.positiveObservation M e he p (transport d h L o e he M p u) := by
  rw [representative_space_transport d h L o e he M p u]
  exact TypedModeObservations.sourceRepresentative_positive_lift M e he p _

theorem negative_lift_transport (u : Mode d h L o) :
    NegativeOrientedLift.lift M
      (NeumannScaleTransport.unitary L M (representative d h L o u : ComplexIntervalL2 0 L))
      =ᵐ[AddCircle.haarAddCircle]
        TypedModeObservations.reversedObservation M e he p (transport d h L o e he M p u) := by
  rw [representative_space_transport d h L o e he M p u]
  exact TypedModeObservations.sourceRepresentative_negative_lift M e he p _

/-- Both source and target orientation tags are reversed in this square. -/
theorem transport_reversal_square (u : Mode d h L o) :
    transport d h L (-o) e he M (-p) (reverseMode d h L o u) =
      reverseMode e he M p (transport d h L o e he M p u) := by
  apply toGenerated_injective e he M (-p)
  simp only [toGenerated_transport, toGenerated_reverseMode]

theorem transport_reversal (u : Mode d h L o) :
    transport d h L o d h L (-o) u = reversalEquiv d h L o u :=
  TypedArithmetic.transport_reversal d h L o u

theorem positiveObservation_flow_transport (u : Mode d h L o) (t : ℝ) :
    TypedModeObservations.positiveObservation M e he p (transport d h L o e he M p u)
        ((M / Real.pi * t : ℝ) : AddCircle (2 * M)) =
      TypedModeObservations.positiveObservation L d h o u
        ((L / Real.pi * t : ℝ) : AddCircle (2 * L)) := by
  simp only [TypedModeObservations.positiveObservation_flow, toGenerated_transport,
    GeneratedModes.transport_val]

theorem reversedObservation_flow_transport (u : Mode d h L o) (t : ℝ) :
    TypedModeObservations.reversedObservation M e he p (transport d h L o e he M p u)
        ((M / Real.pi * t : ℝ) : AddCircle (2 * M)) =
      TypedModeObservations.reversedObservation L d h o u
        ((L / Real.pi * t : ℝ) : AddCircle (2 * L)) := by
  simp only [TypedModeObservations.reversedObservation_flow, toGenerated_transport,
    GeneratedModes.transport_val]

/-- The positive Hilbert comparison is induced by the same interval unitary. -/
def positiveTransport : positiveChannel L ≃ₗᵢ[ℂ] positiveChannel M :=
  (OrientedLift.unitary L).symm.trans
    ((NeumannScaleTransport.unitary L M).trans (OrientedLift.unitary M))

theorem positiveTransport_unitary (f : ComplexIntervalL2 0 L) :
    positiveTransport L M (OrientedLift.unitary L f) =
      OrientedLift.unitary M (NeumannScaleTransport.unitary L M f) := by
  change OrientedLift.unitary M (NeumannScaleTransport.unitary L M
    ((OrientedLift.unitary L).symm (OrientedLift.unitary L f))) = _
  rw [LinearIsometryEquiv.symm_apply_apply]

def negativeTransport : negativeChannel L ≃ₗᵢ[ℂ] negativeChannel M :=
  (NegativeOrientedLift.unitary L).symm.trans
    ((NeumannScaleTransport.unitary L M).trans (NegativeOrientedLift.unitary M))

theorem negativeTransport_unitary (f : ComplexIntervalL2 0 L) :
    negativeTransport L M (NegativeOrientedLift.unitary L f) =
      NegativeOrientedLift.unitary M (NeumannScaleTransport.unitary L M f) := by
  change NegativeOrientedLift.unitary M (NeumannScaleTransport.unitary L M
    ((NegativeOrientedLift.unitary L).symm (NegativeOrientedLift.unitary L f))) = _
  rw [LinearIsometryEquiv.symm_apply_apply]

theorem channelReflection_transport (f : positiveChannel L) :
    negativeTransport L M (NegativeOrientedLift.channelReflection L f) =
      NegativeOrientedLift.channelReflection M (positiveTransport L M f) := by
  obtain ⟨g, rfl⟩ := (OrientedLift.unitary L).surjective f
  change negativeTransport L M (NegativeOrientedLift.unitary L g) =
    NegativeOrientedLift.channelReflection M
      (positiveTransport L M (OrientedLift.unitary L g))
  rw [negativeTransport_unitary, positiveTransport_unitary]
  rfl

theorem positiveTransport_heat (t : ℝ≥0) (f : positiveChannel L) :
    positiveTransport L M (OrientedLift.positiveHeat L t f) =
      OrientedLift.positiveHeat M (NeumannScaleTransport.changeParameter L M t)
        (positiveTransport L M f) := by
  obtain ⟨g, rfl⟩ := (OrientedLift.unitary L).surjective f
  rw [← OrientedLift.unitary_heat, positiveTransport_unitary,
    NeumannScaleTransport.heat_intertwining, OrientedLift.unitary_heat,
    positiveTransport_unitary]

theorem negativeTransport_heat (t : ℝ≥0) (f : negativeChannel L) :
    negativeTransport L M (NegativeOrientedLift.heat L t f) =
      NegativeOrientedLift.heat M (NeumannScaleTransport.changeParameter L M t)
        (negativeTransport L M f) := by
  obtain ⟨g, rfl⟩ := (NegativeOrientedLift.unitary L).surjective f
  rw [← NegativeOrientedLift.unitary_heat, negativeTransport_unitary,
    NeumannScaleTransport.heat_intertwining, NegativeOrientedLift.unitary_heat,
    negativeTransport_unitary]

theorem positive_representative_transport (u : Mode d h L o) :
    positiveTransport L M (OrientedLift.unitary L (representative d h L o u)) =
      OrientedLift.unitary M (representative e he M p (transport d h L o e he M p u)) := by
  rw [positiveTransport_unitary, representative_space_transport d h L o e he M p u]

theorem negative_representative_transport (u : Mode d h L o) :
    negativeTransport L M (NegativeOrientedLift.unitary L (representative d h L o u)) =
      NegativeOrientedLift.unitary M (representative e he M p (transport d h L o e he M p u)) := by
  rw [negativeTransport_unitary, representative_space_transport d h L o e he M p u]

/-- The actual physical-window vector belonging to this same typed source mode. -/
abbrev windowRepresentative (a : ℝ) (u : Mode d h L o) : complexNeumannDomain a (a + L) :=
  PhysicalWindowModes.representative a L (toGenerated d h L o u)

theorem window_representative_transport (a c : ℝ) (u : Mode d h L o) :
    NeumannSpatialScale.windowAffineUnitary L M a c
        (windowRepresentative d h L o a u : ComplexIntervalL2 a (a + L)) =
      (windowRepresentative e he M p c (transport d h L o e he M p u) :
        ComplexIntervalL2 c (c + M)) := by
  rw [PhysicalWindowModes.representative_toL2, PhysicalWindowModes.representative_toL2]
  change (shiftCanonicalL2Equiv (a := c) (L := M)).symm
      (NeumannScaleTransport.unitary L M ((shiftCanonicalL2Equiv (a := a) (L := L))
        ((shiftCanonicalL2Equiv (a := a) (L := L)).symm
          (representative d h L o u : ComplexIntervalL2 0 L)))) =
    (shiftCanonicalL2Equiv (a := c) (L := M)).symm
      (representative e he M p (transport d h L o e he M p u) : ComplexIntervalL2 0 M)
  rw [LinearIsometryEquiv.apply_symm_apply,
    representative_space_transport d h L o e he M p u]

theorem window_representative_affine (a c : ℝ) (u : Mode d h L o) :
    (windowRepresentative e he M p c (transport d h L o e he M p u) :
        ComplexIntervalL2 c (c + M)) =ᵐ[intervalMeasure c (c + M)]
      fun y => (Real.sqrt (L / M) : ℂ) *
        (windowRepresentative d h L o a u : ComplexIntervalL2 a (a + L))
          (a + L * (y - c) / M) := by
  have ha := NeumannSpatialScale.windowAffineUnitary_coe L M a c
    (windowRepresentative d h L o a u : ComplexIntervalL2 a (a + L))
  rw [window_representative_transport d h L o e he M p a c u] at ha
  exact ha

/-- A joint conclusion for one comparison of the two actual source systems.
The fields below are proved for the constructed comparison; none is an
additional hypothesis on the minimal change data. -/
structure IsSourceSpectralTransport (F : Mode d h L o → Mode e he M p) : Prop where
  zero : F 0 = 0
  successor : ∀ u, F (TypedSourceModes.successor d h L o u) =
    TypedSourceModes.successor e he M p (F u)
  source : ∀ u x, F u (carrierComparison d h o e he p x) =
    carrierComparison d h o e he p (u x)
  representative : ∀ u,
    NeumannScaleTransport.domainEquiv L M (GeneratedTransport.representative d h L o u) =
      GeneratedTransport.representative e he M p (F u)
  projection : ∀ u f,
    NeumannScaleTransport.unitary L M ((component d h L o u).val f) =
      (component e he M p (F u)).val (NeumannScaleTransport.unitary L M f)
  heat : ∀ t u,
    NeumannScaleTransport.unitary L M
        (NeumannHeatSemigroup.heat L t (GeneratedTransport.representative d h L o u)) =
      NeumannHeatSemigroup.heat M (NeumannScaleTransport.changeParameter L M t)
        (GeneratedTransport.representative e he M p (F u))
  positive : ∀ u,
    positiveTransport L M
        (OrientedLift.unitary L (GeneratedTransport.representative d h L o u)) =
      OrientedLift.unitary M (GeneratedTransport.representative e he M p (F u))
  negative : ∀ u,
    negativeTransport L M
        (NegativeOrientedLift.unitary L (GeneratedTransport.representative d h L o u)) =
      NegativeOrientedLift.unitary M (GeneratedTransport.representative e he M p (F u))
  window : ∀ a c u,
    NeumannSpatialScale.windowAffineUnitary L M a c
        (windowRepresentative d h L o a u : ComplexIntervalL2 a (a + L)) =
      (windowRepresentative e he M p c (F u) : ComplexIntervalL2 c (c + M))

theorem transport_spec :
    IsSourceSpectralTransport d h L o e he M p (transport d h L o e he M p) where
  zero := map_zero _
  successor := transport_successor d h L o e he M p
  source := transport_apply_carrierComparison d h L o e he M p
  representative := representative_transport d h L o e he M p
  projection := projection_transport d h L o e he M p
  heat := representative_heat_transport d h L o e he M p
  positive := positive_representative_transport d h L o e he M p
  negative := negative_representative_transport d h L o e he M p
  window := window_representative_transport d h L o e he M p

/-- Uniqueness holds among all functions of the original source modes.
The same unique function realizes every displayed source/spectral square. -/
theorem nativeTransport_existsUnique :
    ∃! F : Mode d h L o → Mode e he M p,
      IsSourceSpectralTransport d h L o e he M p F :=
  ⟨transport d h L o e he M p, transport_spec d h L o e he M p,
    fun F hF => transport_unique d h L o e he M p F hF.zero hF.successor⟩

end GeneratedFoundations.Arithmetic.GeneratedTransport

module

public import GeneratedFoundations.Physical.SourceFourDimensionalGaugeKinematics
public import GeneratedFoundations.Physical.SourceFrameConstruction

/-!
# The concrete generated matter bundle

The base is the four-coordinate Hermitian carrier already constructed from
the source. Every fibre is the complete source matter Hilbert space. Thus
the total space and its global coordinate map require no supplied family of
fibres, local trivializations or compatibility witnesses.

Local gauge fields below are configurations on this fixed bundle. Their
relative transitions and passive components are derived from the same
faithful source action. The construction does not classify other topological
bundles, nor identify an arbitrary localized bundle with this one.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Physical.CanonicalMatterBundle

open SourceChiralCarrier SourceGaugeUnitary

abbrev Base := SourceFourDimensionalGaugeKinematics.FourCarrier
abbrev Fibre := FullMatter
abbrev TotalSpace := Base × Fibre
abbrev GaugeField := Base → EffectiveGroup
abbrev Section := Base → Fibre

def projection : TotalSpace → Base := Prod.fst

/-- The source coordinate on the already fixed complete matter fibre. -/
def fibreCoordinate : TotalSpace → Fibre := Prod.snd

def globalCoordinates : TotalSpace ≃ Base × Fibre := Equiv.refl _

/-- A coordinate map preserving both generated coordinates has no freedom. -/
theorem globalCoordinates_unique (F : TotalSpace → Base × Fibre)
    (hbase : ∀ v, (F v).1 = projection v)
    (hfibre : ∀ v, (F v).2 = fibreCoordinate v) :
    F = globalCoordinates := by
  funext v
  exact Prod.ext (hbase v) (hfibre v)

def canonicalFrame : GaugeField := fun _ => 1

/-- Changes of frame act on the same generated fibre and leave the base fixed. -/
def gaugeAction (g : GaugeField) (v : TotalSpace) : TotalSpace :=
  (v.1, effectiveUnitaryRepresentation (g v.1) v.2)

@[simp] theorem gaugeAction_projection (g : GaugeField) (v : TotalSpace) :
    projection (gaugeAction g v) = projection v := rfl

theorem gaugeAction_fibre_norm (g : GaugeField) (v : TotalSpace) :
    ‖fibreCoordinate (gaugeAction g v)‖ = ‖fibreCoordinate v‖ :=
  (effectiveUnitaryRepresentation (g v.1)).norm_map v.2

@[simp] theorem gaugeAction_one (v : TotalSpace) :
    gaugeAction canonicalFrame v = v := by
  simp [gaugeAction, canonicalFrame]

theorem gaugeAction_inverse (g : GaugeField) (v : TotalSpace) :
    gaugeAction (fun x => (g x)⁻¹) (gaugeAction g v) = v := by
  apply Prod.ext
  · rfl
  · change effectiveUnitaryRepresentation (g v.1)⁻¹
      (effectiveUnitaryRepresentation (g v.1) v.2) = v.2
    rw [map_inv]
    exact (effectiveUnitaryRepresentation (g v.1)).symm_apply_apply v.2

def transition (g h : GaugeField) (x : Base) : EffectiveGroup := (g x)⁻¹ * h x

theorem transition_cocycle (g h k : GaugeField) (x : Base) :
    transition g h x * transition h k x = transition g k x := by
  simp [transition, mul_assoc]

/-- No overlap compatibility premise is needed for the generated transitions. -/
theorem canonical_transition (x : Base) :
    transition canonicalFrame canonicalFrame x = 1 := by
  simp [transition, canonicalFrame]

def components (g : GaugeField) (s : Section) (x : Base) : Fibre :=
  (effectiveUnitaryRepresentation (g x)).symm (s x)

theorem components_transition (g h : GaugeField) (s : Section) (x : Base) :
    components g s x =
      effectiveUnitaryRepresentation (transition g h x) (components h s x) := by
  simp [components, transition, map_mul, map_inv]

/-- Faithfulness makes a proposed relative transition unique on every fibre. -/
theorem transition_unique (g h : GaugeField) (x : Base) (q : EffectiveGroup)
    (hq : ∀ v : Fibre,
      effectiveUnitaryRepresentation (g x)
        (effectiveUnitaryRepresentation q v) =
      effectiveUnitaryRepresentation (h x) v) : q = transition g h x := by
  let f : Bool → Base → EffectiveGroup := fun b => bif b then h else g
  exact SourceFrameConstruction.relativeTransition_unique f false true x q hq

structure Conclusions : Prop where
  four_dimensional_base : Module.finrank ℝ Base = 4
  unique_coordinates : ∀ F : TotalSpace → Base × Fibre,
    (∀ v, (F v).1 = projection v) →
    (∀ v, (F v).2 = fibreCoordinate v) → F = globalCoordinates
  preserves_fibres : ∀ g v, projection (gaugeAction g v) = projection v
  unitary_fibres : ∀ g v,
    ‖fibreCoordinate (gaugeAction g v)‖ = ‖fibreCoordinate v‖
  exact_transitions : ∀ g h k x,
    transition g h x * transition h k x = transition g k x
  compatible_components : ∀ g h s x,
    components g s x =
      effectiveUnitaryRepresentation (transition g h x) (components h s x)

/-- All objects and compatibility facts are supplied by the generated source. -/
theorem generated : Conclusions where
  four_dimensional_base := SourceFourDimensionalGaugeKinematics.fourCarrier_finrank
  unique_coordinates := globalCoordinates_unique
  preserves_fibres := gaugeAction_projection
  unitary_fibres := gaugeAction_fibre_norm
  exact_transitions := transition_cocycle
  compatible_components := components_transition

end GeneratedFoundations.Physical.CanonicalMatterBundle

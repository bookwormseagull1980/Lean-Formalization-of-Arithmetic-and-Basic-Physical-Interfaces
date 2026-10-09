module

public import GeneratedFoundations.Source.RotationWitness
public import GeneratedFoundations.Source.ConnectedPlaneAction
public import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Minimal orthogonal change carriers

The comparison class consists of nonzero finite-dimensional real carriers
with faithful irreducible actions of nontrivial compact connected Lie groups.
Neither a carrier dimension nor a complex structure is supplied as part of a
datum. Minimality is a comparison with every datum in this class.

The classification below is an orthogonal intertwining and a topological
group isomorphism. Identification of its Lie differential and normalized
infinitesimal generator is a further assertion.
-/

@[expose] public section

open scoped Manifold ContDiff

namespace GeneratedFoundations.Source.MinimalCarrier

structure OrthogonalChangeDatum where
  Carrier : Type
  [carrierNormed : NormedAddCommGroup Carrier]
  [carrierInner : InnerProductSpace ℝ Carrier]
  [carrierFinite : FiniteDimensional ℝ Carrier]
  [carrierNontrivial : Nontrivial Carrier]
  Changes : Type
  [changesGroup : Group Changes]
  [changesTopology : TopologicalSpace Changes]
  [changesCompact : CompactSpace Changes]
  [changesConnected : ConnectedSpace Changes]
  [changesNontrivial : Nontrivial Changes]
  [changesHausdorff : T2Space Changes]
  [changesSecondCountable : SecondCountableTopology Changes]
  groupDimension : ℕ
  [changesCharts : ChartedSpace (EuclideanSpace ℝ (Fin groupDimension)) Changes]
  [changesManifold : IsManifold (𝓡 groupDimension) ∞ Changes]
  [changesLie : LieGroup (𝓡 groupDimension) ∞ Changes]
  action : Changes →* (Carrier ≃ₗᵢ[ℝ] Carrier)
  continuous : ∀ v : Carrier, Continuous (fun g : Changes => action g v)
  faithful : Function.Injective action
  irreducible : ∀ P : Submodule ℝ Carrier,
    (∀ g : Changes, ∀ v ∈ P, action g v ∈ P) → P = ⊥ ∨ P = ⊤

attribute [instance] OrthogonalChangeDatum.carrierNormed
  OrthogonalChangeDatum.carrierInner OrthogonalChangeDatum.carrierFinite
  OrthogonalChangeDatum.carrierNontrivial OrthogonalChangeDatum.changesGroup
  OrthogonalChangeDatum.changesTopology OrthogonalChangeDatum.changesCompact
  OrthogonalChangeDatum.changesConnected OrthogonalChangeDatum.changesNontrivial
  OrthogonalChangeDatum.changesHausdorff OrthogonalChangeDatum.changesSecondCountable
  OrthogonalChangeDatum.changesCharts OrthogonalChangeDatum.changesManifold
  OrthogonalChangeDatum.changesLie

def IsMinimal (d : OrthogonalChangeDatum) : Prop :=
  ∀ e : OrthogonalChangeDatum,
    Module.finrank ℝ d.Carrier ≤ Module.finrank ℝ e.Carrier

noncomputable def rotationDatum : OrthogonalChangeDatum where
  Carrier := ℂ
  Changes := Circle
  changesNontrivial := ⟨⟨1, -1, by
    intro h
    have hh := congrArg (fun z : Circle => (z : ℂ)) h
    norm_num at hh⟩⟩
  groupDimension := 1
  action := RotationWitness.action
  continuous := RotationWitness.action_continuous
  faithful := RotationWitness.action_faithful
  irreducible := RotationWitness.real_irreducible

theorem dimension_lowerBound (d : OrthogonalChangeDatum) :
    2 ≤ Module.finrank ℝ d.Carrier :=
  DimensionLowerBound.faithful_connected_dimension_at_least_two
    d.action d.continuous d.faithful

theorem rotationDatum_isMinimal : IsMinimal rotationDatum := by
  intro d
  change Module.finrank ℝ ℂ ≤ Module.finrank ℝ d.Carrier
  rw [Complex.finrank_real_complex]
  exact dimension_lowerBound d

theorem minimal_iff_dimension_two (d : OrthogonalChangeDatum) :
    IsMinimal d ↔ Module.finrank ℝ d.Carrier = 2 := by
  constructor
  · intro h
    have hupper := h rotationDatum
    have hlower := dimension_lowerBound d
    have hdim : Module.finrank ℝ rotationDatum.Carrier = 2 :=
      Complex.finrank_real_complex
    rw [hdim] at hupper
    exact Nat.le_antisymm hupper hlower
  · intro h e
    rw [h]
    exact dimension_lowerBound e

theorem minimalCarrier_classification (d : OrthogonalChangeDatum) (h : IsMinimal d) :
    Module.finrank ℝ d.Carrier = 2 ∧
      ∃ (e : d.Carrier ≃ₗᵢ[ℝ] ℂ) (f : d.Changes ≃* Circle),
        Continuous f ∧ Continuous f.symm ∧
          ∀ g v, e (d.action g v) = (f g : ℂ) * e v := by
  have hdim := (minimal_iff_dimension_two d).mp h
  exact ⟨hdim, ConnectedPlaneAction.plane_action_classification
    d.action d.continuous d.faithful hdim⟩

theorem minimalDatum_exists : ∃ d : OrthogonalChangeDatum, IsMinimal d :=
  ⟨rotationDatum, rotationDatum_isMinimal⟩

end GeneratedFoundations.Source.MinimalCarrier

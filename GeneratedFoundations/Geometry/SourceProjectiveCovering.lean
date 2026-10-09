module

public import GeneratedFoundations.Geometry.SourceProjectiveGeometry
public import Mathlib.Topology.Covering.Quotient

/-!
# The two-sheeted covering by the actual source group

The source group retains its matrix topology. Its previously determined
centre is a discrete subgroup, so the actual central quotient map is a
covering map. The homeomorphism with independently defined real projective
space transfers this covering to the source projection onto `RP3`.

Each fibre has exactly two points. In particular, every projective point
has a neighbourhood whose full inverse image is homeomorphic, over that
neighbourhood, to its product with the two-element centre. This assertion
uses the quotient topology and supplies local trivializations; it is
stronger than the algebraic identification of the central fibres.

No simple-connectedness assertion is needed for this covering theorem.
-/

@[expose] public section

noncomputable section

open Topology
open GeneratedFoundations.Operations.SourceSpinCornerGroup (SU2)
open GeneratedFoundations.Geometry.SourceSpinCentre
open GeneratedFoundations.Geometry.SourceCentralObservations
open GeneratedFoundations.Geometry.SourceQuaternionAmplitude
open GeneratedFoundations.Geometry.SourceProjectiveGeometry

namespace GeneratedFoundations.Geometry.SourceProjectiveCovering

theorem centre_isDiscrete : IsDiscrete (Subgroup.center SU2 : Set SU2) := by
  rw [centre_eq_pair]
  exact ((Set.finite_singleton negativeIdentity).insert (1 : SU2)).isDiscrete

/-- The deck action is multiplication by the actual central source operations. -/
theorem central_quotient_isQuotientCoveringMap :
    IsQuotientCoveringMap quotientContinuous (Subgroup.center SU2) := by
  have hf : IsQuotientMap (quotientMap : SU2 → CentralQuotient) :=
    quotientContinuous_isQuotientMap
  have hk : IsDiscrete (quotientMap.ker : Set SU2) := by
    rw [quotientMap_kernel]
    exact centre_isDiscrete
  have hc := hf.isQuotientCoveringMap_of_isDiscrete_ker_monoidHom hk
  rw [quotientMap_kernel] at hc
  exact hc

theorem central_quotient_isCoveringMap : IsCoveringMap quotientContinuous :=
  central_quotient_isQuotientCoveringMap.isCoveringMap

theorem sourceProjection_isQuotientCoveringMap :
    IsQuotientCoveringMap sourceProjection (Subgroup.center SU2) := by
  have he : centralProjectiveHomeomorph ∘ quotientContinuous = sourceProjection := by
    funext U
    exact projectiveDescend_apply U
  rw [← he]
  exact central_quotient_isQuotientCoveringMap.homeomorph_comp
    centralProjectiveHomeomorph

/-- The source projection covers the independent projective topology. -/
theorem sourceProjection_isCoveringMap : IsCoveringMap sourceProjection :=
  sourceProjection_isQuotientCoveringMap.isCoveringMap

theorem sourceProjection_isLocalHomeomorph : IsLocalHomeomorph sourceProjection :=
  sourceProjection_isCoveringMap.isLocalHomeomorph

theorem sourceProjection_fibre_eq (U : SU2) :
    sourceProjection ⁻¹' {sourceProjection U} = {U, negativeIdentity * U} := by
  ext V
  change sourceProjection V = sourceProjection U ↔ V = U ∨ V = negativeIdentity * U
  exact sourceProjection_eq_iff V U

theorem sourceProjection_fibre_card (p : RP3) :
    Nat.card (sourceProjection ⁻¹' {p}) = 2 := by
  obtain ⟨U, hU⟩ := sourceProjection_isQuotientMap.surjective p
  exact (Nat.card_congr
    (sourceProjection_isQuotientCoveringMap.fiberEquivGroup ⟨U, hU⟩)).trans centre_card

/-- The two central elements index the sheets in a genuine local trivialization. -/
theorem sourceProjection_evenlyCovered (p : RP3) :
    IsEvenlyCovered sourceProjection p (Subgroup.center SU2) := by
  let : DiscreteTopology (Subgroup.center SU2) :=
    SetLike.isDiscrete_iff_discreteTopology.mp centre_isDiscrete
  let : DiscreteTopology (sourceProjection ⁻¹' {p}) :=
    (sourceProjection_isCoveringMap p).1
  obtain ⟨U, hU⟩ := sourceProjection_isQuotientMap.surjective p
  exact (sourceProjection_isCoveringMap p).of_fiber_homeomorph
    (sourceProjection_isQuotientCoveringMap.fiberEquivGroup ⟨U, hU⟩).toHomeomorphOfDiscrete

theorem sourceProjection_local_trivialization (p : RP3) :
    ∃ t : Bundle.Trivialization (Subgroup.center SU2) sourceProjection,
      p ∈ t.baseSet := by
  let h := sourceProjection_evenlyCovered p
  exact ⟨h.toTrivialization', h.2.choose_spec.1⟩

/-- The usual unit-sphere projection has the same covering property. -/
theorem sphereProjection_isCoveringMap : IsCoveringMap sphereProjection := by
  have he : sourceProjection ∘ sourceSphereHomeomorph.symm = sphereProjection := by
    funext x
    simp only [Function.comp_apply, sourceProjection_apply,
      Homeomorph.apply_symm_apply]
  rw [← he]
  exact sourceProjection_isCoveringMap.comp_homeomorph sourceSphereHomeomorph.symm

end GeneratedFoundations.Geometry.SourceProjectiveCovering

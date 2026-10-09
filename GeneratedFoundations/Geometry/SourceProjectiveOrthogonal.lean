module

public import GeneratedFoundations.Geometry.SourceOrthogonalTopology
public import GeneratedFoundations.Geometry.SourceProjectiveCovering

/-!
# The effective projective orthogonal response

All determinant-one real isometries of the amplitude space act on the
independent projectivization of four-dimensional Euclidean space. The
kernel of this action is exactly the identity and the antipodal isometry.
Their quotient is therefore the effective projective orthogonal group.
The original pair of source groups covers it with four sheets, indexed by
the two independent source centres.

The target is defined from all ambient orthogonal transformations, not
as the range of the source action. The construction identifies the actual
action on projective points. A classification of arbitrary intrinsic
isometries of a Riemannian projective space is a separate assertion.
-/

@[expose] public section

noncomputable section

open Topology
open scoped Quaternion
open GeneratedFoundations.Operations.SourceSpinCornerGroup (SU2)
open GeneratedFoundations.Geometry.SourceQuaternionAmplitude
open GeneratedFoundations.Geometry.SourceSpinCentre
open GeneratedFoundations.Geometry.SourceProjectiveGeometry
open GeneratedFoundations.Geometry.SourceLeftRightAction
open GeneratedFoundations.Geometry.SourceOrthogonalCover
open GeneratedFoundations.Geometry.SourceOrthogonalTopology

namespace GeneratedFoundations.Geometry.SourceProjectiveOrthogonal

/-- The ordinary Euclidean coordinate expression of an ambient isometry. -/
def euclideanIsometry (e : specialOrthogonal) : ResponseVector ≃ₗᵢ[ℝ] ResponseVector :=
  (Quaternion.linearIsometryEquivTuple.symm.trans e.val).trans
    Quaternion.linearIsometryEquivTuple

/-- The projective action is induced by the actual linear map on vectors. -/
def ambientAction (e : specialOrthogonal) : RP3 → RP3 :=
  Projectivization.map (euclideanIsometry e).toLinearMap (euclideanIsometry e).injective

theorem ambientAction_source_sphere (p : SourcePair) (x : Sphere3) :
    ambientAction (sourceCover p) (sphereProjection x) =
      sphereProjection (sphereAction p x) := by
  rw [sphereProjection_apply, sphereProjection_apply]
  unfold ambientAction
  rw [Projectivization.map_mk]
  have hx : euclideanIsometry (sourceCover p) x =
      (sphereAction p x : ResponseVector) := sourceRepresentation_sphere p x
  apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr
  exact ⟨1, (one_smul ℝ (sphereAction p x : ResponseVector)).trans hx.symm⟩

theorem ambientAction_source (p : SourcePair) (x : RP3) :
    ambientAction (sourceCover p) x = projectiveAction p x := by
  obtain ⟨y, rfl⟩ := sphereProjection_isQuotientMap.surjective x
  rw [ambientAction_source_sphere, projectiveAction_sphere]

/-- The homomorphism is defined on the full orthogonal group. -/
def projectiveRepresentation : specialOrthogonal →* Function.End RP3 where
  toFun := ambientAction
  map_one' := by
    funext x
    rw [← sourceCover.map_one, ambientAction_source, projectiveAction_one]
    rfl
  map_mul' e f := by
    obtain ⟨p, rfl⟩ := sourceCover_surjective e
    obtain ⟨q, rfl⟩ := sourceCover_surjective f
    funext x
    change ambientAction (sourceCover p * sourceCover q) x =
      ambientAction (sourceCover p) (ambientAction (sourceCover q) x)
    rw [← map_mul, ambientAction_source, ambientAction_source,
      ambientAction_source, projectiveAction_mul]

theorem projectiveRepresentation_source_kernel (p : SourcePair) :
    sourceCover p ∈ projectiveRepresentation.ker ↔
      p.1 ∈ Subgroup.center SU2 ∧ p.2 ∈ Subgroup.center SU2 := by
  change (ambientAction (sourceCover p) = id) ↔ _
  rw [funext_iff]
  simp only [ambientAction_source, id_eq]
  exact projectiveAction_trivial_iff_centres p

/-- This element is proved below to negate every ambient vector. -/
def antipodal : specialOrthogonal := sourceCover (negativeIdentity, 1)

theorem antipodal_apply (x : ℍ) : antipodal.val x = -x := by
  have hunit (q : unitary ℍ) : antipodal.val (q : ℍ) = -(q : ℍ) := by
    apply Quaternion.linearIsometryEquivTuple.injective
    change Quaternion.linearIsometryEquivTuple
        (sourceRepresentation (negativeIdentity, 1) (q : ℍ)) =
      Quaternion.linearIsometryEquivTuple (-(q : ℍ))
    have h := sphereAction_left_central (unitarySphereHomeomorph q)
    rw [← sourceRepresentation_sphere] at h
    change Quaternion.linearIsometryEquivTuple
        (sourceRepresentation (negativeIdentity, 1)
          (Quaternion.linearIsometryEquivTuple.symm
            (Quaternion.linearIsometryEquivTuple (q : ℍ)))) =
      -Quaternion.linearIsometryEquivTuple (q : ℍ) at h
    simpa only [Quaternion.linearIsometryEquivTuple.symm_apply_apply, map_neg] using h
  by_cases hx : x = 0
  · simp [hx]
  · rw [← normalizedUnit_synthesis x hx, map_smul, hunit, smul_neg,
      normalizedUnit_synthesis]

theorem antipodal_ne_one : antipodal ≠ 1 := by
  intro h
  have hx := antipodal_apply (1 : ℍ)
  rw [h] at hx
  have hr := congrArg (fun q : ℍ => q.re) hx
  norm_num at hr

theorem right_centre_eq_antipodal : sourceCover (1, negativeIdentity) = antipodal := by
  apply (sourceCover_fiber_iff _ _).mpr
  right
  apply Prod.ext
  · change 1 = negativeIdentity * negativeIdentity
    exact negativeIdentity_sq.symm
  · change negativeIdentity = negativeIdentity * 1
    exact (mul_one _).symm

theorem diagonal_centre_eq_one : sourceCover (negativeIdentity, negativeIdentity) = 1 :=
  (sourceCover_kernel_iff _).mpr (Or.inr rfl)

/-- The ineffective subgroup is exactly the two ambient scalar isometries. -/
theorem projectiveRepresentation_kernel :
    (projectiveRepresentation.ker : Set specialOrthogonal) = {1, antipodal} := by
  ext e
  obtain ⟨p, rfl⟩ := sourceCover_surjective e
  change sourceCover p ∈ projectiveRepresentation.ker ↔
    sourceCover p = 1 ∨ sourceCover p = antipodal
  rw [projectiveRepresentation_source_kernel]
  constructor
  · rintro ⟨ha, hb⟩
    rcases (mem_centre_iff _).mp ha with ha | ha <;>
      rcases (mem_centre_iff _).mp hb with hb | hb
    · left
      rw [show p = (1, 1) from Prod.ext ha hb]
      exact sourceCover.map_one
    · right
      rw [show p = (1, negativeIdentity) from Prod.ext ha hb]
      exact right_centre_eq_antipodal
    · right
      rw [show p = (negativeIdentity, 1) from Prod.ext ha hb]
      rfl
    · left
      rw [show p = (negativeIdentity, negativeIdentity) from Prod.ext ha hb]
      exact diagonal_centre_eq_one
  · rintro (h | h)
    · apply (projectiveRepresentation_source_kernel p).mp
      rw [h]
      exact projectiveRepresentation.ker.one_mem
    · apply (projectiveRepresentation_source_kernel p).mp
      rw [h]
      exact (projectiveRepresentation_source_kernel (negativeIdentity, 1)).mpr
        ⟨negativeIdentity_mem_centre, (Subgroup.center SU2).one_mem⟩

instance : IsClosed (projectiveRepresentation.ker : Set specialOrthogonal) := by
  rw [projectiveRepresentation_kernel]
  exact ((Set.finite_singleton antipodal).insert (1 : specialOrthogonal)).isClosed

/-- `SO(4)/{I,-I}`, using the matrix topology on the full ambient group. -/
abbrev EffectiveOrthogonal := specialOrthogonal ⧸ projectiveRepresentation.ker

def effectiveCover : SourcePair →* EffectiveOrthogonal :=
  (QuotientGroup.mk' projectiveRepresentation.ker).comp sourceCover

theorem effectiveCover_continuous : Continuous effectiveCover :=
  QuotientGroup.continuous_mk.comp sourceCover_continuous

theorem effectiveCover_surjective : Function.Surjective effectiveCover :=
  QuotientGroup.mk_surjective.comp sourceCover_surjective

theorem effectiveCover_eq_one_iff (p : SourcePair) :
    effectiveCover p = 1 ↔
      p.1 ∈ Subgroup.center SU2 ∧ p.2 ∈ Subgroup.center SU2 := by
  change (QuotientGroup.mk (sourceCover p) : EffectiveOrthogonal) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff, projectiveRepresentation_source_kernel]

theorem effectiveCover_kernel :
    effectiveCover.ker = (Subgroup.center SU2).prod (Subgroup.center SU2) := by
  ext p
  exact effectiveCover_eq_one_iff p

def kernelCentreEquiv :
    effectiveCover.ker ≃ (Subgroup.center SU2) × (Subgroup.center SU2) where
  toFun p := ⟨⟨p.val.1, ((effectiveCover_eq_one_iff p.val).mp p.property).1⟩,
    ⟨p.val.2, ((effectiveCover_eq_one_iff p.val).mp p.property).2⟩⟩
  invFun z := ⟨(z.1.val, z.2.val),
    (effectiveCover_eq_one_iff _).mpr ⟨z.1.property, z.2.property⟩⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)

theorem effectiveCover_kernel_card : Nat.card effectiveCover.ker = 4 := by
  rw [Nat.card_congr kernelCentreEquiv, Nat.card_prod, centre_card]

theorem effectiveCover_kernel_isDiscrete :
    IsDiscrete (effectiveCover.ker : Set SourcePair) := by
  have hs : (effectiveCover.ker : Set SourcePair) =
      (Subgroup.center SU2 : Set SU2) ×ˢ (Subgroup.center SU2 : Set SU2) := by
    ext p
    exact effectiveCover_eq_one_iff p
  rw [hs, centre_eq_pair]
  exact (((Set.finite_singleton negativeIdentity).insert (1 : SU2)).prod
    ((Set.finite_singleton negativeIdentity).insert (1 : SU2))).isDiscrete

theorem effectiveCover_isQuotientMap : IsQuotientMap effectiveCover :=
  IsQuotientMap.of_surjective_continuous effectiveCover_surjective effectiveCover_continuous

/-- The two source centres give four, rather than two, covering sheets. -/
theorem effectiveCover_isQuotientCoveringMap :
    IsQuotientCoveringMap effectiveCover effectiveCover.ker :=
  effectiveCover_isQuotientMap.isQuotientCoveringMap_of_isDiscrete_ker_monoidHom
    effectiveCover_kernel_isDiscrete

theorem effectiveCover_isCoveringMap : IsCoveringMap effectiveCover :=
  effectiveCover_isQuotientCoveringMap.isCoveringMap

theorem effectiveCover_fibre_card (e : EffectiveOrthogonal) :
    Nat.card (effectiveCover ⁻¹' {e}) = 4 := by
  obtain ⟨p, hp⟩ := effectiveCover_surjective e
  exact (Nat.card_congr
    (effectiveCover_isQuotientCoveringMap.fiberEquivGroup ⟨p, hp⟩)).trans
    effectiveCover_kernel_card

/-- The descended action is faithful by construction from the actual ambient kernel. -/
def effectiveRepresentation : EffectiveOrthogonal →* Function.End RP3 :=
  QuotientGroup.lift projectiveRepresentation.ker projectiveRepresentation le_rfl

theorem effectiveRepresentation_injective : Function.Injective effectiveRepresentation :=
  (QuotientGroup.injective_lift_iff projectiveRepresentation.ker
    projectiveRepresentation le_rfl).mpr rfl

theorem effectiveRepresentation_source (p : SourcePair) (x : RP3) :
    effectiveRepresentation (effectiveCover p) x = projectiveAction p x :=
  ambientAction_source p x

theorem effectiveAction_continuous :
    Continuous (fun ex : EffectiveOrthogonal × RP3 => effectiveRepresentation ex.1 ex.2) := by
  have hq := effectiveCover_isQuotientCoveringMap.isOpenQuotientMap
  apply (hq.prodMap IsOpenQuotientMap.id).isQuotientMap.continuous_iff.mpr
  simpa only [Function.comp_def, Prod.map, id_eq, effectiveRepresentation_source] using
    projectiveAction_continuous

def effectiveQuotientEquiv : SourcePair ⧸ effectiveCover.ker ≃* EffectiveOrthogonal :=
  QuotientGroup.quotientKerEquivOfSurjective effectiveCover effectiveCover_surjective

theorem effectiveQuotientEquiv_continuous : Continuous effectiveQuotientEquiv := by
  apply (QuotientGroup.isQuotientMap_mk effectiveCover.ker).continuous_iff.mpr
  exact effectiveCover_continuous

def effectiveQuotientHomeomorph : SourcePair ⧸ effectiveCover.ker ≃ₜ EffectiveOrthogonal :=
  effectiveQuotientEquiv.toEquiv.toHomeomorphOfContinuousClosed
    effectiveQuotientEquiv_continuous effectiveQuotientEquiv_continuous.isClosedMap

def effectiveQuotientContinuousEquiv :
    SourcePair ⧸ effectiveCover.ker ≃ₜ* EffectiveOrthogonal where
  toMulEquiv := effectiveQuotientEquiv
  continuous_toFun := effectiveQuotientHomeomorph.continuous
  continuous_invFun := effectiveQuotientHomeomorph.symm.continuous

@[simp] theorem effectiveQuotientContinuousEquiv_mk (p : SourcePair) :
    effectiveQuotientContinuousEquiv (QuotientGroup.mk p) = effectiveCover p := rfl

theorem effectiveQuotientContinuousEquiv_unique
    (e : SourcePair ⧸ effectiveCover.ker ≃ₜ* EffectiveOrthogonal)
    (he : ∀ p : SourcePair, e (QuotientGroup.mk p) = effectiveCover p) :
    e = effectiveQuotientContinuousEquiv := by
  apply ContinuousMulEquiv.ext
  intro q
  induction q using Quotient.inductionOn' with
  | h p => exact he p

end GeneratedFoundations.Geometry.SourceProjectiveOrthogonal

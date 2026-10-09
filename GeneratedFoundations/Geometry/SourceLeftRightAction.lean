module

public import GeneratedFoundations.Geometry.SourceProjectiveGeometry
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Left and right actions of the generated source group

Two actual source operations act by left multiplication and inverse right
multiplication. The previously constructed homeomorphisms transport this
continuous action to the independent Euclidean three-sphere and real
projective three-space. The sphere kernel is the diagonal centre. The
projective kernel is the full product of the two centres: continuity and
connectedness exclude a sign that varies with the source point.

These are actions of the original source group and its product. No
identification with an independently constructed Clifford spin group or
covering of an orthogonal group is assumed or asserted here.
-/

@[expose] public section

noncomputable section

open Topology Set
open scoped Quaternion
open GeneratedFoundations.Operations.SourceSpinCorner (Mat2)
open GeneratedFoundations.Operations.SourceSpinCornerGroup (SU2)
open GeneratedFoundations.Geometry.SourceSpinCentre
open GeneratedFoundations.Geometry.SourceCentralObservations
open GeneratedFoundations.Geometry.SourceQuaternionAmplitude
open GeneratedFoundations.Geometry.SourceProjectiveGeometry

namespace GeneratedFoundations.Geometry.SourceLeftRightAction

abbrev SourcePair := SU2 × SU2

/-- The product uses the actual generated source matrices in both factors. -/
def sourceAction (p : SourcePair) (u : SU2) : SU2 := p.1 * u * p.2⁻¹

theorem sourceAction_matrix (p : SourcePair) (u : SU2) :
    (sourceAction p u : Mat2) = (p.1 : Mat2) * (u : Mat2) * (p.2 : Mat2).conjTranspose := rfl

@[simp] theorem sourceAction_one (u : SU2) : sourceAction 1 u = u := by
  simp [sourceAction]

theorem sourceAction_mul (p q : SourcePair) (u : SU2) :
    sourceAction (p * q) u = sourceAction p (sourceAction q u) := by
  change (p.1 * q.1) * u * (p.2 * q.2)⁻¹ = p.1 * (q.1 * u * q.2⁻¹) * p.2⁻¹
  simp only [mul_inv_rev, mul_assoc]

@[instance_reducible] def sourceMulAction : MulAction SourcePair SU2 where
  smul := sourceAction
  one_smul := sourceAction_one
  mul_smul := sourceAction_mul

theorem sourceAction_continuous :
    Continuous (fun pu : SourcePair × SU2 => sourceAction pu.1 pu.2) :=
  (continuous_fst.fst.mul continuous_snd).mul continuous_fst.snd.inv

theorem sourceAction_continuous_fixed (p : SourcePair) : Continuous (sourceAction p) :=
  (continuous_const.mul continuous_id).mul continuous_const

def sphereAction (p : SourcePair) (x : Sphere3) : Sphere3 :=
  sourceSphereHomeomorph (sourceAction p (sourceSphereHomeomorph.symm x))

@[simp] theorem sphereAction_source (p : SourcePair) (u : SU2) :
    sphereAction p (sourceSphereHomeomorph u) = sourceSphereHomeomorph (sourceAction p u) := by
  unfold sphereAction
  rw [Homeomorph.symm_apply_apply]

@[simp] theorem sphereAction_one (x : Sphere3) : sphereAction 1 x = x := by
  rw [sphereAction, sourceAction_one, Homeomorph.apply_symm_apply]

theorem sphereAction_mul (p q : SourcePair) (x : Sphere3) :
    sphereAction (p * q) x = sphereAction p (sphereAction q x) := by
  unfold sphereAction
  rw [Homeomorph.symm_apply_apply, sourceAction_mul]

@[instance_reducible] def sphereMulAction : MulAction SourcePair Sphere3 where
  smul := sphereAction
  one_smul := sphereAction_one
  mul_smul := sphereAction_mul

theorem sphereAction_continuous :
    Continuous (fun px : SourcePair × Sphere3 => sphereAction px.1 px.2) := by
  have hp : Continuous (fun px : SourcePair × Sphere3 =>
      (px.1, sourceSphereHomeomorph.symm px.2)) :=
    continuous_fst.prodMk (sourceSphereHomeomorph.symm.continuous.comp continuous_snd)
  have ha := sourceAction_continuous.comp hp
  simpa only [Function.comp_def, sphereAction] using
    sourceSphereHomeomorph.continuous.comp ha

/-- This action is defined in the actual central group quotient. -/
def quotientAction (p : SourcePair) (q : CentralQuotient) : CentralQuotient :=
  quotientMap p.1 * q * (quotientMap p.2)⁻¹

@[simp] theorem quotientAction_source (p : SourcePair) (u : SU2) :
    quotientAction p (quotientContinuous u) = quotientContinuous (sourceAction p u) := by
  change quotientMap p.1 * quotientMap u * (quotientMap p.2)⁻¹ =
    quotientMap (p.1 * u * p.2⁻¹)
  simp only [map_mul, map_inv]

@[simp] theorem quotientAction_one (q : CentralQuotient) : quotientAction 1 q = q := by
  simp [quotientAction]

theorem quotientAction_mul (p r : SourcePair) (q : CentralQuotient) :
    quotientAction (p * r) q = quotientAction p (quotientAction r q) := by
  change quotientMap (p.1 * r.1) * q * (quotientMap (p.2 * r.2))⁻¹ =
    quotientMap p.1 * (quotientMap r.1 * q * (quotientMap r.2)⁻¹) * (quotientMap p.2)⁻¹
  simp only [map_mul, mul_inv_rev, mul_assoc]

theorem quotientAction_continuous :
    Continuous (fun pq : SourcePair × CentralQuotient => quotientAction pq.1 pq.2) :=
  ((quotientContinuous.continuous.comp continuous_fst.fst).mul continuous_snd).mul
    (quotientContinuous.continuous.comp continuous_fst.snd).inv

def projectiveAction (p : SourcePair) (x : RP3) : RP3 :=
  centralProjectiveHomeomorph (quotientAction p (centralProjectiveHomeomorph.symm x))

@[simp] theorem projectiveAction_quotient (p : SourcePair) (q : CentralQuotient) :
    projectiveAction p (centralProjectiveHomeomorph q) =
      centralProjectiveHomeomorph (quotientAction p q) := by
  unfold projectiveAction
  rw [Homeomorph.symm_apply_apply]

theorem projectiveHomeomorph_source (u : SU2) :
    centralProjectiveHomeomorph (quotientContinuous u) = sourceProjection u :=
  projectiveDescend_apply u

/-- The independent projective-space action commutes with the source projection. -/
theorem projectiveAction_source (p : SourcePair) (u : SU2) :
    projectiveAction p (sourceProjection u) = sourceProjection (sourceAction p u) := by
  rw [← projectiveHomeomorph_source u, projectiveAction_quotient,
    quotientAction_source, projectiveHomeomorph_source]

theorem projectiveAction_sphere (p : SourcePair) (x : Sphere3) :
    projectiveAction p (sphereProjection x) = sphereProjection (sphereAction p x) := by
  obtain ⟨u, rfl⟩ := sourceSphereHomeomorph.surjective x
  rw [sphereAction_source]
  exact projectiveAction_source p u

@[simp] theorem projectiveAction_one (x : RP3) : projectiveAction 1 x = x := by
  rw [projectiveAction, quotientAction_one, Homeomorph.apply_symm_apply]

theorem projectiveAction_mul (p q : SourcePair) (x : RP3) :
    projectiveAction (p * q) x = projectiveAction p (projectiveAction q x) := by
  unfold projectiveAction
  rw [Homeomorph.symm_apply_apply, quotientAction_mul]

@[instance_reducible] def projectiveMulAction : MulAction SourcePair RP3 where
  smul := projectiveAction
  one_smul := projectiveAction_one
  mul_smul := projectiveAction_mul

theorem projectiveAction_continuous :
    Continuous (fun px : SourcePair × RP3 => projectiveAction px.1 px.2) := by
  have hp : Continuous (fun px : SourcePair × RP3 =>
      (px.1, centralProjectiveHomeomorph.symm px.2)) :=
    continuous_fst.prodMk (centralProjectiveHomeomorph.symm.continuous.comp continuous_snd)
  have ha := quotientAction_continuous.comp hp
  simpa only [Function.comp_def, projectiveAction] using
    centralProjectiveHomeomorph.continuous.comp ha

/-- The same multiplication is expressed in the unit quaternions, not in an
independent group chosen to fit the desired action. -/
def quaternionAction (p : SourcePair) (q : unitary ℍ) : unitary ℍ :=
  unitaryEquiv.symm p.1 * q * (unitaryEquiv.symm p.2)⁻¹

theorem quaternionAction_source (p : SourcePair) (q : unitary ℍ) :
    unitaryEquiv (quaternionAction p q) = sourceAction p (unitaryEquiv q) := by
  simp only [quaternionAction, sourceAction, map_mul, map_inv,
    ContinuousMulEquiv.apply_symm_apply]

theorem sourceSphere_unitary (q : unitary ℍ) :
    sourceSphereHomeomorph (unitaryEquiv q) = unitarySphereHomeomorph q := by
  change unitarySphereHomeomorph (unitaryEquiv.symm (unitaryEquiv q)) = _
  rw [ContinuousMulEquiv.symm_apply_apply]

theorem sphereAction_quaternion (p : SourcePair) (q : unitary ℍ) :
    sphereAction p (unitarySphereHomeomorph q) =
      unitarySphereHomeomorph (quaternionAction p q) := by
  rw [← sourceSphere_unitary q, sphereAction_source, ← quaternionAction_source,
    sourceSphere_unitary]

/-- Unit left and right factors preserve the full quaternion distance. -/
theorem quaternionAction_dist (p : SourcePair) (q r : unitary ℍ) :
    dist (quaternionAction p q : ℍ) (quaternionAction p r : ℍ) = dist (q : ℍ) (r : ℍ) := by
  have ha : ‖(unitaryEquiv.symm p.1 : ℍ)‖ = 1 :=
    (mem_unitary_iff_norm _).mp (unitaryEquiv.symm p.1).property
  have hb : ‖(((unitaryEquiv.symm p.2)⁻¹ : unitary ℍ) : ℍ)‖ = 1 :=
    (mem_unitary_iff_norm _).mp ((unitaryEquiv.symm p.2)⁻¹).property
  rw [dist_eq_norm, dist_eq_norm]
  change ‖(unitaryEquiv.symm p.1 : ℍ) * (q : ℍ) *
      (((unitaryEquiv.symm p.2)⁻¹ : unitary ℍ) : ℍ) -
    (unitaryEquiv.symm p.1 : ℍ) * (r : ℍ) *
      (((unitaryEquiv.symm p.2)⁻¹ : unitary ℍ) : ℍ)‖ = ‖(q : ℍ) - (r : ℍ)‖
  rw [← sub_mul, ← mul_sub, norm_mul, norm_mul, ha, hb, one_mul, mul_one]

theorem quaternionAction_isometry (p : SourcePair) : Isometry (quaternionAction p) :=
  isometry_iff_dist_eq.mpr (quaternionAction_dist p)

theorem unitarySphere_isometry : Isometry unitarySphereHomeomorph := by
  apply isometry_iff_dist_eq.mpr
  intro q r
  change dist (Quaternion.linearIsometryEquivTuple (q : ℍ))
    (Quaternion.linearIsometryEquivTuple (r : ℍ)) = dist (q : ℍ) (r : ℍ)
  exact Quaternion.linearIsometryEquivTuple.dist_map q r

/-- Each constructed sphere action is an isometry. This does not classify all
sphere isometries or identify a covering of the orthogonal group. -/
theorem sphereAction_isometry (p : SourcePair) : Isometry (sphereAction p) := by
  apply isometry_iff_dist_eq.mpr
  intro x y
  obtain ⟨q, rfl⟩ := unitarySphereHomeomorph.surjective x
  obtain ⟨r, rfl⟩ := unitarySphereHomeomorph.surjective y
  rw [sphereAction_quaternion, sphereAction_quaternion]
  calc
    dist (unitarySphereHomeomorph (quaternionAction p q))
        (unitarySphereHomeomorph (quaternionAction p r)) =
        dist (quaternionAction p q) (quaternionAction p r) :=
      unitarySphere_isometry.dist_eq _ _
    _ = dist q r := (quaternionAction_isometry p).dist_eq q r
    _ = dist (unitarySphereHomeomorph q) (unitarySphereHomeomorph r) :=
      (unitarySphere_isometry.dist_eq q r).symm

/-- Fixing the identity forces equal factors; fixing every source point then
forces this common factor into the entire centre, already classified upstream. -/
theorem sourceAction_trivial_iff (p : SourcePair) :
    (∀ u : SU2, sourceAction p u = u) ↔
      p.1 = p.2 ∧ p.1 ∈ Subgroup.center SU2 := by
  constructor
  · intro hp
    have hab : p.1 = p.2 := mul_inv_eq_one.mp (by simpa [sourceAction] using hp 1)
    refine ⟨hab, Subgroup.mem_center_iff.mpr ?_⟩
    intro u
    have heq := congrArg (fun v : SU2 => v * p.1) (hp u)
    simpa only [sourceAction, ← hab, mul_assoc, inv_mul_cancel, mul_one] using heq.symm
  · rintro ⟨hab, ha⟩ u
    change p.1 * u * p.2⁻¹ = u
    rw [← hab, ← Subgroup.mem_center_iff.mp ha u, mul_assoc, mul_inv_cancel, mul_one]

theorem sourceAction_kernel (p : SourcePair) :
    (∀ u : SU2, sourceAction p u = u) ↔
      p = (1, 1) ∨ p = (negativeIdentity, negativeIdentity) := by
  rw [sourceAction_trivial_iff, mem_centre_iff]
  constructor
  · rintro ⟨hab, ha | ha⟩
    · exact Or.inl (Prod.ext ha (hab.symm.trans ha))
    · exact Or.inr (Prod.ext ha (hab.symm.trans ha))
  · rintro (rfl | rfl)
    · exact ⟨rfl, Or.inl rfl⟩
    · exact ⟨rfl, Or.inr rfl⟩

theorem sphereAction_trivial_iff_source (p : SourcePair) :
    (∀ x : Sphere3, sphereAction p x = x) ↔ ∀ u : SU2, sourceAction p u = u := by
  constructor
  · intro hp u
    apply sourceSphereHomeomorph.injective
    simpa only [sphereAction_source] using hp (sourceSphereHomeomorph u)
  · intro hp x
    rw [sphereAction, hp, Homeomorph.apply_symm_apply]

theorem sphereAction_kernel (p : SourcePair) :
    (∀ x : Sphere3, sphereAction p x = x) ↔
      p = (1, 1) ∨ p = (negativeIdentity, negativeIdentity) := by
  rw [sphereAction_trivial_iff_source, sourceAction_kernel]

theorem sphereAction_kernel_set :
    {p : SourcePair | ∀ x : Sphere3, sphereAction p x = x} =
      {(1, 1), (negativeIdentity, negativeIdentity)} := by
  ext p
  simp only [Set.mem_ofPred_eq, sphereAction_kernel, Set.mem_insert_iff, Set.mem_singleton_iff]

/-- Connectedness comes from the independent sphere and the proved source
homeomorphism. It is not imposed as a hypothesis on the projective kernel. -/
theorem source_connected : ConnectedSpace SU2 := by
  have hrank : 1 < Module.rank ℝ ResponseVector := by
    rw [← Module.finrank_eq_rank ℝ ResponseVector, finrank_euclideanSpace_fin]
    norm_num
  let : ConnectedSpace Sphere3 :=
    Subtype.connectedSpace (isConnected_sphere hrank (0 : ResponseVector)
      (r := 1) (by norm_num))
  exact sourceSphereHomeomorph.symm.surjective.connectedSpace
    sourceSphereHomeomorph.symm.continuous

/-- The source displacement measures the possible point-dependent central sign. -/
def displacement (p : SourcePair) (u : SU2) : SU2 := sourceAction p u * u⁻¹

theorem displacement_continuous (p : SourcePair) : Continuous (displacement p) :=
  (sourceAction_continuous_fixed p).mul continuous_inv

theorem projective_kernel_displacement_pair (p : SourcePair)
    (hp : ∀ x : RP3, projectiveAction p x = x) (u : SU2) :
    displacement p u = 1 ∨ displacement p u = negativeIdentity := by
  have hproj : sourceProjection (sourceAction p u) = sourceProjection u :=
    (projectiveAction_source p u).symm.trans (hp (sourceProjection u))
  rcases (sourceProjection_eq_iff _ _).mp hproj with hu | hu
  · left
    simp only [displacement, hu, mul_inv_cancel]
  · right
    simp only [displacement, hu, mul_assoc, mul_inv_cancel, mul_one]

/-- A projectively trivial action cannot choose a different central sign at
different source points: its displacement is continuous into a discrete pair. -/
theorem projective_kernel_displacement_constant (p : SourcePair)
    (hp : ∀ x : RP3, projectiveAction p x = x) (u : SU2) :
    displacement p u = displacement p 1 := by
  let : ConnectedSpace SU2 := source_connected
  apply (isPreconnected_univ : IsPreconnected (Set.univ : Set SU2)).constant_of_mapsTo
    (((Set.finite_singleton negativeIdentity).insert (1 : SU2)).isDiscrete)
    (displacement_continuous p).continuousOn ?_ (Set.mem_univ u) (Set.mem_univ 1)
  intro v _
  exact (show displacement p v = 1 ∨ displacement p v = negativeIdentity from
    projective_kernel_displacement_pair p hp v)

theorem projectiveAction_trivial_iff_centres (p : SourcePair) :
    (∀ x : RP3, projectiveAction p x = x) ↔
      p.1 ∈ Subgroup.center SU2 ∧ p.2 ∈ Subgroup.center SU2 := by
  constructor
  · intro hp
    have hdiag : ∀ u : SU2, sourceAction (p.2, p.2) u = u := by
      intro u
      have hconst := projective_kernel_displacement_constant p hp u
      have hcancel := congrArg (fun v : SU2 => p.2 * p.1⁻¹ * v * u) hconst
      simpa [displacement, sourceAction, mul_assoc] using hcancel
    have hb : p.2 ∈ Subgroup.center SU2 :=
      ((sourceAction_trivial_iff (p.2, p.2)).mp hdiag).2
    have hdelta : p.1 * p.2⁻¹ ∈ Subgroup.center SU2 := by
      apply (mem_centre_iff _).mpr
      simpa [displacement, sourceAction] using projective_kernel_displacement_pair p hp 1
    have ha : p.1 ∈ Subgroup.center SU2 := by
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using
        (Subgroup.center SU2).mul_mem hdelta hb
    exact ⟨ha, hb⟩
  · rintro ⟨ha, hb⟩ x
    have hqa : quotientMap p.1 = 1 := (quotientMap_eq_one_iff _).mpr ((mem_centre_iff _).mp ha)
    have hqb : quotientMap p.2 = 1 := (quotientMap_eq_one_iff _).mpr ((mem_centre_iff _).mp hb)
    simp only [projectiveAction, quotientAction, hqa, hqb, inv_one, one_mul, mul_one,
      Homeomorph.apply_symm_apply]

/-- The four independent central pairs, rather than just the diagonal pair,
are precisely the kernel on the independent real projective space. -/
theorem projectiveAction_kernel (p : SourcePair) :
    (∀ x : RP3, projectiveAction p x = x) ↔
      p = (1, 1) ∨ p = (1, negativeIdentity) ∨
        p = (negativeIdentity, 1) ∨ p = (negativeIdentity, negativeIdentity) := by
  rw [projectiveAction_trivial_iff_centres, mem_centre_iff, mem_centre_iff]
  constructor
  · rintro ⟨ha | ha, hb | hb⟩
    · exact Or.inl (Prod.ext ha hb)
    · exact Or.inr (Or.inl (Prod.ext ha hb))
    · exact Or.inr (Or.inr (Or.inl (Prod.ext ha hb)))
    · exact Or.inr (Or.inr (Or.inr (Prod.ext ha hb)))
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨Or.inl rfl, Or.inl rfl⟩
    · exact ⟨Or.inl rfl, Or.inr rfl⟩
    · exact ⟨Or.inr rfl, Or.inl rfl⟩
    · exact ⟨Or.inr rfl, Or.inr rfl⟩

theorem projectiveAction_kernel_set :
    {p : SourcePair | ∀ x : RP3, projectiveAction p x = x} =
      {(1, 1), (1, negativeIdentity), (negativeIdentity, 1),
        (negativeIdentity, negativeIdentity)} := by
  ext p
  simp only [Set.mem_ofPred_eq, projectiveAction_kernel, Set.mem_insert_iff, Set.mem_singleton_iff]

theorem negativeIdentity_inv : negativeIdentity⁻¹ = negativeIdentity := by
  have heq := congrArg (fun u : SU2 => negativeIdentity⁻¹ * u) negativeIdentity_sq
  simpa only [← mul_assoc, inv_mul_cancel, one_mul, mul_one] using heq.symm

theorem sourceAction_left_central (u : SU2) :
    sourceAction (negativeIdentity, 1) u = negativeIdentity * u := by
  simp only [sourceAction, inv_one, mul_one]

theorem sourceAction_right_central (u : SU2) :
    sourceAction (1, negativeIdentity) u = negativeIdentity * u := by
  simp only [sourceAction, one_mul, negativeIdentity_inv]
  exact Subgroup.mem_center_iff.mp negativeIdentity_mem_centre u

theorem sphereAction_left_central (x : Sphere3) :
    (sphereAction (negativeIdentity, 1) x : ResponseVector) = -(x : ResponseVector) := by
  rw [sphereAction, sourceAction_left_central, sourceSphere_central,
    Homeomorph.apply_symm_apply]

theorem sphereAction_right_central (x : Sphere3) :
    (sphereAction (1, negativeIdentity) x : ResponseVector) = -(x : ResponseVector) := by
  rw [sphereAction, sourceAction_right_central, sourceSphere_central,
    Homeomorph.apply_symm_apply]

theorem sphereAction_diagonal_central (x : Sphere3) :
    sphereAction (negativeIdentity, negativeIdentity) x = x :=
  (sphereAction_kernel _).mpr (Or.inr rfl) x

end GeneratedFoundations.Geometry.SourceLeftRightAction

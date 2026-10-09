module

public import GeneratedFoundations.Geometry.SourceSpecialOrthogonal
public import GeneratedFoundations.Geometry.SourceLeftRightAction
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Surjectivity of the generated quaternion action onto the orthogonal group

Every real linear isometry of the actual quaternion amplitude carrier is
either a left--right unit-quaternion action or such an action followed by
quaternion conjugation. This follows from the library's finite reflection
factorization, with each reflection calculated on the actual amplitudes.
The second form has determinant minus one. Thus the determinant-one
isometries are exactly the generated left--right actions.

The source-matrix product group maps onto this full special orthogonal
group, with the previously computed diagonal two-element kernel. The
independent sphere action is the restriction of this same representation.
The quotient isomorphism below is an algebraic group isomorphism. This
file does not assert a topological covering map, simple connectedness, or
an identification with the library's separately defined Clifford spin group.
-/

@[expose] public section

noncomputable section

open scoped Quaternion RealInnerProductSpace
open GeneratedFoundations.Geometry.SourceQuaternionAmplitude
open GeneratedFoundations.Geometry.SourceInvariantMetric
open GeneratedFoundations.Geometry.SourceSpecialOrthogonal
open GeneratedFoundations.Geometry.SourceLeftRightAction
open GeneratedFoundations.Geometry.SourceSpinCentre

namespace GeneratedFoundations.Geometry.SourceOrthogonalCover

/-- Conjugation is a real linear isometry of the complete amplitude space. -/
def quaternionStar : ℍ ≃ₗᵢ[ℝ] ℍ where
  toFun := star
  invFun := star
  left_inv := star_star
  right_inv := star_star
  map_add' := star_add
  map_smul' a x := Quaternion.star_smul a x
  norm_map' := Quaternion.norm_star

@[simp] theorem quaternionStar_apply (x : ℍ) : quaternionStar x = star x := rfl

theorem quaternionStar_square : quaternionStar * quaternionStar = 1 := by
  apply LinearIsometryEquiv.ext
  intro x
  exact star_star x

theorem quaternionStar_matrix :
    LinearMap.toMatrix quaternionBasis quaternionBasis quaternionStar.toLinearMap =
      Matrix.diagonal (![1, -1, -1, -1] : Fin 4 → ℝ) := by
  ext i j
  rw [LinearMap.toMatrix_apply, quaternionBasis_apply]
  change (![ (star (sourceAxis j)).re, (star (sourceAxis j)).imI,
    (star (sourceAxis j)).imJ, (star (sourceAxis j)).imK] : Fin 4 → ℝ) i = _
  fin_cases i <;> fin_cases j <;> norm_num [sourceAxis, Matrix.diagonal]

theorem quaternionStar_det : quaternionStar.toLinearMap.det = -1 := by
  rw [← LinearMap.det_toMatrix quaternionBasis, quaternionStar_matrix,
    Matrix.det_diagonal, Fin.prod_univ_four]
  norm_num

theorem leftRight_one : leftRight 1 1 = 1 := by
  apply LinearIsometryEquiv.ext
  intro x
  simp only [leftRight_apply, OneMemClass.coe_one, star_one, one_mul, mul_one,
    LinearIsometryEquiv.coe_one, id_eq]

theorem leftRight_mul (a b c d : unitary ℍ) :
    leftRight a b * leftRight c d = leftRight (a * c) (b * d) := by
  apply LinearIsometryEquiv.ext
  intro x
  simp only [LinearIsometryEquiv.coe_mul, Function.comp_apply, leftRight_apply,
    Submonoid.coe_mul, star_mul, mul_assoc]

theorem quaternionStar_leftRight (a b : unitary ℍ) :
    quaternionStar * leftRight a b = leftRight b a * quaternionStar := by
  apply LinearIsometryEquiv.ext
  intro x
  simp only [LinearIsometryEquiv.coe_mul, Function.comp_apply,
    quaternionStar_apply, leftRight_apply, star_mul, star_star, mul_assoc]

theorem conjugated_mul_leftRight (a b c d : unitary ℍ) :
    (leftRight a b * quaternionStar) * leftRight c d =
      leftRight (a * d) (b * c) * quaternionStar := by
  rw [mul_assoc, quaternionStar_leftRight, ← mul_assoc, leftRight_mul]

theorem conjugated_mul_conjugated (a b c d : unitary ℍ) :
    (leftRight a b * quaternionStar) * (leftRight c d * quaternionStar) =
      leftRight (a * d) (b * c) := by
  rw [← mul_assoc, conjugated_mul_leftRight, mul_assoc,
    quaternionStar_square, mul_one]

/-- Positive normalization is performed on the given reflection direction. -/
def normalizedUnit (v : ℍ) (hv : v ≠ 0) : unitary ℍ :=
  ⟨‖v‖⁻¹ • v, (mem_unitary_iff_norm _).mpr (by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg v)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)])⟩

theorem normalizedUnit_span (v : ℍ) (hv : v ≠ 0) :
    (ℝ ∙ (normalizedUnit v hv : ℍ)) = ℝ ∙ v := by
  change (ℝ ∙ (‖v‖⁻¹ • v)) = ℝ ∙ v
  exact Submodule.span_singleton_smul_eq
    (isUnit_iff_ne_zero.mpr (inv_ne_zero (norm_ne_zero_iff.mpr hv))) v

theorem normalizedUnit_synthesis (v : ℍ) (hv : v ≠ 0) :
    ‖v‖ • (normalizedUnit v hv : ℍ) = v := by
  change ‖v‖ • (‖v‖⁻¹ • v) = v
  rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul]

/-- Reflection in the hyperplane normal to a unit amplitude, calculated
using its quaternion product and the original real inner product. -/
theorem reflection_unit_apply (u : unitary ℍ) (x : ℍ) :
    Submodule.reflection (ℝ ∙ (u : ℍ))ᗮ x = -(u : ℍ) * star x * (u : ℍ) := by
  have hu : ‖(u : ℍ)‖ = 1 := (mem_unitary_iff_norm _).mp u.property
  have hsum : (u : ℍ) * star x + x * star (u : ℍ) =
      ((2 * inner ℝ (u : ℍ) x : ℝ) : ℍ) := by
    simpa only [star_mul, star_star, Quaternion.inner_def] using
      Quaternion.self_add_star' ((u : ℍ) * star x)
  have hm := congrArg (fun y : ℍ => y * (u : ℍ)) hsum
  rw [add_mul, mul_assoc x, Unitary.coe_star_mul_self, mul_one,
    Quaternion.coe_mul_eq_smul] at hm
  have hproduct : (u : ℍ) * star x * (u : ℍ) =
      (2 * inner ℝ (u : ℍ) x) • (u : ℍ) - x := eq_sub_iff_add_eq.mpr hm
  rw [Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply,
    hu, RCLike.ofReal_one, one_pow, div_one]
  calc
    -(2 • inner ℝ (u : ℍ) x • (u : ℍ) - x) =
        -((2 * inner ℝ (u : ℍ) x) • (u : ℍ) - x) := by
      simp only [two_smul, two_mul, add_smul]
    _ = -((u : ℍ) * star x * (u : ℍ)) := congrArg Neg.neg hproduct.symm
    _ = -(u : ℍ) * star x * (u : ℍ) := by rw [neg_mul, neg_mul]

theorem reflection_unit (u : unitary ℍ) :
    Submodule.reflection (ℝ ∙ (u : ℍ))ᗮ =
      leftRight (-u) (star u) * quaternionStar := by
  apply LinearIsometryEquiv.ext
  intro x
  change Submodule.reflection (ℝ ∙ (u : ℍ))ᗮ x =
    ((-u : unitary ℍ) : ℍ) * star x * star ((star u : unitary ℍ) : ℍ)
  simpa only [Unitary.coe_neg, Unitary.coe_star, star_star] using reflection_unit_apply u x

theorem reflection_nonzero (v : ℍ) (hv : v ≠ 0) :
    Submodule.reflection (ℝ ∙ v)ᗮ =
      leftRight (-normalizedUnit v hv) (star (normalizedUnit v hv)) * quaternionStar := by
  have he := congrArg (fun K : Submodule ℝ ℍ => Submodule.reflection Kᗮ)
    (normalizedUnit_span v hv)
  exact he.symm.trans (reflection_unit (normalizedUnit v hv))

theorem reflection_zero :
    Submodule.reflection (ℝ ∙ (0 : ℍ))ᗮ = 1 := by
  apply LinearIsometryEquiv.ext
  intro x
  change Submodule.reflection (ℝ ∙ (0 : ℍ))ᗮ x = x
  apply Submodule.reflection_mem_subspace_eq_self
  simp

/-- No tensor or left--right form is assumed for the competing isometry. -/
theorem reflection_product_forms (l : List ℍ) :
    ∃ a b : unitary ℍ,
      (l.map (fun v => Submodule.reflection (ℝ ∙ v)ᗮ)).prod = leftRight a b ∨
      (l.map (fun v => Submodule.reflection (ℝ ∙ v)ᗮ)).prod =
        leftRight a b * quaternionStar := by
  induction l with
  | nil =>
      refine ⟨1, 1, Or.inl ?_⟩
      simpa only [List.map_nil, List.prod_nil] using leftRight_one.symm
  | cons v l ih =>
      simp only [List.map_cons, List.prod_cons]
      by_cases hv : v = 0
      · rw [hv, reflection_zero, one_mul]
        exact ih
      · rw [reflection_nonzero v hv]
        obtain ⟨a, b, h | h⟩ := ih
        · refine ⟨(-normalizedUnit v hv) * b, star (normalizedUnit v hv) * a,
            Or.inr ?_⟩
          rw [h, conjugated_mul_leftRight]
        · refine ⟨(-normalizedUnit v hv) * b, star (normalizedUnit v hv) * a,
            Or.inl ?_⟩
          rw [h, conjugated_mul_conjugated]

theorem real_isometry_forms (e : ℍ ≃ₗᵢ[ℝ] ℍ) :
    ∃ a b : unitary ℍ, e = leftRight a b ∨ e = leftRight a b * quaternionStar := by
  obtain ⟨l, _, he⟩ := e.reflections_generate_dim
  rw [he]
  exact reflection_product_forms l

theorem isometry_det_mul (e f : ℍ ≃ₗᵢ[ℝ] ℍ) :
    (e * f).toLinearMap.det = e.toLinearMap.det * f.toLinearMap.det :=
  LinearMap.det_comp e.toLinearMap f.toLinearMap

theorem conjugated_leftRight_det (a b : unitary ℍ) :
    (leftRight a b * quaternionStar).toLinearMap.det = -1 := by
  rw [isometry_det_mul, leftRight_det, quaternionStar_det, one_mul]

/-- Every orientation-preserving real isometry is generated by two source
unit amplitudes; determinant one is not used merely as a necessary test. -/
theorem leftRight_surjective (e : ℍ ≃ₗᵢ[ℝ] ℍ) (he : e.toLinearMap.det = 1) :
    ∃ a b : unitary ℍ, leftRight a b = e := by
  obtain ⟨a, b, h | h⟩ := real_isometry_forms e
  · exact ⟨a, b, h.symm⟩
  · rw [h, conjugated_leftRight_det] at he
    norm_num at he

theorem leftRight_exists_iff (e : ℍ ≃ₗᵢ[ℝ] ℍ) :
    (∃ a b : unitary ℍ, leftRight a b = e) ↔ e.toLinearMap.det = 1 := by
  constructor
  · rintro ⟨a, b, rfl⟩
    exact leftRight_det a b
  · exact leftRight_surjective e

/-- Surjectivity also gives the reverse passage between the source and
special-orthogonal metric comparison classes. -/
theorem sourceMetric_toSpecialOrthogonal {G : MetricFamily}
    (hG : IsCalibratedSourceMetric G) : IsCalibratedSpecialOrthogonalMetric G where
  invariant hr e he q h k := by
    obtain ⟨a, b, rfl⟩ := leftRight_surjective e he
    simpa only [unitAction_leftRight] using hG.invariant hr a b q h k
  radial := hG.radial
  homothety := hG.homothety
  unit_angular := hG.unit_angular

theorem calibratedMetric_iff (G : MetricFamily) :
    IsCalibratedSourceMetric G ↔ IsCalibratedSpecialOrthogonalMetric G :=
  ⟨sourceMetric_toSpecialOrthogonal, fun hG => hG.toSourceMetric⟩

/-- The target is all determinant-one real linear isometries of the
four-dimensional amplitude space, independently of the source action. -/
def specialOrthogonal : Subgroup (ℍ ≃ₗᵢ[ℝ] ℍ) where
  carrier := {e | e.toLinearMap.det = 1}
  one_mem' := LinearMap.det_id
  mul_mem' {e f} he hf := by
    change (e * f).toLinearMap.det = 1
    rw [isometry_det_mul, he, hf, one_mul]
  inv_mem' {e} he := by
    have h : (e⁻¹ * e).toLinearMap.det = 1 := by
      rw [inv_mul_cancel]
      exact LinearMap.det_id
    rw [isometry_det_mul, he, mul_one] at h
    exact h

def sourceRepresentation : SourcePair →* (ℍ ≃ₗᵢ[ℝ] ℍ) where
  toFun p := leftRight (unitaryEquiv.symm p.1) (unitaryEquiv.symm p.2)
  map_one' := by
    change leftRight (unitaryEquiv.symm 1) (unitaryEquiv.symm 1) = 1
    simp only [map_one, leftRight_one]
  map_mul' p q := by
    change leftRight (unitaryEquiv.symm (p.1 * q.1))
      (unitaryEquiv.symm (p.2 * q.2)) =
      leftRight (unitaryEquiv.symm p.1) (unitaryEquiv.symm p.2) *
        leftRight (unitaryEquiv.symm q.1) (unitaryEquiv.symm q.2)
    simp only [map_mul, leftRight_mul]

theorem sourceRepresentation_unit (p : SourcePair) (q : unitary ℍ) :
    sourceRepresentation p (q : ℍ) = (quaternionAction p q : ℍ) := rfl

theorem sourceRepresentation_det (p : SourcePair) :
    (sourceRepresentation p).toLinearMap.det = 1 :=
  leftRight_det _ _

/-- Restriction to the independent sphere recovers the already constructed
source action, with its actual quaternion-to-Euclidean coordinates. -/
theorem sourceRepresentation_sphere (p : SourcePair) (x : Sphere3) :
    Quaternion.linearIsometryEquivTuple
        (sourceRepresentation p (Quaternion.linearIsometryEquivTuple.symm x)) =
      (sphereAction p x : EuclideanSpace ℝ (Fin 4)) := by
  obtain ⟨q, rfl⟩ := unitarySphereHomeomorph.surjective x
  rw [sphereAction_quaternion]
  change Quaternion.linearIsometryEquivTuple
      (sourceRepresentation p
        (Quaternion.linearIsometryEquivTuple.symm (Quaternion.linearIsometryEquivTuple q))) =
    Quaternion.linearIsometryEquivTuple (quaternionAction p q)
  rw [Quaternion.linearIsometryEquivTuple.symm_apply_apply, sourceRepresentation_unit]

theorem sourceRepresentation_eq_one_iff (p : SourcePair) :
    sourceRepresentation p = 1 ↔ ∀ u, sourceAction p u = u := by
  constructor
  · intro hp u
    obtain ⟨q, rfl⟩ := unitaryEquiv.surjective u
    have hq : quaternionAction p q = q := by
      apply Subtype.ext
      change sourceRepresentation p (q : ℍ) = (q : ℍ)
      simp only [hp, LinearIsometryEquiv.coe_one, id_eq]
    rw [← quaternionAction_source, hq]
  · intro hp
    have hunit (q : unitary ℍ) : sourceRepresentation p (q : ℍ) = (q : ℍ) := by
      rw [sourceRepresentation_unit]
      apply congrArg Subtype.val
      apply unitaryEquiv.injective
      rw [quaternionAction_source, hp]
    apply LinearIsometryEquiv.ext
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · change sourceRepresentation p x = x
      calc
        sourceRepresentation p x =
            sourceRepresentation p (‖x‖ • (normalizedUnit x hx : ℍ)) := by
          rw [normalizedUnit_synthesis]
        _ = ‖x‖ • (normalizedUnit x hx : ℍ) := by rw [map_smul, hunit]
        _ = x := normalizedUnit_synthesis x hx

/-- A surjective homomorphism onto the full special orthogonal group. -/
def sourceCover : SourcePair →* specialOrthogonal where
  toFun p := ⟨sourceRepresentation p, sourceRepresentation_det p⟩
  map_one' := Subtype.ext sourceRepresentation.map_one
  map_mul' p q := Subtype.ext (sourceRepresentation.map_mul p q)

theorem sourceCover_surjective : Function.Surjective sourceCover := by
  intro e
  obtain ⟨a, b, he⟩ := leftRight_surjective e e.property
  refine ⟨(unitaryEquiv a, unitaryEquiv b), ?_⟩
  apply Subtype.ext
  change leftRight (unitaryEquiv.symm (unitaryEquiv a))
    (unitaryEquiv.symm (unitaryEquiv b)) = e
  simpa only [ContinuousMulEquiv.symm_apply_apply] using he

theorem sourceCover_kernel_iff (p : SourcePair) :
    sourceCover p = 1 ↔ p = (1, 1) ∨ p = (negativeIdentity, negativeIdentity) := by
  have h : sourceCover p = 1 ↔ sourceRepresentation p = 1 :=
    ⟨fun hp => congrArg Subtype.val hp, fun hp => Subtype.ext hp⟩
  rw [h, sourceRepresentation_eq_one_iff, sourceAction_kernel]

theorem sourceCover_kernel :
    (sourceCover.ker : Set SourcePair) = {(1, 1), (negativeIdentity, negativeIdentity)} := by
  ext p
  change sourceCover p = 1 ↔ _
  rw [sourceCover_kernel_iff]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]

theorem sourceCover_fiber_iff (p q : SourcePair) :
    sourceCover p = sourceCover q ↔
      p = q ∨ p = (negativeIdentity, negativeIdentity) * q := by
  have h : sourceCover p = sourceCover q ↔ sourceCover (p * q⁻¹) = 1 := by
    rw [map_mul, map_inv, mul_inv_eq_one]
  rw [h, sourceCover_kernel_iff]
  change (p * q⁻¹ = 1 ∨ p * q⁻¹ = (negativeIdentity, negativeIdentity)) ↔ _
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]

/-- First isomorphism theorem for the actual source homomorphism. No
covering-space or smooth-group conclusion is encoded in this type. -/
def sourceQuotientEquiv : SourcePair ⧸ sourceCover.ker ≃* specialOrthogonal :=
  QuotientGroup.quotientKerEquivOfSurjective sourceCover sourceCover_surjective

end GeneratedFoundations.Geometry.SourceOrthogonalCover

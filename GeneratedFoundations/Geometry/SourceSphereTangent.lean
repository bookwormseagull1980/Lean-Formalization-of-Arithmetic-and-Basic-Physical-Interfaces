module

public import GeneratedFoundations.Geometry.SourcePolarMetric
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The actual sphere tangent spaces of the source amplitude

The sphere is the previously constructed unit sphere in four-dimensional
Euclidean space, with the library's analytic atlas. The differential of
its inclusion has image exactly the angular orthogonal complement and is
injective. Quaternion coordinates therefore identify its actual tangent
space continuously and linearly with the angular space used in the source
trace metric.

The radial--angular linear equivalence and the full polar trace formula
below act on these manifold tangent vectors. The metric is the pullback
of the amplitude inner product; the norm of a chart coordinate is not
identified with the induced sphere norm. These results do not yet assert
a global smooth polar-coordinate equivalence, a connection, or curvature.
-/

@[expose] public section

noncomputable section

open scoped Quaternion RealInnerProductSpace Manifold
open GeneratedFoundations.Operations.SourceSpinCorner (Mat2)
open GeneratedFoundations.Operations.SourceSpinCornerGroup (SU2)
open GeneratedFoundations.Geometry.SourceQuaternionAmplitude
open GeneratedFoundations.Geometry.SourcePolarMetric

namespace GeneratedFoundations.Geometry.SourceSphereTangent

abbrev Ambient := EuclideanSpace ℝ (Fin 4)

local instance : Fact (Module.finrank ℝ Ambient = 3 + 1) :=
  ⟨by simp [Ambient]⟩

abbrev SphereTangent (q : Sphere3) := TangentSpace (𝓡 3) q

/-- The existing source sphere expressed in its quaternion amplitude coordinates. -/
def quaternionPoint (q : Sphere3) : ℍ := Quaternion.linearIsometryEquivTuple.symm q

theorem quaternionPoint_norm (q : Sphere3) : ‖quaternionPoint q‖ = 1 := by
  rw [quaternionPoint, Quaternion.linearIsometryEquivTuple.symm.norm_map]
  exact mem_sphere_zero_iff_norm.mp q.property

theorem quaternionPoint_source (U : SU2) :
    quaternionPoint (sourceSphereHomeomorph U) = ofMatrix U := by
  rw [quaternionPoint, sourceSphere_apply,
    Quaternion.linearIsometryEquivTuple.symm_apply_apply]

/-- This is the derivative of the library sphere inclusion, not an assigned tangent map. -/
def inclusionDerivative (q : Sphere3) : SphereTangent q →L[ℝ] Ambient :=
  mvfderiv (𝓡 3) (Subtype.val : Sphere3 → Ambient) q

theorem inclusionDerivative_range (q : Sphere3) :
    (inclusionDerivative q).range = (ℝ ∙ (q : Ambient))ᗮ :=
  range_mvfderiv_subtypeVal q

theorem inclusionDerivative_injective (q : Sphere3) :
    Function.Injective (inclusionDerivative q) :=
  injective_mvfderiv_subtypeVal_sphere q

/-- The same actual tangent derivative in quaternion coordinates. -/
def quaternionDerivative (q : Sphere3) : SphereTangent q →L[ℝ] ℍ :=
  Quaternion.linearIsometryEquivTuple.symm.toContinuousLinearMap.comp
    (inclusionDerivative q)

theorem quaternionDerivative_angular (q : Sphere3) (v : SphereTangent q) :
    quaternionDerivative q v ∈ angularSpace (quaternionPoint q) := by
  have hv : inclusionDerivative q v ∈ (ℝ ∙ (q : Ambient))ᗮ := by
    rw [← inclusionDerivative_range q]
    exact ⟨v, rfl⟩
  apply mem_angularSpace.mpr
  change inner ℝ (Quaternion.linearIsometryEquivTuple.symm (q : Ambient))
    (Quaternion.linearIsometryEquivTuple.symm (inclusionDerivative q v)) = 0
  rw [Quaternion.linearIsometryEquivTuple.symm.inner_map_map]
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp hv

def tangentAngularMap (q : Sphere3) :
    SphereTangent q →L[ℝ] angularSpace (quaternionPoint q) :=
  (quaternionDerivative q).codRestrict _ (quaternionDerivative_angular q)

@[simp] theorem tangentAngularMap_coe (q : Sphere3) (v : SphereTangent q) :
    (tangentAngularMap q v : ℍ) = quaternionDerivative q v := rfl

theorem tangentAngularMap_injective (q : Sphere3) :
    Function.Injective (tangentAngularMap q) := by
  intro v w hvw
  apply inclusionDerivative_injective q
  apply Quaternion.linearIsometryEquivTuple.symm.injective
  exact congrArg Subtype.val hvw

theorem tangentAngularMap_surjective (q : Sphere3) :
    Function.Surjective (tangentAngularMap q) := by
  intro v
  have hv : Quaternion.linearIsometryEquivTuple (v : ℍ) ∈
      (ℝ ∙ (q : Ambient))ᗮ := by
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    have hq : Quaternion.linearIsometryEquivTuple (quaternionPoint q) = (q : Ambient) :=
      Quaternion.linearIsometryEquivTuple.apply_symm_apply q
    rw [← hq, Quaternion.linearIsometryEquivTuple.inner_map_map]
    exact angular_inner (quaternionPoint q) v
  rw [← inclusionDerivative_range q] at hv
  obtain ⟨w, hw⟩ := hv
  change inclusionDerivative q w = Quaternion.linearIsometryEquivTuple (v : ℍ) at hw
  refine ⟨w, Subtype.ext ?_⟩
  change Quaternion.linearIsometryEquivTuple.symm (inclusionDerivative q w) = (v : ℍ)
  rw [hw, Quaternion.linearIsometryEquivTuple.symm_apply_apply]

/-- A continuous linear identification with the genuine manifold tangent fibre. -/
def tangentAngularEquiv (q : Sphere3) :
    SphereTangent q ≃L[ℝ] angularSpace (quaternionPoint q) :=
  (LinearEquiv.ofBijective (tangentAngularMap q).toLinearMap
    ⟨tangentAngularMap_injective q, tangentAngularMap_surjective q⟩).toContinuousLinearEquiv

@[simp] theorem tangentAngularEquiv_apply (q : Sphere3) (v : SphereTangent q) :
    tangentAngularEquiv q v = tangentAngularMap q v := rfl

theorem tangent_finrank (q : Sphere3) : Module.finrank ℝ (SphereTangent q) = 3 := by
  rw [(tangentAngularEquiv q).toLinearEquiv.finrank_eq]
  exact angular_finrank (quaternionPoint_norm q)

/-- The metric measured by the source is pulled back along the actual sphere inclusion. -/
def sphereMetric (q : Sphere3) (v w : SphereTangent q) : ℝ :=
  inner ℝ (quaternionDerivative q v) (quaternionDerivative q w)

theorem sphereMetric_eq_ambient (q : Sphere3) (v w : SphereTangent q) :
    sphereMetric q v w = inner ℝ (inclusionDerivative q v) (inclusionDerivative q w) :=
  Quaternion.linearIsometryEquivTuple.symm.inner_map_map _ _

theorem sphereMetric_pos (q : Sphere3) {v : SphereTangent q} (hv : v ≠ 0) :
    0 < sphereMetric q v v := by
  apply real_inner_self_pos.mpr
  intro hzero
  apply hv
  apply tangentAngularMap_injective q
  apply Subtype.ext
  simpa only [tangentAngularMap_coe, map_zero, Submodule.coe_zero] using hzero

def polarTangentMap (q : Sphere3) (r : ℝ) : (ℝ × SphereTangent q) →L[ℝ] ℍ :=
  ((polarLinear r (quaternionPoint q)).comp
    ((LinearMap.id : ℝ →ₗ[ℝ] ℝ).prodMap
      (tangentAngularMap q).toLinearMap)).toContinuousLinearMap

@[simp] theorem polarTangentMap_apply (q : Sphere3) (r : ℝ)
    (x : ℝ × SphereTangent q) :
    polarTangentMap q r x = x.1 • quaternionPoint q + r • quaternionDerivative q x.2 := rfl

/-- Every actual amplitude variation has unique radial and manifold-tangent coordinates. -/
def polarTangentEquiv (q : Sphere3) {r : ℝ} (hr : r ≠ 0) :
    (ℝ × SphereTangent q) ≃L[ℝ] ℍ :=
  (((LinearEquiv.refl ℝ ℝ).prodCongr (tangentAngularEquiv q).toLinearEquiv).trans
    (polarLinearEquiv (quaternionPoint_norm q) hr)).toContinuousLinearEquiv

@[simp] theorem polarTangentEquiv_apply (q : Sphere3) {r : ℝ} (hr : r ≠ 0)
    (x : ℝ × SphereTangent q) :
    polarTangentEquiv q hr x = polarTangentMap q r x := rfl

theorem polarTangent_existsUnique (q : Sphere3) {r : ℝ} (hr : r ≠ 0) (h : ℍ) :
    ∃! x : ℝ × SphereTangent q, polarTangentMap q r x = h := by
  refine ⟨(polarTangentEquiv q hr).symm h, (polarTangentEquiv q hr).apply_symm_apply h, ?_⟩
  intro x hx
  apply (polarTangentEquiv q hr).injective
  exact hx.trans ((polarTangentEquiv q hr).apply_symm_apply h).symm

theorem polarTangent_inner (q : Sphere3) (r : ℝ) (x y : ℝ × SphereTangent q) :
    inner ℝ (polarTangentMap q r x) (polarTangentMap q r y) =
      x.1 * y.1 + r ^ 2 * sphereMetric q x.2 y.2 :=
  polar_inner (quaternionPoint_norm q) r
    (x.1, tangentAngularMap q x.2) (y.1, tangentAngularMap q y.2)

/-- The same source matrix comparison evaluated on actual manifold tangent vectors. -/
theorem source_trace_polar_tangent (q : Sphere3) (r : ℝ)
    (x y : ℝ × SphereTangent q) :
    (Matrix.trace ((matrixMap (polarTangentMap q r x)).conjTranspose *
      matrixMap (polarTangentMap q r y))).re / 2 =
      x.1 * y.1 + r ^ 2 * sphereMetric q x.2 y.2 := by
  rw [trace_inner, polarTangent_inner]

theorem source_group_trace_polar_tangent (U : SU2) (r : ℝ)
    (x y : ℝ × SphereTangent (sourceSphereHomeomorph U)) :
    (Matrix.trace ((matrixMap (polarTangentMap (sourceSphereHomeomorph U) r x)).conjTranspose *
      matrixMap (polarTangentMap (sourceSphereHomeomorph U) r y))).re / 2 =
      x.1 * y.1 + r ^ 2 * sphereMetric (sourceSphereHomeomorph U) x.2 y.2 :=
  source_trace_polar_tangent (sourceSphereHomeomorph U) r x y

end GeneratedFoundations.Geometry.SourceSphereTangent

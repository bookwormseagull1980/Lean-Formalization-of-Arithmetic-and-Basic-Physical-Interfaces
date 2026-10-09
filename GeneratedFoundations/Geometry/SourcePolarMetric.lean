module

public import GeneratedFoundations.Geometry.SourceQuaternionAmplitude
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Matrix.Normed

/-!
# The polar trace metric on the generated amplitude space

The differential of the amplitude map `(r,q) ↦ r • q` identifies the radial
line and the angular orthogonal complement with the full quaternion space.
The normalized trace of the actual source matrices pulls back to
`s*t + r²*inner v w`. The velocity of a unit-sphere curve is orthogonal
to its position.
-/

@[expose] public section

noncomputable section

open scoped Quaternion RealInnerProductSpace Topology Matrix.Norms.Elementwise
open GeneratedFoundations.Operations.SourceSpinCorner
open GeneratedFoundations.Operations.SourceSpinCornerGroup
open GeneratedFoundations.Geometry.SourceQuaternionAmplitude

namespace GeneratedFoundations.Geometry.SourcePolarMetric

def angularSpace (q : ℍ) : Submodule ℝ ℍ := (ℝ ∙ q)ᗮ

theorem mem_angularSpace {q v : ℍ} :
    v ∈ angularSpace q ↔ inner ℝ q v = 0 :=
  Submodule.mem_orthogonal_singleton_iff_inner_right

theorem angular_inner (q : ℍ) (v : angularSpace q) : inner ℝ q (v : ℍ) = 0 :=
  mem_angularSpace.mp v.property

theorem unit_inner {q : ℍ} (hq : ‖q‖ = 1) : inner ℝ q q = 1 := by
  rw [real_inner_self_eq_norm_sq, hq, one_pow]

theorem angular_finrank {q : ℍ} (hq : ‖q‖ = 1) :
    Module.finrank ℝ (angularSpace q) = 3 := by
  have hqne : q ≠ 0 := by
    intro hz
    simp only [hz, norm_zero] at hq
    norm_num at hq
  have hd := (ℝ ∙ q).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton hqne, Quaternion.finrank_eq_four] at hd
  change 1 + Module.finrank ℝ (angularSpace q) = 4 at hd
  omega

/-- The differential of radial scaling on the sphere tangent space. -/
def polarLinear (r : ℝ) (q : ℍ) : (ℝ × angularSpace q) →ₗ[ℝ] ℍ where
  toFun x := x.1 • q + r • (x.2 : ℍ)
  map_add' x y := by
    change (x.1 + y.1) • q + r • ((x.2 : ℍ) + (y.2 : ℍ)) =
      (x.1 • q + r • (x.2 : ℍ)) + (y.1 • q + r • (y.2 : ℍ))
    simp only [add_smul, smul_add]
    abel
  map_smul' c x := by
    change (c * x.1) • q + r • (c • (x.2 : ℍ)) =
      c • (x.1 • q + r • (x.2 : ℍ))
    simp only [smul_add, smul_smul]
    rw [mul_comm r c]

@[simp] theorem polarLinear_apply (r : ℝ) (q : ℍ) (x : ℝ × angularSpace q) :
    polarLinear r q x = x.1 • q + r • (x.2 : ℍ) := rfl

theorem radial_coordinate {q : ℍ} (hq : ‖q‖ = 1) (r : ℝ)
    (x : ℝ × angularSpace q) : inner ℝ q (polarLinear r q x) = x.1 := by
  simp only [polarLinear_apply, inner_add_right, real_inner_smul_right,
    unit_inner hq, angular_inner, mul_one, mul_zero, add_zero]

def angularCoordinate {q : ℍ} (hq : ‖q‖ = 1) (r : ℝ) (h : ℍ) : angularSpace q :=
  ⟨r⁻¹ • (h - (inner ℝ q h) • q), by
    apply mem_angularSpace.mpr
    rw [real_inner_smul_right, inner_sub_right, real_inner_smul_right, unit_inner hq]
    ring⟩

/-- Every amplitude variation has unique radial and angular coordinates. -/
def polarLinearEquiv {q : ℍ} (hq : ‖q‖ = 1) {r : ℝ} (hr : r ≠ 0) :
    (ℝ × angularSpace q) ≃ₗ[ℝ] ℍ where
  toLinearMap := polarLinear r q
  invFun h := (inner ℝ q h, angularCoordinate hq r h)
  left_inv x := by
    apply Prod.ext
    · exact radial_coordinate hq r x
    · apply Subtype.ext
      change r⁻¹ • (polarLinear r q x - (inner ℝ q (polarLinear r q x)) • q) =
        (x.2 : ℍ)
      rw [radial_coordinate hq, polarLinear_apply, add_sub_cancel_left,
        smul_smul, inv_mul_cancel₀ hr, one_smul]
  right_inv h := by
    change (inner ℝ q h) • q + r • (r⁻¹ • (h - (inner ℝ q h) • q)) = h
    rw [smul_smul, mul_inv_cancel₀ hr, one_smul]
    abel

theorem polar_coordinates_existsUnique {q : ℍ} (hq : ‖q‖ = 1)
    {r : ℝ} (hr : r ≠ 0) (h : ℍ) :
    ∃! x : ℝ × angularSpace q, polarLinear r q x = h := by
  refine ⟨(polarLinearEquiv hq hr).symm h,
    (polarLinearEquiv hq hr).apply_symm_apply h, ?_⟩
  intro x hx
  apply (polarLinearEquiv hq hr).injective
  exact hx.trans ((polarLinearEquiv hq hr).apply_symm_apply h).symm

/-- The complete bilinear metric, including the vanishing mixed terms. -/
theorem polar_inner {q : ℍ} (hq : ‖q‖ = 1) (r : ℝ)
    (x y : ℝ × angularSpace q) :
    inner ℝ (polarLinear r q x) (polarLinear r q y) =
      x.1 * y.1 + r ^ 2 * inner ℝ (x.2 : ℍ) (y.2 : ℍ) := by
  have hx : inner ℝ (x.2 : ℍ) q = 0 := by
    rw [real_inner_comm]
    exact angular_inner q x.2
  simp only [polarLinear_apply, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, unit_inner hq,
    angular_inner, hx]
  ring

theorem polar_norm_sq {q : ℍ} (hq : ‖q‖ = 1) (r : ℝ)
    (x : ℝ × angularSpace q) :
    ‖polarLinear r q x‖ ^ 2 = x.1 ^ 2 + r ^ 2 * ‖(x.2 : ℍ)‖ ^ 2 := by
  simpa only [real_inner_self_eq_norm_sq, pow_two] using polar_inner hq r x x

/-- The metric is positive on every nonzero radial--angular variation. -/
theorem polar_metric_pos {q : ℍ} (hq : ‖q‖ = 1) {r : ℝ} (hr : r ≠ 0)
    {x : ℝ × angularSpace q} (hx : x ≠ 0) :
    0 < x.1 ^ 2 + r ^ 2 * ‖(x.2 : ℍ)‖ ^ 2 := by
  rw [← polar_norm_sq hq r x]
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  intro hz
  apply hx
  apply (polarLinearEquiv hq hr).injective
  rw [map_zero]
  change polarLinear r q x = 0
  exact hz

def sourceVariation (r : ℝ) (q : ℍ) (x : ℝ × angularSpace q) : Mat2 :=
  matrixMap (polarLinear r q x)

theorem source_trace_polar {q : ℍ} (hq : ‖q‖ = 1) (r : ℝ)
    (x y : ℝ × angularSpace q) :
    (Matrix.trace ((sourceVariation r q x).conjTranspose *
      sourceVariation r q y)).re / 2 =
      x.1 * y.1 + r ^ 2 * inner ℝ (x.2 : ℍ) (y.2 : ℍ) := by
  rw [sourceVariation, sourceVariation, trace_inner, polar_inner hq]

theorem source_unit_norm (U : SU2) : ‖ofMatrix U‖ = 1 :=
  (mem_unitary_iff_norm _).mp
    ((mem_unitary_iff_normSq _).mpr (normSq_of_specialUnitary U))

/-- The actual source group provides the unit angular amplitude. -/
theorem source_group_trace_polar (U : SU2) (r : ℝ)
    (x y : ℝ × angularSpace (ofMatrix U)) :
    (Matrix.trace ((sourceVariation r (ofMatrix U) x).conjTranspose *
      sourceVariation r (ofMatrix U) y)).re / 2 =
      x.1 * y.1 + r ^ 2 * inner ℝ (x.2 : ℍ) (y.2 : ℍ) :=
  source_trace_polar (source_unit_norm U) r x y

theorem unit_curve_derivative_orthogonal {u : ℝ → ℍ} {v : ℍ} {t : ℝ}
    (hu : HasDerivAt u v t) (hunit : ∀ s, ‖u s‖ = 1) :
    inner ℝ (u t) v = 0 := by
  have hnorm : (fun s => inner ℝ (u s) (u s)) = fun _ => (1 : ℝ) := by
    funext s
    exact unit_inner (hunit s)
  have hd := hu.inner ℝ hu
  rw [hnorm] at hd
  have hz := hd.unique (hasDerivAt_const t (1 : ℝ))
  rw [real_inner_comm (u t) v] at hz
  linarith

/-- The polar variation is the derivative of the actual amplitude curve. -/
theorem polar_curve_derivative {ρ : ℝ → ℝ} {u : ℝ → ℍ}
    {s t : ℝ} {v : ℍ} (hρ : HasDerivAt ρ s t) (hu : HasDerivAt u v t)
    (hunit : ∀ a, ‖u a‖ = 1) :
    HasDerivAt (fun a => ρ a • u a)
      (polarLinear (ρ t) (u t)
        (s, ⟨v, mem_angularSpace.mpr (unit_curve_derivative_orthogonal hu hunit)⟩)) t := by
  simpa only [polarLinear_apply, Pi.smul_apply, add_comm] using! hρ.smul hu

def matrixMapCLM : ℍ →L[ℝ] Mat2 := matrixMap.toLinearMap.toContinuousLinearMap

private theorem map_curve_derivative {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) {u : ℝ → E} {v : E} {t : ℝ}
    (hu : HasDerivAt u v t) :
    HasDerivAt (fun a => L (u a)) (L v) t :=
  L.hasFDerivAt.comp_hasDerivAt t hu

theorem source_curve_derivative {ρ : ℝ → ℝ} {u : ℝ → ℍ}
    {s t : ℝ} {v : ℍ} (hρ : HasDerivAt ρ s t) (hu : HasDerivAt u v t)
    (hunit : ∀ a, ‖u a‖ = 1) :
    HasDerivAt (fun a => matrixMap (ρ a • u a))
      (sourceVariation (ρ t) (u t)
        (s, ⟨v, mem_angularSpace.mpr (unit_curve_derivative_orthogonal hu hunit)⟩)) t := by
  have h := map_curve_derivative (E := ℍ) (F := Mat2) matrixMapCLM
    (polar_curve_derivative hρ hu hunit)
  simpa only [Function.comp_def, matrixMapCLM, LinearMap.coe_toContinuousLinearMap,
    sourceVariation] using! h

end GeneratedFoundations.Geometry.SourcePolarMetric

module

public import GeneratedFoundations.Geometry.SourcePolarMetric
public import Mathlib.Analysis.CStarAlgebra.Unitary.Maps
public import Mathlib.LinearAlgebra.BilinearForm.Basic

/-!
# Uniqueness of the calibrated source metric

A metric is expressed on actual quaternion amplitude variations. Left and
right source invariance, radial unit speed, Gaussian homothety and the
unit-orbit calibration determine its full bilinear form. Four source
conjugations eliminate the mixed terms; orthogonality is not an assumption.

The unit quaternions here are identified with the generated matrix group by
`SourceQuaternionAmplitude.unitaryEquiv`. The result concerns the pointwise
metric comparison class. It does not construct a manifold tangent bundle or
identify a Clifford spin group with an independently defined orthogonal group.
-/

@[expose] public section

noncomputable section

open scoped Quaternion BigOperators RealInnerProductSpace
open GeneratedFoundations.Geometry.SourceQuaternionAmplitude
open GeneratedFoundations.Geometry.SourcePolarMetric

namespace GeneratedFoundations.Geometry.SourceInvariantMetric

abbrev MetricFamily := ℝ → unitary ℍ → LinearMap.BilinForm ℝ ℍ

/-- The actual left and inverse-right source action on amplitude variations. -/
def leftRight (a b : unitary ℍ) : ℍ ≃ₗᵢ[ℝ] ℍ :=
  (Unitary.mulLeft ℝ ℍ a).trans (Unitary.mulRight ℝ (star b))

@[simp] theorem leftRight_apply (a b : unitary ℍ) (h : ℍ) :
    leftRight a b h = (a : ℍ) * h * star (b : ℍ) := rfl

theorem leftRight_unit (a b q : unitary ℍ) :
    leftRight a b (q : ℍ) = ((a * q * b⁻¹ : unitary ℍ) : ℍ) := rfl

theorem leftRight_matrix (a b : unitary ℍ) (h : ℍ) :
    matrixMap (leftRight a b h) =
      (unitaryEquiv a : Operations.SourceSpinCorner.Mat2) * matrixMap h *
        (unitaryEquiv b : Operations.SourceSpinCorner.Mat2).conjTranspose := by
  change matrixMap ((a : ℍ) * h * star (b : ℍ)) = _
  rw [map_mul, map_mul, matrixMap_star]
  rfl

/-- The comparison conditions are stated before any radial-angular splitting.
Homothety scales the actual amplitude variation in both slots. -/
structure IsCalibratedSourceMetric (G : MetricFamily) : Prop where
  invariant : ∀ {r : ℝ}, 0 < r → ∀ a b q : unitary ℍ, ∀ h k : ℍ,
    G r (a * q * b⁻¹) (leftRight a b h) (leftRight a b k) = G r q h k
  radial : ∀ {r : ℝ}, 0 < r → ∀ q : unitary ℍ, G r q q q = 1
  homothety : ∀ {r c : ℝ}, 0 < r → 0 < c → ∀ q : unitary ℍ, ∀ h k : ℍ,
    G (c * r) q (c • h) (c • k) = c ^ 2 * G r q h k
  unit_angular : ∀ q : unitary ℍ, ∀ h k : ℍ,
    inner ℝ (q : ℍ) h = 0 → inner ℝ (q : ℍ) k = 0 →
      G 1 q h k = inner ℝ h k

def sourceAxis (i : Fin 4) : ℍ :=
  ![1, ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩] i

theorem sourceAxis_normSq (i : Fin 4) : Quaternion.normSq (sourceAxis i) = 1 := by
  fin_cases i <;> norm_num [sourceAxis, Quaternion.normSq_def']

def sourceAxisUnit (i : Fin 4) : unitary ℍ :=
  ⟨sourceAxis i, (mem_unitary_iff_normSq _).mpr (sourceAxis_normSq i)⟩

/-- The four conjugations average to the real scalar channel. -/
theorem source_conjugation_sum (h : ℍ) :
    (∑ i : Fin 4, leftRight (sourceAxisUnit i) (sourceAxisUnit i) h) =
      (4 * h.re) • (1 : ℍ) := by
  rw [Fin.sum_univ_four]
  apply Quaternion.ext <;> simp [leftRight_apply, sourceAxisUnit, sourceAxis]
  ring

variable {G : MetricFamily}

theorem IsCalibratedSourceMetric.conjugation_right
    (hG : IsCalibratedSourceMetric G) {r : ℝ} (hr : 0 < r)
    (a : unitary ℍ) (h : ℍ) :
    G r 1 1 (leftRight a a h) = G r 1 1 h := by
  have hi := hG.invariant hr a a 1 (1 : ℍ) h
  simpa only [mul_one, mul_inv_cancel, leftRight_apply,
    a.property.2] using hi

theorem IsCalibratedSourceMetric.conjugation_left
    (hG : IsCalibratedSourceMetric G) {r : ℝ} (hr : 0 < r)
    (a : unitary ℍ) (h : ℍ) :
    G r 1 (leftRight a a h) 1 = G r 1 h 1 := by
  have hi := hG.invariant hr a a 1 h (1 : ℍ)
  simpa only [mul_one, mul_inv_cancel, leftRight_apply,
    a.property.2] using hi

theorem IsCalibratedSourceMetric.radial_right_at_one
    (hG : IsCalibratedSourceMetric G) {r : ℝ} (hr : 0 < r) (h : ℍ) :
    G r 1 1 h = h.re := by
  have hs : G r 1 1 (∑ i : Fin 4,
      leftRight (sourceAxisUnit i) (sourceAxisUnit i) h) = 4 * G r 1 1 h := by
    simp only [Fin.sum_univ_four, LinearMap.BilinForm.add_right,
      hG.conjugation_right hr]
    ring
  have hradial : G r 1 1 1 = 1 := hG.radial hr 1
  rw [source_conjugation_sum, LinearMap.BilinForm.smul_right, hradial] at hs
  linarith

theorem IsCalibratedSourceMetric.radial_left_at_one
    (hG : IsCalibratedSourceMetric G) {r : ℝ} (hr : 0 < r) (h : ℍ) :
    G r 1 h 1 = h.re := by
  have hs : G r 1 (∑ i : Fin 4,
      leftRight (sourceAxisUnit i) (sourceAxisUnit i) h) 1 = 4 * G r 1 h 1 := by
    simp only [Fin.sum_univ_four, LinearMap.BilinForm.add_left,
      hG.conjugation_left hr]
    ring
  have hradial : G r 1 1 1 = 1 := hG.radial hr 1
  rw [source_conjugation_sum, LinearMap.BilinForm.smul_left, hradial] at hs
  linarith

theorem star_mul_real_inner (q h : ℍ) : (star q * h).re = inner ℝ q h := by
  simp [Quaternion.inner_def]

theorem leftRight_undo (q : unitary ℍ) (h : ℍ) :
    leftRight q 1 (star (q : ℍ) * h) = h := by
  simp only [leftRight_apply, OneMemClass.coe_one, star_one, mul_one]
  rw [← mul_assoc, q.property.2, one_mul]

theorem IsCalibratedSourceMetric.radial_right
    (hG : IsCalibratedSourceMetric G) {r : ℝ} (hr : 0 < r)
    (q : unitary ℍ) (h : ℍ) : G r q q h = inner ℝ (q : ℍ) h := by
  have hi := hG.invariant hr q 1 1 (1 : ℍ) (star (q : ℍ) * h)
  rw [leftRight_undo] at hi
  simpa only [mul_one, inv_one, leftRight_apply, OneMemClass.coe_one,
    star_one, hG.radial_right_at_one hr, star_mul_real_inner] using hi

theorem IsCalibratedSourceMetric.radial_left
    (hG : IsCalibratedSourceMetric G) {r : ℝ} (hr : 0 < r)
    (q : unitary ℍ) (h : ℍ) : G r q h q = inner ℝ (q : ℍ) h := by
  have hi := hG.invariant hr q 1 1 (star (q : ℍ) * h) (1 : ℍ)
  rw [leftRight_undo] at hi
  simpa only [mul_one, inv_one, leftRight_apply, OneMemClass.coe_one,
    star_one, hG.radial_left_at_one hr, star_mul_real_inner] using hi

theorem IsCalibratedSourceMetric.scale_eq
    (hG : IsCalibratedSourceMetric G) {r : ℝ} (hr : 0 < r)
    (q : unitary ℍ) (h k : ℍ) : G r q h k = G 1 q h k := by
  have hs := hG.homothety (r := 1) (c := r) (by norm_num) hr q h k
  simp only [mul_one, LinearMap.BilinForm.smul_left,
    LinearMap.BilinForm.smul_right] at hs
  apply mul_left_cancel₀ (pow_ne_zero 2 hr.ne')
  calc
    r ^ 2 * G r q h k = r * (r * G r q h k) := by ring
    _ = r ^ 2 * G 1 q h k := hs

/-- The full polar bilinear form is forced by the comparison conditions. -/
theorem IsCalibratedSourceMetric.polar_formula
    (hG : IsCalibratedSourceMetric G) {r : ℝ} (hr : 0 < r)
    (q : unitary ℍ) (x y : ℝ × angularSpace (q : ℍ)) :
    G r q (polarLinear r q x) (polarLinear r q y) =
      x.1 * y.1 + r ^ 2 * inner ℝ (x.2 : ℍ) (y.2 : ℍ) := by
  have ha : G r q (x.2 : ℍ) (y.2 : ℍ) = inner ℝ (x.2 : ℍ) (y.2 : ℍ) := by
    rw [hG.scale_eq hr]
    exact hG.unit_angular q x.2 y.2 (angular_inner q x.2) (angular_inner q y.2)
  simp only [polarLinear_apply, LinearMap.BilinForm.add_left,
    LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_left,
    LinearMap.BilinForm.smul_right, hG.radial_right hr,
    hG.radial_left hr, angular_inner, ha]
  simp only [inner_add_right, real_inner_smul_right,
    unit_inner ((mem_unitary_iff_norm _).mp q.property), angular_inner, mul_zero, add_zero]
  ring

/-- Uniqueness holds for every bilinear metric in the stated comparison class. -/
theorem IsCalibratedSourceMetric.eq_inner
    (hG : IsCalibratedSourceMetric G) {r : ℝ} (hr : 0 < r)
    (q : unitary ℍ) : G r q = innerₗ ℍ := by
  have hq : ‖(q : ℍ)‖ = 1 := (mem_unitary_iff_norm _).mp q.property
  apply LinearMap.BilinForm.ext
  intro h k
  obtain ⟨x, rfl⟩ := (polarLinearEquiv hq hr.ne').surjective h
  obtain ⟨y, rfl⟩ := (polarLinearEquiv hq hr.ne').surjective k
  change G r q (polarLinear r q x) (polarLinear r q y) =
    inner ℝ (polarLinear r q x) (polarLinear r q y)
  rw [hG.polar_formula hr, polar_inner hq]

def traceMetric : MetricFamily := fun _ _ => innerₗ ℍ

theorem traceMetric_calibrated : IsCalibratedSourceMetric traceMetric where
  invariant hr a b q h k := (leftRight a b).inner_map_map h k
  radial hr q := unit_inner ((mem_unitary_iff_norm _).mp q.property)
  homothety := by
    intro r c hr hc q h k
    change inner ℝ (c • h) (c • k) = c ^ 2 * inner ℝ h k
    rw [real_inner_smul_left, real_inner_smul_right]
    ring
  unit_angular q h k hh hk := rfl

theorem calibratedPolarMetric_unique (G H : MetricFamily)
    (hG : IsCalibratedSourceMetric G) (hH : IsCalibratedSourceMetric H)
    {r : ℝ} (hr : 0 < r) (q : unitary ℍ) : G r q = H r q := by
  rw [hG.eq_inner hr, hH.eq_inner hr]

theorem calibratedMetric_source_trace (hG : IsCalibratedSourceMetric G)
    {r : ℝ} (hr : 0 < r) (q : unitary ℍ) (h k : ℍ) :
    G r q h k = (Matrix.trace ((matrixMap h).conjTranspose * matrixMap k)).re / 2 := by
  rw [hG.eq_inner hr, innerₗ_apply_apply, trace_inner]

end GeneratedFoundations.Geometry.SourceInvariantMetric

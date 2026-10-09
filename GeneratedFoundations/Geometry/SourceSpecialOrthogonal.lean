module

public import GeneratedFoundations.Geometry.SourceInvariantMetric
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Special-orthogonal invariance of the source metric

Left and right multiplication by a quaternion have determinant equal to
the square of its norm square. The actual action by two unit source
amplitudes therefore has determinant one. Invariance under determinant-one
real linear isometries implies the source invariance used in the metric
uniqueness theorem. No surjectivity onto the special orthogonal group is
required for this implication.
-/

@[expose] public section

noncomputable section

open scoped Quaternion BigOperators RealInnerProductSpace
open Module
open GeneratedFoundations.Geometry.SourceQuaternionAmplitude
open GeneratedFoundations.Geometry.SourceInvariantMetric

namespace GeneratedFoundations.Geometry.SourceSpecialOrthogonal

def quaternionBasis : Basis (Fin 4) ℝ ℍ :=
  QuaternionAlgebra.basisOneIJK (-1 : ℝ) 0 (-1)

theorem quaternionBasis_apply (i : Fin 4) : quaternionBasis i = sourceAxis i := by
  apply quaternionBasis.repr.injective
  rw [Basis.repr_self]
  ext j
  rw [Finsupp.single_apply]
  change (if i = j then (1 : ℝ) else 0) =
    (![ (sourceAxis i).re, (sourceAxis i).imI,
      (sourceAxis i).imJ, (sourceAxis i).imK] : Fin 4 → ℝ) j
  fin_cases i <;> fin_cases j <;> norm_num [sourceAxis]

def quaternionLeftMatrix (q : ℍ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![q.re, -q.imI, -q.imJ, -q.imK;
     q.imI, q.re, -q.imK, q.imJ;
     q.imJ, q.imK, q.re, -q.imI;
     q.imK, -q.imJ, q.imI, q.re]

def quaternionRightMatrix (q : ℍ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![q.re, -q.imI, -q.imJ, -q.imK;
     q.imI, q.re, q.imK, -q.imJ;
     q.imJ, -q.imK, q.re, q.imI;
     q.imK, q.imJ, -q.imI, q.re]

theorem toMatrix_quaternion_mulLeft (q : ℍ) :
    LinearMap.toMatrix quaternionBasis quaternionBasis (LinearMap.mulLeft ℝ q) =
      quaternionLeftMatrix q := by
  ext i j
  rw [LinearMap.toMatrix_apply, quaternionBasis_apply]
  change (![ (q * sourceAxis j).re, (q * sourceAxis j).imI,
    (q * sourceAxis j).imJ, (q * sourceAxis j).imK] : Fin 4 → ℝ) i = _
  fin_cases i <;> fin_cases j <;>
    simp [sourceAxis, quaternionLeftMatrix]

theorem toMatrix_quaternion_mulRight (q : ℍ) :
    LinearMap.toMatrix quaternionBasis quaternionBasis (LinearMap.mulRight ℝ q) =
      quaternionRightMatrix q := by
  ext i j
  rw [LinearMap.toMatrix_apply, quaternionBasis_apply]
  change (![ (sourceAxis j * q).re, (sourceAxis j * q).imI,
    (sourceAxis j * q).imJ, (sourceAxis j * q).imK] : Fin 4 → ℝ) i = _
  fin_cases i <;> fin_cases j <;>
    simp [sourceAxis, quaternionRightMatrix]

theorem quaternionLeftMatrix_det (q : ℍ) :
    (quaternionLeftMatrix q).det = (Quaternion.normSq q) ^ 2 := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_four]
  norm_num [Matrix.det_fin_three, Matrix.submatrix_apply, quaternionLeftMatrix,
    Fin.succAbove, Quaternion.normSq_def']
  ring

theorem quaternionRightMatrix_det (q : ℍ) :
    (quaternionRightMatrix q).det = (Quaternion.normSq q) ^ 2 := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_four]
  norm_num [Matrix.det_fin_three, Matrix.submatrix_apply, quaternionRightMatrix,
    Fin.succAbove, Quaternion.normSq_def']
  ring

theorem quaternion_mulLeft_det (q : ℍ) :
    (LinearMap.mulLeft ℝ q).det = (Quaternion.normSq q) ^ 2 := by
  rw [← LinearMap.det_toMatrix quaternionBasis, toMatrix_quaternion_mulLeft,
    quaternionLeftMatrix_det]

theorem quaternion_mulRight_det (q : ℍ) :
    (LinearMap.mulRight ℝ q).det = (Quaternion.normSq q) ^ 2 := by
  rw [← LinearMap.det_toMatrix quaternionBasis, toMatrix_quaternion_mulRight,
    quaternionRightMatrix_det]

theorem leftRight_toLinearMap (a b : unitary ℍ) :
    (leftRight a b).toLinearMap =
      (LinearMap.mulRight ℝ (star (b : ℍ))).comp (LinearMap.mulLeft ℝ (a : ℍ)) := by
  apply LinearMap.ext
  intro h
  rfl

/-- The generated left-right action is orientation-preserving on the real amplitude space. -/
theorem leftRight_det (a b : unitary ℍ) : (leftRight a b).toLinearMap.det = 1 := by
  rw [leftRight_toLinearMap, LinearMap.det_comp, quaternion_mulRight_det,
    quaternion_mulLeft_det, Quaternion.normSq_star,
    (mem_unitary_iff_normSq _).mp a.property,
    (mem_unitary_iff_normSq _).mp b.property]
  norm_num

/-- A real linear isometry acts on the actual unit source amplitudes. -/
def unitAction (e : ℍ ≃ₗᵢ[ℝ] ℍ) (q : unitary ℍ) : unitary ℍ :=
  ⟨e (q : ℍ), (mem_unitary_iff_norm _).mpr (by
    rw [e.norm_map]
    exact (mem_unitary_iff_norm _).mp q.property)⟩

@[simp] theorem unitAction_coe (e : ℍ ≃ₗᵢ[ℝ] ℍ) (q : unitary ℍ) :
    (unitAction e q : ℍ) = e (q : ℍ) := rfl

theorem unitAction_leftRight (a b q : unitary ℍ) :
    unitAction (leftRight a b) q = a * q * b⁻¹ := by
  apply Subtype.ext
  exact leftRight_unit a b q

/-- The comparison class uses all determinant-one real linear isometries.
The radial, homothetic and unit-angular conditions are unchanged. -/
structure IsCalibratedSpecialOrthogonalMetric (G : MetricFamily) : Prop where
  invariant : ∀ {r : ℝ}, 0 < r → ∀ e : ℍ ≃ₗᵢ[ℝ] ℍ,
    e.toLinearMap.det = 1 → ∀ q : unitary ℍ, ∀ h k : ℍ,
      G r (unitAction e q) (e h) (e k) = G r q h k
  radial : ∀ {r : ℝ}, 0 < r → ∀ q : unitary ℍ, G r q q q = 1
  homothety : ∀ {r c : ℝ}, 0 < r → 0 < c → ∀ q : unitary ℍ, ∀ h k : ℍ,
    G (c * r) q (c • h) (c • k) = c ^ 2 * G r q h k
  unit_angular : ∀ q : unitary ℍ, ∀ h k : ℍ,
    inner ℝ (q : ℍ) h = 0 → inner ℝ (q : ℍ) k = 0 →
      G 1 q h k = inner ℝ h k

theorem IsCalibratedSpecialOrthogonalMetric.toSourceMetric {G : MetricFamily}
    (hG : IsCalibratedSpecialOrthogonalMetric G) : IsCalibratedSourceMetric G where
  invariant hr a b q h k := by
    simpa only [unitAction_leftRight] using
      hG.invariant hr (leftRight a b) (leftRight_det a b) q h k
  radial := hG.radial
  homothety := hG.homothety
  unit_angular := hG.unit_angular

theorem IsCalibratedSpecialOrthogonalMetric.eq_inner {G : MetricFamily}
    (hG : IsCalibratedSpecialOrthogonalMetric G) {r : ℝ} (hr : 0 < r)
    (q : unitary ℍ) : G r q = innerₗ ℍ :=
  hG.toSourceMetric.eq_inner hr q

/-- The special-orthogonal comparison class has the full calibrated cone form. -/
theorem IsCalibratedSpecialOrthogonalMetric.polar_formula {G : MetricFamily}
    (hG : IsCalibratedSpecialOrthogonalMetric G) {r : ℝ} (hr : 0 < r)
    (q : unitary ℍ)
    (x y : ℝ × SourcePolarMetric.angularSpace (q : ℍ)) :
    G r q (SourcePolarMetric.polarLinear r q x)
        (SourcePolarMetric.polarLinear r q y) =
      x.1 * y.1 + r ^ 2 * inner ℝ (x.2 : ℍ) (y.2 : ℍ) :=
  hG.toSourceMetric.polar_formula hr q x y

theorem traceMetric_specialOrthogonal : IsCalibratedSpecialOrthogonalMetric traceMetric where
  invariant _hr e _he _q h k := e.inner_map_map h k
  radial := traceMetric_calibrated.radial
  homothety := traceMetric_calibrated.homothety
  unit_angular := traceMetric_calibrated.unit_angular

theorem calibratedSpecialOrthogonalMetric_unique (G H : MetricFamily)
    (hG : IsCalibratedSpecialOrthogonalMetric G)
    (hH : IsCalibratedSpecialOrthogonalMetric H) {r : ℝ} (hr : 0 < r)
    (q : unitary ℍ) : G r q = H r q :=
  calibratedPolarMetric_unique G H hG.toSourceMetric hH.toSourceMetric hr q

end GeneratedFoundations.Geometry.SourceSpecialOrthogonal

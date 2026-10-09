module

public import GeneratedFoundations.Geometry.SourceCentralObservations
public import Mathlib.Algebra.QuaternionBasis
public import Mathlib.Analysis.Quaternion
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Quaternion amplitudes of the generated source operations

The matrix representation is constructed from a quaternion basis in the
actual source corner. Its image is exactly the smallest real algebra
containing the generated determinant-one unitary group. The unit quaternions
are continuously isomorphic to this group and identify it with the unit
sphere in four-dimensional Euclidean space. The central sign becomes the
antipodal map. The normalized matrix trace recovers the quaternion inner
product, and every nonzero amplitude has a unique positive radial factor.
-/

@[expose] public section

noncomputable section

open scoped Quaternion ComplexConjugate RealInnerProductSpace
open GeneratedFoundations.Operations.SourceSpinCorner
open GeneratedFoundations.Operations.SourceSpinCornerGroup
open GeneratedFoundations.Geometry.SourceSpinCentre

namespace GeneratedFoundations.Geometry.SourceQuaternionAmplitude

/-- Three matrices in the already generated source group satisfy the quaternion relations. -/
def matrixBasis : QuaternionAlgebra.Basis Mat2 (-1 : ℝ) 0 (-1) where
  i := canonical Complex.I 0
  j := canonical 0 1
  k := canonical 0 Complex.I
  i_mul_i := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [canonical, Matrix.mul_apply, Fin.sum_univ_two]
  j_mul_j := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [canonical, Matrix.mul_apply, Fin.sum_univ_two]
  i_mul_j := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [canonical, Matrix.mul_apply, Fin.sum_univ_two]
  j_mul_i := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [canonical, Matrix.mul_apply, Fin.sum_univ_two]

def matrixMap : ℍ →ₐ[ℝ] Mat2 := matrixBasis.liftHom

theorem matrixBasis_source_axes :
    matrixBasis.i = (-2 * Complex.I) • spinMatrix3 ∧
    matrixBasis.j = (-2 * Complex.I) • spinMatrix2 ∧
    matrixBasis.k = (2 * Complex.I) • spinMatrix1 := by
  refine ⟨?_, ?_, ?_⟩
  all_goals
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [matrixBasis, canonical, spinMatrix1, spinMatrix2, spinMatrix3]
    all_goals ring_nf <;> norm_num

theorem matrixMap_eq (q : ℍ) :
    matrixMap q = canonical ((q.re : ℂ) + q.imI * Complex.I)
      ((q.imJ : ℂ) + q.imK * Complex.I) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixMap, QuaternionAlgebra.Basis.liftHom, QuaternionAlgebra.Basis.lift,
      matrixBasis, canonical, Algebra.algebraMap_eq_smul_one]
  all_goals ring

/-- The four real entries of the first row recover the amplitude. -/
def ofMatrix (M : Mat2) : ℍ :=
  ⟨(M 0 0).re, (M 0 0).im, (M 0 1).re, (M 0 1).im⟩

def ofMatrixLinear : Mat2 →ₗ[ℝ] ℍ where
  toFun := ofMatrix
  map_add' M N := by ext <;> simp [ofMatrix]
  map_smul' r M := by ext <;> simp [ofMatrix, smul_eq_mul]

@[simp] theorem ofMatrix_matrixMap (q : ℍ) : ofMatrix (matrixMap q) = q := by
  rw [matrixMap_eq]
  ext <;> simp [ofMatrix, canonical]

theorem matrixMap_injective : Function.Injective matrixMap := by
  intro p q h
  simpa only [ofMatrix_matrixMap] using congrArg ofMatrix h

theorem matrixMap_ofMatrix (M : Mat2) :
    matrixMap (ofMatrix M) = canonical (M 0 0) (M 0 1) := by
  rw [matrixMap_eq]
  simp only [ofMatrix, Complex.re_add_im]

theorem matrixMap_of_specialUnitary (U : SU2) : matrixMap (ofMatrix U) = (U : Mat2) :=
  (matrixMap_ofMatrix U).trans (specialUnitary_entries U U.property).symm

theorem matrixMap_star (q : ℍ) : matrixMap (star q) = (matrixMap q).conjTranspose := by
  rw [matrixMap_eq, matrixMap_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [canonical, Matrix.conjTranspose_apply] <;> ring

theorem basis_i_mem : matrixBasis.i ∈ SU2 :=
  canonical_mem_specialUnitary _ _ (by simp)

theorem basis_j_mem : matrixBasis.j ∈ SU2 :=
  canonical_mem_specialUnitary _ _ (by simp)

theorem basis_k_mem : matrixBasis.k ∈ SU2 :=
  canonical_mem_specialUnitary _ _ (by simp)

/-- The real algebra of the actual generated reversible matrices. -/
def amplitudeAlgebra : Subalgebra ℝ Mat2 := matrixMap.range

def amplitudeEquiv : ℍ ≃ₐ[ℝ] amplitudeAlgebra :=
  AlgEquiv.ofLeftInverse ofMatrix_matrixMap

theorem amplitude_finrank : Module.finrank ℝ amplitudeAlgebra = 4 := by
  rw [← amplitudeEquiv.toLinearEquiv.finrank_eq]
  exact Quaternion.finrank_eq_four

theorem specialUnitary_mem_amplitude (U : SU2) : (U : Mat2) ∈ amplitudeAlgebra :=
  ⟨ofMatrix U, matrixMap_of_specialUnitary U⟩

/-- The image is the minimal real algebra containing all actual source operations. -/
theorem amplitudeAlgebra_eq_adjoin :
    amplitudeAlgebra = Algebra.adjoin ℝ (SU2 : Set Mat2) := by
  apply le_antisymm
  · change matrixBasis.liftHom.range ≤ _
    rw [QuaternionAlgebra.Basis.range_liftHom]
    apply Algebra.adjoin_mono
    intro M hM
    rcases hM with rfl | rfl | rfl
    · exact basis_i_mem
    · exact basis_j_mem
    · exact basis_k_mem
  · apply Algebra.adjoin_le_iff.mpr
    intro M hM
    exact specialUnitary_mem_amplitude ⟨M, hM⟩

theorem amplitudeAlgebra_le_iff (A : Subalgebra ℝ Mat2) :
    amplitudeAlgebra ≤ A ↔ ∀ U : SU2, (U : Mat2) ∈ A := by
  rw [amplitudeAlgebra_eq_adjoin, Algebra.adjoin_le_iff]
  exact ⟨fun h U => h U.property, fun h M hM => h ⟨M, hM⟩⟩

/-- Real linear combinations suffice; products create no additional amplitudes. -/
theorem amplitudeAlgebra_eq_span :
    amplitudeAlgebra.toSubmodule = Submodule.span ℝ (SU2 : Set Mat2) := by
  apply le_antisymm
  · rintro M ⟨q, rfl⟩
    change matrixBasis.lift q ∈ Submodule.span ℝ (SU2 : Set Mat2)
    rw [QuaternionAlgebra.Basis.lift, Algebra.algebraMap_eq_smul_one]
    exact Submodule.add_mem _
      (Submodule.add_mem _
        (Submodule.add_mem _
          (Submodule.smul_mem _ _ (Submodule.subset_span (Matrix.specialUnitaryGroup _ _).one_mem))
          (Submodule.smul_mem _ _ (Submodule.subset_span basis_i_mem)))
        (Submodule.smul_mem _ _ (Submodule.subset_span basis_j_mem)))
      (Submodule.smul_mem _ _ (Submodule.subset_span basis_k_mem))
  · apply Submodule.span_le.mpr
    intro M hM
    exact specialUnitary_mem_amplitude ⟨M, hM⟩

theorem normSq_ofMatrix (M : Mat2) :
    Quaternion.normSq (ofMatrix M) = ‖M 0 0‖ ^ 2 + ‖M 0 1‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [ofMatrix, Quaternion.normSq_def', Complex.normSq_apply]
  ring

theorem normSq_of_specialUnitary (U : SU2) : Quaternion.normSq (ofMatrix U) = 1 := by
  rw [normSq_ofMatrix]
  exact specialUnitary_norms U U.property

theorem matrixMap_mem_specialUnitary_iff (q : ℍ) :
    matrixMap q ∈ SU2 ↔ Quaternion.normSq q = 1 := by
  constructor
  · intro hq
    have h := specialUnitary_norms (matrixMap q) hq
    rw [← normSq_ofMatrix, ofMatrix_matrixMap] at h
    exact h
  · intro hq
    have h := normSq_ofMatrix (matrixMap q)
    rw [ofMatrix_matrixMap, hq, matrixMap_eq] at h
    rw [matrixMap_eq]
    apply canonical_mem_specialUnitary
    simpa [canonical] using h.symm

theorem mem_unitary_iff_normSq (q : ℍ) :
    q ∈ unitary ℍ ↔ Quaternion.normSq q = 1 := by
  rw [Unitary.mem_iff, Quaternion.star_mul_self, Quaternion.self_mul_star, and_self]
  exact Quaternion.coe_inj

theorem mem_unitary_iff_norm (q : ℍ) : q ∈ unitary ℍ ↔ ‖q‖ = 1 := by
  rw [mem_unitary_iff_normSq, Quaternion.normSq_eq_norm_mul_self]
  constructor
  · intro h
    nlinarith [norm_nonneg q]
  · intro h
    rw [h, one_mul]

/-- The quaternion product represents multiplication of the same source matrices. -/
def unitaryEquiv : unitary ℍ ≃ₜ* SU2 where
  toFun q := ⟨matrixMap q,
    (matrixMap_mem_specialUnitary_iff q).mpr ((mem_unitary_iff_normSq q).mp q.property)⟩
  invFun U := ⟨ofMatrix U, (mem_unitary_iff_normSq _).mpr (normSq_of_specialUnitary U)⟩
  left_inv q := Subtype.ext (ofMatrix_matrixMap q)
  right_inv U := Subtype.ext (matrixMap_of_specialUnitary U)
  map_mul' p q := Subtype.ext (map_mul matrixMap (p : ℍ) (q : ℍ))
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    exact matrixMap.toLinearMap.continuous_of_finiteDimensional.comp continuous_subtype_val
  continuous_invFun := by
    apply continuous_induced_rng.mpr
    exact ofMatrixLinear.continuous_of_finiteDimensional.comp continuous_subtype_val

abbrev Sphere3 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

/-- The target sphere is the independent Euclidean sphere from the library. -/
def unitarySphereHomeomorph : unitary ℍ ≃ₜ Sphere3 where
  toFun q := ⟨Quaternion.linearIsometryEquivTuple q, by
    rw [Metric.mem_sphere, dist_zero_right, Quaternion.linearIsometryEquivTuple.norm_map]
    exact (mem_unitary_iff_norm q).mp q.property⟩
  invFun x := ⟨Quaternion.linearIsometryEquivTuple.symm x, by
    apply (mem_unitary_iff_norm _).mpr
    rw [Quaternion.linearIsometryEquivTuple.symm.norm_map]
    exact mem_sphere_zero_iff_norm.mp x.property⟩
  left_inv q := Subtype.ext (Quaternion.linearIsometryEquivTuple.symm_apply_apply q)
  right_inv x := Subtype.ext (Quaternion.linearIsometryEquivTuple.apply_symm_apply x)
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    exact Quaternion.linearIsometryEquivTuple.continuous.comp continuous_subtype_val
  continuous_invFun := by
    apply continuous_induced_rng.mpr
    exact Quaternion.linearIsometryEquivTuple.symm.continuous.comp continuous_subtype_val

def sourceSphereHomeomorph : SU2 ≃ₜ Sphere3 :=
  unitaryEquiv.toHomeomorph.symm.trans unitarySphereHomeomorph

theorem sourceSphere_apply (U : SU2) :
    (sourceSphereHomeomorph U : EuclideanSpace ℝ (Fin 4)) =
      Quaternion.linearIsometryEquivTuple (ofMatrix U) := rfl

theorem sourceSphere_central (U : SU2) :
    (sourceSphereHomeomorph (negativeIdentity * U) : EuclideanSpace ℝ (Fin 4)) =
      -(sourceSphereHomeomorph U : EuclideanSpace ℝ (Fin 4)) := by
  rw [sourceSphere_apply, sourceSphere_apply]
  have h : ((negativeIdentity * U : SU2) : Mat2) = -(U : Mat2) := by
    change (negativeIdentity : Mat2) * (U : Mat2) = -(U : Mat2)
    simp
  rw [h]
  change Quaternion.linearIsometryEquivTuple (ofMatrixLinear (-(U : Mat2))) = _
  rw [map_neg, map_neg]
  rfl

theorem trace_matrixMap (q : ℍ) : Matrix.trace (matrixMap q) = (2 * q.re : ℝ) := by
  rw [matrixMap_eq]
  simp [Matrix.trace, Fin.sum_univ_two, canonical]
  ring

/-- This is the full positive trace comparison on the four-real-dimensional amplitude space. -/
theorem trace_inner (p q : ℍ) :
    (Matrix.trace ((matrixMap p).conjTranspose * matrixMap q)).re / 2 = inner ℝ p q := by
  rw [← matrixMap_star, ← map_mul, trace_matrixMap]
  simp only [Complex.ofReal_re, Quaternion.inner_def]
  simp

theorem trace_normSq (q : ℍ) :
    (Matrix.trace ((matrixMap q).conjTranspose * matrixMap q)).re / 2 = Quaternion.normSq q := by
  rw [trace_inner, Quaternion.inner_self]

/-- The unit factor comes from the same amplitude by positive real normalization. -/
def polarUnit (q : ℍ) (hq : q ≠ 0) : SU2 :=
  unitaryEquiv ⟨‖q‖⁻¹ • q, (mem_unitary_iff_norm _).mpr (by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg q)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hq)])⟩

theorem positive_polar_factorization (q : ℍ) (hq : q ≠ 0) :
    matrixMap q = ‖q‖ • (polarUnit q hq : Mat2) := by
  change matrixMap q = ‖q‖ • matrixMap (‖q‖⁻¹ • q)
  rw [map_smul, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hq), one_smul]

theorem positive_polar_unique (q : ℍ) (hq : q ≠ 0) (r : ℝ) (hr : 0 < r)
    (U : SU2) (h : matrixMap q = r • (U : Mat2)) :
    r = ‖q‖ ∧ U = polarUnit q hq := by
  have hqU : q = r • ofMatrix U := by
    have hc := congrArg ofMatrixLinear h
    rw [map_smul] at hc
    change ofMatrix (matrixMap q) = r • ofMatrix U at hc
    simpa only [ofMatrix_matrixMap] using hc
  have hU : ‖ofMatrix U‖ = 1 :=
    (mem_unitary_iff_norm _).mp ((mem_unitary_iff_normSq _).mpr (normSq_of_specialUnitary U))
  have hrq : r = ‖q‖ := by
    rw [hqU, norm_smul, Real.norm_of_nonneg hr.le, hU, mul_one]
  refine ⟨hrq, ?_⟩
  apply Subtype.ext
  apply smul_right_injective Mat2 (norm_ne_zero_iff.mpr hq)
  change ‖q‖ • (U : Mat2) = ‖q‖ • (polarUnit q hq : Mat2)
  rw [← positive_polar_factorization q hq, ← hrq]
  exact h.symm

/-- Both the positive radius and the source-group factor are unique. -/
theorem positive_polar_existsUnique (q : ℍ) (hq : q ≠ 0) :
    ∃! p : ℝ × SU2, 0 < p.1 ∧ matrixMap q = p.1 • (p.2 : Mat2) := by
  refine ⟨(‖q‖, polarUnit q hq),
    ⟨norm_pos_iff.mpr hq, positive_polar_factorization q hq⟩, ?_⟩
  intro p hp
  obtain ⟨hr, hU⟩ := positive_polar_unique q hq p.1 hp.1 p.2 hp.2
  exact Prod.ext hr hU

theorem amplitude_positive_polar_existsUnique (M : amplitudeAlgebra) (hM : (M : Mat2) ≠ 0) :
    ∃! p : ℝ × SU2, 0 < p.1 ∧ (M : Mat2) = p.1 • (p.2 : Mat2) := by
  rcases M with ⟨M, hMrange⟩
  obtain ⟨q, rfl⟩ := hMrange
  apply positive_polar_existsUnique q
  intro hq
  exact hM (by change matrixMap q = 0; rw [hq, map_zero])

end GeneratedFoundations.Geometry.SourceQuaternionAmplitude

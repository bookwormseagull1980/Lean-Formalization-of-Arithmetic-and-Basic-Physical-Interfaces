module

public import GeneratedFoundations.Geometry.SourceTensorSpectralCore
public import GeneratedFoundations.Geometry.SourceOneFormHaarBlock

/-!
# Tensor fields on the original projective source

All nine tensor coefficients are Haar-square-integrable functions on the
already generated projective source. The homogeneous row embeddings use
the existing quotient matrix coefficients and their derived normalization.
Schur orthogonality proves the embeddings isometric. The complete scalar
Haar basis supplies the full tensor basis before any differential kernel
or tensor spectral branch is selected.
-/

@[expose] public section

noncomputable section

open MeasureTheory Module
open scoped BigOperators ComplexConjugate lp
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourceSchurOrthogonality
open GeneratedFoundations.Geometry.SourceCompleteCoefficients
open GeneratedFoundations.Geometry.SourceQuotientHilbert
open GeneratedFoundations.Geometry.SourceOneFormHaarBlock
open GeneratedFoundations.Geometry.SourceTensorSpectralCore

namespace GeneratedFoundations.Geometry.SourceTensorHaarBlock

abbrev TensorL2 := PiLp 2 (fun _ : Fin 3 × Fin 3 => QuotientL2)

instance tensorL2Inner : InnerProductSpace ℂ TensorL2 :=
  PiLp.innerProductSpace (fun _ : Fin 3 × Fin 3 => QuotientL2)

def tensorRowLinear {m : ℕ} (hm : Even m) (i : Fin (m + 1)) :
    TensorBlock m →ₗ[ℂ] TensorL2 where
  toFun H := WithLp.toLp 2 (fun ab => rowIsometry hm i (H ab))
  map_add' H K := by
    apply (WithLp.equiv 2 (Fin 3 × Fin 3 → QuotientL2)).injective
    exact funext fun ab => map_add (rowIsometry hm i) (H ab) (K ab)
  map_smul' c H := by
    apply (WithLp.equiv 2 (Fin 3 × Fin 3 → QuotientL2)).injective
    exact funext fun ab => map_smul (rowIsometry hm i) c (H ab)

theorem tensorRowLinear_inner {m : ℕ} (hm : Even m) (i : Fin (m + 1))
    (H K : TensorBlock m) :
    inner ℂ (tensorRowLinear hm i H) (tensorRowLinear hm i K) = inner ℂ H K := by
  simp only [PiLp.inner_apply, tensorRowLinear, LinearMap.coe_mk, AddHom.coe_mk,
    LinearIsometry.inner_map_map]

def tensorRowIsometry {m : ℕ} (hm : Even m) (i : Fin (m + 1)) :
    TensorBlock m →ₗᵢ[ℂ] TensorL2 :=
  (tensorRowLinear hm i).isometryOfInner (tensorRowLinear_inner hm i)

@[simp] theorem tensorRowIsometry_apply {m : ℕ} (hm : Even m)
    (i : Fin (m + 1)) (H : TensorBlock m) (ab : Fin 3 × Fin 3) :
    tensorRowIsometry hm i H ab = rowIsometry hm i (H ab) := rfl

/-- Every tensor component is the Haar class of the same original source
matrix coefficient, rather than an independently selected eigenfunction. -/
theorem tensorRow_original_representative {m : ℕ} (hm : Even m)
    (i : Fin (m + 1)) (H : TensorBlock m) (ab : Fin 3 × Fin 3) :
    pullbackL2 (tensorRowIsometry hm i H ab) =
      normalization m • ContinuousMap.toLp 2
        sourceHaar ℂ
        (SourceSchurOrthogonality.matrixCoefficient m (sourceBasis m i) (H ab)) :=
  pullback_rowIsometry hm i (H ab)

abbrev FieldIndex := (Fin 3 × Fin 3) × EvenIndex

def fieldBasisVector (a : FieldIndex) : TensorL2 :=
  PiLp.single 2 a.1 (quotientBasisVector a.2)

theorem field_single_inner (ab : Fin 3 × Fin 3) (v : QuotientL2) (H : TensorL2) :
    inner ℂ (PiLp.single 2 ab v : TensorL2) H = inner ℂ v (H ab) := by
  classical
  change (∑ cd : Fin 3 × Fin 3,
    inner ℂ ((PiLp.single 2 ab v : TensorL2) cd) (H cd)) = _
  rw [Finset.sum_eq_single ab]
  · simp only [PiLp.single_eq_same]
  · intro cd _ hcd
    simp only [PiLp.single_eq_of_ne _ hcd, inner_zero_left]
  · simp

theorem fieldBasisVector_orthonormal : Orthonormal ℂ fieldBasisVector := by
  classical
  rw [orthonormal_iff_ite]
  rintro ⟨ab, a⟩ ⟨cd, b⟩
  by_cases hab : ab = cd
  · subst cd
    simp [fieldBasisVector, field_single_inner, PiLp.single_eq_same,
      orthonormal_iff_ite.mp quotientBasisVector_orthonormal]
  · have hpair : (ab, a) ≠ (cd, b) := fun h => hab (congrArg Prod.fst h)
    simp only [fieldBasisVector, field_single_inner, PiLp.single_eq_of_ne _ hab,
      inner_zero_right, ite_eq_right hpair]

def finiteFieldCore : Submodule ℂ TensorL2 :=
  Submodule.span ℂ (Set.range fieldBasisVector)

theorem finiteFieldCore_orthogonal : finiteFieldCoreᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  intro H hH
  have hall (ab : Fin 3 × Fin 3) (a : EvenIndex) :
      inner ℂ (quotientBasisVector a) (H ab) = 0 := by
    have h := (finiteFieldCore.mem_orthogonal H).mp hH
      (fieldBasisVector (ab, a)) (Submodule.subset_span (Set.mem_range_self (ab, a)))
    simpa only [fieldBasisVector, field_single_inner] using h
  have hz (ab : Fin 3 × Fin 3) : H ab = 0 := by
    apply quotientBasis.repr.injective
    apply lp.ext
    funext a
    simp only [HilbertBasis.repr_apply_apply, quotientBasis_apply, hall, inner_zero_right]
  change H = 0
  apply (WithLp.equiv 2 (Fin 3 × Fin 3 → QuotientL2)).injective
  exact funext hz

def fieldBasis : HilbertBasis FieldIndex ℂ TensorL2 :=
  HilbertBasis.mkOfOrthogonalEqBot fieldBasisVector_orthonormal finiteFieldCore_orthogonal

@[simp] theorem fieldBasis_apply (a : FieldIndex) : fieldBasis a = fieldBasisVector a :=
  congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot
    fieldBasisVector_orthonormal finiteFieldCore_orthogonal) a

theorem finiteFieldCore_dense : Dense (finiteFieldCore : Set TensorL2) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff]
  exact finiteFieldCore_orthogonal

end GeneratedFoundations.Geometry.SourceTensorHaarBlock

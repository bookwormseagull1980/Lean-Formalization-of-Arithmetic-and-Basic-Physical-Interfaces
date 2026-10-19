module

public import GeneratedFoundations.Geometry.SourceOneFormHaarBlock

/-!
# Complete one-form fields in the original quotient Haar space

The three frame components are taken in the trace metric already obtained
from the source. Each component uses the complete matrix coefficients of
the same central quotient. Their product family is proved orthonormal and
complete in the actual Haar space, without selecting a spectral branch.

Consequently the finite coefficient fields are dense before any curl or
Yang--Mills operator is closed. Both matrix indices, every even source
degree and all frame components occur in this dense core.
-/

@[expose] public section

noncomputable section

open MeasureTheory Module
open scoped BigOperators ComplexConjugate lp
open GeneratedFoundations.Geometry.SourceQuotientHilbert
open GeneratedFoundations.Geometry.SourceOneFormSpectralCore
open GeneratedFoundations.Geometry.SourceOneFormHaarBlock

namespace GeneratedFoundations.Geometry.SourceOneFormCompleteness

abbrev FieldIndex := Fin 3 × EvenIndex

/-- A single actual quotient matrix coefficient in one frame component. -/
def fieldBasisVector (a : FieldIndex) : OneFormL2 :=
  PiLp.single 2 a.1 (quotientBasisVector a.2)

theorem field_single_inner (r : Fin 3) (v : QuotientL2) (A : OneFormL2) :
    inner ℂ (PiLp.single 2 r v : OneFormL2) A = inner ℂ v (A r) := by
  classical
  change (∑ i : Fin 3, inner ℂ ((PiLp.single 2 r v : OneFormL2) i) (A i)) = _
  rw [Finset.sum_eq_single r]
  · simp only [PiLp.single_eq_same]
  · intro i _ hir
    simp only [PiLp.single_eq_of_ne _ hir, inner_zero_left]
  · simp

theorem fieldBasisVector_orthonormal : Orthonormal ℂ fieldBasisVector := by
  classical
  rw [orthonormal_iff_ite]
  rintro ⟨r, a⟩ ⟨s, b⟩
  by_cases hrs : r = s
  · subst s
    simp [fieldBasisVector, field_single_inner, PiLp.single_eq_same,
      orthonormal_iff_ite.mp quotientBasisVector_orthonormal]
  · have hpair : (r, a) ≠ (s, b) := fun h => hrs (congrArg Prod.fst h)
    simp only [fieldBasisVector, field_single_inner, PiLp.single_eq_of_ne _ hrs,
      inner_zero_right, ite_eq_right hpair]

def finiteFieldCore : Submodule ℂ OneFormL2 :=
  Submodule.span ℂ (Set.range fieldBasisVector)

/-- Completeness is inherited from the proved quotient Haar basis, not from
a presumed list of one-form eigenvalues. -/
theorem finiteFieldCore_orthogonal : finiteFieldCoreᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  intro A hA
  have hall (r : Fin 3) (a : EvenIndex) :
      inner ℂ (quotientBasisVector a) (A r) = 0 := by
    have h := (finiteFieldCore.mem_orthogonal A).mp hA
      (fieldBasisVector (r, a))
      (Submodule.subset_span (Set.mem_range_self (r, a)))
    simpa only [fieldBasisVector, field_single_inner] using h
  have hz (r : Fin 3) : A r = 0 := by
    apply quotientBasis.repr.injective
    apply lp.ext
    funext a
    simp only [HilbertBasis.repr_apply_apply, quotientBasis_apply, hall, inner_zero_right]
  change A = 0
  apply (WithLp.equiv 2 (Fin 3 → QuotientL2)).injective
  exact funext hz

def fieldBasis : HilbertBasis FieldIndex ℂ OneFormL2 :=
  HilbertBasis.mkOfOrthogonalEqBot fieldBasisVector_orthonormal finiteFieldCore_orthogonal

@[simp] theorem fieldBasis_apply (a : FieldIndex) :
    fieldBasis a = fieldBasisVector a :=
  congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot
    fieldBasisVector_orthonormal finiteFieldCore_orthogonal) a

theorem finiteFieldCore_dense : Dense (finiteFieldCore : Set OneFormL2) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff]
  exact finiteFieldCore_orthogonal

/-- Every Haar one-form has its expansion in the original field vectors. -/
theorem field_hasSum_expansion (A : OneFormL2) :
    HasSum (fun a : FieldIndex =>
      inner ℂ (fieldBasisVector a) A • fieldBasisVector a) A := by
  simpa only [HilbertBasis.repr_apply_apply, fieldBasis_apply]
    using fieldBasis.hasSum_repr A

end GeneratedFoundations.Geometry.SourceOneFormCompleteness

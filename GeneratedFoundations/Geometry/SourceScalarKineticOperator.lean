module

public import GeneratedFoundations.Geometry.SourceScalarKineticForm
public import GeneratedFoundations.Geometry.SourceOneFormHilbertSum

/-!
# The complete scalar kinetic pairing in the original Haar space

The diagonal kinetic values do not by themselves identify a Hessian.
Here the cross-row pairings are calculated by the original differentiated
Haar embeddings and Schur orthogonality. Linear extension then gives the
Green identity for arbitrary finite source coefficients. The operator in
that identity is the already constructed quotient Casimir, on its original
finite core and its unique self-adjoint closure.
-/

@[expose] public section
noncomputable section
open scoped BigOperators ComplexConjugate LinearPMap

open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourceSchurOrthogonality
open GeneratedFoundations.Geometry.SourceQuotientHilbert
open GeneratedFoundations.Geometry.SourceOneFormHaarBlock
open GeneratedFoundations.Geometry.SourceOneFormHodgeBlock
open GeneratedFoundations.Geometry.SourceOneFormHilbertSum
open GeneratedFoundations.Geometry.SourceOneFormScalarCoordinates
open GeneratedFoundations.Geometry.SourceScalarResolution
open GeneratedFoundations.Geometry.SourceScalarKineticForm
open GeneratedFoundations.Operations

namespace GeneratedFoundations.Geometry.SourceScalarKineticOperator

theorem include_rowCoordinates {m : ℕ} (hm : Even m)
    (i : Fin (m + 1)) (v : HilbertCarrier m) :
    includeScalar (rowCoordinates hm i v) = rowIsometry hm i v := by
  have h : includeScalar.comp (rowCoordinates hm i) =
      (rowIsometry hm i).toLinearMap := by
    apply (sourceBasis m).toBasis.ext
    intro j
    change includeScalar (rowCoordinates hm i (sourceBasis m j)) =
      rowIsometry hm i (sourceBasis m j)
    rw [rowCoordinates_basis, includeScalar_basis, rowIsometry_basis]
  exact LinearMap.congr_fun h v

private theorem distinct_rows_pairing (a b : EvenIndex)
    (h : rowOfIndex a ≠ rowOfIndex b) :
    inner ℂ (gradient (scalarBasis a)) (gradient (scalarBasis b)) = 0 := by
  have ha : scalarBasis a = rowCoordinates a.property a.val.2.1
      (sourceBasis a.val.1 a.val.2.2) := (rowCoordinates_basis _ _ _).symm
  have hb : scalarBasis b = rowCoordinates b.property b.val.2.1
      (sourceBasis b.val.1 b.val.2.2) := (rowCoordinates_basis _ _ _).symm
  rw [ha, hb, gradient_rowCoordinates, gradient_rowCoordinates]
  exact blockEmbedding_orthogonal h _ _

/-- Every off-diagonal pairing is calculated; no diagonal-matrix premise
is imposed on the actual differentiated coefficients. -/
theorem gradient_basis_pairing (a b : EvenIndex) :
    inner ℂ (gradient (scalarBasis a)) (gradient (scalarBasis b)) =
      (SourceCasimirClosure.energy a.val.1 : ℂ) *
        inner ℂ (includeScalar (scalarBasis a)) (includeScalar (scalarBasis b)) := by
  classical
  by_cases hrow : rowOfIndex a = rowOfIndex b
  · rcases a with ⟨⟨m, i, j⟩, hm⟩
    rcases b with ⟨⟨n, k, l⟩, hn⟩
    have hmn : m = n := congrArg (fun r : RowIndex => r.1.val) hrow
    subst n
    have hik : i = k := by
      have h := congrArg (fun r : RowIndex => (r.2 : ℕ)) hrow
      exact Fin.ext h
    subst k
    rw [← rowCoordinates_basis hm i j, ← rowCoordinates_basis hm i l,
      gradient_row_pairing, include_rowCoordinates, include_rowCoordinates,
      LinearIsometry.inner_map_map]
    congr 1
    simp [SourceCasimirClosure.energy, Complex.ofReal_mul, Complex.ofReal_natCast]
  · have hab : a ≠ b := fun h => hrow (congrArg rowOfIndex h)
    rw [distinct_rows_pairing a b hrow, includeScalar_basis, includeScalar_basis,
      orthonormal_iff_ite.mp quotientBasisVector_orthonormal, ite_eq_right hab, mul_zero]

def coreLaplacian : ScalarCore →ₗ[ℂ] ScalarCore :=
  scalarBasis.constr ℂ (fun a =>
    (SourceCasimirClosure.energy a.val.1 : ℂ) • scalarBasis a)

@[simp] theorem coreLaplacian_basis (a : EvenIndex) :
    coreLaplacian (scalarBasis a) =
      (SourceCasimirClosure.energy a.val.1 : ℂ) • scalarBasis a :=
  scalarBasis.constr_basis ℂ _ a

private theorem gradient_basis_pairing_all (a : EvenIndex) (f : ScalarCore) :
    inner ℂ (gradient (scalarBasis a)) (gradient f) =
      (SourceCasimirClosure.energy a.val.1 : ℂ) *
        inner ℂ (includeScalar (scalarBasis a)) (includeScalar f) := by
  have h : (innerSL ℂ (gradient (scalarBasis a))).toLinearMap.comp gradient =
      (SourceCasimirClosure.energy a.val.1 : ℂ) •
        ((innerSL ℂ (includeScalar (scalarBasis a))).toLinearMap.comp includeScalar) := by
    apply scalarBasis.ext
    intro b
    exact gradient_basis_pairing a b
  exact LinearMap.congr_fun h f

/-- Integration by parts for arbitrary finite coefficients, including
all phases and all cross-source terms in the original metric. -/
theorem green_identity (f g : ScalarCore) :
    inner ℂ (gradient f) (gradient g) =
      inner ℂ (includeScalar f) (includeScalar (coreLaplacian g)) := by
  have h : (innerSL ℂ (gradient f)).toLinearMap.comp gradient =
      (innerSL ℂ (includeScalar f)).toLinearMap.comp
        (includeScalar.comp coreLaplacian) := by
    apply scalarBasis.ext
    intro b
    change inner ℂ (gradient f) (gradient (scalarBasis b)) =
      inner ℂ (includeScalar f) (includeScalar (coreLaplacian (scalarBasis b)))
    rw [← inner_conj_symm (gradient f) (gradient (scalarBasis b)),
      gradient_basis_pairing_all, map_mul, Complex.conj_ofReal,
      inner_conj_symm, coreLaplacian_basis, map_smul, inner_smul_right]
  exact LinearMap.congr_fun h g

def coreInclusion : ScalarCore →ₗ[ℂ] SourceQuotientCasimir.finiteCore.domain :=
  scalarBasis.constr ℂ (fun a =>
    ⟨quotientBasisVector a, by
      simpa only [SourceQuotientCasimir.finiteCore, quotientBasis_apply] using
        FiniteEigenbasisCore.basis_mem_domain quotientBasis
          (fun b => SourceCasimirClosure.energy b.val.1) a⟩)

theorem coreInclusion_coe (f : ScalarCore) :
    (coreInclusion f : QuotientL2) = includeScalar f := by
  have h : SourceQuotientCasimir.finiteCore.domain.subtype.comp coreInclusion =
      includeScalar := by
    apply scalarBasis.ext
    intro a
    simp only [LinearMap.comp_apply, coreInclusion, Module.Basis.constr_basis,
      includeScalar_basis, Submodule.subtype_apply]
  exact LinearMap.congr_fun h f

theorem finite_operator_identity (f : ScalarCore) :
    SourceQuotientCasimir.finiteCore (coreInclusion f) =
      includeScalar (coreLaplacian f) := by
  have h : SourceQuotientCasimir.finiteCore.toFun.comp coreInclusion =
      includeScalar.comp coreLaplacian := by
    apply scalarBasis.ext
    intro a
    simp only [LinearMap.comp_apply, coreInclusion, Module.Basis.constr_basis,
      coreLaplacian_basis, map_smul, includeScalar_basis]
    rw [LinearPMap.toFun_eq_coe]
    simpa only [SourceQuotientCasimir.finiteCore, quotientBasis_apply] using
      FiniteEigenbasisCore.basis_action quotientBasis
        (fun b => SourceCasimirClosure.energy b.val.1) a
  exact LinearMap.congr_fun h f

def closedInclusion (f : ScalarCore) : SourceQuotientCasimir.operator.domain :=
  ⟨includeScalar f, by
    rw [← coreInclusion_coe f]
    exact SourceQuotientCasimir.finiteCore_le_operator.1 (coreInclusion f).property⟩

theorem closed_operator_identity (f : ScalarCore) :
    SourceQuotientCasimir.operator (closedInclusion f) =
      includeScalar (coreLaplacian f) := by
  have h := SourceQuotientCasimir.finiteCore_le_operator.2
    (x := coreInclusion f) (y := closedInclusion f) (coreInclusion_coe f)
  exact h.symm.trans (finite_operator_identity f)

theorem closed_green_identity (f g : ScalarCore) :
    inner ℂ (gradient f) (gradient g) =
      inner ℂ (includeScalar f)
        (SourceQuotientCasimir.operator (closedInclusion g)) := by
  rw [closed_operator_identity]
  exact green_identity f g

end GeneratedFoundations.Geometry.SourceScalarKineticOperator

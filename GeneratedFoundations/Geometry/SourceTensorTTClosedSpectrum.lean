module

public import GeneratedFoundations.Geometry.SourceTensorTTField
public import GeneratedFoundations.Operations.SpectralFormLowerBound

/-!
# The closed covariant rough operator on the original TT field

The finite operator is identified with the original covariant differential
on every entire homogeneous TT row. The complete Haar TT basis then gives
its unique self-adjoint closure, full weighted-square domain and uniform
quadratic lower bound. No finite cutoff enters the closed-domain estimate.
-/

@[expose] public section

noncomputable section

open Module
open scoped BigOperators ComplexConjugate LinearPMap lp
open GeneratedFoundations.Geometry.SourceTensorSpectralCore
open GeneratedFoundations.Geometry.SourceTensorTTBlock
open GeneratedFoundations.Geometry.SourceTensorHaarBlock
open GeneratedFoundations.Geometry.SourceTensorHilbertSum
open GeneratedFoundations.Geometry.SourceTensorTTField
open GeneratedFoundations.Operations

namespace GeneratedFoundations.Geometry.SourceTensorTTClosedSpectrum

attribute [local irreducible] ttBasis ttCurlEigenvalue

def rowField (r : RowIndex) : ttSpace r.1.val →ₗ[ℂ] ttField :=
  (ttEmbedding r).toLinearMap.codRestrict ttField (row_mem_ttField r)

theorem row_mem_finiteTTCore (r : RowIndex) (H : ttSpace r.1.val) :
    rowField r H ∈ finiteTTCore := by
  classical
  rw [← (ttBasis r.1.val).sum_repr H, map_sum]
  apply Submodule.sum_mem
  intro j _
  rw [map_smul]
  exact Submodule.smul_mem finiteTTCore _
    (Submodule.subset_span (Set.mem_range_self (⟨r, j⟩ : TTIndex)))

def finiteRough : ttField →ₗ.[ℂ] ttField :=
  FiniteEigenbasisCore.finiteMultiplier ttHilbertBasis roughEigenvalue

theorem finiteRough_domain : finiteRough.domain = finiteTTCore := by
  simp only [finiteRough, FiniteEigenbasisCore.domain_eq, finiteTTCore,
    coe_ttHilbertBasis]

def rowCoreMap (r : RowIndex) : ttSpace r.1.val →ₗ[ℂ] finiteRough.domain :=
  (rowField r).codRestrict finiteRough.domain
    (fun H => finiteRough_domain.symm ▸ row_mem_finiteTTCore r H)

theorem finiteRough_eigenfield (a : TTIndex) :
    finiteRough ⟨eigenfield a, finiteRough_domain.symm ▸
      Submodule.subset_span (Set.mem_range_self a)⟩ =
        (roughEigenvalue a : ℂ) • eigenfield a := by
  simpa only [finiteRough, ttHilbertBasis_apply] using
    FiniteEigenbasisCore.basis_action ttHilbertBasis roughEigenvalue a

/-- The spectral core differentiates every vector in each original TT row,
not merely its selected eigenvectors. -/
theorem finiteRough_row (r : RowIndex) (H : ttSpace r.1.val) :
    finiteRough (rowCoreMap r H) = rowField r (ttRough r.1.val H) := by
  have h : finiteRough.toFun.comp (rowCoreMap r) =
      (rowField r).comp (ttRough r.1.val) := by
    apply (ttBasis r.1.val).toBasis.ext
    intro j
    change finiteRough (rowCoreMap r (ttBasis r.1.val j)) =
      rowField r (ttRough r.1.val (ttBasis r.1.val j))
    calc
      _ = ((ttCurlEigenvalue r.1.val j ^ 2 - 3 : ℝ) : ℂ) •
          rowField r (ttBasis r.1.val j) := finiteRough_eigenfield ⟨r, j⟩
      _ = rowField r
          (((ttCurlEigenvalue r.1.val j ^ 2 - 3 : ℝ) : ℂ) • ttBasis r.1.val j) :=
        ((rowField r).map_smul _ _).symm
      _ = _ := congrArg (rowField r) (ttBasis_rough_eigenvector r.1.val j).symm
  exact LinearMap.congr_fun h H

def closedRough : ttField →ₗ.[ℂ] ttField := finiteRough.closure

theorem closedRough_selfAdjoint : IsSelfAdjoint closedRough :=
  FiniteEigenbasisCore.closure_selfAdjoint ttHilbertBasis roughEigenvalue

theorem closedRough_unique (S : ttField →ₗ.[ℂ] ttField)
    (hS : IsSelfAdjoint S) (hcore : finiteRough ≤ S) : S = closedRough :=
  FiniteEigenbasisCore.selfAdjoint_extension_unique ttHilbertBasis roughEigenvalue
    S hS hcore

theorem closedRough_domain (H : ttField) :
    H ∈ closedRough.domain ↔
      Summable (fun a : TTIndex =>
        roughEigenvalue a ^ 2 * ‖inner ℂ (eigenfield a) H‖ ^ 2) := by
  simpa only [closedRough, finiteRough, ttHilbertBasis_apply] using
    FiniteEigenbasisCore.closure_domain_iff_summable ttHilbertBasis roughEigenvalue H

theorem closedRough_coefficients (H : closedRough.domain) (a : TTIndex) :
    inner ℂ (eigenfield a) (closedRough H) =
      (roughEigenvalue a : ℂ) * inner ℂ (eigenfield a) (H : ttField) := by
  simpa only [closedRough, finiteRough, ttHilbertBasis_apply] using
    FiniteEigenbasisCore.closure_coefficients ttHilbertBasis roughEigenvalue H a

theorem row_mem_closedRough (r : RowIndex) (H : ttSpace r.1.val) :
    rowField r H ∈ closedRough.domain :=
  (FiniteEigenbasisCore.le_closure ttHilbertBasis roughEigenvalue).1
    (rowCoreMap r H).property

theorem closedRough_row (r : RowIndex) (H : ttSpace r.1.val) :
    closedRough ⟨rowField r H, row_mem_closedRough r H⟩ =
      rowField r (ttRough r.1.val H) := by
  have he := FiniteEigenbasisCore.le_closure ttHilbertBasis roughEigenvalue
  exact (he.2 (x := rowCoreMap r H)
    (y := ⟨rowField r H, row_mem_closedRough r H⟩) rfl).symm.trans
      (finiteRough_row r H)

/-- The actual original TT field energy is uniformly coercive on the full
closed domain. The constant was derived in the differential blocks. -/
theorem closedRough_quadratic_lower (H : closedRough.domain) :
    6 * ‖(H : ttField)‖ ^ 2 ≤ (inner ℂ (H : ttField) (closedRough H)).re :=
  SpectralFormLowerBound.closed_quadratic_lower_bound
    ttHilbertBasis roughEigenvalue 6 roughEigenvalue_ge_six H

theorem closedRough_kernel (H : closedRough.domain) (hH : closedRough H = 0) :
    (H : ttField) = 0 := by
  have h := closedRough_quadratic_lower H
  rw [hH, inner_zero_right, Complex.zero_re] at h
  have hz : ‖(H : ttField)‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖(H : ttField)‖]
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)

end GeneratedFoundations.Geometry.SourceTensorTTClosedSpectrum

module

public import GeneratedFoundations.Geometry.SourceOneFormHilbertSum
public import GeneratedFoundations.Operations.FiniteEigenbasisCore

/-!
# Closure of the differentiated curl in the original Haar field space

The source-row embeddings exhaust the actual one-form Haar space. Within
each row we diagonalize the already differentiated curl. Their orthogonal
union therefore gives a complete field eigenbasis, including the gradient
null space. The finite operator agrees with the source differential on
every entire coefficient row, not merely on a supplied list of eigenvalues.

Its unique self-adjoint closure consequently belongs to the original field
space. The closed domain is the full weighted square-summability domain.
-/

@[expose] public section

noncomputable section

open Module
open scoped BigOperators ComplexConjugate LinearPMap
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourceOneFormDifferential
open GeneratedFoundations.Geometry.SourceOneFormSpectralCore
open GeneratedFoundations.Geometry.SourceCoclosedDifferentialBlock
open GeneratedFoundations.Geometry.SourceOneFormHaarBlock
open GeneratedFoundations.Geometry.SourceOneFormHilbertSum
open GeneratedFoundations.Operations

namespace GeneratedFoundations.Geometry.SourceOneFormCurlSpectrum

-- The finite spectral construction is used through its proved basis action.
-- Keeping it folded avoids reopening the choice of eigenvectors in later
-- field-space typeclass and definitional-equality checks.
attribute [local irreducible] curlBasis curlEigenvalue

abbrev CurlIndex := Σ r : RowIndex, Fin (3 * (r.1.val + 1))

def eigenfield (a : CurlIndex) : OneFormL2 :=
  blockEmbedding a.1 (curlBasis a.1.1.val a.2)

def eigenvalue (a : CurlIndex) : ℝ :=
  curlEigenvalue a.1.1.val a.2

theorem eigenfield_orthonormal : Orthonormal ℂ eigenfield := by
  exact OrthogonalFamily.orthonormal_sigma_orthonormal
    (𝕜 := ℂ) (G := fun r : RowIndex => FrameCarrier r.1.val)
    (V := blockEmbedding) blockEmbedding_orthogonal
    (α := fun r : RowIndex => Fin (3 * (r.1.val + 1)))
    (v_family := fun r : RowIndex => curlBasis r.1.val)
    (fun r => (curlBasis r.1.val).orthonormal)

def finiteCurlCore : Submodule ℂ OneFormL2 :=
  Submodule.span ℂ (Set.range eigenfield)

theorem row_mem_finiteCurlCore (r : RowIndex) (A : FrameCarrier r.1.val) :
    blockEmbedding r A ∈ finiteCurlCore := by
  classical
  rw [← (curlBasis r.1.val).sum_repr A, map_sum]
  apply Submodule.sum_mem
  intro j _
  rw [map_smul]
  exact Submodule.smul_mem finiteCurlCore _
    (Submodule.subset_span (Set.mem_range_self (⟨r, j⟩ : CurlIndex)))

theorem finiteCurlCore_dense : Dense (finiteCurlCore : Set OneFormL2) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  apply eq_top_iff.mpr
  refine block_ranges_dense.trans (Submodule.topologicalClosure_mono ?_)
  apply iSup_le
  rintro r A ⟨B, rfl⟩
  exact row_mem_finiteCurlCore r B

def curlHilbertBasis : HilbertBasis CurlIndex ℂ OneFormL2 :=
  HilbertBasis.mk eigenfield_orthonormal
    (eq_top_iff.mp (Submodule.dense_iff_topologicalClosure_eq_top.mp finiteCurlCore_dense))

@[simp] theorem curlHilbertBasis_apply (a : CurlIndex) :
    curlHilbertBasis a = eigenfield a :=
  congrFun (HilbertBasis.coe_mk eigenfield_orthonormal _) a

theorem coe_curlHilbertBasis : (curlHilbertBasis : CurlIndex → OneFormL2) = eigenfield :=
  funext curlHilbertBasis_apply

def finiteCurl : OneFormL2 →ₗ.[ℂ] OneFormL2 :=
  FiniteEigenbasisCore.finiteMultiplier curlHilbertBasis eigenvalue

theorem finiteCurl_domain : finiteCurl.domain = finiteCurlCore := by
  simp only [finiteCurl, FiniteEigenbasisCore.domain_eq, finiteCurlCore,
    coe_curlHilbertBasis]

def rowCoreMap (r : RowIndex) : FrameCarrier r.1.val →ₗ[ℂ] finiteCurl.domain :=
  (blockEmbedding r).toLinearMap.codRestrict finiteCurl.domain
    (fun A => finiteCurl_domain.symm ▸ row_mem_finiteCurlCore r A)

theorem finiteCurl_eigenfield (a : CurlIndex) :
    finiteCurl ⟨eigenfield a, finiteCurl_domain.symm ▸
      Submodule.subset_span (Set.mem_range_self a)⟩ =
        (eigenvalue a : ℂ) • eigenfield a := by
  simpa only [finiteCurl, curlHilbertBasis_apply] using
    FiniteEigenbasisCore.basis_action curlHilbertBasis eigenvalue a

/-- The finite operator is the actual differentiated curl on every source
row. This identifies the operator before closing its graph. -/
theorem finiteCurl_row (r : RowIndex) (A : FrameCarrier r.1.val) :
    finiteCurl (rowCoreMap r A) = blockEmbedding r (curlOperator r.1.val A) := by
  have h : finiteCurl.toFun.comp (rowCoreMap r) =
      (blockEmbedding r).toLinearMap.comp (curlOperator r.1.val) := by
    apply (curlBasis r.1.val).toBasis.ext
    intro j
    change finiteCurl (rowCoreMap r (curlBasis r.1.val j)) =
      blockEmbedding r (curlOperator r.1.val (curlBasis r.1.val j))
    rw [curlBasis_eigenvector, map_smul]
    exact finiteCurl_eigenfield ⟨r, j⟩
  exact LinearMap.congr_fun h A

def closedCurl : OneFormL2 →ₗ.[ℂ] OneFormL2 := finiteCurl.closure

theorem closedCurl_selfAdjoint : IsSelfAdjoint closedCurl :=
  FiniteEigenbasisCore.closure_selfAdjoint curlHilbertBasis eigenvalue

theorem closedCurl_unique (S : OneFormL2 →ₗ.[ℂ] OneFormL2)
    (hS : IsSelfAdjoint S) (hcore : finiteCurl ≤ S) : S = closedCurl :=
  FiniteEigenbasisCore.selfAdjoint_extension_unique curlHilbertBasis eigenvalue S hS hcore

/-- The domain includes every Haar field with square-summable differentiated
coefficients; it is not restricted to finite source histories. -/
theorem closedCurl_domain (A : OneFormL2) :
    A ∈ closedCurl.domain ↔
      Summable (fun a : CurlIndex => eigenvalue a ^ 2 * ‖inner ℂ (eigenfield a) A‖ ^ 2) := by
  simpa only [closedCurl, finiteCurl, curlHilbertBasis_apply] using
    FiniteEigenbasisCore.closure_domain_iff_summable curlHilbertBasis eigenvalue A

theorem closedCurl_coefficients (A : closedCurl.domain) (a : CurlIndex) :
    inner ℂ (eigenfield a) (closedCurl A) =
      (eigenvalue a : ℂ) * inner ℂ (eigenfield a) (A : OneFormL2) := by
  simpa only [closedCurl, finiteCurl, curlHilbertBasis_apply] using
    FiniteEigenbasisCore.closure_coefficients curlHilbertBasis eigenvalue A a

end GeneratedFoundations.Geometry.SourceOneFormCurlSpectrum

module

public import GeneratedFoundations.Geometry.SourceSpinorHilbertSum
public import GeneratedFoundations.Operations.SpectralFormLowerBound

/-!
# The closed source Dirac operator in the original Haar field space

The row embeddings exhaust the original spinor space. Their bases are
obtained by diagonalizing the differentiated source operator, whose
continuous representatives were identified before taking a graph closure.
This gives a unique self-adjoint closure with its full coefficient domain.
-/

@[expose] public section

noncomputable section

open Module
open scoped BigOperators ComplexConjugate LinearPMap lp
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourceSpinorSpectralCore
open GeneratedFoundations.Geometry.SourceSpinorHaarBlock
open GeneratedFoundations.Geometry.SourceSpinorHilbertSum
open GeneratedFoundations.Operations

namespace GeneratedFoundations.Geometry.SourceSpinorClosedSpectrum

attribute [local irreducible] kineticBasis kineticEigenvalue

abbrev SpinIndex := Σ r : RowIndex, Fin (2 * (r.1 + 1))

def eigenfield (a : SpinIndex) : SpinorL2 :=
  blockEmbedding a.1 (kineticBasis a.1.1 a.2)

def eigenvalue (a : SpinIndex) : ℝ := kineticEigenvalue a.1.1 a.2 + 3 / 2

theorem eigenfield_orthonormal : Orthonormal ℂ eigenfield :=
  OrthogonalFamily.orthonormal_sigma_orthonormal
    (𝕜 := ℂ) (G := fun r : RowIndex => SpinorBlock r.1)
    (V := blockEmbedding) blockEmbedding_orthogonal
    (α := fun r : RowIndex => Fin (2 * (r.1 + 1)))
    (v_family := fun r : RowIndex => kineticBasis r.1)
    (fun r => (kineticBasis r.1).orthonormal)

def finiteDiracCore : Submodule ℂ SpinorL2 :=
  Submodule.span ℂ (Set.range eigenfield)

theorem row_mem_finiteDiracCore (r : RowIndex) (A : SpinorBlock r.1) :
    blockEmbedding r A ∈ finiteDiracCore := by
  classical
  rw [← (kineticBasis r.1).sum_repr A, map_sum]
  apply Submodule.sum_mem
  intro j _
  rw [map_smul]
  exact Submodule.smul_mem finiteDiracCore _
    (Submodule.subset_span (Set.mem_range_self (⟨r, j⟩ : SpinIndex)))

theorem finiteDiracCore_dense : Dense (finiteDiracCore : Set SpinorL2) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  apply eq_top_iff.mpr
  refine block_ranges_dense.trans (Submodule.topologicalClosure_mono ?_)
  apply iSup_le
  rintro r A ⟨B, rfl⟩
  exact row_mem_finiteDiracCore r B

def diracHilbertBasis : HilbertBasis SpinIndex ℂ SpinorL2 :=
  HilbertBasis.mk eigenfield_orthonormal
    (eq_top_iff.mp (Submodule.dense_iff_topologicalClosure_eq_top.mp finiteDiracCore_dense))

@[simp] theorem diracHilbertBasis_apply (a : SpinIndex) :
    diracHilbertBasis a = eigenfield a :=
  congrFun (HilbertBasis.coe_mk eigenfield_orthonormal _) a

theorem coe_diracHilbertBasis : (diracHilbertBasis : SpinIndex → SpinorL2) = eigenfield :=
  funext diracHilbertBasis_apply

def finiteDirac : SpinorL2 →ₗ.[ℂ] SpinorL2 :=
  FiniteEigenbasisCore.finiteMultiplier diracHilbertBasis eigenvalue

theorem finiteDirac_domain : finiteDirac.domain = finiteDiracCore := by
  simp only [finiteDirac, FiniteEigenbasisCore.domain_eq, finiteDiracCore,
    coe_diracHilbertBasis]

def rowCoreMap (r : RowIndex) : SpinorBlock r.1 →ₗ[ℂ] finiteDirac.domain :=
  (blockEmbedding r).toLinearMap.codRestrict finiteDirac.domain
    (fun A => finiteDirac_domain.symm ▸ row_mem_finiteDiracCore r A)

theorem finiteDirac_eigenfield (a : SpinIndex) :
    finiteDirac ⟨eigenfield a, finiteDirac_domain.symm ▸
      Submodule.subset_span (Set.mem_range_self a)⟩ =
        (eigenvalue a : ℂ) • eigenfield a := by
  simpa only [finiteDirac, diracHilbertBasis_apply] using
    FiniteEigenbasisCore.basis_action diracHilbertBasis eigenvalue a

/-- Identification with the differentiated operator holds on every entire
source row. It is not restricted to selected eigenfields. -/
theorem finiteDirac_row (r : RowIndex) (A : SpinorBlock r.1) :
    finiteDirac (rowCoreMap r A) = blockEmbedding r (diracBlock r.1 A) := by
  have h : finiteDirac.toFun.comp (rowCoreMap r) =
      (blockEmbedding r).toLinearMap.comp (diracBlock r.1) := by
    apply (kineticBasis r.1).toBasis.ext
    intro j
    change finiteDirac (rowCoreMap r (kineticBasis r.1 j)) =
      blockEmbedding r (diracBlock r.1 (kineticBasis r.1 j))
    rw [diracBlock_basis, map_smul]
    exact finiteDirac_eigenfield ⟨r, j⟩
  exact LinearMap.congr_fun h A

def closedDirac : SpinorL2 →ₗ.[ℂ] SpinorL2 := finiteDirac.closure

theorem closedDirac_selfAdjoint : IsSelfAdjoint closedDirac :=
  FiniteEigenbasisCore.closure_selfAdjoint diracHilbertBasis eigenvalue

theorem closedDirac_unique (S : SpinorL2 →ₗ.[ℂ] SpinorL2)
    (hS : IsSelfAdjoint S) (hcore : finiteDirac ≤ S) : S = closedDirac :=
  FiniteEigenbasisCore.selfAdjoint_extension_unique diracHilbertBasis eigenvalue S hS hcore

theorem closedDirac_domain (A : SpinorL2) :
    A ∈ closedDirac.domain ↔
      Summable (fun a : SpinIndex => eigenvalue a ^ 2 * ‖inner ℂ (eigenfield a) A‖ ^ 2) := by
  simpa only [closedDirac, finiteDirac, diracHilbertBasis_apply] using
    FiniteEigenbasisCore.closure_domain_iff_summable diracHilbertBasis eigenvalue A

theorem closedDirac_coefficients (A : closedDirac.domain) (a : SpinIndex) :
    inner ℂ (eigenfield a) (closedDirac A) =
      (eigenvalue a : ℂ) * inner ℂ (eigenfield a) (A : SpinorL2) := by
  simpa only [closedDirac, finiteDirac, diracHilbertBasis_apply] using
    FiniteEigenbasisCore.closure_coefficients diracHilbertBasis eigenvalue A a

theorem eigenvalue_sq_lower (a : SpinIndex) : (3 / 2 : ℝ) ^ 2 ≤ eigenvalue a ^ 2 :=
  diracEigenvalue_sq_lower a.1.1 a.2

/-- The Dirac gap holds for every original Haar field in the complete closed
domain, with a constant independent of a finite spectral cutoff. -/
theorem closedDirac_norm_lower (F : closedDirac.domain) :
    (3 / 2 : ℝ) ^ 2 * ‖(F : SpinorL2)‖ ^ 2 ≤ ‖closedDirac F‖ ^ 2 :=
  SpectralFormLowerBound.closed_norm_lower_bound diracHilbertBasis eigenvalue
    ((3 / 2 : ℝ) ^ 2) eigenvalue_sq_lower F

end GeneratedFoundations.Geometry.SourceSpinorClosedSpectrum

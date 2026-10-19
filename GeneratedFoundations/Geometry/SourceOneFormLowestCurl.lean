module

public import GeneratedFoundations.Geometry.SourceOneFormClosedHodge

/-!
# Sharpness of the complete coclosed differential lower bound

The source degree-zero matrix coefficient and one original frame direction
give a unit Haar field. Its differentiated curl is twice the same field.
It belongs to the full closed domain and to the weak-divergence kernel.
Thus the lower bound four is attained by an actual field, independently
of a representation-labelled mode table.
-/

@[expose] public section

noncomputable section

open Module
open scoped BigOperators ComplexConjugate LinearPMap lp
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourceSchurOrthogonality
open GeneratedFoundations.Geometry.SourceOneFormDifferential
open GeneratedFoundations.Geometry.SourceOneFormSpectralCore
open GeneratedFoundations.Geometry.SourceOneFormHaarBlock
open GeneratedFoundations.Geometry.SourceOneFormHilbertSum
open GeneratedFoundations.Geometry.SourceOneFormCurlSpectrum
open GeneratedFoundations.Geometry.SourceOneFormClosedHodge
open GeneratedFoundations.Operations

namespace GeneratedFoundations.Geometry.SourceOneFormLowestCurl

theorem row_mem_closedCurl (r : RowIndex) (A : FrameCarrier r.1.val) :
    blockEmbedding r A ∈ closedCurl.domain :=
  (FiniteEigenbasisCore.le_closure curlHilbertBasis eigenvalue).1 (rowCoreMap r A).property

theorem closedCurl_row (r : RowIndex) (A : FrameCarrier r.1.val) :
    closedCurl ⟨blockEmbedding r A, row_mem_closedCurl r A⟩ =
      blockEmbedding r (curlOperator r.1.val A) := by
  have h := FiniteEigenbasisCore.le_closure curlHilbertBasis eigenvalue
  exact (h.2 (x := rowCoreMap r A)
    (y := ⟨blockEmbedding r A, row_mem_closedCurl r A⟩) rfl).symm.trans
      (finiteCurl_row r A)

def lowestRow : RowIndex := ⟨⟨0, by decide⟩, 0⟩

def lowestBlock : FrameCarrier 0 := PiLp.single 2 0 (sourceBasis 0 0)

theorem lowestBlock_norm : ‖lowestBlock‖ = 1 := by
  simp only [lowestBlock, PiLp.norm_single, OrthonormalBasis.norm_eq_one]

theorem lowestBlock_curl : curlOperator 0 lowestBlock = (2 : ℂ) • lowestBlock := by
  apply (WithLp.equiv 2 (Fin 3 → HilbertCarrier 0)).injective
  exact coefficientCurl_degree_zero (fun i => lowestBlock i)

def lowestField : OneFormL2 := blockEmbedding lowestRow lowestBlock

theorem lowestField_norm : ‖lowestField‖ = 1 :=
  ((blockEmbedding lowestRow).norm_map lowestBlock).trans lowestBlock_norm

theorem lowestField_mem_domain : lowestField ∈ closedCurl.domain :=
  row_mem_closedCurl lowestRow lowestBlock

def lowestDomain : closedCurl.domain := ⟨lowestField, lowestField_mem_domain⟩

theorem lowestField_curl : closedCurl lowestDomain = (2 : ℂ) • lowestField := by
  exact (closedCurl_row lowestRow lowestBlock).trans
    ((congrArg (fun B : FrameCarrier 0 => blockEmbedding lowestRow B)
      lowestBlock_curl).trans
      ((blockEmbedding lowestRow).map_smul (2 : ℂ) lowestBlock))

theorem lowestField_coclosed : lowestField ∈ coclosedField := by
  have h := closedCurl_coclosed lowestDomain
  rw [lowestField_curl] at h
  have hh := coclosedField.smul_mem ((2 : ℂ)⁻¹) h
  simpa only [smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul] using hh

/-- The differential bound is attained in the complete physical field
space; four is therefore its exact squared lower edge. -/
theorem complete_coclosed_bottom :
    (∀ A : closedCurl.domain, A.val ∈ coclosedField →
      4 * ‖A.val‖ ^ 2 ≤ ‖closedCurl A‖ ^ 2) ∧
    (‖lowestField‖ = 1 ∧ lowestField ∈ coclosedField ∧
      ‖closedCurl lowestDomain‖ ^ 2 = 4) := by
  refine ⟨closedCurl_coclosed_coercivity,
    lowestField_norm, lowestField_coclosed, ?_⟩
  rw [lowestField_curl, norm_smul, lowestField_norm]
  norm_num

end GeneratedFoundations.Geometry.SourceOneFormLowestCurl

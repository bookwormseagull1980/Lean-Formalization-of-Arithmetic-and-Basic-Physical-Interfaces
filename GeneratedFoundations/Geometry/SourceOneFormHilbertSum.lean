module

public import GeneratedFoundations.Geometry.SourceOneFormCompleteness

/-!
# Exhaustion by the differentiated source one-form blocks

The embeddings are the normalized matrix coefficients in the original
quotient Haar space. Distinct source rows are orthogonal by the existing
Schur theorem. Their ranges contain every vector of the complete field
basis, so the resulting Hilbert sum exhausts the actual one-form space.
The block coordinates therefore preserve all fields, rather than specifying
an auxiliary sequence model with an assumed completeness property.
-/

@[expose] public section

noncomputable section

open MeasureTheory Module
open scoped BigOperators ComplexConjugate lp
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourceSchurOrthogonality
open GeneratedFoundations.Geometry.SourceCompleteCoefficients
open GeneratedFoundations.Geometry.SourceQuotientHilbert
open GeneratedFoundations.Geometry.SourceOneFormSpectralCore
open GeneratedFoundations.Geometry.SourceOneFormHaarBlock
open GeneratedFoundations.Geometry.SourceOneFormCompleteness

namespace GeneratedFoundations.Geometry.SourceOneFormHilbertSum

abbrev RowIndex := Σ m : {d : ℕ // Even d}, Fin (m.val + 1)

def rowOfIndex (a : EvenIndex) : RowIndex :=
  ⟨⟨a.val.1, a.property⟩, a.val.2.1⟩

def blockEmbedding (r : RowIndex) : FrameCarrier r.1.val →ₗᵢ[ℂ] OneFormL2 :=
  frameRowIsometry r.1.property r.2

private theorem scalar_rows_orthogonal (r s : RowIndex) (hrs : r ≠ s)
    (a : HilbertCarrier r.1.val) (b : HilbertCarrier s.1.val) :
    inner ℂ (rowIsometry r.1.property r.2 a)
      (rowIsometry s.1.property s.2 b) = 0 := by
  classical
  have hindices (j : Fin (r.1.val + 1)) (k : Fin (s.1.val + 1)) :
      (⟨⟨r.1.val, r.2, j⟩, r.1.property⟩ : EvenIndex) ≠
        ⟨⟨s.1.val, s.2, k⟩, s.1.property⟩ := by
    intro h
    exact hrs (congrArg rowOfIndex h)
  have ha : rowIsometry r.1.property r.2 a =
      ∑ j : Fin (r.1.val + 1), (sourceBasis r.1.val).repr a j •
        quotientBasisVector ⟨⟨r.1.val, r.2, j⟩, r.1.property⟩ := by
    nth_rw 1 [← (sourceBasis r.1.val).sum_repr a]
    simp only [map_sum, map_smul, rowIsometry_basis]
  have hb : rowIsometry s.1.property s.2 b =
      ∑ k : Fin (s.1.val + 1), (sourceBasis s.1.val).repr b k •
        quotientBasisVector ⟨⟨s.1.val, s.2, k⟩, s.1.property⟩ := by
    nth_rw 1 [← (sourceBasis s.1.val).sum_repr b]
    simp only [map_sum, map_smul, rowIsometry_basis]
  rw [ha, hb]
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    orthonormal_iff_ite.mp quotientBasisVector_orthonormal, ite_eq_right (hindices _ _),
    mul_zero, Finset.sum_const_zero]

theorem blockEmbedding_orthogonal :
    OrthogonalFamily ℂ (fun r : RowIndex => FrameCarrier r.1.val) blockEmbedding := by
  intro r s hrs A B
  change (∑ i : Fin 3,
    inner ℂ (rowIsometry r.1.property r.2 (A i))
      (rowIsometry s.1.property s.2 (B i))) = 0
  apply Finset.sum_eq_zero
  intro i _
  exact scalar_rows_orthogonal r s hrs (A i) (B i)

theorem blockEmbedding_single (r : Fin 3) (a : EvenIndex) :
    blockEmbedding (rowOfIndex a)
      (PiLp.single 2 r (sourceBasis a.val.1 a.val.2.2)) = fieldBasisVector (r, a) := by
  apply (WithLp.equiv 2 (Fin 3 → QuotientL2)).injective
  funext s
  by_cases hsr : s = r
  · subst s
    change rowIsometry a.property a.val.2.1
      (((PiLp.single 2 r (sourceBasis a.val.1 a.val.2.2)) : FrameCarrier a.val.1) r) =
        (PiLp.single 2 r (quotientBasisVector a) : OneFormL2) r
    simp only [PiLp.single_eq_same, rowIsometry_basis]
  · change rowIsometry a.property a.val.2.1
      (((PiLp.single 2 r (sourceBasis a.val.1 a.val.2.2)) : FrameCarrier a.val.1) s) =
        (PiLp.single 2 r (quotientBasisVector a) : OneFormL2) s
    simp only [PiLp.single_eq_of_ne _ hsr, map_zero]

theorem finiteFieldCore_le_block_ranges :
    finiteFieldCore ≤ ⨆ r : RowIndex, LinearMap.range (blockEmbedding r).toLinearMap := by
  apply Submodule.span_le.mpr
  rintro A ⟨⟨r, a⟩, rfl⟩
  apply (le_iSup (fun s : RowIndex => LinearMap.range (blockEmbedding s).toLinearMap)
    (rowOfIndex a))
  exact ⟨PiLp.single 2 r (sourceBasis a.val.1 a.val.2.2), blockEmbedding_single r a⟩

theorem block_ranges_dense :
    ⊤ ≤ (⨆ r : RowIndex, LinearMap.range (blockEmbedding r).toLinearMap).topologicalClosure := by
  have hd : finiteFieldCore.topologicalClosure = ⊤ :=
    Submodule.dense_iff_topologicalClosure_eq_top.mp finiteFieldCore_dense
  rw [← hd]
  exact Submodule.topologicalClosure_mono finiteFieldCore_le_block_ranges

/-- The full quotient one-form Haar space, with no missing row or component. -/
theorem completeHilbertSum :
    IsHilbertSum ℂ (fun r : RowIndex => FrameCarrier r.1.val) blockEmbedding :=
  IsHilbertSum.mk blockEmbedding_orthogonal block_ranges_dense

def blockCoordinates :
    OneFormL2 ≃ₗᵢ[ℂ] lp (fun r : RowIndex => FrameCarrier r.1.val) 2 :=
  completeHilbertSum.linearIsometryEquiv

/-- Inverting the block coordinates recovers the original Haar field as an
actual convergent sum of its normalized source matrix coefficients. -/
theorem hasSum_block_reconstruction (A : OneFormL2) :
    HasSum (fun r : RowIndex => blockEmbedding r (blockCoordinates A r)) A := by
  simpa only [blockCoordinates, LinearIsometryEquiv.symm_apply_apply]
    using completeHilbertSum.hasSum_linearIsometryEquiv_symm (blockCoordinates A)

end GeneratedFoundations.Geometry.SourceOneFormHilbertSum

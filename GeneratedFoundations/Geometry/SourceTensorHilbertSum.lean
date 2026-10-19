module

public import GeneratedFoundations.Geometry.SourceTensorHaarBlock
public import GeneratedFoundations.Geometry.SourceOneFormHilbertSum

/-!
# Complete homogeneous rows of the original tensor field

The same scalar Schur orthogonality used for one-forms applies to each of
the nine tensor components. Every vector of the complete tensor Haar basis
belongs to a row range. The resulting Hilbert sum is therefore an isometric
description of the original full field, not an independently postulated
sequence space.
-/

@[expose] public section

noncomputable section

open Module
open scoped BigOperators ComplexConjugate lp
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourceSchurOrthogonality
open GeneratedFoundations.Geometry.SourceCompleteCoefficients
open GeneratedFoundations.Geometry.SourceQuotientHilbert
open GeneratedFoundations.Geometry.SourceOneFormHaarBlock
open GeneratedFoundations.Geometry.SourceTensorSpectralCore
open GeneratedFoundations.Geometry.SourceTensorHaarBlock

namespace GeneratedFoundations.Geometry.SourceTensorHilbertSum

abbrev RowIndex := SourceOneFormHilbertSum.RowIndex

abbrev rowOfIndex := SourceOneFormHilbertSum.rowOfIndex

def blockEmbedding (r : RowIndex) : TensorBlock r.1.val →ₗᵢ[ℂ] TensorL2 :=
  tensorRowIsometry r.1.property r.2

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
    OrthogonalFamily ℂ (fun r : RowIndex => TensorBlock r.1.val) blockEmbedding := by
  intro r s hrs H K
  change (∑ ab : Fin 3 × Fin 3,
    inner ℂ (rowIsometry r.1.property r.2 (H ab))
      (rowIsometry s.1.property s.2 (K ab))) = 0
  exact Finset.sum_eq_zero fun ab _ => scalar_rows_orthogonal r s hrs (H ab) (K ab)

theorem blockEmbedding_single (ab : Fin 3 × Fin 3) (a : EvenIndex) :
    blockEmbedding (rowOfIndex a)
      (PiLp.single 2 ab (sourceBasis a.val.1 a.val.2.2)) = fieldBasisVector (ab, a) := by
  apply (WithLp.equiv 2 (Fin 3 × Fin 3 → QuotientL2)).injective
  funext cd
  by_cases hcd : cd = ab
  · subst cd
    change rowIsometry a.property a.val.2.1
      (((PiLp.single 2 ab (sourceBasis a.val.1 a.val.2.2)) : TensorBlock a.val.1) ab) =
        (PiLp.single 2 ab (quotientBasisVector a) : TensorL2) ab
    simp only [PiLp.single_eq_same, rowIsometry_basis]
  · change rowIsometry a.property a.val.2.1
      (((PiLp.single 2 ab (sourceBasis a.val.1 a.val.2.2)) : TensorBlock a.val.1) cd) =
        (PiLp.single 2 ab (quotientBasisVector a) : TensorL2) cd
    simp only [PiLp.single_eq_of_ne _ hcd, map_zero]

theorem finiteFieldCore_le_block_ranges :
    finiteFieldCore ≤ ⨆ r : RowIndex, LinearMap.range (blockEmbedding r).toLinearMap := by
  apply Submodule.span_le.mpr
  rintro H ⟨⟨ab, a⟩, rfl⟩
  apply (le_iSup (fun s : RowIndex => LinearMap.range (blockEmbedding s).toLinearMap)
    (rowOfIndex a))
  exact ⟨PiLp.single 2 ab (sourceBasis a.val.1 a.val.2.2), blockEmbedding_single ab a⟩

theorem block_ranges_dense :
    ⊤ ≤ (⨆ r : RowIndex, LinearMap.range (blockEmbedding r).toLinearMap).topologicalClosure := by
  have hd : finiteFieldCore.topologicalClosure = ⊤ :=
    Submodule.dense_iff_topologicalClosure_eq_top.mp finiteFieldCore_dense
  rw [← hd]
  exact Submodule.topologicalClosure_mono finiteFieldCore_le_block_ranges

theorem completeHilbertSum :
    IsHilbertSum ℂ (fun r : RowIndex => TensorBlock r.1.val) blockEmbedding :=
  IsHilbertSum.mk blockEmbedding_orthogonal block_ranges_dense

def blockCoordinates : TensorL2 ≃ₗᵢ[ℂ] lp (fun r : RowIndex => TensorBlock r.1.val) 2 :=
  completeHilbertSum.linearIsometryEquiv

theorem hasSum_block_reconstruction (H : TensorL2) :
    HasSum (fun r : RowIndex => blockEmbedding r (blockCoordinates H r)) H := by
  simpa only [blockCoordinates, LinearIsometryEquiv.symm_apply_apply] using
    completeHilbertSum.hasSum_linearIsometryEquiv_symm (blockCoordinates H)

theorem blockCoordinates_embedding (r : RowIndex) (H : TensorBlock r.1.val) :
    blockCoordinates (blockEmbedding r H) = lp.single 2 r H := by
  classical
  apply blockCoordinates.symm.injective
  rw [LinearIsometryEquiv.symm_apply_apply]
  exact (completeHilbertSum.linearIsometryEquiv_symm_apply_single H).symm

theorem inner_blockEmbedding (r : RowIndex) (H : TensorBlock r.1.val) (K : TensorL2) :
    inner ℂ (blockEmbedding r H) K = inner ℂ H (blockCoordinates K r) := by
  calc
    _ = inner ℂ (blockCoordinates (blockEmbedding r H)) (blockCoordinates K) :=
      (blockCoordinates.inner_map_map (blockEmbedding r H) K).symm
    _ = inner ℂ (lp.single 2 r H) (blockCoordinates K) := by
      rw [blockCoordinates_embedding]
    _ = _ := lp.inner_single_left (𝕜 := ℂ)
      (G := fun s : RowIndex => TensorBlock s.1.val) r H (blockCoordinates K)

end GeneratedFoundations.Geometry.SourceTensorHilbertSum

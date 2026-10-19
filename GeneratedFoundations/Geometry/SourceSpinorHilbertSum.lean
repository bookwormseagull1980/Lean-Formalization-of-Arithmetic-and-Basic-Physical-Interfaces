module

public import GeneratedFoundations.Geometry.SourceSpinorHaarBlock

/-!
# Exhaustion of the original Haar spinor by differentiated source rows

Schur orthogonality separates different rows. The complete scalar Haar
basis proves that their two-component images exhaust the original field
space, before a self-adjoint spin operator is closed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Module
open scoped BigOperators ComplexConjugate lp
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourceSchurOrthogonality
open GeneratedFoundations.Geometry.SourceCompleteCoefficients
open GeneratedFoundations.Geometry.SourceSpinorSpectralCore
open GeneratedFoundations.Geometry.SourceSpinorHaarBlock

namespace GeneratedFoundations.Geometry.SourceSpinorHilbertSum

abbrev RowIndex := Σ m : ℕ, Fin (m + 1)

def rowOfIndex (a : Index) : RowIndex := ⟨a.1, a.2.1⟩

def blockEmbedding (r : RowIndex) : SpinorBlock r.1 →ₗᵢ[ℂ] SpinorL2 :=
  spinRowIsometry r.1 r.2

private theorem scalar_rows_orthogonal (r s : RowIndex) (hrs : r ≠ s)
    (a : HilbertCarrier r.1) (b : HilbertCarrier s.1) :
    inner ℂ (scalarRowIsometry r.1 r.2 a)
      (scalarRowIsometry s.1 s.2 b) = 0 := by
  classical
  have hindices (j : Fin (r.1 + 1)) (k : Fin (s.1 + 1)) :
      (⟨r.1, r.2, j⟩ : Index) ≠ ⟨s.1, s.2, k⟩ := by
    intro h
    exact hrs (congrArg rowOfIndex h)
  have ha : scalarRowIsometry r.1 r.2 a =
      ∑ j : Fin (r.1 + 1), (sourceBasis r.1).repr a j •
        basisVector ⟨r.1, r.2, j⟩ := by
    nth_rw 1 [← (sourceBasis r.1).sum_repr a]
    simp only [map_sum, map_smul, scalarRowIsometry_basis]
  have hb : scalarRowIsometry s.1 s.2 b =
      ∑ k : Fin (s.1 + 1), (sourceBasis s.1).repr b k •
        basisVector ⟨s.1, s.2, k⟩ := by
    nth_rw 1 [← (sourceBasis s.1).sum_repr b]
    simp only [map_sum, map_smul, scalarRowIsometry_basis]
  rw [ha, hb]
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    orthonormal_iff_ite.mp basisVector_orthonormal, ite_eq_right (hindices _ _), mul_zero,
    Finset.sum_const_zero]

theorem blockEmbedding_orthogonal :
    OrthogonalFamily ℂ (fun r : RowIndex => SpinorBlock r.1) blockEmbedding := by
  intro r s hrs A B
  change (∑ i : Fin 2,
    inner ℂ (scalarRowIsometry r.1 r.2 (A i))
      (scalarRowIsometry s.1 s.2 (B i))) = 0
  exact Finset.sum_eq_zero fun i _ => scalar_rows_orthogonal r s hrs (A i) (B i)

theorem blockEmbedding_single (r : Fin 2) (a : Index) :
    blockEmbedding (rowOfIndex a)
      (PiLp.single 2 r (sourceBasis a.1 a.2.2)) = fieldBasisVector (r, a) := by
  apply (WithLp.equiv 2 (Fin 2 → SourceL2)).injective
  funext s
  by_cases hsr : s = r
  · subst s
    change scalarRowIsometry a.1 a.2.1
      (((PiLp.single 2 r (sourceBasis a.1 a.2.2)) : SpinorBlock a.1) r) =
        (PiLp.single 2 r (basisVector a) : SpinorL2) r
    simp only [PiLp.single_eq_same, scalarRowIsometry_basis]
  · change scalarRowIsometry a.1 a.2.1
      (((PiLp.single 2 r (sourceBasis a.1 a.2.2)) : SpinorBlock a.1) s) =
        (PiLp.single 2 r (basisVector a) : SpinorL2) s
    simp only [PiLp.single_eq_of_ne _ hsr, map_zero]

theorem finiteFieldCore_le_block_ranges :
    finiteFieldCore ≤ ⨆ r : RowIndex, LinearMap.range (blockEmbedding r).toLinearMap := by
  apply Submodule.span_le.mpr
  rintro A ⟨⟨r, a⟩, rfl⟩
  apply (le_iSup (fun s : RowIndex => LinearMap.range (blockEmbedding s).toLinearMap)
    (rowOfIndex a))
  exact ⟨PiLp.single 2 r (sourceBasis a.1 a.2.2), blockEmbedding_single r a⟩

theorem block_ranges_dense :
    ⊤ ≤ (⨆ r : RowIndex, LinearMap.range (blockEmbedding r).toLinearMap).topologicalClosure := by
  have hd : finiteFieldCore.topologicalClosure = ⊤ :=
    Submodule.dense_iff_topologicalClosure_eq_top.mp finiteFieldCore_dense
  rw [← hd]
  exact Submodule.topologicalClosure_mono finiteFieldCore_le_block_ranges

theorem completeHilbertSum :
    IsHilbertSum ℂ (fun r : RowIndex => SpinorBlock r.1) blockEmbedding :=
  IsHilbertSum.mk blockEmbedding_orthogonal block_ranges_dense

def blockCoordinates : SpinorL2 ≃ₗᵢ[ℂ] lp (fun r : RowIndex => SpinorBlock r.1) 2 :=
  completeHilbertSum.linearIsometryEquiv

theorem hasSum_block_reconstruction (A : SpinorL2) :
    HasSum (fun r : RowIndex => blockEmbedding r (blockCoordinates A r)) A := by
  simpa only [blockCoordinates, LinearIsometryEquiv.symm_apply_apply] using
    completeHilbertSum.hasSum_linearIsometryEquiv_symm (blockCoordinates A)

end GeneratedFoundations.Geometry.SourceSpinorHilbertSum

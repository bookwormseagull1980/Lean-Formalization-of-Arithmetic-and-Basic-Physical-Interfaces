module

public import GeneratedFoundations.Geometry.SourceTensorHilbertSum
public import GeneratedFoundations.Geometry.SourceTensorTTBranches

/-!
# The full weak TT kernel in the original tensor Haar space

Symmetry, trace and divergence are tested on every homogeneous source row.
These tests are the original tensor differential constraints. Their joint
kernel is closed in the full nine-component field norm. The differentiated
TT bases exhaust this kernel, including every source degree and row.
-/

@[expose] public section

noncomputable section

open Module
open scoped BigOperators ComplexConjugate lp
open GeneratedFoundations.Geometry.SourceTensorSpectralCore
open GeneratedFoundations.Geometry.SourceTensorTTBlock
open GeneratedFoundations.Geometry.SourceTensorHaarBlock
open GeneratedFoundations.Geometry.SourceTensorHilbertSum

namespace GeneratedFoundations.Geometry.SourceTensorTTField

attribute [local irreducible] ttBasis ttCurlEigenvalue

def rowCoordinate (r : RowIndex) : TensorL2 →L[ℂ] TensorBlock r.1.val :=
  (lp.evalCLM ℂ (fun s : RowIndex => TensorBlock s.1.val) 2 r).comp
    blockCoordinates.toContinuousLinearEquiv.toContinuousLinearMap

def ttField : Submodule ℂ TensorL2 :=
  ⨅ r : RowIndex, (ttSpace r.1.val).comap (rowCoordinate r).toLinearMap

instance ttFieldNormed : NormedAddCommGroup ttField :=
  Submodule.normedAddCommGroup (𝕜 := ℂ) (E := TensorL2) ttField

instance ttFieldInner : InnerProductSpace ℂ ttField :=
  Submodule.innerProductSpace (𝕜 := ℂ) (E := TensorL2) ttField

theorem mem_ttField (H : TensorL2) : H ∈ ttField ↔
    ∀ r : RowIndex, blockCoordinates H r ∈ ttSpace r.1.val := by
  simp only [ttField, Submodule.mem_iInf, Submodule.mem_comap]
  rfl

theorem ttField_isClosed : IsClosed (ttField : Set TensorL2) := by
  have h (r : RowIndex) :
      IsClosed ((ttSpace r.1.val).comap (rowCoordinate r).toLinearMap : Set TensorL2) :=
    (ttSpace r.1.val).closed_of_finiteDimensional.preimage (rowCoordinate r).continuous
  simpa only [ttField, Submodule.coe_iInf] using isClosed_iInter h

instance ttFieldComplete : CompleteSpace ttField :=
  ttField_isClosed.isComplete.completeSpace_coe

theorem row_mem_ttField (r : RowIndex) (H : ttSpace r.1.val) :
    blockEmbedding r (H : TensorBlock r.1.val) ∈ ttField := by
  classical
  rw [mem_ttField]
  intro s
  rw [blockCoordinates_embedding]
  by_cases hsr : s = r
  · subst s
    rw [lp.single_apply_self]
    exact H.property
  · rw [lp.single_apply_ne _ _ _ hsr]
    exact (ttSpace s.1.val).zero_mem

def ttEmbedding (r : RowIndex) : ttSpace r.1.val →ₗᵢ[ℂ] TensorL2 :=
  (blockEmbedding r).comp (ttSpace r.1.val).subtypeₗᵢ

theorem ttEmbedding_orthogonal :
    OrthogonalFamily ℂ (fun r : RowIndex => ttSpace r.1.val) ttEmbedding := by
  intro r s hrs H K
  exact blockEmbedding_orthogonal hrs H K

abbrev TTIndex := Σ r : RowIndex, Fin (Module.finrank ℂ (ttSpace r.1.val))

def eigenfield (a : TTIndex) : ttField :=
  ⟨blockEmbedding a.1 (ttBasis a.1.1.val a.2),
    row_mem_ttField a.1 (ttBasis a.1.1.val a.2)⟩

def roughEigenvalue (a : TTIndex) : ℝ := ttCurlEigenvalue a.1.1.val a.2 ^ 2 - 3

theorem eigenfield_orthonormal : Orthonormal ℂ eigenfield := by
  have h := OrthogonalFamily.orthonormal_sigma_orthonormal
    (𝕜 := ℂ) (G := fun r : RowIndex => ttSpace r.1.val)
    (V := ttEmbedding) ttEmbedding_orthogonal
    (α := fun r : RowIndex => Fin (Module.finrank ℂ (ttSpace r.1.val)))
    (v_family := fun r : RowIndex => ttBasis r.1.val)
    (fun r => (ttBasis r.1.val).orthonormal)
  rw [orthonormal_iff_ite] at h ⊢
  exact h

def finiteTTCore : Submodule ℂ ttField :=
  Submodule.span ℂ (Set.range eigenfield)

theorem finiteTTCore_orthogonal : finiteTTCoreᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  intro H hH
  have hall (a : TTIndex) : inner ℂ (eigenfield a) H = 0 :=
    (finiteTTCore.mem_orthogonal H).mp hH (eigenfield a)
      (Submodule.subset_span (Set.mem_range_self a))
  have hrow (r : RowIndex) : blockCoordinates (H : TensorL2) r = 0 := by
    let Hr : ttSpace r.1.val :=
      ⟨blockCoordinates (H : TensorL2) r, (mem_ttField _).mp H.property r⟩
    have hz : Hr = 0 := by
      apply (ttBasis r.1.val).repr.injective
      apply (WithLp.equiv 2
        (Fin (Module.finrank ℂ (ttSpace r.1.val)) → ℂ)).injective
      funext j
      change (ttBasis r.1.val).repr Hr j = (ttBasis r.1.val).repr 0 j
      simp only [OrthonormalBasis.repr_apply_apply, inner_zero_right]
      have he := hall (⟨r, j⟩ : TTIndex)
      change inner ℂ (blockEmbedding r (ttBasis r.1.val j)) (H : TensorL2) = 0 at he
      rw [inner_blockEmbedding] at he
      exact he
    exact congrArg (fun K : ttSpace r.1.val => (K : TensorBlock r.1.val)) hz
  change H = 0
  apply Subtype.ext
  change (H : TensorL2) = 0
  apply blockCoordinates.injective
  apply lp.ext
  funext r
  simpa only [map_zero, lp.coeFn_zero, Pi.zero_apply] using hrow r

def ttHilbertBasis : HilbertBasis TTIndex ℂ ttField :=
  HilbertBasis.mkOfOrthogonalEqBot eigenfield_orthonormal finiteTTCore_orthogonal

@[simp] theorem ttHilbertBasis_apply (a : TTIndex) : ttHilbertBasis a = eigenfield a :=
  congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot
    eigenfield_orthonormal finiteTTCore_orthogonal) a

theorem coe_ttHilbertBasis : (ttHilbertBasis : TTIndex → ttField) = eigenfield :=
  funext ttHilbertBasis_apply

theorem roughEigenvalue_ge_six (a : TTIndex) : 6 ≤ roughEigenvalue a :=
  SourceTensorTTBranches.tt_rough_eigenvalue_ge_six a.1.1.property a.2

end GeneratedFoundations.Geometry.SourceTensorTTField

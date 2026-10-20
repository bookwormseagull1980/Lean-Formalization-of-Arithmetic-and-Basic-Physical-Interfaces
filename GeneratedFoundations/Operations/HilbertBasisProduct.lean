module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Complete orthogonal product coordinates

The two factors keep their original Hilbert inner products. The union of
their embedded complete bases is a complete basis for the Hilbert product;
no finite-dimensionality or truncation is required.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Operations.HilbertBasisProduct

variable {ι κ E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

variable (B : HilbertBasis ι ℂ E) (C : HilbertBasis κ ℂ F)

def vector : ι ⊕ κ → WithLp 2 (E × F) :=
  Sum.elim (fun i => WithLp.toLp 2 (B i, 0))
    (fun j => WithLp.toLp 2 (0, C j))

omit [CompleteSpace E] [CompleteSpace F] in
theorem vector_orthonormal : Orthonormal ℂ (vector B C) := by
  classical
  rw [orthonormal_iff_ite]
  intro a b
  cases a <;> cases b <;>
    simp [vector, orthonormal_iff_ite.mp B.orthonormal,
      orthonormal_iff_ite.mp C.orthonormal]

omit [CompleteSpace E] [CompleteSpace F] in
theorem span_orthogonal :
    (Submodule.span ℂ (Set.range (vector B C)))ᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  have hleft (i : ι) : inner ℂ (B i) x.fst = 0 := by
    have h := (Submodule.mem_orthogonal _ x).mp hx (vector B C (.inl i))
      (Submodule.subset_span (Set.mem_range_self (Sum.inl i : ι ⊕ κ)))
    simpa [vector] using h
  have hright (j : κ) : inner ℂ (C j) x.snd = 0 := by
    have h := (Submodule.mem_orthogonal _ x).mp hx (vector B C (.inr j))
      (Submodule.subset_span (Set.mem_range_self (Sum.inr j : ι ⊕ κ)))
    simpa [vector] using h
  have hl : x.fst = 0 := by
    apply B.repr.injective
    apply lp.ext
    funext i
    simp only [HilbertBasis.repr_apply_apply, hleft, inner_zero_right]
  have hr : x.snd = 0 := by
    apply C.repr.injective
    apply lp.ext
    funext j
    simp only [HilbertBasis.repr_apply_apply, hright, inner_zero_right]
  change x = 0
  apply (WithLp.equiv 2 (E × F)).injective
  exact Prod.ext hl hr

def basis : HilbertBasis (ι ⊕ κ) ℂ (WithLp 2 (E × F)) :=
  HilbertBasis.mkOfOrthogonalEqBot (vector_orthonormal B C) (span_orthogonal B C)

@[simp] theorem basis_inl (i : ι) :
    basis B C (.inl i) = WithLp.toLp 2 (B i, 0) :=
  congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot
    (vector_orthonormal B C) (span_orthogonal B C)) (.inl i)

@[simp] theorem basis_inr (j : κ) :
    basis B C (.inr j) = WithLp.toLp 2 (0, C j) :=
  congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot
    (vector_orthonormal B C) (span_orthogonal B C)) (.inr j)

@[simp] theorem coefficient_inl (i : ι) (x : WithLp 2 (E × F)) :
    inner ℂ (basis B C (.inl i)) x = inner ℂ (B i) x.fst := by simp

@[simp] theorem coefficient_inr (j : κ) (x : WithLp 2 (E × F)) :
    inner ℂ (basis B C (.inr j)) x = inner ℂ (C j) x.snd := by simp

end GeneratedFoundations.Operations.HilbertBasisProduct

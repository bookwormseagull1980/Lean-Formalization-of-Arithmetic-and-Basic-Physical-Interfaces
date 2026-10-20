module

public import GeneratedFoundations.Arithmetic.HistoryReversalIsometry

/-!
# Complete source-sector blocks on arithmetic histories

The two sectors are the existing orthogonal subspaces of the complete
history--phase/source carrier. Each diagonal block below is an arbitrary
endomorphism of its whole sector, including cross-history and cross-phase
coefficients. The uniform two-dimensional source responses are a proved
subfamily, not the definition of a general sector block.

This block calculus identifies the existing projections, source grading and
exchange with their complete Hilbert-space formulas. Conjugation by the
source-sector coordinates preserves the actual adjoints and all matrix
coefficients. The multiplicity is the derived arithmetic label count.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryChiralBlocks

open HistoryCliffordAction
open HistoryComplexConnector (Mat2 sectorAction connector positiveInclusion negativeInclusion)

def diagonalBlocks (N : ℕ) (A B : Module.End ℂ (SectorSpace N)) :
    Module.End ℂ (Space N) where
  toFun x := (sectorCoordinates N).symm (WithLp.toLp 2
    (A (WithLp.ofLp (sectorCoordinates N x)).1,
      B (WithLp.ofLp (sectorCoordinates N x)).2))
  map_add' x y := by
    apply (sectorCoordinates N).injective
    simp only [LinearIsometryEquiv.apply_symm_apply, map_add]
    apply WithLp.ofLp_injective 2
    exact Prod.ext (map_add A _ _) (map_add B _ _)
  map_smul' c x := by
    apply (sectorCoordinates N).injective
    simp only [LinearIsometryEquiv.apply_symm_apply, map_smul]
    apply WithLp.ofLp_injective 2
    exact Prod.ext (map_smul A c _) (map_smul B c _)

@[simp] theorem diagonalBlocks_apply (N : ℕ) (A B : Module.End ℂ (SectorSpace N))
    (x : Space N) :
    WithLp.ofLp (sectorCoordinates N (diagonalBlocks N A B x)) =
      (A (WithLp.ofLp (sectorCoordinates N x)).1,
        B (WithLp.ofLp (sectorCoordinates N x)).2) := by
  change WithLp.ofLp ((sectorCoordinates N) ((sectorCoordinates N).symm _)) = _
  rw [LinearIsometryEquiv.apply_symm_apply]

theorem diagonalBlocks_mul (N : ℕ) (A B C D : Module.End ℂ (SectorSpace N)) :
    diagonalBlocks N A B * diagonalBlocks N C D = diagonalBlocks N (A * C) (B * D) := by
  apply LinearMap.ext
  intro x
  apply (sectorCoordinates N).injective
  apply WithLp.ofLp_injective 2
  simp only [Module.End.mul_apply, diagonalBlocks_apply]

@[simp] theorem diagonalBlocks_one (N : ℕ) : diagonalBlocks N 1 1 = 1 := by
  apply LinearMap.ext
  intro x
  apply (sectorCoordinates N).injective
  apply WithLp.ofLp_injective 2
  exact diagonalBlocks_apply N 1 1 x

theorem diagonalBlocks_adjoint (N : ℕ) (A B : Module.End ℂ (SectorSpace N)) :
    (diagonalBlocks N A B).adjoint = diagonalBlocks N A.adjoint B.adjoint := by
  symm
  apply (LinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  rw [← (sectorCoordinates N).inner_map_map,
    ← (sectorCoordinates N).inner_map_map x (diagonalBlocks N A B y)]
  simp only [WithLp.prod_inner_apply, diagonalBlocks_apply, LinearMap.adjoint_inner_left]

theorem source_blocks (N : ℕ) (p : Mat2 × Mat2) :
    action N (HistoryEvenResponse.matrix N p) =
      diagonalBlocks N (sectorAction N p.1) (sectorAction N p.2) := by
  apply LinearMap.ext
  intro x
  apply (sectorCoordinates N).injective
  apply WithLp.ofLp_injective 2
  rw [HistoryEvenResponse.sectorCoordinates_matrix, diagonalBlocks_apply]

theorem leftProjection_eq (N : ℕ) :
    action N (positiveProjection N) = diagonalBlocks N 1 0 := by
  apply LinearMap.ext
  intro x
  apply (sectorCoordinates N).injective
  apply WithLp.ofLp_injective 2
  rw [sectorCoordinates_positiveProjection, diagonalBlocks_apply]
  rfl

theorem rightProjection_eq (N : ℕ) :
    action N (negativeProjection N) = diagonalBlocks N 0 1 := by
  apply LinearMap.ext
  intro x
  apply (sectorCoordinates N).injective
  apply WithLp.ofLp_injective 2
  rw [sectorCoordinates_negativeProjection, diagonalBlocks_apply]
  rfl

theorem projections_orthogonal (N : ℕ) :
    action N (positiveProjection N) * action N (negativeProjection N) = 0 ∧
      action N (negativeProjection N) * action N (positiveProjection N) = 0 := by
  constructor <;> apply LinearMap.ext <;> intro x <;>
    apply (sectorCoordinates N).injective <;> apply WithLp.ofLp_injective 2 <;>
    simp [leftProjection_eq, rightProjection_eq, Module.End.mul_apply]

theorem projection_adjoint (N : ℕ) :
    (action N (positiveProjection N)).adjoint = action N (positiveProjection N) ∧
    (action N (negativeProjection N)).adjoint = action N (negativeProjection N) := by
  simp [leftProjection_eq, rightProjection_eq, diagonalBlocks_adjoint]

theorem exchange_apply (N : ℕ) (x : Space N) :
    WithLp.ofLp (sectorCoordinates N (action N (exchange N) x)) =
      ((WithLp.ofLp (sectorCoordinates N x)).2, (WithLp.ofLp (sectorCoordinates N x)).1) := by
  rw [HistoryComplexConnector.exchange_eq_connector_one,
    HistoryComplexConnector.sectorCoordinates_connector]
  have he : sectorAction N 1 = 1 := by
    apply LinearMap.ext
    intro y
    ext ⟨h, i⟩
    simp [HistoryComplexConnector.sectorAction_apply, Matrix.one_apply]
  simp [he]

theorem exchange_diagonalBlocks (N : ℕ) (A B : Module.End ℂ (SectorSpace N)) :
    action N (exchange N) * diagonalBlocks N A B =
      diagonalBlocks N B A * action N (exchange N) := by
  apply LinearMap.ext
  intro x
  apply (sectorCoordinates N).injective
  apply WithLp.ofLp_injective 2
  simp only [Module.End.mul_apply, exchange_apply, diagonalBlocks_apply]

theorem grading_eq (N : ℕ) : action N (sourceGrading N) = diagonalBlocks N 1 (-1) := by
  apply LinearMap.ext
  intro x
  apply (sectorCoordinates N).injective
  apply WithLp.ofLp_injective 2
  rw [diagonalBlocks_apply]
  apply Prod.ext <;> ext ⟨h, i⟩
  · change action N (sourceGrading N) x (h, Sum.inl i) = x (h, Sum.inl i)
    simp [action_apply, sourceGrading, Operations.SourceCliffordConnector.grading,
      Fintype.sum_prod_type, Fintype.sum_sum_type, Matrix.one_apply]
  · change action N (sourceGrading N) x (h, Sum.inr i) = -x (h, Sum.inr i)
    simp [action_apply, sourceGrading, Operations.SourceCliffordConnector.grading,
      Fintype.sum_prod_type, Fintype.sum_sum_type, Matrix.one_apply]

theorem grading_eq_projections (N : ℕ) :
    action N (sourceGrading N) = action N (positiveProjection N) - action N (negativeProjection N) := by
  apply LinearMap.ext
  intro x
  apply (sectorCoordinates N).injective
  apply WithLp.ofLp_injective 2
  simp [grading_eq, leftProjection_eq, rightProjection_eq, diagonalBlocks_apply]

theorem grading_left (N : ℕ) (x : SectorSpace N) :
    action N (sourceGrading N) (positiveInclusion N x) = positiveInclusion N x := by
  apply PiLp.ext
  rintro ⟨h, i⟩
  cases i with
  | inl i =>
    simp [action_apply, sourceGrading, Operations.SourceCliffordConnector.grading,
      Fintype.sum_prod_type, Fintype.sum_sum_type, Matrix.one_apply]
  | inr i =>
    simp [action_apply, sourceGrading, Operations.SourceCliffordConnector.grading,
      Fintype.sum_prod_type, Fintype.sum_sum_type, Matrix.one_apply]

theorem grading_right (N : ℕ) (x : SectorSpace N) :
    action N (sourceGrading N) (negativeInclusion N x) = -negativeInclusion N x := by
  apply PiLp.ext
  rintro ⟨h, i⟩
  cases i with
  | inl i =>
    simp [action_apply, sourceGrading, Operations.SourceCliffordConnector.grading,
      Fintype.sum_prod_type, Fintype.sum_sum_type, Matrix.one_apply]
  | inr i =>
    simp [action_apply, sourceGrading, Operations.SourceCliffordConnector.grading,
      Fintype.sum_prod_type, Fintype.sum_sum_type, Matrix.one_apply]

theorem right_left_inner (N : ℕ) (x y : SectorSpace N) :
    inner ℂ (negativeInclusion N x) (positiveInclusion N y) = 0 := by
  simp [PiLp.inner_apply, Fintype.sum_prod_type, Fintype.sum_sum_type]

structure Conclusions : Prop where
  general_block_multiplication : ∀ N A B C D,
    diagonalBlocks N A B * diagonalBlocks N C D = diagonalBlocks N (A * C) (B * D)
  general_block_adjoint : ∀ N A B,
    (diagonalBlocks N A B).adjoint = diagonalBlocks N A.adjoint B.adjoint
  actual_even_source : ∀ N p, action N (HistoryEvenResponse.matrix N p) =
    diagonalBlocks N (sectorAction N p.1) (sectorAction N p.2)
  actual_exchange : ∀ N A B, action N (exchange N) * diagonalBlocks N A B =
    diagonalBlocks N B A * action N (exchange N)
  actual_grading : ∀ N, action N (sourceGrading N) =
    action N (positiveProjection N) - action N (negativeProjection N)
  orthogonal_projections : ∀ N,
    action N (positiveProjection N) * action N (negativeProjection N) = 0 ∧
    action N (negativeProjection N) * action N (positiveProjection N) = 0

theorem generated : Conclusions where
  general_block_multiplication := diagonalBlocks_mul
  general_block_adjoint := diagonalBlocks_adjoint
  actual_even_source := source_blocks
  actual_exchange := exchange_diagonalBlocks
  actual_grading := grading_eq_projections
  orthogonal_projections := projections_orthogonal

end GeneratedFoundations.Arithmetic.HistoryChiralBlocks

module

public import GeneratedFoundations.Arithmetic.HistoryChiralBlocks
public import GeneratedFoundations.Geometry.SourceSpinCoordinates

/-!
# Full arithmetic source coordinates and their Hermite image

The source-sector basis is indexed by actual arithmetic histories and phases.
It uses the original two-dimensional source coordinate at every label. The
formulas below retain every pair of labels, so off-diagonal coefficients are
not replaced by a trace or by an occupation average.

Reindexing by the derived finite label count relates these coordinates to the
common Hermite corner. Its range is exactly the span of the displayed states.
No assertion of surjectivity onto the entire infinite Gaussian Hilbert space
is needed or made for this finite carrier.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Kronecker

namespace GeneratedFoundations.Arithmetic.HistoryChiralCoordinates

abbrev SpinLabel := Fin 2
abbrev ChiralLabel := Operations.SourceCliffordConnector.ChiralIndex

open HistoryCliffordAction
open HistoryComplexConnector (sectorAction connector positiveInclusion negativeInclusion)

def sectorBasis (N : ℕ) :
    OrthonormalBasis (HistoryLabel N × Fin 2) ℂ (SectorSpace N) :=
  EuclideanSpace.basisFun _ ℂ

def sourceCoordinates (N : ℕ) :
    SectorSpace N ≃ₗᵢ[ℂ] EuclideanSpace ℂ (HistoryLabel N × Fin 2) := (sectorBasis N).repr

@[simp] theorem sourceCoordinates_apply (N : ℕ) (x : SectorSpace N) :
    sourceCoordinates N x = x := by
  ext i
  simp [sourceCoordinates, sectorBasis]

def commonSpin (N : ℕ) (M : HistoryComplexConnector.Mat2) : Module.End ℂ (Space N) :=
  action N (HistoryEvenResponse.matrix N (M, M))

theorem commonSpin_blocks (N : ℕ) (M : HistoryComplexConnector.Mat2) :
    commonSpin N M = HistoryChiralBlocks.diagonalBlocks N (sectorAction N M)
      (sectorAction N M) := HistoryChiralBlocks.source_blocks N (M, M)

def sectorMatrixCoordinates (N : ℕ) : Module.End ℂ (SectorSpace N) ≃⋆ₐ[ℂ]
    Matrix (HistoryLabel N × Fin 2) (HistoryLabel N × Fin 2) ℂ :=
  LinearMap.toMatrixOrthonormal (sectorBasis N)

theorem sectorMatrixCoordinates_apply (N : ℕ) (A : Module.End ℂ (SectorSpace N))
    (i j : HistoryLabel N × Fin 2) :
    sectorMatrixCoordinates N A i j = inner ℂ (sectorBasis N i) (A (sectorBasis N j)) :=
  LinearMap.toMatrixOrthonormal_apply_apply (sectorBasis N) A i j

theorem sectorMatrixCoordinates_adjoint (N : ℕ) (A : Module.End ℂ (SectorSpace N)) :
    sectorMatrixCoordinates N A.adjoint = (sectorMatrixCoordinates N A).conjTranspose := by
  exact map_star (sectorMatrixCoordinates N) A

theorem sectorBasis_spin_entry (N : ℕ) (M : HistoryComplexConnector.Mat2)
    (h k : HistoryLabel N) (i j : Fin 2) :
    inner ℂ (sectorBasis N (h, i)) (sectorAction N M (sectorBasis N (k, j))) =
      (if h = k then 1 else 0) * M i j := by
  fin_cases j <;> by_cases hh : h = k <;>
  simp [sectorBasis, EuclideanSpace.basisFun_apply,
    EuclideanSpace.inner_single_left, HistoryComplexConnector.sectorAction_apply,
    PiLp.single_apply, hh]

theorem basis_left (N : ℕ) (h : HistoryLabel N) (i : Fin 2) :
    basis N (h, Sum.inl i) = positiveInclusion N (sectorBasis N (h, i)) := by
  ext ⟨k, j⟩
  cases j <;> simp [basis, sectorBasis, EuclideanSpace.basisFun_apply,
    PiLp.single_apply, Prod.mk.injEq]

theorem basis_right (N : ℕ) (h : HistoryLabel N) (i : Fin 2) :
    basis N (h, Sum.inr i) = negativeInclusion N (sectorBasis N (h, i)) := by
  ext ⟨k, j⟩
  cases j <;> simp [basis, sectorBasis, EuclideanSpace.basisFun_apply,
    PiLp.single_apply, Prod.mk.injEq]

theorem basis_action_entry (N : ℕ) (A : Algebra N) (i j : Index N) :
    inner ℂ (basis N i) (action N A (basis N j)) = A i j := by
  simp [basis, EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]

theorem basis_connector_entry (N : ℕ) (M : HistoryComplexConnector.Mat2)
    (h k : HistoryLabel N) (i j : Operations.SourceCliffordConnector.ChiralIndex) :
    inner ℂ (basis N (h, i)) (action N (connector N M) (basis N (k, j))) =
      (if h = k then 1 else 0) *
        (Matrix.fromBlocks 0 M M.conjTranspose 0) i j := by
  rw [basis_action_entry]
  rfl

theorem basis_grading_entry (N : ℕ) (h k : HistoryLabel N)
    (i j : Operations.SourceCliffordConnector.ChiralIndex) :
    inner ℂ (basis N (h, i)) (action N (sourceGrading N) (basis N (k, j))) =
      (if h = k then 1 else 0) * Operations.SourceCliffordConnector.grading i j := by
  rw [basis_action_entry]
  rfl

def hermiteBasis (N : ℕ) :
    OrthonormalBasis (Operations.SourceCliffordConnector.ColourIndex
      (Fintype.card (HistoryLabel N))) ℂ (Space N) :=
  (basis N).reindex (indexCoordinates N)

theorem hermiteBasis_reindexed (N : ℕ) (i : Index N) :
    hermiteBasis N (indexCoordinates N i) = basis N i := by
  simp [hermiteBasis, OrthonormalBasis.reindex_apply]

theorem hermiteBasis_pair (N : ℕ) (h : Fin (Fintype.card (HistoryLabel N)))
    (i : Operations.SourceCliffordConnector.ChiralIndex) :
    hermiteBasis N (h, i) = basis N ((Fintype.equivFin (HistoryLabel N)).symm h, i) := by
  simp [hermiteBasis, OrthonormalBasis.reindex_apply, indexCoordinates]

def fullMatrixCoordinates (N : ℕ) : Module.End ℂ (Space N) ≃⋆ₐ[ℂ]
    Operations.SourceCliffordConnector.ColourMatrix (Fintype.card (HistoryLabel N)) :=
  LinearMap.toMatrixOrthonormal (hermiteBasis N)

theorem fullMatrixCoordinates_action (N : ℕ) (A : Algebra N) :
    fullMatrixCoordinates N (action N A) = matrixCoordinates N A := by
  ext i j
  rw [show fullMatrixCoordinates N (action N A) i j =
      inner ℂ (hermiteBasis N i) (action N A (hermiteBasis N j)) from
        LinearMap.toMatrixOrthonormal_apply_apply (hermiteBasis N) _ i j]
  simp only [hermiteBasis, OrthonormalBasis.reindex_apply, basis_action_entry]
  rfl

theorem matrixCoordinates_grading (N : ℕ) :
    matrixCoordinates N (sourceGrading N) =
      Operations.SourceCliffordConnector.colourGrading (Fintype.card (HistoryLabel N)) := by
  ext i j
  simp [matrixCoordinates, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
    indexCoordinates, sourceGrading, Operations.SourceCliffordConnector.colourGrading,
    Matrix.one_apply]

theorem hermiteIsometry_range (N : ℕ) :
    LinearMap.range (hermiteIsometry N).toLinearMap =
      Operations.FiniteHermiteCorner.sourceSpace Source.CanonicalRealization.width_pos
        (hermiteMode N) := by
  change LinearMap.range ((basis N).toBasis.constr ℂ _) = _
  exact (basis N).toBasis.constr_range ℂ

theorem hermiteIsometry_left (N : ℕ) (h : HistoryLabel N) (i : Fin 2) :
    hermiteIsometry N (positiveInclusion N (sectorBasis N (h, i))) =
      Operations.HermiteFamily.state Source.CanonicalRealization.width_pos
        (4 * (Fintype.equivFin (HistoryLabel N) h).val + i.val) := by
  rw [← basis_left, hermiteIsometry_basis]
  rfl

theorem hermiteIsometry_right (N : ℕ) (h : HistoryLabel N) (i : Fin 2) :
    hermiteIsometry N (negativeInclusion N (sectorBasis N (h, i))) =
      Operations.HermiteFamily.state Source.CanonicalRealization.width_pos
        (4 * (Fintype.equivFin (HistoryLabel N) h).val + (2 + i.val)) := by
  rw [← basis_right, hermiteIsometry_basis]
  rfl

theorem hermiteIsometry_grading (N : ℕ) (x : Space N) :
    hermiteIsometry N (action N (sourceGrading N) x) =
      Operations.SourceCliffordConnector.sourceGrading Source.CanonicalRealization.width_pos
        (Fintype.card (HistoryLabel N)) (hermiteIsometry N x) := by
  rw [hermiteIsometry_intertwines]
  simp only [fullHermiteOperator, matrixCoordinates_grading]
  rfl

structure Conclusions : Prop where
  all_matrix_entries : ∀ N (A : Algebra N) i j,
    inner ℂ (basis N i) (action N A (basis N j)) = A i j
  complete_matrix_transport : ∀ N (A : Algebra N),
    fullMatrixCoordinates N (action N A) = matrixCoordinates N A
  exact_state_range : ∀ N,
    LinearMap.range (hermiteIsometry N).toLinearMap =
      Operations.FiniteHermiteCorner.sourceSpace Source.CanonicalRealization.width_pos
        (hermiteMode N)
  grading_transport : ∀ N (x : Space N),
    hermiteIsometry N (action N (sourceGrading N) x) =
      Operations.SourceCliffordConnector.sourceGrading Source.CanonicalRealization.width_pos
        (Fintype.card (HistoryLabel N)) (hermiteIsometry N x)

theorem generated : Conclusions where
  all_matrix_entries := basis_action_entry
  complete_matrix_transport := fullMatrixCoordinates_action
  exact_state_range := hermiteIsometry_range
  grading_transport := hermiteIsometry_grading

end GeneratedFoundations.Arithmetic.HistoryChiralCoordinates

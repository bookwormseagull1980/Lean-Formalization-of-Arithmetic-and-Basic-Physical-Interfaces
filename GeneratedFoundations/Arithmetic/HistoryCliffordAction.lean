module

public import GeneratedFoundations.Arithmetic.HistoryCentralSectors
public import GeneratedFoundations.Operations.SourceCliffordSectors
public import GeneratedFoundations.Operations.OrthonormalCoordinates
public import GeneratedFoundations.Source.CanonicalRealization

/-!
# Common-source Clifford operations on actual history--phase observations

The source response has a four-component Clifford coordinate computed in the
common operation algebra. Each actual arithmetic history and finite phase
retains that coordinate. Its repetitions are indexed by the complete generated
arithmetic labels, not by a physical colour multiplicity. Every matrix entry is
represented on the resulting Hilbert space.

Source chirality acts on the source coordinate. Prime occupation parity acts
on the arithmetic coordinate. Their actions commute; an odd source connector
exchanges source chirality and preserves arithmetic occupation parity. Ordered
history reflection remains a third, separately defined operation. These facts
specify which structures are shared and which representations are distinct.

The Hermite realization uses the already generated unit-covariance width and
the actual arithmetic label count. Neither is a new root parameter.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Kronecker Quaternion

namespace GeneratedFoundations.Arithmetic.HistoryCliffordAction

open GeneratedFoundations.Operations

abbrev HistoryLabel (N : ℕ) := HistoryCentralSectors.Label N
abbrev Index (N : ℕ) := HistoryLabel N × SourceCliffordConnector.ChiralIndex
abbrev Algebra (N : ℕ) := Matrix (Index N) (Index N) ℂ
abbrev Space (N : ℕ) := EuclideanSpace ℂ (Index N)

noncomputable instance (N : ℕ) : DecidableEq (Index N) := Classical.decEq _

def historyPoint (N : ℕ) : HistoryLabel N :=
  ⟨⟨0, Nat.zero_lt_succ N⟩, HistoryModuleRepresentation.base 0⟩

/-- The full operation representation retains off-diagonal arithmetic and
    source entries, including operators not preserving either grading. -/
def action (N : ℕ) : Algebra N ≃ₐ[ℂ] Module.End ℂ (Space N) :=
  Matrix.toLinAlgEquiv'.trans
    ((WithLp.linearEquiv 2 ℂ (Index N → ℂ)).symm.conjAlgEquiv ℂ)

@[simp] theorem action_apply (N : ℕ) (A : Algebra N) (x : Space N) (i : Index N) :
    action N A x i = ∑ j, A i j * x j := rfl

theorem action_coefficient (N : ℕ) (A : Algebra N) (i j : Index N) :
    action N A (PiLp.single 2 j 1) i = A i j := by
  simp [PiLp.single_apply]

theorem action_adjoint (N : ℕ) (A : Algebra N) :
    (action N A).adjoint = action N A.conjTranspose := by
  symm
  apply (LinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp only [PiLp.inner_apply, RCLike.inner_apply', action_apply,
    Matrix.conjTranspose_apply, RCLike.star_def, map_sum, map_mul,
    Finset.sum_mul, Finset.mul_sum, starRingEnd_self_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The existing source operation acts uniformly on all retained labels. -/
def sourceMatrix (N : ℕ) (q : ℍ) : Algebra N :=
  (1 : Matrix (HistoryLabel N) (HistoryLabel N) ℂ) ⊗ₖ
    SourceCliffordConnector.clifford q

def sourceGrading (N : ℕ) : Algebra N :=
  (1 : Matrix (HistoryLabel N) (HistoryLabel N) ℂ) ⊗ₖ
    SourceCliffordConnector.grading

def positiveProjection (N : ℕ) : Algebra N :=
  (1 : Matrix (HistoryLabel N) (HistoryLabel N) ℂ) ⊗ₖ
    SourceCliffordSectors.positiveProjection

def negativeProjection (N : ℕ) : Algebra N :=
  (1 : Matrix (HistoryLabel N) (HistoryLabel N) ℂ) ⊗ₖ
    SourceCliffordSectors.negativeProjection

def historyLift (N : ℕ) (A : Matrix (HistoryLabel N) (HistoryLabel N) ℂ) : Algebra N :=
  A ⊗ₖ (1 : SourceCliffordConnector.ChiralMatrix)

theorem sourceMatrix_adjoint (N : ℕ) (q : ℍ) :
    (sourceMatrix N q).conjTranspose = sourceMatrix N q := by
  simp [sourceMatrix, Matrix.conjTranspose_kronecker,
    SourceCliffordConnector.clifford_adjoint]

theorem sourceGrading_adjoint (N : ℕ) :
    (sourceGrading N).conjTranspose = sourceGrading N := by
  simp [sourceGrading, Matrix.conjTranspose_kronecker,
    SourceCliffordConnector.grading_adjoint]

theorem sourceMatrix_square (N : ℕ) (q : ℍ) :
    sourceMatrix N q * sourceMatrix N q = Quaternion.normSq q • (1 : Algebra N) := by
  rw [sourceMatrix, ← Matrix.mul_kronecker_mul, one_mul,
    SourceCliffordConnector.clifford_square,
    Matrix.kronecker_smul, Matrix.one_kronecker_one]
  ext i j
  simp [Matrix.one_apply]

theorem sourceGrading_square (N : ℕ) : sourceGrading N * sourceGrading N = 1 := by
  rw [sourceGrading, ← Matrix.mul_kronecker_mul, one_mul,
    SourceCliffordConnector.grading_square, Matrix.one_kronecker_one]
  ext i j
  simp [Matrix.one_apply]

theorem sourceMatrix_odd (N : ℕ) (q : ℍ) :
    sourceGrading N * sourceMatrix N q + sourceMatrix N q * sourceGrading N = 0 := by
  simp only [sourceGrading, sourceMatrix, ← Matrix.mul_kronecker_mul, one_mul,
    ← Matrix.kronecker_add, SourceCliffordConnector.clifford_odd, Matrix.kronecker_zero]

theorem sourceMatrix_injective (N : ℕ) : Function.Injective (sourceMatrix N) := by
  intro p q hpq
  apply SourceCliffordConnector.clifford_injective
  ext i j
  have h := congrArg (fun A : Algebra N => A (historyPoint N, i) (historyPoint N, j)) hpq
  simpa only [sourceMatrix, Matrix.kronecker_apply, Matrix.one_apply_eq, one_mul] using h

theorem positive_square (N : ℕ) : positiveProjection N * positiveProjection N = positiveProjection N := by
  have h : SourceCliffordSectors.positiveProjection * SourceCliffordSectors.positiveProjection =
      SourceCliffordSectors.positiveProjection :=
    congrArg Subtype.val SourceCliffordSectors.positive_square
  rw [positiveProjection, ← Matrix.mul_kronecker_mul, one_mul, h]

theorem negative_square (N : ℕ) : negativeProjection N * negativeProjection N = negativeProjection N := by
  have h : SourceCliffordSectors.negativeProjection * SourceCliffordSectors.negativeProjection =
      SourceCliffordSectors.negativeProjection :=
    congrArg Subtype.val SourceCliffordSectors.negative_square
  rw [negativeProjection, ← Matrix.mul_kronecker_mul, one_mul, h]

theorem projections_mul (N : ℕ) : positiveProjection N * negativeProjection N = 0 := by
  have h : SourceCliffordSectors.positiveProjection * SourceCliffordSectors.negativeProjection = 0 :=
    congrArg Subtype.val SourceCliffordSectors.positive_mul_negative
  rw [positiveProjection, negativeProjection, ← Matrix.mul_kronecker_mul, one_mul, h,
    Matrix.kronecker_zero]

theorem projections_sum (N : ℕ) : positiveProjection N + negativeProjection N = 1 := by
  have h : SourceCliffordSectors.positiveProjection + SourceCliffordSectors.negativeProjection = 1 :=
    congrArg Subtype.val SourceCliffordSectors.projections_sum
  rw [positiveProjection, negativeProjection, ← Matrix.kronecker_add, h,
    Matrix.one_kronecker_one]
  ext i j
  simp [Matrix.one_apply]

def exchange (N : ℕ) : Algebra N := sourceMatrix N 1

theorem exchange_square (N : ℕ) : exchange N * exchange N = 1 := by
  simpa [exchange] using sourceMatrix_square N 1

theorem exchange_adjoint (N : ℕ) : (exchange N).conjTranspose = exchange N :=
  sourceMatrix_adjoint N 1

theorem exchange_positive (N : ℕ) :
    positiveProjection N * exchange N = exchange N * negativeProjection N := by
  have h : SourceCliffordSectors.positiveProjection * SourceCliffordConnector.clifford 1 =
      SourceCliffordConnector.clifford 1 * SourceCliffordSectors.negativeProjection := by
    simp [SourceCliffordSectors.positiveProjection, SourceCliffordSectors.negativeProjection,
      SourceCliffordSectors.pairMap, SourceCliffordConnector.clifford, Matrix.fromBlocks_multiply]
  simp only [positiveProjection, negativeProjection, exchange, sourceMatrix,
    ← Matrix.mul_kronecker_mul, one_mul, h]

theorem exchange_negative (N : ℕ) :
    negativeProjection N * exchange N = exchange N * positiveProjection N := by
  have h : SourceCliffordSectors.negativeProjection * SourceCliffordConnector.clifford 1 =
      SourceCliffordConnector.clifford 1 * SourceCliffordSectors.positiveProjection := by
    simp [SourceCliffordSectors.positiveProjection, SourceCliffordSectors.negativeProjection,
      SourceCliffordSectors.pairMap, SourceCliffordConnector.clifford, Matrix.fromBlocks_multiply]
  simp only [positiveProjection, negativeProjection, exchange, sourceMatrix,
    ← Matrix.mul_kronecker_mul, one_mul, h]

abbrev SectorSpace (N : ℕ) := EuclideanSpace ℂ (HistoryLabel N × Fin 2)
abbrev TwoSectors (N : ℕ) := WithLp 2 (SectorSpace N × SectorSpace N)

/-- Source-sector coordinates retain every actual history and phase. -/
def sectorCoordinates (N : ℕ) : Space N ≃ₗᵢ[ℂ] TwoSectors N :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (Equiv.prodSumDistrib (HistoryLabel N) (Fin 2) (Fin 2))).trans
      (PiLp.sumPiLpEquivProdLpPiLp 2
        (fun _ : (HistoryLabel N × Fin 2) ⊕ (HistoryLabel N × Fin 2) => ℂ))

@[simp] theorem sectorCoordinates_positive (N : ℕ) (x : Space N) (i : HistoryLabel N × Fin 2) :
    (WithLp.ofLp (sectorCoordinates N x)).1 i = x (i.1, Sum.inl i.2) := rfl

@[simp] theorem sectorCoordinates_negative (N : ℕ) (x : Space N) (i : HistoryLabel N × Fin 2) :
    (WithLp.ofLp (sectorCoordinates N x)).2 i = x (i.1, Sum.inr i.2) := rfl

theorem sector_dimension (N : ℕ) :
    Module.finrank ℂ (SectorSpace N) = 2 * Fintype.card (HistoryLabel N) := by
  simp [SectorSpace, finrank_euclideanSpace, Nat.mul_comm]

@[simp] theorem positive_left (N : ℕ) (x : Space N) (h : HistoryLabel N) (i : Fin 2) :
    action N (positiveProjection N) x (h, Sum.inl i) = x (h, Sum.inl i) := by
  simp [action_apply, positiveProjection, SourceCliffordSectors.positiveProjection,
    SourceCliffordSectors.pairMap, Fintype.sum_prod_type, Fintype.sum_sum_type,
    Matrix.one_apply]

@[simp] theorem positive_right (N : ℕ) (x : Space N) (h : HistoryLabel N) (i : Fin 2) :
    action N (positiveProjection N) x (h, Sum.inr i) = 0 := by
  simp [action_apply, positiveProjection, SourceCliffordSectors.positiveProjection,
    SourceCliffordSectors.pairMap, Fintype.sum_prod_type, Fintype.sum_sum_type]

@[simp] theorem negative_left (N : ℕ) (x : Space N) (h : HistoryLabel N) (i : Fin 2) :
    action N (negativeProjection N) x (h, Sum.inl i) = 0 := by
  simp [action_apply, negativeProjection, SourceCliffordSectors.negativeProjection,
    SourceCliffordSectors.pairMap, Fintype.sum_prod_type, Fintype.sum_sum_type]

@[simp] theorem negative_right (N : ℕ) (x : Space N) (h : HistoryLabel N) (i : Fin 2) :
    action N (negativeProjection N) x (h, Sum.inr i) = x (h, Sum.inr i) := by
  simp [action_apply, negativeProjection, SourceCliffordSectors.negativeProjection,
    SourceCliffordSectors.pairMap, Fintype.sum_prod_type, Fintype.sum_sum_type,
    Matrix.one_apply]

theorem sectorCoordinates_positiveProjection (N : ℕ) (x : Space N) :
    WithLp.ofLp (sectorCoordinates N (action N (positiveProjection N) x)) =
      ((WithLp.ofLp (sectorCoordinates N x)).1, 0) := by
  apply Prod.ext <;> ext i
  · change action N (positiveProjection N) x (i.1, Sum.inl i.2) = x (i.1, Sum.inl i.2)
    exact positive_left N x i.1 i.2
  · change action N (positiveProjection N) x (i.1, Sum.inr i.2) = 0
    exact positive_right N x i.1 i.2

theorem sectorCoordinates_negativeProjection (N : ℕ) (x : Space N) :
    WithLp.ofLp (sectorCoordinates N (action N (negativeProjection N) x)) =
      (0, (WithLp.ofLp (sectorCoordinates N x)).2) := by
  apply Prod.ext <;> ext i
  · change action N (negativeProjection N) x (i.1, Sum.inl i.2) = 0
    exact negative_left N x i.1 i.2
  · change action N (negativeProjection N) x (i.1, Sum.inr i.2) = x (i.1, Sum.inr i.2)
    exact negative_right N x i.1 i.2

/-- This commutation holds for every arithmetic matrix, including cross-root
    entries; it does not assert that arithmetic parity commutes with them. -/
theorem sourceMatrix_historyLift (N : ℕ) (q : ℍ)
    (A : Matrix (HistoryLabel N) (HistoryLabel N) ℂ) :
    sourceMatrix N q * historyLift N A = historyLift N A * sourceMatrix N q := by
  simp [sourceMatrix, historyLift, ← Matrix.mul_kronecker_mul]

def occupationGrading (N : ℕ) : Algebra N :=
  historyLift N (Matrix.diagonal fun i => HistoryCentralSectors.sign i.1.val)

def gaussian (N : ℕ) (t : ℝ) : Algebra N :=
  historyLift N (Matrix.diagonal fun i =>
    (Real.exp (-t * ((i.1.val + 1 : ℕ) : ℝ) ^ 2) : ℂ))

theorem sourceMatrix_occupation (N : ℕ) (q : ℍ) :
    sourceMatrix N q * occupationGrading N = occupationGrading N * sourceMatrix N q :=
  sourceMatrix_historyLift N q _

theorem sourceMatrix_gaussian (N : ℕ) (q : ℍ) (t : ℝ) :
    sourceMatrix N q * gaussian N t = gaussian N t * sourceMatrix N q :=
  sourceMatrix_historyLift N q _

theorem space_finrank (N : ℕ) :
    Module.finrank ℂ (Space N) = 4 * Fintype.card (HistoryLabel N) := by
  rw [finrank_euclideanSpace]
  simp [Index, SourceCliffordConnector.ChiralIndex, Nat.mul_comm]

def indexCoordinates (N : ℕ) :
    Index N ≃ SourceCliffordConnector.ColourIndex (Fintype.card (HistoryLabel N)) :=
  Equiv.prodCongr (Fintype.equivFin (HistoryLabel N)) (Equiv.refl _)

def matrixCoordinates (N : ℕ) : Algebra N ≃ₐ[ℂ]
    SourceCliffordConnector.ColourMatrix (Fintype.card (HistoryLabel N)) :=
  Matrix.reindexAlgEquiv ℂ ℂ (indexCoordinates N)

theorem matrixCoordinates_sourceMatrix (N : ℕ) (q : ℍ) :
    matrixCoordinates N (sourceMatrix N q) =
      SourceCliffordConnector.colourClifford (Fintype.card (HistoryLabel N)) q := by
  ext i j
  simp [matrixCoordinates, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
    indexCoordinates, sourceMatrix, SourceCliffordConnector.colourClifford,
    Matrix.one_apply]

theorem matrixCoordinates_adjoint (N : ℕ) (A : Algebra N) :
    matrixCoordinates N A.conjTranspose = (matrixCoordinates N A).conjTranspose := by
  ext i j
  rfl

/-- All arithmetic/source matrix entries, not just Clifford generators,
    are realized faithfully on the actual Gaussian Hilbert space. -/
def fullHermiteOperator (N : ℕ) (A : Algebra N) :=
  FiniteHermiteCorner.corner Source.CanonicalRealization.width_pos
    SourceCliffordConnector.sourceMode (matrixCoordinates N A)

theorem fullHermiteOperator_injective (N : ℕ) : Function.Injective (fullHermiteOperator N) :=
  (FiniteHermiteCorner.corner_injective Source.CanonicalRealization.width_pos _
    (SourceCliffordConnector.sourceMode_injective _)).comp (matrixCoordinates N).injective

theorem fullHermiteOperator_mul (N : ℕ) (A B : Algebra N) :
    fullHermiteOperator N (A * B) = fullHermiteOperator N A * fullHermiteOperator N B := by
  rw [fullHermiteOperator, map_mul, FiniteHermiteCorner.corner_mul _ _
    (SourceCliffordConnector.sourceMode_injective _)]
  rfl

theorem fullHermiteOperator_adjoint (N : ℕ) (A : Algebra N) :
    fullHermiteOperator N A.conjTranspose = (fullHermiteOperator N A).adjoint := by
  simp only [fullHermiteOperator, matrixCoordinates_adjoint, FiniteHermiteCorner.corner_adjoint]

theorem fullHermiteOperator_entries (N : ℕ) (A : Algebra N) :
    (matrixCoordinates N).symm
      (FiniteHermiteCorner.entries Source.CanonicalRealization.width_pos
        SourceCliffordConnector.sourceMode (fullHermiteOperator N A)) = A := by
  rw [fullHermiteOperator, FiniteHermiteCorner.entries_corner _ _
    (SourceCliffordConnector.sourceMode_injective _), AlgEquiv.symm_apply_apply]

def hermiteMode (N : ℕ) (i : Index N) : ℕ :=
  SourceCliffordConnector.sourceMode (indexCoordinates N i)

theorem hermiteMode_injective (N : ℕ) : Function.Injective (hermiteMode N) :=
  (SourceCliffordConnector.sourceMode_injective _).comp (indexCoordinates N).injective

def basis (N : ℕ) : OrthonormalBasis (Index N) ℂ (Space N) :=
  EuclideanSpace.basisFun (Index N) ℂ

def hermiteLinear (N : ℕ) : Space N →ₗ[ℂ] Correlation.ComplexGaussianStates.ComplexL2 :=
  (basis N).toBasis.constr ℂ fun i =>
    HermiteFamily.state Source.CanonicalRealization.width_pos (hermiteMode N i)

@[simp] theorem hermiteLinear_basis (N : ℕ) (i : Index N) :
    hermiteLinear N (basis N i) =
      HermiteFamily.state Source.CanonicalRealization.width_pos (hermiteMode N i) :=
  OrthonormalCoordinates.orthonormal_constr_basis (basis N) _ i

theorem hermiteLinear_orthonormal (N : ℕ) :
    Orthonormal ℂ (hermiteLinear N ∘ basis N) := by
  have h := (HermiteFamily.state_orthonormal Source.CanonicalRealization.width_pos).comp
    (hermiteMode N) (hermiteMode_injective N)
  simpa only [Function.comp_def, hermiteLinear_basis] using h

/-- An actual isometry of states, in addition to the faithful operator map. -/
def hermiteIsometry (N : ℕ) :
    Space N →ₗᵢ[ℂ] Correlation.ComplexGaussianStates.ComplexL2 :=
  OrthonormalCoordinates.orthonormalLinearIsometry (basis N) (hermiteLinear N)
    (hermiteLinear_orthonormal N)

@[simp] theorem hermiteIsometry_basis (N : ℕ) (i : Index N) :
    hermiteIsometry N (basis N i) =
      HermiteFamily.state Source.CanonicalRealization.width_pos (hermiteMode N i) :=
  hermiteLinear_basis N i

theorem hermiteIsometry_intertwines_basis (N : ℕ) (A : Algebra N) (j : Index N) :
    hermiteIsometry N (action N A (basis N j)) =
      fullHermiteOperator N A (hermiteIsometry N (basis N j)) := by
  have hx := (basis N).sum_repr (action N A (basis N j))
  conv_lhs => rw [← hx]
  simp only [map_sum, map_smul, hermiteIsometry_basis]
  simp only [hermiteMode]
  rw [fullHermiteOperator, FiniteHermiteCorner.corner_state _ _
    (SourceCliffordConnector.sourceMode_injective _)]
  apply Fintype.sum_equiv (indexCoordinates N)
  intro i
  congr 1
  change action N A (basis N j) i = matrixCoordinates N A (indexCoordinates N i) (indexCoordinates N j)
  simp [basis, EuclideanSpace.basisFun_apply,
    matrixCoordinates, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply]

theorem hermiteIsometry_intertwines (N : ℕ) (A : Algebra N) (x : Space N) :
    hermiteIsometry N (action N A x) = fullHermiteOperator N A (hermiteIsometry N x) := by
  have hmap : (hermiteIsometry N).toLinearMap.comp (action N A) =
      (fullHermiteOperator N A).toLinearMap.comp (hermiteIsometry N).toLinearMap :=
    OrthonormalCoordinates.orthonormalBasis_linearMap_ext (basis N) _ _
      (hermiteIsometry_intertwines_basis N A)
  exact LinearMap.congr_fun hmap x

/-- The original Gaussian source contains the same response with the
    internally derived number of arithmetic copies. -/
def hermiteOperator (N : ℕ) (q : ℍ) :=
  SourceCliffordConnector.sourceConnector Source.CanonicalRealization.width_pos
    (Fintype.card (HistoryLabel N)) q

theorem fullHermiteOperator_sourceMatrix (N : ℕ) (q : ℍ) :
    fullHermiteOperator N (sourceMatrix N q) = hermiteOperator N q := by
  rw [fullHermiteOperator, matrixCoordinates_sourceMatrix]
  rfl

theorem hermiteIsometry_connector (N : ℕ) (q : ℍ) (x : Space N) :
    hermiteIsometry N (action N (sourceMatrix N q) x) =
      hermiteOperator N q (hermiteIsometry N x) := by
  rw [hermiteIsometry_intertwines, fullHermiteOperator_sourceMatrix]

theorem hermiteOperator_adjoint (N : ℕ) (q : ℍ) :
    (hermiteOperator N q).adjoint = hermiteOperator N q :=
  SourceCliffordConnector.sourceConnector_adjoint _ _ _

theorem hermiteOperator_square (N : ℕ) (q : ℍ) :
    hermiteOperator N q * hermiteOperator N q = Quaternion.normSq q •
      FiniteHermiteCorner.projection Source.CanonicalRealization.width_pos
        (SourceCliffordConnector.sourceMode (d := Fintype.card (HistoryLabel N))) :=
  SourceCliffordConnector.sourceConnector_square _ _ _

theorem hermiteOperator_mem_ladder (N : ℕ) (q : ℍ) :
    hermiteOperator N q ∈
      SourceMatrixUnits.ladderOperationAlgebra Source.CanonicalRealization.width_pos :=
  SourceCliffordConnector.sourceConnector_mem_ladder _ _ _

structure Conclusions : Prop where
  full_coefficients : ∀ N (A : Algebra N) i j,
    action N A (PiLp.single 2 j 1) i = A i j
  adjoint_transport : ∀ N (A : Algebra N), (action N A).adjoint = action N A.conjTranspose
  faithful_source : ∀ N, Function.Injective (sourceMatrix N)
  actual_dimension : ∀ N, Module.finrank ℂ (Space N) = 4 * Fintype.card (HistoryLabel N)
  source_square : ∀ N q, sourceMatrix N q * sourceMatrix N q = Quaternion.normSq q • 1
  source_odd : ∀ N q,
    sourceGrading N * sourceMatrix N q + sourceMatrix N q * sourceGrading N = 0
  complete_source_sectors : ∀ N, positiveProjection N + negativeProjection N = 1
  independent_occupation : ∀ N q,
    sourceMatrix N q * occupationGrading N = occupationGrading N * sourceMatrix N q
  gaussian_compatibility : ∀ N q t,
    sourceMatrix N q * gaussian N t = gaussian N t * sourceMatrix N q
  original_source : ∀ N q, hermiteOperator N q ∈
    SourceMatrixUnits.ladderOperationAlgebra Source.CanonicalRealization.width_pos
  original_source_transport : ∀ N q,
    fullHermiteOperator N (sourceMatrix N q) = hermiteOperator N q
  original_source_faithfulness : ∀ N, Function.Injective (fullHermiteOperator N)
  original_state_transport : ∀ N q (x : Space N),
    hermiteIsometry N (action N (sourceMatrix N q) x) =
      hermiteOperator N q (hermiteIsometry N x)

theorem generated : Conclusions where
  full_coefficients := action_coefficient
  adjoint_transport := action_adjoint
  faithful_source := sourceMatrix_injective
  actual_dimension := space_finrank
  source_square := sourceMatrix_square
  source_odd := sourceMatrix_odd
  complete_source_sectors := projections_sum
  independent_occupation := sourceMatrix_occupation
  gaussian_compatibility := sourceMatrix_gaussian
  original_source := hermiteOperator_mem_ladder
  original_source_transport := fullHermiteOperator_sourceMatrix
  original_source_faithfulness := fullHermiteOperator_injective
  original_state_transport := hermiteIsometry_connector

end GeneratedFoundations.Arithmetic.HistoryCliffordAction

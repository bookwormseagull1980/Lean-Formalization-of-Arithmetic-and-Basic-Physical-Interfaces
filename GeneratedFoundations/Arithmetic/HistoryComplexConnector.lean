module

public import GeneratedFoundations.Arithmetic.HistoryCliffordAction
public import GeneratedFoundations.Operations.SourceCliffordComplex

/-!
# Full complex source responses on arithmetic history--phase fibres

The common source real form generates all complex two-by-two responses.
These responses act on every actual history--phase label. The carrier and
its dimension remain those already constructed in `HistoryCliffordAction`.
No matter multiplicity or numerical physical parameter is transferred.

An arbitrary complex response is paired with its adjoint. Its complete odd
operator is transported to the original Gaussian/Hermite space by the
already constructed state isometry, including every matrix coefficient.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Kronecker Quaternion

namespace GeneratedFoundations.Arithmetic.HistoryComplexConnector

open GeneratedFoundations.Operations
open HistoryCliffordAction

abbrev Mat2 := SourceSpinCorner.Mat2

/-- Uniform source response on the actual arithmetic multiplicity. -/
def connector (N : ℕ) (M : Mat2) : Algebra N :=
  (1 : Matrix (HistoryLabel N) (HistoryLabel N) ℂ) ⊗ₖ
    SourceCliffordComplex.connector M

theorem connector_adjoint (N : ℕ) (M : Mat2) :
    (connector N M).conjTranspose = connector N M := by
  simp [connector, Matrix.conjTranspose_kronecker,
    SourceCliffordComplex.connector_adjoint]

theorem connector_injective (N : ℕ) : Function.Injective (connector N) := by
  intro M M' h
  apply SourceCliffordComplex.connector_injective
  ext i j
  have hc := congrArg (fun A : Algebra N =>
    A (historyPoint N, i) (historyPoint N, j)) h
  simpa only [connector, Matrix.kronecker_apply, Matrix.one_apply_eq, one_mul] using hc

theorem action_adjoint_connector (N : ℕ) (M : Mat2) :
    (action N (connector N M)).adjoint = action N (connector N M) := by
  rw [action_adjoint, connector_adjoint]

theorem connector_odd (N : ℕ) (M : Mat2) :
    sourceGrading N * connector N M + connector N M * sourceGrading N = 0 := by
  simp only [sourceGrading, connector, ← Matrix.mul_kronecker_mul, one_mul,
    ← Matrix.kronecker_add, SourceCliffordComplex.connector_odd, Matrix.kronecker_zero]

theorem connector_square (N : ℕ) (M : Mat2) :
    connector N M * connector N M =
      (1 : Matrix (HistoryLabel N) (HistoryLabel N) ℂ) ⊗ₖ
        Matrix.fromBlocks (M * M.conjTranspose) 0 0 (M.conjTranspose * M) := by
  rw [connector, ← Matrix.mul_kronecker_mul, one_mul,
    SourceCliffordComplex.connector_square]

theorem connector_square_of_unitary (N : ℕ) (M : Mat2)
    (hl : M * M.conjTranspose = 1) (hr : M.conjTranspose * M = 1) :
    connector N M * connector N M = 1 := by
  rw [connector, ← Matrix.mul_kronecker_mul, one_mul,
    SourceCliffordComplex.connector_square_of_unitary M hl hr, Matrix.one_kronecker_one]
  ext i j
  simp [Matrix.one_apply]

theorem action_connector_square (N : ℕ) (M : Mat2) :
    action N (connector N M) * action N (connector N M) =
      action N ((1 : Matrix (HistoryLabel N) (HistoryLabel N) ℂ) ⊗ₖ
        Matrix.fromBlocks (M * M.conjTranspose) 0 0 (M.conjTranspose * M)) := by
  rw [← map_mul, connector_square]

theorem connector_quaternion (N : ℕ) (q : ℍ) :
    connector N (Geometry.SourceQuaternionAmplitude.matrixMap q) = sourceMatrix N q := by
  rw [connector, SourceCliffordComplex.connector_matrixMap]
  rfl

theorem connector_positive (N : ℕ) (M : Mat2) :
    positiveProjection N * connector N M = connector N M * negativeProjection N := by
  simp only [positiveProjection, negativeProjection, connector,
    ← Matrix.mul_kronecker_mul, one_mul, SourceCliffordComplex.connector_positive]

theorem connector_negative (N : ℕ) (M : Mat2) :
    negativeProjection N * connector N M = connector N M * positiveProjection N := by
  simp only [positiveProjection, negativeProjection, connector,
    ← Matrix.mul_kronecker_mul, one_mul, SourceCliffordComplex.connector_negative]

theorem exchange_eq_connector_one (N : ℕ) : exchange N = connector N 1 := by
  rw [exchange, ← connector_quaternion]
  simp

@[simp] theorem connector_left (N : ℕ) (M : Mat2) (x : Space N)
    (h : HistoryLabel N) (i : Fin 2) :
    action N (connector N M) x (h, Sum.inl i) =
      ∑ j, M i j * x (h, Sum.inr j) := by
  simp [action_apply, connector, SourceCliffordComplex.connector,
    Fintype.sum_prod_type, Fintype.sum_sum_type, Matrix.one_apply]

@[simp] theorem connector_right (N : ℕ) (M : Mat2) (x : Space N)
    (h : HistoryLabel N) (i : Fin 2) :
    action N (connector N M) x (h, Sum.inr i) =
      ∑ j, M.conjTranspose i j * x (h, Sum.inl j) := by
  simp [action_apply, connector, SourceCliffordComplex.connector,
    Fintype.sum_prod_type, Fintype.sum_sum_type, Matrix.one_apply]

/-- The two embeddings retain the complete arithmetic label; neither is an
    occupation-parity projection. -/
def positiveInclusion (N : ℕ) : SectorSpace N →ₗ[ℂ] Space N where
  toFun x := WithLp.toLp 2 fun
    | (h, Sum.inl i) => x (h, i)
    | (_, Sum.inr _) => 0
  map_add' x y := by ext ⟨h, i⟩; cases i <;> simp
  map_smul' r x := by ext ⟨h, i⟩; cases i <;> simp

def negativeInclusion (N : ℕ) : SectorSpace N →ₗ[ℂ] Space N where
  toFun x := WithLp.toLp 2 fun
    | (_, Sum.inl _) => 0
    | (h, Sum.inr i) => x (h, i)
  map_add' x y := by ext ⟨h, i⟩; cases i <;> simp
  map_smul' r x := by ext ⟨h, i⟩; cases i <;> simp

@[simp] theorem positiveInclusion_left (N : ℕ) (x : SectorSpace N)
    (h : HistoryLabel N) (i : Fin 2) :
    positiveInclusion N x (h, Sum.inl i) = x (h, i) := rfl

@[simp] theorem positiveInclusion_right (N : ℕ) (x : SectorSpace N)
    (h : HistoryLabel N) (i : Fin 2) :
    positiveInclusion N x (h, Sum.inr i) = 0 := rfl

@[simp] theorem negativeInclusion_left (N : ℕ) (x : SectorSpace N)
    (h : HistoryLabel N) (i : Fin 2) :
    negativeInclusion N x (h, Sum.inl i) = 0 := rfl

@[simp] theorem negativeInclusion_right (N : ℕ) (x : SectorSpace N)
    (h : HistoryLabel N) (i : Fin 2) :
    negativeInclusion N x (h, Sum.inr i) = x (h, i) := rfl

theorem inclusions_orthogonal (N : ℕ) (x y : SectorSpace N) :
    inner ℂ (positiveInclusion N x) (negativeInclusion N y) = 0 := by
  simp [PiLp.inner_apply, Fintype.sum_prod_type, Fintype.sum_sum_type]

theorem positiveInclusion_inner (N : ℕ) (x y : SectorSpace N) :
    inner ℂ (positiveInclusion N x) (positiveInclusion N y) = inner ℂ x y := by
  simp [PiLp.inner_apply, Fintype.sum_prod_type, Fintype.sum_sum_type]

theorem negativeInclusion_inner (N : ℕ) (x y : SectorSpace N) :
    inner ℂ (negativeInclusion N x) (negativeInclusion N y) = inner ℂ x y := by
  simp [PiLp.inner_apply, Fintype.sum_prod_type, Fintype.sum_sum_type]

theorem inclusions_reconstruct (N : ℕ) (x : Space N) :
    positiveInclusion N (WithLp.ofLp (sectorCoordinates N x)).1 +
      negativeInclusion N (WithLp.ofLp (sectorCoordinates N x)).2 = x := by
  ext ⟨h, i⟩
  cases i with
  | inl i => change x (h, Sum.inl i) + 0 = _; exact add_zero _
  | inr i => change 0 + x (h, Sum.inr i) = _; exact zero_add _

/-- The response on a single source sector, uniform on every retained
    arithmetic history and phase. -/
def sectorAction (N : ℕ) (M : Mat2) : Module.End ℂ (SectorSpace N) where
  toFun x := WithLp.toLp 2 fun i => ∑ j, M i.2 j * x (i.1, j)
  map_add' x y := by ext i; simp [mul_add, Finset.sum_add_distrib]
  map_smul' r x := by ext i; simp [mul_left_comm, mul_add]

@[simp] theorem sectorAction_apply (N : ℕ) (M : Mat2) (x : SectorSpace N)
    (h : HistoryLabel N) (i : Fin 2) :
    sectorAction N M x (h, i) = ∑ j, M i j * x (h, j) := rfl

theorem sectorAction_adjoint (N : ℕ) (M : Mat2) :
    (sectorAction N M).adjoint = sectorAction N M.conjTranspose := by
  symm
  apply (LinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp only [PiLp.inner_apply, RCLike.inner_apply', Fintype.sum_prod_type, sectorAction_apply,
    Matrix.conjTranspose_apply, RCLike.star_def, map_sum, map_mul,
    Finset.sum_mul, Finset.mul_sum, starRingEnd_self_apply]
  apply Finset.sum_congr rfl
  intro h _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Exact inclusion formulas, rather than just a row-wise block analogy. -/
theorem connector_on_positive (N : ℕ) (M : Mat2) (x : SectorSpace N) :
    action N (connector N M) (positiveInclusion N x) =
      negativeInclusion N (sectorAction N M.conjTranspose x) := by
  ext ⟨h, i⟩
  cases i with
  | inl i => rw [connector_left]; simp only [positiveInclusion_right, mul_zero,
      Finset.sum_const_zero, negativeInclusion_left]
  | inr i => rw [connector_right]; rfl

theorem connector_on_negative (N : ℕ) (M : Mat2) (x : SectorSpace N) :
    action N (connector N M) (negativeInclusion N x) =
      positiveInclusion N (sectorAction N M x) := by
  ext ⟨h, i⟩
  cases i with
  | inl i => rw [connector_left]; rfl
  | inr i => rw [connector_right]; simp only [negativeInclusion_left, mul_zero,
      Finset.sum_const_zero, positiveInclusion_right]

theorem sectorCoordinates_connector (N : ℕ) (M : Mat2) (x : Space N) :
    WithLp.ofLp (sectorCoordinates N (action N (connector N M) x)) =
      (sectorAction N M (WithLp.ofLp (sectorCoordinates N x)).2,
        sectorAction N M.conjTranspose (WithLp.ofLp (sectorCoordinates N x)).1) := by
  apply Prod.ext <;> ext ⟨h, i⟩
  · change action N (connector N M) x (h, Sum.inl i) =
      ∑ j, M i j * x (h, Sum.inr j)
    exact connector_left N M x h i
  · change action N (connector N M) x (h, Sum.inr i) =
      ∑ j, M.conjTranspose i j * x (h, Sum.inl j)
    exact connector_right N M x h i

theorem connector_isSelfAdjoint (N : ℕ) (M : Mat2) :
    IsSelfAdjoint (action N (connector N M)) :=
  LinearMap.isSelfAdjoint_iff'.mpr (action_adjoint_connector N M)

/-- The same factorization holds for arbitrary arithmetic operators, not just
    the diagonal Gaussian or the occupation character. -/
theorem connector_historyLift (N : ℕ) (M : Mat2)
    (A : Matrix (HistoryLabel N) (HistoryLabel N) ℂ) :
    connector N M * historyLift N A = historyLift N A * connector N M := by
  simp [connector, historyLift, ← Matrix.mul_kronecker_mul]

theorem connector_gaussian (N : ℕ) (M : Mat2) (t : ℝ) :
    connector N M * gaussian N t = gaussian N t * connector N M :=
  connector_historyLift N M _

theorem connector_occupation (N : ℕ) (M : Mat2) :
    connector N M * occupationGrading N = occupationGrading N * connector N M :=
  connector_historyLift N M _

/-- The actual old quaternion source is the unique real-form slice of this
    complete complex response family. -/
theorem connector_real_decomposition (M : Mat2) :
    M = Geometry.SourceQuaternionAmplitude.matrixMap (SourceComplexAmplitude.realPart M) +
      Complex.I • Geometry.SourceQuaternionAmplitude.matrixMap
        (SourceComplexAmplitude.imagPart M) ∧
    ∀ p q : ℍ, M = Geometry.SourceQuaternionAmplitude.matrixMap p +
      Complex.I • Geometry.SourceQuaternionAmplitude.matrixMap q →
      p = SourceComplexAmplitude.realPart M ∧ q = SourceComplexAmplitude.imagPart M :=
  ⟨SourceComplexAmplitude.matrix_decomposition M,
    SourceComplexAmplitude.decomposition_unique M⟩

/-- Every complex connector is represented in the original Gaussian space. -/
def hermiteConnector (N : ℕ) (M : Mat2) := fullHermiteOperator N (connector N M)

theorem matrixCoordinates_connector (N : ℕ) (M : Mat2) :
    matrixCoordinates N (connector N M) =
      (1 : Matrix (Fin (Fintype.card (HistoryLabel N)))
        (Fin (Fintype.card (HistoryLabel N))) ℂ) ⊗ₖ
          SourceCliffordComplex.connector M := by
  ext i j
  simp [matrixCoordinates, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
    indexCoordinates, connector, Matrix.one_apply]

theorem hermiteConnector_adjoint (N : ℕ) (M : Mat2) :
    (hermiteConnector N M).adjoint = hermiteConnector N M := by
  rw [hermiteConnector, ← fullHermiteOperator_adjoint, connector_adjoint]

theorem hermiteConnector_injective (N : ℕ) : Function.Injective (hermiteConnector N) :=
  (fullHermiteOperator_injective N).comp (connector_injective N)

theorem hermiteConnector_intertwines (N : ℕ) (M : Mat2) (x : Space N) :
    hermiteIsometry N (action N (connector N M) x) =
      hermiteConnector N M (hermiteIsometry N x) :=
  hermiteIsometry_intertwines N _ x

theorem hermiteConnector_quaternion (N : ℕ) (q : ℍ) :
    hermiteConnector N (Geometry.SourceQuaternionAmplitude.matrixMap q) =
      hermiteOperator N q := by
  rw [hermiteConnector, connector_quaternion, fullHermiteOperator_sourceMatrix]

theorem hermiteConnector_mem_ladder (N : ℕ) (M : Mat2) :
    hermiteConnector N M ∈
      SourceMatrixUnits.ladderOperationAlgebra Source.CanonicalRealization.width_pos :=
  FiniteHermiteCorner.corner_mem_ladder _ _ _

structure Conclusions : Prop where
  complete_complex_response : ∀ N, Function.Injective (connector N)
  self_adjoint : ∀ N M,
    (action N (connector N M)).adjoint = action N (connector N M)
  odd : ∀ N M, sourceGrading N * connector N M + connector N M * sourceGrading N = 0
  quaternion_slice : ∀ N q,
    connector N (Geometry.SourceQuaternionAmplitude.matrixMap q) = sourceMatrix N q
  source_sector_exchange : ∀ N M,
    positiveProjection N * connector N M = connector N M * negativeProjection N
  actual_arithmetic_compatibility : ∀ N M A,
    connector N M * historyLift N A = historyLift N A * connector N M
  faithful_original_response : ∀ N, Function.Injective (hermiteConnector N)
  original_state_transport : ∀ N M (x : Space N),
    hermiteIsometry N (action N (connector N M) x) =
      hermiteConnector N M (hermiteIsometry N x)

theorem generated : Conclusions where
  complete_complex_response := connector_injective
  self_adjoint := action_adjoint_connector
  odd := connector_odd
  quaternion_slice := connector_quaternion
  source_sector_exchange := connector_positive
  actual_arithmetic_compatibility := connector_historyLift
  faithful_original_response := hermiteConnector_injective
  original_state_transport := hermiteConnector_intertwines

end GeneratedFoundations.Arithmetic.HistoryComplexConnector

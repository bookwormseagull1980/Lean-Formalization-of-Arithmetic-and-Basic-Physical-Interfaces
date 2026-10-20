module

public import GeneratedFoundations.Arithmetic.HistoryComplexConnector

/-!
# Independent even responses on the actual arithmetic source sectors

The even algebra is the complex extension of the source-real operation
algebra, proved upstream to be the pair of two-by-two matrix algebras.
Its action here repeats over the actual history--phase labels. Each sector
can respond independently; the off-diagonal connector transforms with both
responses together. All formulas concern the actual operators, including
their faithful return to the original Gaussian space.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Kronecker

namespace GeneratedFoundations.Arithmetic.HistoryEvenResponse

open GeneratedFoundations.Operations
open HistoryCliffordAction
open HistoryComplexConnector (Mat2 connector sectorAction)

/-- The full complex even source response on every retained arithmetic label. -/
def matrix (N : ℕ) (p : Mat2 × Mat2) : Algebra N :=
  (1 : Matrix (HistoryLabel N) (HistoryLabel N) ℂ) ⊗ₖ
    SourceCliffordComplex.complexPairMap p

theorem matrix_mul (N : ℕ) (p q : Mat2 × Mat2) :
    matrix N (p * q) = matrix N p * matrix N q := by
  simp [matrix, ← Matrix.mul_kronecker_mul]

theorem matrix_add (N : ℕ) (p q : Mat2 × Mat2) :
    matrix N (p + q) = matrix N p + matrix N q := by
  simp [matrix, Matrix.kronecker_add]

theorem matrix_one (N : ℕ) : matrix N 1 = 1 := by
  simp only [matrix, map_one, Matrix.one_kronecker_one]
  ext i j
  simp [Matrix.one_apply]

theorem matrix_adjoint (N : ℕ) (p : Mat2 × Mat2) :
    (matrix N p).conjTranspose =
      matrix N (p.1.conjTranspose, p.2.conjTranspose) := by
  simp [matrix, Matrix.conjTranspose_kronecker,
    SourceCliffordComplex.complexPairMap_adjoint]

theorem matrix_injective (N : ℕ) : Function.Injective (matrix N) := by
  intro p q h
  apply SourceCliffordComplex.complexPairMap_injective
  ext i j
  have hc := congrArg (fun A : Algebra N =>
    A (historyPoint N, i) (historyPoint N, j)) h
  simpa only [matrix, Matrix.kronecker_apply, Matrix.one_apply_eq, one_mul] using hc

theorem matrix_central (N : ℕ) (p : Mat2 × Mat2) :
    sourceGrading N * matrix N p = matrix N p * sourceGrading N := by
  simp [sourceGrading, matrix, ← Matrix.mul_kronecker_mul,
    SourceCliffordConnector.grading, SourceCliffordComplex.complexPairMap,
    Matrix.fromBlocks_multiply]

@[simp] theorem matrix_left (N : ℕ) (p : Mat2 × Mat2) (x : Space N)
    (h : HistoryLabel N) (i : Fin 2) :
    action N (matrix N p) x (h, Sum.inl i) =
      ∑ j, p.1 i j * x (h, Sum.inl j) := by
  simp [action_apply, matrix, SourceCliffordComplex.complexPairMap,
    Fintype.sum_prod_type, Fintype.sum_sum_type, Matrix.one_apply]

@[simp] theorem matrix_right (N : ℕ) (p : Mat2 × Mat2) (x : Space N)
    (h : HistoryLabel N) (i : Fin 2) :
    action N (matrix N p) x (h, Sum.inr i) =
      ∑ j, p.2 i j * x (h, Sum.inr j) := by
  simp [action_apply, matrix, SourceCliffordComplex.complexPairMap,
    Fintype.sum_prod_type, Fintype.sum_sum_type, Matrix.one_apply]

theorem sectorCoordinates_matrix (N : ℕ) (p : Mat2 × Mat2) (x : Space N) :
    WithLp.ofLp (sectorCoordinates N (action N (matrix N p) x)) =
      (sectorAction N p.1 (WithLp.ofLp (sectorCoordinates N x)).1,
        sectorAction N p.2 (WithLp.ofLp (sectorCoordinates N x)).2) := by
  apply Prod.ext <;> ext ⟨h, i⟩
  · change action N (matrix N p) x (h, Sum.inl i) =
      ∑ j, p.1 i j * x (h, Sum.inl j)
    exact matrix_left N p x h i
  · change action N (matrix N p) x (h, Sum.inr i) =
      ∑ j, p.2 i j * x (h, Sum.inr j)
    exact matrix_right N p x h i

theorem connector_covariance (N : ℕ) (p : Mat2 × Mat2) (M : Mat2) :
    matrix N p * connector N M * (matrix N p).conjTranspose =
      connector N (p.1 * M * p.2.conjTranspose) := by
  simp only [matrix, connector, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, one_mul,
    SourceCliffordComplex.connector_covariance]

theorem action_connector_covariance (N : ℕ) (p : Mat2 × Mat2) (M : Mat2) :
    action N (matrix N p) * action N (connector N M) *
      (action N (matrix N p)).adjoint =
        action N (connector N (p.1 * M * p.2.conjTranspose)) := by
  rw [action_adjoint, ← map_mul, ← map_mul, connector_covariance]

theorem matrix_historyLift (N : ℕ) (p : Mat2 × Mat2)
    (A : Matrix (HistoryLabel N) (HistoryLabel N) ℂ) :
    matrix N p * historyLift N A = historyLift N A * matrix N p := by
  simp [matrix, historyLift, ← Matrix.mul_kronecker_mul]

theorem hermite_covariance (N : ℕ) (p : Mat2 × Mat2) (M : Mat2) :
    fullHermiteOperator N (matrix N p) *
      HistoryComplexConnector.hermiteConnector N M *
      (fullHermiteOperator N (matrix N p)).adjoint =
        HistoryComplexConnector.hermiteConnector N (p.1 * M * p.2.conjTranspose) := by
  rw [HistoryComplexConnector.hermiteConnector, ← fullHermiteOperator_adjoint,
    ← fullHermiteOperator_mul, ← fullHermiteOperator_mul, connector_covariance]
  rfl

structure Conclusions : Prop where
  faithful_even_action : ∀ N, Function.Injective (matrix N)
  independent_sectors : ∀ N p (x : Space N),
    WithLp.ofLp (sectorCoordinates N (action N (matrix N p) x)) =
      (sectorAction N p.1 (WithLp.ofLp (sectorCoordinates N x)).1,
        sectorAction N p.2 (WithLp.ofLp (sectorCoordinates N x)).2)
  exact_covariance : ∀ N p M,
    matrix N p * connector N M * (matrix N p).conjTranspose =
      connector N (p.1 * M * p.2.conjTranspose)
  arithmetic_compatibility : ∀ N p A,
    matrix N p * historyLift N A = historyLift N A * matrix N p

theorem generated : Conclusions where
  faithful_even_action := matrix_injective
  independent_sectors := sectorCoordinates_matrix
  exact_covariance := connector_covariance
  arithmetic_compatibility := matrix_historyLift

end GeneratedFoundations.Arithmetic.HistoryEvenResponse

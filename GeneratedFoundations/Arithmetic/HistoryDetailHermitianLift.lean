module

public import GeneratedFoundations.Arithmetic.HistoryDetailGeneratorLift
public import GeneratedFoundations.Operations.MatrixHermitianFrame

/-!
# Hermitian operations on every actual phase-detail coefficient

Symmetric and antisymmetric centred matrices are represented on the actual
detail range, extended by zero on its invariant complement, then retained
at all four original source coordinates. The complete Hermitian quadratic
sum equals the previously calculated detail response. The zero-dimensional
case is included. Neither a physical colour dimension nor an additional
response coefficient is used.

This frame is deliberately indexed by ordered pairs. It is redundant and
has the half-trace normalization proved below; independence is not inferred
from the independent basis of the full operation space.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryDetailHermitianLift

open HistoryDetailCasimir (Detail BasisIndex basis)
open HistoryJointCharge (Space)
open Operations

def matrixLift (n : ℕ) : Matrix (BasisIndex n) (BasisIndex n) ℂ →ₗ[ℂ]
    Module.End ℂ (Space n) :=
  (HistoryDetailGeneratorLift.fullLift n).comp
    (Matrix.toLinAlgEquiv (basis n).toBasis).toLinearMap

theorem matrixLift_mul (n : ℕ) (A B : Matrix (BasisIndex n) (BasisIndex n) ℂ) :
    matrixLift n (A * B) = matrixLift n A * matrixLift n B := by
  change HistoryDetailGeneratorLift.fullLift n
    (Matrix.toLinAlgEquiv (basis n).toBasis (A * B)) = _
  rw [map_mul, HistoryDetailGeneratorLift.fullLift_mul]
  rfl

theorem matrixLift_one (n : ℕ) : matrixLift n 1 =
    HistoryJointCharge.blocks n (fun _ => HistoryPhaseProjection.residual n) := by
  change HistoryDetailGeneratorLift.fullLift n
    (Matrix.toLinAlgEquiv (basis n).toBasis 1) = _
  rw [map_one, HistoryDetailGeneratorLift.fullLift_one]

theorem matrixLift_adjoint (n : ℕ) (A : Matrix (BasisIndex n) (BasisIndex n) ℂ) :
    (matrixLift n A).adjoint = matrixLift n A.conjTranspose := by
  change (HistoryDetailGeneratorLift.fullLift n
    (Matrix.toLinAlgEquiv (basis n).toBasis A)).adjoint = _
  rw [HistoryDetailGeneratorLift.fullLift_adjoint]
  change HistoryDetailGeneratorLift.fullLift n
    (LinearMap.adjoint ((Matrix.toLinAlgEquiv (basis n).toBasis) A)) =
      HistoryDetailGeneratorLift.fullLift n
        ((Matrix.toLinAlgEquiv (basis n).toBasis) A.conjTranspose)
  exact congrArg (HistoryDetailGeneratorLift.fullLift n)
    (Matrix.toLin_conjTranspose (basis n) (basis n) A).symm

def symmetric (n : ℕ) (i j : BasisIndex n) : Module.End ℂ (Space n) :=
  matrixLift n (MatrixHermitianFrame.symmetric i j)

def antisymmetric (n : ℕ) (i j : BasisIndex n) : Module.End ℂ (Space n) :=
  matrixLift n (MatrixHermitianFrame.antisymmetric i j)

theorem symmetric_adjoint (n : ℕ) (i j : BasisIndex n) :
    (symmetric n i j).adjoint = symmetric n i j := by
  rw [symmetric, matrixLift_adjoint, (MatrixHermitianFrame.symmetric_hermitian i j).eq]

theorem antisymmetric_adjoint (n : ℕ) (i j : BasisIndex n) :
    (antisymmetric n i j).adjoint = antisymmetric n i j := by
  rw [antisymmetric, matrixLift_adjoint, (MatrixHermitianFrame.antisymmetric_hermitian i j).eq]

def quadraticResponse (n : ℕ) : Module.End ℂ (Space n) :=
  (1 / 2 : ℂ) • ∑ i, ∑ j,
    (symmetric n i j * symmetric n i j + antisymmetric n i j * antisymmetric n i j)

theorem quadraticResponse_eq (n : ℕ) : quadraticResponse n =
    HistoryChargedCasimirResponse.detailResponse n := by
  have hm := congrArg (matrixLift n)
    (MatrixHermitianFrame.response_eq_traceDual (ι := BasisIndex n))
  have ht : matrixLift n (MatrixDefiningCasimir.response (ι := BasisIndex n)) =
      HistoryDetailGeneratorLift.quadraticResponse n := by
    simp only [MatrixDefiningCasimir.response, MatrixDefiningCasimir.quadraticSum,
      map_smul, map_sum, HistoryDetailGeneratorLift.quadraticResponse,
      HistoryDetailGeneratorLift.generator, matrixLift, LinearMap.comp_apply,
      AlgEquiv.toLinearMap_apply, FiniteDefiningResponse.generator, map_mul,
      HistoryDetailGeneratorLift.fullLift_mul]
  rw [ht, HistoryDetailGeneratorLift.quadraticResponse_eq] at hm
  simpa only [MatrixHermitianFrame.response, map_smul, map_sum, map_add,
    matrixLift_mul, quadraticResponse, symmetric, antisymmetric] using hm

theorem quadraticResponse_adjoint (n : ℕ) :
    (quadraticResponse n).adjoint = quadraticResponse n := by
  rw [quadraticResponse_eq]
  exact (HistoryChargedCasimirResponse.detailResponse_positive n).adjoint_eq

theorem quadraticResponse_nonneg (n : ℕ) (x : Space n) :
    0 ≤ (inner ℂ x (quadraticResponse n x)).re := by
  rw [quadraticResponse_eq]
  exact (HistoryChargedCasimirResponse.detailResponse_positive n).re_inner_nonneg_right x

structure Conclusions : Prop where
  supported_identity : ∀ n, matrixLift n 1 =
    HistoryJointCharge.blocks n (fun _ => HistoryPhaseProjection.residual n)
  symmetric_generators : ∀ n i j, (symmetric n i j).adjoint = symmetric n i j
  antisymmetric_generators : ∀ n i j, (antisymmetric n i j).adjoint = antisymmetric n i j
  complete_quadratic_sum : ∀ n, quadraticResponse n =
    HistoryChargedCasimirResponse.detailResponse n
  positive_response : ∀ n x, 0 ≤ (inner ℂ x (quadraticResponse n x)).re

theorem generated : Conclusions where
  supported_identity := matrixLift_one
  symmetric_generators := symmetric_adjoint
  antisymmetric_generators := antisymmetric_adjoint
  complete_quadratic_sum := quadraticResponse_eq
  positive_response := quadraticResponse_nonneg

end GeneratedFoundations.Arithmetic.HistoryDetailHermitianLift

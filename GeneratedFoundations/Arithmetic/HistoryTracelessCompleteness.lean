module

public import GeneratedFoundations.Arithmetic.HistoryDefiningResponse
public import GeneratedFoundations.Operations.MatrixTracelessCompleteness

/-!
# One complete arithmetic generator family for both quadratic responses

The sandwich and double-commutator below use the same centred generators
already acting on every retained history, phase and source coordinate. Their
trace-dual normalization is computed before transport to operators. Thus the
defining and adjoint response coefficients refer to the same full carrier.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryTracelessCompleteness

open HistoryCliffordAction (Index Space Algebra action)
open HistoryDefiningResponse (generator)
open HistoryAdjointCasimir (dimension)

def sandwich (N : ℕ) (X : Module.End ℂ (Space N)) : Module.End ℂ (Space N) :=
  (1 / 2 : ℂ) • ∑ i, ∑ j, generator N i j * X * generator N j i

theorem sandwich_representation (N : ℕ) (X : Algebra N) :
    sandwich N (action N X) =
      action N (Operations.MatrixTracelessCompleteness.sandwich X) := by
  simp only [sandwich, Operations.MatrixTracelessCompleteness.sandwich,
    HistoryDefiningResponse.generator, map_smul, map_sum, map_mul]

theorem sandwich_eq (N : ℕ) (X : Module.End ℂ (Space N)) :
    sandwich N X = (LinearMap.trace ℂ (Space N) X / 2) • 1 -
      (1 / (2 * dimension N) : ℂ) • X := by
  have h := sandwich_representation N ((action N).symm X)
  rw [AlgEquiv.apply_symm_apply, Operations.MatrixTracelessCompleteness.sandwich_eq,
    map_sub, map_smul, map_smul, map_one, AlgEquiv.apply_symm_apply] at h
  rw [← HistoryAdjointCasimir.trace_action N ((action N).symm X),
    AlgEquiv.apply_symm_apply] at h
  exact h

def commutator (N : ℕ) (X Y : Module.End ℂ (Space N)) : Module.End ℂ (Space N) :=
  X * Y - Y * X

def adjointResponse (N : ℕ) (X : Module.End ℂ (Space N)) : Module.End ℂ (Space N) :=
  (1 / 2 : ℂ) • ∑ i, ∑ j,
    commutator N (generator N i j) (commutator N (generator N j i) X)

theorem adjointResponse_representation (N : ℕ) (X : Algebra N) :
    adjointResponse N (action N X) =
      action N (Operations.MatrixTracelessCompleteness.adjointResponse X) := by
  simp only [adjointResponse, commutator,
    Operations.MatrixTracelessCompleteness.adjointResponse,
    Operations.MatrixAdjointCasimir.commutator, HistoryDefiningResponse.generator,
    map_smul, map_sum, map_sub, map_mul]

theorem adjointResponse_eq_operator (N : ℕ) (X : Module.End ℂ (Space N)) :
    adjointResponse N X = HistoryAdjointCasimir.operator N X := by
  have h := adjointResponse_representation N ((action N).symm X)
  rw [AlgEquiv.apply_symm_apply,
    Operations.MatrixTracelessCompleteness.adjointResponse_eq_casimir] at h
  exact h

theorem adjointResponse_expansion (N : ℕ) (X : Module.End ℂ (Space N)) :
    adjointResponse N X = HistoryDefiningResponse.response N * X -
      (2 : ℂ) • sandwich N X + X * HistoryDefiningResponse.response N := by
  have h := congrArg (action N)
    (Operations.MatrixTracelessCompleteness.adjointResponse_expansion ((action N).symm X))
  rw [← adjointResponse_representation, AlgEquiv.apply_symm_apply] at h
  simp only [map_add, map_sub, map_mul, map_smul] at h
  rw [AlgEquiv.apply_symm_apply, ← sandwich_representation,
    AlgEquiv.apply_symm_apply] at h
  have hr : action N (Operations.MatrixDefiningCasimir.response (ι := Index N)) =
      HistoryDefiningResponse.response N := by
    simp only [Operations.MatrixDefiningCasimir.response,
      Operations.MatrixDefiningCasimir.quadraticSum, HistoryDefiningResponse.response,
      HistoryDefiningResponse.generator, map_smul, map_sum, map_mul]
  rw [hr] at h
  exact h

theorem complete_response (N : ℕ) (X : Module.End ℂ (Space N)) :
    adjointResponse N X = (dimension N : ℂ) • X -
      LinearMap.trace ℂ (Space N) X • 1 := by
  rw [adjointResponse_eq_operator, HistoryAdjointCasimir.operator_eq]

theorem scalar_kernel (N : ℕ) (X : Module.End ℂ (Space N)) :
    adjointResponse N X = 0 ↔ ∃ c : ℂ, X = c • 1 := by
  rw [adjointResponse_eq_operator, HistoryAdjointCasimir.operator_kernel]

structure Conclusions : Prop where
  actual_sandwich : ∀ N (X : Module.End ℂ (Space N)),
    sandwich N X = (LinearMap.trace ℂ (Space N) X / 2) • 1 -
      (1 / (2 * dimension N) : ℂ) • X
  joint_expansion : ∀ N X,
    adjointResponse N X = HistoryDefiningResponse.response N * X -
      (2 : ℂ) • sandwich N X + X * HistoryDefiningResponse.response N
  existing_operator : ∀ N X, adjointResponse N X = HistoryAdjointCasimir.operator N X
  exact_kernel : ∀ N X, adjointResponse N X = 0 ↔ ∃ c : ℂ, X = c • 1

theorem generated : Conclusions where
  actual_sandwich := sandwich_eq
  joint_expansion := adjointResponse_expansion
  existing_operator := adjointResponse_eq_operator
  exact_kernel := scalar_kernel

end GeneratedFoundations.Arithmetic.HistoryTracelessCompleteness

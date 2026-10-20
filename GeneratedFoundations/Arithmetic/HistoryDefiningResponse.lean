module

public import GeneratedFoundations.Arithmetic.HistoryAdjointCasimir
public import GeneratedFoundations.Operations.MatrixDefiningCasimir

/-!
# The defining quadratic response at the actual history dimension

The full trace-free operation family, not a fixed physical colour corner,
acts on the complete generated history--phase carrier. Its trace-dual
quadratic sum is transported through the existing faithful representation.
The normalization, positivity and lower bound are then calculated from the
actual dimension. This defining state response and the adjoint response on
operators have different eigenvalues and are kept as separate constructions.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryDefiningResponse

open HistoryCliffordAction (Index Space Algebra action historyPoint)
open HistoryAdjointCasimir (dimension dimension_ge_four)

noncomputable instance (N : ℕ) : Nonempty (Index N) :=
  ⟨(historyPoint N, Sum.inl 0)⟩

def coefficient (N : ℕ) : ℝ := Operations.MatrixDefiningCasimir.coefficient (Index N)

theorem coefficient_eq (N : ℕ) :
    coefficient N = ((dimension N : ℝ) - (dimension N : ℝ)⁻¹) / 2 := rfl

theorem coefficient_lower (N : ℕ) : (15 / 8 : ℝ) ≤ coefficient N := by
  have hd : (4 : ℝ) ≤ dimension N := by exact_mod_cast dimension_ge_four N
  have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) hd
  simp only [one_div] at hi
  rw [coefficient_eq]
  norm_num at hi
  linarith

theorem coefficient_pos (N : ℕ) : 0 < coefficient N :=
  lt_of_lt_of_le (by norm_num) (coefficient_lower N)

def generator (N : ℕ) (i j : Index N) : Module.End ℂ (Space N) :=
  action N (Operations.MatrixDefiningCasimir.centredUnit i j)

theorem generator_trace (N : ℕ) (i j : Index N) :
    LinearMap.trace ℂ (Space N) (generator N i j) = 0 := by
  rw [generator, HistoryAdjointCasimir.trace_action]
  exact Operations.MatrixDefiningCasimir.trace_centredUnit i j

theorem generator_adjoint (N : ℕ) (i j : Index N) :
    (generator N i j).adjoint = generator N j i := by
  rw [generator, HistoryCliffordAction.action_adjoint,
    Operations.MatrixDefiningCasimir.centredUnit_adjoint]
  rfl

/-- The actual complete quadratic sum in the faithful operation action. -/
def response (N : ℕ) : Module.End ℂ (Space N) :=
  (1 / 2 : ℂ) • ∑ i, ∑ j, generator N i j * generator N j i

theorem response_eq (N : ℕ) :
    response N = (coefficient N : ℂ) • (1 : Module.End ℂ (Space N)) := by
  have h := congrArg (action N)
    (Operations.MatrixDefiningCasimir.response_eq (ι := Index N))
  simpa only [Operations.MatrixDefiningCasimir.response,
    Operations.MatrixDefiningCasimir.quadraticSum, response, generator,
    map_smul, map_sum, map_mul, map_one, coefficient] using h

theorem response_adjoint (N : ℕ) : (response N).adjoint = response N := by
  symm
  apply (LinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  rw [response_eq]
  change inner ℂ ((coefficient N : ℂ) • x) y =
    inner ℂ x ((coefficient N : ℂ) • y)
  rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal]

theorem response_commutes (N : ℕ) (T : Module.End ℂ (Space N)) :
    response N * T = T * response N := by
  rw [response_eq]
  simp

def quadratic (N : ℕ) (x : Space N) : ℝ := (inner ℂ x (response N x)).re

theorem quadratic_eq (N : ℕ) (x : Space N) :
    quadratic N x = coefficient N * ‖x‖ ^ 2 := by
  rw [quadratic, response_eq]
  change (inner ℂ x ((coefficient N : ℂ) • x)).re = _
  rw [inner_smul_right]
  change ((coefficient N : ℂ) * inner ℂ x x).re = _
  rw [Complex.mul_re]
  change coefficient N * (inner ℂ x x).re - 0 * (inner ℂ x x).im = _
  rw [zero_mul, sub_zero]
  exact congrArg (coefficient N * ·) (inner_self_eq_norm_sq (𝕜 := ℂ) x)

theorem quadratic_coercive (N : ℕ) (x : Space N) :
    (15 / 8 : ℝ) * ‖x‖ ^ 2 ≤ quadratic N x := by
  rw [quadratic_eq]
  exact mul_le_mul_of_nonneg_right (coefficient_lower N) (sq_nonneg _)

theorem quadratic_zero_iff (N : ℕ) (x : Space N) : quadratic N x = 0 ↔ x = 0 := by
  rw [quadratic_eq, mul_eq_zero]
  simp [(coefficient_pos N).ne']

theorem response_kernel (N : ℕ) (x : Space N) : response N x = 0 ↔ x = 0 := by
  constructor
  · intro h
    apply (quadratic_zero_iff N x).mp
    simp [quadratic, h]
  · rintro rfl
    exact map_zero _

structure Conclusions : Prop where
  actual_coefficient : ∀ N,
    coefficient N = ((dimension N : ℝ) - (dimension N : ℝ)⁻¹) / 2
  complete_sum : ∀ N,
    response N = (coefficient N : ℂ) • (1 : Module.End ℂ (Space N))
  self_adjoint : ∀ N, (response N).adjoint = response N
  full_covariance : ∀ N T, response N * T = T * response N
  uniform_lower_bound : ∀ N (x : Space N), (15 / 8 : ℝ) * ‖x‖ ^ 2 ≤ quadratic N x
  no_unobserved_direction : ∀ N (x : Space N), response N x = 0 ↔ x = 0

theorem generated : Conclusions where
  actual_coefficient := coefficient_eq
  complete_sum := response_eq
  self_adjoint := response_adjoint
  full_covariance := response_commutes
  uniform_lower_bound := quadratic_coercive
  no_unobserved_direction := response_kernel

end GeneratedFoundations.Arithmetic.HistoryDefiningResponse

module

public import GeneratedFoundations.Arithmetic.HistoryAdjointFlow

/-!
# Variation of the full arithmetic adjoint response

The action is the complete trace form of the already computed double
commutator. Its gradient and mixed Hessian are derived on all endomorphisms
of the actual history--phase carrier. The scalar kernel is retained; the
trace-free lower bound uses that carrier's computed dimension.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Arithmetic.HistoryAdjointVariation

open HistoryCliffordAction (Space)
open HistoryAdjointCasimir
open HistoryAdjointFlow (Operator responseAction)
open Geometry.HilbertTraceVariation

theorem operator_add (N : ℕ) (X Y : Operator N) :
    operator N (X + Y) = operator N X + operator N Y := by
  simp only [operator_eq, map_add, smul_add, add_smul]
  module

theorem operator_real_smul (N : ℕ) (t : ℝ) (X : Operator N) :
    operator N ((t : ℂ) • X) = (t : ℂ) • operator N X := by
  simp only [operator_eq, map_smul, smul_sub, smul_smul, smul_eq_mul]
  module

theorem pair_traceless_right (N : ℕ) (X Y : Operator N) :
    pair X (tracelessPart N Y) = pair (tracelessPart N X) (tracelessPart N Y) := by
  calc
    _ = pair (scalarPart N X + tracelessPart N X) (tracelessPart N Y) := by
      rw [← complete_decomposition N X]
    _ = _ := by
      have ho : pair (scalarPart N X) (tracelessPart N Y) = 0 :=
        scalar_traceless_orthogonal N _ _ (trace_tracelessPart N Y)
      rw [pair_add_left, ho, zero_add]

/-- Symmetry of the actual response, including arbitrary complex matrix
coefficients and its scalar kernel. -/
theorem operator_pair_symm (N : ℕ) (X Y : Operator N) :
    pair X (operator N Y) = pair Y (operator N X) := by
  simp only [operator_eq_tracelessPart]
  have hX := pair_smul_right (dimension N : ℝ) X (tracelessPart N Y)
  have hY := pair_smul_right (dimension N : ℝ) Y (tracelessPart N X)
  simp only [Complex.ofReal_natCast] at hX hY
  rw [hX, hY, pair_traceless_right N X Y, pair_traceless_right N Y X,
    pair_symm (tracelessPart N X) (tracelessPart N Y)]

/-- Exact quadratic line expansion before any estimate. -/
theorem action_line (N : ℕ) (X H : Operator N) (t : ℝ) :
    responseAction N (X + (t : ℂ) • H) =
      responseAction N X + t * pair H (operator N X) +
        t ^ 2 * responseAction N H := by
  simp only [responseAction, operator_add, operator_real_smul,
    pair_add_left, pair_add_right, pair_smul_left, pair_smul_right,
    operator_pair_symm N X H]
  ring

theorem action_line_hasDerivAt (N : ℕ) (X H : Operator N) (t : ℝ) :
    HasDerivAt (fun s : ℝ => responseAction N (X + (s : ℂ) • H))
      (pair H (operator N X) + 2 * t * responseAction N H) t := by
  convert quartic_hasDerivAt (responseAction N X) (pair H (operator N X))
    (responseAction N H) 0 0 t using 1
  · funext s
    rw [action_line]
    ring
  · ring

def firstVariation (N : ℕ) (X H : Operator N) : ℝ := pair H (operator N X)

theorem firstVariation_eq_deriv (N : ℕ) (X H : Operator N) :
    deriv (fun t : ℝ => responseAction N (X + (t : ℂ) • H)) 0 =
      firstVariation N X H := by
  rw [(action_line_hasDerivAt N X H 0).deriv]
  simp [firstVariation]

/-- The mixed derivative is the original complete operator, rather than a
second quadratic form assigned independently of the action. -/
theorem firstVariation_hasDerivAt (N : ℕ) (X H K : Operator N) (t : ℝ) :
    HasDerivAt (fun s : ℝ => firstVariation N (X + (s : ℂ) • K) H)
      (pair H (operator N K)) t := by
  have h := (hasDerivAt_const t (pair H (operator N X))).add
    ((hasDerivAt_id t).mul_const (pair H (operator N K)))
  convert h using 1
  · funext s
    change pair H (operator N (X + (s : ℂ) • K)) =
      pair H (operator N X) + s * pair H (operator N K)
    rw [operator_add, operator_real_smul, pair_add_right, pair_smul_right]
  · simp

def hessian (N : ℕ) (H K : Operator N) : ℝ := pair H (operator N K)

theorem hessian_eq_mixed_deriv (N : ℕ) (X H K : Operator N) :
    deriv (fun t : ℝ => firstVariation N (X + (t : ℂ) • K) H) 0 =
      hessian N H K :=
  (firstVariation_hasDerivAt N X H K 0).deriv

theorem hessian_symm (N : ℕ) (H K : Operator N) :
    hessian N H K = hessian N K H := operator_pair_symm N H K

theorem hessian_coercivity (N : ℕ) (H : Operator N) :
    4 * Geometry.HilbertTraceQuadratic.energy (tracelessPart N H) ≤
      hessian N H H := complete_coercivity N H

/-- No certificate of stationarity is supplied as root input: all stationary
operators of the actual action are exactly its computed scalar kernel. -/
theorem stationary_iff_scalar (N : ℕ) (X : Operator N) :
    (∀ H : Operator N, firstVariation N X H = 0) ↔
      ∃ c : ℂ, X = c • (1 : Operator N) := by
  constructor
  · intro h
    have haction : responseAction N X = 0 := by
      rw [responseAction, show pair X (operator N X) = 0 from h X]
      norm_num
    have hp := (HistoryAdjointFlow.responseAction_zero_iff N X).1 haction
    apply (operator_kernel N X).1
    rw [operator_eq_tracelessPart, hp, smul_zero]
  · intro h H
    have hz := (operator_kernel N X).2 h
    simp [firstVariation, hz, pair]

structure Conclusions : Prop where
  action_derivative : ∀ N X H t,
    HasDerivAt (fun s : ℝ => responseAction N (X + (s : ℂ) • H))
      (pair H (operator N X) + 2 * t * responseAction N H) t
  mixed_derivative : ∀ N X H K,
    deriv (fun t : ℝ => firstVariation N (X + (t : ℂ) • K) H) 0 = hessian N H K
  hessian_symmetric : ∀ N H K, hessian N H K = hessian N K H
  uniform_restoring_bound : ∀ N H,
    4 * Geometry.HilbertTraceQuadratic.energy (tracelessPart N H) ≤ hessian N H H
  exact_stationary_space : ∀ N X,
    (∀ H : Operator N, firstVariation N X H = 0) ↔ ∃ c : ℂ, X = c • (1 : Operator N)

theorem generated : Conclusions where
  action_derivative := action_line_hasDerivAt
  mixed_derivative := hessian_eq_mixed_deriv
  hessian_symmetric := hessian_symm
  uniform_restoring_bound := hessian_coercivity
  exact_stationary_space := stationary_iff_scalar

end GeneratedFoundations.Arithmetic.HistoryAdjointVariation

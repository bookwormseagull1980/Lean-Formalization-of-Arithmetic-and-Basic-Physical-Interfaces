module

public import GeneratedFoundations.Arithmetic.HistoryDefiningResponse
public import GeneratedFoundations.Geometry.HilbertTraceVariation

/-!
# Action, variation and evolution of the complete defining response

The operator in this module is the quadratic sum already calculated from
all trace-free operations on the actual history--phase/source carrier. The
action, first variation, Hessian and evolution are derived for that operator
on its full state space. The positive coefficient and uniform rate are
outputs of the actual dimension calculation. They do not assert a rate for
the distinct Gaussian-weighted reaction operator on complete histories.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Arithmetic.HistoryDefiningDynamics

open HistoryCliffordAction (Space)
open HistoryDefiningResponse (coefficient coefficient_pos coefficient_lower response)

def action (N : ℕ) (x : Space N) : ℝ := coefficient N / 2 * ‖x‖ ^ 2

theorem action_eq_response (N : ℕ) (x : Space N) :
    2 * action N x = HistoryDefiningResponse.quadratic N x := by
  rw [HistoryDefiningResponse.quadratic_eq, action]
  ring

theorem action_coercive (N : ℕ) (x : Space N) :
    (15 / 16 : ℝ) * ‖x‖ ^ 2 ≤ action N x := by
  have hc := coefficient_lower N
  unfold action
  nlinarith [sq_nonneg ‖x‖]

theorem action_zero_iff (N : ℕ) (x : Space N) : action N x = 0 ↔ x = 0 := by
  have hc : coefficient N / 2 ≠ 0 := ne_of_gt (div_pos (coefficient_pos N) (by norm_num))
  simp [action, hc]

def firstVariation (N : ℕ) (x h : Space N) : ℝ := coefficient N * inner ℝ h x

theorem action_line (N : ℕ) (x h : Space N) (t : ℝ) :
    action N (x + t • h) = action N x + t * firstVariation N x h + t ^ 2 * action N h := by
  simp only [action, firstVariation, norm_add_sq_real, real_inner_smul_right,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [real_inner_comm x h]
  ring

theorem action_hasDerivAt (N : ℕ) (x h : Space N) (t : ℝ) :
    HasDerivAt (fun s : ℝ => action N (x + s • h))
      (firstVariation N x h + 2 * t * action N h) t := by
  convert Geometry.HilbertTraceVariation.quartic_hasDerivAt
    (action N x) (firstVariation N x h) (action N h) 0 0 t using 1
  · funext s
    rw [action_line]
    ring
  · ring

theorem firstVariation_self (N : ℕ) (x : Space N) :
    firstVariation N x x = 2 * action N x := by
  rw [firstVariation, real_inner_self_eq_norm_sq, action]
  ring

def hessian (N : ℕ) (h k : Space N) : ℝ := coefficient N * inner ℝ h k

theorem firstVariation_hasDerivAt (N : ℕ) (x h k : Space N) (t : ℝ) :
    HasDerivAt (fun s : ℝ => firstVariation N (x + s • k) h) (hessian N h k) t := by
  have ht := (hasDerivAt_const t (firstVariation N x h)).add
    ((hasDerivAt_id t).mul_const (hessian N h k))
  convert ht using 1
  · funext s
    simp only [firstVariation, hessian, inner_add_right, real_inner_smul_right,
      Pi.add_apply, id_eq]
    ring
  · simp

theorem hessian_symm (N : ℕ) (h k : Space N) : hessian N h k = hessian N k h := by
  rw [hessian, hessian, real_inner_comm h k]

theorem hessian_coercive (N : ℕ) (h : Space N) :
    (15 / 8 : ℝ) * ‖h‖ ^ 2 ≤ hessian N h h := by
  rw [hessian, real_inner_self_eq_norm_sq]
  exact mul_le_mul_of_nonneg_right (coefficient_lower N) (sq_nonneg _)

theorem stationary_iff_zero (N : ℕ) (x : Space N) :
    (∀ h : Space N, firstVariation N x h = 0) ↔ x = 0 := by
  constructor
  · intro hx
    apply (action_zero_iff N x).mp
    have h := hx x
    rw [firstVariation_self] at h
    linarith
  · rintro rfl h
    simp [firstVariation]

theorem response_apply_real (N : ℕ) (x : Space N) : response N x = coefficient N • x := by
  rw [HistoryDefiningResponse.response_eq]
  rfl

theorem hessian_operator (N : ℕ) (h k : Space N) :
    hessian N h k = inner ℝ h (response N k) := by
  rw [response_apply_real, real_inner_smul_right]
  rfl

def flow (N : ℕ) (t : ℝ) (x : Space N) : Space N := Real.exp (-coefficient N * t) • x

@[simp] theorem flow_zero (N : ℕ) (x : Space N) : flow N 0 x = x := by simp [flow]

@[simp] theorem flow_zero_input (N : ℕ) (t : ℝ) : flow N t 0 = 0 := by simp [flow]

theorem flow_add (N : ℕ) (s t : ℝ) (x : Space N) :
    flow N s (flow N t x) = flow N (s + t) x := by
  simp only [flow, smul_smul, mul_add, Real.exp_add]

theorem flow_hasDerivAt (N : ℕ) (t : ℝ) (x : Space N) :
    HasDerivAt (fun s : ℝ => flow N s x) (-(response N (flow N t x))) t := by
  have h := (((hasDerivAt_id t).const_mul (-coefficient N)).exp).smul_const x
  convert h using 1
  · rfl
  · rw [response_apply_real, flow, smul_smul, ← neg_smul]
    congr 1
    simp only [id_eq, mul_one]
    ring

theorem flow_continuous (N : ℕ) (x : Space N) : Continuous (fun t : ℝ => flow N t x) :=
  continuous_iff_continuousAt.mpr fun t => (flow_hasDerivAt N t x).continuousAt

theorem norm_flow (N : ℕ) (t : ℝ) (x : Space N) :
    ‖flow N t x‖ = Real.exp (-coefficient N * t) * ‖x‖ := by
  simp only [flow, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

theorem action_flow (N : ℕ) (t : ℝ) (x : Space N) :
    action N (flow N t x) = Real.exp (-2 * coefficient N * t) * action N x := by
  rw [action, norm_flow, mul_pow, ← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  have he : (2 : ℝ) * (-coefficient N * t) = -2 * coefficient N * t := by ring
  rw [he]
  unfold action
  ring

theorem uniform_decay (N : ℕ) (t : ℝ) (ht : 0 ≤ t) (x : Space N) :
    action N (flow N t x) ≤ Real.exp (-(15 / 4 : ℝ) * t) * action N x := by
  rw [action_flow]
  apply mul_le_mul_of_nonneg_right
  · apply Real.exp_le_exp.mpr
    have hc := mul_le_mul_of_nonneg_right (coefficient_lower N) ht
    linarith
  · exact mul_nonneg (div_nonneg (coefficient_pos N).le (by norm_num)) (sq_nonneg _)

structure Conclusions : Prop where
  actual_action : ∀ N (x : Space N), 2 * action N x = HistoryDefiningResponse.quadratic N x
  uniform_coercivity : ∀ N (x : Space N), (15 / 16 : ℝ) * ‖x‖ ^ 2 ≤ action N x
  actual_derivative : ∀ N (x h : Space N) t,
    HasDerivAt (fun s : ℝ => action N (x + s • h))
      (firstVariation N x h + 2 * t * action N h) t
  mixed_response : ∀ N (h k : Space N), hessian N h k = inner ℝ h (response N k)
  unique_stationary : ∀ N (x : Space N), (∀ h, firstVariation N x h = 0) ↔ x = 0
  semigroup : ∀ N s t (x : Space N), flow N s (flow N t x) = flow N (s + t) x
  generated_equation : ∀ N t (x : Space N),
    HasDerivAt (fun s : ℝ => flow N s x) (-(response N (flow N t x))) t
  exact_decay : ∀ N t (x : Space N),
    action N (flow N t x) = Real.exp (-2 * coefficient N * t) * action N x
  cutoff_independent_rate : ∀ N t, 0 ≤ t → ∀ x : Space N,
    action N (flow N t x) ≤ Real.exp (-(15 / 4 : ℝ) * t) * action N x

theorem generated : Conclusions where
  actual_action := action_eq_response
  uniform_coercivity := action_coercive
  actual_derivative := action_hasDerivAt
  mixed_response := hessian_operator
  unique_stationary := stationary_iff_zero
  semigroup := flow_add
  generated_equation := flow_hasDerivAt
  exact_decay := action_flow
  cutoff_independent_rate := uniform_decay

end GeneratedFoundations.Arithmetic.HistoryDefiningDynamics

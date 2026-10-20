module

public import GeneratedFoundations.Arithmetic.HistoryHaarClosedHessian
public import GeneratedFoundations.Arithmetic.HistoryDefiningDynamics

/-!
# Joint Haar curvature and defining-state action

The connection has every history/source matrix coefficient in the original
continuous differentiated Haar core. The state is a homogeneous section of
the same complete finite source fibre. Its connection derivative is actual
matrix evaluation in the Haar one-form space. Curvature, this derivative
and the already derived defining Casimir enter one nonnegative functional.

Scaling connection and state together retains their bilinear product: its
energy is quartic, whereas the original differential and defining response
give the quadratic term. The vanishing mixed vacuum block follows from
this expansion. It is not imposed on the nonlinear action. The second
variation has a cutoff-independent positive lower bound on the joint
carrier. This homogeneous-section result does not assert a field equation
for arbitrary position-dependent matter sections.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryHaarCoupledAction

open Geometry.SourceOneFormContinuousCore Geometry.SourceOneFormHaarBlock
open Geometry.SourceOneFormHodgeLaplacian
open HistoryHaarMatrixCurvature (Index Coefficients differentiated curvature vertex)

abbrev State (N : ℕ) := HistoryCliffordAction.Space N
abbrev MatterFields (N : ℕ) := PiLp 2 (fun _ : Index N => OneFormL2)

/-- Matrix evaluation on a homogeneous section in the original Haar space. -/
def connectionDerivative (N : ℕ) (A : Coefficients N) (ψ : State N) : MatterFields N :=
  WithLp.toLp 2 fun i => ∑ j, ψ j • includeCore (A i j)

theorem connectionDerivative_smul (N : ℕ) (z w : ℂ)
    (A : Coefficients N) (ψ : State N) :
    connectionDerivative N (z • A) (w • ψ) =
      (z * w) • connectionDerivative N A ψ := by
  apply (WithLp.equiv 2 (Index N → OneFormL2)).injective
  funext i
  change (∑ j, (w * ψ j) • includeCore (z • A i j)) =
    (z * w) • ∑ j, ψ j • includeCore (A i j)
  simp only [map_smul, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  ring

def action (N : ℕ) (A : Coefficients N) (ψ : State N) : ℝ :=
  HistoryHaarMatrixCurvature.action N A +
    ‖connectionDerivative N A ψ‖ ^ 2 / 2 + HistoryDefiningDynamics.action N ψ

theorem action_nonneg (N : ℕ) (A : Coefficients N) (ψ : State N) :
    0 ≤ action N A ψ := by
  apply add_nonneg (add_nonneg (HistoryHaarMatrixCurvature.action_nonneg N A)
    (div_nonneg (sq_nonneg _) (by norm_num)))
  exact (mul_nonneg (by norm_num : (0 : ℝ) ≤ 15 / 16) (sq_nonneg _)).trans
    (HistoryDefiningDynamics.action_coercive N ψ)

def quadratic (N : ℕ) (A : Coefficients N) (ψ : State N) : ℝ :=
  ‖differentiated N A‖ ^ 2 + HistoryDefiningResponse.coefficient N * ‖ψ‖ ^ 2

def cubic (N : ℕ) (A : Coefficients N) : ℝ :=
  (inner ℂ (differentiated N A) (vertex N A)).re

def quartic (N : ℕ) (A : Coefficients N) (ψ : State N) : ℝ :=
  (‖vertex N A‖ ^ 2 + ‖connectionDerivative N A ψ‖ ^ 2) / 2

theorem action_ray (N : ℕ) (t : ℝ) (A : Coefficients N) (ψ : State N) :
    action N ((t : ℂ) • A) ((t : ℂ) • ψ) =
      t ^ 2 * quadratic N A ψ / 2 + t ^ 3 * cubic N A + t ^ 4 * quartic N A ψ := by
  rw [action, HistoryHaarMatrixCurvature.action_ray, connectionDerivative_smul]
  simp only [HistoryDefiningDynamics.action, norm_smul, Complex.norm_mul,
    Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  unfold quadratic cubic quartic
  ring

/-- Varying only the connection retains the full homogeneous-state term.
In particular its quadratic coupling is not suppressed before variation. -/
theorem action_connection_ray (N : ℕ) (t : ℝ) (A : Coefficients N) (ψ : State N) :
    action N ((t : ℂ) • A) ψ = HistoryDefiningDynamics.action N ψ +
      t ^ 2 * (‖differentiated N A‖ ^ 2 + ‖connectionDerivative N A ψ‖ ^ 2) / 2 +
      t ^ 3 * cubic N A + t ^ 4 * ‖vertex N A‖ ^ 2 / 2 := by
  have hd : connectionDerivative N ((t : ℂ) • A) ψ =
      (t : ℂ) • connectionDerivative N A ψ := by
    simpa using connectionDerivative_smul N (t : ℂ) 1 A ψ
  rw [action, HistoryHaarMatrixCurvature.action_ray, hd]
  simp only [norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  unfold cubic
  ring

theorem action_connection_firstDeriv_zero (N : ℕ) (A : Coefficients N) (ψ : State N) :
    HasDerivAt (fun t : ℝ => action N ((t : ℂ) • A) ψ) 0 0 := by
  convert Geometry.HilbertTraceVariation.quartic_hasDerivAt
    (HistoryDefiningDynamics.action N ψ) 0
    ((‖differentiated N A‖ ^ 2 + ‖connectionDerivative N A ψ‖ ^ 2) / 2)
    (cubic N A) (‖vertex N A‖ ^ 2 / 2) 0 using 1
  · funext t
    rw [action_connection_ray]
    ring
  · simp

/-- The mixed derivative vanishes as a derivative of the original nonlinear
action. Neither the state-dependent connection term nor its return is removed. -/
theorem action_mixed_secondDeriv_zero (N : ℕ) (A : Coefficients N) (ψ : State N) :
    HasDerivAt (fun s : ℝ => deriv (fun t : ℝ =>
      action N ((t : ℂ) • A) ((s : ℂ) • ψ)) 0) 0 0 := by
  have he : (fun s : ℝ => deriv (fun t : ℝ =>
      action N ((t : ℂ) • A) ((s : ℂ) • ψ)) 0) = fun _ => 0 := by
    funext s
    exact (action_connection_firstDeriv_zero N A ((s : ℂ) • ψ)).deriv
  rw [he]
  exact hasDerivAt_const 0 0

def rayDerivative (N : ℕ) (A : Coefficients N) (ψ : State N) (t : ℝ) : ℝ :=
  t * quadratic N A ψ + 3 * t ^ 2 * cubic N A + 4 * t ^ 3 * quartic N A ψ

theorem action_hasDerivAt (N : ℕ) (A : Coefficients N) (ψ : State N) (t : ℝ) :
    HasDerivAt (fun s : ℝ => action N ((s : ℂ) • A) ((s : ℂ) • ψ))
      (rayDerivative N A ψ t) t := by
  convert Geometry.HilbertTraceVariation.quartic_hasDerivAt 0 0
    (quadratic N A ψ / 2) (cubic N A) (quartic N A ψ) t using 1
  · funext s
    rw [action_ray]
    ring
  · unfold rayDerivative
    ring

theorem secondDeriv_zero (N : ℕ) (A : Coefficients N) (ψ : State N) :
    HasDerivAt (fun t : ℝ => deriv
      (fun s : ℝ => action N ((s : ℂ) • A) ((s : ℂ) • ψ)) t)
      (quadratic N A ψ) 0 := by
  have he : (fun t : ℝ => deriv
      (fun s : ℝ => action N ((s : ℂ) • A) ((s : ℂ) • ψ)) t) =
      rayDerivative N A ψ := funext fun t => (action_hasDerivAt N A ψ t).deriv
  rw [he]
  convert Geometry.HilbertTraceVariation.quartic_hasDerivAt 0
    (quadratic N A ψ) (3 * cubic N A) (4 * quartic N A ψ) 0 0 using 1
  · funext t
    unfold rayDerivative
    ring
  · simp

/-- Polarized second variation of the same joint nonlinear functional. -/
def hessian (N : ℕ) (A B : Coefficients N) (ψ ξ : State N) : ℝ :=
  (inner ℂ (differentiated N A) (differentiated N B)).re +
    HistoryDefiningResponse.coefficient N * (inner ℂ ψ ξ).re

theorem hessian_diagonal (N : ℕ) (A : Coefficients N) (ψ : State N) :
    hessian N A A ψ ψ = quadratic N A ψ := by
  simp [hessian, quadratic, inner_self_eq_norm_sq_to_K, pow_two, Complex.mul_re]

theorem hessian_symm (N : ℕ) (A B : Coefficients N) (ψ ξ : State N) :
    hessian N A B ψ ξ = hessian N B A ξ ψ := by
  unfold hessian
  rw [← inner_conj_symm (differentiated N A) (differentiated N B),
    ← inner_conj_symm ψ ξ]
  simp only [Complex.conj_re]

theorem hessian_polarization (N : ℕ) (A B : Coefficients N) (ψ ξ : State N) :
    quadratic N (A + B) (ψ + ξ) - quadratic N A ψ - quadratic N B ξ =
      2 * hessian N A B ψ ξ := by
  simp only [quadratic, map_add, norm_add_sq (𝕜 := ℂ), hessian,
    RCLike.re_eq_complex_re]
  ring

theorem mixed_vacuum_zero (N : ℕ) (A : Coefficients N) (ψ : State N) :
    hessian N A 0 0 ψ = 0 := by
  simp [hessian]

theorem joint_coercivity (N : ℕ) (A : Coefficients N) (ψ : State N) :
    (15 / 8 : ℝ) * (‖HistoryHaarMatrixCurvature.field N A‖ ^ 2 + ‖ψ‖ ^ 2) ≤
      quadratic N A ψ := by
  have hA := HistoryHaarMatrixCurvature.hessian_coercive N A
  have hψ := HistoryDefiningResponse.quadratic_coercive N ψ
  rw [HistoryDefiningResponse.quadratic_eq] at hψ
  unfold quadratic
  nlinarith [sq_nonneg ‖HistoryHaarMatrixCurvature.field N A‖]

theorem hessian_operator (N : ℕ) (A : HistoryHaarClosedHessian.FieldCore N)
    (ψ : State N) :
    quadratic N (HistoryHaarClosedHessian.coefficients N A) ψ =
      (inner ℂ (A : HistoryHaarClosedHessian.Fields N)
        (HistoryHaarClosedHessian.finiteOperator N A)).re +
      (inner ℂ ψ (HistoryDefiningResponse.response N ψ)).re := by
  rw [quadratic, ← HistoryHaarClosedHessian.finiteOperator_energy]
  congr 1
  exact (HistoryDefiningResponse.quadratic_eq N ψ).symm

structure Conclusions : Prop where
  positive_action : ∀ N A ψ, 0 ≤ action N A ψ
  exact_joint_expansion : ∀ N (t : ℝ) A ψ,
    action N ((t : ℂ) • A) ((t : ℂ) • ψ) =
      t ^ 2 * quadratic N A ψ / 2 + t ^ 3 * cubic N A + t ^ 4 * quartic N A ψ
  actual_second_variation : ∀ N A ψ,
    HasDerivAt (fun t : ℝ => deriv
      (fun s : ℝ => action N ((s : ℂ) • A) ((s : ℂ) • ψ)) t)
      (quadratic N A ψ) 0
  full_polarization : ∀ N A B ψ ξ,
    quadratic N (A + B) (ψ + ξ) - quadratic N A ψ - quadratic N B ξ =
      2 * hessian N A B ψ ξ
  derived_mixed_zero : ∀ N A ψ, hessian N A 0 0 ψ = 0
  actual_mixed_variation : ∀ N A ψ,
    HasDerivAt (fun s : ℝ => deriv (fun t : ℝ =>
      action N ((t : ℂ) • A) ((s : ℂ) • ψ)) 0) 0 0
  uniform_joint_bound : ∀ N A ψ,
    (15 / 8 : ℝ) * (‖HistoryHaarMatrixCurvature.field N A‖ ^ 2 + ‖ψ‖ ^ 2) ≤
      quadratic N A ψ

theorem generated : Conclusions :=
  ⟨action_nonneg, action_ray, secondDeriv_zero, hessian_polarization,
    mixed_vacuum_zero, action_mixed_secondDeriv_zero, joint_coercivity⟩

end GeneratedFoundations.Arithmetic.HistoryHaarCoupledAction

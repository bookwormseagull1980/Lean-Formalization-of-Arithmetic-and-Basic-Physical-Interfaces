module

public import GeneratedFoundations.Arithmetic.HistoryChargedReconstruction
public import GeneratedFoundations.Arithmetic.HistoryChargeContent
public import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Quadratic charge response on the complete arithmetic source

The generator is the previously derived joint integer character on every
history and phase coefficient. Its squared response is its adjoint square,
so positivity and the neutral kernel are proved on the original carrier.
The right restriction keeps both original right source coordinates and all
history multiplicities. No physical colour coefficient or neutral line is
inserted into this construction.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryJointQuadraticResponse

open HistoryJointCharge HistoryJointChargeLattice
open HistoryPhaseProjection (projection residual)

theorem component_symmetric (n : ℕ) (r b : ℤ) (s : Spin) (x y : Fibre n) :
    inner ℂ (component n r b s x) y = inner ℂ x (component n r b s y) := by
  have hp : inner ℂ (projection n x) y = inner ℂ x (projection n y) := by
    simpa only [HistoryPhaseProjection.projection_adjoint] using
      LinearMap.adjoint_inner_left (projection n) y x
  have hr : inner ℂ (residual n x) y = inner ℂ x (residual n y) := by
    simpa only [HistoryChargedReconstruction.residual_adjoint] using
      LinearMap.adjoint_inner_left (residual n) y x
  change inner ℂ ((weight n r b (false, s) : ℂ) • projection n x +
      (weight n r b (true, s) : ℂ) • residual n x) y =
    inner ℂ x ((weight n r b (false, s) : ℂ) • projection n y +
      (weight n r b (true, s) : ℂ) • residual n y)
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    map_intCast, hp, hr]

theorem response_symmetric (n : ℕ) (r b : ℤ) (x y : Space n) :
    inner ℂ (response n r b x) y = inner ℂ x (response n r b y) := by
  change (∑ s : Spin, inner ℂ (response n r b x s) (y s)) =
    ∑ s : Spin, inner ℂ (x s) (response n r b y s)
  apply Finset.sum_congr rfl
  intro s _
  simpa only [response, blocks_apply] using component_symmetric n r b s (x s) (y s)

theorem response_adjoint (n : ℕ) (r b : ℤ) : (response n r b).adjoint = response n r b := by
  symm
  exact (LinearMap.eq_adjoint_iff _ _).mpr (response_symmetric n r b)

theorem generatedResponse_adjoint (n : ℕ) :
    (generatedResponse n).adjoint = generatedResponse n := response_adjoint n n 1

theorem normalizedResponse_adjoint (n : ℕ) :
    (HistoryChargeContent.normalizedResponse n).adjoint =
      HistoryChargeContent.normalizedResponse n := by
  unfold HistoryChargeContent.normalizedResponse
  rw [map_smulₛₗ, generatedResponse_adjoint]
  simp only [map_inv₀, map_mul, map_natCast, map_ofNat]

def squaredResponse (n : ℕ) : Module.End ℂ (Space n) :=
  (generatedResponse n).adjoint * generatedResponse n

theorem squaredResponse_eq (n : ℕ) :
    squaredResponse n = generatedResponse n * generatedResponse n := by
  rw [squaredResponse, generatedResponse_adjoint]

theorem squaredResponse_positive (n : ℕ) : (squaredResponse n).IsPositive :=
  LinearMap.isPositive_adjoint_comp_self (generatedResponse n)

theorem squaredResponse_adjoint (n : ℕ) :
    (squaredResponse n).adjoint = squaredResponse n :=
  (squaredResponse_positive n).adjoint_eq

theorem quadratic_eq (n : ℕ) (x : Space n) :
    (inner ℂ x (squaredResponse n x)).re = ‖generatedResponse n x‖ ^ 2 := by
  change (inner ℂ x ((generatedResponse n).adjoint (generatedResponse n x))).re = _
  rw [LinearMap.adjoint_inner_right]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) (generatedResponse n x)

theorem quadratic_components (n : ℕ) (x : Space n) :
    (inner ℂ x (squaredResponse n x)).re = ∑ s : Spin,
      ((generatedWeight n (false, s) : ℝ) ^ 2 * ‖projection n (x s)‖ ^ 2 +
        (generatedWeight n (true, s) : ℝ) ^ 2 * ‖residual n (x s)‖ ^ 2) := by
  rw [quadratic_eq]
  exact response_energy n n 1 x

theorem squaredResponse_zero_iff (n : ℕ) (x : Space n) :
    squaredResponse n x = 0 ↔ generatedResponse n x = 0 := by
  constructor
  · intro hx
    have h : ‖generatedResponse n x‖ ^ 2 = 0 := by
      rw [← quadratic_eq, hx, inner_zero_right]
      rfl
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp h)
  · intro hx
    simp [squaredResponse, Module.End.mul_apply, hx]

theorem squaredResponse_kernel (n : ℕ) : LinearMap.ker (squaredResponse n) = neutral n := by
  ext x
  exact squaredResponse_zero_iff n x

theorem squaredResponse_trace (n : ℕ) :
    LinearMap.trace ℂ (Space n) (squaredResponse n) =
      2 * (Fintype.card (CompleteHistory.History (n + 1)) : ℂ) * n * (n + 1) * (n + 2) := by
  rw [squaredResponse_eq]
  exact HistoryJointChargeQuotient.response_sq_trace n

theorem squaredResponse_retained (n : ℕ) (x : Space n) :
    squaredResponse n
      (HistoryChargedReconstruction.quotientRetained n ((neutral n).mkQ x) : Space n) =
    squaredResponse n x := by
  simp only [squaredResponse, Module.End.mul_apply,
    HistoryChargedReconstruction.response_retained]

abbrev RightSpace (n : ℕ) := PiLp 2 (fun _ : Fin 2 => Fibre n)

def rightInclusion (n : ℕ) : RightSpace n →ₗ[ℂ] Space n where
  toFun x := WithLp.toLp 2 (Sum.elim (fun _ => 0) (fun i => x i))
  map_add' x y := by
    apply PiLp.ext
    intro s
    cases s <;> simp
  map_smul' c x := by
    apply PiLp.ext
    intro s
    cases s <;> simp

@[simp] theorem rightInclusion_left (n : ℕ) (x : RightSpace n) (i : Fin 2) :
    rightInclusion n x (.inl i) = 0 := rfl

@[simp] theorem rightInclusion_right (n : ℕ) (x : RightSpace n) (i : Fin 2) :
    rightInclusion n x (.inr i) = x i := rfl

theorem rightInclusion_injective (n : ℕ) : Function.Injective (rightInclusion n) := by
  intro x y h
  apply PiLp.ext
  intro i
  exact congrArg (fun z : Space n => z (.inr i)) h

theorem rightInclusion_inner (n : ℕ) (x y : RightSpace n) :
    inner ℂ (rightInclusion n x) (rightInclusion n y) = inner ℂ x y := by
  change (∑ s : Spin, inner ℂ (rightInclusion n x s) (rightInclusion n y s)) = _
  simp only [Fintype.sum_sum_type, rightInclusion_left, rightInclusion_right,
    inner_zero_left, Finset.sum_const_zero, zero_add]
  rfl

def rightCharge (n : ℕ) : Module.End ℂ (RightSpace n) where
  toFun x := WithLp.toLp 2 fun i => component n n 1 (.inr i) (x i)
  map_add' x y := by
    apply PiLp.ext
    intro i
    exact map_add _ _ _
  map_smul' c x := by
    apply PiLp.ext
    intro i
    change component n n 1 (.inr i) (c • x i) = c • component n n 1 (.inr i) (x i)
    exact map_smul (component n n 1 (.inr i)) c (x i)

theorem generatedResponse_right (n : ℕ) (x : RightSpace n) :
    generatedResponse n (rightInclusion n x) = rightInclusion n (rightCharge n x) := by
  apply PiLp.ext
  intro s
  cases s <;>
    simp [generatedResponse, response, blocks_apply, rightCharge]

theorem rightCharge_symmetric (n : ℕ) (x y : RightSpace n) :
    inner ℂ (rightCharge n x) y = inner ℂ x (rightCharge n y) := by
  change (∑ i : Fin 2, inner ℂ (component n n 1 (.inr i) (x i)) (y i)) =
    ∑ i : Fin 2, inner ℂ (x i) (component n n 1 (.inr i) (y i))
  exact Finset.sum_congr rfl (fun i _ => component_symmetric n n 1 (.inr i) (x i) (y i))

theorem rightCharge_adjoint (n : ℕ) : (rightCharge n).adjoint = rightCharge n := by
  symm
  exact (LinearMap.eq_adjoint_iff _ _).mpr (rightCharge_symmetric n)

def rightSquaredResponse (n : ℕ) : Module.End ℂ (RightSpace n) :=
  (rightCharge n).adjoint * rightCharge n

theorem rightSquaredResponse_positive (n : ℕ) : (rightSquaredResponse n).IsPositive :=
  LinearMap.isPositive_adjoint_comp_self (rightCharge n)

theorem rightSquaredResponse_adjoint (n : ℕ) :
    (rightSquaredResponse n).adjoint = rightSquaredResponse n :=
  (rightSquaredResponse_positive n).adjoint_eq

theorem squaredResponse_right (n : ℕ) (x : RightSpace n) :
    squaredResponse n (rightInclusion n x) =
      rightInclusion n (rightSquaredResponse n x) := by
  rw [squaredResponse_eq]
  change generatedResponse n (generatedResponse n (rightInclusion n x)) = _
  rw [generatedResponse_right, generatedResponse_right]
  rw [rightSquaredResponse, rightCharge_adjoint]
  rfl

theorem rightSquaredResponse_kernel (n : ℕ) :
    LinearMap.ker (rightSquaredResponse n) = LinearMap.ker (rightCharge n) := by
  ext x
  change rightSquaredResponse n x = 0 ↔ rightCharge n x = 0
  have hi := rightInclusion_injective n
  constructor
  · intro hx
    apply hi
    rw [map_zero, ← generatedResponse_right]
    apply (squaredResponse_zero_iff n _).mp
    rw [squaredResponse_right, hx, map_zero]
  · intro hx
    simp [rightSquaredResponse, Module.End.mul_apply, hx]

theorem rightNeutral_iff (n : ℕ) (x : RightSpace n) :
    x ∈ LinearMap.ker (rightCharge n) ↔ rightInclusion n x ∈ neutral n := by
  change rightCharge n x = 0 ↔ generatedResponse n (rightInclusion n x) = 0
  rw [generatedResponse_right]
  exact (map_eq_zero_iff _ (rightInclusion_injective n)).symm

structure Conclusions : Prop where
  charge_self_adjoint : ∀ n, (generatedResponse n).adjoint = generatedResponse n
  positive_response : ∀ n, (squaredResponse n).IsPositive
  exact_quadratic : ∀ n x,
    (inner ℂ x (squaredResponse n x)).re = ‖generatedResponse n x‖ ^ 2
  complete_kernel : ∀ n, LinearMap.ker (squaredResponse n) = neutral n
  retained_response : ∀ n x,
    squaredResponse n
      (HistoryChargedReconstruction.quotientRetained n ((neutral n).mkQ x) : Space n) =
    squaredResponse n x
  right_intertwining : ∀ n x, squaredResponse n (rightInclusion n x) =
    rightInclusion n (rightSquaredResponse n x)
  right_positive : ∀ n, (rightSquaredResponse n).IsPositive
  complete_right_kernel : ∀ n,
    LinearMap.ker (rightSquaredResponse n) = LinearMap.ker (rightCharge n)

theorem generated : Conclusions where
  charge_self_adjoint := generatedResponse_adjoint
  positive_response := squaredResponse_positive
  exact_quadratic := quadratic_eq
  complete_kernel := squaredResponse_kernel
  retained_response := squaredResponse_retained
  right_intertwining := squaredResponse_right
  right_positive := rightSquaredResponse_positive
  complete_right_kernel := rightSquaredResponse_kernel

end GeneratedFoundations.Arithmetic.HistoryJointQuadraticResponse

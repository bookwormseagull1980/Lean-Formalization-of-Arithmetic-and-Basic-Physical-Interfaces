module

public import GeneratedFoundations.Arithmetic.HistoryPhaseAction
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.Trace

/-!
# The orthogonal phase average on actual complex history coefficients

The complete generated fibre carries its already constructed finite phase
translations. Averaging those very translations agrees with averaging the
phase coordinate at each retained history. This identifies the algebraic
quotient with a self-adjoint Hilbert projection, including its complementary
subspace and both traces. No neutral subspace or projection is supplied.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryPhaseProjection

open CompleteHistory HistoryModuleRepresentation

abbrev HistorySpace (n : ℕ) := History (n + 1) → ℂ

def lift (n : ℕ) : HistorySpace n →ₗ[ℂ] Space n where
  toFun f := WithLp.toLp 2 fun x => f x.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def average (n : ℕ) : Space n →ₗ[ℂ] HistorySpace n where
  toFun f h := (∑ a : ZMod (n + 1), f (h, a)) / (n + 1 : ℂ)
  map_add' f g := by ext h; simp [Finset.sum_add_distrib, add_div]
  map_smul' c f := by
    ext h
    simp only [Pi.smul_apply, PiLp.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum, mul_div_assoc]
    rfl

theorem average_lift (n : ℕ) : (average n).comp (lift n) = 1 := by
  ext f h
  change (∑ _a : ZMod (n + 1), f h) / (n + 1 : ℂ) = f h
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  simp [hn, mul_div_cancel_left₀]

def projection (n : ℕ) : Module.End ℂ (Space n) := (lift n).comp (average n)

def residual (n : ℕ) : Module.End ℂ (Space n) := 1 - projection n

@[simp] theorem projection_apply (n : ℕ) (f : Space n) (h : History (n + 1))
    (a : ZMod (n + 1)) :
    projection n f (h, a) = (∑ b : ZMod (n + 1), f (h, b)) / (n + 1 : ℂ) := rfl

theorem projection_idempotent (n : ℕ) : projection n * projection n = projection n := by
  change (lift n).comp (((average n).comp (lift n)).comp (average n)) = _
  rw [average_lift]
  rfl

def projectionMatrix (n : ℕ) : Algebra n :=
  by classical exact fun i j => if i.1 = j.1 then (n + 1 : ℂ)⁻¹ else 0

theorem projection_matrix (n : ℕ) :
    representation n (projectionMatrix n) = projection n := by
  classical
  ext f ⟨h, a⟩
  simp only [representation_apply, projectionMatrix, Fintype.sum_prod_type,
    ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← Finset.mul_sum]
  change (n + 1 : ℂ)⁻¹ * ∑ b, f (h, b) = (∑ b, f (h, b)) / (n + 1 : ℂ)
  simp only [div_eq_mul_inv, mul_comm]

theorem projectionMatrix_adjoint (n : ℕ) :
    (projectionMatrix n).conjTranspose = projectionMatrix n := by
  classical
  ext i j
  by_cases hij : i.1 = j.1
  · simp only [projectionMatrix, Matrix.conjTranspose_apply, ite_eq_left hij,
      ite_eq_left hij.symm]
    simp only [star_inv₀, star_add, star_natCast, star_one]
  · simp [projectionMatrix, Matrix.conjTranspose_apply, hij, Ne.symm hij]

theorem projection_adjoint (n : ℕ) : (projection n).adjoint = projection n := by
  symm
  apply (LinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  rw [← projection_matrix]
  have h := representation_starCompatible n (projectionMatrix n) x y
  simpa only [projectionMatrix_adjoint] using h

theorem projection_translation (n : ℕ) (q : ZMod (n + 1)) (f : Space n) :
    projection n (HistoryPhaseAction.unitary n q f) = projection n f := by
  ext ⟨h, a⟩
  simp only [projection_apply, HistoryPhaseAction.unitary_apply]
  apply congrArg (fun z : ℂ => z / (n + 1 : ℂ))
  exact Fintype.sum_equiv (Equiv.subRight q)
    (fun b => f (h, b - q)) (fun b => f (h, b)) (fun _ => rfl)

theorem translation_projection (n : ℕ) (q : ZMod (n + 1)) (f : Space n) :
    HistoryPhaseAction.unitary n q (projection n f) = projection n f := by
  ext ⟨h, a⟩
  rfl

/-- This is the average of the actual faithful finite phase action. -/
theorem group_average (n : ℕ) (f : Space n) :
    (n + 1 : ℂ)⁻¹ • ∑ q : ZMod (n + 1), HistoryPhaseAction.unitary n q f =
      projection n f := by
  ext ⟨h, a⟩
  simp only [PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply, smul_eq_mul,
    HistoryPhaseAction.unitary_apply, projection_apply, div_eq_mul_inv]
  rw [mul_comm]
  congr 1
  exact Fintype.sum_equiv (Equiv.subLeft a)
    (fun q => f (h, a - q)) (fun q => f (h, q)) (fun _ => rfl)

theorem projection_fixed_iff (n : ℕ) (f : Space n) :
    projection n f = f ↔ ∀ q : ZMod (n + 1), HistoryPhaseAction.unitary n q f = f := by
  constructor
  · intro hf q
    rw [← hf, translation_projection]
  · intro hf
    rw [← group_average, funext hf]
    have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    rw [Finset.sum_const, Finset.card_univ, ZMod.card, ← Nat.cast_smul_eq_nsmul ℂ,
      smul_smul]
    simp [hn]

theorem projection_residual (n : ℕ) : projection n * residual n = 0 := by
  rw [residual, mul_sub, mul_one, projection_idempotent, sub_self]

theorem residual_projection (n : ℕ) : residual n * projection n = 0 := by
  rw [residual, sub_mul, one_mul, projection_idempotent, sub_self]

theorem residual_idempotent (n : ℕ) : residual n * residual n = residual n := by
  rw [residual, mul_sub, mul_one, sub_mul, one_mul, projection_idempotent, sub_self,
    sub_zero]

theorem full_reconstruction (n : ℕ) (f : Space n) :
    projection n f + residual n f = f := by
  simp [residual]

theorem projection_residual_inner (n : ℕ) (x y : Space n) :
    inner ℂ (projection n x) (residual n y) = 0 := by
  have h := (LinearMap.eq_adjoint_iff _ _).mp (projection_adjoint n).symm x (residual n y)
  rw [h]
  have hz := LinearMap.congr_fun (projection_residual n) y
  change projection n (residual n y) = 0 at hz
  rw [hz, inner_zero_right]

theorem norm_decomposition (n : ℕ) (x : Space n) :
    ‖x‖ ^ 2 = ‖projection n x‖ ^ 2 + ‖residual n x‖ ^ 2 := by
  have h := norm_add_sq (𝕜 := ℂ) (projection n x) (residual n x)
  rw [full_reconstruction, projection_residual_inner] at h
  simpa using h

theorem projection_trace (n : ℕ) :
    LinearMap.trace ℂ (Space n) (projection n) =
      (Fintype.card (History (n + 1)) : ℂ) := by
  rw [projection, LinearMap.trace_comp_comm', average_lift, LinearMap.trace_one]
  simp [HistorySpace, Module.finrank_fintype_fun_eq_card]

theorem residual_trace (n : ℕ) :
    LinearMap.trace ℂ (Space n) (residual n) =
      (Fintype.card (History (n + 1)) : ℂ) * n := by
  rw [residual, map_sub, LinearMap.trace_one, projection_trace, actual_dimension]
  push_cast
  ring

structure Conclusions : Prop where
  actual_average : ∀ n (f : Space n),
    (n + 1 : ℂ)⁻¹ • ∑ q : ZMod (n + 1), HistoryPhaseAction.unitary n q f = projection n f
  self_adjoint : ∀ n, (projection n).adjoint = projection n
  actual_invariants : ∀ n (f : Space n), projection n f = f ↔
    ∀ q : ZMod (n + 1), HistoryPhaseAction.unitary n q f = f
  exact_energy : ∀ n (f : Space n),
    ‖f‖ ^ 2 = ‖projection n f‖ ^ 2 + ‖residual n f‖ ^ 2
  invariant_trace : ∀ n, LinearMap.trace ℂ (Space n) (projection n) =
    (Fintype.card (History (n + 1)) : ℂ)
  detail_trace : ∀ n, LinearMap.trace ℂ (Space n) (residual n) =
    (Fintype.card (History (n + 1)) : ℂ) * n

theorem generated : Conclusions where
  actual_average := group_average
  self_adjoint := projection_adjoint
  actual_invariants := projection_fixed_iff
  exact_energy := norm_decomposition
  invariant_trace := projection_trace
  detail_trace := residual_trace

end GeneratedFoundations.Arithmetic.HistoryPhaseProjection

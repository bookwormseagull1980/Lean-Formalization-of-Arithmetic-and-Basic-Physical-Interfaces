module

public import GeneratedFoundations.Arithmetic.HistoryHaarJointCore

/-!
# Quadratic equation on the full joint Haar operator domain

The quadratic functional is the vacuum Hessian of the previously constructed
nonlinear connection--state action. Its equation is the actual closed
differential operator, with precisely its previously proved domain. No
finite spectral cutoff or independent multiplier is substituted for it.

Polarization, first variation and the unique stationary state are proved
on this domain. The coercivity constant is the derived joint spectral
edge. These statements concern the quadratic vacuum response; they do not
identify its stationary equation with the full nonlinear field equation.
-/

@[expose] public section

noncomputable section

open scoped LinearPMap ComplexConjugate

namespace GeneratedFoundations.Arithmetic.HistoryHaarJointEquation

open HistoryHaarJointHessian

abbrev Domain (N : ℕ) := (operator N).domain

def equation (N : ℕ) : Domain N →ₗ[ℂ] Space N := (operator N).toFun

def action (N : ℕ) (x : Domain N) : ℝ :=
  (inner ℂ (x : Space N) (equation N x)).re / 2

def firstVariation (N : ℕ) (x y : Domain N) : ℝ :=
  (inner ℂ (y : Space N) (equation N x)).re

theorem equation_symmetric (N : ℕ) (x y : Domain N) :
    inner ℂ (equation N x) (y : Space N) =
      inner ℂ (x : Space N) (equation N y) := by
  have h := LinearPMap.adjoint_isFormalAdjoint (operator_selfAdjoint N).dense_domain
  rw [LinearPMap.isSelfAdjoint_def.mp (operator_selfAdjoint N)] at h
  exact h x y

theorem firstVariation_symm (N : ℕ) (x y : Domain N) :
    firstVariation N x y = firstVariation N y x := by
  unfold firstVariation
  rw [← equation_symmetric N x y, ← inner_conj_symm (y : Space N) (equation N x)]
  rfl

theorem firstVariation_self (N : ℕ) (x : Domain N) :
    firstVariation N x x = 2 * action N x := by
  unfold firstVariation action
  ring

theorem action_line (N : ℕ) (x y : Domain N) (t : ℝ) :
    action N (x + (t : ℂ) • y) =
      action N x + t * firstVariation N x y + t ^ 2 * action N y := by
  have hs := firstVariation_symm N x y
  unfold firstVariation at hs
  simp only [action, firstVariation, map_add, map_smul,
    Submodule.coe_add, Submodule.coe_smul, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, Complex.conj_ofReal,
    Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at *
  rw [hs]
  ring

theorem action_hasDerivAt (N : ℕ) (x y : Domain N) (t : ℝ) :
    HasDerivAt (fun s : ℝ => action N (x + (s : ℂ) • y))
      (firstVariation N x y + 2 * t * action N y) t := by
  convert Geometry.HilbertTraceVariation.quartic_hasDerivAt
    (action N x) (firstVariation N x y) (action N y) 0 0 t using 1
  · funext s
    rw [action_line]
    ring
  · ring

theorem action_add (N : ℕ) (x y : Domain N) :
    action N (x + y) = action N x + firstVariation N x y + action N y := by
  simpa using action_line N x y 1

theorem action_coercive (N : ℕ) (x : Domain N) :
    gapSq N / 2 * ‖(x : Space N)‖ ^ 2 ≤ action N x := by
  have h := sharp_coercivity N x
  change gapSq N * ‖(x : Space N)‖ ^ 2 ≤
    (inner ℂ (x : Space N) (equation N x)).re at h
  unfold action
  linarith

theorem action_uniform_coercive (N : ℕ) (x : Domain N) :
    (15 / 16 : ℝ) * ‖(x : Space N)‖ ^ 2 ≤ action N x := by
  have h := complete_coercivity N x
  change (15 / 8 : ℝ) * ‖(x : Space N)‖ ^ 2 ≤
    (inner ℂ (x : Space N) (equation N x)).re at h
  unfold action
  linarith

theorem action_nonneg (N : ℕ) (x : Domain N) : 0 ≤ action N x :=
  (mul_nonneg (by norm_num : (0 : ℝ) ≤ 15 / 16) (sq_nonneg _)).trans
    (action_uniform_coercive N x)

theorem action_eq_zero_iff (N : ℕ) (x : Domain N) : action N x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    have h := action_uniform_coercive N x
    rw [hx] at h
    have hn : ‖(x : Space N)‖ = 0 := by nlinarith [sq_nonneg ‖(x : Space N)‖]
    exact Subtype.ext (norm_eq_zero.mp hn)
  · rintro rfl
    simp [action]

theorem equation_eq_zero_iff (N : ℕ) (x : Domain N) : equation N x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    apply (action_eq_zero_iff N x).mp
    simp [action, hx]
  · rintro rfl
    exact map_zero _

theorem stationary_iff_zero (N : ℕ) (x : Domain N) :
    (∀ y : Domain N, firstVariation N x y = 0) ↔ x = 0 := by
  constructor
  · intro hx
    apply (action_eq_zero_iff N x).mp
    have h := hx x
    rw [firstVariation_self] at h
    linarith
  · rintro rfl y
    simp [firstVariation]

theorem firstVariation_coercive (N : ℕ) (x : Domain N) :
    gapSq N * ‖(x : Space N)‖ ^ 2 ≤ firstVariation N x x := sharp_coercivity N x

theorem firstVariation_self_pos (N : ℕ) (x : Domain N) (hx : x ≠ 0) :
    0 < firstVariation N x x := by
  have hp : (0 : ℝ) < gapSq N := (by norm_num : (0 : ℝ) < 15 / 8).trans_le
    (gapSq_lower N)
  have hn : (x : Space N) ≠ 0 := fun h => hx (Subtype.ext h)
  exact (mul_pos hp (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hn))).trans_le
    (firstVariation_coercive N x)

theorem action_on_core (N : ℕ) (x : HistoryHaarJointCore.ResponseCore N) :
    action N ⟨x.val,
      (Operations.FiniteEigenbasisCore.le_closure (basis N) (eigenvalue N)).1 x.property⟩ =
      HistoryHaarCoupledAction.quadratic N
        (HistoryHaarClosedHessian.coefficients N (HistoryHaarJointCore.coreField N x))
        (HistoryHaarJointCore.stateProjection N x.val) / 2 := by
  have he := (Operations.FiniteEigenbasisCore.le_closure (basis N) (eigenvalue N)).2
    (x := x) (y := ⟨x.val,
      (Operations.FiniteEigenbasisCore.le_closure (basis N) (eigenvalue N)).1 x.property⟩) rfl
  change finiteOperator N x = operator N ⟨x.val,
    (Operations.FiniteEigenbasisCore.le_closure (basis N) (eigenvalue N)).1 x.property⟩ at he
  change (inner ℂ x.val (operator N ⟨x.val,
    (Operations.FiniteEigenbasisCore.le_closure (basis N) (eigenvalue N)).1 x.property⟩)).re / 2 = _
  rw [← he, HistoryHaarJointCore.finiteOperator_energy]

structure Conclusions : Prop where
  domain_equation : ∀ N (x : Domain N), equation N x = operator N x
  actual_first_variation : ∀ N x y t,
    HasDerivAt (fun s : ℝ => action N (x + (s : ℂ) • y))
      (firstVariation N x y + 2 * t * action N y) t
  complete_polarization : ∀ N x y,
    action N (x + y) = action N x + firstVariation N x y + action N y
  unique_stationary_state : ∀ N x,
    (∀ y : Domain N, firstVariation N x y = 0) ↔ x = 0
  nondegenerate_equation : ∀ N x, equation N x = 0 ↔ x = 0
  sharp_bound : ∀ N (x : Domain N), gapSq N / 2 * ‖(x : Space N)‖ ^ 2 ≤ action N x
  uniform_bound : ∀ N (x : Domain N), (15 / 16 : ℝ) * ‖(x : Space N)‖ ^ 2 ≤ action N x

theorem generated : Conclusions where
  domain_equation _ _ := rfl
  actual_first_variation := action_hasDerivAt
  complete_polarization := action_add
  unique_stationary_state := stationary_iff_zero
  nondegenerate_equation := equation_eq_zero_iff
  sharp_bound := action_coercive
  uniform_bound := action_uniform_coercive

end GeneratedFoundations.Arithmetic.HistoryHaarJointEquation

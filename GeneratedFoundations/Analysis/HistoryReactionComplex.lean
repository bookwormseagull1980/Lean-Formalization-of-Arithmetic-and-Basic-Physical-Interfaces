module

public import GeneratedFoundations.Analysis.HistoryReactionKernel

/-!
# The actual finite differential complex of generated histories

Zero-cochains are functions on retained histories; one-cochains are functions
on their actual ordered binary assemblies. The differential has three legs,
with multiplicity retained when the two children agree. Its weighted adjoint
uses precisely the Gaussian detailed-balance conductance of the action.

Each non-leaf history has its own unique assembly. Consequently every
one-cochain has a unique primitive after fixing its unit-leaf value. This is
proved by recursion on the retained history, rather than by treating
associativity or distributivity as additional closed edges. The finite
complex therefore has leaf charge in degree zero and no degree-one residual.
The graded symmetric operator has the actual reaction Hessian as its
degree-zero square. All spaces and sums retain their natural cutoff.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Analysis.HistoryReactionComplex

open Arithmetic.CompleteHistory
open HistoryReactionForm HistoryReactionOperator HistoryReactionKernel

abbrev Zero (N : ℕ) := Species N → ℝ
abbrev One (N : ℕ) := Reaction N → ℝ
abbrev Graded (N : ℕ) := Zero N × One N

def pairZero {N : ℕ} (f g : Zero N) : ℝ := ∑ s, f s * g s

def pairOne (alpha L : ℝ) {N : ℕ} (u v : One N) : ℝ :=
  ∑ e, conductance alpha L e * u e * v e

def adjoint (alpha L : ℝ) {N : ℕ} (u : One N) (s : Species N) : ℝ :=
  ∑ e, conductance alpha L e * u e * incidence e s

theorem adjoint_identity (alpha L : ℝ) {N : ℕ} (f : Zero N) (u : One N) :
    pairZero f (adjoint alpha L u) = pairOne alpha L (differential f) u := by
  classical
  simp only [pairZero, adjoint, Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold pairOne
  apply Finset.sum_congr rfl
  intro e _
  calc
    (∑ s, f s * (conductance alpha L e * u e * incidence e s)) =
        conductance alpha L e * u e * ∑ s, f s * incidence e s := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ = _ := by rw [incidence_sum]; ring

theorem pairZero_symm {N : ℕ} (f g : Zero N) : pairZero f g = pairZero g f := by
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem pairOne_symm (alpha L : ℝ) {N : ℕ} (u v : One N) :
    pairOne alpha L u v = pairOne alpha L v u := by
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem pairOne_zero_iff (alpha L : ℝ) {N : ℕ} (u : One N) :
    pairOne alpha L u u = 0 ↔ u = 0 := by
  constructor
  · intro hz
    funext e
    have he : conductance alpha L e * u e * u e = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun e _ => by
        nlinarith [conductance_pos alpha L e, sq_nonneg (u e)])).mp hz e
        (Finset.mem_univ e)
    exact (mul_eq_zero.mp he).elim
      (fun h => (mul_eq_zero.mp h).resolve_left (ne_of_gt (conductance_pos alpha L e))) id
  · intro hz
    simp [hz, pairOne]

/-- Integrate along the actual expression history. Both children are retained
and the current assembly contributes exactly once. -/
def primitiveValue {N : ℕ} (u : One N) :
    {k : ℕ} → (h : History k) → k ≤ N → ℝ
  | _, .one, _ => 0
  | k, .node c hl hr, hk =>
      primitiveValue u hl (Nat.le_trans (Nat.le_of_lt c.left_lt) hk) +
      primitiveValue u hr (Nat.le_trans (Nat.le_of_lt c.right_lt) hk) +
      u ⟨⟨k, Nat.lt_succ_of_le hk⟩, c, hl, hr⟩

def primitive {N : ℕ} (u : One N) (s : Species N) : ℝ :=
  primitiveValue u s.2 (Nat.le_of_lt_succ s.1.isLt)

@[simp] theorem primitive_unit {N : ℕ} (hN : 1 ≤ N) (u : One N) :
    primitive u (unit hN) = 0 := rfl

theorem differential_primitive {N : ℕ} (u : One N) : differential (primitive u) = u := by
  funext e
  rcases e with ⟨⟨k, hk⟩, c, hl, hr⟩
  simp only [differential, primitive, parent, left, right, primitiveValue]
  ring

theorem differential_surjective (N : ℕ) :
    Function.Surjective (differential (N := N)) := fun u => ⟨primitive u, differential_primitive u⟩

theorem unique_primitive {N : ℕ} (hN : 1 ≤ N) (u : One N) :
    ∃! f : Zero N, f (unit hN) = 0 ∧ differential f = u := by
  refine ⟨primitive u, ⟨primitive_unit hN u, differential_primitive u⟩, ?_⟩
  intro f hf
  have hclosed : ∀ e : Reaction N,
      (f - primitive u) (parent e) = (f - primitive u) (left e) +
        (f - primitive u) (right e) := by
    intro e
    have h1 := congrFun hf.2 e
    have h2 := congrFun (differential_primitive u) e
    simp only [differential] at h1 h2
    simp only [Pi.sub_apply]
    linarith
  have he := (closed_iff_leaf hN (f - primitive u)).mp hclosed
  funext s
  have hs := congrFun he s
  simp only [Pi.sub_apply, hf.1, primitive_unit, sub_self, mul_zero] at hs
  exact sub_eq_zero.mp hs

/-- The anchored chain decomposition uses the actual unit-leaf value.
The orthogonal decomposition is constructed in `HistoryReactionHodge`. -/
theorem zero_decomposition {N : ℕ} (hN : 1 ≤ N) (f : Zero N) :
    f = fun s => equilibrium (f (unit hN)) s + primitive (differential f) s := by
  have hprim : differential (fun s => f s - equilibrium (f (unit hN)) s) =
      differential f := by
    funext e
    have he := leafCharge_closed e
    have heq : leafCharge (parent e) = leafCharge (left e) + leafCharge (right e) := by
      dsimp [differential] at he
      linarith
    dsimp [differential, equilibrium]
    rw [heq]
    ring
  have hp := (unique_primitive hN (differential f)).unique
    ⟨by simp, hprim⟩ ⟨primitive_unit hN _, differential_primitive _⟩
  funext s
  have hs := congrFun hp s
  linarith

theorem adjoint_injective (alpha L : ℝ) (N : ℕ) :
    Function.Injective (adjoint alpha L (N := N)) := by
  intro u v huv
  have hz : adjoint alpha L (u - v) = 0 := by
    funext s
    simp only [adjoint, Pi.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr (congrFun huv s)
  have hp := adjoint_identity alpha L (primitive (u - v)) (u - v)
  rw [hz, differential_primitive] at hp
  have hzero : u - v = 0 := (pairOne_zero_iff alpha L _).mp (by simpa [pairZero] using hp.symm)
  exact sub_eq_zero.mp hzero

def dirac (alpha L : ℝ) {N : ℕ} (x : Graded N) : Graded N :=
  (adjoint alpha L x.2, differential x.1)

def grading {N : ℕ} (x : Graded N) : Graded N := (x.1, -x.2)

def pairGraded (alpha L : ℝ) {N : ℕ} (x y : Graded N) : ℝ :=
  pairZero x.1 y.1 + pairOne alpha L x.2 y.2

theorem dirac_symmetric (alpha L : ℝ) {N : ℕ} (x y : Graded N) :
    pairGraded alpha L x (dirac alpha L y) =
      pairGraded alpha L (dirac alpha L x) y := by
  change pairZero x.1 (adjoint alpha L y.2) + pairOne alpha L x.2 (differential y.1) =
    pairZero (adjoint alpha L x.2) y.1 + pairOne alpha L (differential x.1) y.2
  rw [adjoint_identity, pairZero_symm (adjoint alpha L x.2), adjoint_identity,
    pairOne_symm alpha L x.2]
  ring

theorem dirac_square (alpha L : ℝ) {N : ℕ} (x : Graded N) :
    dirac alpha L (dirac alpha L x) =
      (operator alpha L x.1, differential (adjoint alpha L x.2)) := rfl

theorem grading_involution {N : ℕ} (x : Graded N) : grading (grading x) = x := by
  simp [grading]

theorem dirac_odd (alpha L : ℝ) {N : ℕ} (x : Graded N) :
    dirac alpha L (grading x) = -grading (dirac alpha L x) := by
  apply Prod.ext
  · funext s
    simp [dirac, grading, adjoint]
  · funext e
    simp [dirac, grading]

structure Conclusions : Prop where
  actual_adjoint : ∀ (alpha L : ℝ) {N : ℕ} (f : Zero N) (u : One N),
    pairZero f (adjoint alpha L u) = pairOne alpha L (differential f) u
  complete_primitives : ∀ {N : ℕ} (hN : 1 ≤ N) (u : One N),
    ∃! f : Zero N, f (unit hN) = 0 ∧ differential f = u
  decomposition : ∀ {N : ℕ} (hN : 1 ≤ N) (f : Zero N),
    f = fun s => equilibrium (f (unit hN)) s + primitive (differential f) s
  full_square : ∀ (alpha L : ℝ) {N : ℕ} (x : Graded N),
    dirac alpha L (dirac alpha L x) =
      (operator alpha L x.1, differential (adjoint alpha L x.2))
  symmetry : ∀ (alpha L : ℝ) {N : ℕ} (x y : Graded N),
    pairGraded alpha L x (dirac alpha L y) = pairGraded alpha L (dirac alpha L x) y

theorem generated : Conclusions where
  actual_adjoint := adjoint_identity
  complete_primitives := unique_primitive
  decomposition := zero_decomposition
  full_square := dirac_square
  symmetry := dirac_symmetric

end GeneratedFoundations.Analysis.HistoryReactionComplex

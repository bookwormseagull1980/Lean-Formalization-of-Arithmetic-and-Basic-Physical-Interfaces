module

public import GeneratedFoundations.Arithmetic.HistoryObservation
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# The common quadratic response of all generated reaction channels

Species are actual histories below a finite natural cutoff; reactions are
actual ordered channels together with both child histories.  The coefficient
of a reaction is its parent intensity, equivalently the product of its child
intensities and the previously derived merge rate.  Thus addition,
multiplication and all history multiplicities enter the same form before any
bound is taken.

The differential is the reaction incidence `parent - left - right`, not an
invented edge between a parent and a single child.  Squaring it keeps the
three pairwise mixed terms.  Its nullspace is characterized by the exact
channel relations, and scalar line variations identify this form with the
actual second variation of the quadratic action.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Analysis.HistoryReactionForm

open Arithmetic.CompleteHistory Arithmetic.CompleteHistoryDynamics

abbrev Species (N : ℕ) := Σ k : Fin (N + 1), History k.val

abbrev Reaction (N : ℕ) :=
  Σ k : Fin (N + 1), Σ c : Channel k.val, History c.left.val × History c.right.val

def parent {N : ℕ} (e : Reaction N) : Species N := ⟨e.1, .node e.2.1 e.2.2.1 e.2.2.2⟩

def left {N : ℕ} (e : Reaction N) : Species N :=
  ⟨⟨e.2.1.left.val, e.2.1.left_lt.trans e.1.isLt⟩, e.2.2.1⟩

def right {N : ℕ} (e : Reaction N) : Species N :=
  ⟨⟨e.2.1.right.val, e.2.1.right_lt.trans e.1.isLt⟩, e.2.2.2⟩

def conductance (alpha L : ℝ) {N : ℕ} (e : Reaction N) : ℝ :=
  flatGaussianIntensity alpha L (parent e).2

theorem conductance_pos (alpha L : ℝ) {N : ℕ} (e : Reaction N) :
    0 < conductance alpha L e :=
  HistoryTiltedBalance.flatGaussianIntensity_pos _ _ _

theorem conductance_from_children (alpha L : ℝ) {N : ℕ} (e : Reaction N) :
    conductance alpha L e =
      flatGaussianIntensity alpha L (left e).2 *
        flatGaussianIntensity alpha L (right e).2 * mergeRate alpha L e.2.1 :=
  (edge_detailed_balance alpha L e.2.1 e.2.2.1 e.2.2.2).symm

def differential {N : ℕ} (f : Species N → ℝ) (e : Reaction N) : ℝ :=
  f (parent e) - f (left e) - f (right e)

def form (alpha L : ℝ) {N : ℕ} (f g : Species N → ℝ) : ℝ :=
  ∑ e, conductance alpha L e * differential f e * differential g e

def action (alpha L : ℝ) {N : ℕ} (f : Species N → ℝ) : ℝ := form alpha L f f / 2

theorem differential_add {N : ℕ} (f g : Species N → ℝ) (e : Reaction N) :
    differential (fun x => f x + g x) e = differential f e + differential g e := by
  simp only [differential]
  ring

theorem differential_line {N : ℕ} (f v : Species N → ℝ) (t : ℝ) (e : Reaction N) :
    differential (fun x => f x + t * v x) e = differential f e + t * differential v e := by
  simp only [differential]
  ring

theorem form_symm (alpha L : ℝ) {N : ℕ} (f g : Species N → ℝ) :
    form alpha L f g = form alpha L g f := by
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem form_nonneg (alpha L : ℝ) {N : ℕ} (f : Species N → ℝ) :
    0 ≤ form alpha L f f := by
  apply Finset.sum_nonneg
  intro e _
  nlinarith [conductance_pos alpha L e, sq_nonneg (differential f e)]

theorem form_zero_iff (alpha L : ℝ) {N : ℕ} (f : Species N → ℝ) :
    form alpha L f f = 0 ↔ ∀ e, f (parent e) = f (left e) + f (right e) := by
  constructor
  · intro hf e
    have he : conductance alpha L e * differential f e * differential f e = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun e _ => by
        nlinarith [conductance_pos alpha L e, sq_nonneg (differential f e)])).mp hf e
        (Finset.mem_univ e)
    have hc := conductance_pos alpha L e
    have hd : differential f e = 0 :=
      (mul_eq_zero.mp he).elim
        (fun hz => (mul_eq_zero.mp hz).resolve_left (ne_of_gt hc)) id
    dsimp [differential] at hd
    linarith
  · intro hf
    apply Finset.sum_eq_zero
    intro e _
    have hd : differential f e = 0 := by dsimp [differential]; linarith [hf e]
    simp only [hd, mul_zero]

theorem full_mixed_expansion (alpha L : ℝ) {N : ℕ} (f : Species N → ℝ) :
    form alpha L f f = ∑ e : Reaction N, conductance alpha L e *
      (f (parent e) ^ 2 + f (left e) ^ 2 + f (right e) ^ 2 -
        2 * f (parent e) * f (left e) - 2 * f (parent e) * f (right e) +
        2 * f (left e) * f (right e)) := by
  apply Finset.sum_congr rfl
  intro e _
  dsimp [differential]
  ring

theorem action_line (alpha L : ℝ) {N : ℕ} (f v : Species N → ℝ) (t : ℝ) :
    action alpha L (fun x => f x + t * v x) =
      action alpha L f + t * form alpha L f v + t ^ 2 / 2 * form alpha L v v := by
  simp only [action, form, differential_line, Finset.sum_div, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem action_mixed_variation (alpha L : ℝ) {N : ℕ}
    (f u v : Species N → ℝ) :
    action alpha L (fun x => f x + u x + v x) -
      action alpha L (fun x => f x + u x) -
      action alpha L (fun x => f x + v x) + action alpha L f = form alpha L u v := by
  simp only [action, form, differential_add, Finset.sum_div,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem action_line_hasDerivAt (alpha L : ℝ) {N : ℕ}
    (f v : Species N → ℝ) (t : ℝ) :
    HasDerivAt (fun s => action alpha L (fun x => f x + s * v x))
      (form alpha L f v + t * form alpha L v v) t := by
  have hp := ((hasDerivAt_const t (action alpha L f)).add
    ((hasDerivAt_id t).mul_const (form alpha L f v))).add
    ((((hasDerivAt_id t).pow 2).div_const 2).mul_const (form alpha L v v))
  convert hp using 1
  · funext s
    exact action_line alpha L f v s
  · simp only [id_eq]
    ring

theorem action_line_deriv (alpha L : ℝ) {N : ℕ}
    (f v : Species N → ℝ) (t : ℝ) :
    deriv (fun s => action alpha L (fun x => f x + s * v x)) t =
      form alpha L f v + t * form alpha L v v :=
  (action_line_hasDerivAt alpha L f v t).deriv

theorem action_line_second_deriv (alpha L : ℝ) {N : ℕ}
    (f v : Species N → ℝ) (t : ℝ) :
    deriv (fun s => deriv (fun r => action alpha L (fun x => f x + r * v x)) s) t =
      form alpha L v v := by
  have he : (fun s => deriv (fun r => action alpha L (fun x => f x + r * v x)) s) =
      (fun s => form alpha L f v + s * form alpha L v v) := by
    funext s
    exact action_line_deriv alpha L f v s
  rw [he]
  simp

structure Conclusions : Prop where
  true_balance : ∀ (alpha L : ℝ) {N : ℕ} (e : Reaction N),
    conductance alpha L e = flatGaussianIntensity alpha L (left e).2 *
      flatGaussianIntensity alpha L (right e).2 * mergeRate alpha L e.2.1
  positive : ∀ (alpha L : ℝ) {N : ℕ} (f : Species N → ℝ), 0 ≤ form alpha L f f
  exact_kernel : ∀ (alpha L : ℝ) {N : ℕ} (f : Species N → ℝ),
    form alpha L f f = 0 ↔ ∀ e, f (parent e) = f (left e) + f (right e)
  common_variation : ∀ (alpha L : ℝ) {N : ℕ} (f u v : Species N → ℝ),
    action alpha L (fun x => f x + u x + v x) -
      action alpha L (fun x => f x + u x) -
      action alpha L (fun x => f x + v x) + action alpha L f = form alpha L u v

theorem generated : Conclusions where
  true_balance := conductance_from_children
  positive := form_nonneg
  exact_kernel := form_zero_iff
  common_variation := action_mixed_variation

end GeneratedFoundations.Analysis.HistoryReactionForm

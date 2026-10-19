module

public import GeneratedFoundations.Analysis.HistoryReactionForm

/-!
# Incidence, adjoint and Hessian on actual finite history species

This is the operator belonging to `HistoryReactionForm`, rather than a new
diagonal spectral model.  A reaction has three incidences, including the
multiplicity two when its children coincide.  Finite summation gives the
adjoint identity on the whole space and identifies the positive Hessian with
the full reaction form.  The leaf charge is an actual conserved direction.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Analysis.HistoryReactionOperator

open Arithmetic.CompleteHistory Arithmetic.CompleteHistoryGeometry HistoryReactionForm

def incidence {N : ℕ} (e : Reaction N) (s : Species N) : ℝ := by
  classical
  exact (if s = parent e then 1 else 0) - (if s = left e then 1 else 0) -
    (if s = right e then 1 else 0)

theorem incidence_sum {N : ℕ} (f : Species N → ℝ) (e : Reaction N) :
    (∑ s, f s * incidence e s) = differential f e := by
  classical
  simp [incidence, mul_sub, Finset.sum_sub_distrib, differential]

def operator (alpha L : ℝ) {N : ℕ} (f : Species N → ℝ) (s : Species N) : ℝ :=
  ∑ e, conductance alpha L e * differential f e * incidence e s

theorem adjoint_identity (alpha L : ℝ) {N : ℕ} (f g : Species N → ℝ) :
    (∑ s, f s * operator alpha L g s) = form alpha L f g := by
  classical
  simp only [operator, Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold form
  apply Finset.sum_congr rfl
  intro e _
  calc
    (∑ s, f s * (conductance alpha L e * differential g e * incidence e s)) =
        conductance alpha L e * differential g e * ∑ s, f s * incidence e s := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ = _ := by rw [incidence_sum]; ring

theorem symmetric (alpha L : ℝ) {N : ℕ} (f g : Species N → ℝ) :
    (∑ s, f s * operator alpha L g s) = ∑ s, g s * operator alpha L f s := by
  rw [adjoint_identity, adjoint_identity, form_symm]

theorem nonnegative (alpha L : ℝ) {N : ℕ} (f : Species N → ℝ) :
    0 ≤ ∑ s, f s * operator alpha L f s := by
  rw [adjoint_identity]
  exact form_nonneg alpha L f

theorem action_operator (alpha L : ℝ) {N : ℕ} (f : Species N → ℝ) :
    action alpha L f = (∑ s, f s * operator alpha L f s) / 2 := by
  rw [adjoint_identity]
  rfl

theorem mixed_hessian_operator (alpha L : ℝ) {N : ℕ} (f u v : Species N → ℝ) :
    action alpha L (fun x => f x + u x + v x) -
      action alpha L (fun x => f x + u x) -
      action alpha L (fun x => f x + v x) + action alpha L f =
        ∑ s, u s * operator alpha L v s := by
  rw [action_mixed_variation, adjoint_identity]

def leafCharge {N : ℕ} (s : Species N) : ℝ := (leafCount s.2 : ℝ)

theorem leafCharge_closed {N : ℕ} (e : Reaction N) :
    differential leafCharge e = 0 := by
  simp [differential, leafCharge, parent, left, right]

theorem leafCharge_stationary (alpha L : ℝ) (N : ℕ) :
    operator alpha L (leafCharge (N := N)) = 0 := by
  funext s
  simp [operator, leafCharge_closed]

theorem leafCharge_conservation (alpha L : ℝ) {N : ℕ} (f : Species N → ℝ) :
    (∑ s, leafCharge s * (-operator alpha L f s)) = 0 := by
  have h := symmetric alpha L leafCharge f
  rw [leafCharge_stationary] at h
  simpa using h

structure Conclusions : Prop where
  actual_adjoint : ∀ (alpha L : ℝ) {N : ℕ} (f g : Species N → ℝ),
    (∑ s, f s * operator alpha L g s) = form alpha L f g
  full_positive_operator : ∀ (alpha L : ℝ) {N : ℕ} (f : Species N → ℝ),
    0 ≤ ∑ s, f s * operator alpha L f s
  common_hessian : ∀ (alpha L : ℝ) {N : ℕ} (f u v : Species N → ℝ),
    action alpha L (fun x => f x + u x + v x) -
      action alpha L (fun x => f x + u x) -
      action alpha L (fun x => f x + v x) + action alpha L f =
        ∑ s, u s * operator alpha L v s
  conserved_charge : ∀ (alpha L : ℝ) {N : ℕ} (f : Species N → ℝ),
    (∑ s, leafCharge s * (-operator alpha L f s)) = 0

theorem generated : Conclusions where
  actual_adjoint := adjoint_identity
  full_positive_operator := nonnegative
  common_hessian := mixed_hessian_operator
  conserved_charge := leafCharge_conservation

end GeneratedFoundations.Analysis.HistoryReactionOperator

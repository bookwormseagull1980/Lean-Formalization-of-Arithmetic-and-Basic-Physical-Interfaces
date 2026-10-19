module

public import GeneratedFoundations.Analysis.HistoryReactionOperator

/-!
# The complete nullspace of the finite history reaction operator

Every species is an actual retained history and every reaction is its actual
binary assembly.  The channel equations therefore determine a null vector
recursively from its value at the unit leaf.  The resulting conserved
direction is leaf charge, rather than the constant function on species.

Fixing that one value removes the whole kernel and selects a unique
zero-action equilibrium.  The cutoff indexes the finite observation and is
not an additional datum of the generated source.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Analysis.HistoryReactionKernel

open Arithmetic.CompleteHistory Arithmetic.CompleteHistoryGeometry
open HistoryReactionForm HistoryReactionOperator

def unit {N : ℕ} (hN : 1 ≤ N) : Species N := ⟨⟨1, by omega⟩, .one⟩

theorem closed_value {N : ℕ} (hN : 1 ≤ N) (f : Species N → ℝ)
    (hf : ∀ e : Reaction N, f (parent e) = f (left e) + f (right e))
    {k : ℕ} (h : History k) (hk : k ≤ N) :
    f ⟨⟨k, Nat.lt_succ_of_le hk⟩, h⟩ = (leafCount h : ℝ) * f (unit hN) := by
  induction h with
  | one => simp [unit]
  | @node k c hl hr ihl ihr =>
      let e : Reaction N := ⟨⟨k, Nat.lt_succ_of_le hk⟩, c, hl, hr⟩
      have he := hf e
      change f ⟨⟨k, Nat.lt_succ_of_le hk⟩, .node c hl hr⟩ =
        f ⟨⟨c.left.val, _⟩, hl⟩ + f ⟨⟨c.right.val, _⟩, hr⟩ at he
      rw [he, ihl (Nat.le_trans (Nat.le_of_lt c.left_lt) hk),
        ihr (Nat.le_trans (Nat.le_of_lt c.right_lt) hk)]
      simp only [leafCount_node, Nat.cast_add]
      ring

theorem closed_iff_leaf {N : ℕ} (hN : 1 ≤ N) (f : Species N → ℝ) :
    (∀ e : Reaction N, f (parent e) = f (left e) + f (right e)) ↔
      f = fun s => leafCharge s * f (unit hN) := by
  constructor
  · intro hf
    funext s
    exact closed_value hN f hf s.2 (Nat.le_of_lt_succ s.1.isLt)
  · intro hf e
    rw [hf]
    have h := leafCharge_closed e
    dsimp [differential] at h
    have heq : leafCharge (parent e) = leafCharge (left e) + leafCharge (right e) := by
      linarith
    change leafCharge (parent e) * f (unit hN) =
      leafCharge (left e) * f (unit hN) + leafCharge (right e) * f (unit hN)
    rw [heq]
    ring

theorem form_zero_iff_leaf (alpha L : ℝ) {N : ℕ} (hN : 1 ≤ N)
    (f : Species N → ℝ) :
    form alpha L f f = 0 ↔ f = fun s => leafCharge s * f (unit hN) := by
  rw [form_zero_iff, closed_iff_leaf hN]

theorem operator_zero_iff_closed (alpha L : ℝ) {N : ℕ} (f : Species N → ℝ) :
    operator alpha L f = 0 ↔
      ∀ e : Reaction N, f (parent e) = f (left e) + f (right e) := by
  constructor
  · intro hf
    apply (form_zero_iff alpha L f).mp
    rw [← adjoint_identity, hf]
    simp
  · intro hf
    funext s
    apply Finset.sum_eq_zero
    intro e _
    have hd : differential f e = 0 := by
      dsimp [differential]
      linarith [hf e]
    simp only [hd, mul_zero, zero_mul]

theorem operator_zero_iff_leaf (alpha L : ℝ) {N : ℕ} (hN : 1 ≤ N)
    (f : Species N → ℝ) :
    operator alpha L f = 0 ↔ f = fun s => leafCharge s * f (unit hN) := by
  rw [operator_zero_iff_closed, closed_iff_leaf hN]

def equilibrium {N : ℕ} (q : ℝ) : Species N → ℝ := fun s => leafCharge s * q

@[simp] theorem equilibrium_unit {N : ℕ} (hN : 1 ≤ N) (q : ℝ) :
    equilibrium q (unit hN) = q := by
  simp [equilibrium, unit, leafCharge]

theorem equilibrium_zero_action (alpha L : ℝ) (N : ℕ) (q : ℝ) :
    action alpha L (equilibrium (N := N) q) = 0 := by
  unfold action
  have hf : form alpha L (equilibrium (N := N) q) (equilibrium q) = 0 := by
    apply (form_zero_iff alpha L _).mpr
    intro e
    have h := leafCharge_closed e
    dsimp [differential] at h
    dsimp [equilibrium]
    have heq : leafCharge (parent e) = leafCharge (left e) + leafCharge (right e) := by
      linarith
    rw [heq]
    ring
  rw [hf, zero_div]

theorem unique_zero_action (alpha L : ℝ) {N : ℕ} (hN : 1 ≤ N) (q : ℝ)
    (f : Species N → ℝ) (hunit : f (unit hN) = q)
    (haction : action alpha L f = 0) : f = equilibrium q := by
  have hf : form alpha L f f = 0 := by
    unfold action at haction
    linarith
  have h := (form_zero_iff_leaf alpha L hN f).mp hf
  change f = fun s => leafCharge s * q
  rw [hunit] at h
  exact h

/-- Fixing the unit observation removes every zero direction of the full
reaction form, rather than merely a selected diagonal block. -/
theorem positive_on_anchored (alpha L : ℝ) {N : ℕ} (hN : 1 ≤ N)
    (f : Species N → ℝ) (hunit : f (unit hN) = 0) (hf : f ≠ 0) :
    0 < form alpha L f f := by
  apply lt_of_le_of_ne (form_nonneg alpha L f)
  intro hz
  have heq := (form_zero_iff_leaf alpha L hN f).mp hz.symm
  apply hf
  funext s
  have hs := congrFun heq s
  simpa only [hunit, mul_zero, Pi.zero_apply] using hs

theorem equilibrium_unique_stationary (alpha L : ℝ) {N : ℕ} (hN : 1 ≤ N)
    (q : ℝ) :
    ∃! f : Species N → ℝ, f (unit hN) = q ∧ operator alpha L f = 0 := by
  refine ⟨equilibrium q, ⟨equilibrium_unit hN q, ?_⟩, ?_⟩
  · apply (operator_zero_iff_closed alpha L _).mpr
    intro e
    have h := leafCharge_closed e
    dsimp [differential] at h
    dsimp [equilibrium]
    have heq : leafCharge (parent e) = leafCharge (left e) + leafCharge (right e) := by
      linarith
    rw [heq]
    ring
  · intro f hf
    have he := (operator_zero_iff_leaf alpha L hN f).mp hf.2
    change f = fun s => leafCharge s * q
    simpa only [hf.1] using he

structure Conclusions : Prop where
  complete_kernel : ∀ (alpha L : ℝ) {N : ℕ} (hN : 1 ≤ N) (f : Species N → ℝ),
    operator alpha L f = 0 ↔ f = fun s => leafCharge s * f (unit hN)
  zero_action : ∀ (alpha L : ℝ) (N : ℕ) (q : ℝ),
    action alpha L (equilibrium (N := N) q) = 0
  unique_equilibrium : ∀ (alpha L : ℝ) {N : ℕ} (hN : 1 ≤ N) (q : ℝ)
    (f : Species N → ℝ), f (unit hN) = q → action alpha L f = 0 → f = equilibrium q
  strict_restoring : ∀ (alpha L : ℝ) {N : ℕ} (hN : 1 ≤ N)
    (f : Species N → ℝ), f (unit hN) = 0 → f ≠ 0 → 0 < form alpha L f f

theorem generated : Conclusions where
  complete_kernel := operator_zero_iff_leaf
  zero_action := equilibrium_zero_action
  unique_equilibrium := unique_zero_action
  strict_restoring := positive_on_anchored

end GeneratedFoundations.Analysis.HistoryReactionKernel

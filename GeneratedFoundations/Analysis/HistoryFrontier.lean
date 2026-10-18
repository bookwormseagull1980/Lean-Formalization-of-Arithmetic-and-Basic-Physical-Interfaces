module

public import GeneratedFoundations.Arithmetic.CompleteHistoryGeometry
public import Mathlib.Data.Nat.Log

/-!
# Canonical minimal-frontier evaluation of complete histories

The complete generated history is an ordered binary tree.  Reaction order may
change the intermediate frontier without changing the ordered history or its
root.  This module fixes the Sethi--Ullman order intrinsically: evaluate the
child with larger register demand first and use left-first order at a tie.

The resulting peak frontier is the recursively defined register number.  Its
power lower bound shows that the frontier grows at most logarithmically in the
number of retained unit leaves.  The exact evaluation-path length is also
derived from the same history, so neither quantity is an external cutoff.
-/

@[expose] public section

namespace GeneratedFoundations.Analysis.HistoryFrontier

open GeneratedFoundations.Arithmetic.CompleteHistory
open GeneratedFoundations.Arithmetic.CompleteHistoryGeometry

/-- Register demand of an ordered complete history. -/
def registerNumber : {k : ℕ} → History k → ℕ
  | _, .one => 1
  | _, .node _ hl hr =>
      if registerNumber hl = registerNumber hr then
        registerNumber hl + 1
      else
        max (registerNumber hl) (registerNumber hr)

/-- Peak number of simultaneously retained histories under the canonical
larger-register-first schedule, with left-first tie breaking. -/
def scheduledPeak : {k : ℕ} → History k → ℕ
  | _, .one => 1
  | _, .node _ hl hr =>
      if registerNumber hl < registerNumber hr then
        max (scheduledPeak hr) (scheduledPeak hl + 1)
      else
        max (scheduledPeak hl) (scheduledPeak hr + 1)

/-- One source step per leaf and one reaction step per internal vertex. -/
def pathLength : {k : ℕ} → History k → ℕ
  | _, .one => 1
  | _, .node _ hl hr => pathLength hl + pathLength hr + 1

theorem registerNumber_pos {k : ℕ} (h : History k) : 0 < registerNumber h := by
  induction h with
  | one => simp [registerNumber]
  | node c hl hr ihl ihr =>
      simp only [registerNumber]
      split_ifs <;> omega

/-- The deterministic schedule realizes exactly the recursive register
number; no path-order parameter remains. -/
theorem scheduledPeak_eq_registerNumber {k : ℕ} (h : History k) :
    scheduledPeak h = registerNumber h := by
  induction h with
  | one => rfl
  | node c hl hr ihl ihr =>
      simp only [scheduledPeak, ihl, ihr, registerNumber]
      by_cases hlt : registerNumber hl < registerNumber hr
      · have hne : registerNumber hl ≠ registerNumber hr := ne_of_lt hlt
        have hsucc : registerNumber hl + 1 ≤ registerNumber hr := hlt
        rw [ite_eq_left hlt, ite_eq_right hne, Nat.max_eq_left hsucc,
          Nat.max_eq_right hlt.le]
      · have hle : registerNumber hr ≤ registerNumber hl := Nat.le_of_not_gt hlt
        rw [ite_eq_right hlt]
        by_cases heq : registerNumber hl = registerNumber hr
        · rw [heq]
          simp
        · have hstrict : registerNumber hr < registerNumber hl :=
            lt_of_le_of_ne hle (Ne.symm heq)
          have hsucc : registerNumber hr + 1 ≤ registerNumber hl := hstrict
          rw [ite_eq_right heq, Nat.max_eq_left hsucc,
            Nat.max_eq_left hstrict.le]

/-- A register demand of `q` requires at least `2^(q-1)` unit leaves. -/
theorem registerPower_le_leafCount {k : ℕ} (h : History k) :
    2 ^ (registerNumber h - 1) ≤ leafCount h := by
  induction h with
  | one => norm_num [registerNumber, leafCount]
  | node c hl hr ihl ihr =>
      simp only [registerNumber, leafCount_node]
      by_cases heq : registerNumber hl = registerNumber hr
      · rw [ite_eq_left heq]
        have hpos := registerNumber_pos hl
        have hexp : registerNumber hl = (registerNumber hl - 1) + 1 := by omega
        rw [Nat.add_sub_cancel, hexp, pow_succ]
        rw [← heq] at ihr
        omega
      · rw [ite_eq_right heq]
        by_cases hle : registerNumber hl ≤ registerNumber hr
        · rw [Nat.max_eq_right hle]
          omega
        · have hrl : registerNumber hr ≤ registerNumber hl := Nat.le_of_not_ge hle
          rw [Nat.max_eq_left hrl]
          omega

/-- Logarithmic frontier bound in the exact form used by the finite-history
recovery argument. -/
theorem registerNumber_le_log_leafCount {k : ℕ} (h : History k) :
    registerNumber h ≤ 1 + Nat.log2 (leafCount h) := by
  have hleaf : leafCount h ≠ 0 := by
    have hpow := registerPower_le_leafCount h
    have hpos : 0 < 2 ^ (registerNumber h - 1) := by positivity
    omega
  have hlog : registerNumber h - 1 ≤ Nat.log2 (leafCount h) :=
    (Nat.le_log2 hleaf).2 (registerPower_le_leafCount h)
  omega

theorem scheduledPeak_le_log_leafCount {k : ℕ} (h : History k) :
    scheduledPeak h ≤ 1 + Nat.log2 (leafCount h) := by
  rw [scheduledPeak_eq_registerNumber]
  exact registerNumber_le_log_leafCount h

theorem pathLength_add_one {k : ℕ} (h : History k) :
    pathLength h + 1 = 2 * leafCount h := by
  induction h with
  | one => norm_num [pathLength, leafCount]
  | node c hl hr ihl ihr =>
      simp only [pathLength, leafCount_node]
      omega

/-- The canonical path contains exactly one source event per leaf and one
reaction event per internal node. -/
theorem pathLength_eq_two_mul_leafCount_sub_one {k : ℕ} (h : History k) :
    pathLength h = 2 * leafCount h - 1 := by
  have hlen := pathLength_add_one h
  omega

structure Conclusions : Prop where
  schedule_exact : ∀ {k : ℕ} (h : History k),
    scheduledPeak h = registerNumber h
  exponential_support : ∀ {k : ℕ} (h : History k),
    2 ^ (registerNumber h - 1) ≤ leafCount h
  logarithmic_frontier : ∀ {k : ℕ} (h : History k),
    scheduledPeak h ≤ 1 + Nat.log2 (leafCount h)
  exact_path_length : ∀ {k : ℕ} (h : History k),
    pathLength h = 2 * leafCount h - 1

theorem historyFrontierConclusions : Conclusions where
  schedule_exact := scheduledPeak_eq_registerNumber
  exponential_support := registerPower_le_leafCount
  logarithmic_frontier := scheduledPeak_le_log_leafCount
  exact_path_length := pathLength_eq_two_mul_leafCount_sub_one

end GeneratedFoundations.Analysis.HistoryFrontier

module

public import GeneratedFoundations.Arithmetic.CompleteNaturalObject

/-!
# Information retained by complete arithmetic histories

The generated root does not determine how it was produced.  This module keeps
the finite observables that are lost under scalar evaluation: leaf charge,
the two native node counts, left-right orientation and multiplicative capacity
defect.  All are recursive functions on the existing complete history; no
extra label or probabilistic assumption is introduced.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Arithmetic.CompleteHistoryGeometry

open GeneratedFoundations.Arithmetic.CompleteHistory

namespace Channel

/-- The canonical ordered additive channel on two positive roots. -/
@[reducible] def add (m n : ℕ) (hm : 0 < m) (hn : 0 < n) : Channel (m + n) := by
  refine ⟨(.add, ⟨m, by omega⟩, ⟨n, by omega⟩), ?_⟩
  change 0 < m ∧ 0 < n ∧ m + n = m + n
  exact ⟨hm, hn, rfl⟩

/-- The canonical ordered nontrivial multiplicative channel. -/
@[reducible] def mul (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) : Channel (m * n) := by
  refine ⟨(.mul,
    ⟨m, lt_mul_of_one_lt_right (by omega) (by omega)⟩,
    ⟨n, by
      rw [Nat.mul_comm]
      exact lt_mul_of_one_lt_right (by omega) (by omega)⟩), ?_⟩
  change 0 < m ∧ 0 < n ∧ (2 ≤ m ∧ 2 ≤ n ∧ m * n = m * n)
  exact ⟨by omega, by omega, hm, hn, rfl⟩

/-- Reverse the ordered children of a native top channel. -/
@[reducible] def swap {k : ℕ} (c : Channel k) : Channel k := by
  refine ⟨(c.operation, c.right, c.left), c.right_pos, c.left_pos, ?_⟩
  cases hop : c.operation with
  | add =>
      have h := c.equation
      rw [hop] at h
      simpa [Nat.add_comm] using h
  | mul =>
      have h := c.equation
      rw [hop] at h
      exact ⟨h.2.1, h.1, by simpa [Nat.mul_comm] using h.2.2⟩

@[simp] theorem swap_operation {k : ℕ} (c : Channel k) :
    (swap c).operation = c.operation := rfl

@[simp] theorem swap_left {k : ℕ} (c : Channel k) :
    (swap c).left = c.right := rfl

@[simp] theorem swap_right {k : ℕ} (c : Channel k) :
    (swap c).right = c.left := rfl

@[simp] theorem swap_swap {k : ℕ} (c : Channel k) : swap (swap c) = c := by
  apply Subtype.ext
  rfl

end Channel

theorem history_root_pos {k : ℕ} (_h : History k) : 0 < k := by
  cases _h with
  | one => norm_num
  | node c _ _ => exact c.left_pos.trans c.left_lt

/-- Native addition of two complete positive histories. -/
def addHistory {m n : ℕ} (hm : History m) (hn : History n) : History (m + n) :=
  .node (Channel.add m n (history_root_pos hm) (history_root_pos hn)) hm hn

/-- Native multiplication of two histories whose roots are nontrivial. -/
def mulHistory {m n : ℕ} (hm : History m) (hn : History n)
    (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) : History (m * n) :=
  .node (Channel.mul m n hm2 hn2) hm hn

/-- Number of unit leaves retained by a history. -/
def leafCount : {k : ℕ} → History k → ℕ
  | _, .one => 1
  | _, .node _ hl hr => leafCount hl + leafCount hr

/-- Number of additive internal vertices. -/
def addCount : {k : ℕ} → History k → ℕ
  | _, .one => 0
  | _, .node c hl hr =>
      addCount hl + addCount hr + if c.operation = .add then 1 else 0

/-- Number of multiplicative internal vertices. -/
def mulCount : {k : ℕ} → History k → ℕ
  | _, .one => 0
  | _, .node c hl hr =>
      mulCount hl + mulCount hr + if c.operation = .mul then 1 else 0

/-- Intrinsic ordered orientation.  It changes sign under reflection and is
independent of the names of the two native operations. -/
def orientationScore : {k : ℕ} → History k → ℤ
  | _, .one => 0
  | _, .node _ hl hr =>
      (leafCount hl : ℤ) - (leafCount hr : ℤ) +
        orientationScore hl + orientationScore hr

/-- Reflect every ordered vertex of a complete history. -/
def reflect : {k : ℕ} → History k → History k
  | _, .one => .one
  | _, .node c hl hr => .node (Channel.swap c) (reflect hr) (reflect hl)

@[simp] theorem leafCount_one : leafCount History.one = 1 := rfl
@[simp] theorem addCount_one : addCount History.one = 0 := rfl
@[simp] theorem mulCount_one : mulCount History.one = 0 := rfl
@[simp] theorem orientationScore_one : orientationScore History.one = 0 := rfl

@[simp] theorem leafCount_node {k : ℕ} (c : Channel k)
    (hl : History c.left.1) (hr : History c.right.1) :
    leafCount (.node c hl hr) = leafCount hl + leafCount hr := rfl

/-- Every full binary history has one more leaf than internal vertices. -/
theorem leafCount_eq_nodeCount_succ {k : ℕ} (h : History k) :
    leafCount h = addCount h + mulCount h + 1 := by
  induction h with
  | one => rfl
  | node c hl hr ihl ihr =>
      cases hop : c.operation with
      | add => simp [leafCount, addCount, mulCount, hop, ihl, ihr]; omega
      | mul => simp [leafCount, addCount, mulCount, hop, ihl, ihr]; omega

/-- The number of retained unit leaves never exceeds the generated root. -/
theorem leafCount_le_root {k : ℕ} (h : History k) : leafCount h ≤ k := by
  induction h with
  | one => rfl
  | @node k c hl hr ihl ihr =>
      have hsum : leafCount hl + leafCount hr ≤ c.left.1 + c.right.1 :=
        Nat.add_le_add ihl ihr
      cases hop : c.operation with
      | add =>
          have heq := c.equation
          rw [hop] at heq
          simpa [leafCount, heq] using hsum
      | mul =>
          have heq := c.equation
          rw [hop] at heq
          have hchildren : c.left.1 + c.right.1 ≤ c.left.1 * c.right.1 :=
            add_le_mul heq.1 heq.2.1
          simpa [leafCount, heq.2.2] using hsum.trans hchildren

/-- Capacity retained at the root but not represented by unit leaves. -/
def capacityDefect {k : ℕ} (h : History k) : ℕ := k - leafCount h

/-- Integer form of the same defect, convenient for exact recursive laws. -/
def capacityDefectZ {k : ℕ} (h : History k) : ℤ :=
  (k : ℤ) - (leafCount h : ℤ)

theorem capacityDefectZ_nonneg {k : ℕ} (h : History k) :
    0 ≤ capacityDefectZ h := by
  exact sub_nonneg.mpr (Int.ofNat_le.mpr (leafCount_le_root h))

/-- Additive vertices only combine the defects already present below them. -/
theorem capacityDefectZ_add_node {k : ℕ} (c : Channel k)
    (hl : History c.left.1) (hr : History c.right.1)
    (hop : c.operation = .add) :
    capacityDefectZ (.node c hl hr) = capacityDefectZ hl + capacityDefectZ hr := by
  have heq := c.equation
  rw [hop] at heq
  simp only [capacityDefectZ, leafCount_node]
  norm_num at heq ⊢
  omega

/-- A multiplicative vertex contributes precisely its local capacity excess. -/
theorem capacityDefectZ_mul_node {k : ℕ} (c : Channel k)
    (hl : History c.left.1) (hr : History c.right.1)
    (hop : c.operation = .mul) :
    capacityDefectZ (.node c hl hr) =
      capacityDefectZ hl + capacityDefectZ hr +
        ((c.left.1 * c.right.1 : ℕ) : ℤ) - c.left.1 - c.right.1 := by
  have heq := c.equation
  rw [hop] at heq
  simp only [capacityDefectZ, leafCount_node]
  norm_num at heq ⊢
  omega

@[simp] theorem leafCount_reflect {k : ℕ} (h : History k) :
    leafCount (reflect h) = leafCount h := by
  induction h with
  | one => simp [reflect, leafCount]
  | node c hl hr ihl ihr => simp [reflect, leafCount, ihl, ihr, Nat.add_comm]

@[simp] theorem addCount_reflect {k : ℕ} (h : History k) :
    addCount (reflect h) = addCount h := by
  induction h with
  | one => simp [reflect, addCount]
  | node c hl hr ihl ihr =>
      simp [reflect, addCount, ihl, ihr, Nat.add_comm]
      rfl

@[simp] theorem mulCount_reflect {k : ℕ} (h : History k) :
    mulCount (reflect h) = mulCount h := by
  induction h with
  | one => simp [reflect, mulCount]
  | node c hl hr ihl ihr =>
      simp [reflect, mulCount, ihl, ihr, Nat.add_comm]
      rfl

@[simp] theorem orientationScore_reflect {k : ℕ} (h : History k) :
    orientationScore (reflect h) = -orientationScore h := by
  induction h with
  | one => simp [reflect, orientationScore]
  | node c hl hr ihl ihr =>
      simp [reflect, orientationScore, ihl, ihr]
      ring

/-- The three source coordinates obey the exact native vertex law used by the
history Fisher geometry. -/
theorem orientationScore_node_from_sources {k : ℕ} (c : Channel k)
    (hl : History c.left.1) (hr : History c.right.1) :
    orientationScore (.node c hl hr) =
      ((addCount hl + mulCount hl : ℕ) : ℤ) + orientationScore hl -
      ((addCount hr + mulCount hr : ℕ) : ℤ) + orientationScore hr := by
  have hlid := leafCount_eq_nodeCount_succ hl
  have hrid := leafCount_eq_nodeCount_succ hr
  simp only [orientationScore]
  norm_num at hlid hrid ⊢
  omega

structure Conclusions : Prop where
  binary_tree_identity : ∀ {k : ℕ} (h : History k),
    leafCount h = addCount h + mulCount h + 1
  leaf_bound : ∀ {k : ℕ} (h : History k), leafCount h ≤ k
  defect_nonnegative : ∀ {k : ℕ} (h : History k), 0 ≤ capacityDefectZ h
  reflection_even : ∀ {k : ℕ} (h : History k),
    leafCount (reflect h) = leafCount h ∧
      addCount (reflect h) = addCount h ∧
      mulCount (reflect h) = mulCount h
  reflection_odd : ∀ {k : ℕ} (h : History k),
    orientationScore (reflect h) = -orientationScore h
  vertex_orientation : ∀ {k : ℕ} (c : Channel k)
      (hl : History c.left.1) (hr : History c.right.1),
    orientationScore (.node c hl hr) =
      ((addCount hl + mulCount hl : ℕ) : ℤ) + orientationScore hl -
      ((addCount hr + mulCount hr : ℕ) : ℤ) + orientationScore hr

theorem completeHistoryGeometryConclusions : Conclusions where
  binary_tree_identity := leafCount_eq_nodeCount_succ
  leaf_bound := leafCount_le_root
  defect_nonnegative := capacityDefectZ_nonneg
  reflection_even := fun h =>
    ⟨leafCount_reflect h, addCount_reflect h, mulCount_reflect h⟩
  reflection_odd := orientationScore_reflect
  vertex_orientation := orientationScore_node_from_sources

end GeneratedFoundations.Arithmetic.CompleteHistoryGeometry

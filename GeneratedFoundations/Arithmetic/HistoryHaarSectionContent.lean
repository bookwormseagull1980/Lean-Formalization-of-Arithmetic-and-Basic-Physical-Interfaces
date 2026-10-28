module

public import GeneratedFoundations.Arithmetic.HistoryHaarSectionComparison

/-!
# Content counted from the actual scalar section window

The number of visible scalar positions is computed from the differentiated
even Casimir spectrum. Every position retains all history labels and both
matrix-coefficient coordinates. The resulting finite content embeds
injectively into the original joint basis, and exhausts exactly its visible
scalar sector. Neither a position count nor a field multiplicity is supplied
as new source data.

These are content and support identities. A condition selecting an endpoint
must be stated on this content and the same variational response; a chosen
number of visible positions is not a consequence of these counting identities.
-/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryHaarSectionContent

open HistoryHaarSectionWindow
open HistoryHaarSectionJointHessian (Index)
open Geometry.SourceScalarKineticForm (position)

local instance (N : ℕ) : DecidableEq (Index N) := Classical.decEq _

/-- Number of positions strictly below the actual squared kinetic cutoff. -/
def positionCount (B : ℝ) : ℕ := Nat.ceil ((Real.sqrt (B + 1) - 1) / 2)

theorem position_lt_iff (j : ℕ) (B : ℝ) : position j < B ↔ j < positionCount B := by
  rw [positionCount, Nat.lt_ceil, Geometry.SourceScalarKineticForm.position_eq]
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hs : (2 * (j : ℝ) + 1) < Real.sqrt (B + 1) ↔
      (2 * (j : ℝ) + 1) ^ 2 < B + 1 := Real.lt_sqrt (by linarith)
  constructor
  · intro h
    have ht := hs.mpr (by nlinarith)
    linarith
  · intro h
    have ht := hs.mp (by linarith)
    nlinarith

theorem positionCount_unique (B : ℝ) (m : ℕ)
    (h : ∀ j, position j < B ↔ j < m) : m = positionCount B := by
  apply Nat.le_antisymm
  · by_contra hn
    have hp := (h (positionCount B)).mpr (Nat.lt_of_not_ge hn)
    exact Nat.lt_irrefl _ ((position_lt_iff _ B).mp hp)
  · by_contra hn
    have hp := (position_lt_iff m B).mpr (Nat.lt_of_not_ge hn)
    exact Nat.lt_irrefl _ ((h m).mp hp)

theorem positionCount_mono : Monotone positionCount := by
  intro B C hBC
  apply Nat.le_of_not_gt
  intro hc
  have hp := (position_lt_iff (positionCount C) B).mpr hc
  have hpc := (position_lt_iff (positionCount C) C).mp (lt_of_lt_of_le hp hBC)
  exact Nat.lt_irrefl _ hpc

theorem positionCount_eq_zero_iff (B : ℝ) : positionCount B = 0 ↔ B ≤ 0 := by
  have h := position_lt_iff 0 B
  norm_num [Geometry.SourceScalarKineticForm.position_eq] at h
  constructor
  · intro hz
    apply le_of_not_gt
    intro hB
    simpa only [hz, lt_self_iff_false] using h.mp hB
  · intro hB
    apply Nat.eq_zero_of_not_pos
    intro hc
    exact not_lt_of_ge hB (h.mpr hc)

theorem positionCount_eq_succ_iff (B : ℝ) (m : ℕ) :
    positionCount B = m + 1 ↔ position m < B ∧ B ≤ position (m + 1) := by
  rw [← Geometry.SourceScalarKineticForm.position_plateau_iff]
  constructor
  · intro h j
    simpa only [h] using position_lt_iff j B
  · intro h
    exact (positionCount_unique B (m + 1) h).symm

theorem positionCount_eq_one_iff (B : ℝ) :
    positionCount B = 1 ↔ 0 < B ∧ B ≤ 8 := by
  have h := positionCount_eq_succ_iff B 0
  norm_num [Geometry.SourceScalarKineticForm.position_eq] at h
  exact h

theorem positionCount_eq_two_iff (B : ℝ) :
    positionCount B = 2 ↔ 8 < B ∧ B ≤ 24 := by
  have h := positionCount_eq_succ_iff B 1
  norm_num [Geometry.SourceScalarKineticForm.position_eq] at h
  exact h

theorem positionCount_eq_three_iff (B : ℝ) :
    positionCount B = 3 ↔ 24 < B ∧ B ≤ 48 := by
  have h := positionCount_eq_succ_iff B 2
  norm_num [Geometry.SourceScalarKineticForm.position_eq] at h
  exact h

/-- A complete finite collection of scalar positions, with all native
history and matrix-coefficient labels in every row. -/
abbrev ContentLabels (N m : ℕ) :=
  (j : Fin m) × HistoryHaarSectionAction.PositionLabels N j.val

def contentIndex (N m : ℕ) (i : ContentLabels N m) : Index N :=
  positionIndex N i.1.val i.2

theorem contentIndex_injective (N m : ℕ) : Function.Injective (contentIndex N m) := by
  rintro ⟨⟨j, hj⟩, a⟩ ⟨⟨k, hk⟩, b⟩ h
  have hd : 2 * j = 2 * k := by
    have hd := congrArg (fun i : Index N =>
      Sum.elim (fun _ => 0) (fun a => a.2.val.1) i) h
    exact hd
  have hjk : j = k := by omega
  subst k
  have hab : a = b := positionIndex_injective N j h
  subst b
  rfl

theorem contentIndex_visible (N : ℕ) (B : ℝ)
    (i : ContentLabels N (positionCount B)) :
    contentIndex N (positionCount B) i ∈ support N B := by
  rw [contentIndex, position_membership]
  exact (position_lt_iff _ B).mpr i.1.isLt

theorem contentIndex_is_scalar (N m : ℕ) (i : ContentLabels N m) :
    (contentIndex N m i).isRight = true := rfl

/-- The correspondence goes onto the actual scalar support of the full
joint operator; it is not a count on a replacement label family. -/
theorem visible_scalar_iff_content (N : ℕ) (B : ℝ) (i : Index N) :
    (i ∈ support N B ∧ i.isRight = true) ↔
      ∃ c : ContentLabels N (positionCount B), contentIndex N (positionCount B) c = i := by
  constructor
  · rintro ⟨hi, hs⟩
    cases i with
    | inl a => simp at hs
    | inr a =>
      rcases a with ⟨i, ⟨⟨m, r, c⟩, he⟩⟩
      obtain ⟨j, hj⟩ := he
      change m = j + j at hj
      have hm : m = 2 * j := by omega
      rcases hm with rfl
      have hp : position j < B := by
        exact (mem_support N B _).mp hi
      exact ⟨⟨⟨j, (position_lt_iff j B).mp hp⟩, i, r, c⟩, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨contentIndex_visible N B c, contentIndex_is_scalar _ _ c⟩

theorem content_card (N m : ℕ) :
    Fintype.card (ContentLabels N m) =
      HistoryAdjointCasimir.dimension N * ∑ j ∈ Finset.range m, (2 * j + 1) ^ 2 := by
  classical
  rw [Fintype.card_sigma]
  simp only [HistoryHaarSectionAction.position_multiplicity]
  rw [Fin.sum_univ_eq_sum_range (fun j =>
    HistoryAdjointCasimir.dimension N * (2 * j + 1) ^ 2), Finset.mul_sum]

theorem odd_square_sum (m : ℕ) :
    3 * (∑ j ∈ Finset.range m, (2 * j + 1) ^ 2) + m = 4 * m ^ 3 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    nlinarith

theorem content_card_identity (N m : ℕ) :
    3 * Fintype.card (ContentLabels N m) + HistoryAdjointCasimir.dimension N * m =
      4 * HistoryAdjointCasimir.dimension N * m ^ 3 := by
  rw [content_card]
  nlinarith [odd_square_sum m]

theorem content_card_one (N : ℕ) :
    Fintype.card (ContentLabels N 1) = HistoryAdjointCasimir.dimension N := by
  rw [content_card]
  norm_num

theorem content_card_two (N : ℕ) :
    Fintype.card (ContentLabels N 2) = 10 * HistoryAdjointCasimir.dimension N := by
  rw [content_card]
  norm_num [Finset.sum_range_succ]
  omega

theorem content_card_three (N : ℕ) :
    Fintype.card (ContentLabels N 3) = 35 * HistoryAdjointCasimir.dimension N := by
  rw [content_card]
  norm_num [Finset.sum_range_succ]
  omega

/-- These are the visible labels of the original joint operator, not a
second copy whose cardinality has merely been chosen to agree. -/
theorem scalarSupport_eq_image (N : ℕ) (B : ℝ) :
    (support N B).filter (fun i => i.isRight = true) =
      (Finset.univ : Finset (ContentLabels N (positionCount B))).image
        (contentIndex N (positionCount B)) := by
  classical
  ext i
  simpa only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and] using
    visible_scalar_iff_content N B i

theorem scalarSupport_card (N : ℕ) (B : ℝ) :
    ((support N B).filter (fun i => i.isRight = true)).card =
      Fintype.card (ContentLabels N (positionCount B)) := by
  classical
  rw [scalarSupport_eq_image, Finset.card_image_of_injective _
    (contentIndex_injective N (positionCount B)), Finset.card_univ]

/-- The full scalar contribution, with the complete original rows. -/
def scalarResponse (N : ℕ) (B : ℝ) : ℝ :=
  ∑ i ∈ (support N B).filter (fun i => i.isRight = true), branchIntegral N B i

/-- The connection contribution is retained with all its matrix entries
and both curl branches. It is not replaced by a position-count factor. -/
def fieldResponse (N : ℕ) (B : ℝ) : ℝ :=
  ∑ i ∈ (support N B).filter (fun i => ¬ i.isRight = true), branchIntegral N B i

theorem scalarResponse_eq_rows (N : ℕ) (B : ℝ) :
    scalarResponse N B =
      ∑ j : Fin (positionCount B),
        (HistoryAdjointCasimir.dimension N * (2 * j.val + 1) ^ 2 : ℕ) *
          positionIntegral N j.val B := by
  classical
  rw [scalarResponse, scalarSupport_eq_image, Finset.sum_image]
  · change (∑ i : ContentLabels N (positionCount B),
      branchIntegral N B (contentIndex N (positionCount B) i)) = _
    rw [Fintype.sum_sigma]
    exact Finset.sum_congr rfl (fun j _ => complete_position_trace N j.val B)
  · exact fun _ _ _ _ h => contentIndex_injective _ _ h

/-- Counting positions and evaluating the Gaussian response are connected
by an identity for the very same complete joint trace. -/
theorem responseTrace_content_decomposition (N : ℕ) (B : ℝ) :
    responseTrace N B = fieldResponse N B +
      ∑ j : Fin (positionCount B),
        (HistoryAdjointCasimir.dimension N * (2 * j.val + 1) ^ 2 : ℕ) *
          positionIntegral N j.val B := by
  classical
  rw [← scalarResponse_eq_rows]
  exact (Finset.sum_filter_add_sum_filter_not (support N B)
    (fun i => i.isRight = true) (branchIntegral N B)).symm.trans (add_comm _ _)

/-- A response crossing and a position plateau are equivalent tests only
when both refer to this same complete response. The connection sector and
every new spectral birth are present on both sides of the comparison. -/
theorem response_characterizes_content_count (N m : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    positionCount B = m + 1 ↔
      responseTrace N (position m) < responseTrace N B ∧
        responseTrace N B ≤ responseTrace N (position (m + 1)) := by
  have hp (j : ℕ) : 0 ≤ position j :=
    Geometry.SourceCasimirClosure.energy_nonneg _
  rw [positionCount_eq_succ_iff]
  constructor
  · rintro ⟨hlo, hhi⟩
    exact ⟨responseTrace_strictMonoOn N (hp m) hB hlo, responseTrace_mono N hhi⟩
  · rintro ⟨hlo, hhi⟩
    constructor
    · by_contra hn
      exact not_lt_of_ge (responseTrace_mono N (le_of_not_gt hn)) hlo
    · by_contra hn
      exact not_lt_of_ge hhi
        (responseTrace_strictMonoOn N (hp (m + 1)) hB (lt_of_not_ge hn))

structure Conclusions : Prop where
  calculated_positions : ∀ j B, position j < B ↔ j < positionCount B
  unique_position_count : ∀ B m, (∀ j, position j < B ↔ j < m) → m = positionCount B
  complete_scalar_content : ∀ N B i,
    (i ∈ support N B ∧ i.isRight = true) ↔
      ∃ c : ContentLabels N (positionCount B), contentIndex N (positionCount B) c = i
  faithful_content_labels : ∀ N m, Function.Injective (contentIndex N m)
  calculated_content_rank : ∀ N m,
    3 * Fintype.card (ContentLabels N m) + HistoryAdjointCasimir.dimension N * m =
      4 * HistoryAdjointCasimir.dimension N * m ^ 3
  actual_visible_rank : ∀ N B,
    ((support N B).filter (fun i => i.isRight = true)).card =
      Fintype.card (ContentLabels N (positionCount B))
  complete_response_rows : ∀ N B,
    responseTrace N B = fieldResponse N B +
      ∑ j : Fin (positionCount B),
        (HistoryAdjointCasimir.dimension N * (2 * j.val + 1) ^ 2 : ℕ) *
          positionIntegral N j.val B
  same_response_content_test : ∀ N m B, 0 ≤ B →
    (positionCount B = m + 1 ↔
      responseTrace N (position m) < responseTrace N B ∧
        responseTrace N B ≤ responseTrace N (position (m + 1)))

theorem generated : Conclusions where
  calculated_positions := position_lt_iff
  unique_position_count := positionCount_unique
  complete_scalar_content := visible_scalar_iff_content
  faithful_content_labels := contentIndex_injective
  calculated_content_rank := content_card_identity
  actual_visible_rank := scalarSupport_card
  complete_response_rows := responseTrace_content_decomposition
  same_response_content_test := fun N m _ hB => response_characterizes_content_count N m hB

end GeneratedFoundations.Arithmetic.HistoryHaarSectionContent

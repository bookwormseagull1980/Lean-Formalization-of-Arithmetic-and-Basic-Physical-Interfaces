module

public import GeneratedFoundations.Arithmetic.HistoryHaarSectionProbability
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Complete source content and Gaussian shell budgets

Every original joint eigenvector occurs in a finite source window, but no
finite window contains all scalar source positions. The complete Gaussian
shell sums nevertheless converge. Their actual multiplicities give a
cutoff-independent bound for the full response at each fixed history
stage; the displayed bound retains its dependence on the history rank.

This separates exhaustion of generated content from selection of a finite
observed content. The physical three-position condition is not used in
either statement. All shell weights below come from the original joint
operator, including both nonzero curl signs.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Set Filter

namespace GeneratedFoundations.Arithmetic.HistoryHaarSectionExhaustion

open HistoryHaarSectionWindow HistoryHaarSectionContent HistoryHaarSectionShells
open HistoryHaarSectionJointHessian (Index)
open Geometry.SourceScalarKineticForm (position)

def basePositionLabel (N j : ℕ) : HistoryHaarSectionAction.PositionLabels N j :=
  ((HistoryCliffordAction.historyPoint N, Sum.inl 0), 0, 0)

theorem every_label_visible (N : ℕ) (i : Index N) :
    ∃ R : ℕ, i ∈ support N (R : ℝ) := by
  obtain ⟨R, hR⟩ := exists_nat_gt (kinetic N i)
  exact ⟨R, (mem_support N _ i).mpr hR⟩

theorem every_position_visible (N j : ℕ) :
    ∃ R : ℕ, ∀ a : HistoryHaarSectionAction.PositionLabels N j,
      positionIndex N j a ∈ support N (R : ℝ) := by
  obtain ⟨R, hR⟩ := exists_nat_gt (position j)
  exact ⟨R, fun a => (position_membership N j R a).mpr hR⟩

theorem finite_window_omits_position (N : ℕ) (B : ℝ) :
    ∃ j, positionIndex N j (basePositionLabel N j) ∉ support N B := by
  obtain ⟨j, hj⟩ := exists_nat_gt B
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have he : B < position (j + 1) := by
    rw [Geometry.SourceScalarKineticForm.position_eq]
    push_cast
    nlinarith
  exact ⟨j + 1, fun h => (not_lt_of_ge he.le)
    ((position_membership N _ B _).mp h)⟩

theorem position_count_unbounded (m : ℕ) :
    ∃ R : ℕ, m < positionCount (R : ℝ) := by
  obtain ⟨R, hR⟩ := exists_nat_gt (position m)
  exact ⟨R, (position_lt_iff m R).mp hR⟩

/-- Every finite position count is realized at its own calculated next
scalar edge. This is a family of source windows, not a selected count. -/
def contentEndpoint (m : ℕ) : ℕ := 4 * (m + 1) * (m + 2)

theorem contentEndpoint_position (m : ℕ) :
    (contentEndpoint m : ℝ) = position (m + 1) := by
  simp only [contentEndpoint, Geometry.SourceScalarKineticForm.position_eq]
  push_cast
  ring

theorem positionCount_contentEndpoint (m : ℕ) :
    positionCount (contentEndpoint m : ℝ) = m + 1 := by
  rw [positionCount_eq_succ_iff, contentEndpoint_position]
  constructor
  · rw [Geometry.SourceScalarKineticForm.position_eq,
      Geometry.SourceScalarKineticForm.position_eq]
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast
    nlinarith
  · exact le_rfl

/-- Half of the original real Gaussian frequency integral. -/
def frequencyMass : ℝ := Real.sqrt Real.pi / 2

theorem frequencyMass_pos : 0 < frequencyMass := by
  unfold frequencyMass
  positivity

/-- The bound uses the original Gaussian on the entire half-line. No
hard cutoff of the Gaussian or replacement of a shell weight is made. -/
theorem fieldIntegral_le_full (B a : ℝ) :
    fieldIntegral B a ≤ Real.exp (-a) * frequencyMass := by
  have he (u : ℝ) : Real.exp (-(u ^ 2 + a)) =
      Real.exp (-a) * Real.exp (-(u ^ 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [fieldIntegral, he, intervalIntegral.integral_const_mul]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  rw [intervalIntegral.integral_of_le (Real.sqrt_nonneg _)]
  have h := setIntegral_mono_set
    ((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).integrableOn
      (s := Ioi (0 : ℝ)))
    (Filter.Eventually.of_forall (fun x : ℝ => by
      change (0 : ℝ) ≤ Real.exp (-1 * x ^ 2)
      exact (Real.exp_pos _).le))
    (Filter.Eventually.of_forall (fun x : ℝ =>
      show x ∈ Ioc 0 (Real.sqrt (B - a)) → x ∈ Ioi 0 from fun hx => hx.1))
  have hgauss : (∫ x in Ioi (0 : ℝ), Real.exp (-(x ^ 2))) = frequencyMass := by
    simpa [frequencyMass] using integral_gaussian_Ioi 1
  simpa only [neg_mul, one_mul, hgauss] using h

/-- Actual two-sign differential row, with its original source-row
multiplicity. The missing negative branch at degree zero stays zero. -/
def fieldHeat (m : ℕ) : ℝ :=
  if Even m then
    (m + 1 : ℕ) * ((m + 3 : ℕ) * Real.exp (-(((m : ℝ) + 2) ^ 2)) +
      (m - 1 : ℕ) * Real.exp (-((m : ℝ) ^ 2))) else 0

def scalarHeat (j : ℕ) : ℝ :=
  (2 * j + 1 : ℕ) ^ 2 * Real.exp (-position j)

theorem fieldHeat_nonneg (m : ℕ) : 0 ≤ fieldHeat m := by
  unfold fieldHeat
  split_ifs <;> positivity

theorem scalarHeat_nonneg (j : ℕ) : 0 ≤ scalarHeat j := by
  unfold scalarHeat
  positivity

private theorem square_ge_nat (m : ℕ) : (m : ℝ) ≤ (m : ℝ) ^ 2 := by
  by_cases hm : m = 0
  · simp [hm]
  · have hp : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
    nlinarith

theorem fieldHeat_le (m : ℕ) :
    fieldHeat m ≤ 2 * ((m : ℝ) + 3) ^ 2 * Real.exp (-(m : ℝ)) := by
  unfold fieldHeat
  split_ifs with hm
  · have hn : ((m - 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.sub_le m 1
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast
    have he1 : Real.exp (-(((m : ℝ) + 2) ^ 2)) ≤ Real.exp (-(m : ℝ)) :=
      Real.exp_le_exp.mpr (by nlinarith [square_ge_nat m])
    have he2 : Real.exp (-((m : ℝ) ^ 2)) ≤ Real.exp (-(m : ℝ)) :=
      Real.exp_le_exp.mpr (by linarith [square_ge_nat m])
    have h1 := mul_le_mul_of_nonneg_left he1 (Nat.cast_nonneg (m + 3))
    have h2 := mul_le_mul_of_nonneg_left he2 (Nat.cast_nonneg (m - 1))
    have hh := mul_le_mul_of_nonneg_left (add_le_add h1 h2) (Nat.cast_nonneg (m + 1))
    push_cast at hh
    have hc : ((m : ℝ) + 1) * (((m : ℝ) + 3) + (m - 1 : ℕ)) ≤
        2 * ((m : ℝ) + 3) ^ 2 := by nlinarith
    calc
      _ ≤ ((m : ℝ) + 1) * (((m : ℝ) + 3) + (m - 1 : ℕ)) *
          Real.exp (-(m : ℝ)) := by nlinarith [hh]
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le
  · positivity

theorem scalarHeat_le (j : ℕ) :
    scalarHeat j ≤ (2 * (j : ℝ) + 1) ^ 2 * Real.exp (-(j : ℝ)) := by
  have hp : (j : ℝ) ≤ position j := by
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    rw [Geometry.SourceScalarKineticForm.position_eq]
    nlinarith
  unfold scalarHeat
  push_cast
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (sq_nonneg _)

theorem summable_fieldHeat : Summable fieldHeat := by
  have h0 := Real.summable_exp_neg_nat
  have h1 := Real.summable_pow_mul_exp_neg_nat_mul 1 (by norm_num : (0 : ℝ) < 1)
  have h2 := Real.summable_pow_mul_exp_neg_nat_mul 2 (by norm_num : (0 : ℝ) < 1)
  have h : Summable (fun m : ℕ =>
      2 * ((m : ℝ) + 3) ^ 2 * Real.exp (-(m : ℝ))) := by
    convert ((h2.mul_left 2).add (h1.mul_left 12)).add (h0.mul_left 18) using 1
    funext m
    simp only [neg_mul, one_mul, pow_one]
    ring
  exact h.of_nonneg_of_le fieldHeat_nonneg fieldHeat_le

theorem summable_scalarHeat : Summable scalarHeat := by
  have h0 := Real.summable_exp_neg_nat
  have h1 := Real.summable_pow_mul_exp_neg_nat_mul 1 (by norm_num : (0 : ℝ) < 1)
  have h2 := Real.summable_pow_mul_exp_neg_nat_mul 2 (by norm_num : (0 : ℝ) < 1)
  have h : Summable (fun j : ℕ =>
      (2 * (j : ℝ) + 1) ^ 2 * Real.exp (-(j : ℝ))) := by
    convert ((h2.mul_left 4).add (h1.mul_left 4)).add h0 using 1
    funext j
    simp only [neg_mul, one_mul, pow_one]
    ring
  exact h.of_nonneg_of_le scalarHeat_nonneg scalarHeat_le

def fullBudget (N : ℕ) : ℝ := frequencyMass *
  ((HistoryAdjointCasimir.dimension N : ℝ) ^ 2 * ∑' m, fieldHeat m +
    (HistoryAdjointCasimir.dimension N : ℝ) * ∑' j, scalarHeat j)

theorem positionIntegral_le_full (N j : ℕ) (B : ℝ) :
    positionIntegral N j B ≤ Real.exp (-position j) * frequencyMass := by
  rw [← branchIntegral_positionIndex N j B (basePositionLabel N j)]
  apply (HistoryHaarSectionProbability.branchIntegral_le_mass N B _).trans
  exact fieldIntegral_le_full B (position j)

theorem field_row_le_full (B : ℝ) (m : ℕ) :
    (if Even m then
      (m + 1 : ℕ) * ((m + 3 : ℕ) * fieldIntegral B (((m : ℝ) + 2) ^ 2) +
        (m - 1 : ℕ) * fieldIntegral B ((m : ℝ) ^ 2)) else 0) ≤
      fieldHeat m * frequencyMass := by
  unfold fieldHeat
  split_ifs
  · have h1 := mul_le_mul_of_nonneg_left
      (fieldIntegral_le_full B (((m : ℝ) + 2) ^ 2)) (Nat.cast_nonneg (m + 3))
    have h2 := mul_le_mul_of_nonneg_left
      (fieldIntegral_le_full B ((m : ℝ) ^ 2)) (Nat.cast_nonneg (m - 1))
    have h := mul_le_mul_of_nonneg_left (add_le_add h1 h2) (Nat.cast_nonneg (m + 1))
    nlinarith [h]
  · simp

/-- The source rank remains visible: the bound is uniform in the
observation cutoff, not in the number of arithmetic histories. -/
theorem responseTrace_le_fullBudget (N : ℕ) (B : ℝ) :
    responseTrace N B ≤ fullBudget N := by
  rw [responseTrace_eq_shellTable, shellTable]
  have hf := Finset.sum_le_sum (s := Finset.range (HistorySpectralWindow.enumerationBound B))
    (fun m _ => field_row_le_full B m)
  have hft := summable_fieldHeat.sum_le_tsum
    (Finset.range (HistorySpectralWindow.enumerationBound B)) (fun m _ => fieldHeat_nonneg m)
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (positionCount B))))
    (fun j _ => mul_le_mul_of_nonneg_left (positionIntegral_le_full N j.val B)
      (Nat.cast_nonneg (HistoryAdjointCasimir.dimension N * (2 * j.val + 1) ^ 2)))
  have hst := summable_scalarHeat.sum_le_tsum (Finset.range (positionCount B))
    (fun j _ => scalarHeat_nonneg j)
  rw [← Finset.sum_mul] at hf
  have hs' :
      (∑ j : Fin (positionCount B),
        (HistoryAdjointCasimir.dimension N * (2 * j.val + 1) ^ 2 : ℕ) *
          positionIntegral N j.val B) ≤
      (HistoryAdjointCasimir.dimension N : ℝ) *
        (∑ j ∈ Finset.range (positionCount B), scalarHeat j) * frequencyMass := by
    convert hs using 1
    rw [← Fin.sum_univ_eq_sum_range]
    simp only [scalarHeat, Nat.cast_mul, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    ring
  have hfm := mul_le_mul_of_nonneg_right hft frequencyMass_pos.le
  have hsm := mul_le_mul_of_nonneg_right hst frequencyMass_pos.le
  have hd : 0 ≤ (HistoryAdjointCasimir.dimension N : ℝ) := Nat.cast_nonneg _
  have hfm' := mul_le_mul_of_nonneg_left (hf.trans hfm) (sq_nonneg (HistoryAdjointCasimir.dimension N : ℝ))
  have hsm' := mul_le_mul_of_nonneg_left hsm hd
  unfold fullBudget
  nlinarith [hfm', hsm', hs']

def rowTail (N J : ℕ) : ℝ := frequencyMass *
  ((HistoryAdjointCasimir.dimension N : ℝ) ^ 2 * ∑' m, fieldHeat (m + J) +
    (HistoryAdjointCasimir.dimension N : ℝ) * ∑' j, scalarHeat (j + J))

theorem rowTail_nonneg (N J : ℕ) : 0 ≤ rowTail N J := by
  unfold rowTail
  exact mul_nonneg frequencyMass_pos.le (add_nonneg
    (mul_nonneg (sq_nonneg _) (tsum_nonneg (fun m => fieldHeat_nonneg (m + J))))
    (mul_nonneg (Nat.cast_nonneg _) (tsum_nonneg (fun j => scalarHeat_nonneg (j + J)))))

theorem rowTail_tendsto_zero (N : ℕ) : Tendsto (rowTail N) atTop (𝓝 0) := by
  have hf := tendsto_sum_nat_add fieldHeat
  have hs := tendsto_sum_nat_add scalarHeat
  change Tendsto (fun J => frequencyMass *
    ((HistoryAdjointCasimir.dimension N : ℝ) ^ 2 * ∑' m, fieldHeat (m + J) +
      (HistoryAdjointCasimir.dimension N : ℝ) * ∑' j, scalarHeat (j + J))) atTop (𝓝 0)
  simpa only [mul_zero, add_zero] using
    ((hf.const_mul ((HistoryAdjointCasimir.dimension N : ℝ) ^ 2)).add
      (hs.const_mul (HistoryAdjointCasimir.dimension N : ℝ))).const_mul frequencyMass

/-- A finite omitted set is bounded by the tail of the same summable
majorant. The shift is an injective reindexing of actual omitted rows. -/
private theorem finite_tail_le (f g : ℕ → ℝ) (hg : Summable g)
    (hg0 : ∀ k, 0 ≤ g k) (hfg : ∀ k, f k ≤ g k) (M J : ℕ) :
    (∑ k ∈ (Finset.range M).filter (fun k => J ≤ k), f k) ≤
      ∑' k, g (k + J) := by
  classical
  let s := (Finset.range M).filter (fun k => J ≤ k)
  have hi : ∀ k ∈ s, ∀ l ∈ s, k - J = l - J → k = l := by
    intro k hk l hl he
    have hk' := (Finset.mem_filter.mp hk).2
    have hl' := (Finset.mem_filter.mp hl).2
    omega
  have he : (∑ k ∈ s, g k) = ∑ k ∈ s.image (fun k => k - J), g (k + J) := by
    rw [Finset.sum_image hi]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Nat.sub_add_cancel (Finset.mem_filter.mp hk).2]
  have htail : Summable (fun k => g (k + J)) :=
    hg.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  exact (Finset.sum_le_sum (fun k _ => hfg k)).trans
    (he.trans_le (htail.sum_le_tsum _ (fun k _ => hg0 (k + J))))

def fieldRow (B : ℝ) (m : ℕ) : ℝ :=
  if Even m then (m + 1 : ℕ) *
    ((m + 3 : ℕ) * fieldIntegral B (((m : ℝ) + 2) ^ 2) +
      (m - 1 : ℕ) * fieldIntegral B ((m : ℝ) ^ 2)) else 0

def scalarRow (N : ℕ) (B : ℝ) (j : ℕ) : ℝ :=
  (HistoryAdjointCasimir.dimension N * (2 * j + 1) ^ 2 : ℕ) * positionIntegral N j B

theorem fieldRow_nonneg (B : ℝ) (m : ℕ) : 0 ≤ fieldRow B m := by
  have h (a : ℝ) : 0 ≤ fieldIntegral B a :=
    intervalIntegral.integral_nonneg_of_forall (Real.sqrt_nonneg _)
      (fun _ => (Real.exp_pos _).le)
  unfold fieldRow
  split_ifs
  · exact mul_nonneg (Nat.cast_nonneg _) (add_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (h _)) (mul_nonneg (Nat.cast_nonneg _) (h _)))
  · exact le_rfl

theorem scalarRow_nonneg (N : ℕ) (B : ℝ) (j : ℕ) : 0 ≤ scalarRow N B j := by
  apply mul_nonneg (Nat.cast_nonneg _)
  exact branchIntegral_nonneg N B (positionIndex N j (basePositionLabel N j))

theorem responseTrace_eq_rows (N : ℕ) (B : ℝ) :
    responseTrace N B =
      (HistoryAdjointCasimir.dimension N : ℝ) ^ 2 *
        ∑ m ∈ Finset.range (HistorySpectralWindow.enumerationBound B), fieldRow B m +
      ∑ j ∈ Finset.range (positionCount B), scalarRow N B j := by
  rw [responseTrace_eq_shellTable, shellTable]
  congr 1
  exact Fin.sum_univ_eq_sum_range (scalarRow N B) (positionCount B)

/-- Original spectral rows below `J`; all multiplicities and frequency
intervals are unchanged. -/
def retainedResponse (N : ℕ) (B : ℝ) (J : ℕ) : ℝ :=
  (HistoryAdjointCasimir.dimension N : ℝ) ^ 2 *
    (∑ m ∈ (Finset.range (HistorySpectralWindow.enumerationBound B)).filter
      (fun m => m < J), fieldRow B m) +
    ∑ j ∈ (Finset.range (positionCount B)).filter (fun j => j < J), scalarRow N B j

def omittedResponse (N : ℕ) (B : ℝ) (J : ℕ) : ℝ :=
  (HistoryAdjointCasimir.dimension N : ℝ) ^ 2 *
    (∑ m ∈ (Finset.range (HistorySpectralWindow.enumerationBound B)).filter
      (fun m => J ≤ m), fieldRow B m) +
    ∑ j ∈ (Finset.range (positionCount B)).filter (fun j => J ≤ j), scalarRow N B j

theorem retained_add_omitted (N : ℕ) (B : ℝ) (J : ℕ) :
    retainedResponse N B J + omittedResponse N B J = responseTrace N B := by
  classical
  have h (s : Finset ℕ) (f : ℕ → ℝ) :
      (∑ k ∈ s.filter (fun k => k < J), f k) +
        (∑ k ∈ s.filter (fun k => J ≤ k), f k) = ∑ k ∈ s, f k := by
    simpa only [not_lt] using Finset.sum_filter_add_sum_filter_not s (fun k => k < J) f
  rw [responseTrace_eq_rows]
  unfold retainedResponse omittedResponse
  have hf := h (Finset.range (HistorySpectralWindow.enumerationBound B)) (fieldRow B)
  have hs := h (Finset.range (positionCount B)) (scalarRow N B)
  nlinarith [hf, hs]

theorem omittedResponse_nonneg (N : ℕ) (B : ℝ) (J : ℕ) :
    0 ≤ omittedResponse N B J := by
  unfold omittedResponse
  exact add_nonneg
    (mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun m _ => fieldRow_nonneg B m)))
    (Finset.sum_nonneg (fun j _ => scalarRow_nonneg N B j))

/-- The error certificate applies to the original complete response and
is uniform in its bandwidth. Its tail keeps the actual Gaussian series. -/
theorem omittedResponse_le_rowTail (N : ℕ) (B : ℝ) (J : ℕ) :
    omittedResponse N B J ≤ rowTail N J := by
  have hf := finite_tail_le (fieldRow B) (fun m => fieldHeat m * frequencyMass)
    (summable_fieldHeat.mul_right frequencyMass)
    (fun m => mul_nonneg (fieldHeat_nonneg m) frequencyMass_pos.le)
    (field_row_le_full B) (HistorySpectralWindow.enumerationBound B) J
  have hs := finite_tail_le (scalarRow N B)
    (fun j => (HistoryAdjointCasimir.dimension N : ℝ) * scalarHeat j * frequencyMass)
    ((summable_scalarHeat.mul_left _).mul_right frequencyMass)
    (fun j => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (scalarHeat_nonneg j))
      frequencyMass_pos.le)
    (fun j => by
      have h := mul_le_mul_of_nonneg_left (positionIntegral_le_full N j B)
        (Nat.cast_nonneg (HistoryAdjointCasimir.dimension N * (2 * j + 1) ^ 2))
      simpa only [scalarRow, scalarHeat, Nat.cast_mul, Nat.cast_pow, mul_assoc] using h)
    (positionCount B) J
  simp_rw [tsum_mul_right, tsum_mul_left] at hf hs
  have hf' := mul_le_mul_of_nonneg_left hf
    (sq_nonneg (HistoryAdjointCasimir.dimension N : ℝ))
  unfold omittedResponse rowTail
  nlinarith [hf', hs]

theorem response_error_le_rowTail (N : ℕ) (B : ℝ) (J : ℕ) :
    |responseTrace N B - retainedResponse N B J| ≤ rowTail N J := by
  have he : responseTrace N B - retainedResponse N B J = omittedResponse N B J := by
    linarith [retained_add_omitted N B J]
  rw [he, abs_of_nonneg (omittedResponse_nonneg N B J)]
  exact omittedResponse_le_rowTail N B J

structure Conclusions : Prop where
  complete_content_exhaustion : ∀ N i, ∃ R : ℕ, i ∈ support N (R : ℝ)
  no_finite_full_content : ∀ N B,
    ∃ j, positionIndex N j (basePositionLabel N j) ∉ support N B
  unbounded_position_count : ∀ m, ∃ R : ℕ, m < positionCount (R : ℝ)
  every_finite_count_realized : ∀ m, positionCount (contentEndpoint m : ℝ) = m + 1
  full_field_weights_summable : Summable fieldHeat
  full_scalar_weights_summable : Summable scalarHeat
  full_window_budget : ∀ N B, responseTrace N B ≤ fullBudget N
  vanishing_shell_tail : ∀ N, Tendsto (rowTail N) atTop (𝓝 0)
  exact_row_partition : ∀ N B J,
    retainedResponse N B J + omittedResponse N B J = responseTrace N B
  uniform_original_response_error : ∀ N B J,
    |responseTrace N B - retainedResponse N B J| ≤ rowTail N J

theorem generated : Conclusions where
  complete_content_exhaustion := every_label_visible
  no_finite_full_content := finite_window_omits_position
  unbounded_position_count := position_count_unbounded
  every_finite_count_realized := positionCount_contentEndpoint
  full_field_weights_summable := summable_fieldHeat
  full_scalar_weights_summable := summable_scalarHeat
  full_window_budget := responseTrace_le_fullBudget
  vanishing_shell_tail := rowTail_tendsto_zero
  exact_row_partition := retained_add_omitted
  uniform_original_response_error := response_error_le_rowTail

end GeneratedFoundations.Arithmetic.HistoryHaarSectionExhaustion

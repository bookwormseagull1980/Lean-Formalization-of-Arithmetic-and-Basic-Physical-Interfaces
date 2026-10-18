module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic

/-!
# Finite factorial overlap behind the shared-edge estimate

Minimal-frontier evaluation uses each exact background species at order at
most two.  Consequently the Poisson overlap calculation needs only the
falling-factorial product formula for orders `0`, `1`, and `2`.  This module
proves that finite algebraic identity and the scale-independent polynomial
bounds that produce the constants `7`, `2`, and `1` in the three possible
denominator orders.

No probability law or all-scale estimate is assumed here.  The analytic step
that identifies Poisson factorial moments with powers of the intensity remains
outside this finite algebraic kernel.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Analysis.FinitePoissonOverlap

open scoped BigOperators

/-- Falling factorial as a polynomial over the reals. -/
def falling (x : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => falling x k * (x - k)

@[simp] theorem falling_zero (x : ℝ) : falling x 0 = 1 := rfl
@[simp] theorem falling_one (x : ℝ) : falling x 1 = x := by
  simp [falling]

/-- Exact finite overlap formula for the only local orders admitted by the
minimal-frontier multiplicity bound. -/
theorem falling_mul_falling_of_le_two (x : ℝ) (a b : ℕ)
    (ha : a ≤ 2) (hb : b ≤ 2) :
    falling x a * falling x b =
      ∑ j ∈ Finset.range (min a b + 1),
        ((a.choose j * b.choose j * j.factorial : ℕ) : ℝ) *
          falling x (a + b - j) := by
  interval_cases a <;> interval_cases b <;>
    norm_num [falling, Finset.sum_range_succ] <;> ring

theorem overlap_order_two_two (x : ℝ) :
    falling x 2 * falling x 2 =
      falling x 4 + 4 * falling x 3 + 2 * falling x 2 := by
  norm_num [falling]
  ring

/-- Worst unremoved second-order overlap polynomial for an intensity in the
unit interval. -/
theorem unremoved_second_overlap_le_seven (lambda : ℝ)
    (h0 : 0 ≤ lambda) (h1 : lambda ≤ 1) :
    lambda ^ 4 + 4 * lambda ^ 3 + 2 * lambda ^ 2 ≤ 7 * lambda ^ 2 := by
  have h2 : lambda ^ 2 ≤ lambda := by
    nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)]
  have h3 : lambda ^ 3 ≤ lambda ^ 2 := by
    calc
      lambda ^ 3 = lambda ^ 2 * lambda := by ring
      _ ≤ lambda * lambda := mul_le_mul_of_nonneg_right h2 h0
      _ = lambda ^ 2 := by ring
  have h4 : lambda ^ 4 ≤ lambda ^ 2 := by
    calc
      lambda ^ 4 = lambda ^ 2 * lambda ^ 2 := by ring
      _ ≤ lambda ^ 2 * lambda :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg lambda)
      _ = lambda ^ 3 := by ring
      _ ≤ lambda ^ 2 := h3
  linarith

/-- Removing one shared input lowers the worst local polynomial constant from
`7` to `2`. -/
theorem once_removed_second_overlap_le_two (lambda : ℝ)
    (h0 : 0 ≤ lambda) (h1 : lambda ≤ 1) :
    lambda ^ 3 + lambda ^ 2 ≤ 2 * lambda ^ 2 := by
  have h2 : lambda ^ 2 ≤ lambda := by
    nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)]
  have h3 : lambda ^ 3 ≤ lambda ^ 2 := by
    calc
      lambda ^ 3 = lambda ^ 2 * lambda := by ring
      _ ≤ lambda * lambda := mul_le_mul_of_nonneg_right h2 h0
      _ = lambda ^ 2 := by ring
  linarith

structure Conclusions : Prop where
  finite_overlap : ∀ (x : ℝ) (a b : ℕ), a ≤ 2 → b ≤ 2 →
    falling x a * falling x b =
      ∑ j ∈ Finset.range (min a b + 1),
        ((a.choose j * b.choose j * j.factorial : ℕ) : ℝ) *
          falling x (a + b - j)
  unit_intensity_constant : ∀ lambda : ℝ, 0 ≤ lambda → lambda ≤ 1 →
    lambda ^ 4 + 4 * lambda ^ 3 + 2 * lambda ^ 2 ≤ 7 * lambda ^ 2
  once_removed_constant : ∀ lambda : ℝ, 0 ≤ lambda → lambda ≤ 1 →
    lambda ^ 3 + lambda ^ 2 ≤ 2 * lambda ^ 2

theorem finitePoissonOverlapConclusions : Conclusions where
  finite_overlap := falling_mul_falling_of_le_two
  unit_intensity_constant := unremoved_second_overlap_le_seven
  once_removed_constant := once_removed_second_overlap_le_two

end GeneratedFoundations.Analysis.FinitePoissonOverlap

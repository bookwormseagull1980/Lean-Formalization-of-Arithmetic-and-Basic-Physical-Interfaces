module

public import GeneratedFoundations.Arithmetic.DifferenceRing
public import Mathlib.Algebra.Order.Ring.Defs

/-!
# The native positive cone in the difference ring

The order is defined by adding an embedded mode. Its formula on pairs follows
from the quotient relation and the native additive order. Thus positivity is
established internally, without transferring an order from the integers.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Arithmetic.NativeModes.Differences

instance : LE Difference := ⟨fun x y => ∃ a : Mode, y = x + ofMode a⟩

theorem pair_le_pair (a b c d : Mode) : pair a b ≤ pair c d ↔ a + d ≤ c + b := by
  constructor
  · rintro ⟨w, hw⟩
    change pair c d = pair a b + pair w 0 at hw
    rw [pair_add, add_zero] at hw
    have h := pair_eq_pair.mp hw
    apply (native_le_iff_exists_add _ _).mpr
    exact ⟨w, by simpa [add_assoc, add_comm, add_left_comm] using h⟩
  · intro h
    obtain ⟨w, hw⟩ := (native_le_iff_exists_add _ _).mp h
    refine ⟨w, ?_⟩
    change pair c d = pair a b + pair w 0
    rw [pair_add, add_zero]
    apply pair_eq_pair.mpr
    simpa [add_assoc, add_comm, add_left_comm] using hw

instance : PartialOrder Difference where
  le_refl x := ⟨0, by simp⟩
  le_trans x y z hxy hyz := by
    obtain ⟨a, ha⟩ := hxy
    obtain ⟨b, hb⟩ := hyz
    refine ⟨a + b, ?_⟩
    rw [hb, ha, map_add, add_assoc]
  le_antisymm x y hxy hyx := by
    induction x, y using Quotient.inductionOn₂ with | _ p q =>
      apply pair_eq_pair.mpr
      exact le_antisymm ((pair_le_pair _ _ _ _).mp hxy)
        ((pair_le_pair _ _ _ _).mp hyx)

instance : LinearOrder Difference where
  __ : PartialOrder Difference := inferInstance
  le_total x y := by
    induction x, y using Quotient.inductionOn₂ with | _ p q =>
      exact (le_total (p.1 + q.2) (q.1 + p.2)).imp
        ((pair_le_pair _ _ _ _).mpr) ((pair_le_pair _ _ _ _).mpr)
  toDecidableLE x y := Classical.propDecidable (x ≤ y)

@[simp] theorem ofMode_eq_zero_iff (a : Mode) : ofMode a = 0 ↔ a = 0 := by
  rw [← map_zero ofMode, ofMode_injective.eq_iff]

@[simp] theorem ofMode_le_iff (a b : Mode) : ofMode a ≤ ofMode b ↔ a ≤ b := by
  change pair a 0 ≤ pair b 0 ↔ a ≤ b
  simpa only [add_zero] using pair_le_pair a 0 b 0

theorem nonnegative_iff_native (x : Difference) : 0 ≤ x ↔ ∃ a : Mode, ofMode a = x := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, by simpa using ha.symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, by simp⟩

theorem positive_iff_native (x : Difference) :
    0 < x ↔ ∃ a : Mode, a ≠ 0 ∧ ofMode a = x := by
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := (nonnegative_iff_native x).mp hx.le
    refine ⟨a, ?_, ha⟩
    intro hz
    exact hx.ne' (by simpa [hz] using ha.symm)
  · rintro ⟨a, ha, rfl⟩
    exact lt_of_le_of_ne ((nonnegative_iff_native _).mpr ⟨a, rfl⟩)
      (Ne.symm ((ofMode_eq_zero_iff a).not.mpr ha))

theorem positive_native_unique {x : Difference} (hx : 0 < x) :
    ∃! a : Mode, a ≠ 0 ∧ ofMode a = x := by
  obtain ⟨a, ha, hax⟩ := (positive_iff_native x).mp hx
  exact ⟨a, ⟨ha, hax⟩, fun b hb => ofMode_injective (hb.2.trans hax.symm)⟩

instance : IsOrderedAddMonoid Difference where
  add_le_add_left a b hab c := by
    obtain ⟨w, hw⟩ := hab
    refine ⟨w, ?_⟩
    rw [hw]
    ring

instance : ZeroLEOneClass Difference := ⟨⟨1, by simp⟩⟩

instance : Nontrivial Difference := by
  refine ⟨⟨ofMode 0, ofMode 1, ?_⟩⟩
  intro h
  have hi := congrArg index (ofMode_injective h)
  norm_num at hi

theorem native_positive_mul (x y : Difference) (hx : 0 < x) (hy : 0 < y) : 0 < x * y := by
  obtain ⟨a, ha, rfl⟩ := (positive_iff_native x).mp hx
  obtain ⟨b, hb, rfl⟩ := (positive_iff_native y).mp hy
  rw [← map_mul]
  exact (positive_iff_native _).mpr ⟨a * b, native_mul_ne_zero ha hb, rfl⟩

instance : IsStrictOrderedRing Difference := .of_mul_pos native_positive_mul

theorem difference_is_integral_domain : IsDomain Difference := inferInstance

end GeneratedFoundations.Arithmetic.NativeModes.Differences

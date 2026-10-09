module

public import GeneratedFoundations.Arithmetic.InternalDivision
public import Mathlib.Tactic.Ring

/-!
# Euclidean descent and a native Bézout certificate

The gcd is constructed by decreasing native remainders. A Bézout certificate
is retained as an equality of positive and negative parts in the original
semiring. Its interpretation in the additive group completion is separate
from this construction. No natural-number gcd or factorization result is used.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Arithmetic.NativeModes

theorem native_dvd_add {d u v : Mode} (hu : d ∣ u) (hv : d ∣ v) : d ∣ u + v := by
  obtain ⟨a, rfl⟩ := hu
  obtain ⟨b, rfl⟩ := hv
  exact ⟨a + b, (mul_add d a b).symm⟩

theorem native_dvd_mul_right {d u : Mode} (hu : d ∣ u) (v : Mode) : d ∣ u * v := by
  obtain ⟨a, rfl⟩ := hu
  exact ⟨a * v, (mul_assoc d a v).symm⟩

/-- A common divisor survives subtraction whenever the difference is a
native mode. Positivity and additive cancellation supply the witness. -/
theorem native_dvd_of_dvd_add {d u v : Mode} (hu : d ∣ u) (huv : d ∣ u + v) : d ∣ v := by
  obtain ⟨a, ha⟩ := hu
  obtain ⟨b, hb⟩ := huv
  by_cases hd : d = 0
  · have hu0 : u = 0 := by simpa [hd] using ha
    have hv0 : v = 0 := by simpa [hd, hu0] using hb
    exact ⟨0, by simp [hv0]⟩
  · have hmul : d * a ≤ d * b := by
      apply (native_le_iff_exists_add _ _).mpr
      exact ⟨v, by rw [← ha, ← hb]⟩
    have hab : a ≤ b := by
      by_contra h
      exact (not_le_of_gt ((native_mul_strictMono hd) (lt_of_not_ge h))) hmul
    obtain ⟨c, hc⟩ := (native_le_iff_exists_add a b).mp hab
    refine ⟨c, ?_⟩
    apply native_add_cancel_left (u := u)
    rw [hb, hc, mul_add, ← ha]

def NativeGcd (g x y : Mode) : Prop :=
  g ∣ x ∧ g ∣ y ∧ ∀ d : Mode, d ∣ x → d ∣ y → d ∣ g

def BezoutCertificate (g x y : Mode) : Prop :=
  ∃ a b c d : Mode, g + c * x + d * y = a * x + b * y

theorem native_gcd_bezout (x y : Mode) : ∃ g : Mode, NativeGcd g x y ∧ BezoutCertificate g x y := by
  have hrec : ∀ n : ℕ, ∀ y : Mode, index y = n → ∀ x : Mode,
      ∃ g : Mode, NativeGcd g x y ∧ BezoutCertificate g x y := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro y hy x
      by_cases hy0 : y = 0
      · subst y
        refine ⟨x, ⟨dvd_refl x, dvd_zero x, fun _ hd _ => hd⟩,
          1, 0, 0, 0, ?_⟩
        simp
      · obtain ⟨q, r, hx, hr⟩ := native_division_exists x y hy0
        have hsmall : index r < n := by
          rw [← hy]
          exact hr
        obtain ⟨g, hg, a, b, c, d, hbez⟩ := ih (index r) hsmall r rfl y
        refine ⟨g, ?_, b, a + d * q, d, c + b * q, ?_⟩
        · refine ⟨?_, hg.1, ?_⟩
          · rw [hx]
            exact native_dvd_add (native_dvd_mul_right hg.1 q) hg.2.1
          · intro k hkx hky
            apply hg.2.2 k hky
            apply native_dvd_of_dvd_add (native_dvd_mul_right hky q)
            simpa only [← hx] using hkx
        · calc
            g + d * x + (c + b * q) * y =
                (g + c * y + d * r) + (d * q * y + b * q * y) := by
                  rw [hx]
                  ring
            _ = (a * y + b * r) + (d * q * y + b * q * y) := by rw [hbez]
            _ = b * x + (a + d * q) * y := by rw [hx]; ring
  exact hrec (index y) y rfl x

theorem native_dvd_antisymm {u v : Mode} (huv : u ∣ v) (hvu : v ∣ u) : u = v := by
  by_cases hu : u = 0
  · obtain ⟨a, ha⟩ := huv
    simpa [hu] using ha.symm
  · obtain ⟨a, ha⟩ := huv
    obtain ⟨b, hb⟩ := hvu
    have hab : a * b = 1 := by
      apply native_mul_cancel_left hu
      rw [← mul_assoc, ← ha, ← hb, mul_one]
    have hi := congrArg index hab
    simp only [index_mul, index_one] at hi
    have ha1 : a = 1 := by
      apply index_injective
      simpa only [index_one] using Nat.eq_one_of_mul_eq_one_right hi
    simpa [ha1] using ha.symm

theorem native_gcd_unique {g h x y : Mode} (hg : NativeGcd g x y)
    (hh : NativeGcd h x y) : g = h :=
  native_dvd_antisymm (hh.2.2 g hg.1 hg.2.1) (hg.2.2 h hh.1 hh.2.1)

theorem native_gcd_existsUnique (x y : Mode) :
    ∃! g : Mode, NativeGcd g x y ∧ BezoutCertificate g x y := by
  obtain ⟨g, hg, hbez⟩ := native_gcd_bezout x y
  exact ⟨g, ⟨hg, hbez⟩, fun h hh => native_gcd_unique hh.1 hg⟩

end GeneratedFoundations.Arithmetic.NativeModes

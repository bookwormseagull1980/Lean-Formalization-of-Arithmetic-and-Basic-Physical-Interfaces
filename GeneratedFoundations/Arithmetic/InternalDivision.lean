module

public import GeneratedFoundations.Arithmetic.NativePeano
public import Mathlib.Order.Basic

/-!
# Division by successor induction on the native modes

The order is the additive order of the actual circle-map semiring. The
successor-chain length checks its order properties. Quotients and remainders
are constructed by native successor induction; no natural-number division,
gcd, primality or factorization theorem is used.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Arithmetic.NativeModes

theorem index_injective : Function.Injective index := by
  intro u v h
  simpa using congrArg powerMode h

@[simp] theorem index_one : index (1 : Mode) = 1 := by
  simpa only [powerMode_one] using index_powerMode 1

@[simp] theorem index_add (u v : Mode) : index (u + v) = index u + index v := by
  apply powerMode_injective
  simp [powerMode_add]

@[simp] theorem index_mul (u v : Mode) : index (u * v) = index u * index v := by
  apply powerMode_injective
  simp [powerMode_mul]

@[simp] theorem index_eq_zero_iff (u : Mode) : index u = 0 ↔ u = 0 := by
  constructor
  · intro h
    apply index_injective
    simpa using h
  · rintro rfl
    exact index_zero

instance : LinearOrder Mode := LinearOrder.lift' index index_injective

theorem native_le_iff_index_le (u v : Mode) : u ≤ v ↔ index u ≤ index v := Iff.rfl

theorem native_lt_iff_index_lt (u v : Mode) : u < v ↔ index u < index v := Iff.rfl

theorem native_le_iff_exists_add (u v : Mode) : u ≤ v ↔ ∃ w, v = u + w := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le h
    refine ⟨powerMode n, index_injective ?_⟩
    simpa only [index_add, index_powerMode] using hn
  · rintro ⟨w, rfl⟩
    change index u ≤ index (u + w)
    rw [index_add]
    exact Nat.le_add_right _ _

theorem native_lt_iff_exists_add (u v : Mode) :
    u < v ↔ ∃ w, w ≠ 0 ∧ v = u + w := by
  constructor
  · intro h
    obtain ⟨w, hw⟩ := (native_le_iff_exists_add u v).mp h.le
    refine ⟨w, ?_, hw⟩
    intro hz
    simp only [hz, add_zero] at hw
    exact (ne_of_lt h) hw.symm
  · rintro ⟨w, hw, rfl⟩
    change index u < index (u + w)
    rw [index_add]
    exact Nat.lt_add_of_pos_right (Nat.pos_of_ne_zero ((index_eq_zero_iff w).not.mpr hw))

theorem native_nonnegative (u : Mode) : 0 ≤ u := by
  change index 0 ≤ index u
  simp

theorem native_positive_iff (u : Mode) : 0 < u ↔ u ≠ 0 :=
  lt_iff_le_and_ne.trans (by simp [native_nonnegative u, ne_comm])

theorem native_add_cancel_left {u v w : Mode} (h : u + v = u + w) : v = w := by
  apply ext
  intro z
  have hz := congrArg (fun x : Mode => x z) h
  exact mul_left_cancel hz

theorem native_mul_ne_zero {u v : Mode} (hu : u ≠ 0) (hv : v ≠ 0) : u * v ≠ 0 := by
  intro h
  have hi := congrArg index h
  rw [index_mul, index_zero] at hi
  exact (Nat.mul_ne_zero ((index_eq_zero_iff u).not.mpr hu)
    ((index_eq_zero_iff v).not.mpr hv)) hi

theorem native_mul_strictMono {d : Mode} (hd : d ≠ 0) : StrictMono (fun x : Mode => d * x) := by
  intro u v huv
  obtain ⟨w, hw, rfl⟩ := (native_lt_iff_exists_add u v).mp huv
  exact (native_lt_iff_exists_add _ _).mpr
    ⟨d * w, native_mul_ne_zero hd hw, mul_add d u w⟩

theorem native_mul_cancel_left {d u v : Mode} (hd : d ≠ 0) (h : d * u = d * v) : u = v :=
  (native_mul_strictMono hd).injective h

theorem native_successor_le_of_lt {r d : Mode} (h : r < d) : successor r ≤ d := by
  change index (successor r) ≤ index d
  rw [index_successor]
  exact Nat.succ_le_of_lt h

theorem native_successor_lt_of_ne {r d : Mode} (h : r < d) (hne : successor r ≠ d) :
    successor r < d := lt_of_le_of_ne (native_successor_le_of_lt h) hne

theorem native_division_exists (x d : Mode) (hd : d ≠ 0) :
    ∃ q r : Mode, x = d * q + r ∧ r < d := by
  apply successor_induction (P := fun x => ∃ q r : Mode, x = d * q + r ∧ r < d)
  · exact ⟨0, 0, by simp, (native_positive_iff d).mpr hd⟩
  · intro u hu
    obtain ⟨q, r, hq, hr⟩ := hu
    by_cases hnext : successor r = d
    · refine ⟨successor q, 0, ?_, (native_positive_iff d).mpr hd⟩
      change u + 1 = d * (q + 1) + 0
      have hrd : r + 1 = d := hnext
      rw [hq, add_assoc, hrd]
      simp [mul_add]
    · refine ⟨q, successor r, ?_, native_successor_lt_of_ne hr hnext⟩
      simp only [successor, hq, add_assoc]

/-- Any smaller quotient would leave at least one whole divisor in its
remainder. The argument uses the additive order and cancellation. -/
theorem native_division_quotient_not_lt {x d q r q' r' : Mode}
    (hx : x = d * q + r) (hx' : x = d * q' + r') (hr : r < d) : ¬q < q' := by
  intro hq
  obtain ⟨w, hw, hqw⟩ := (native_lt_iff_exists_add q q').mp hq
  have hwpos : 0 < w := (native_positive_iff w).mpr hw
  have hwone : 1 ≤ w := by
    change index 1 ≤ index w
    rw [index_one]
    have hi : 0 < index w := by simpa only [native_lt_iff_index_lt, index_zero] using hwpos
    exact hi
  obtain ⟨a, ha⟩ := (native_le_iff_exists_add 1 w).mp hwone
  have hr' : r = d * w + r' := by
    apply native_add_cancel_left (u := d * q)
    calc
      d * q + r = x := hx.symm
      _ = d * q' + r' := hx'
      _ = d * q + (d * w + r') := by rw [hqw, mul_add, add_assoc]
  have hdr : d ≤ r := (native_le_iff_exists_add d r).mpr
    ⟨d * a + r', by rw [hr', ha, mul_add, mul_one, add_assoc]⟩
  exact (not_le_of_gt hr) hdr

theorem native_division_pair_unique {x d : Mode} {p p' : Mode × Mode}
    (hp : x = d * p.1 + p.2 ∧ p.2 < d)
    (hp' : x = d * p'.1 + p'.2 ∧ p'.2 < d) : p = p' := by
  have hq : p.1 = p'.1 := le_antisymm
    (le_of_not_gt (native_division_quotient_not_lt hp'.1 hp.1 hp'.2))
    (le_of_not_gt (native_division_quotient_not_lt hp.1 hp'.1 hp.2))
  apply Prod.ext hq
  apply native_add_cancel_left (u := d * p.1)
  rw [← hp.1, hq, ← hp'.1]

theorem native_division_existsUnique (x d : Mode) (hd : d ≠ 0) :
    ∃! p : Mode × Mode, x = d * p.1 + p.2 ∧ p.2 < d := by
  obtain ⟨q, r, hx, hr⟩ := native_division_exists x d hd
  exact ⟨(q, r), ⟨hx, hr⟩, fun p hp => native_division_pair_unique hp ⟨hx, hr⟩⟩

end GeneratedFoundations.Arithmetic.NativeModes

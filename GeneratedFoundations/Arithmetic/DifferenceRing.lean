module

public import GeneratedFoundations.Arithmetic.InternalEuclid
public import Mathlib.Data.Quot

/-!
# The difference ring of the native mode semiring

The carrier is the quotient of pairs of actual modes by additive cancellation.
Addition and multiplication descend from the two semiring operations. The
ring laws and the embedding are proved on these representatives, before any
comparison with the standard integers.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Arithmetic.NativeModes

namespace Differences

def Related (p q : Mode × Mode) : Prop := p.1 + q.2 = q.1 + p.2

theorem related_trans {p q r : Mode × Mode} (hpq : Related p q)
    (hqr : Related q r) : Related p r := by
  apply native_add_cancel_left (u := q.2)
  calc
    _ = (p.1 + q.2) + r.2 := by ring
    _ = (q.1 + p.2) + r.2 := by rw [hpq]
    _ = (q.1 + r.2) + p.2 := by ring
    _ = (r.1 + q.2) + p.2 := by rw [hqr]
    _ = _ := by ring

instance pairSetoid : Setoid (Mode × Mode) where
  r := Related
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h k => related_trans h k⟩

def Difference := Quotient pairSetoid

def pair (a b : Mode) : Difference := Quotient.mk pairSetoid (a, b)

theorem pair_eq_pair {a b c d : Mode} : pair a b = pair c d ↔ a + d = c + b :=
  Quotient.eq

def pairAdd (p q : Mode × Mode) : Mode × Mode := (p.1 + q.1, p.2 + q.2)

def pairMul (p q : Mode × Mode) : Mode × Mode :=
  (p.1 * q.1 + p.2 * q.2, p.1 * q.2 + p.2 * q.1)

theorem pairAdd_related {p p' q q' : Mode × Mode} (hp : Related p p')
    (hq : Related q q') : Related (pairAdd p q) (pairAdd p' q') := by
  change (p.1 + q.1) + (p'.2 + q'.2) = (p'.1 + q'.1) + (p.2 + q.2)
  calc
    _ = (p.1 + p'.2) + (q.1 + q'.2) := by ring
    _ = (p'.1 + p.2) + (q'.1 + q.2) := by rw [hp, hq]
    _ = _ := by ring

theorem pairMul_comm (p q : Mode × Mode) : pairMul p q = pairMul q p := by
  apply Prod.ext <;> dsimp [pairMul] <;> ring

theorem pairMul_related_left {p p' : Mode × Mode} (hp : Related p p')
    (q : Mode × Mode) : Related (pairMul p q) (pairMul p' q) := by
  change (p.1 * q.1 + p.2 * q.2) + (p'.1 * q.2 + p'.2 * q.1) =
    (p'.1 * q.1 + p'.2 * q.2) + (p.1 * q.2 + p.2 * q.1)
  calc
    _ = (p.1 + p'.2) * q.1 + (p'.1 + p.2) * q.2 := by ring
    _ = (p'.1 + p.2) * q.1 + (p.1 + p'.2) * q.2 := by rw [hp]
    _ = _ := by ring

theorem pairMul_related {p p' q q' : Mode × Mode} (hp : Related p p')
    (hq : Related q q') : Related (pairMul p q) (pairMul p' q') := by
  apply related_trans (pairMul_related_left hp q)
  rw [pairMul_comm p' q, pairMul_comm p' q']
  exact pairMul_related_left hq p'

instance : Zero Difference := ⟨pair 0 0⟩
instance : One Difference := ⟨pair 1 0⟩
instance : Add Difference := ⟨Quotient.map₂ pairAdd (fun {_ _} hp {_ _} hq => pairAdd_related hp hq)⟩
instance : Mul Difference := ⟨Quotient.map₂ pairMul (fun {_ _} hp {_ _} hq => pairMul_related hp hq)⟩
instance : Neg Difference := ⟨Quotient.map Prod.swap (by
  intro p q h
  change p.2 + q.1 = q.2 + p.1
  simpa only [add_comm] using h.symm)⟩

@[simp] theorem pair_zero : pair 0 0 = 0 := rfl
@[simp] theorem pair_one : pair 1 0 = 1 := rfl
@[simp] theorem pair_add (a b c d : Mode) :
    pair a b + pair c d = pair (a + c) (b + d) := rfl
@[simp] theorem pair_mul (a b c d : Mode) :
    pair a b * pair c d = pair (a * c + b * d) (a * d + b * c) := rfl
@[simp] theorem pair_neg (a b : Mode) : -pair a b = pair b a := rfl

instance : CommRing Difference where
  add_assoc x y z := by
    induction x, y, z using Quotient.inductionOn₃ with | _ p q r =>
      apply Quotient.sound
      change Related _ _
      dsimp [pairAdd, Related]
      ring
  zero_add x := by
    induction x using Quotient.inductionOn with | _ p =>
      apply Quotient.sound
      change Related _ _
      dsimp [pairAdd, Related]
      ring
  add_zero x := by
    induction x using Quotient.inductionOn with | _ p =>
      apply Quotient.sound
      change Related _ _
      dsimp [pairAdd, Related]
      ring
  add_comm x y := by
    induction x, y using Quotient.inductionOn₂ with | _ p q =>
      apply Quotient.sound
      change Related _ _
      dsimp [pairAdd, Related]
      ring
  neg_add_cancel x := by
    induction x using Quotient.inductionOn with | _ p =>
      apply Quotient.sound
      change Related _ _
      dsimp [pairAdd, Related]
      ring
  nsmul := nsmulRec
  zsmul := zsmulRec
  mul_assoc x y z := by
    induction x, y, z using Quotient.inductionOn₃ with | _ p q r =>
      apply Quotient.sound
      change Related _ _
      dsimp [pairMul, Related]
      ring
  one_mul x := by
    induction x using Quotient.inductionOn with | _ p =>
      apply Quotient.sound
      change Related _ _
      dsimp [pairMul, Related]
      ring
  mul_one x := by
    induction x using Quotient.inductionOn with | _ p =>
      apply Quotient.sound
      change Related _ _
      dsimp [pairMul, Related]
      ring
  mul_comm x y := by
    induction x, y using Quotient.inductionOn₂ with | _ p q =>
      apply Quotient.sound
      change Related _ _
      dsimp [pairMul, Related]
      ring
  zero_mul x := by
    induction x using Quotient.inductionOn with | _ p =>
      apply Quotient.sound
      change Related _ _
      dsimp [pairMul, Related]
      ring
  mul_zero x := by
    induction x using Quotient.inductionOn with | _ p =>
      apply Quotient.sound
      change Related _ _
      dsimp [pairMul, Related]
      ring
  left_distrib x y z := by
    induction x, y, z using Quotient.inductionOn₃ with | _ p q r =>
      apply Quotient.sound
      change Related _ _
      dsimp [pairMul, pairAdd, Related]
      ring
  right_distrib x y z := by
    induction x, y, z using Quotient.inductionOn₃ with | _ p q r =>
      apply Quotient.sound
      change Related _ _
      dsimp [pairMul, pairAdd, Related]
      ring
  npow := npowRec
  natCast n := pair (powerMode n) 0
  natCast_zero := by simp
  natCast_succ n := by
    change pair (powerMode (n + 1)) 0 = pair (powerMode n) 0 + pair 1 0
    rw [pair_add, powerMode_add, powerMode_one, zero_add]

def ofMode : Mode →+* Difference where
  toFun a := pair a 0
  map_zero' := rfl
  map_one' := rfl
  map_add' a b := by simp
  map_mul' a b := by simp

theorem ofMode_injective : Function.Injective ofMode := by
  intro a b h
  simpa only [ofMode, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    pair_eq_pair, add_zero] using h

theorem pair_eq_sub (a b : Mode) : pair a b = ofMode a - ofMode b := by
  simp [ofMode, sub_eq_add_neg]

theorem difference_induction {P : Difference → Prop}
    (h : ∀ a b : Mode, P (ofMode a - ofMode b)) (x : Difference) : P x := by
  induction x using Quotient.inductionOn with | _ p =>
    change P (pair p.1 p.2)
    rw [pair_eq_sub]
    exact h p.1 p.2

theorem every_difference_has_sign (x : Difference) :
    (∃ a : Mode, x = ofMode a) ∨ ∃ a : Mode, x = -ofMode a := by
  induction x using Quotient.inductionOn with | _ p =>
    rcases le_total p.1 p.2 with h | h
    · obtain ⟨w, hw⟩ := (native_le_iff_exists_add _ _).mp h
      right
      refine ⟨w, ?_⟩
      change pair p.1 p.2 = pair 0 w
      apply pair_eq_pair.mpr
      simpa using hw.symm
    · obtain ⟨w, hw⟩ := (native_le_iff_exists_add _ _).mp h
      left
      refine ⟨w, ?_⟩
      apply pair_eq_pair.mpr
      simpa [add_comm] using hw

theorem bezout_in_difference_ring (x y : Mode) :
    ∃ g : Mode, NativeGcd g x y ∧ ∃ A B : Difference,
      ofMode g = A * ofMode x + B * ofMode y := by
  obtain ⟨g, hg, a, b, c, d, hbez⟩ := native_gcd_bezout x y
  refine ⟨g, hg, ofMode a - ofMode c, ofMode b - ofMode d, ?_⟩
  have h := congrArg ofMode hbez
  simp only [map_add, map_mul] at h
  have heq : ofMode g + (ofMode c * ofMode x + ofMode d * ofMode y) =
      ((ofMode a - ofMode c) * ofMode x + (ofMode b - ofMode d) * ofMode y) +
        (ofMode c * ofMode x + ofMode d * ofMode y) := by
    calc
      _ = ofMode a * ofMode x + ofMode b * ofMode y := by simpa [add_assoc] using h
      _ = _ := by ring
  exact add_right_cancel heq

end Differences

end GeneratedFoundations.Arithmetic.NativeModes

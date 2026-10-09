module

public import GeneratedFoundations.Arithmetic.CircleEndomorphisms

/-!
# Nonnegative circle modes

The elements are continuous maps of the unit circle. Modulation is pointwise
multiplication and multiplication is composition. The identification of this
family with the oriented Neumann modes belongs to the spectral construction.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Arithmetic.NativeModes

open CircleEndomorphisms

def Mode := {u : Circle →ₜ* Circle // ∃ n : ℕ, u = powerEndomorphism n}

instance : CoeFun Mode (fun _ => Circle → Circle) := ⟨fun u => u.val⟩

@[ext] theorem ext {u v : Mode} (h : ∀ z : Circle, u z = v z) : u = v := by
  apply Subtype.ext
  exact DFunLike.ext _ _ h

def powerMode (n : ℕ) : Mode := ⟨powerEndomorphism n, n, rfl⟩

@[simp] theorem powerMode_apply (n : ℕ) (z : Circle) : powerMode n z = z ^ n := by
  simp [powerMode]

theorem powerMode_injective : Function.Injective powerMode := by
  intro m n h
  have hi := powerEndomorphism_injective (congrArg Subtype.val h)
  exact_mod_cast hi

theorem powerMode_surjective : Function.Surjective powerMode := by
  intro u
  obtain ⟨n, hn⟩ := u.property
  exact ⟨n, Subtype.ext hn.symm⟩

def zeroMode : Mode := ⟨1, 0, by ext z; simp⟩

def unitMode : Mode := ⟨ContinuousMonoidHom.id Circle, 1, by ext z; simp⟩

def modulate (u v : Mode) : Mode :=
  ⟨u.val * v.val, by
    obtain ⟨m, hm⟩ := u.property
    obtain ⟨n, hn⟩ := v.property
    refine ⟨m + n, ?_⟩
    rw [hm, hn]
    ext z
    simp [zpow_add]
  ⟩

def compose (u v : Mode) : Mode :=
  ⟨u.val.comp v.val, by
    obtain ⟨m, hm⟩ := u.property
    obtain ⟨n, hn⟩ := v.property
    refine ⟨m * n, ?_⟩
    rw [hm, hn]
    apply DFunLike.ext
    intro z
    change (z ^ (n : ℤ)) ^ (m : ℤ) = z ^ ((m * n : ℕ) : ℤ)
    rw [← zpow_mul, Nat.cast_mul, mul_comm]
  ⟩

instance : Zero Mode := ⟨zeroMode⟩
instance : One Mode := ⟨unitMode⟩
instance : Add Mode := ⟨modulate⟩
instance : Mul Mode := ⟨compose⟩

@[simp] theorem zero_apply (z : Circle) : (0 : Mode) z = 1 := rfl
@[simp] theorem one_apply (z : Circle) : (1 : Mode) z = z := rfl
@[simp] theorem add_apply (u v : Mode) (z : Circle) : (u + v) z = u z * v z := rfl
@[simp] theorem mul_apply (u v : Mode) (z : Circle) : (u * v) z = u (v z) := rfl

@[simp] theorem powerMode_zero : powerMode 0 = 0 := by ext z; simp
@[simp] theorem powerMode_one : powerMode 1 = 1 := by ext z; simp

theorem powerMode_add (m n : ℕ) : powerMode (m + n) = powerMode m + powerMode n := by
  ext z
  simp [pow_add]

theorem powerMode_mul (m n : ℕ) : powerMode (m * n) = powerMode m * powerMode n := by
  ext z
  simp [← pow_mul, Nat.mul_comm]

theorem composition_comm (u v : Mode) : u * v = v * u := by
  obtain ⟨m, rfl⟩ := powerMode_surjective u
  obtain ⟨n, rfl⟩ := powerMode_surjective v
  rw [← powerMode_mul, ← powerMode_mul, Nat.mul_comm]

instance instCommSemiringMode : CommSemiring Mode where
  add_assoc u v w := by ext z; simp [mul_assoc]
  zero_add u := by ext z; simp
  add_zero u := by ext z; simp
  add_comm u v := by ext z; simp [mul_comm]
  nsmul := nsmulRec
  mul_assoc u v w := by ext z; rfl
  one_mul u := by ext z; rfl
  mul_one u := by ext z; rfl
  npow := npowRec
  left_distrib u v w := by apply ext; intro z; exact u.val.map_mul (v z) (w z)
  right_distrib u v w := by ext z; rfl
  zero_mul u := by ext z; rfl
  mul_zero u := by apply ext; intro z; exact u.val.map_one
  mul_comm := composition_comm
  natCast := powerMode
  natCast_zero := powerMode_zero
  natCast_succ n := by rw [powerMode_add, powerMode_one]

/-- Modulation by the first positive mode. -/
def successor (u : Mode) : Mode := u + 1

@[simp] theorem successor_powerMode (n : ℕ) :
    successor (powerMode n) = powerMode (n + 1) := by
  simp [successor, powerMode_add]

theorem successor_injective : Function.Injective successor := by
  intro u v h
  apply ext
  intro z
  have hz := congrArg (fun w : Mode => w z) h
  change u z * z = v z * z at hz
  exact mul_right_cancel hz

theorem successor_ne_zero (u : Mode) : successor u ≠ 0 := by
  obtain ⟨n, rfl⟩ := powerMode_surjective u
  rw [successor_powerMode, ← powerMode_zero]
  exact fun h => Nat.succ_ne_zero n (powerMode_injective h)

theorem successor_induction {P : Mode → Prop} (hzero : P 0)
    (hstep : ∀ u, P u → P (successor u)) : ∀ u, P u := by
  intro u
  obtain ⟨n, rfl⟩ := powerMode_surjective u
  induction n with
  | zero => simpa using hzero
  | succ n ih => simpa using hstep (powerMode n) ih

end GeneratedFoundations.Arithmetic.NativeModes

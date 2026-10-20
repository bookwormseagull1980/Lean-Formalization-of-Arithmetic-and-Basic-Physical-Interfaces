module

public import GeneratedFoundations.Arithmetic.HistoryRelativeCharge
public import GeneratedFoundations.Operations.SourceCliffordSectors

/-!
# The residual character of a generated phase fibre and its source sectors

The invariant/detail relative weights have already been derived from the
actual phase-average ranks: `(-n,1)`. They are combined here with the source
right Cartan weights `0,0,1,-1`. Fixing the invariant upper right sector
determines their relative coefficient; primitive positive orientation then
determines the integer character. These are comparison conditions on
competing characters, not parameters supplied to the canonical source.

The actual nontrivial phase fibres have `n > 0`. The formulas also retain
the degenerate value `n = 0`; its virtual detail weights are not asserted
to be occupied. At `n = 1` a second neutral sector occurs. Neither this
exception nor the actual history multiplicities may be replaced by the
physical sixteen-component carrier.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Arithmetic.HistoryJointChargeLattice

abbrev Spin := Operations.SourceCliffordConnector.ChiralIndex
abbrev Sector := Bool × Spin

def relativeWeight (n : ℕ) : Bool → ℤ
  | false => -(n : ℤ)
  | true => 1

def rightWeight : Spin → ℤ
  | .inl _ => 0
  | .inr i => if i = 0 then 1 else -1

def weight (n : ℕ) (r b : ℤ) (p : Sector) : ℤ :=
  r * rightWeight p.2 + b * relativeWeight n p.1

def generatedWeight (n : ℕ) : Sector → ℤ := weight n n 1

def Primitive (n : ℕ) (r b : ℤ) : Prop :=
  ∀ d : ℤ, (∀ p : Sector, d ∣ weight n r b p) → IsUnit d

@[simp] theorem detail_left (n : ℕ) (r b : ℤ) (i : Fin 2) :
    weight n r b (true, .inl i) = b := by simp [weight, rightWeight, relativeWeight]

@[simp] theorem invariant_upper (n : ℕ) (r b : ℤ) :
    weight n r b (false, .inr 0) = r - n * b := by
  simp [weight, rightWeight, relativeWeight]; ring

@[simp] theorem detail_upper (n : ℕ) (r b : ℤ) :
    weight n r b (true, .inr 0) = r + b := by
  simp [weight, rightWeight, relativeWeight]

@[simp] theorem detail_lower (n : ℕ) (r b : ℤ) :
    weight n r b (true, .inr 1) = -r + b := by
  simp [weight, rightWeight, relativeWeight]

@[simp] theorem invariant_left (n : ℕ) (r b : ℤ) (i : Fin 2) :
    weight n r b (false, .inl i) = -(n : ℤ) * b := by
  simp [weight, rightWeight, relativeWeight]; ring

@[simp] theorem invariant_lower (n : ℕ) (r b : ℤ) :
    weight n r b (false, .inr 1) = -r - (n : ℤ) * b := by
  simp [weight, rightWeight, relativeWeight]; ring

theorem weight_scaled (n : ℕ) (r b k : ℤ) (p : Sector) :
    weight n (k * r) (k * b) p = k * weight n r b p := by
  unfold weight
  ring

/-- The rational readout uses the same unit as the actual normalized
charge operator. The primitive character itself remains integral. -/
def normalizedWeight (n : ℕ) (p : Sector) : ℚ :=
  (generatedWeight n p : ℚ) / (2 * n)

theorem normalizedWeight_from_generators (n : ℕ) (p : Sector) :
    normalizedWeight n p =
      ((n : ℚ) * rightWeight p.2 + relativeWeight n p.1) /
        (2 * n) := by
  simp [normalizedWeight, generatedWeight, weight]

theorem primitive_iff (n : ℕ) (r b : ℤ) :
    Primitive n r b ↔ HistoryRelativeCharge.PrimitivePair r b := by
  constructor
  · intro hp d hdr hdb
    exact hp d (fun p => dvd_add (dvd_mul_of_dvd_left hdr _)
      (dvd_mul_of_dvd_left hdb _))
  · intro hp d hd
    have hb : d ∣ b := by simpa using hd (true, .inl 0)
    have hu : d ∣ r + b := by simpa using hd (true, .inr 0)
    exact hp d (by simpa using dvd_sub hu hb) hb

theorem fixed_upper_primitive_iff (n : ℕ) (r b : ℤ)
    (hv : weight n r b (false, .inr 0) = 0) : Primitive n r b ↔ IsUnit b := by
  have hr : r = n * b := by rw [invariant_upper] at hv; linarith
  constructor
  · intro hp
    apply (primitive_iff n r b).mp hp b
    · exact ⟨n, by rw [hr]; ring⟩
    · exact dvd_rfl
  · intro hb
    apply (primitive_iff n r b).mpr
    intro d _ hdb
    exact isUnit_of_dvd_unit hdb hb

theorem oriented_unique (n : ℕ) {r b : ℤ} (hp : Primitive n r b)
    (hv : weight n r b (false, .inr 0) = 0) (hb : 0 < b) : r = n ∧ b = 1 := by
  rcases Int.isUnit_iff.mp ((fixed_upper_primitive_iff n r b hv).mp hp) with h | h
  · refine ⟨?_, h⟩
    rw [invariant_upper, h] at hv
    linarith
  · exfalso; linarith

theorem oriented_existsUnique (n : ℕ) :
    ∃! p : ℤ × ℤ, Primitive n p.1 p.2 ∧
      weight n p.1 p.2 (false, .inr 0) = 0 ∧ 0 < p.2 := by
  refine ⟨(n, 1), ⟨?_, by simp, by norm_num⟩, ?_⟩
  · exact (primitive_iff n n 1).mpr (fun d _ hd => isUnit_of_dvd_one hd)
  · intro p hp
    exact Prod.ext (oriented_unique n hp.1 hp.2.1 hp.2.2).1
      (oriented_unique n hp.1 hp.2.1 hp.2.2).2

def weyl : Spin ≃ Spin where
  toFun s := match s with
    | .inl i => .inl i
    | .inr i => .inr (1 - i)
  invFun s := match s with
    | .inl i => .inl i
    | .inr i => .inr (1 - i)
  left_inv s := by rcases s with i | i <;> fin_cases i <;> rfl
  right_inv s := by rcases s with i | i <;> fin_cases i <;> rfl

theorem weight_weyl (n : ℕ) (r b : ℤ) (c : Bool) (s : Spin) :
    weight n (-r) b (c, s) = weight n r b (c, weyl s) := by
  rcases s with i | i <;> fin_cases i <;> simp [weight, rightWeight, weyl]

theorem weight_orientation (n : ℕ) (r b : ℤ) (p : Sector) :
    weight n (-r) (-b) p = -weight n r b p := by unfold weight; ring

theorem generated_values (n : ℕ) :
    generatedWeight n (false, .inl 0) = -(n : ℤ) ∧
    generatedWeight n (true, .inl 0) = 1 ∧
    generatedWeight n (false, .inr 0) = 0 ∧
    generatedWeight n (true, .inr 0) = n + 1 ∧
    generatedWeight n (false, .inr 1) = -2 * (n : ℤ) ∧
    generatedWeight n (true, .inr 1) = 1 - (n : ℤ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [generatedWeight, weight, rightWeight, relativeWeight] <;> ring

theorem generated_zero_iff {n : ℕ} (hn : 2 ≤ n) (p : Sector) :
    generatedWeight n p = 0 ↔ p = (false, .inr 0) := by
  rcases p with ⟨c, i | i⟩ <;> cases c <;> fin_cases i <;>
    simp [generatedWeight, weight, rightWeight, relativeWeight] <;> omega

theorem generated_zero_one (p : Sector) : generatedWeight 1 p = 0 ↔
    p = (false, .inr 0) ∨ p = (true, .inr 1) := by
  rcases p with ⟨c, i | i⟩ <;> cases c <;> fin_cases i <;>
    norm_num [generatedWeight, weight, rightWeight, relativeWeight]

end GeneratedFoundations.Arithmetic.HistoryJointChargeLattice

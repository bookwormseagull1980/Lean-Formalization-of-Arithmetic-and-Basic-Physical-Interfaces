module

public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Finite Weyl averaging

Translations and the standard additive character of `ZMod (n+1)` define
the shift and phase matrices. Character orthogonality removes off-diagonal
entries, and averaging shifts replaces the diagonal by its mean. The same
finite label group has a unique translation-invariant probability weight.
-/

@[expose] public section

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace GeneratedFoundations.Operations.FiniteWeylAverage

abbrev Index (n : ℕ) := ZMod (n + 1)
abbrev Mat (n : ℕ) := Matrix (Index n) (Index n) ℂ
abbrev Label (n : ℕ) := Index n × Index n

local instance positiveDimension (n : ℕ) : NeZero (n + 1) := ⟨Nat.succ_ne_zero n⟩

theorem dimension_ne_zero (n : ℕ) : ((n + 1 : ℕ) : ℂ) ≠ 0 := by
  exact_mod_cast Nat.succ_ne_zero n

theorem sum_character (n : ℕ) (k : Index n) :
    (∑ b : Index n, ZMod.stdAddChar (b * k)) =
      if k = 0 then ((n + 1 : ℕ) : ℂ) else 0 := by
  simpa only [ZMod.card, Nat.cast_ite, Nat.cast_zero] using
    AddChar.sum_mulShift k (ZMod.isPrimitive_stdAddChar (n + 1))

theorem character_conj (n : ℕ) (k : Index n) :
    conj (ZMod.stdAddChar k) = ZMod.stdAddChar (-k) := by
  rw [AddChar.map_neg_eq_inv]
  apply (Complex.inv_eq_conj _).symm
  simpa only [ZMod.stdAddChar_apply] using (ZMod.toCircle k).norm_coe

/-- The shift sends the basis vector indexed by `j` to that indexed by `j+a`. -/
def shift (n : ℕ) (a : Index n) : Mat n :=
  fun i j => if j = i - a then 1 else 0

def phase (n : ℕ) (b : Index n) : Mat n :=
  Matrix.diagonal fun j => ZMod.stdAddChar (b * j)

theorem shift_mul_apply (n : ℕ) (a : Index n) (X : Mat n) (i j : Index n) :
    (shift n a * X) i j = X (i - a) j := by
  simp [Matrix.mul_apply, shift, ite_mul]

theorem mul_shift_adjoint_apply (n : ℕ) (a : Index n) (X : Mat n) (i j : Index n) :
    (X * (shift n a).conjTranspose) i j = X i (j - a) := by
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, shift, mul_ite]

theorem shift_conj_apply (n : ℕ) (a : Index n) (X : Mat n) (i j : Index n) :
    (shift n a * X * (shift n a).conjTranspose) i j = X (i - a) (j - a) := by
  rw [mul_shift_adjoint_apply, shift_mul_apply]

theorem phase_conj_apply (n : ℕ) (b : Index n) (X : Mat n) (i j : Index n) :
    (phase n b * X * (phase n b).conjTranspose) i j =
      ZMod.stdAddChar (b * (i - j)) * X i j := by
  simp only [phase, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal,
    Matrix.diagonal_mul, Pi.star_apply, Complex.star_def]
  rw [character_conj]
  calc
    _ = (ZMod.stdAddChar (b * i) * ZMod.stdAddChar (-(b * j))) * X i j := by ring
    _ = _ := by
      rw [← AddChar.map_add_eq_mul,
        show b * i + -(b * j) = b * (i - j) by ring]

theorem shift_unitary (n : ℕ) (a : Index n) :
    shift n a ∈ Matrix.unitaryGroup (Index n) ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  change shift n a * (shift n a).conjTranspose = 1
  ext i j
  simpa only [mul_one, Matrix.one_apply, sub_left_inj] using
    shift_conj_apply n a (1 : Mat n) i j

theorem phase_unitary (n : ℕ) (b : Index n) :
    phase n b ∈ Matrix.unitaryGroup (Index n) ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  change phase n b * (phase n b).conjTranspose = 1
  ext i j
  have h := phase_conj_apply n b (1 : Mat n) i j
  by_cases hij : i = j
  · subst j
    simpa using h
  · simpa [Matrix.one_apply, hij] using h

@[simp] theorem shift_zero (n : ℕ) : shift n 0 = 1 := by
  ext i j
  simp [shift, Matrix.one_apply, eq_comm]

@[simp] theorem phase_zero (n : ℕ) : phase n 0 = 1 := by
  simp [phase]

theorem shift_add (n : ℕ) (a b : Index n) : shift n (a + b) = shift n a * shift n b := by
  ext i j
  rw [shift_mul_apply]
  simp only [shift, sub_sub]

theorem phase_add (n : ℕ) (a b : Index n) : phase n (a + b) = phase n a * phase n b := by
  simp [phase, Matrix.diagonal_mul_diagonal, add_mul, AddChar.map_add_eq_mul]

def U (n : ℕ) : Mat n := shift n 1
def V (n : ℕ) : Mat n := phase n 1

theorem U_pow (n k : ℕ) : U n ^ k = shift n (k : Index n) := by
  induction k with
  | zero => simp
  | succ k hk =>
      rw [pow_succ, hk]
      change shift n (k : Index n) * shift n 1 = shift n ((k + 1 : ℕ) : Index n)
      rw [← shift_add, Nat.cast_add, Nat.cast_one]

theorem V_pow (n k : ℕ) : V n ^ k = phase n (k : Index n) := by
  induction k with
  | zero => simp
  | succ k hk =>
      rw [pow_succ, hk]
      change phase n (k : Index n) * phase n 1 = phase n ((k + 1 : ℕ) : Index n)
      rw [← phase_add, Nat.cast_add, Nat.cast_one]

def weyl (n : ℕ) (a b : Index n) : Mat n := shift n a * phase n b

theorem weyl_eq_powers (n : ℕ) (a b : Index n) :
    weyl n a b = U n ^ a.val * V n ^ b.val := by
  simp only [U_pow, V_pow, ZMod.natCast_zmod_val, weyl]

theorem weyl_unitary (n : ℕ) (a b : Index n) :
    weyl n a b ∈ Matrix.unitaryGroup (Index n) ℂ :=
  (Matrix.unitaryGroup (Index n) ℂ).mul_mem (shift_unitary n a) (phase_unitary n b)

theorem weyl_conj_apply (n : ℕ) (a b : Index n) (X : Mat n) (i j : Index n) :
    (weyl n a b * X * (weyl n a b).conjTranspose) i j =
      ZMod.stdAddChar (b * ((i - a) - (j - a))) * X (i - a) (j - a) := by
  have h : weyl n a b * X * (weyl n a b).conjTranspose =
      shift n a * (phase n b * X * (phase n b).conjTranspose) *
        (shift n a).conjTranspose := by
    simp only [weyl, Matrix.conjTranspose_mul, mul_assoc]
  rw [h, shift_conj_apply, phase_conj_apply]

theorem sum_phase_conjugates (n : ℕ) (a : Index n) (X : Mat n) (i j : Index n) :
    (∑ b : Index n, (weyl n a b * X * (weyl n a b).conjTranspose) i j) =
      if i = j then ((n + 1 : ℕ) : ℂ) * X (i - a) (j - a) else 0 := by
  simp only [weyl_conj_apply, ← Finset.sum_mul, sum_character,
    sub_eq_zero, sub_left_inj, ite_mul, zero_mul]

theorem sum_shifted_diagonal (n : ℕ) (X : Mat n) (i : Index n) :
    (∑ a : Index n, X (i - a) (i - a)) = Matrix.trace X := by
  exact (Equiv.subLeft i).sum_comp (fun j => X j j)

theorem sum_conjugates (n : ℕ) (X : Mat n) :
    (∑ a : Index n, ∑ b : Index n,
      weyl n a b * X * (weyl n a b).conjTranspose) =
      (((n + 1 : ℕ) : ℂ) * Matrix.trace X) • (1 : Mat n) := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, sum_phase_conjugates]
  by_cases hij : i = j
  · subst j
    simp only [ite_true, ← Finset.mul_sum, sum_shifted_diagonal,
      Matrix.one_apply_eq, mul_one]
  · simp [hij]

def average (n : ℕ) (X : Mat n) : Mat n :=
  ((((n + 1 : ℕ) : ℂ) ^ 2)⁻¹) •
    (∑ a : Index n, ∑ b : Index n,
      weyl n a b * X * (weyl n a b).conjTranspose)

theorem average_eq_trace (n : ℕ) (X : Mat n) :
    average n X = (Matrix.trace X / ((n + 1 : ℕ) : ℂ)) • (1 : Mat n) := by
  rw [average, sum_conjugates, smul_smul]
  congr 1
  field_simp [dimension_ne_zero n]

/-- In particular this applies to every density matrix of trace one. -/
theorem average_of_trace_one (n : ℕ) (X : Mat n) (hX : Matrix.trace X = 1) :
    average n X = (((n + 1 : ℕ) : ℂ)⁻¹) • (1 : Mat n) := by
  simp only [average_eq_trace, hX, one_div]

def TranslationInvariant (n : ℕ) (w : Label n → ℝ) : Prop :=
  ∀ a b : Label n, w (a + b) = w b

theorem translationInvariant_constant (n : ℕ) (w : Label n → ℝ)
    (hw : TranslationInvariant n w) (a : Label n) : w a = w 0 := by
  simpa only [add_zero] using hw a 0

theorem normalized_translationInvariant_unique (n : ℕ) (w : Label n → ℝ)
    (hw : TranslationInvariant n w) (hsum : ∑ a : Label n, w a = 1)
    (a : Label n) : w a = 1 / (((n + 1 : ℕ) : ℝ) ^ 2) := by
  have hconstant := translationInvariant_constant n w hw
  have hc : (((n + 1 : ℕ) : ℝ) ^ 2) * w 0 = 1 := by
    simpa only [hconstant, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
      ZMod.card, nsmul_eq_mul, Nat.cast_mul, pow_two] using hsum
  rw [hconstant]
  apply (eq_div_iff (by positivity : (((n + 1 : ℕ) : ℝ) ^ 2) ≠ 0)).mpr
  simpa only [mul_comm] using hc

def uniformWeight (n : ℕ) (_a : Label n) : ℝ := 1 / (((n + 1 : ℕ) : ℝ) ^ 2)

theorem uniformWeight_nonneg (n : ℕ) (a : Label n) : 0 ≤ uniformWeight n a := by
  unfold uniformWeight
  positivity

theorem uniformWeight_normalized (n : ℕ) : ∑ a : Label n, uniformWeight n a = 1 := by
  simp only [uniformWeight, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    ZMod.card, nsmul_eq_mul, Nat.cast_mul]
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hn]

theorem uniformWeight_translationInvariant (n : ℕ) :
    TranslationInvariant n (uniformWeight n) := fun _ _ => rfl

theorem uniformWeight_unique (n : ℕ) :
    ∃! w : Label n → ℝ,
      (∀ a, 0 ≤ w a) ∧ (∑ a : Label n, w a = 1) ∧ TranslationInvariant n w := by
  refine ⟨uniformWeight n,
    ⟨uniformWeight_nonneg n, uniformWeight_normalized n, uniformWeight_translationInvariant n⟩,
    ?_⟩
  intro w hw
  funext a
  exact normalized_translationInvariant_unique n w hw.2.2 hw.2.1 a

end GeneratedFoundations.Operations.FiniteWeylAverage

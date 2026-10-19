module

public import GeneratedFoundations.Arithmetic.GeneratedPrimeParity
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The complete multiplicative occupation and its square-spectrum response

A nonzero native mode already has its unique generated prime multiset.
This module retains that occupation through its actual evaluation.  Its
Gaussian energy is the square of the whole evaluation, not the sum of
squared prime labels.  Subtracting the unit-mode energy gives a unique
vacuum and the first nonvacuum lower edge three.  Unlike a free additive
Fock energy, multiplication has a nonzero joint energy term; the exact
composition formula below retains it.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Arithmetic.OccupationResponse

open NativeModes GeneratedPrimeParity

abbrev Occupation := {x : Mode // x ≠ 0}

def vacuum : Occupation := ⟨1, mode_one_ne_zero⟩

def compose (x y : Occupation) : Occupation :=
  ⟨x.val * y.val, native_mul_ne_zero x.property y.property⟩

def root (x : Occupation) : ℕ := index x.val

theorem root_pos (x : Occupation) : 0 < root x :=
  Nat.pos_of_ne_zero ((index_eq_zero_iff x.val).not.mpr x.property)

@[simp] theorem root_vacuum : root vacuum = 1 := index_one

@[simp] theorem root_compose (x y : Occupation) :
    root (compose x y) = root x * root y := index_mul _ _

theorem root_faithful {x y : Occupation} (h : root x = root y) : x = y :=
  Subtype.ext (index_injective h)

def energy (x : Occupation) : ℝ := (root x : ℝ) ^ 2 - 1

@[simp] theorem energy_vacuum : energy vacuum = 0 := by simp [energy]

theorem energy_nonneg (x : Occupation) : 0 ≤ energy x := by
  have hx : (1 : ℝ) ≤ root x := by exact_mod_cast root_pos x
  dsimp [energy]
  nlinarith

theorem energy_eq_zero_iff (x : Occupation) : energy x = 0 ↔ x = vacuum := by
  constructor
  · intro he
    have hp : (0 : ℝ) < root x := by exact_mod_cast root_pos x
    have h1 : (root x : ℝ) = 1 := by dsimp [energy] at he; nlinarith
    apply root_faithful
    rw [root_vacuum]
    exact_mod_cast h1
  · rintro rfl
    exact energy_vacuum

theorem nonvacuum_gap (x : Occupation) (hx : x ≠ vacuum) : 3 ≤ energy x := by
  have hn : root x ≠ 1 := by
    intro h
    exact hx (root_faithful (h.trans root_vacuum.symm))
  have h2 : 2 ≤ root x := by have := root_pos x; omega
  have hr : (2 : ℝ) ≤ root x := by exact_mod_cast h2
  dsimp [energy]
  nlinarith

theorem complete_energy_composition (x y : Occupation) :
    energy (compose x y) = energy x + energy y + energy x * energy y := by
  simp only [energy, root_compose, Nat.cast_mul]
  ring

theorem generated_factorization (x : Occupation) :
    (∀ p ∈ factorMultiset x.val x.property, NativeIrreducible p) ∧
      (factorMultiset x.val x.property).prod = x.val := factorMultiset_spec _ _

theorem occupation_composition (x y : Occupation) :
    factorMultiset (compose x y).val (compose x y).property =
      factorMultiset x.val x.property + factorMultiset y.val y.property :=
  factorMultiset_mul _ _ _ _

def character (x : Occupation) : ℤ := modeCentre x.val x.property

theorem character_composition (x y : Occupation) :
    character (compose x y) = character x * character y := modeCentre_mul _ _ _ _

/-- Particle number counts the actual generated prime multiset, including
repeated primes. It is not the spectral root or the square-spectrum energy. -/
def particleNumber (x : Occupation) : ℕ := factorCount x.val x.property

@[simp] theorem factors_vacuum : factorMultiset vacuum.val vacuum.property = 0 :=
  (factorMultiset_unique mode_one_ne_zero 0 (by simp)).symm

@[simp] theorem particleNumber_vacuum : particleNumber vacuum = 0 := by
  simp [particleNumber, factorCount]

theorem particleNumber_composition (x y : Occupation) :
    particleNumber (compose x y) = particleNumber x + particleNumber y :=
  factorCount_mul _ _ _ _

theorem particleNumber_eq_zero_iff (x : Occupation) :
    particleNumber x = 0 ↔ x = vacuum := by
  constructor
  · intro h
    have hf : factorMultiset x.val x.property = 0 := Multiset.card_eq_zero.mp h
    apply Subtype.ext
    change x.val = 1
    have hp := (factorMultiset_spec x.val x.property).2
    simpa only [hf, Multiset.prod_zero] using hp.symm
  · rintro rfl
    exact particleNumber_vacuum

/-- A native prime occupies exactly its own generated prime direction. -/
def oneParticle (p : Mode) (hp : NativeIrreducible p) : Occupation := ⟨p, hp.1⟩

@[simp] theorem factors_oneParticle (p : Mode) (hp : NativeIrreducible p) :
    factorMultiset (oneParticle p hp).val (oneParticle p hp).property = {p} := by
  symm
  apply factorMultiset_unique hp.1
  exact ⟨by simpa using hp, by simp⟩

@[simp] theorem particleNumber_oneParticle (p : Mode) (hp : NativeIrreducible p) :
    particleNumber (oneParticle p hp) = 1 := by
  simp [particleNumber, factorCount]

@[simp] theorem energy_oneParticle (p : Mode) (hp : NativeIrreducible p) :
    energy (oneParticle p hp) = (index p : ℝ) ^ 2 - 1 := rfl

theorem oneParticle_ne_vacuum (p : Mode) (hp : NativeIrreducible p) :
    oneParticle p hp ≠ vacuum := by
  intro h
  exact hp.2.1 (congrArg Subtype.val h)

/-- The least nonvacuum root is an actual generated mode. The lower edge is
attained, not merely an inequality on all other occupations. -/
def groundOccupation : Occupation := ⟨powerMode 2, by
  intro h
  have := congrArg index h
  simp at this⟩

@[simp] theorem energy_groundOccupation : energy groundOccupation = 3 := by
  norm_num [energy, root, groundOccupation]

theorem groundOccupation_ne_vacuum : groundOccupation ≠ vacuum := by
  intro h
  have := congrArg energy h
  simp at this

def heatWeight (t : ℝ) (x : Occupation) : ℝ := Real.exp (-t * energy x)

@[simp] theorem heat_zero (x : Occupation) : heatWeight 0 x = 1 := by simp [heatWeight]

@[simp] theorem heat_vacuum (t : ℝ) : heatWeight t vacuum = 1 := by simp [heatWeight]

theorem heat_semigroup (s t : ℝ) (x : Occupation) :
    heatWeight (s + t) x = heatWeight s x * heatWeight t x := by
  simp only [heatWeight, ← Real.exp_add]
  congr 1
  ring

theorem heat_pos (t : ℝ) (x : Occupation) : 0 < heatWeight t x := Real.exp_pos _

theorem heat_nonvacuum_le (t : ℝ) (ht : 0 ≤ t) (x : Occupation) (hx : x ≠ vacuum) :
    heatWeight t x ≤ Real.exp (-3 * t) := by
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonpos_left (nonvacuum_gap x hx) (neg_nonpos.mpr ht)
  simpa [mul_comm] using h

theorem original_gaussian (t : ℝ) (x : Occupation) :
    Real.exp (-t * (root x : ℝ) ^ 2) = Real.exp (-t) * heatWeight t x := by
  simp only [heatWeight, energy, ← Real.exp_add]
  congr 1
  ring

structure Conclusions : Prop where
  unique_vacuum : ∀ x, energy x = 0 ↔ x = vacuum
  nonvacuum_lower : ∀ x, x ≠ vacuum → 3 ≤ energy x
  complete_joint_energy : ∀ x y,
    energy (compose x y) = energy x + energy y + energy x * energy y
  actual_prime_occupation : ∀ x y,
    factorMultiset (compose x y).val (compose x y).property =
      factorMultiset x.val x.property + factorMultiset y.val y.property
  semigroup : ∀ s t x, heatWeight (s + t) x = heatWeight s x * heatWeight t x
  original_response : ∀ t x,
    Real.exp (-t * (root x : ℝ) ^ 2) = Real.exp (-t) * heatWeight t x
  occupation_number : ∀ x y,
    particleNumber (compose x y) = particleNumber x + particleNumber y
  empty_iff_vacuum : ∀ x, particleNumber x = 0 ↔ x = vacuum
  one_prime : ∀ p hp, particleNumber (oneParticle p hp) = 1
  gap_attained : groundOccupation ≠ vacuum ∧ energy groundOccupation = 3

theorem generated : Conclusions where
  unique_vacuum := energy_eq_zero_iff
  nonvacuum_lower := nonvacuum_gap
  complete_joint_energy := complete_energy_composition
  actual_prime_occupation := occupation_composition
  semigroup := heat_semigroup
  original_response := original_gaussian
  occupation_number := particleNumber_composition
  empty_iff_vacuum := particleNumber_eq_zero_iff
  one_prime := particleNumber_oneParticle
  gap_attained := ⟨groundOccupation_ne_vacuum, energy_groundOccupation⟩

end GeneratedFoundations.Arithmetic.OccupationResponse

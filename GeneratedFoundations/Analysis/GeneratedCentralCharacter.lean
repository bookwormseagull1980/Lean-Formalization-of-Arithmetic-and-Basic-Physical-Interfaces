module

public import GeneratedFoundations.Arithmetic.CompleteHistorySource
public import GeneratedFoundations.Arithmetic.GeneratedPrimeParity
public import Mathlib.NumberTheory.ArithmeticFunction.Liouville

/-!
# Central character as a downstream arithmetic observation

The complete positive history source is constructed before a sign is read.
The central character is defined from the unique irreducible multiset of the
generated circle mode.  Its agreement with the classical Liouville function
is proved afterwards.  Thus the classical arithmetic function is a comparison
target and is not used to construct histories or their central parity.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Analysis.GeneratedCentralCharacter

open GeneratedFoundations.Arithmetic.CompleteHistory
open GeneratedFoundations.Arithmetic.NativeModes
open GeneratedFoundations.Arithmetic.GeneratedPrimeParity

/-- The central parity attached to a generated positive root. -/
def centreCharacter (k : ℕ) : ℤ := rootCentre k

@[simp] theorem centreCharacter_one : centreCharacter 1 = 1 := by
  exact rootCentre_one

theorem centreCharacter_mul (m n : ℕ) :
    centreCharacter (m * n) = centreCharacter m * centreCharacter n := by
  exact rootCentre_mul m n

/-- The intrinsic source-mode character agrees with Liouville only as a
consequence of its generated uniqueness property. -/
theorem modeCentre_eq_liouville_index (x : Mode) (hx : x ≠ 0) :
    modeCentre x hx = ArithmeticFunction.liouville (index x) := by
  symm
  apply modeCentre_unique (fun u => ArithmeticFunction.liouville (index u))
  · simpa only [index_one] using ArithmeticFunction.liouville_apply_one
  · intro u v
    simp only [index_mul, ArithmeticFunction.liouville_apply_mul]
  · intro p hp
    have hprime := index_prime_of_nativeIrreducible hp
    rw [ArithmeticFunction.liouville_apply hprime.ne_zero,
      ArithmeticFunction.cardFactors_apply_prime hprime]
    norm_num

/-- Classical Liouville is the coordinate expression of the generated
central character, not a premise of its definition. -/
theorem centreCharacter_eq_liouville (n : ℕ) :
    centreCharacter n = ArithmeticFunction.liouville n := by
  by_cases hn : n = 0
  · subst n
    simp [centreCharacter]
  have hmode : powerMode n ≠ 0 := by
    intro h
    apply hn
    exact powerMode_injective (by simpa using h)
  have hcompare := modeCentre_eq_liouville_index (powerMode n) hmode
  simpa [centreCharacter, rootCentre, rootPrimeCount, modeCentre, hn] using hcompare

/-- The central parity is constant on each complete history fibre. -/
def historyCentre {k : ℕ} (_h : History k) : ℤ := centreCharacter k

theorem historyCentre_fibre_constant {k : ℕ} (h₁ h₂ : History k) :
    historyCentre h₁ = historyCentre h₂ := rfl

/-- Multiplicative top channels preserve the central character exactly. -/
theorem centreCharacter_mul_channel {k : ℕ} (c : Channel k)
    (hop : c.operation = .mul) :
    centreCharacter k = centreCharacter c.left.1 * centreCharacter c.right.1 := by
  have heq : c.left.1 * c.right.1 = k := by
    have hall := c.equation
    rw [hop] at hall
    exact hall.2.2
  calc
    centreCharacter k = centreCharacter (c.left.1 * c.right.1) :=
      congrArg centreCharacter heq.symm
    _ = centreCharacter c.left.1 * centreCharacter c.right.1 :=
      centreCharacter_mul c.left.1 c.right.1

theorem centreCharacter_sq (n : ℕ) (hn : n ≠ 0) :
    centreCharacter n * centreCharacter n = 1 := by
  rw [centreCharacter_eq_liouville, ArithmeticFunction.liouville_apply hn]
  rcases neg_one_pow_eq_or ℤ (ArithmeticFunction.cardFactors n) with h | h <;>
    rw [h] <;> norm_num

/-- The additive defect is the sign needed to reconstruct the parent central
character from the two child characters. -/
def additiveDefect {k : ℕ} (c : Channel k) : ℤ :=
  centreCharacter k * centreCharacter c.left.1 * centreCharacter c.right.1

theorem centreCharacter_additive_reconstruction {k : ℕ} (c : Channel k) :
    centreCharacter k = centreCharacter c.left.1 * centreCharacter c.right.1 *
      additiveDefect c := by
  have hl0 : c.left.1 ≠ 0 := Nat.ne_of_gt c.left_pos
  have hr0 : c.right.1 ≠ 0 := Nat.ne_of_gt c.right_pos
  have hl2 := centreCharacter_sq c.left.1 hl0
  have hr2 := centreCharacter_sq c.right.1 hr0
  rw [additiveDefect]
  calc
    centreCharacter k = centreCharacter k * 1 * 1 := by ring
    _ = centreCharacter k *
        (centreCharacter c.left.1 * centreCharacter c.left.1) *
        (centreCharacter c.right.1 * centreCharacter c.right.1) := by
      rw [hl2, hr2]
    _ = centreCharacter c.left.1 * centreCharacter c.right.1 *
        (centreCharacter k * centreCharacter c.left.1 *
          centreCharacter c.right.1) := by ring

structure Conclusions : Prop where
  multiplicative : ∀ m n : ℕ,
    centreCharacter (m * n) = centreCharacter m * centreCharacter n
  fibre_constancy : ∀ {k : ℕ} (h₁ h₂ : History k),
    historyCentre h₁ = historyCentre h₂
  multiplicative_channels : ∀ {k : ℕ} (c : Channel k),
    c.operation = .mul →
      centreCharacter k = centreCharacter c.left.1 * centreCharacter c.right.1
  additive_reconstruction : ∀ {k : ℕ} (c : Channel k),
    centreCharacter k = centreCharacter c.left.1 * centreCharacter c.right.1 *
      additiveDefect c

theorem generatedCentralCharacterConclusions : Conclusions where
  multiplicative := centreCharacter_mul
  fibre_constancy := historyCentre_fibre_constant
  multiplicative_channels := centreCharacter_mul_channel
  additive_reconstruction := centreCharacter_additive_reconstruction

end GeneratedFoundations.Analysis.GeneratedCentralCharacter

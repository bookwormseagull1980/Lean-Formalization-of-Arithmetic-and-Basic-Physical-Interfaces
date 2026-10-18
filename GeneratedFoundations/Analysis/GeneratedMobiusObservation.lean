module

public import GeneratedFoundations.Analysis.GeneratedCentralCharacter
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# The generated signed arithmetic source

The complete history source retains every ordered additive and multiplicative
construction above a positive generated natural value.  Its central character
records multiplicative parity.  The squarefree projector is determined by the
same generated factorization, so their product is the signed observation on
the existing source rather than an independently supplied arithmetic weight.

The main theorem identifies this generated observation with the classical
Moebius function.  The final pushforward keeps the sign inside the complete
history sum and therefore supplies the finite signed Gaussian source used by
later scale-energy constructions.
-/

@[expose] public section

noncomputable section

open scoped BigOperators ArithmeticFunction.Moebius

namespace GeneratedFoundations.Analysis.GeneratedMobiusObservation

open GeneratedFoundations.Arithmetic.CompleteHistory
open GeneratedFoundations.Arithmetic.NativeModes
open GeneratedFoundations.Arithmetic.GeneratedPrimeParity
open GeneratedCentralCharacter

/-- The native irreducible factors of a positive generated root, expressed in
the generated natural coordinate.  The zero list is only a totalization. -/
def generatedFactorList (n : ℕ) : List ℕ :=
  if hn : n = 0 then [] else
    (factorMultiset (powerMode n) (by
      intro h
      apply hn
      exact powerMode_injective (by simpa using h))).toList.map index

theorem generatedFactorList_prod (n : ℕ) (hn : n ≠ 0) :
    (generatedFactorList n).prod = n := by
  simp only [generatedFactorList, hn, ↓reduceDIte]
  let hx : powerMode n ≠ 0 := by
    intro h
    apply hn
    exact powerMode_injective (by simpa using h)
  have hprod : (factorMultiset (powerMode n) hx).toList.prod = powerMode n := by
    rw [Multiset.prod_toList, (factorMultiset_spec (powerMode n) hx).2]
  have hmap : ∀ l : List Mode, (l.map index).prod = index l.prod := by
    intro l
    induction l with
    | nil => simp
    | cons p l ih => simp [ih]
  rw [hmap, hprod, index_powerMode]

theorem generatedFactorList_prime (n : ℕ) (hn : n ≠ 0) :
    ∀ p ∈ generatedFactorList n, Nat.Prime p := by
  intro p hp
  simp only [generatedFactorList, hn, ↓reduceDIte, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  exact index_prime_of_nativeIrreducible
    ((factorMultiset_spec (powerMode n) (by
      intro h
      apply hn
      exact powerMode_injective (by simpa using h))).1 q
        (Multiset.mem_toList.mp hq))

/-- The generated factor list is the classical prime-factor list only after
both have been expressed in the same natural coordinate. -/
theorem generatedFactorList_perm_primeFactorsList (n : ℕ) (hn : n ≠ 0) :
    (generatedFactorList n).Perm n.primeFactorsList :=
  Nat.primeFactorsList_unique (generatedFactorList_prod n hn)
    (generatedFactorList_prime n hn)

/-- Intrinsic squarefreeness: the unique native factor multiset contains no
repeated irreducible after applying the generated coordinate. -/
def GeneratedSquarefree (n : ℕ) : Prop :=
  n ≠ 0 ∧ (generatedFactorList n).Nodup

theorem generatedSquarefree_iff_squarefree {n : ℕ} :
    GeneratedSquarefree n ↔ Squarefree n := by
  constructor
  · rintro ⟨hn, hnodup⟩
    apply (Nat.squarefree_iff_nodup_primeFactorsList hn).2
    exact (generatedFactorList_perm_primeFactorsList n hn).nodup_iff.mp hnodup
  · intro hn
    refine ⟨hn.ne_zero, ?_⟩
    exact (generatedFactorList_perm_primeFactorsList n hn.ne_zero).nodup_iff.mpr
      ((Nat.squarefree_iff_nodup_primeFactorsList hn.ne_zero).1 hn)

/-- The projector onto values whose generated native factor profile has no
repeated factor.  No classical squarefreeness predicate enters this
definition. -/
def squarefreeProjector (n : ℕ) : ℤ :=
  by
    classical
    exact if GeneratedSquarefree n then 1 else 0

@[simp] theorem squarefreeProjector_of_generatedSquarefree {n : ℕ}
    (hn : GeneratedSquarefree n) :
    squarefreeProjector n = 1 := by
  simp [squarefreeProjector, hn]

@[simp] theorem squarefreeProjector_of_not_generatedSquarefree {n : ℕ}
    (hn : ¬GeneratedSquarefree n) : squarefreeProjector n = 0 := by
  simp [squarefreeProjector, hn]

/-- Central multiplicative parity observed only on squarefree generated
values. -/
def generatedMoebius (n : ℕ) : ℤ :=
  centreCharacter n * squarefreeProjector n

/-- The source-generated signed observation is exactly the Moebius function. -/
theorem generatedMoebius_eq_moebius (n : ℕ) :
    generatedMoebius n = ArithmeticFunction.moebius n := by
  by_cases hn : GeneratedSquarefree n
  · have hs : Squarefree n := generatedSquarefree_iff_squarefree.mp hn
    rw [generatedMoebius, squarefreeProjector_of_generatedSquarefree hn, mul_one,
      centreCharacter_eq_liouville, ArithmeticFunction.liouville_apply hs.ne_zero,
      ArithmeticFunction.moebius_apply_of_squarefree hs]
  · have hs : ¬Squarefree n := fun h => hn (generatedSquarefree_iff_squarefree.mpr h)
    rw [generatedMoebius, squarefreeProjector_of_not_generatedSquarefree hn, mul_zero,
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]

theorem generatedMoebius_ne_zero_iff_squarefree {n : ℕ} :
    generatedMoebius n ≠ 0 ↔ Squarefree n := by
  rw [generatedMoebius_eq_moebius,
    ArithmeticFunction.moebius_ne_zero_iff_squarefree]

theorem generatedMoebius_sq (n : ℕ) :
    generatedMoebius n ^ 2 = squarefreeProjector n := by
  by_cases hn : GeneratedSquarefree n
  · have hs : Squarefree n := generatedSquarefree_iff_squarefree.mp hn
    rw [generatedMoebius_eq_moebius, ArithmeticFunction.moebius_sq,
      squarefreeProjector_of_generatedSquarefree hn]
    simp [hs]
  · have hs : ¬Squarefree n := fun h => hn (generatedSquarefree_iff_squarefree.mpr h)
    rw [generatedMoebius_eq_moebius,
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs,
      squarefreeProjector_of_not_generatedSquarefree hn]
    norm_num

/-- The generated signed source is the Dirichlet inverse of the constant-one
divisor source.  This is the incidence identity that characterizes the sign
after native factorization has generated it. -/
theorem generatedMoebius_divisor_sum (n : ℕ) :
    ∑ d ∈ n.divisors, generatedMoebius d = if n = 1 then 1 else 0 := by
  simp_rw [generatedMoebius_eq_moebius]
  calc
    ∑ d ∈ n.divisors, ArithmeticFunction.moebius d =
        ((ArithmeticFunction.moebius * ArithmeticFunction.zeta :
          ArithmeticFunction ℤ) n) := by
            symm
            exact ArithmeticFunction.coe_mul_zeta_apply
    _ = (1 : ArithmeticFunction ℤ) n := by
      rw [ArithmeticFunction.moebius_mul_coe_zeta]
    _ = if n = 1 then 1 else 0 := ArithmeticFunction.one_apply

/-- The signed observation attached to a complete history depends only on its
generated root, hence is constant on each complete history fiber. -/
def historyMoebius {n : ℕ} (_h : History n) : ℤ := generatedMoebius n

theorem historyMoebius_fiber_constant {n : ℕ} (h₁ h₂ : History n) :
    historyMoebius h₁ = historyMoebius h₂ := rfl

/-- The persistent Gaussian history source with its generated arithmetic sign
retained before summation. -/
def signedGaussianIntensity (alpha L : ℝ) {n : ℕ} (h : History n) : ℝ :=
  (generatedMoebius n : ℝ) * flatGaussianIntensity alpha L h

/-- Pushing the complete signed history source to its root preserves both the
Gaussian mass and the generated Moebius sign. -/
theorem signedGaussian_pushforward (alpha L : ℝ) (n : ℕ) (hn : 0 < n) :
    ∑ h : History n, signedGaussianIntensity alpha L h =
      (generatedMoebius n : ℝ) * gaussianRootMass alpha L n := by
  simp only [signedGaussianIntensity, ← Finset.mul_sum,
    flatGaussian_pushforward alpha L n hn]

/-- The squarefree-central sign and its complete signed Gaussian pushforward
form one output of the existing generated arithmetic source. -/
structure Conclusions : Prop where
  intrinsic_support : ∀ n : ℕ, GeneratedSquarefree n ↔ Squarefree n
  classical_identification : ∀ n : ℕ,
    generatedMoebius n = ArithmeticFunction.moebius n
  incidence_inverse : ∀ n : ℕ,
    ∑ d ∈ n.divisors, generatedMoebius d = if n = 1 then 1 else 0
  support : ∀ n : ℕ, generatedMoebius n ≠ 0 ↔ Squarefree n
  square : ∀ n : ℕ, generatedMoebius n ^ 2 = squarefreeProjector n
  fiber_constancy : ∀ {n : ℕ} (h₁ h₂ : History n),
    historyMoebius h₁ = historyMoebius h₂
  signed_pushforward : ∀ (alpha L : ℝ) (n : ℕ), 0 < n →
    ∑ h : History n, signedGaussianIntensity alpha L h =
      (generatedMoebius n : ℝ) * gaussianRootMass alpha L n

theorem generatedMobiusConclusions : Conclusions where
  intrinsic_support := fun _ => generatedSquarefree_iff_squarefree
  classical_identification := generatedMoebius_eq_moebius
  incidence_inverse := generatedMoebius_divisor_sum
  support := fun _ => generatedMoebius_ne_zero_iff_squarefree
  square := generatedMoebius_sq
  fiber_constancy := historyMoebius_fiber_constant
  signed_pushforward := signedGaussian_pushforward

end GeneratedFoundations.Analysis.GeneratedMobiusObservation

module

public import Mathlib.NumberTheory.SumPrimeReciprocals
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Tactic

/-!
# Prime capacity algebra

This module supplies the **capacity layer** that the arithmetic branch was
missing for a Riemann-type closure:

* a positive unit--prime capacity pair;
* total, signed and transverse capacities;
* the exact identity `C^2 - B^2 = 4 C_+ C_-`;
* nonnegativity of the transverse capacity;
* the Gaussian prime weight `exp(-beta p^2 / 2) * p^(-2 sigma)`;
* summability for `sigma > 1/2` and a positive infinite prime capacity.

This is capacity algebra, not a proof of the Riemann hypothesis.  A
zero-free/critical-line conclusion still requires the missing transverse
covariance bound identifying the capacity closure with the zeta zeros.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Analysis.PrimeCapacity

/-- A positive two-sector capacity pair. -/
structure CapacityPair where
  plus : ℝ
  minus : ℝ
  plus_nonneg : 0 ≤ plus
  minus_nonneg : 0 ≤ minus
  total_pos : 0 < plus + minus

namespace CapacityPair

/-- Total capacity. -/
def total (C : CapacityPair) : ℝ := C.plus + C.minus

/-- Signed capacity. -/
def signed (C : CapacityPair) : ℝ := C.plus - C.minus

/-- Transverse capacity `C - B^2/C`. -/
def transverse (C : CapacityPair) : ℝ :=
  C.total - C.signed ^ 2 / C.total

theorem total_eq (C : CapacityPair) : C.total = C.plus + C.minus := rfl

theorem signed_eq (C : CapacityPair) : C.signed = C.plus - C.minus := rfl

/-- The exact transverse identity. -/
theorem transverse_eq (C : CapacityPair) :
    C.transverse = 4 * C.plus * C.minus / C.total := by
  dsimp [transverse, total, signed]
  field_simp [C.total_pos.ne']
  ring

/-- The transverse capacity is nonnegative. -/
theorem transverse_nonneg (C : CapacityPair) : 0 ≤ C.transverse := by
  rw [transverse_eq]
  apply div_nonneg
  · nlinarith [C.plus_nonneg, C.minus_nonneg]
  · exact C.total_pos.le

/-- The signed capacity is bounded by the total. -/
theorem signed_sq_le_total_sq (C : CapacityPair) :
    C.signed ^ 2 ≤ C.total ^ 2 := by
  dsimp [signed, total]
  nlinarith [mul_nonneg C.plus_nonneg C.minus_nonneg]

end CapacityPair

/-- The Gaussian prime weight. -/
def primeWeight (β σ : ℝ) (p : Nat.Primes) : ℝ :=
  Real.exp (-(β * (p : ℝ) ^ 2) / 2) * (p : ℝ) ^ (-2 * σ)

theorem primeWeight_nonneg (β σ : ℝ) (p : Nat.Primes) :
    0 ≤ primeWeight β σ p := by
  dsimp [primeWeight]
  positivity

theorem primeWeight_pos (β σ : ℝ) (p : Nat.Primes) :
    0 < primeWeight β σ p := by
  dsimp [primeWeight]
  exact mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (by exact_mod_cast p.prop.pos) _)

/-- The Gaussian factor is at most one for nonnegative `β`. -/
theorem primeWeight_le_rpow {β σ : ℝ} (hβ : 0 ≤ β) (p : Nat.Primes) :
    primeWeight β σ p ≤ (p : ℝ) ^ (-2 * σ) := by
  have hp : (0 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.prop.pos.le
  have hexp : Real.exp (-(β * (p : ℝ) ^ 2) / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [sq_nonneg (p : ℝ), hβ]
  have hpow : 0 ≤ (p : ℝ) ^ (-2 * σ) := Real.rpow_nonneg hp _
  dsimp [primeWeight]
  exact mul_le_of_le_one_left hpow hexp

/-- Summability of the Gaussian prime weight for `sigma > 1/2`. -/
theorem summable_primeWeight {β σ : ℝ} (hβ : 0 ≤ β) (hσ : 1 / 2 < σ) :
    Summable (fun p : Nat.Primes => primeWeight β σ p) := by
  have hbase : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-2 * σ)) := by
    exact (Nat.Primes.summable_rpow).mpr (by linarith)
  exact Summable.of_nonneg_of_le (fun p => primeWeight_nonneg β σ p)
    (fun p => primeWeight_le_rpow hβ p) hbase

/-- The infinite unit--prime capacity. -/
def primeCapacityLimit (β σ : ℝ) : ℝ :=
  1 + ∑' p : Nat.Primes, primeWeight β σ p

theorem primeCapacityLimit_pos (β σ : ℝ) :
    0 < primeCapacityLimit β σ := by
  have hsum : 0 ≤ ∑' p : Nat.Primes, primeWeight β σ p :=
    tsum_nonneg (fun p => primeWeight_nonneg β σ p)
  dsimp [primeCapacityLimit]
  linarith

/-- The unit--prime capacity pair at a finite/infinite prime sum. -/
def unitPrimeCapacity (β σ : ℝ) : CapacityPair where
  plus := 1
  minus := ∑' p : Nat.Primes, primeWeight β σ p
  plus_nonneg := by norm_num
  minus_nonneg := tsum_nonneg (fun p => primeWeight_nonneg β σ p)
  total_pos := primeCapacityLimit_pos β σ

theorem unitPrimeCapacity_total (β σ : ℝ) :
    (unitPrimeCapacity β σ).total = primeCapacityLimit β σ := rfl

theorem unitPrimeCapacity_transverse_nonneg (β σ : ℝ) :
    0 ≤ (unitPrimeCapacity β σ).transverse :=
  CapacityPair.transverse_nonneg _

end GeneratedFoundations.Analysis.PrimeCapacity

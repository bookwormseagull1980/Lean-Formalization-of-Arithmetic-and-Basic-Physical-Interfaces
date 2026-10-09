module

public import GeneratedFoundations.Spectral.NeumannHeatSemigroup
public import GeneratedFoundations.Spectral.PositiveOperatorTrace
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Trace class of the original Neumann heat semigroup

The heat operator acts on the original interval L² space. Its complete cosine
basis identifies the basis-independent positive trace with the convergent
Gaussian spectral sum, including the fixed constant mode.
-/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace GeneratedFoundations.Spectral.NeumannHeatTrace

open NeumannHeatSemigroup PositiveOperatorTrace

variable (L : ℝ)

theorem decay_eq_exp_square (t : ℝ) (n : ℕ) :
    decay L t n = Real.exp ((-t * (Real.pi / L) ^ 2 / 2) * (n : ℝ) ^ 2) := by
  unfold decay neumannEigenvalue
  congr 1
  ring

variable [hL : Fact (0 < L)]

theorem summable_decay {t : ℝ} (ht : 0 < t) : Summable (decay L t) := by
  have hc : -t * (Real.pi / L) ^ 2 / 2 < 0 := by
    have hp : 0 < (Real.pi / L) ^ 2 := sq_pos_of_pos (div_pos Real.pi_pos hL.out)
    nlinarith
  have hn (n : ℕ) : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    rw [pow_two]
    exact_mod_cast (Nat.le_mul_self n)
  change Summable (fun n => decay L t n)
  simp_rw [decay_eq_exp_square]
  exact Real.summable_exp_nat_mul_of_ge hc hn

theorem heat_quadratic_nonneg (t : ℝ≥0) (f : ComplexIntervalL2 0 L) :
    0 ≤ (inner ℂ f (heat L t f)).re := by
  apply diagonal_quadratic_nonneg (neumannCosineBasis L) (heat L t) (decay L t)
    (fun n => (decay_pos L t n).le)
  intro x n
  simpa only [coe_neumannCosineBasis] using heat_coefficient L t x n

theorem heat_positiveTrace_eq_sum (t : ℝ≥0) (ht : 0 < t) :
    positiveTrace (heat L t) = ∑' n, ENNReal.ofReal (decay L t n) := by
  apply positiveTrace_eq_tsum_of_diagonal (neumannCosineBasis L) (heat L t) (decay L t)
    (fun n => (decay_pos L t n).le) (summable_decay L ht)
  intro x n
  simpa only [coe_neumannCosineBasis] using heat_coefficient L t x n

theorem heat_positiveTrace_eq_ofReal_sum (t : ℝ≥0) (ht : 0 < t) :
    positiveTrace (heat L t) = ENNReal.ofReal (∑' n, decay L t n) := by
  rw [heat_positiveTrace_eq_sum L t ht]
  exact (ENNReal.ofReal_tsum_of_nonneg (fun n => (decay_pos L t n).le)
    (summable_decay L ht)).symm

theorem heat_positiveTrace_lt_top (t : ℝ≥0) (ht : 0 < t) :
    positiveTrace (heat L t) < ∞ := by
  rw [heat_positiveTrace_eq_sum L t ht]
  exact (summable_decay L ht).tsum_ofReal_lt_top

theorem heat_isPositiveTraceClass (t : ℝ≥0) (ht : 0 < t) :
    IsPositiveTraceClass (heat L t) :=
  ⟨heat_selfAdjoint L t, heat_quadratic_nonneg L t, heat_positiveTrace_lt_top L t ht⟩

theorem one_le_heat_positiveTrace (t : ℝ≥0) (ht : 0 < t) :
    1 ≤ positiveTrace (heat L t) := by
  rw [heat_positiveTrace_eq_sum L t ht]
  have h := ENNReal.le_tsum (f := fun n => ENNReal.ofReal (decay L t n)) 0
  simpa only [decay_mode_zero, ENNReal.ofReal_one] using h

theorem heat_positiveTrace_zeroMode (t : ℝ≥0) (ht : 0 < t) :
    positiveTrace (heat L t) = 1 + ∑' n, ENNReal.ofReal (decay L t (n + 1)) := by
  rw [heat_positiveTrace_eq_sum L t ht, tsum_eq_zero_add' ENNReal.summable]
  simp only [decay_mode_zero, ENNReal.ofReal_one]

end GeneratedFoundations.Spectral.NeumannHeatTrace

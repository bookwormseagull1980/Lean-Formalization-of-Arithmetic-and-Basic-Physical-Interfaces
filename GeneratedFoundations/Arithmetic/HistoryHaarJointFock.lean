module

public import GeneratedFoundations.Arithmetic.HistoryHaarJointHessian
public import Mathlib.Data.Finsupp.Order

/-!
# Occupations of the complete arithmetic response Hessian

The occupied directions are the actual complete basis of the joint Haar
Hessian: all coclosed matrix-field modes and the homogeneous state fibre.
Their energies are fixed by the second variation of the same coupled
action. The minimum is attained, and its cutoff-independent lower bound
passes to every nonvacuum finite occupation and to its heat weight.

These occupations lift the linearized response operator. They are distinct
from the prime-factor occupations of natural numbers, whose original
Gaussian energy depends on the whole evaluated product. No identification
of those two energy laws is made here.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Arithmetic.HistoryHaarJointFock

open HistoryHaarJointHessian

abbrev Occupation (N : ℕ) := Index N →₀ ℕ

def vacuum (N : ℕ) : Occupation N := 0

def totalEnergy (N : ℕ) (n : Occupation N) : ℝ :=
  n.sum fun i k => (k : ℝ) * eigenvalue N i

@[simp] theorem totalEnergy_vacuum (N : ℕ) : totalEnergy N (vacuum N) = 0 := by
  simp [totalEnergy, vacuum]

theorem eigenvalue_pos (N : ℕ) (i : Index N) : 0 < eigenvalue N i :=
  (by norm_num : (0 : ℝ) < 15 / 8).trans_le (eigenvalue_lower N i)

theorem totalEnergy_nonneg (N : ℕ) (n : Occupation N) : 0 ≤ totalEnergy N n := by
  unfold totalEnergy Finsupp.sum
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (Nat.cast_nonneg _) (eigenvalue_pos N i).le

theorem totalEnergy_add (N : ℕ) (n m : Occupation N) :
    totalEnergy N (n + m) = totalEnergy N n + totalEnergy N m := by
  classical
  exact Finsupp.sum_add_index (fun _ => by simp)
    (fun _ _ _ => by simp [Nat.cast_add, add_mul])

@[simp] theorem totalEnergy_single (N : ℕ) (i : Index N) (k : ℕ) :
    totalEnergy N (Finsupp.single i k) = (k : ℝ) * eigenvalue N i := by
  classical
  simp [totalEnergy]

theorem nonvacuum_gap (N : ℕ) {n : Occupation N} (hn : n ≠ vacuum N) :
    gapSq N ≤ totalEnergy N n := by
  classical
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hn
  have hone : (1 : ℝ) ≤ (n i : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
  have hs : (n i : ℝ) * eigenvalue N i ≤ totalEnergy N n := by
    unfold totalEnergy
    simpa using Finsupp.single_le_sum n
      (fun j k => mul_nonneg (Nat.cast_nonneg k) (eigenvalue_pos N j).le) i
  calc
    gapSq N = 1 * gapSq N := by ring
    _ ≤ (n i : ℝ) * gapSq N :=
      mul_le_mul_of_nonneg_right hone
        ((by norm_num : (0 : ℝ) ≤ 15 / 8).trans (gapSq_lower N))
    _ ≤ (n i : ℝ) * eigenvalue N i :=
      mul_le_mul_of_nonneg_left (eigenvalue_ge_gap N i) (Nat.cast_nonneg _)
    _ ≤ totalEnergy N n := hs

theorem nonvacuum_uniform_gap (N : ℕ) {n : Occupation N} (hn : n ≠ vacuum N) :
    (15 / 8 : ℝ) ≤ totalEnergy N n :=
  (gapSq_lower N).trans (nonvacuum_gap N hn)

theorem vacuum_unique (N : ℕ) (n : Occupation N) :
    totalEnergy N n = 0 ↔ n = vacuum N := by
  constructor
  · intro he
    by_contra hn
    have h := nonvacuum_uniform_gap N hn
    linarith
  · rintro rfl
    exact totalEnergy_vacuum N

def groundOccupation (N : ℕ) : Occupation N :=
  Finsupp.single (minimizingIndex N) 1

theorem groundOccupation_ne_vacuum (N : ℕ) : groundOccupation N ≠ vacuum N := by
  classical
  simp [groundOccupation, vacuum]

@[simp] theorem groundOccupation_energy (N : ℕ) :
    totalEnergy N (groundOccupation N) = gapSq N := by
  simp [groundOccupation, eigenvalue_minimizingIndex]

def heatWeight (N : ℕ) (t : ℝ) (n : Occupation N) : ℝ :=
  Real.exp (-t * totalEnergy N n)

@[simp] theorem heatWeight_zero (N : ℕ) (n : Occupation N) :
    heatWeight N 0 n = 1 := by
  simp [heatWeight]

theorem heatWeight_add (N : ℕ) (s t : ℝ) (n : Occupation N) :
    heatWeight N (s + t) n = heatWeight N s n * heatWeight N t n := by
  rw [heatWeight, heatWeight, heatWeight, ← Real.exp_add]
  congr 1
  ring

theorem heatWeight_pos (N : ℕ) (t : ℝ) (n : Occupation N) :
    0 < heatWeight N t n := Real.exp_pos _

@[simp] theorem heatWeight_vacuum (N : ℕ) (t : ℝ) :
    heatWeight N t (vacuum N) = 1 := by
  simp [heatWeight]

theorem heatWeight_nonvacuum_le (N : ℕ) {t : ℝ} (ht : 0 ≤ t)
    {n : Occupation N} (hn : n ≠ vacuum N) :
    heatWeight N t n ≤ Real.exp (-t * gapSq N) :=
  Real.exp_le_exp.mpr
    (mul_le_mul_of_nonpos_left (nonvacuum_gap N hn) (neg_nonpos.mpr ht))

theorem heatWeight_uniform_decay (N : ℕ) {t : ℝ} (ht : 0 ≤ t)
    {n : Occupation N} (hn : n ≠ vacuum N) :
    heatWeight N t n ≤ Real.exp (-t * (15 / 8 : ℝ)) :=
  Real.exp_le_exp.mpr
    (mul_le_mul_of_nonpos_left (nonvacuum_uniform_gap N hn) (neg_nonpos.mpr ht))

structure Conclusions : Prop where
  vacuum_only : ∀ N n, totalEnergy N n = 0 ↔ n = vacuum N
  actual_gap : ∀ N {n : Occupation N}, n ≠ vacuum N → gapSq N ≤ totalEnergy N n
  attained : ∀ N, groundOccupation N ≠ vacuum N ∧
    totalEnergy N (groundOccupation N) = gapSq N
  semigroup : ∀ N s t n,
    heatWeight N (s + t) n = heatWeight N s n * heatWeight N t n
  uniform_decay : ∀ N {t : ℝ}, 0 ≤ t → ∀ {n : Occupation N}, n ≠ vacuum N →
    heatWeight N t n ≤ Real.exp (-t * (15 / 8 : ℝ))

theorem generated : Conclusions where
  vacuum_only := vacuum_unique
  actual_gap := nonvacuum_gap
  attained N := ⟨groundOccupation_ne_vacuum N, groundOccupation_energy N⟩
  semigroup := heatWeight_add
  uniform_decay := heatWeight_uniform_decay

end GeneratedFoundations.Arithmetic.HistoryHaarJointFock

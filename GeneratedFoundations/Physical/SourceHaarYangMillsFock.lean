module

public import GeneratedFoundations.Physical.SourceHaarYangMillsHessian
public import Mathlib.Data.Finsupp.Order

/-!
# Finite occupations of the original field Hessian

The occupied vectors are the complete Haar-field eigenbasis of the closed
differential Hessian. Positivity and the minimizing occupation therefore use
the same operator as the differentiated nonlinear action.
-/

@[expose] public section

noncomputable section

open GeneratedFoundations.Physical.SourceGeneratedYangMillsGap
open GeneratedFoundations.Physical.SourceHaarYangMillsHessian

namespace GeneratedFoundations.Physical.SourceHaarYangMillsFock

abbrev Occupation := ResponseIndex →₀ ℕ

def vacuum : Occupation := 0

def totalEnergy (L z : ℝ) (n : Occupation) : ℝ :=
  n.sum fun a k => (k : ℝ) * responseEigenvalue L z a

@[simp] theorem totalEnergy_vacuum (L z : ℝ) : totalEnergy L z vacuum = 0 := by
  simp [totalEnergy, vacuum]

theorem eigenvalue_pos {L z : ℝ} (hL : 0 < L) (hz : 0 < z) (a : ResponseIndex) :
    0 < responseEigenvalue L z a :=
  (generatedYangMillsGapSq_pos hL hz).trans_le (eigenvalue_lower L z a)

theorem nonvacuum_gap {L z : ℝ} (hL : 0 < L) (hz : 0 < z)
    {n : Occupation} (hn : n ≠ vacuum) :
    generatedYangMillsGapSq L z ≤ totalEnergy L z n := by
  classical
  have hn0 : n ≠ 0 := hn
  obtain ⟨a, ha⟩ := Finsupp.support_nonempty_iff.mpr hn0
  have hone : (1 : ℝ) ≤ (n a : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp ha))
  have hs : (n a : ℝ) * responseEigenvalue L z a ≤ totalEnergy L z n := by
    unfold totalEnergy
    simpa using (Finsupp.single_le_sum n
      (fun i k => mul_nonneg (Nat.cast_nonneg k) (eigenvalue_pos hL hz i).le) a)
  calc
    generatedYangMillsGapSq L z = 1 * generatedYangMillsGapSq L z := by ring
    _ ≤ (n a : ℝ) * generatedYangMillsGapSq L z :=
      mul_le_mul_of_nonneg_right hone (generatedYangMillsGapSq_pos hL hz).le
    _ ≤ (n a : ℝ) * responseEigenvalue L z a :=
      mul_le_mul_of_nonneg_left (eigenvalue_lower L z a) (Nat.cast_nonneg _)
    _ ≤ totalEnergy L z n := hs

theorem vacuum_unique {L z : ℝ} (hL : 0 < L) (hz : 0 < z) (n : Occupation) :
    totalEnergy L z n = 0 ↔ n = vacuum := by
  constructor
  · intro he
    by_contra hn
    have hgap := nonvacuum_gap hL hz hn
    linarith [generatedYangMillsGapSq_pos hL hz]
  · rintro rfl
    exact totalEnergy_vacuum L z

def groundOccupation (L z : ℝ) : Occupation :=
  Finsupp.single (minimizingIndex L z) 1

theorem groundOccupation_ne_vacuum (L z : ℝ) : groundOccupation L z ≠ vacuum := by
  classical
  simp [groundOccupation, vacuum]

@[simp] theorem groundOccupation_energy (L z : ℝ) :
    totalEnergy L z (groundOccupation L z) = generatedYangMillsGapSq L z := by
  classical
  simp [totalEnergy, groundOccupation, eigenvalue_minimizingIndex]

end GeneratedFoundations.Physical.SourceHaarYangMillsFock

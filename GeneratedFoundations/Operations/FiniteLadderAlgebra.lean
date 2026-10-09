module

public import Mathlib.Algebra.Star.Subalgebra
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.Tactic

/-!
# The algebra of a finite Gaussian ladder

The compressed lowering matrix has weights `sqrt j`. Its number matrix has
the distinct eigenvalues `0, ..., n`. Finite interpolation gives the diagonal
matrix units; the lowering matrix connects adjacent eigenspaces. These
operations generate the full matrix algebra, including the one-dimensional
case.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace GeneratedFoundations.Operations.FiniteLadderAlgebra

abbrev Index (n : ℕ) := Fin (n + 1)
abbrev Mat (n : ℕ) := Matrix (Index n) (Index n) ℂ

def lowering (n : ℕ) : Mat n :=
  fun i j => if i.val + 1 = j.val then (Real.sqrt (j.val : ℝ) : ℂ) else 0

def number (n : ℕ) : Mat n := (lowering n).conjTranspose * lowering n

theorem number_eq_diagonal (n : ℕ) :
    number n = Matrix.diagonal (fun i : Index n => (i.val : ℂ)) := by
  ext i j
  by_cases hij : i = j
  · subst j
    rw [Matrix.diagonal_apply_eq]
    simp only [number, Matrix.mul_apply, Matrix.conjTranspose_apply]
    by_cases hi : i.val = 0
    · simp [lowering, hi]
    · let p : Index n := ⟨i.val - 1, by omega⟩
      have hp : p.val + 1 = i.val := by dsimp [p]; omega
      rw [Finset.sum_eq_single p]
      · simp only [lowering, ite_eq_left hp, Complex.star_def, Complex.conj_ofReal]
        exact_mod_cast Real.mul_self_sqrt (Nat.cast_nonneg i.val : (0 : ℝ) ≤ i.val)
      · intro k _ hk
        have hki : k.val + 1 ≠ i.val := by
          intro h
          apply hk
          apply Fin.ext
          dsimp [p]
          omega
        simp [lowering, hki]
      · simp
  · rw [Matrix.diagonal_apply_ne _ hij]
    simp only [number, Matrix.mul_apply, Matrix.conjTranspose_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hki : k.val + 1 = i.val
    · have hkj : k.val + 1 ≠ j.val := by
        intro h
        apply hij
        apply Fin.ext
        omega
      simp only [lowering, ite_eq_left hki, ite_eq_right hkj, mul_zero]
    · simp [lowering, hki]

def generatedAlgebra (n : ℕ) : StarSubalgebra ℂ (Mat n) :=
  StarAlgebra.adjoin ℂ {lowering n}

theorem lowering_mem (n : ℕ) : lowering n ∈ generatedAlgebra n :=
  StarAlgebra.self_mem_adjoin_singleton ℂ _

theorem raising_mem (n : ℕ) : (lowering n).conjTranspose ∈ generatedAlgebra n := by
  simpa only [Matrix.star_eq_conjTranspose] using star_mem (lowering_mem n)

theorem number_mem (n : ℕ) : number n ∈ generatedAlgebra n :=
  mul_mem (raising_mem n) (lowering_mem n)

def interpolationFactor (n : ℕ) (j k : Index n) : Mat n :=
  ((j.val : ℂ) - (k.val : ℂ))⁻¹ •
    (number n - (k.val : ℂ) • (1 : Mat n))

theorem interpolationFactor_mem (n : ℕ) (j k : Index n) :
    interpolationFactor n j k ∈ generatedAlgebra n := by
  apply (generatedAlgebra n).smul_mem
  exact sub_mem (number_mem n) ((generatedAlgebra n).smul_mem (one_mem _) _)

theorem interpolationFactor_eq_diagonal (n : ℕ) (j k : Index n) :
    interpolationFactor n j k = Matrix.diagonal
      (fun i : Index n => ((i.val : ℂ) - (k.val : ℂ)) /
        ((j.val : ℂ) - (k.val : ℂ))) := by
  rw [interpolationFactor, number_eq_diagonal]
  ext i l
  by_cases hil : i = l
  · subst l
    simp [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  · simp [Matrix.smul_apply, Matrix.sub_apply, hil]

def interpolation (n : ℕ) (j : Index n) (s : Finset (Index n)) : Mat n :=
  Matrix.diagonal fun i => ∏ k ∈ s,
    ((i.val : ℂ) - (k.val : ℂ)) / ((j.val : ℂ) - (k.val : ℂ))

theorem interpolation_mem (n : ℕ) (j : Index n) (s : Finset (Index n)) :
    interpolation n j s ∈ generatedAlgebra n := by
  induction s using Finset.induction_on with
  | empty => simp [interpolation]
  | @insert k s hk hs =>
      have hmul : interpolation n j (insert k s) =
          interpolationFactor n j k * interpolation n j s := by
        simp only [interpolation, interpolationFactor_eq_diagonal,
          Matrix.diagonal_mul_diagonal, Finset.prod_insert hk]
      rw [hmul]
      exact mul_mem (interpolationFactor_mem n j k) hs

theorem interpolation_eq_matrixUnit (n : ℕ) (j : Index n) :
    interpolation n j (Finset.univ.erase j) = Matrix.single j j 1 := by
  rw [interpolation, ← Matrix.diagonal_single]
  congr 1
  funext i
  by_cases hij : i = j
  · subst i
    simp only [Pi.single_eq_same]
    apply Finset.prod_eq_one
    intro k hk
    have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
    have hval : j.val ≠ k.val := by
      intro h
      exact hkj (Fin.ext h.symm)
    have hcast : (j.val : ℂ) ≠ (k.val : ℂ) := by exact_mod_cast hval
    exact div_self (sub_ne_zero.mpr hcast)
  · have hi : i ∈ Finset.univ.erase j := by simp [hij]
    have hprod : (∏ k ∈ Finset.univ.erase j,
        ((i.val : ℂ) - (k.val : ℂ)) / ((j.val : ℂ) - (k.val : ℂ))) = 0 :=
      Finset.prod_eq_zero hi (by simp)
    rw [hprod]
    simp [hij]

theorem diagonal_matrixUnit_mem (n : ℕ) (j : Index n) :
    Matrix.single j j (1 : ℂ) ∈ generatedAlgebra n := by
  rw [← interpolation_eq_matrixUnit n j]
  exact interpolation_mem n j _

theorem adjacent_matrixUnit_mem (n : ℕ) (i j : Index n) (hij : i.val + 1 = j.val) :
    Matrix.single i j (1 : ℂ) ∈ generatedAlgebra n := by
  have hj : 0 < (j.val : ℝ) := by exact_mod_cast (show 0 < j.val by omega)
  have hc : (Real.sqrt (j.val : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr hj))
  have hmem : Matrix.single i i (1 : ℂ) * lowering n * Matrix.single j j 1 ∈
      generatedAlgebra n :=
    mul_mem (mul_mem (diagonal_matrixUnit_mem n i) (lowering_mem n))
      (diagonal_matrixUnit_mem n j)
  simp only [Matrix.single_mul_mul_single, lowering, ite_eq_left hij, one_mul, mul_one] at hmem
  have hscaled := (generatedAlgebra n).smul_mem hmem
    (Real.sqrt (j.val : ℝ) : ℂ)⁻¹
  simpa only [Matrix.smul_single, smul_eq_mul, inv_mul_cancel₀ hc] using hscaled

theorem matrixUnit_mem_of_le (n : ℕ) (i j : Index n) (hij : i.val ≤ j.val) :
    Matrix.single i j (1 : ℂ) ∈ generatedAlgebra n := by
  have h : ∀ k : ℕ, ∀ q : Index n, q.val = i.val + k →
      Matrix.single i q (1 : ℂ) ∈ generatedAlgebra n := by
    intro k
    induction k with
    | zero =>
        intro q hq
        have hqi : q = i := Fin.ext (by omega)
        subst q
        exact diagonal_matrixUnit_mem n i
    | succ k ih =>
        intro q hq
        let p : Index n := ⟨i.val + k, by omega⟩
        have hp : p.val + 1 = q.val := by dsimp [p]; omega
        have hprod := mul_mem (ih p rfl) (adjacent_matrixUnit_mem n p q hp)
        simpa only [Matrix.single_mul_single_same, one_mul] using hprod
  exact h (j.val - i.val) j (by omega)

theorem matrixUnit_mem (n : ℕ) (i j : Index n) :
    Matrix.single i j (1 : ℂ) ∈ generatedAlgebra n := by
  rcases le_total i.val j.val with hij | hji
  · exact matrixUnit_mem_of_le n i j hij
  · have h := star_mem (matrixUnit_mem_of_le n j i hji)
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single, star_one] using h

theorem single_mem (n : ℕ) (i j : Index n) (c : ℂ) :
    Matrix.single i j c ∈ generatedAlgebra n := by
  simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using
    (generatedAlgebra n).smul_mem (matrixUnit_mem n i j) c

theorem matrix_mem (n : ℕ) (M : Mat n) : M ∈ generatedAlgebra n := by
  rw [Matrix.matrix_eq_sum_single M]
  apply sum_mem
  intro i _
  apply sum_mem
  intro j _
  exact single_mem n i j (M i j)

theorem generatedAlgebra_eq_top (n : ℕ) : generatedAlgebra n = ⊤ :=
  StarSubalgebra.eq_top_iff.mpr (matrix_mem n)

theorem adjoin_lowering_eq_top (n : ℕ) :
    StarAlgebra.adjoin ℂ {lowering n} = ⊤ := generatedAlgebra_eq_top n

end GeneratedFoundations.Operations.FiniteLadderAlgebra

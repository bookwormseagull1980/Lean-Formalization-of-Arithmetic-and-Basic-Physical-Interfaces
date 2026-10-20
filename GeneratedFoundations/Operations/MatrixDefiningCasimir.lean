module

public import GeneratedFoundations.Operations.MatrixAdjointCasimir
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Defining response of the complete traceless operation family

The scalar part is removed from every actual matrix unit before taking
its trace-dual quadratic sum. The resulting operator is computed at the
carrier's own dimension. In the half-trace convention the coefficient is
`(d - 1/d)/2`; it is not prescribed from a fixed colour representation.
The family is redundant, but its reconstruction and quadratic sum retain
all operation directions.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Matrix

namespace GeneratedFoundations.Operations.MatrixDefiningCasimir

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open MatrixAdjointCasimir (Algebra matrixUnit pairedSquareSum_eq)

def centredUnit (i j : ι) : Algebra ι :=
  matrixUnit i j - (if i = j then (Fintype.card ι : ℂ)⁻¹ else 0) • 1

theorem sum_diagonal_units : (∑ i : ι, matrixUnit i i) = (1 : Algebra ι) := by
  ext a b
  by_cases hab : a = b
  · subst b
    simp [matrixUnit, Matrix.single, Matrix.sum_apply]
  · have h : ∀ i, ¬ (a = i ∧ b = i) := fun i hi => hab (hi.1.trans hi.2.symm)
    simp [matrixUnit, Matrix.single, Matrix.sum_apply, hab]

variable [Nonempty ι]

theorem trace_centredUnit (i j : ι) : Matrix.trace (centredUnit i j) = 0 := by
  have hd : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  by_cases hij : i = j
  · subst j
    simp [centredUnit, matrixUnit, Matrix.trace_sub, Matrix.trace_smul,
      Matrix.trace_one, hd]
  · simp [centredUnit, matrixUnit, hij]

omit [Nonempty ι] in
theorem centredUnit_adjoint (i j : ι) : (centredUnit i j)ᴴ = centredUnit j i := by
  by_cases hij : i = j <;>
    simp [centredUnit, matrixUnit, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_single, hij, Ne.symm]

def quadraticSum : Algebra ι :=
  ∑ i, ∑ j, centredUnit i j * centredUnit j i

theorem quadraticSum_eq :
    quadraticSum (ι := ι) =
      ((Fintype.card ι : ℂ) - (Fintype.card ι : ℂ)⁻¹) • (1 : Algebra ι) := by
  have hd : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have he (i j : ι) : centredUnit i j * centredUnit j i =
      matrixUnit i j * matrixUnit j i -
      (if i = j then (2 * (Fintype.card ι : ℂ)⁻¹) • matrixUnit i i else 0) +
      (if i = j then ((Fintype.card ι : ℂ)⁻¹ ^ 2) • (1 : Algebra ι) else 0) := by
    by_cases hij : i = j
    · subst j
      simp only [centredUnit, ite_true, sub_mul, mul_sub, smul_mul_assoc,
        mul_smul_comm, one_mul, mul_one]
      module
    · simp [centredUnit, hij, Ne.symm hij]
  simp only [quadraticSum, he, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← Finset.smul_sum, sum_diagonal_units]
  change MatrixAdjointCasimir.pairedSquareSum -
    (2 * (Fintype.card ι : ℂ)⁻¹) • (1 : Algebra ι) +
    ∑ _i : ι, ((Fintype.card ι : ℂ)⁻¹ ^ 2) • (1 : Algebra ι) = _
  rw [pairedSquareSum_eq, ← Finset.sum_smul]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : (Fintype.card ι : ℂ) * ((Fintype.card ι : ℂ)⁻¹ ^ 2) =
      (Fintype.card ι : ℂ)⁻¹ := by field_simp
  rw [hc]
  module

def coefficient (ι : Type*) [Fintype ι] : ℝ :=
  ((Fintype.card ι : ℝ) - (Fintype.card ι : ℝ)⁻¹) / 2

def response : Algebra ι := (1 / 2 : ℂ) • quadraticSum

theorem response_eq : response (ι := ι) = (coefficient ι : ℂ) • (1 : Algebra ι) := by
  rw [response, quadraticSum_eq, smul_smul]
  congr 1
  simp [coefficient, div_eq_mul_inv]
  ring

theorem response_conjugate (u : (Algebra ι)ˣ) :
    (↑u : Algebra ι) * response * (↑(u⁻¹) : Algebra ι) = response := by
  rw [response_eq]
  simp

end GeneratedFoundations.Operations.MatrixDefiningCasimir

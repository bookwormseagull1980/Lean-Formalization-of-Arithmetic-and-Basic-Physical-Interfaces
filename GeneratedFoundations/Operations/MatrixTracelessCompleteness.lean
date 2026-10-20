module

public import GeneratedFoundations.Operations.MatrixDefiningCasimir

/-!
# Trace-dual completeness after removal of the scalar direction

The centred matrix units form a redundant, canonical spanning family of the
traceless matrices. The sandwich sum below uses their trace-dual partners;
it is not an assertion that the individual centred units are orthonormal.
Its half-trace normalization agrees with the defining response and yields
the adjoint response by expansion of the complete double commutator.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Matrix

namespace GeneratedFoundations.Operations.MatrixTracelessCompleteness

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

open MatrixAdjointCasimir (Algebra matrixUnit)
open MatrixDefiningCasimir (centredUnit)

def sandwich (X : Algebra ι) : Algebra ι :=
  (1 / 2 : ℂ) • ∑ i, ∑ j, centredUnit i j * X * centredUnit j i

theorem sandwich_eq (X : Algebra ι) :
    sandwich X = (Matrix.trace X / 2) • (1 : Algebra ι) -
      (1 / (2 * Fintype.card ι) : ℂ) • X := by
  have hd : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have he (i j : ι) : centredUnit i j * X * centredUnit j i =
      matrixUnit i j * X * matrixUnit j i -
      (if i = j then (Fintype.card ι : ℂ)⁻¹ • (matrixUnit i i * X) else 0) -
      (if i = j then (Fintype.card ι : ℂ)⁻¹ • (X * matrixUnit i i) else 0) +
      (if i = j then ((Fintype.card ι : ℂ)⁻¹ ^ 2) • X else 0) := by
    by_cases hij : i = j
    · subst j
      simp only [centredUnit, ite_true, sub_mul, mul_sub,
        smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
      module
    · simp [centredUnit, hij, Ne.symm hij]
  have hs : (∑ i : ι, matrixUnit i i * X) = X := by
    rw [← Finset.sum_mul, MatrixDefiningCasimir.sum_diagonal_units, one_mul]
  have ht : (∑ i : ι, X * matrixUnit i i) = X := by
    rw [← Finset.mul_sum, MatrixDefiningCasimir.sum_diagonal_units, mul_one]
  have hc : (Fintype.card ι : ℂ) * ((Fintype.card ι : ℂ)⁻¹ ^ 2) =
      (Fintype.card ι : ℂ)⁻¹ := by field_simp
  simp only [sandwich, he, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← Finset.smul_sum, ← Finset.smul_sum, hs, ht, ← Finset.sum_smul]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hc]
  change (1 / 2 : ℂ) •
    (MatrixAdjointCasimir.sandwich X - (Fintype.card ι : ℂ)⁻¹ • X -
      (Fintype.card ι : ℂ)⁻¹ • X + (Fintype.card ι : ℂ)⁻¹ • X) = _
  rw [MatrixAdjointCasimir.sandwich_eq]
  have hi : (1 / (2 * Fintype.card ι) : ℂ) = (1 / 2) * (Fintype.card ι : ℂ)⁻¹ := by
    field_simp
  rw [hi]
  module

def adjointResponse (X : Algebra ι) : Algebra ι :=
  (1 / 2 : ℂ) • ∑ i, ∑ j,
    MatrixAdjointCasimir.commutator (centredUnit i j)
      (MatrixAdjointCasimir.commutator (centredUnit j i) X)

omit [Nonempty ι] in
theorem adjointResponse_expansion (X : Algebra ι) :
    adjointResponse X = MatrixDefiningCasimir.response * X -
      (2 : ℂ) • sandwich X + X * MatrixDefiningCasimir.response := by
  have he (i j : ι) :
      MatrixAdjointCasimir.commutator (centredUnit i j)
        (MatrixAdjointCasimir.commutator (centredUnit j i) X) =
      (centredUnit i j * centredUnit j i) * X -
        centredUnit i j * X * centredUnit j i -
        centredUnit j i * X * centredUnit i j +
        X * (centredUnit j i * centredUnit i j) := by
    unfold MatrixAdjointCasimir.commutator
    noncomm_ring
  have hs : (∑ i, ∑ j, centredUnit j i * X * centredUnit i j) =
      ∑ i, ∑ j, centredUnit i j * X * centredUnit j i := by rw [Finset.sum_comm]
  have hp : (∑ i, ∑ j, centredUnit j i * centredUnit i j) =
      MatrixDefiningCasimir.quadraticSum (ι := ι) := by
    rw [Finset.sum_comm]
    rfl
  simp only [adjointResponse, he, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  rw [hs, hp]
  change (1 / 2 : ℂ) •
    (MatrixDefiningCasimir.quadraticSum * X -
      (∑ i, ∑ j, centredUnit i j * X * centredUnit j i) -
      (∑ i, ∑ j, centredUnit i j * X * centredUnit j i) +
      X * MatrixDefiningCasimir.quadraticSum) = _
  simp only [MatrixDefiningCasimir.response, sandwich,
    smul_mul_assoc, mul_smul_comm]
  module

theorem adjointResponse_eq (X : Algebra ι) :
    adjointResponse X = (Fintype.card ι : ℂ) • X -
      Matrix.trace X • (1 : Algebra ι) := by
  have hd : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [adjointResponse_expansion, MatrixDefiningCasimir.response_eq, sandwich_eq]
  simp only [MatrixDefiningCasimir.coefficient, Complex.ofReal_div,
    Complex.ofReal_sub, Complex.ofReal_natCast, Complex.ofReal_inv,
    Complex.ofReal_ofNat, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  have hi : (1 / (2 * Fintype.card ι) : ℂ) = (Fintype.card ι : ℂ)⁻¹ / 2 := by
    field_simp
  rw [hi]
  module

theorem adjointResponse_eq_casimir (X : Algebra ι) :
    adjointResponse X = MatrixAdjointCasimir.casimir X := by
  rw [adjointResponse_eq, MatrixAdjointCasimir.casimir_eq]

theorem sandwich_conjugate (u : (Algebra ι)ˣ) (X : Algebra ι) :
    sandwich ((↑u : Algebra ι) * X * (↑(u⁻¹) : Algebra ι)) =
      (↑u : Algebra ι) * sandwich X * (↑(u⁻¹) : Algebra ι) := by
  have ht : Matrix.trace ((↑u : Algebra ι) * X * (↑(u⁻¹) : Algebra ι)) = Matrix.trace X := by
    rw [Matrix.trace_mul_cycle, Units.inv_mul, one_mul]
  rw [sandwich_eq, ht, sandwich_eq]
  simp [mul_sub, sub_mul, mul_assoc]

end GeneratedFoundations.Operations.MatrixTracelessCompleteness

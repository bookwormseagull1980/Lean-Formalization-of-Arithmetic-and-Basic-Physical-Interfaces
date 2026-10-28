module

public import GeneratedFoundations.Arithmetic.HistoryHermitianBasis

/-!
# Complete contractions in the arithmetic trace metric

The independent Hermitian generators have unit Hilbert--Schmidt norm.
Their completeness determines both the sandwich contraction and the
double commutator, including the scalar kernel. In particular their
quadratic sum is twice the half-trace defining Casimir. This factor is
calculated from the complete basis, rather than assigned from a colour
normalization. Every matrix entry and both Hermitian parts are retained.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Matrix

namespace GeneratedFoundations.Arithmetic.HistoryHermitianContraction

open HistoryCliffordAction (Index Algebra)
open HistoryHermitianBasis (GeneratorIndex generator complexCoefficient)

theorem reconstruction (N : ℕ) (X : Algebra N) :
    (∑ a, complexCoefficient N X a • generator N a) =
      X - (Matrix.trace X / (HistoryAdjointCasimir.dimension N : ℂ)) • 1 := by
  let Y := X - (Matrix.trace X / (HistoryAdjointCasimir.dimension N : ℂ)) •
    (1 : Algebra N)
  have hd : (HistoryAdjointCasimir.dimension N : ℂ) ≠ 0 := by
    exact_mod_cast (HistoryAdjointCasimir.dimension_pos N).ne'
  have hy : Matrix.trace Y = 0 := by
    simp only [Y, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]
    change Matrix.trace X - Matrix.trace X /
      (HistoryAdjointCasimir.dimension N : ℂ) * HistoryAdjointCasimir.dimension N = 0
    field_simp
    ring
  have hc (a : GeneratorIndex N) : complexCoefficient N Y a = complexCoefficient N X a := by
    simp [complexCoefficient, Y, Matrix.mul_sub,
      Matrix.trace_sub, Matrix.trace_smul, HistoryHermitianBasis.generator_trace]
  simpa only [hc] using HistoryHermitianBasis.complex_expansion N Y hy

/-- The full four-index contraction, with the trace direction removed. -/
theorem completeness_entry (N : ℕ) (i j k l : Index N) :
    (∑ a, generator N a i j * generator N a k l) =
      (1 : Algebra N) i l * (1 : Algebra N) k j -
        (HistoryAdjointCasimir.dimension N : ℂ)⁻¹ *
          (1 : Algebra N) i j * (1 : Algebra N) k l := by
  have h := congrArg (fun X : Algebra N => X i j)
    (reconstruction N (Matrix.single l k 1))
  have ht : Matrix.trace (Matrix.single l k (1 : ℂ)) = (1 : Algebra N) k l := by
    by_cases h : l = k
    · subst k
      simp
    · simp [h, Ne.symm h]
  have he : (Matrix.single l k (1 : ℂ)) i j =
      (1 : Algebra N) i l * (1 : Algebra N) k j := by
    simp only [Matrix.single, Matrix.of_apply, Matrix.one_apply, ite_and]
    by_cases hil : i = l <;> by_cases hjk : j = k <;> simp [hil, hjk, Ne.symm]
  simp only [complexCoefficient, Matrix.trace_mul_single, op_smul_eq_smul,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply, ht, one_mul] at h
  rw [Finset.sum_congr rfl (fun a _ => mul_comm _ _)] at h
  rw [he] at h
  calc
    _ = _ := h
    _ = _ := by ring

def sandwich (N : ℕ) (X : Algebra N) : Algebra N :=
  ∑ a, generator N a * X * generator N a

theorem sandwich_eq (N : ℕ) (X : Algebra N) :
    sandwich N X = Matrix.trace X • (1 : Algebra N) -
      (HistoryAdjointCasimir.dimension N : ℂ)⁻¹ • X := by
  ext i j
  calc
    sandwich N X i j =
        ∑ k, ∑ l, X l k * (∑ a, generator N a i l * generator N a k j) := by
      simp only [sandwich, Matrix.sum_apply, Matrix.mul_apply,
        Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by
      simp_rw [completeness_entry]
      simp only [mul_sub, Finset.sum_sub_distrib]
      by_cases hij : i = j
      · subst j
        simp [Matrix.one_apply, Matrix.trace, Matrix.sub_apply,
          Matrix.smul_apply, smul_eq_mul, mul_comm, Finset.mul_sum]
      · simp [Matrix.one_apply, Matrix.sub_apply, Matrix.smul_apply,
          smul_eq_mul, hij, mul_comm]

def squareSum (N : ℕ) : Algebra N := ∑ a, generator N a * generator N a

theorem squareSum_eq (N : ℕ) :
    squareSum N =
      ((HistoryAdjointCasimir.dimension N : ℂ) -
        (HistoryAdjointCasimir.dimension N : ℂ)⁻¹) • (1 : Algebra N) := by
  simpa [sandwich, squareSum, Matrix.trace_one,
    HistoryAdjointCasimir.dimension, sub_smul] using sandwich_eq N (1 : Algebra N)

theorem squareSum_eq_twice_defining (N : ℕ) :
    squareSum N = (2 * (HistoryDefiningResponse.coefficient N : ℂ)) • (1 : Algebra N) := by
  rw [squareSum_eq]
  congr 1
  simp only [HistoryDefiningResponse.coefficient, Operations.MatrixDefiningCasimir.coefficient,
    Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_inv, Complex.ofReal_natCast,
    Complex.ofReal_ofNat]
  change (HistoryAdjointCasimir.dimension N : ℂ) -
    (HistoryAdjointCasimir.dimension N : ℂ)⁻¹ =
      2 * (((HistoryAdjointCasimir.dimension N : ℂ) -
        (HistoryAdjointCasimir.dimension N : ℂ)⁻¹) / 2)
  ring

def doubleCommutator (N : ℕ) (X : Algebra N) : Algebra N :=
  ∑ a, Operations.MatrixAdjointCasimir.commutator (generator N a)
    (Operations.MatrixAdjointCasimir.commutator (generator N a) X)

theorem doubleCommutator_expansion (N : ℕ) (X : Algebra N) :
    doubleCommutator N X = squareSum N * X - 2 • sandwich N X + X * squareSum N := by
  calc
    doubleCommutator N X = ∑ a,
        (generator N a * generator N a * X -
          2 • (generator N a * X * generator N a) +
          X * (generator N a * generator N a)) := by
      apply Finset.sum_congr rfl
      intro a _
      unfold Operations.MatrixAdjointCasimir.commutator
      simp only [two_smul]
      noncomm_ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.smul_sum, squareSum, sandwich]

theorem doubleCommutator_eq (N : ℕ) (X : Algebra N) :
    doubleCommutator N X =
      (2 * (HistoryAdjointCasimir.dimension N : ℂ)) • X -
        (2 * Matrix.trace X) • (1 : Algebra N) := by
  rw [doubleCommutator_expansion, squareSum_eq, sandwich_eq]
  simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  module

theorem doubleCommutator_eq_twice_adjoint (N : ℕ) (X : Algebra N) :
    doubleCommutator N X = (2 : ℂ) • HistoryAdjointCasimir.casimir N X := by
  rw [doubleCommutator_eq, HistoryAdjointCasimir.casimir_eq]
  module

theorem doubleCommutator_traceless (N : ℕ) (X : Algebra N)
    (hX : Matrix.trace X = 0) :
    doubleCommutator N X = (2 * (HistoryAdjointCasimir.dimension N : ℂ)) • X := by
  simp [doubleCommutator_eq, hX]

theorem doubleCommutator_scalar (N : ℕ) (c : ℂ) :
    doubleCommutator N (c • (1 : Algebra N)) = 0 := by
  rw [doubleCommutator_eq_twice_adjoint]
  simp [HistoryAdjointCasimir.casimir, Operations.MatrixAdjointCasimir.casimir_scalar]

/-- Every orthogonal change of the independent real coordinates has the
same defining response. No generator basis is an extra source choice. -/
theorem squareSum_basis_independent (N : ℕ)
    (O : Matrix (GeneratorIndex N) (GeneratorIndex N) ℝ)
    (hO : Operations.OrthogonalQuadraticFrame.OrthogonalChange O) :
    (∑ a, Operations.OrthogonalQuadraticFrame.rotated O (generator N) a *
      Operations.OrthogonalQuadraticFrame.rotated O (generator N) a) = squareSum N :=
  Operations.OrthogonalQuadraticFrame.quadratic_invariant O hO (generator N)

end GeneratedFoundations.Arithmetic.HistoryHermitianContraction

module

public import GeneratedFoundations.Operations.MatrixTracelessCompleteness
public import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# A complete Hermitian frame with its computed quadratic response

The centred matrix units are a trace-dual frame, not a Hermitian orthonormal
basis. Their symmetric and antisymmetric combinations below are Hermitian.
The ordered-pair indexing is redundant; both its reconstruction and its
quadratic normalization are retained explicitly. In particular no assertion
of linear independence is made for this family.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Matrix

namespace GeneratedFoundations.Operations.MatrixHermitianFrame

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

open MatrixAdjointCasimir (Algebra matrixUnit)
open MatrixDefiningCasimir (centredUnit)

def symmetric (i j : ι) : Algebra ι :=
  (1 / 2 : ℂ) • (centredUnit i j + centredUnit j i)

def antisymmetric (i j : ι) : Algebra ι :=
  (-Complex.I / 2 : ℂ) • (centredUnit i j - centredUnit j i)

omit [Nonempty ι] in
theorem symmetric_hermitian (i j : ι) : (symmetric i j).IsHermitian := by
  change (symmetric i j)ᴴ = symmetric i j
  simp [symmetric, Matrix.conjTranspose_smul, MatrixDefiningCasimir.centredUnit_adjoint,
    add_comm]

omit [Nonempty ι] in
theorem antisymmetric_hermitian (i j : ι) : (antisymmetric i j).IsHermitian := by
  change (antisymmetric i j)ᴴ = antisymmetric i j
  simp only [antisymmetric, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
    MatrixDefiningCasimir.centredUnit_adjoint]
  have hc : star (-Complex.I / 2 : ℂ) = Complex.I / 2 := by simp
  rw [hc]
  module

theorem symmetric_trace (i j : ι) : Matrix.trace (symmetric i j) = 0 := by
  simp [symmetric, Matrix.trace_smul, Matrix.trace_add,
    MatrixDefiningCasimir.trace_centredUnit]

theorem antisymmetric_trace (i j : ι) : Matrix.trace (antisymmetric i j) = 0 := by
  simp [antisymmetric, Matrix.trace_smul, Matrix.trace_sub,
    MatrixDefiningCasimir.trace_centredUnit]

omit [Nonempty ι] in
theorem centred_reconstruction (i j : ι) :
    symmetric i j + Complex.I • antisymmetric i j = centredUnit i j := by
  simp only [symmetric, antisymmetric, smul_smul]
  have hc : Complex.I * (-Complex.I / 2) = (1 / 2 : ℂ) := by
    ring_nf
    norm_num [Complex.I_sq]
  rw [hc]
  module

omit [Nonempty ι] in
theorem matrixUnit_expansion (X : Algebra ι) :
    (∑ i, ∑ j, X i j • matrixUnit i j) = X := by
  ext a b
  simp [matrixUnit, Matrix.single, Matrix.sum_apply, ite_and]

omit [Nonempty ι] in
theorem centred_expansion (X : Algebra ι) (hX : Matrix.trace X = 0) :
    (∑ i, ∑ j, X i j • centredUnit i j) = X := by
  simp only [centredUnit, smul_sub, Finset.sum_sub_distrib, smul_smul]
  rw [matrixUnit_expansion]
  have he : (∑ i, ∑ j,
      (X i j * if i = j then (Fintype.card ι : ℂ)⁻¹ else 0) • (1 : Algebra ι)) = 0 := by
    simp only [mul_ite, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
    rw [← Finset.sum_smul, ← Finset.sum_mul]
    change (Matrix.trace X * (Fintype.card ι : ℂ)⁻¹) • (1 : Algebra ι) = 0
    rw [hX, zero_mul, zero_smul]
  rw [he, sub_zero]

omit [Nonempty ι] in
/-- All traceless directions are reconstructed with their original entries. -/
theorem complete_expansion (X : Algebra ι) (hX : Matrix.trace X = 0) :
    (∑ i, ∑ j, X i j • (symmetric i j + Complex.I • antisymmetric i j)) = X := by
  simp_rw [centred_reconstruction]
  exact centred_expansion X hX

omit [Nonempty ι] in
theorem pair_square (i j : ι) :
    symmetric i j * symmetric i j + antisymmetric i j * antisymmetric i j =
      (1 / 2 : ℂ) •
        (centredUnit i j * centredUnit j i + centredUnit j i * centredUnit i j) := by
  simp only [symmetric, antisymmetric, smul_mul_assoc, mul_smul_comm, smul_smul]
  have hc : (-Complex.I / 2 : ℂ) * (-Complex.I / 2) = -1 / 4 := by
    ring_nf
    norm_num [Complex.I_sq]
  rw [hc]
  norm_num only
  simp only [add_mul, mul_add, sub_mul, mul_sub]
  module

def response : Algebra ι :=
  (1 / 2 : ℂ) • ∑ i, ∑ j,
    (symmetric i j * symmetric i j + antisymmetric i j * antisymmetric i j)

omit [Nonempty ι] in
/-- The Hermitian frame and the original trace-dual frame have exactly the
same half-trace normalization. -/
theorem response_eq_traceDual : response (ι := ι) = MatrixDefiningCasimir.response := by
  have hs : (∑ i : ι, ∑ j : ι, centredUnit j i * centredUnit i j) =
      ∑ i : ι, ∑ j : ι, centredUnit i j * centredUnit j i := by
    rw [Finset.sum_comm]
  simp only [response, pair_square, ← Finset.smul_sum, Finset.sum_add_distrib]
  rw [hs]
  simp only [MatrixDefiningCasimir.response, MatrixDefiningCasimir.quadraticSum]
  module

theorem response_eq : response (ι := ι) =
    (MatrixDefiningCasimir.coefficient ι : ℂ) • (1 : Algebra ι) := by
  rw [response_eq_traceDual, MatrixDefiningCasimir.response_eq]

theorem response_conjugate (u : (Algebra ι)ˣ) :
    (↑u : Algebra ι) * response * (↑(u⁻¹) : Algebra ι) = response := by
  rw [response_eq_traceDual]
  exact MatrixDefiningCasimir.response_conjugate u

end GeneratedFoundations.Operations.MatrixHermitianFrame

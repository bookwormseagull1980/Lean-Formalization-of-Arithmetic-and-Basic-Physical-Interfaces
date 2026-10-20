module

public import GeneratedFoundations.Operations.MatrixDefiningCasimir
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Basis-independent defining response of a finite Hilbert space

The response is the trace-dual quadratic sum of all centred matrix units
in an orthonormal basis. Its computed value depends only on the dimension.
Consequently a basis used to calculate the sum is not additional response
data. The zero-dimensional case is included.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Operations.FiniteDefiningResponse

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [Fintype ι] [DecidableEq ι]

def generator (b : OrthonormalBasis ι ℂ E) (i j : ι) : Module.End ℂ E :=
  Matrix.toLinAlgEquiv b.toBasis (MatrixDefiningCasimir.centredUnit i j)

def response (b : OrthonormalBasis ι ℂ E) : Module.End ℂ E :=
  (1 / 2 : ℂ) • ∑ i, ∑ j, generator b i j * generator b j i

theorem matrix_response_eq :
    MatrixDefiningCasimir.response (ι := ι) =
      (MatrixDefiningCasimir.coefficient ι : ℂ) • (1 : Matrix ι ι ℂ) := by
  cases isEmpty_or_nonempty ι with
  | inl h =>
    let := h
    ext i
    exact isEmptyElim i
  | inr h =>
    let := h
    exact MatrixDefiningCasimir.response_eq

theorem response_eq (b : OrthonormalBasis ι ℂ E) :
    response b = (MatrixDefiningCasimir.coefficient ι : ℂ) • (1 : Module.End ℂ E) := by
  have h := congrArg (Matrix.toLinAlgEquiv b.toBasis) (matrix_response_eq (ι := ι))
  simpa only [MatrixDefiningCasimir.response, MatrixDefiningCasimir.quadraticSum,
    response, generator, map_smul, map_sum, map_mul, map_one] using h

def coefficient (E : Type*) [AddCommGroup E] [Module ℂ E] : ℝ :=
  ((Module.finrank ℂ E : ℝ) - (Module.finrank ℂ E : ℝ)⁻¹) / 2

omit [DecidableEq ι] in
theorem coefficient_basis (b : OrthonormalBasis ι ℂ E) :
    MatrixDefiningCasimir.coefficient ι = coefficient E := by
  unfold MatrixDefiningCasimir.coefficient coefficient
  rw [Module.finrank_eq_card_basis b.toBasis]

theorem response_intrinsic (b : OrthonormalBasis ι ℂ E) :
    response b = (coefficient E : ℂ) • (1 : Module.End ℂ E) := by
  rw [response_eq, coefficient_basis b]

theorem response_basis_independent {κ : Type*} [Fintype κ] [DecidableEq κ]
    (b : OrthonormalBasis ι ℂ E) (c : OrthonormalBasis κ ℂ E) : response b = response c := by
  rw [response_intrinsic, response_intrinsic]

theorem coefficient_nonneg : 0 ≤ coefficient E := by
  by_cases h : Module.finrank ℂ E = 0
  · simp [coefficient, h]
  · have hd : (1 : ℝ) ≤ Module.finrank ℂ E := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
    have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hd
    simp only [one_div, inv_one] at hi
    unfold coefficient
    linarith

theorem coefficient_pos (hd : 2 ≤ Module.finrank ℂ E) : 0 < coefficient E := by
  have hr : (2 : ℝ) ≤ Module.finrank ℂ E := by exact_mod_cast hd
  have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hr
  simp only [one_div] at hi
  unfold coefficient
  norm_num at hi
  linarith

theorem response_adjoint [FiniteDimensional ℂ E] (b : OrthonormalBasis ι ℂ E) :
    (response b).adjoint = response b := by
  symm
  apply (LinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  rw [response_intrinsic]
  change inner ℂ ((coefficient E : ℂ) • x) y = inner ℂ x ((coefficient E : ℂ) • y)
  rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal]

theorem quadratic (b : OrthonormalBasis ι ℂ E) (x : E) :
    (inner ℂ x (response b x)).re = coefficient E * ‖x‖ ^ 2 := by
  rw [response_intrinsic]
  change (inner ℂ x ((coefficient E : ℂ) • x)).re = _
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
  simp [Complex.mul_re, pow_two]

theorem quadratic_nonneg (b : OrthonormalBasis ι ℂ E) (x : E) :
    0 ≤ (inner ℂ x (response b x)).re := by
  rw [quadratic]
  exact mul_nonneg coefficient_nonneg (sq_nonneg _)

end GeneratedFoundations.Operations.FiniteDefiningResponse

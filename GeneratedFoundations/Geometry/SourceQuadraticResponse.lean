module

public import GeneratedFoundations.Geometry.SourceSymmetricPowers
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Data.Matrix.Basis
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Tactic.NormNum

/-!
# The full algebra of quadratic source responses

The carrier is the actual degree-two homogeneous source space. Its three
monomial coefficients give a linear equivalence, used only to compute the
induced operators. Two determinant-one unitary source matrices suffice:
one separates the three monomial weights, and the other has no zero matrix
entry between them. Polynomial interpolation and multiplication then give
every matrix unit and hence every endomorphism of the original carrier.

The result concerns the generated associative complex algebra. It does not
identify the source group with a larger frame group, require the monomial
coordinates to be orthonormal, or assume a classification of irreducible
source representations.
-/

@[expose] public section

noncomputable section

open scoped BigOperators ComplexConjugate
open Module MvPolynomial
open GeneratedFoundations.Operations.SourceSpinCorner
open GeneratedFoundations.Operations.SourceSpinCornerGroup
open GeneratedFoundations.Geometry.SourceSymmetricPowers

namespace GeneratedFoundations.Geometry.SourceQuadraticResponse

abbrev Quadratic := Carrier 2
abbrev CoordinateSpace := Fin 3 → ℂ
abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℂ

def monomialVector (i : Fin 3) : Quadratic :=
  ⟨MvPolynomial.monomial (exponentOfIndex 2 i).val 1,
    MvPolynomial.isHomogeneous_monomial 1 (exponentOfIndex 2 i).property⟩

def coefficients : Quadratic →ₗ[ℂ] CoordinateSpace where
  toFun p i := (p : PolynomialSpace).coeff (exponentOfIndex 2 i).val
  map_add' p q := by ext i; simp
  map_smul' c p := by ext i; simp

def synthesis : CoordinateSpace →ₗ[ℂ] Quadratic where
  toFun c := ∑ i, c i • monomialVector i
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a c := by simp [Finset.smul_sum, smul_smul]

theorem exponentOfIndex_val_injective :
    Function.Injective (fun i : Fin 3 => (exponentOfIndex 2 i).val) := by
  intro i j h
  exact (exponentEquiv 2).symm.injective (Subtype.ext h)

theorem monomialVector_coefficient (i j : Fin 3) :
    coefficients (monomialVector j) i = if j = i then 1 else 0 := by
  change (MvPolynomial.monomial (exponentOfIndex 2 j).val (1 : ℂ)).coeff
    (exponentOfIndex 2 i).val = _
  simp only [MvPolynomial.coeff_monomial, exponentOfIndex_val_injective.eq_iff]

theorem coefficients_synthesis (c : CoordinateSpace) : coefficients (synthesis c) = c := by
  funext i
  change coefficients (∑ j, c j • monomialVector j) i = c i
  simp [map_sum, map_smul, monomialVector_coefficient]

theorem synthesis_injective : Function.Injective synthesis := by
  intro c d h
  have := congrArg coefficients h
  simpa only [coefficients_synthesis] using this

/-- Surjectivity uses the already constructed complete homogeneous basis;
the three coordinates do not replace the original carrier by definition. -/
theorem synthesis_surjective : Function.Surjective synthesis := by
  let e : Quadratic ≃ₗ[ℂ] CoordinateSpace := (monomialBasis 2).equivFun
  let f : CoordinateSpace →ₗ[ℂ] CoordinateSpace := e.toLinearMap.comp synthesis
  have hinj : Function.Injective f := e.injective.comp synthesis_injective
  have hsurj : Function.Surjective f := LinearMap.injective_iff_surjective.mp hinj
  intro p
  obtain ⟨c, hc⟩ := hsurj (e p)
  exact ⟨c, e.injective hc⟩

theorem synthesis_coefficients (p : Quadratic) : synthesis (coefficients p) = p := by
  obtain ⟨c, rfl⟩ := synthesis_surjective p
  rw [coefficients_synthesis]

def coordinateEquiv : Quadratic ≃ₗ[ℂ] CoordinateSpace where
  __ := coefficients
  invFun := synthesis
  left_inv := synthesis_coefficients
  right_inv := coefficients_synthesis

@[simp]
theorem coordinateEquiv_apply (p : Quadratic) : coordinateEquiv p = coefficients p := rfl

@[simp]
theorem coordinateEquiv_symm_apply (c : CoordinateSpace) :
    coordinateEquiv.symm c = synthesis c := rfl

theorem monomialVector_zero : (monomialVector 0 : PolynomialSpace) = X 0 ^ 2 := by
  simp [monomialVector, monomial_binary, exponentOfIndex]

theorem monomialVector_one : (monomialVector 1 : PolynomialSpace) = X 0 * X 1 := by
  simp [monomialVector, monomial_binary, exponentOfIndex]

theorem monomialVector_two : (monomialVector 2 : PolynomialSpace) = X 1 ^ 2 := by
  simp [monomialVector, monomial_binary, exponentOfIndex]

theorem synthesis_polynomial (c : CoordinateSpace) :
    (synthesis c : PolynomialSpace) =
      C (c 0) * X 0 ^ 2 + C (c 1) * X 0 * X 1 + C (c 2) * X 1 ^ 2 := by
  simp [synthesis, Fin.sum_univ_three, monomialVector_zero, monomialVector_one,
    monomialVector_two, Algebra.smul_def, MvPolynomial.algebraMap_eq, mul_assoc]

/-- Matrix coefficients of the actual homogeneous substitution in the
ordered basis `X₀², X₀ X₁, X₁²`. -/
def responseMatrix (M : Mat2) : Mat3 :=
  !![M 0 0 ^ 2, M 0 0 * M 0 1, M 0 1 ^ 2;
     2 * M 0 0 * M 1 0, M 0 0 * M 1 1 + M 0 1 * M 1 0, 2 * M 0 1 * M 1 1;
     M 1 0 ^ 2, M 1 0 * M 1 1, M 1 1 ^ 2]

theorem degreeAction_synthesis (M : Mat2) (c : CoordinateSpace) :
    degreeAction 2 M (synthesis c) = synthesis ((responseMatrix M).mulVec c) := by
  apply Subtype.ext
  change polynomialAction M (synthesis c : PolynomialSpace) =
    (synthesis ((responseMatrix M).mulVec c) : PolynomialSpace)
  rw [synthesis_polynomial, synthesis_polynomial]
  simp [polynomialAction, variableImage, responseMatrix, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, Fin.sum_univ_three, MvPolynomial.algebraMap_eq]
  simp only [map_ofNat]
  ring

theorem source_intertwines (U : SU2) (p : Quadratic) :
    coefficients (sourceRepresentation 2 U p) =
      (responseMatrix (U : Mat2)).mulVec (coefficients p) := by
  obtain ⟨c, rfl⟩ := synthesis_surjective p
  change coefficients (degreeAction 2 (U : Mat2) (synthesis c)) = _
  simp only [degreeAction_synthesis, coefficients_synthesis]

/-- All endomorphisms, including those not obtained from a single source
operation, are transported by this algebra equivalence. -/
def endomorphismCoordinates : Module.End ℂ Quadratic ≃ₐ[ℂ] Mat3 :=
  (coordinateEquiv.conjAlgEquiv ℂ).trans LinearMap.toMatrixAlgEquiv'

theorem endomorphismCoordinates_source (U : SU2) :
    endomorphismCoordinates (sourceRepresentation 2 U) = responseMatrix (U : Mat2) := by
  apply Matrix.toLinAlgEquiv'.injective
  change Matrix.toLinAlgEquiv'
      (LinearMap.toMatrixAlgEquiv' ((coordinateEquiv.conjAlgEquiv ℂ)
        (sourceRepresentation 2 U))) = Matrix.toLinAlgEquiv' (responseMatrix (U : Mat2))
  rw [Matrix.toLinAlgEquiv'_toMatrixAlgEquiv']
  apply LinearMap.ext
  intro c
  change coefficients (sourceRepresentation 2 U (synthesis c)) =
    (responseMatrix (U : Mat2)).mulVec c
  rw [source_intertwines, coefficients_synthesis]

def sourcePhase : ℂ := (3 + 4 * Complex.I) / 5

def diagonalSource : SU2 :=
  ⟨canonical sourcePhase 0, canonical_mem_specialUnitary _ _ (by
    rw [← Complex.normSq_eq_norm_sq]
    norm_num [sourcePhase, Complex.normSq_apply, Complex.div_re, Complex.div_im])⟩

def mixingSource : SU2 :=
  ⟨canonical (3 / 5) (4 / 5), canonical_mem_specialUnitary _ _ (by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    norm_num [Complex.normSq_apply, Complex.div_re, Complex.div_im])⟩

def weights : Fin 3 → ℂ :=
  ![(-7 + 24 * Complex.I) / 25, 1, (-7 - 24 * Complex.I) / 25]

def diagonalResponse : Mat3 := Matrix.diagonal weights

def mixingResponse : Mat3 :=
  (1 / 25 : ℂ) • !![9, 12, 16; -24, -7, 24; 16, -12, 9]

theorem diagonalSource_response : responseMatrix (diagonalSource : Mat2) = diagonalResponse := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    norm_num [responseMatrix, diagonalSource, canonical, sourcePhase,
      diagonalResponse, weights, Matrix.diagonal, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im, Complex.normSq_apply, pow_two]

theorem mixingSource_response : responseMatrix (mixingSource : Mat2) = mixingResponse := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [responseMatrix, mixingSource, canonical, mixingResponse]
  all_goals norm_num [map_ofNat]

theorem weights_injective : Function.Injective weights := by
  intro i j h
  fin_cases i <;> fin_cases j <;> try rfl
  all_goals
    have him := congrArg Complex.im h
    norm_num [weights, Complex.div_re, Complex.div_im, Complex.normSq_apply] at him

theorem mixingResponse_entry_ne_zero (i j : Fin 3) : mixingResponse i j ≠ 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [mixingResponse]

def leftOther : Fin 3 → Fin 3 := ![1, 0, 0]
def rightOther : Fin 3 → Fin 3 := ![2, 2, 1]

def interpolationCoefficient : Fin 3 → ℂ :=
  ![-25 / 128 + (25 / 96) * Complex.I, 25 / 64, -25 / 128 - (25 / 96) * Complex.I]

theorem interpolation_normalized (i : Fin 3) :
    interpolationCoefficient i * (weights i - weights (leftOther i)) *
      (weights i - weights (rightOther i)) = 1 := by
  fin_cases i <;> apply Complex.ext <;>
    norm_num [interpolationCoefficient, weights, leftOther, rightOther,
      Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im, Complex.normSq_apply]

def weightProjection (i : Fin 3) : Mat3 :=
  interpolationCoefficient i •
    ((diagonalResponse - weights (leftOther i) • 1) *
      (diagonalResponse - weights (rightOther i) • 1))

theorem weightProjection_eq_single (i : Fin 3) : weightProjection i = Matrix.single i i 1 := by
  funext r s
  fin_cases i <;> fin_cases r <;> fin_cases s <;>
    apply Complex.ext <;>
    norm_num [weightProjection, interpolationCoefficient, diagonalResponse, weights,
      leftOther, rightOther, Matrix.mul_apply, Matrix.diagonal, Matrix.single,
      Fin.sum_univ_three, Complex.mul_re, Complex.mul_im, Complex.div_re,
      Complex.div_im, Complex.normSq_apply]

/-- The generated algebra is defined on the original homogeneous carrier. -/
def responseAlgebra : Subalgebra ℂ (Module.End ℂ Quadratic) :=
  Algebra.adjoin ℂ (Set.range (sourceRepresentation 2))

def coordinateAlgebra : Subalgebra ℂ Mat3 :=
  responseAlgebra.map endomorphismCoordinates.toAlgHom

theorem source_mem_responseAlgebra (U : SU2) : sourceRepresentation 2 U ∈ responseAlgebra :=
  Algebra.subset_adjoin (Set.mem_range_self U)

theorem responseMatrix_mem (U : SU2) : responseMatrix (U : Mat2) ∈ coordinateAlgebra := by
  apply Subalgebra.mem_map.mpr
  exact ⟨sourceRepresentation 2 U, source_mem_responseAlgebra U,
    endomorphismCoordinates_source U⟩

theorem diagonalResponse_mem : diagonalResponse ∈ coordinateAlgebra := by
  rw [← diagonalSource_response]
  exact responseMatrix_mem diagonalSource

theorem mixingResponse_mem : mixingResponse ∈ coordinateAlgebra := by
  rw [← mixingSource_response]
  exact responseMatrix_mem mixingSource

theorem weightProjection_mem (i : Fin 3) : weightProjection i ∈ coordinateAlgebra := by
  apply coordinateAlgebra.smul_mem
  apply coordinateAlgebra.mul_mem
  · exact coordinateAlgebra.sub_mem diagonalResponse_mem
      (coordinateAlgebra.smul_mem coordinateAlgebra.one_mem _)
  · exact coordinateAlgebra.sub_mem diagonalResponse_mem
      (coordinateAlgebra.smul_mem coordinateAlgebra.one_mem _)

theorem diagonalUnit_mem (i : Fin 3) : Matrix.single i i (1 : ℂ) ∈ coordinateAlgebra := by
  rw [← weightProjection_eq_single]
  exact weightProjection_mem i

theorem matrixUnit_mem (i j : Fin 3) : Matrix.single i j (1 : ℂ) ∈ coordinateAlgebra := by
  have hproduct :
      Matrix.single i i (1 : ℂ) * mixingResponse * Matrix.single j j 1 ∈ coordinateAlgebra :=
    coordinateAlgebra.mul_mem
      (coordinateAlgebra.mul_mem (diagonalUnit_mem i) mixingResponse_mem) (diagonalUnit_mem j)
  have hscaled := coordinateAlgebra.smul_mem hproduct (mixingResponse i j)⁻¹
  simpa only [Matrix.single_mul_mul_single, one_mul, mul_one,
    Matrix.smul_single, smul_eq_mul, inv_mul_cancel₀ (mixingResponse_entry_ne_zero i j)]
    using hscaled

theorem coordinateAlgebra_eq_top : coordinateAlgebra = ⊤ := by
  apply top_unique
  intro M _
  rw [Matrix.matrix_eq_sum_single M]
  apply coordinateAlgebra.sum_mem
  intro i _
  apply coordinateAlgebra.sum_mem
  intro j _
  have h := coordinateAlgebra.smul_mem (matrixUnit_mem i j) (M i j)
  simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using h

/-- Every complex-linear endomorphism of the actual quadratic carrier is a
finite algebraic combination of induced source operations. -/
theorem responseAlgebra_eq_top : responseAlgebra = ⊤ := by
  apply top_unique
  intro A _
  have hA : endomorphismCoordinates A ∈ coordinateAlgebra := by
    rw [coordinateAlgebra_eq_top]
    trivial
  obtain ⟨B, hB, hBA⟩ := Subalgebra.mem_map.mp hA
  exact endomorphismCoordinates.injective hBA ▸ hB

/-- Consequently every unital complex response algebra containing the
source operations is already the full endomorphism algebra. -/
theorem containing_source_eq_top (A : Subalgebra ℂ (Module.End ℂ Quadratic))
    (hA : ∀ U : SU2, sourceRepresentation 2 U ∈ A) : A = ⊤ := by
  apply top_unique
  rw [← responseAlgebra_eq_top]
  apply Algebra.adjoin_le
  rintro _ ⟨U, rfl⟩
  exact hA U

end GeneratedFoundations.Geometry.SourceQuadraticResponse

module

public import GeneratedFoundations.Physical.SourceJointResponse
public import GeneratedFoundations.Physical.SourceVacuumTransport
public import GeneratedFoundations.Operations.SourceNumberFlow

/-!
# The Gaussian phase frame in the degree-one Haar carrier

The degree-one coefficient map is the original two-component vector.
Its source orbit has the same inner product at every group element.
Normalized Haar integration therefore preserves that inner product
without a further change of scale. The explicit polynomial map, rather
than an arbitrary choice of orthonormal basis, identifies the Gaussian
vacuum and first excitation with the two Haar spinor directions.

This identification concerns the common source representation. It does
not identify independently chosen left and right frame bundles.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open GeneratedFoundations.Correlation.ComplexGaussianStates
open GeneratedFoundations.Operations.HermiteSource
open GeneratedFoundations.Operations.SourceSpinCorner
open GeneratedFoundations.Operations.SourceSpinCornerGroup
open GeneratedFoundations.Geometry.SourceSymmetricPowers
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Physical.SourceJointResponse (S sourceOperator)
open GeneratedFoundations.Physical.SourceVacuumTransport

namespace GeneratedFoundations.Physical.SourceSpinIdentification

/-- These coefficients retain the order of the original two source modes. -/
theorem coefficientVector_degreeOne (v : Fin 2 → ℂ) :
    coefficientVector 1 (degreeOnePolynomial v) = WithLp.toLp 2 v := by
  apply PiLp.ext
  intro i
  change (degreeOnePolynomial v : PolynomialSpace).coeff
    (exponentOfIndex 1 i).val = v i
  fin_cases i
  · simpa [exponentOfIndex] using degreeOne_coefficient v 0
  · simpa [exponentOfIndex] using degreeOne_coefficient v 1

def coordinateEquiv : Coordinates ≃ₗ[ℂ] S :=
  ((WithLp.linearEquiv 2 ℂ (Fin 2 → ℂ)).trans degreeOneEquiv).trans (carrierEquiv 1)

@[simp] theorem coordinateEquiv_apply (v : Coordinates) :
    coordinateEquiv v = carrierEquiv 1 (degreeOnePolynomial (WithLp.ofLp v)) := rfl

private theorem column_inner (U : SU2) (v w : Coordinates) :
    inner ℂ (WithLp.toLp 2 ((U : Mat2).mulVec (WithLp.ofLp v)))
      (WithLp.toLp 2 ((U : Mat2).mulVec (WithLp.ofLp w))) = inner ℂ v w := by
  let hb : 0 < (1 : ℝ) := by norm_num
  let x := (sourceCoordinates hb).symm v
  let y := (sourceCoordinates hb).symm w
  have hU : (U : Mat2) ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    (Matrix.mem_specialUnitaryGroup_iff.mp U.property).1
  have hinner := (LinearMap.norm_map_iff_inner_map_map (sourceAction hb (U : Mat2))).mp
    (sourceAction_norm hb (U : Mat2) hU)
  have hx : sourceCoordinates hb x = v := (sourceCoordinates hb).apply_symm_apply v
  have hy : sourceCoordinates hb y = w := (sourceCoordinates hb).apply_symm_apply w
  have hcx : sourceCoordinates hb (sourceAction hb (U : Mat2) x) =
      WithLp.toLp 2 ((U : Mat2).mulVec (WithLp.ofLp v)) := by
    simpa only [hx] using sourceAction_coordinates hb (U : Mat2) x
  have hcy : sourceCoordinates hb (sourceAction hb (U : Mat2) y) =
      WithLp.toLp 2 ((U : Mat2).mulVec (WithLp.ofLp w)) := by
    simpa only [hy] using sourceAction_coordinates hb (U : Mat2) y
  rw [← hcx, ← hcy, (sourceCoordinates hb).inner_map_map, hinner,
    ← (sourceCoordinates hb).inner_map_map x y, hx, hy]

theorem orbit_degreeOne (v : Coordinates) (U : SU2) :
    orbitContinuous 1 (degreeOnePolynomial (WithLp.ofLp v)) U =
      WithLp.toLp 2 (((U⁻¹ : SU2) : Mat2).mulVec (WithLp.ofLp v)) := by
  rw [orbitContinuous_apply, degreeOne_intertwines, coefficientVector_degreeOne]

/-- The Haar realization uses the already normalized source metric. -/
theorem coordinateEquiv_inner (v w : Coordinates) :
    inner ℂ (coordinateEquiv v) (coordinateEquiv w) = inner ℂ v w := by
  change inner ℂ
    (orbitEmbedding 1 (degreeOnePolynomial (WithLp.ofLp v)))
    (orbitEmbedding 1 (degreeOnePolynomial (WithLp.ofLp w))) = _
  rw [L2.inner_def]
  calc
    (∫ U, inner ℂ (orbitEmbedding 1 (degreeOnePolynomial (WithLp.ofLp v)) U)
        (orbitEmbedding 1 (degreeOnePolynomial (WithLp.ofLp w)) U) ∂sourceHaar) =
        ∫ _ : SU2, inner ℂ v w ∂sourceHaar := by
      apply integral_congr_ae
      have hv := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) sourceHaar
        (orbitContinuous 1 (degreeOnePolynomial (WithLp.ofLp v)))
      have hw := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) sourceHaar
        (orbitContinuous 1 (degreeOnePolynomial (WithLp.ofLp w)))
      filter_upwards [hv, hw] with U hvU hwU
      change inner ℂ
        (ContinuousMap.toLp 2 sourceHaar ℂ
          (orbitContinuous 1 (degreeOnePolynomial (WithLp.ofLp v))) U)
        (ContinuousMap.toLp 2 sourceHaar ℂ
          (orbitContinuous 1 (degreeOnePolynomial (WithLp.ofLp w))) U) = _
      rw [hvU, hwU, orbit_degreeOne, orbit_degreeOne]
      exact column_inner U⁻¹ v w
    _ = inner ℂ v w := by simp

def coordinateUnitary : Coordinates ≃ₗᵢ[ℂ] S :=
  coordinateEquiv.isometryOfInner coordinateEquiv_inner

@[simp] theorem coordinateUnitary_apply (v : Coordinates) :
    coordinateUnitary v = coordinateEquiv v := rfl

theorem coordinateUnitary_intertwines (U : SU2) (v : Coordinates) :
    sourceOperator 1 U (coordinateUnitary v) =
      coordinateUnitary (WithLp.toLp 2 ((U : Mat2).mulVec (WithLp.ofLp v))) := by
  simp only [coordinateUnitary_apply, coordinateEquiv_apply,
    SourceJointResponse.sourceOperator_apply, degreeOne_intertwines]

def spinBasis : OrthonormalBasis (Fin 2) ℂ S :=
  (EuclideanSpace.basisFun (Fin 2) ℂ).map coordinateUnitary

@[simp] theorem spinBasis_apply (i : Fin 2) :
    spinBasis i = coordinateUnitary (WithLp.toLp 2 (Pi.single i 1)) := by
  simp [spinBasis, EuclideanSpace.basisFun_apply]

variable {b : ℝ} (hb : 0 < b)

/-- An explicit source map, valid for every positive Gaussian width. -/
def sourceUnitary : V hb ≃ₗᵢ[ℂ] S := (sourceCoordinates hb).trans coordinateUnitary

theorem sourceUnitary_basis (i : Fin 2) :
    sourceUnitary hb (basisVector hb i) = spinBasis i := by
  simp [sourceUnitary, basisVector, spinBasis_apply]

theorem sourceUnitary_intertwines (U : SU2) (v : V hb) :
    sourceUnitary hb (sourceAction hb (U : Mat2) v) =
      sourceOperator 1 U (sourceUnitary hb v) := by
  change coordinateUnitary (sourceCoordinates hb (sourceAction hb (U : Mat2) v)) = _
  rw [sourceAction_coordinates]
  exact (coordinateUnitary_intertwines U (sourceCoordinates hb v)).symm

/-- Arbitrary matrices are transported through the same source coordinates. -/
def spinActionEquiv : Mat2 ≃ₐ[ℂ] Module.End ℂ S :=
  (Matrix.toLpLinAlgEquiv 2).trans (coordinateUnitary.toLinearEquiv.conjAlgEquiv ℂ)

abbrev spinAction (M : Mat2) := spinActionEquiv M

theorem spinAction_coordinates (M : Mat2) (v : Coordinates) :
    spinAction M (coordinateUnitary v) =
      coordinateUnitary (WithLp.toLp 2 (M.mulVec (WithLp.ofLp v))) := by
  change coordinateUnitary ((Matrix.toLpLinAlgEquiv 2 M)
    (coordinateUnitary.symm (coordinateUnitary v))) = _
  rw [coordinateUnitary.symm_apply_apply]
  exact congrArg coordinateUnitary (Matrix.toLpLin_apply 2 2 M v)

theorem spinAction_sourceOperator (U : SU2) :
    spinAction (U : Mat2) = sourceOperator 1 U := by
  apply LinearMap.ext
  intro s
  obtain ⟨v, rfl⟩ := coordinateUnitary.surjective s
  rw [spinAction_coordinates, coordinateUnitary_intertwines]

theorem sourceUnitary_matrix (M : Mat2) (v : V hb) :
    sourceUnitary hb (sourceAction hb M v) = spinAction M (sourceUnitary hb v) := by
  change coordinateUnitary (sourceCoordinates hb (sourceAction hb M v)) =
    spinAction M (coordinateUnitary (sourceCoordinates hb v))
  rw [sourceAction_coordinates, spinAction_coordinates]

/-- In the original Gaussian space the transported matrix is the generated
finite-corner control, including its prescribed identity on the complement. -/
theorem spinAction_original_control (M : Mat2) (v : V hb) :
    ((sourceUnitary hb).symm (spinAction M (sourceUnitary hb v)) : ComplexL2) =
      control hb M v := by
  rw [← sourceUnitary_matrix, LinearIsometryEquiv.symm_apply_apply,
    sourceAction_control]

theorem spinAction_basis (M : Mat2) (j : Fin 2) :
    spinAction M (spinBasis j) = M 0 j • spinBasis 0 + M 1 j • spinBasis 1 := by
  have h : WithLp.toLp 2 (M.mulVec (Pi.single j 1)) =
      M 0 j • (WithLp.toLp 2 (Pi.single 0 1) : Coordinates) +
        M 1 j • WithLp.toLp 2 (Pi.single 1 1) := by
    apply PiLp.ext
    intro i
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  simp only [spinBasis_apply, spinAction_coordinates]
  rw [h, map_add, map_smul, map_smul]

theorem spinAction_matrix (M : Mat2) :
    LinearMap.toMatrixOrthonormal spinBasis (spinAction M) = M := by
  ext i j
  rw [LinearMap.toMatrixOrthonormal_apply_apply, spinAction_basis]
  change inner ℂ (spinBasis i)
    (M 0 j • spinBasis 0 + M 1 j • spinBasis 1) = M i j
  calc
    inner ℂ (spinBasis i) (M 0 j • spinBasis 0 + M 1 j • spinBasis 1) =
        M 0 j * inner ℂ (spinBasis i) (spinBasis 0) +
          M 1 j * inner ℂ (spinBasis i) (spinBasis 1) :=
      (inner_add_right (spinBasis i) (M 0 j • spinBasis 0)
        (M 1 j • spinBasis 1)).trans
          (congrArg₂ (· + ·) (inner_smul_right (spinBasis i) (spinBasis 0) (M 0 j))
            (inner_smul_right (spinBasis i) (spinBasis 1) (M 1 j)))
    _ = M i j := by
      rw [spinBasis.inner_eq_ite i 0, spinBasis.inner_eq_ite i 1]
      fin_cases i <;> simp

theorem spinAction_number_vacuum :
    spinAction Operations.SourceNumberFlow.numberMatrix (spinBasis 0) = 0 := by
  rw [spinAction_basis]
  simp [Operations.SourceNumberFlow.numberMatrix]

theorem spinAction_number_excitation :
    spinAction Operations.SourceNumberFlow.numberMatrix (spinBasis 1) = spinBasis 1 := by
  rw [spinAction_basis]
  simp [Operations.SourceNumberFlow.numberMatrix]

theorem spinAction_flow_vacuum (t : ℝ) :
    spinAction (Operations.SourceNumberFlow.numberFlowMatrix t) (spinBasis 0) = spinBasis 0 := by
  rw [spinAction_basis]
  simp [Operations.SourceNumberFlow.numberFlowMatrix]

theorem spinAction_flow_excitation (t : ℝ) :
    spinAction (Operations.SourceNumberFlow.numberFlowMatrix t) (spinBasis 1) =
      Complex.exp (-Complex.I * (t : ℂ)) • spinBasis 1 := by
  rw [spinAction_basis]
  simp [Operations.SourceNumberFlow.numberFlowMatrix]

theorem spinAction_flow_original (t : ℝ) (v : V hb) :
    ((sourceUnitary hb).symm
      (spinAction (Operations.SourceNumberFlow.numberFlowMatrix t) (sourceUnitary hb v))
      : ComplexL2) = Operations.SourceNumberFlow.numberFlow hb t v := by
  rw [spinAction_original_control, Operations.SourceNumberFlow.numberFlow_control]

end GeneratedFoundations.Physical.SourceSpinIdentification

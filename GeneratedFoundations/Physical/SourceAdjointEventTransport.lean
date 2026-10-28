module

public import GeneratedFoundations.Physical.SourceFourDimensionalYangMills
public import GeneratedFoundations.Physical.SourceInternalYangMillsResponse
public import GeneratedFoundations.Physical.SourceScalarGaugeCovariance

/-!
# Event transport of the original colour source

The fifteen internal modes retain every one of their eight colour
coordinates. Their event derivative uses the already generated connection
and the adjoint matrix bracket. Its local covariance is obtained by the
product rule, including the inhomogeneous connection term. The kinetic
square retains both mixed terms and the quadratic connection term.

The source-natural elementary connector is colour scalar. Its commutator
with a colour insertion therefore vanishes on the complete matter fibre.
This statement concerns that commutator vertex, rather than the effective
vertices obtained from matter propagation.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Kronecker Matrix

namespace GeneratedFoundations.Physical.SourceAdjointEventTransport

open SourceFourDimensionalYangMills SourceInternalYangMillsResponse

abbrev ModeIndex := Fin longRootDimension
abbrev CoefficientIndex := ModeIndex × Fin colourDirectionCount

theorem coefficient_count : Fintype.card CoefficientIndex = 120 := by
  change Fintype.card (Fin longRootDimension × Fin colourDirectionCount) = 120
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, longRootDimension_eq]
  rfl

/-- A configuration of all original source coefficients, in the generated
colour basis, before any event derivative is applied. -/
def sourceMatrix (c : ModeIndex → ColourCoordinates) (r : ModeIndex) : Mat3 :=
  colourLieMatrix (c r)

theorem sourceMatrix_mem (c : ModeIndex → ColourCoordinates) (r : ModeIndex) :
    IsColourLie (sourceMatrix c r) := colourLieMatrix_mem (c r)

def bracket (A X : Mat3) : Mat3 := A * X - X * A

/-- A single event-coordinate derivative of an adjoint scalar. -/
def covariantJet (A X dX : Mat3) : Mat3 := dX + bracket A X

def transformField (q : LocalColourGaugeTwoJet) (X : Mat3) : Mat3 :=
  (↑(colourUnits q.value)⁻¹ : Mat3) * X * (↑(colourUnits q.value) : Mat3)

/-- The derivative of the same transformed field, not a separately chosen jet. -/
def transformFieldJet (q : LocalColourGaugeTwoJet)
    (μ : SourceFourDimensionalGaugeKinematics.CoordinateIndex) (X dX : Mat3) : Mat3 :=
  inverseDerivative q μ * X * (↑(colourUnits q.value) : Mat3) +
    (↑(colourUnits q.value)⁻¹ : Mat3) * dX * (↑(colourUnits q.value) : Mat3) +
    (↑(colourUnits q.value)⁻¹ : Mat3) * X * q.first μ

/-- Common frame transport fixes the adjoint event derivative. -/
theorem covariantJet_transform (q : LocalColourGaugeTwoJet)
    (A : MatrixConnectionJet)
    (μ : SourceFourDimensionalGaugeKinematics.CoordinateIndex) (X dX : Mat3) :
    covariantJet ((transformMatrixConnectionJet q A).value μ)
        (transformField q X) (transformFieldJet q μ X dX) =
      transformField q (covariantJet (A.value μ) X dX) := by
  have huv : (↑(colourUnits q.value) : Mat3) *
      (↑(colourUnits q.value)⁻¹ : Mat3) = 1 := Units.mul_inv _
  have hvu : (↑(colourUnits q.value)⁻¹ : Mat3) *
      (↑(colourUnits q.value) : Mat3) = 1 := Units.inv_mul _
  have huv_assoc (Y : Mat3) : (↑(colourUnits q.value) : Mat3) *
      ((↑(colourUnits q.value)⁻¹ : Mat3) * Y) = Y := by
    rw [← mul_assoc, huv, one_mul]
  have hvu_assoc (Y : Mat3) : (↑(colourUnits q.value)⁻¹ : Mat3) *
      ((↑(colourUnits q.value) : Mat3) * Y) = Y := by
    rw [← mul_assoc, hvu, one_mul]
  simp only [covariantJet, bracket, transformMatrixConnectionJet,
    transformField, transformFieldJet, inverseDerivative]
  noncomm_ring [huv, hvu, huv_assoc, hvu_assoc]

theorem kinetic_gauge_invariant (q : LocalColourGaugeTwoJet)
    (A : MatrixConnectionJet)
    (μ : SourceFourDimensionalGaugeKinematics.CoordinateIndex) (X dX : Mat3) :
    colourQuadratic (covariantJet ((transformMatrixConnectionJet q A).value μ)
      (transformField q X) (transformFieldJet q μ X dX)) =
      colourQuadratic (covariantJet (A.value μ) X dX) := by
  rw [covariantJet_transform]
  exact colourQuadratic_conjugate q.value _

/-- The two current cross terms and the seagull come from the same square. -/
theorem kinetic_expansion (A X dX : Mat3) :
    colourQuadratic (covariantJet A X dX) =
      colourQuadratic dX + colourQuadratic (bracket A X) -
        (Matrix.trace (dX * bracket A X + bracket A X * dX)).re := by
  simp only [covariantJet, colourQuadratic, Matrix.add_mul, Matrix.mul_add,
    Matrix.trace_add, Complex.add_re]
  ring

/-- All internal modes enter the same event connection. -/
def kineticDensity (A : MatrixConnectionJet) (X : ModeIndex → Mat3)
    (dX : SourceFourDimensionalGaugeKinematics.CoordinateIndex → ModeIndex → Mat3) : ℝ :=
  ∑ μ, lorentzSign μ * ∑ r, colourQuadratic (covariantJet (A.value μ) (X r) (dX μ r))

theorem kineticDensity_gauge_invariant (q : LocalColourGaugeTwoJet)
    (A : MatrixConnectionJet) (X : ModeIndex → Mat3)
    (dX : SourceFourDimensionalGaugeKinematics.CoordinateIndex → ModeIndex → Mat3) :
    kineticDensity (transformMatrixConnectionJet q A)
      (fun r => transformField q (X r))
      (fun μ r => transformFieldJet q μ (X r) (dX μ r)) =
      kineticDensity A X dX := by
  unfold kineticDensity
  congr 1
  funext μ
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  exact kinetic_gauge_invariant q A μ (X r) (dX μ r)

open SourceScalarGaugeCovariance SourceChiralCarrier
open GeneratedFoundations.Geometry.SourceSpinCoordinates

/-- The original colour insertion, on the complete labelled matter fibre. -/
def colourBase (X : Mat3) : Matrix ColourLabel ColourLabel ℂ :=
  Matrix.fromBlocks X 0 0 (0 : Matrix (Fin 1) (Fin 1) ℂ)

def matterColourMatrix (X : Mat3) : Matrix FullIndex FullIndex ℂ :=
  colourBase X ⊗ₖ
    (1 : Matrix ChiralLabel ChiralLabel ℂ)

theorem colour_connector_commute (X : Mat3)
    (h : Module.End ℂ SourceJointResponse.S) :
    matterColourMatrix X * matrixCoordinates (connector h) =
      matrixCoordinates (connector h) * matterColourMatrix X := by
  rw [connector_matrix]
  unfold matterColourMatrix
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp only [mul_one, one_mul]

/-- One colour insertion has zero trace against a complete colour-singlet
connector pair. This is distinct from the nonzero two-colour trace below. -/
theorem colour_connector_single_trace_zero {X : Mat3} (hX : IsColourLie X)
    (h : Module.End ℂ SourceJointResponse.S) :
    Matrix.trace (matterColourMatrix X *
      (matrixCoordinates (connector h))ᴴ * matrixCoordinates (connector h)) = 0 := by
  have htrace : Matrix.trace (colourBase X) = 0 := by
    simpa [colourBase, Matrix.trace, Matrix.diag] using hX.2
  rw [connector_matrix]
  simp only [matterColourMatrix, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, mul_one, one_mul,
    Matrix.trace_kronecker, htrace, zero_mul]

/-- Commuting colour and connector actions still have a joint four-insertion
trace. The complete colour and chiral factors remain in that response. -/
theorem colour_connector_mixed_trace (X : Mat3)
    (h : Module.End ℂ SourceJointResponse.S) :
    Matrix.trace ((matterColourMatrix X)ᴴ * matterColourMatrix X *
      (matrixCoordinates (connector h))ᴴ * matrixCoordinates (connector h)) =
      Matrix.trace ((colourBase X)ᴴ * colourBase X) *
        Matrix.trace ((chiralMatrix (spinMatrixCoordinates h))ᴴ *
          chiralMatrix (spinMatrixCoordinates h)) := by
  rw [connector_matrix]
  simp only [matterColourMatrix, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, mul_one, one_mul,
    Matrix.trace_kronecker]

/-- Quantified arguments are fields and their coordinate jets on the
already generated carrier; they add no root datum. -/
structure Properties : Prop where
  coefficient_count : Fintype.card CoefficientIndex = 120
  covariant_derivative : ∀ (q : LocalColourGaugeTwoJet) (A : MatrixConnectionJet)
      (μ : SourceFourDimensionalGaugeKinematics.CoordinateIndex) (X dX : Mat3),
    covariantJet ((transformMatrixConnectionJet q A).value μ)
      (transformField q X) (transformFieldJet q μ X dX) =
        transformField q (covariantJet (A.value μ) X dX)
  complete_kinetic_square : ∀ A X dX : Mat3,
    colourQuadratic (covariantJet A X dX) =
      colourQuadratic dX + colourQuadratic (bracket A X) -
        (Matrix.trace (dX * bracket A X + bracket A X * dX)).re
  elementary_colour_connector : ∀ (X : Mat3) (h : Module.End ℂ SourceJointResponse.S),
    matterColourMatrix X * matrixCoordinates (connector h) =
      matrixCoordinates (connector h) * matterColourMatrix X
  single_colour_trace : ∀ {X : Mat3}, IsColourLie X →
    ∀ (h : Module.End ℂ SourceJointResponse.S),
      Matrix.trace (matterColourMatrix X *
        (matrixCoordinates (connector h))ᴴ * matrixCoordinates (connector h)) = 0
  mixed_fibre_trace : ∀ (X : Mat3) (h : Module.End ℂ SourceJointResponse.S),
    Matrix.trace ((matterColourMatrix X)ᴴ * matterColourMatrix X *
      (matrixCoordinates (connector h))ᴴ * matrixCoordinates (connector h)) =
      Matrix.trace ((colourBase X)ᴴ * colourBase X) *
        Matrix.trace ((chiralMatrix (spinMatrixCoordinates h))ᴴ *
          chiralMatrix (spinMatrixCoordinates h))

theorem generated : Properties where
  coefficient_count := coefficient_count
  covariant_derivative := covariantJet_transform
  complete_kinetic_square := kinetic_expansion
  elementary_colour_connector := colour_connector_commute
  single_colour_trace := colour_connector_single_trace_zero
  mixed_fibre_trace := colour_connector_mixed_trace

end GeneratedFoundations.Physical.SourceAdjointEventTransport

module

public import GeneratedFoundations.Physical.SourceGeneratedYangMillsResponseHessian
public import Mathlib.Tactic.NoncommRing

/-!
# The common response in a moving generated colour frame

The connection-value term in the source response is expressed relative to a
colour frame.  A local frame change acts on the connection inhomogeneously,
so this term must be transported together with that frame.  Curvature
invariance alone does not prove invariance of the common response.

The frame below takes values in the colour group already generated on the
source carrier.  Its first jet is used only for the local product rule; it
is not an additional root datum or an additional propagating field.  The
covariant derivative of the frame transforms by left multiplication.  Its
positive trace norm therefore gives a gauge-invariant expression for the
existing response term.  In the constant source frame this expression is
exactly the connection density used in the common-ray calculation, with
the same source-generated coefficient.
-/

@[expose] public section

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace GeneratedFoundations.Physical.SourceGeneratedYangMillsFrameResponse

open SourceFourDimensionalGaugeKinematics SourceFourDimensionalYangMills
open SourceGeneratedYangMillsGap SourceGeneratedYangMillsResponseHessian

/-- A local presentation of the already generated colour frame and its
first derivative.  This auxiliary jet is not a parameter of the source. -/
structure ColourFrameJet where
  value : ColourGroup
  derivative : CoordinateIndex → Mat3

/-- The constant frame of the canonical source presentation. -/
def sourceFrame : ColourFrameJet where
  value := 1
  derivative := fun _ => 0

/-- Product rule for the frame under the same passive local change as the
connection. -/
def transformFrameJet (q : LocalColourGaugeTwoJet) (U : ColourFrameJet) :
    ColourFrameJet where
  value := q.value⁻¹ * U.value
  derivative := fun μ =>
    (↑(colourUnits q.value)⁻¹ : Mat3) * U.derivative μ +
      inverseDerivative q μ * (U.value : Mat3)

/-- The derivative and the connection are combined before taking a norm. -/
def covariantFrameDerivative (A : MatrixConnectionJet) (U : ColourFrameJet)
    (μ : CoordinateIndex) : Mat3 :=
  U.derivative μ + A.value μ * (U.value : Mat3)

/-- Exact covariance, including cancellation of both inhomogeneous terms. -/
theorem covariantFrameDerivative_transform (q : LocalColourGaugeTwoJet)
    (A : MatrixConnectionJet) (U : ColourFrameJet) (μ : CoordinateIndex) :
    covariantFrameDerivative (transformMatrixConnectionJet q A)
        (transformFrameJet q U) μ =
      (↑(colourUnits q.value)⁻¹ : Mat3) * covariantFrameDerivative A U μ := by
  have huv : (↑(colourUnits q.value) : Mat3) *
      (↑(colourUnits q.value)⁻¹ : Mat3) = 1 := Units.mul_inv _
  have huv_assoc (X : Mat3) : (↑(colourUnits q.value) : Mat3) *
      ((↑(colourUnits q.value)⁻¹ : Mat3) * X) = X := by
    rw [← mul_assoc, huv, one_mul]
  change _ + (_ + _) *
      (((q.value⁻¹ : ColourGroup) : Mat3) * (U.value : Mat3)) = _
  simp only [covariantFrameDerivative, transformFrameJet,
    inverseDerivative]
  change _ + (_ + _) *
      ((↑(colourUnits q.value)⁻¹ : Mat3) * (U.value : Mat3)) = _
  noncomm_ring [huv, huv_assoc]

/-- Positive trace norm on the generated colour matrices. -/
def frameQuadratic (X : Mat3) : ℝ := (Matrix.trace (Xᴴ * X)).re

theorem frameQuadratic_nonneg (X : Mat3) : 0 ≤ frameQuadratic X := by
  change 0 ≤ Complex.reAddGroupHom
    (∑ i : Fin 3, ∑ j : Fin 3, star (X j i) * X j i)
  simp only [map_sum]
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  change 0 ≤ (star (X j i) * X j i).re
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  nlinarith [sq_nonneg (X j i).re, sq_nonneg (X j i).im]

/-- In the generated Lie algebra the positive frame norm is precisely the
source trace form, not a new normalization. -/
theorem frameQuadratic_eq_colourQuadratic {X : Mat3}
    (hX : IsColourLie X) : frameQuadratic X = colourQuadratic X := by
  simp [frameQuadratic, hX.1, colourQuadratic, neg_mul]

theorem colour_star_mul_self (g : ColourGroup) :
    (g : Mat3)ᴴ * (g : Mat3) = 1 := by
  exact g.property.1.1

theorem frameQuadratic_left_invariant (g : ColourGroup) (X : Mat3) :
    frameQuadratic ((g : Mat3) * X) = frameQuadratic X := by
  simp only [frameQuadratic, Matrix.conjTranspose_mul]
  rw [mul_assoc, ← mul_assoc (g : Mat3)ᴴ,
    colour_star_mul_self, one_mul]

/-- Positive response of the frame-relative connection. -/
def frameResponseDensity (A : MatrixConnectionJet) (U : ColourFrameJet) : ℝ :=
  ∑ μ, frameQuadratic (covariantFrameDerivative A U μ)

theorem frameResponseDensity_nonneg (A : MatrixConnectionJet)
    (U : ColourFrameJet) : 0 ≤ frameResponseDensity A U :=
  Finset.sum_nonneg fun _ _ => frameQuadratic_nonneg _

/-- Full local invariance of the response term that is absent from a
curvature-only gauge calculation. -/
theorem frameResponseDensity_gauge_invariant (q : LocalColourGaugeTwoJet)
    (A : MatrixConnectionJet) (U : ColourFrameJet) :
    frameResponseDensity (transformMatrixConnectionJet q A)
        (transformFrameJet q U) = frameResponseDensity A U := by
  unfold frameResponseDensity
  simp only [covariantFrameDerivative_transform]
  exact Finset.sum_congr rfl fun μ _ =>
    frameQuadratic_left_invariant q.value⁻¹ (covariantFrameDerivative A U μ)

/-- Exact constant-source-frame restriction on the generated colour Lie
connection.  The equality is not asserted for arbitrary complex matrices. -/
theorem frameResponseDensity_sourceFrame (A : ColourConnectionJet) :
    frameResponseDensity (colourMatrixConnectionJet A) sourceFrame =
      matrixConnectionDensity (colourMatrixConnectionJet A) := by
  unfold frameResponseDensity matrixConnectionDensity
  apply Finset.sum_congr rfl
  intro μ _
  simp only [covariantFrameDerivative, sourceFrame, Submonoid.coe_one,
    mul_one, zero_add]
  exact frameQuadratic_eq_colourQuadratic (colourLieMatrix_mem (A.value μ))

/-- The common radial, curvature and frame response, with no new coefficient. -/
def commonFrameResponseAction (L z radial : ℝ) (A : MatrixConnectionJet)
    (U : ColourFrameJet) : ℝ :=
  SourceGeneratedRadialVariation.sourceRadialPotential z radial +
    (1 / 2 : ℝ) * SourceGeneratedYangMillsAction.matrixCurvatureDensity A +
    coclosedResponseShift L (z + sourceRadialIncrement z radial) *
      frameResponseDensity A U

/-- The same local colour change preserves every part of the common action. -/
theorem commonFrameResponseAction_gauge_invariant (L z radial : ℝ)
    (q : LocalColourGaugeTwoJet) (A : MatrixConnectionJet) (U : ColourFrameJet) :
    commonFrameResponseAction L z radial (transformMatrixConnectionJet q A)
        (transformFrameJet q U) = commonFrameResponseAction L z radial A U := by
  unfold commonFrameResponseAction
  rw [frameResponseDensity_gauge_invariant]
  rw [show SourceGeneratedYangMillsAction.matrixCurvatureDensity
      (transformMatrixConnectionJet q A) =
      SourceGeneratedYangMillsAction.matrixCurvatureDensity A from
    localQuadraticDensity_gauge_invariant q A]

/-- The nonlinear common source action is exactly the constant-frame
restriction of the covariant response. -/
theorem commonFrameResponseAction_sourceFrame (L z radial : ℝ)
    (A : ColourConnectionJet) :
    commonFrameResponseAction L z radial (colourMatrixConnectionJet A) sourceFrame =
      sourceCommonResponseAction L z radial (colourMatrixConnectionJet A) := by
  rw [commonFrameResponseAction, frameResponseDensity_sourceFrame]
  unfold sourceCommonResponseAction connectionResponse matrixConnectionNormSq
  ring

/-- Changing the presentation of the source frame introduces no change in
the value of the common response. -/
theorem commonFrameResponseAction_sourceOrbit (L z radial : ℝ)
    (q : LocalColourGaugeTwoJet) (A : ColourConnectionJet) :
    commonFrameResponseAction L z radial
        (transformMatrixConnectionJet q (colourMatrixConnectionJet A))
        (transformFrameJet q sourceFrame) =
      sourceCommonResponseAction L z radial (colourMatrixConnectionJet A) := by
  rw [commonFrameResponseAction_gauge_invariant,
    commonFrameResponseAction_sourceFrame]

/-- The canonical source orientation is reversed by coefficient conjugation.
Both values and derivatives are transported, so this operation compares
presentations of the same connection rather than changing its curvature. -/
def conjugateConnection (A : MatrixConnectionJet) : MatrixConnectionJet where
  value := fun μ => (A.value μ).map (starRingEnd ℂ)
  derivative := fun μ ν => (A.derivative μ ν).map (starRingEnd ℂ)

theorem conjugateConnection_involutive (A : MatrixConnectionJet) :
    conjugateConnection (conjugateConnection A) = A := by
  cases A
  dsimp only [conjugateConnection]
  congr 1
  · funext μ i j
    simp
  · funext μ ν i j
    simp

/-- Conjugation preserves the actual matrix commutator and derivative
curvature, not merely its spectrum. -/
theorem matrixCurvature_conjugate (A : MatrixConnectionJet)
    (μ ν : CoordinateIndex) :
    matrixCurvature (conjugateConnection A) μ ν =
      (matrixCurvature A μ ν).map (starRingEnd ℂ) := by
  ext i j
  simp [matrixCurvature, conjugateConnection, Matrix.mul_apply, map_sum]

theorem colourQuadratic_conjugate (X : Mat3) :
    colourQuadratic (X.map (starRingEnd ℂ)) = colourQuadratic X := by
  unfold colourQuadratic
  rw [← Matrix.map_mul, ← AddMonoidHom.map_trace]
  simp

theorem matrixCurvatureDensity_conjugate (A : MatrixConnectionJet) :
    SourceGeneratedYangMillsAction.matrixCurvatureDensity
        (conjugateConnection A) =
      SourceGeneratedYangMillsAction.matrixCurvatureDensity A := by
  simp only [SourceGeneratedYangMillsAction.matrixCurvatureDensity,
    matrixCurvature_conjugate, colourQuadratic_conjugate]

theorem matrixConnectionNormSq_conjugate (A : MatrixConnectionJet) :
    matrixConnectionNormSq (conjugateConnection A) = matrixConnectionNormSq A := by
  simp only [matrixConnectionNormSq, matrixConnectionDensity, conjugateConnection,
    colourQuadratic_conjugate]

/-- The common nonlinear source response is independent of the orientation
presentation. The radial potential, commutator curvature and Gaussian
connection term are all retained in this equality. -/
theorem sourceCommonResponseAction_conjugate (L z radial : ℝ)
    (A : MatrixConnectionJet) :
    sourceCommonResponseAction L z radial (conjugateConnection A) =
      sourceCommonResponseAction L z radial A := by
  unfold sourceCommonResponseAction connectionResponse
  rw [matrixCurvatureDensity_conjugate, matrixConnectionNormSq_conjugate]

/-- Gauge covariance and the constant-frame restriction uniquely determine
the response on the orbit of the generated source presentation.  This is a
comparison theorem for response formulas, not an input to the construction. -/
theorem sourceOrbit_response_unique
    (F : ℝ → ℝ → ℝ → MatrixConnectionJet → ColourFrameJet → ℝ)
    (hinvariant : ∀ L z radial q A U,
      F L z radial (transformMatrixConnectionJet q A) (transformFrameJet q U) =
        F L z radial A U)
    (hsource : ∀ L z radial A,
      F L z radial (colourMatrixConnectionJet A) sourceFrame =
        sourceCommonResponseAction L z radial (colourMatrixConnectionJet A))
    (L z radial : ℝ) (q : LocalColourGaugeTwoJet) (A : ColourConnectionJet) :
    F L z radial (transformMatrixConnectionJet q (colourMatrixConnectionJet A))
        (transformFrameJet q sourceFrame) =
      commonFrameResponseAction L z radial
        (transformMatrixConnectionJet q (colourMatrixConnectionJet A))
        (transformFrameJet q sourceFrame) := by
  rw [hinvariant, hsource, commonFrameResponseAction_sourceOrbit]

end GeneratedFoundations.Physical.SourceGeneratedYangMillsFrameResponse

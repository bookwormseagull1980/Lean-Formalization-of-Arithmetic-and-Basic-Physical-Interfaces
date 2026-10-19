module

public import GeneratedFoundations.Physical.SourceGeneratedYangMillsClosure
public import GeneratedFoundations.Physical.SourceHaarYangMillsHessian
public import GeneratedFoundations.Physical.SourceHaarCurvatureTrace
public import GeneratedFoundations.Physical.SourceHaarYangMillsFock
public import GeneratedFoundations.Source.CanonicalRealization

/-!
# Yang--Mills response at the generated infrared radius

The natural infrared endpoint of the unit-covariance source fixes the radius
used here. It lies strictly beyond the critical endpoint ratio. Consequently
the unique condensed response, its self-adjoint Hessian and its attained
positive bottom require no supplied radius, amplitude, orientation or mass.

Statements with a variable radius elsewhere describe the already generated
response as that radius varies. This module supplies the particular response
fixed by the canonical source itself.
-/

@[expose] public section

noncomputable section

open scoped LinearPMap

namespace GeneratedFoundations.Physical.CanonicalYangMills

open SourceConformalResponse SourceInternalYangMillsResponse SourceGeneratedYangMillsAction
open SourceGeneratedYangMillsGap SourceGeneratedYangMillsPhysicalHessian
open SourceFourDimensionalYangMills SourceGeneratedYangMillsResponseHessian
open SourceGeneratedYangMillsFrameResponse

/-- The generated Gaussian infrared endpoint in unit-covariance coordinates. -/
def internalRadius : ℝ :=
  Correlation.Endpoints.irEndpoint Source.CanonicalRealization.width

theorem internalRadius_eq : internalRadius = Real.sqrt (2 * Real.pi) :=
  Source.CanonicalRealization.endpoints.2.1

/-- The actual generated radius lies on the condensed branch. -/
theorem criticalRadius_lt_internalRadius : criticalRadius < internalRadius := by
  rw [internalRadius_eq, criticalRadius]
  exact Real.sqrt_lt_sqrt Real.pi_pos.le (by linarith [Real.pi_pos])

theorem internalRadius_pos : 0 < internalRadius :=
  criticalRadius_pos.trans criticalRadius_lt_internalRadius

/-- The positive response amplitude uniquely determined at the generated
radius, with no additional target or coupling argument. -/
def amplitude : ℝ :=
  condensedAmplitude internalRadius criticalRadius_lt_internalRadius

theorem amplitude_spec :
    0 < amplitude ∧ completeResponse amplitude = generatedTarget internalRadius ∧
      0 < generatedYangMillsGapSq internalRadius amplitude :=
  condensedAmplitude_spec internalRadius criticalRadius_lt_internalRadius

theorem amplitude_unique {z : ℝ} (hz : 0 < z)
    (hresponse : completeResponse z = generatedTarget internalRadius) :
    z = amplitude :=
  condensedAmplitude_unique internalRadius criticalRadius_lt_internalRadius hz hresponse

/-- The same generated amplitude in the original source-intensity coordinate.
It is determined by the already computed feedback and radius. -/
def gaussianSourceIntensity : ℝ :=
  amplitude / (generatedFeedback internalRadius * internalRadius ^ 2)

theorem gaussianSourceIntensity_pos : 0 < gaussianSourceIntensity := by
  exact div_pos amplitude_spec.1
    (mul_pos (generatedFeedback_pos internalRadius_pos) (sq_pos_of_pos internalRadius_pos))

theorem gaussianSourceIntensity_generates_amplitude :
    generatedDimensionlessIntensity internalRadius gaussianSourceIntensity = amplitude := by
  unfold generatedDimensionlessIntensity gaussianSourceIntensity
  exact mul_div_cancel₀ amplitude (mul_ne_zero
    (generatedFeedback_pos internalRadius_pos).ne' (sq_pos_of_pos internalRadius_pos).ne')

/-- On every traceless colour matrix the actual transverse covariance
contraction gives exactly the connection term in the canonical Hessian. -/
theorem sourceColourContraction (i : Fin 3)
    (X : SourceColourAdjointCasimir.ColourMatrix) (hX : Matrix.trace X = 0) :
    transverseCovarianceAction internalRadius gaussianSourceIntensity i X =
      (coclosedResponseShift internalRadius amplitude : ℂ) • X := by
  rw [transverseCovarianceAction_eq internalRadius gaussianSourceIntensity i X hX,
    ← coclosedResponseShift_generatedIntensity internalRadius_pos.ne',
    gaussianSourceIntensity_generates_amplitude]

/-- The dimensionless bottom of the actual generated response. -/
def gapSq : ℝ := generatedYangMillsGapSq internalRadius amplitude

theorem gapSq_pos : 0 < gapSq := amplitude_spec.2.2

/-- The common nonlinear response in the canonical source presentation.
Only perturbation variables remain; the radius and condensed source are
already generated above. -/
def responseAction (radial : ℝ) (A : MatrixConnectionJet) : ℝ :=
  sourceCommonResponseAction internalRadius amplitude radial A

/-- The other orientation presentation gives the same canonical nonlinear
response when the complete connection jet is conjugated. -/
theorem responseAction_orientation_reverse (radial : ℝ) (A : MatrixConnectionJet) :
    responseAction radial (conjugateConnection A) = responseAction radial A :=
  sourceCommonResponseAction_conjugate internalRadius amplitude radial A

/-- The full local second variation at the canonical generated source. -/
theorem responseAction_secondDeriv (radial : ℝ) (A : MatrixConnectionJet) :
    HasDerivAt (fun t : ℝ => deriv (fun u : ℝ =>
      responseAction (u * radial) (scaleMatrixConnectionJet u A)) t)
      (commonQuadraticSecondVariation internalRadius amplitude radial A) 0 :=
  sourceCommonResponseAction_secondDeriv amplitude_spec.1 internalRadius radial A

/-- The derived source has zero radial/connection mixed derivative. -/
theorem responseAction_mixed_secondDeriv_zero (radial : ℝ) (A : MatrixConnectionJet) :
    HasDerivAt (fun s : ℝ => deriv (fun t : ℝ =>
      responseAction (s * radial) (scaleMatrixConnectionJet t A)) 0) 0 0 :=
  sourceCommonResponseAction_mixed_secondDeriv_zero internalRadius amplitude radial A

/-- A local change of the generated colour frame preserves the actual
canonical nonlinear response, including its Gaussian connection term. -/
theorem responseAction_frame_transport (radial : ℝ)
    (q : LocalColourGaugeTwoJet) (A : ColourConnectionJet) :
    commonFrameResponseAction internalRadius amplitude radial
        (transformMatrixConnectionJet q (colourMatrixConnectionJet A))
        (transformFrameJet q sourceFrame) =
      responseAction radial (colourMatrixConnectionJet A) :=
  commonFrameResponseAction_sourceOrbit internalRadius amplitude radial q A

/-- The nonlinear action on the original coclosed Haar field core. All
colour components and their commutator curvature occur before variation. -/
def haarAction (radial : ℝ) (A : SourceHaarYangMillsAction.ColourCore) : ℝ :=
  SourceHaarYangMillsAction.action internalRadius amplitude radial A

/-- The closed response Hessian on the original radial and Haar fields. -/
def responseHessian := SourceHaarYangMillsHessian.operator internalRadius amplitude

theorem responseHessian_selfAdjoint : IsSelfAdjoint responseHessian :=
  SourceHaarYangMillsHessian.operator_selfAdjoint internalRadius amplitude

theorem responseHessian_unique
    (T : SourceHaarYangMillsHessian.ResponseL2 →ₗ.[ℂ]
      SourceHaarYangMillsHessian.ResponseL2)
    (hT : IsSelfAdjoint T)
    (hcore : SourceHaarYangMillsHessian.finiteOperator internalRadius amplitude ≤ T) :
    T = responseHessian :=
  SourceHaarYangMillsHessian.operator_unique internalRadius amplitude T hT hcore

/-- The same source action has the finite differential operator as its
second variation. The radial argument is the real slice of that operator. -/
theorem haarAction_secondDeriv (radial : ℝ)
    (x : SourceHaarYangMillsHessian.ResponseCore)
    (hr : SourceHaarYangMillsHessian.radialProjection x.val = (radial : ℂ)) :
    HasDerivAt (fun t : ℝ => deriv (fun u : ℝ =>
      haarAction (u * radial)
        ((u : ℂ) • (fun a => SourceHaarYangMillsHessian.coreConnection a x))) t)
      (inner ℂ (x : SourceHaarYangMillsHessian.ResponseL2)
        (SourceHaarYangMillsHessian.finiteOperator internalRadius amplitude x)).re 0 :=
  SourceHaarYangMillsHessian.action_secondDeriv amplitude_spec.1
    internalRadius radial x hr

/-- The mixed block vanishes by differentiation of the same nonlinear
Haar action that defines the full field Hessian. -/
theorem haarAction_mixed_secondDeriv_zero (radial : ℝ)
    (A : SourceHaarYangMillsAction.ColourCore) :
    HasDerivAt (fun s : ℝ => deriv (fun t : ℝ =>
      haarAction (s * radial) ((t : ℂ) • A)) 0) 0 0 :=
  SourceHaarYangMillsAction.action_mixed_secondDeriv_zero
    internalRadius amplitude radial A

theorem responseHessian_coercive (x : responseHessian.domain) :
    gapSq * ‖(x : SourceHaarYangMillsHessian.ResponseL2)‖ ^ 2 ≤
      (inner ℂ (x : SourceHaarYangMillsHessian.ResponseL2) (responseHessian x)).re :=
  SourceHaarYangMillsHessian.complete_coercivity internalRadius amplitude x

/-- Every generated mode lies above the same positive canonical bottom. -/
theorem mode_lower_bound (mode : PhysicalMode) :
    gapSq ≤ physicalEigenvalue internalRadius amplitude mode :=
  gap_le_physicalEigenvalue internalRadius amplitude mode

/-- The canonical bottom is an actual eigenvalue of the closed Hessian. -/
theorem gap_attained :
    responseHessian
        ⟨SourceHaarYangMillsHessian.responseBasis
            (SourceHaarYangMillsHessian.minimizingIndex internalRadius amplitude),
          SourceHaarYangMillsHessian.basis_mem_domain internalRadius amplitude
            (SourceHaarYangMillsHessian.minimizingIndex internalRadius amplitude)⟩ =
      (gapSq : ℂ) • SourceHaarYangMillsHessian.responseBasis
        (SourceHaarYangMillsHessian.minimizingIndex internalRadius amplitude) :=
  SourceHaarYangMillsHessian.gap_attained internalRadius amplitude

theorem vacuum_unique (occupation : SourceHaarYangMillsFock.Occupation) :
    SourceHaarYangMillsFock.totalEnergy internalRadius amplitude occupation = 0 ↔
      occupation = SourceHaarYangMillsFock.vacuum :=
  SourceHaarYangMillsFock.vacuum_unique internalRadius_pos amplitude_spec.1 occupation

theorem nonvacuum_gap {occupation : SourceHaarYangMillsFock.Occupation}
    (hoccupation : occupation ≠ SourceHaarYangMillsFock.vacuum) :
    gapSq ≤ SourceHaarYangMillsFock.totalEnergy internalRadius amplitude occupation :=
  SourceHaarYangMillsFock.nonvacuum_gap internalRadius_pos amplitude_spec.1 hoccupation

/-- Zero-input output of the canonical generated Yang--Mills response. -/
structure Conclusions : Prop where
  radius_generated : internalRadius = Real.sqrt (2 * Real.pi)
  condensed : 0 < amplitude ∧
    completeResponse amplitude = generatedTarget internalRadius
  positive_gap : 0 < gapSq
  source_intensity_positive : 0 < gaussianSourceIntensity
  covariance_contraction : ∀ (i : Fin 3)
    (X : SourceColourAdjointCasimir.ColourMatrix), Matrix.trace X = 0 →
    transverseCovarianceAction internalRadius gaussianSourceIntensity i X =
      (coclosedResponseShift internalRadius amplitude : ℂ) • X
  orientation_response : ∀ radial A,
    responseAction radial (conjugateConnection A) = responseAction radial A
  source_second_derivative : ∀ radial A,
    HasDerivAt (fun t : ℝ => deriv (fun u : ℝ =>
      responseAction (u * radial) (scaleMatrixConnectionJet u A)) t)
      (commonQuadraticSecondVariation internalRadius amplitude radial A) 0
  mixed_second_derivative_zero : ∀ radial A,
    HasDerivAt (fun s : ℝ => deriv (fun t : ℝ =>
      responseAction (s * radial) (scaleMatrixConnectionJet t A)) 0) 0 0
  common_frame_transport : ∀ radial q A,
    commonFrameResponseAction internalRadius amplitude radial
        (transformMatrixConnectionJet q (colourMatrixConnectionJet A))
        (transformFrameJet q sourceFrame) =
      responseAction radial (colourMatrixConnectionJet A)
  selfAdjoint : IsSelfAdjoint responseHessian
  haar_action_second_derivative : ∀ (radial : ℝ) (x : SourceHaarYangMillsHessian.ResponseCore),
    SourceHaarYangMillsHessian.radialProjection x.val = (radial : ℂ) →
    HasDerivAt (fun t : ℝ => deriv (fun u : ℝ =>
      haarAction (u * radial)
        ((u : ℂ) • (fun a => SourceHaarYangMillsHessian.coreConnection a x))) t)
      (inner ℂ (x : SourceHaarYangMillsHessian.ResponseL2)
        (SourceHaarYangMillsHessian.finiteOperator internalRadius amplitude x)).re 0
  closed_field_lower_bound : ∀ x : responseHessian.domain,
    gapSq * ‖(x : SourceHaarYangMillsHessian.ResponseL2)‖ ^ 2 ≤
      (inner ℂ (x : SourceHaarYangMillsHessian.ResponseL2) (responseHessian x)).re
  unique_selfAdjoint_extension : ∀
    (T : SourceHaarYangMillsHessian.ResponseL2 →ₗ.[ℂ]
      SourceHaarYangMillsHessian.ResponseL2),
    IsSelfAdjoint T →
    SourceHaarYangMillsHessian.finiteOperator internalRadius amplitude ≤ T →
      T = responseHessian
  haar_mixed_second_derivative_zero : ∀ (radial : ℝ)
    (A : SourceHaarYangMillsAction.ColourCore),
    HasDerivAt (fun s : ℝ => deriv (fun t : ℝ =>
      haarAction (s * radial) ((t : ℂ) • A)) 0) 0 0
  attained_bottom : responseHessian
      ⟨SourceHaarYangMillsHessian.responseBasis
          (SourceHaarYangMillsHessian.minimizingIndex internalRadius amplitude),
        SourceHaarYangMillsHessian.basis_mem_domain internalRadius amplitude
          (SourceHaarYangMillsHessian.minimizingIndex internalRadius amplitude)⟩ =
    (gapSq : ℂ) • SourceHaarYangMillsHessian.responseBasis
      (SourceHaarYangMillsHessian.minimizingIndex internalRadius amplitude)
  lower_bound : ∀ mode, gapSq ≤ physicalEigenvalue internalRadius amplitude mode
  vacuum_unique : ∀ occupation,
    SourceHaarYangMillsFock.totalEnergy internalRadius amplitude occupation = 0 ↔
      occupation = SourceHaarYangMillsFock.vacuum
  nonvacuum_gap : ∀ {occupation}, occupation ≠ SourceHaarYangMillsFock.vacuum →
    gapSq ≤ SourceHaarYangMillsFock.totalEnergy internalRadius amplitude occupation

theorem generated : Conclusions where
  radius_generated := internalRadius_eq
  condensed := ⟨amplitude_spec.1, amplitude_spec.2.1⟩
  positive_gap := gapSq_pos
  source_intensity_positive := gaussianSourceIntensity_pos
  covariance_contraction := sourceColourContraction
  orientation_response := responseAction_orientation_reverse
  source_second_derivative := responseAction_secondDeriv
  mixed_second_derivative_zero := responseAction_mixed_secondDeriv_zero
  common_frame_transport := responseAction_frame_transport
  selfAdjoint := responseHessian_selfAdjoint
  haar_action_second_derivative := haarAction_secondDeriv
  closed_field_lower_bound := responseHessian_coercive
  unique_selfAdjoint_extension := responseHessian_unique
  haar_mixed_second_derivative_zero := haarAction_mixed_secondDeriv_zero
  attained_bottom := gap_attained
  lower_bound := mode_lower_bound
  vacuum_unique := CanonicalYangMills.vacuum_unique
  nonvacuum_gap := CanonicalYangMills.nonvacuum_gap

end GeneratedFoundations.Physical.CanonicalYangMills

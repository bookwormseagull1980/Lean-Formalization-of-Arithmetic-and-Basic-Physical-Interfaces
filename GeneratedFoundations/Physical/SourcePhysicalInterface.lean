module

public import GeneratedFoundations.Physical.SourceInternalResponse
public import GeneratedFoundations.Physical.SourceCompleteMatterExactSequence
public import GeneratedFoundations.Physical.SourceSplitResponse
public import GeneratedFoundations.Physical.SourceFrameConstruction
public import GeneratedFoundations.Physical.SourceFourDimensionalYangMills
public import GeneratedFoundations.Physical.SourceLinearizedGravity
public import GeneratedFoundations.Physical.SourceRP3FieldSpectrum
public import GeneratedFoundations.Physical.SourceConformalResponse
public import GeneratedFoundations.Physical.SourceInternalYangMillsResponse
public import GeneratedFoundations.Physical.SourceRadialMassIntertwiner
public import GeneratedFoundations.Physical.SourceLorentzCarrier
public import GeneratedFoundations.Physical.CanonicalYangMills
public import GeneratedFoundations.Physical.CanonicalYangMillsUnits
public import GeneratedFoundations.Geometry.SourceSpinorSystem
public import GeneratedFoundations.Geometry.SourceTensorTTSystem
public import GeneratedFoundations.Source.MinimalUnbiasedChange
public import GeneratedFoundations.Source.CanonicalRealization

/-!
# Generated source to the basic physical interfaces

The sole root package is minimal unbiased compositional change. Its canonical
carrier, unit-covariance Gaussian width and original complex orientation are
fixed before the physical interface is assembled. The theorem below therefore
accepts no realization parameter. The root interface does not restate the
component comparison theorems as a parameterized family.
The endpoints, reflecting source evolution, exchange-retained response,
source frames, least matter realization, vacuum lift and elementary connector
are internal constructions and outputs. In particular, no endpoint, boundary
operator or aggregate P4--P6 realization premise is supplied by the caller.
The neutral line, complete sixteen-dimensional matter carrier and charged
fifteen-dimensional quotient form a canonical short exact sequence, and the
charged quotient is characterized by its unique factorization property.
The complete source action has the six-element central kernel, and every
faithful realization of the same generated operator group is uniquely
isomorphic to its intrinsic action group; the product presentation therefore
descends to the effective central quotient rather than remaining a choice.
The internal-response output includes the primitive source Clifford sectors
and their actual Hermite projections. The frame output includes pointwise
colour determinant-phase factorization and its finite central ambiguity.
For competing least representations, one realizing unitary transports every
source operator uniquely; the unitary itself is not asserted to be unique.

Classification statements retain the comparison classes stated in their
individual conclusions. The Hermitian readout uses the same two Gaussian
modes and gives the determinant-preserving algebraic interface for relativistic
kinematics. Its zeroth coordinate is not an assumed primitive physical clock.
The same readout supplies four coordinate directions for the generated colour
connection.  Its eight Lie directions, curvature, source-normalized quadratic
form and local gauge covariance are constructed from the existing colour
carrier and effective group, without a second base space, lattice or coupling
parameter in the root datum.  The three spatial directions then carry the
actual symmetric, transverse and traceless constraint space.  Solving these
constraints gives exactly two polarization amplitudes.  The tensor response
has the unique mass-fraction maximum `4/27`, every positive fixed spectral
coefficient has one positive endpoint, and the generated four-coordinate
two-derivative tensor
operator is uniquely selected in its local five-coefficient class by gauge
annihilation, transversality and unit TT normalization.  Its TT reduction is
`Q² I₂`, with the resulting simple massless pole and positive residue. The
same generated source powers supply the complete left--right tensor-product
family, with dimensions, central characters and Casimir operators computed
uniformly. The actual projective scalar spectrum is anchored to the closed
source quotient operator. Its unique condensed response, normalized radial
block and positive odd coclosed colour-connection tower combine into the
strictly positive generated Yang--Mills spectral bottom. The coclosed vector
space and its spectrum are constructed by differentiation in the original
Haar field space; its nonlinear action and closed differential Hessian enter
the canonical Yang--Mills conclusion. The spinor output likewise differentiates
the source frame, computes its spin connection and constructs the complete
closed Dirac operator on the original Haar fields. Its two central sectors
are restrictions on the full operator domain. The original nine-component
tensor Haar space likewise supplies the closed weak TT kernel. Its actual
Koszul differential has a unique self-adjoint rough closure, full weighted
domain and spectrum k(k+2)-2 for even k at least two, with attained lower
edge six in the unit trace-metric frame. These spectral values are derived
from differential identities and nonzero source-polynomial witnesses;
the separate representation multiplicity tables are not inputs to this
operator construction.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open GeneratedFoundations.Source GeneratedFoundations.Probability
open GeneratedFoundations.Source.TraceLieGeometry
open GeneratedFoundations.Source.CarrierOrientation
open GeneratedFoundations.Correlation.ComplexGaussianStates
open GeneratedFoundations.Operations.SourceSpinCorner

namespace GeneratedFoundations.Physical.SourcePhysicalInterface

open SourceHermitianReadout

/-- The physical outputs of the unique canonical realization. The proposition
has no carrier, law, width or orientation parameter. -/
structure Conclusions : Prop where
  geometry : Geometry.GeneratedSourceGeometry.Conclusions
  split_response : SourceSplitResponse.SplitConclusions
  frames : SourceFrameConstruction.FrameConclusions
  internal_response : SourceInternalResponse.Conclusions
  complete_matter_exact_sequence : SourceCompleteMatterExactSequence.Conclusions
  generated_gauge_group : SourceGeneratedGaugeGroup.FactorOriginProperties
  four_dimensional_gauge_kinematics :
    SourceFourDimensionalGaugeKinematics.Properties
  four_dimensional_colour_yang_mills :
    SourceFourDimensionalYangMills.Properties
  transverse_traceless_carrier :
    SourceTransverseTraceless.Properties
  tensor_response_endpoint :
    SourceTensorResponseEndpoint.Properties
  linearized_gravity :
    SourceLinearizedGravity.Properties
  generated_left_right_family :
    Geometry.SourceLeftRightRepresentations.GeneratedFamilyProperties
  generated_projective_scalar_spectrum :
    SourceRP3FieldSpectrum.GeneratedScalarProperties
  generated_finite_conformal_response :
    SourceConformalResponse.FiniteProperties
  generated_complete_conformal_response :
    SourceConformalResponse.CompleteProperties
  generated_internal_yang_mills_response :
    SourceInternalYangMillsResponse.Properties
  generated_radial_mass_intertwiner :
    SourceRadialMassIntertwiner.Properties
  generated_lorentz_carrier : SourceLorentzCarrier.Properties
  generated_yang_mills_gap : SourceGeneratedYangMillsGap.Properties
  generated_yang_mills_closure : SourceGeneratedYangMillsClosure.Conclusions
  canonical_yang_mills : CanonicalYangMills.Conclusions
  canonical_yang_mills_units : CanonicalYangMillsUnits.Conclusions
  generated_spinor : Geometry.SourceSpinorSystem.Conclusions
  generated_tensor_tt : Geometry.SourceTensorTTSystem.Conclusions
  spin_same_source : ∀ (M : Mat2)
      (v : SourceVacuumTransport.V Source.CanonicalRealization.width_pos),
    SourceSpinIdentification.sourceUnitary Source.CanonicalRealization.width_pos
        (SourceVacuumTransport.sourceAction Source.CanonicalRealization.width_pos M v) =
      SourceSpinIdentification.spinAction M
        (SourceSpinIdentification.sourceUnitary
          Source.CanonicalRealization.width_pos v)
  hermitian_coordinates : ∀ X : Mat2, X.IsHermitian →
    ∃! q : RealCoordinates, hermitianMatrix q = X
  determinant_signature : ∀ q : RealCoordinates,
    (hermitianMatrix q).det = (determinantForm q : ℂ)
  determinant_invariant : ∀ A : Mat2, A.det = 1 → ∀ q : RealCoordinates,
    determinantForm (coordinateTransform A q) = determinantForm q
  hermitian_same_coordinates : ∀ (q : RealCoordinates)
      (v : SourceVacuumTransport.V Source.CanonicalRealization.width_pos),
    Operations.HermiteSource.sourceCoordinates Source.CanonicalRealization.width_pos
        (sourceHermitianAction Source.CanonicalRealization.width_pos q v) =
      WithLp.toLp 2 (spinorAction (hermitianMatrix q)
        (fun i => Operations.HermiteSource.sourceCoordinates
          Source.CanonicalRealization.width_pos v i))
  hermitian_original_action : ∀ (q : RealCoordinates)
      (v : SourceVacuumTransport.V Source.CanonicalRealization.width_pos),
    (sourceHermitianAction Source.CanonicalRealization.width_pos q v : ComplexL2) =
      corner Source.CanonicalRealization.width_pos (hermitianMatrix q) v

/-! ## Zero-input physical entry -/

/-- Minimal unbiased compositional change generates the canonical physical
interface without a carrier, law, width, orientation, coupling or boundary
argument. Unit covariance has already fixed the width to one and the canonical
complex rotation supplies the orientation. -/
theorem generated : Conclusions := by
  refine {
  geometry := Geometry.GeneratedSourceGeometry.generatedSourceGeometry
  split_response := SourceSplitResponse.generated_split
  frames := SourceFrameConstruction.generated_frames
  internal_response := SourceInternalResponse.source_internalResponse
  complete_matter_exact_sequence := SourceCompleteMatterExactSequence.conclusions
  generated_gauge_group := SourceGeneratedGaugeGroup.sourceGeneratedGaugeGroupProperties
  four_dimensional_gauge_kinematics :=
    SourceFourDimensionalGaugeKinematics.sourceFourDimensionalGaugeProperties
  four_dimensional_colour_yang_mills :=
    SourceFourDimensionalYangMills.sourceFourDimensionalYangMillsProperties
  transverse_traceless_carrier :=
    SourceTransverseTraceless.sourceTransverseTracelessProperties
  tensor_response_endpoint :=
    SourceTensorResponseEndpoint.sourceTensorResponseEndpointProperties
  linearized_gravity :=
    SourceLinearizedGravity.sourceLinearizedGravityProperties
  generated_left_right_family :=
    Geometry.SourceLeftRightRepresentations.generatedFamilyProperties
  generated_projective_scalar_spectrum :=
    SourceRP3FieldSpectrum.generatedScalarProperties
  generated_finite_conformal_response :=
    SourceConformalResponse.finiteProperties
  generated_complete_conformal_response :=
    SourceConformalResponse.completeProperties
  generated_internal_yang_mills_response :=
    SourceInternalYangMillsResponse.properties
  generated_radial_mass_intertwiner :=
    SourceRadialMassIntertwiner.properties
  generated_lorentz_carrier := SourceLorentzCarrier.properties
  generated_yang_mills_gap := SourceGeneratedYangMillsGap.properties
  generated_yang_mills_closure := SourceGeneratedYangMillsClosure.conclusions
  canonical_yang_mills := CanonicalYangMills.generated
  canonical_yang_mills_units := CanonicalYangMillsUnits.generated
  generated_spinor := Geometry.SourceSpinorSystem.generated
  generated_tensor_tt := Geometry.SourceTensorTTSystem.generated
  spin_same_source := SourceSpinIdentification.sourceUnitary_matrix
    Source.CanonicalRealization.width_pos
  hermitian_coordinates := by
    intro X hX
    refine ⟨matrixCoordinates X, hermitianMatrix_matrixCoordinates X hX, ?_⟩
    intro q hq
    calc
      q = matrixCoordinates (hermitianMatrix q) := (matrixCoordinates_hermitianMatrix q).symm
      _ = matrixCoordinates X := congrArg matrixCoordinates hq
  determinant_signature := det_hermitianMatrix
  determinant_invariant := determinantForm_coordinateTransform
  hermitian_same_coordinates := sourceHermitianAction_coordinates
    Source.CanonicalRealization.width_pos
  hermitian_original_action := sourceHermitianAction_coe
    Source.CanonicalRealization.width_pos
  }

end GeneratedFoundations.Physical.SourcePhysicalInterface

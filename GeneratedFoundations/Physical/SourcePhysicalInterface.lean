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
public import GeneratedFoundations.Physical.SourceGeneratedYangMillsGap
public import GeneratedFoundations.Source.MinimalUnbiasedChange

/-!
# Generated source to the basic physical interfaces

The sole root package is minimal unbiased compositional change. The physical
component of `GeneratedFoundations.CommonFoundation.fromMinimalUnbiasedChange`
gives the interface for every orientation and positive width of that datum.
These are realization indices, not additional root principles. The
expanded-argument theorem below is retained for applications.
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
coefficient has one positive endpoint, and the external two-derivative tensor
operator is uniquely selected in its local five-coefficient class by gauge
annihilation, transversality and unit TT normalization.  Its TT reduction is
`Q² I₂`, with the resulting simple massless pole and positive residue. The
same generated source powers supply the complete left--right tensor-product
family, with dimensions, central characters and Casimir operators computed
uniformly. The actual projective scalar spectrum is anchored to the closed
source quotient operator. Its unique condensed response, normalized radial
block and positive odd coclosed colour-connection tower combine into the
strictly positive generated Yang--Mills spectral bottom. Selecting vector,
spinor and TT field branches is
not bundled into this root conclusion until their differential-operator
classification has itself been derived.
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

/-- Outputs of the common source construction, including its actual actions. -/
structure Conclusions
    (d : MinimalCarrier.OrthogonalChangeDatum) (h : MinimalCarrier.IsMinimal d)
    (o : OrientationOnCarrier d) (μ : ℝ → Measure (TraceLieSpace d h))
    (b : ℝ) (hb : 0 < b) : Prop where
  geometry : Geometry.GeneratedSourceGeometry.Conclusions d h o μ b hb
  split_response : SourceSplitResponse.SplitConclusions
  frames : SourceFrameConstruction.FrameConclusions
  internal_response : SourceInternalResponse.Conclusions b hb
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
  spin_same_source : ∀ (M : Mat2) (v : SourceVacuumTransport.V hb),
    SourceSpinIdentification.sourceUnitary hb (SourceVacuumTransport.sourceAction hb M v) =
      SourceSpinIdentification.spinAction M (SourceSpinIdentification.sourceUnitary hb v)
  hermitian_coordinates : ∀ X : Mat2, X.IsHermitian →
    ∃! q : RealCoordinates, hermitianMatrix q = X
  determinant_signature : ∀ q : RealCoordinates,
    (hermitianMatrix q).det = (determinantForm q : ℂ)
  determinant_invariant : ∀ A : Mat2, A.det = 1 → ∀ q : RealCoordinates,
    determinantForm (coordinateTransform A q) = determinantForm q
  hermitian_same_coordinates : ∀ (q : RealCoordinates) (v : SourceVacuumTransport.V hb),
    Operations.HermiteSource.sourceCoordinates hb (sourceHermitianAction hb q v) =
      WithLp.toLp 2 (spinorAction (hermitianMatrix q)
        (fun i => Operations.HermiteSource.sourceCoordinates hb v i))
  hermitian_original_action : ∀ (q : RealCoordinates) (v : SourceVacuumTransport.V hb),
    (sourceHermitianAction hb q v : ComplexL2) = corner hb (hermitianMatrix q) v

/-- The physical branch of one minimal unbiased compositional change datum,
for every orientation and positive realization width. No probability law,
endpoint, boundary operator or physical-interface conclusion is supplied by
the caller outside that sole datum. -/
theorem minimalChange_physicalInterface
    (source : MinimalUnbiasedChange.Datum) :
    ∀ (o : OrientationOnCarrier source.change) (b : ℝ) (hb : 0 < b),
      Conclusions source.change source.minimal o source.law b hb := by
  intro o b hb
  refine {
  geometry := Geometry.GeneratedSourceGeometry.generatedSourceGeometry
    source.change source.minimal o source.law b hb source.compositional
  split_response := SourceSplitResponse.generated_split
  frames := SourceFrameConstruction.generated_frames
  internal_response := SourceInternalResponse.source_internalResponse hb
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
  spin_same_source := SourceSpinIdentification.sourceUnitary_matrix hb
  hermitian_coordinates := by
    intro X hX
    refine ⟨matrixCoordinates X, hermitianMatrix_matrixCoordinates X hX, ?_⟩
    intro q hq
    calc
      q = matrixCoordinates (hermitianMatrix q) := (matrixCoordinates_hermitianMatrix q).symm
      _ = matrixCoordinates X := congrArg matrixCoordinates hq
  determinant_signature := det_hermitianMatrix
  determinant_invariant := determinantForm_coordinateTransform
  hermitian_same_coordinates := sourceHermitianAction_coordinates hb
  hermitian_original_action := sourceHermitianAction_coe hb
  }

end GeneratedFoundations.Physical.SourcePhysicalInterface

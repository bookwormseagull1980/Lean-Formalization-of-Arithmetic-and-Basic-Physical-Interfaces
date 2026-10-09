module

public import GeneratedFoundations.Physical.SourceInternalResponse
public import GeneratedFoundations.Physical.SourceSplitResponse
public import GeneratedFoundations.Physical.SourceFrameConstruction
public import GeneratedFoundations.Source.MinimalUnbiasedChange

/-!
# Generated source to the basic physical interfaces

The sole root package is minimal unbiased compositional change. The theorem
`fromMinimalUnbiasedChange` gives the interface for every orientation and
positive width of that datum. These are realization indices, not additional
root principles. The expanded-argument theorem is retained for applications.
The endpoints, reflecting source evolution, exchange-retained response,
source frames, least matter realization, vacuum lift and elementary connector
are internal constructions and outputs. In particular, no endpoint, boundary
operator or aggregate P4--P6 realization premise is supplied by the caller.
The internal-response output includes the primitive source Clifford sectors
and their actual Hermite projections. The frame output includes pointwise
colour determinant-phase factorization and its finite central ambiguity.
For competing least representations, one realizing unitary transports every
source operator uniquely; the unitary itself is not asserted to be unique.

Classification statements retain the comparison classes stated in their
individual conclusions. The Hermitian readout uses the same two Gaussian
modes and gives the determinant-preserving algebraic interface for relativistic
kinematics. Its zeroth coordinate is not an assumed primitive physical clock.
The record does not assert a reconstruction of spacetime or field dynamics.
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

/-- Expanded form of the root construction for one orientation and width.
No endpoint, boundary operator or physical-interface conclusion is an input. -/
theorem minimalChange_physicalInterface
    (d : MinimalCarrier.OrthogonalChangeDatum) (h : MinimalCarrier.IsMinimal d)
    (o : OrientationOnCarrier d) (μ : ℝ → Measure (TraceLieSpace d h))
    (hμ : HilbertCompositionalAxioms μ) (b : ℝ) (hb : 0 < b) :
    Conclusions d h o μ b hb where
  geometry := Geometry.GeneratedSourceGeometry.generatedSourceGeometry d h o μ b hb hμ
  split_response := SourceSplitResponse.generated_split
  frames := SourceFrameConstruction.generated_frames
  internal_response := SourceInternalResponse.source_internalResponse hb
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

/-- Minimal unbiased compositional change is the only root argument. The
constructed interface is available for every orientation and positive width. -/
theorem fromMinimalUnbiasedChange (source : MinimalUnbiasedChange.Datum) :
    ∀ (o : OrientationOnCarrier source.change) (b : ℝ) (hb : 0 < b),
      Conclusions source.change source.minimal o source.law b hb := by
  intro o b hb
  exact minimalChange_physicalInterface source.change source.minimal o source.law
    source.compositional b hb

end GeneratedFoundations.Physical.SourcePhysicalInterface

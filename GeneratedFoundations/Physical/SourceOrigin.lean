module

public import GeneratedFoundations.Correlation.GeneratedSourceWindow
public import GeneratedFoundations.Source.OrientedTraceCoordinate
public import GeneratedFoundations.Physical.SourceSpinIdentification
public import GeneratedFoundations.Geometry.SourceEndpointCasimir

/-!
# Common origin of the correlation window and the spin carrier

The correlation profile, overlap amplitude and oscillator ground amplitude
are coordinate densities of one measure family on the original trace Lie
line. Their source parameters are respectively `b²`, `b²/4` and `b²/2`.
The last two amplitudes therefore use different normalizations, with the
width change already specified in the differential source construction.

The spin carrier is related to the actual two-mode Gaussian subspace by
its explicit unitary map. The same width determines the global endpoint
radius. None of these comparisons requires the native arithmetic branch.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open GeneratedFoundations.Source GeneratedFoundations.Probability
open GeneratedFoundations.Source.TraceLieGeometry
open GeneratedFoundations.Source.CarrierOrientation
open GeneratedFoundations.Correlation
open GeneratedFoundations.Correlation.GaussianCorrelation
open GeneratedFoundations.Operations
open GeneratedFoundations.Operations.HermiteSource
open GeneratedFoundations.Operations.SourceSpinCorner
open GeneratedFoundations.Physical.SourceSpinIdentification
open GeneratedFoundations.Physical.SourceVacuumTransport

namespace GeneratedFoundations.Physical.SourceOrigin

variable (d : MinimalCarrier.OrthogonalChangeDatum) (h : MinimalCarrier.IsMinimal d)
variable {μ : ℝ → Measure (TraceLieSpace d h)} (hμ : HilbertCompositionalAxioms μ)

include hμ

/-- The density of the actual oscillator vacuum is supplied by the original law. -/
theorem coordinate_ground_density (e : TraceLieSpace d h ≃ₗᵢ[ℝ] ℝ)
    {b : ℝ} (hb : 0 < b) :
    (μ (b ^ 2 / 2)).map e =
      volume.withDensity (fun y => ENNReal.ofReal (groundProfile b y ^ 2)) :=
  (groundProfile_squared_measure (hμ.coordinate_axioms e) hb).symm

/-- Pulling back the coordinate density recovers the original measure itself. -/
theorem original_ground_density (e : TraceLieSpace d h ≃ₗᵢ[ℝ] ℝ)
    {b : ℝ} (hb : 0 < b) :
    μ (b ^ 2 / 2) =
      (volume.withDensity (fun y => ENNReal.ofReal (groundProfile b y ^ 2))).map e.symm := by
  rw [← coordinate_ground_density d h hμ e hb, isometry_map_symm_map]

theorem ground_density_coordinate_independent
    (e f : TraceLieSpace d h ≃ₗᵢ[ℝ] ℝ) {b : ℝ} (hb : 0 < b) :
    (μ (b ^ 2 / 2)).map e = (μ (b ^ 2 / 2)).map f := by
  rw [coordinate_ground_density d h hμ e hb, coordinate_ground_density d h hμ f hb]

/-- One oriented coordinate supplies all three densities. -/
theorem common_densities (o : OrientationOnCarrier d) {b : ℝ} (hb : 0 < b) :
    (μ (b ^ 2)).map (OrientedTraceCoordinate.coordinate d h o) =
        volume.withDensity (fun y => ENNReal.ofReal (changeKernel b y)) ∧
      (μ (b ^ 2 / 4)).map (OrientedTraceCoordinate.coordinate d h o) =
        volume.withDensity (fun y => ENNReal.ofReal (state b 0 y ^ 2)) ∧
      (μ (b ^ 2 / 2)).map (OrientedTraceCoordinate.coordinate d h o) =
        volume.withDensity (fun y => ENNReal.ofReal (groundProfile b y ^ 2)) :=
  ⟨GeneratedSourceWindow.coordinate_profile_density d h hμ
      (OrientedTraceCoordinate.coordinate d h o) hb,
    GeneratedSourceWindow.coordinate_state_squared_density d h hμ
      (OrientedTraceCoordinate.coordinate d h o) hb,
    coordinate_ground_density d h hμ (OrientedTraceCoordinate.coordinate d h o) hb⟩

/-- The explicit source unitary transports the controls built from this
vacuum and its first excitation; the radius uses the same positive width. -/
theorem common_source_spin (o : OrientationOnCarrier d) {b : ℝ} (hb : 0 < b) :
    (μ (b ^ 2 / 2)).map (OrientedTraceCoordinate.coordinate d h o) =
        volume.withDensity (fun y => ENNReal.ofReal (groundProfile b y ^ 2)) ∧
      (∀ (M : Mat2) (v : V hb),
        sourceUnitary hb (sourceAction hb M v) = spinAction M (sourceUnitary hb v)) ∧
      (∀ i : Fin 2, sourceUnitary hb (basisVector hb i) = spinBasis i) ∧
      GeneratedFoundations.Geometry.SourceEndpointCasimir.radius b =
        Real.sqrt (2 * Real.pi) * b :=
  ⟨coordinate_ground_density d h hμ (OrientedTraceCoordinate.coordinate d h o) hb,
    sourceUnitary_matrix hb, sourceUnitary_basis hb,
    GeneratedFoundations.Geometry.SourceEndpointCasimir.radius_eq hb⟩

end GeneratedFoundations.Physical.SourceOrigin

module

public import GeneratedFoundations.Correlation.SourceOrigin
public import GeneratedFoundations.Geometry.SourceSphereCapacity
public import GeneratedFoundations.Geometry.SourceProjectiveGeometry
public import GeneratedFoundations.Geometry.SourceOrthogonalCover
public import GeneratedFoundations.Geometry.SourceProjectiveCovering
public import GeneratedFoundations.Geometry.SourceOrthogonalTopology
public import GeneratedFoundations.Geometry.SourceSimplyConnected
public import GeneratedFoundations.Geometry.SourceSphereTangent
public import GeneratedFoundations.Geometry.SourceSmoothPolar
public import GeneratedFoundations.Geometry.SourceThreeRotations
public import GeneratedFoundations.Geometry.SourceProjectiveOrthogonal
public import GeneratedFoundations.Geometry.SourceMinimalSpin
public import GeneratedFoundations.Geometry.SourceOneFormCoclosedSpectrum
public import GeneratedFoundations.Geometry.SourceFiniteControlDiffusion
public import GeneratedFoundations.Operations.SourceProcessAlgebra
public import GeneratedFoundations.Operations.SourceSpinCornerFlow
public import GeneratedFoundations.Spectral.PhysicalWindowSpectrum
public import GeneratedFoundations.Spectral.NeumannScaleTransport
public import GeneratedFoundations.Source.CanonicalRealization

/-!
# Geometry and spin of one generated source

The minimal unbiased compositional-change root supplies its canonical carrier,
unique positive-parameter trace-line law, unit-covariance width and original
complex orientation. The geometric output record and its construction theorem
accept no carrier, law, orientation or width argument.
The three density normalizations, correlation endpoints, reflecting
spectral closure, finite source operations, complete process observations,
central quotient, endpoint spectrum, real amplitude metric and minimal spin
representation are constructed within this common source. They are outputs,
not additional root data.
The source group and its product are simply connected. Their projective
and special-orthogonal projections are actual two-sheeted topological
coverings in the independently specified target topologies.
The central source quotient also identifies with all three-dimensional
rotations, while the effective ambient projective action has four covering
sheets. Positive polar coordinates use the original sphere atlas and have
the actual derivative given by the source trace formula.

`Conclusions` is a record of proved outputs. `generatedSourceGeometry`
constructs it directly from the canonical root. In particular, the quotient spectrum denotes
the spectrum defined by bounded inverses on the full differential domain,
and its multiplicities are dimensions of actual eigenspaces.
The one-form field is the complete three-component quotient Haar space.
Differentiation in the generated orthonormal frame determines its curl,
whose unique self-adjoint closure retains every source row. The weak
divergence kernel has the complete nonzero-curl eigenbasis and the attained
squared lower edge four.

The record does not assert all differential-geometric clauses of P1--P3.
The spherical capacity comparison is explicitly limited to the stated
factorial spectrum class. The metric comparison concerns bilinear forms
on actual amplitude variations and the genuine sphere tangent fibres.
Constant-curvature space-form classification,
a manifold curvature tensor, and a global identification with an independent
Clifford spin group are not conclusions here. The interval and process
Hilbert spaces remain distinct. No arithmetic construction is imported.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Quaternion RealInnerProductSpace Topology NNReal Manifold ContDiff
open GeneratedFoundations.Source GeneratedFoundations.Probability
open GeneratedFoundations.Source.TraceLieGeometry
open GeneratedFoundations.Source.CarrierOrientation
open GeneratedFoundations.Correlation
open GeneratedFoundations.Correlation.GaussianCorrelation
open GeneratedFoundations.Correlation.Endpoints
open GeneratedFoundations.Operations
open GeneratedFoundations.Operations.HermiteSource (groundProfile)
open GeneratedFoundations.Operations.SourceSpinCorner (Mat2)
open GeneratedFoundations.Operations.SourceSpinCornerGroup (SU2)
open GeneratedFoundations.Operations.SourceVacuumTransport (V basisVector sourceAction)
open GeneratedFoundations.Geometry.SourceSpinIdentification
open GeneratedFoundations.Geometry.SourceSpinCentre (CentralQuotient negativeIdentity)
open GeneratedFoundations.Geometry.SourceCentralObservations (invariantAlgebra quotientContinuous)
open GeneratedFoundations.Geometry.SourceQuaternionAmplitude
open GeneratedFoundations.Geometry.SourcePolarMetric
open GeneratedFoundations.Geometry.SourceInvariantMetric
open GeneratedFoundations.Geometry.SourceQuotientHilbert (QuotientL2)
open GeneratedFoundations.Geometry.SourceDirectionalGenerator (Direction)

namespace GeneratedFoundations.Geometry.GeneratedSourceGeometry

local notation "d" => Source.CanonicalRoot.generated.change
local notation "h" => Source.CanonicalRoot.generated.minimal
local notation "o" => Source.CanonicalRealization.orientation
local notation "μ" => Source.CanonicalRoot.generated.law
local notation "b" => Source.CanonicalRealization.width
local notation "hb" => Source.CanonicalRealization.width_pos

/-- Outputs of the canonical common-source construction, with no parameters.
The comparison classes and maps remain explicit in the field types; the
record does not encode the manuscript's full differential geometry. -/
structure Conclusions : Prop where
  correlation_density :
    (μ (b ^ 2)).map (OrientedTraceCoordinate.coordinate d h o) =
      volume.withDensity (fun y => ENNReal.ofReal (changeKernel b y))
  overlap_density :
    (μ (b ^ 2 / 4)).map (OrientedTraceCoordinate.coordinate d h o) =
      volume.withDensity (fun y => ENNReal.ofReal (state b 0 y ^ 2))
  oscillator_density :
    (μ (b ^ 2 / 2)).map (OrientedTraceCoordinate.coordinate d h o) =
      volume.withDensity (fun y => ENNReal.ofReal (groundProfile b y ^ 2))
  overlap_readout : ∀ x z : ℝ, overlap b x z = profile b (x - z)
  window_endpoints : uvEndpoint b = Real.sqrt 2 * b ∧
    irEndpoint b = Real.sqrt (2 * Real.pi) * b ∧
    windowLength b = b * (Real.sqrt (2 * Real.pi) - Real.sqrt 2) ∧ 0 < windowLength b
  endpoint_readouts : information b (uvEndpoint b) = 1 ∧
    irEndpoint b = peakEquivalentWidth (profile b) ∧
    irEndpoint b / uvEndpoint b = Real.sqrt Real.pi
  endpoint_radius : SourceEndpointCasimir.radius b = Real.sqrt (2 * Real.pi) * b
  endpoint_amplitude_norm : ∀ q : Sphere3,
    ‖SourceSmoothPolar.amplitude (SourceEndpointCasimir.radius b, q)‖ = irEndpoint b
  window_spectrum :
    Spectral.intervalNeumannSpectrum
        (sub_pos.mp (Spectral.windowLengthGenerated_pos hb)) =
      Set.range (fun n : ℕ => (Spectral.neumannEigenvalue
        (Spectral.windowLengthGenerated b) n : ℂ))
  normalized_window_energy : ∀ n : ℕ,
    Spectral.neumannEigenvalue (Spectral.windowLengthGenerated b) n /
        Spectral.neumannEigenvalue (Spectral.windowLengthGenerated b) 1 = (n : ℝ) ^ 2
  finite_corner_algebra : ∀ n : ℕ,
    StarAlgebra.adjoin ℂ ({SourceFiniteCornerAlgebra.sourceAnnihilator hb n} :
      Set (SourceFiniteCornerAlgebra.Carrier hb n →ₗ[ℂ]
        SourceFiniteCornerAlgebra.Carrier hb n)) = ⊤
  finite_corner_capacity : ∀ n : ℕ,
    Module.finrank ℂ (SourceFiniteCornerAlgebra.Carrier hb n →ₗ[ℂ]
      SourceFiniteCornerAlgebra.Carrier hb n) = (n + 1) ^ 2
  process_completion : (SourceProcessAlgebra.processAlgebra hb).topologicalClosure = ⊤
  local_cycle : SourceSpinCornerFlow.localFlow hb (2 * Real.pi) =
    SourceSpinCorner.control hb (-(1 : Mat2))
  sphere_central_sign : ∀ U : SU2,
    (sourceSphereHomeomorph (negativeIdentity * U) : EuclideanSpace ℝ (Fin 4)) =
      -(sourceSphereHomeomorph U : EuclideanSpace ℝ (Fin 4))
  projective_readout : ∀ U : SU2,
    SourceProjectiveGeometry.characterProjectiveHomeomorph
      (SourceObservationSpectrum.sourceCharacter U) = SourceProjectiveGeometry.sourceProjection U
  projective_identification_unique :
    ∀ e : CentralQuotient ≃ₜ SourceProjectiveGeometry.RP3,
      (∀ U : SU2, e (quotientContinuous U) = SourceProjectiveGeometry.sourceProjection U) →
      e = SourceProjectiveGeometry.centralProjectiveHomeomorph
  source_simply_connected : SimplyConnectedSpace SU2
  source_pair_simply_connected : SimplyConnectedSpace SourceLeftRightAction.SourcePair
  projective_covering : IsCoveringMap SourceProjectiveGeometry.sourceProjection
  projective_sheets : ∀ p : SourceProjectiveGeometry.RP3,
    Nat.card (SourceProjectiveGeometry.sourceProjection ⁻¹' {p}) = 2
  complete_observation_orbits : ∀ U W : SU2,
    (∀ f : invariantAlgebra, f.val U = f.val W) ↔
      SourceProjectiveGeometry.sourceProjection U = SourceProjectiveGeometry.sourceProjection W
  all_characters : ∀ φ : WeakDual.characterSpace ℂ invariantAlgebra,
    ∃! q : CentralQuotient, ∀ f : invariantAlgebra,
      φ f = SourceCentralObservations.descentStarAlgEquiv f q
  endpoint_spectrum :
    SourceEndpointSpectrum.spectrum (SourceEndpointCasimir.radius b) =
      Set.range (fun n : ℕ =>
        ((((2 * (n : ℝ) + 1) ^ 2 - 1) / SourceEndpointCasimir.radius b ^ 2 : ℝ) : ℂ))
  endpoint_multiplicity : ∀ n : ℕ,
    Module.finrank ℂ (SourceEndpointSpectrum.eigenspace (SourceEndpointCasimir.radius b)
      ((((2 * (n : ℝ) + 1) ^ 2 - 1) / SourceEndpointCasimir.radius b ^ 2 : ℝ) : ℂ)) =
        (2 * n + 1) ^ 2
  endpoint_compact_resolvent : ∃ R : QuotientL2 →L[ℂ] QuotientL2,
    SourceEndpointSpectrum.IsResolvent (SourceEndpointCasimir.radius b) (-1) R ∧
      IsCompactOperator R
  one_form_curl_selfAdjoint :
    IsSelfAdjoint SourceOneFormCurlSpectrum.closedCurl
  one_form_curl_unique : ∀ S,
    IsSelfAdjoint S → SourceOneFormCurlSpectrum.finiteCurl ≤ S →
      S = SourceOneFormCurlSpectrum.closedCurl
  one_form_coclosed_expansion : ∀ A : SourceOneFormClosedHodge.coclosedField,
    HasSum (fun a : SourceOneFormCoclosedSpectrum.CoclosedIndex =>
      inner ℂ (SourceOneFormCoclosedSpectrum.coclosedHilbertBasis a) A •
        SourceOneFormCoclosedSpectrum.coclosedHilbertBasis a) A
  one_form_coclosed_bound : ∀ A : SourceOneFormCurlSpectrum.closedCurl.domain,
    A.val ∈ SourceOneFormClosedHodge.coclosedField →
      4 * ‖A.val‖ ^ 2 ≤ ‖SourceOneFormCurlSpectrum.closedCurl A‖ ^ 2
  one_form_coclosed_attainment :
    ‖SourceOneFormLowestCurl.lowestField‖ = 1 ∧
      SourceOneFormLowestCurl.lowestField ∈ SourceOneFormClosedHodge.coclosedField ∧
      ‖SourceOneFormCurlSpectrum.closedCurl SourceOneFormLowestCurl.lowestDomain‖ ^ 2 = 4
  one_form_projective_parity : ∀ a : SourceOneFormCoclosedSpectrum.CoclosedIndex,
    ∃ l : ℕ, Odd l ∧ 1 ≤ l ∧
      SourceOneFormCurlSpectrum.eigenvalue a.val ^ 2 = ((l : ℝ) + 1) ^ 2
  same_degree_capacity : ∀ l : ℕ, Even l →
    Module.finrank ℂ (SourceFiniteCornerAlgebra.Carrier hb l →ₗ[ℂ]
      SourceFiniteCornerAlgebra.Carrier hb l) =
    Module.finrank ℂ (SourceEndpointSpectrum.eigenspace (SourceEndpointCasimir.radius b)
      ((SourceSphereCapacity.sphereEigenvalue 3 l / SourceEndpointCasimir.radius b ^ 2 : ℝ) : ℂ))
  spherical_capacity_unique : ∀ k : ℕ, 2 ≤ k →
    ((∀ l : ℕ, Even l → SourceSphereCapacity.sphereMultiplicity k l =
      (Module.finrank ℂ (SourceFiniteCornerAlgebra.Carrier hb l →ₗ[ℂ]
        SourceFiniteCornerAlgebra.Carrier hb l) : ℝ)) ↔ k = 3)
  spherical_affine_unique : ∀ k : ℕ, 2 ≤ k → ∀ a c : ℝ,
    (0 < a ∧ ∀ l : ℕ, Even l → SourceSphereCapacity.sphereMultiplicity k l =
      a * SourceSphereCapacity.sphereEigenvalue k l + c) ↔ k = 3 ∧ a = 1 ∧ c = 1
  amplitude_minimal : ∀ A : Subalgebra ℝ Mat2,
    amplitudeAlgebra ≤ A ↔ ∀ U : SU2, (U : Mat2) ∈ A
  amplitude_dimension : Module.finrank ℝ amplitudeAlgebra = 4
  positive_polar_unique : ∀ M : amplitudeAlgebra, (M : Mat2) ≠ 0 →
    ∃! p : ℝ × SU2, 0 < p.1 ∧ (M : Mat2) = p.1 • (p.2 : Mat2)
  endpoint_trace_metric : ∀ (U : SU2) (x y : ℝ × angularSpace (ofMatrix U)),
    (Matrix.trace ((sourceVariation (SourceEndpointCasimir.radius b) (ofMatrix U) x).conjTranspose *
      sourceVariation (SourceEndpointCasimir.radius b) (ofMatrix U) y)).re / 2 =
        x.1 * y.1 + SourceEndpointCasimir.radius b ^ 2 * inner ℝ (x.2 : ℍ) (y.2 : ℍ)
  tangent_dimension : ∀ U : SU2,
    Module.finrank ℝ (SourceSphereTangent.SphereTangent (sourceSphereHomeomorph U)) = 3
  tangent_metric_positive : ∀ (q : Sphere3) (v : SourceSphereTangent.SphereTangent q),
    v ≠ 0 → 0 < SourceSphereTangent.sphereMetric q v v
  tangent_polar_unique : ∀ (U : SU2) (v : ℍ),
    ∃! x : ℝ × SourceSphereTangent.SphereTangent (sourceSphereHomeomorph U),
      SourceSphereTangent.polarTangentMap (sourceSphereHomeomorph U)
        (SourceEndpointCasimir.radius b) x = v
  endpoint_tangent_metric : ∀ (U : SU2)
    (x y : ℝ × SourceSphereTangent.SphereTangent (sourceSphereHomeomorph U)),
    (Matrix.trace
      ((matrixMap (SourceSphereTangent.polarTangentMap (sourceSphereHomeomorph U)
          (SourceEndpointCasimir.radius b) x)).conjTranspose *
        matrixMap (SourceSphereTangent.polarTangentMap (sourceSphereHomeomorph U)
          (SourceEndpointCasimir.radius b) y))).re / 2 =
      x.1 * y.1 + SourceEndpointCasimir.radius b ^ 2 *
        SourceSphereTangent.sphereMetric (sourceSphereHomeomorph U) x.2 y.2
  positive_polar_smooth :
    ContMDiff SourceSmoothPolar.polarModel 𝓘(ℝ, ℍ) ∞ SourceSmoothPolar.polar
  positive_polar_inverse_smooth :
    ContMDiff 𝓘(ℝ, ℍ) SourceSmoothPolar.polarModel ∞ SourceSmoothPolar.polarInverse
  positive_polar_differential : ∀ p : SourceSmoothPolar.PolarCarrier,
    mfderiv SourceSmoothPolar.polarModel 𝓘(ℝ, ℍ) SourceSmoothPolar.polar p =
      (SourceSphereTangent.polarTangentMap p.2 (p.1 : ℝ)).comp
        (SourceSmoothPolar.positiveProductCoordinates p).toContinuousLinearMap
  positive_polar_trace : ∀ (p : SourceSmoothPolar.PolarCarrier)
    (v w : TangentSpace SourceSmoothPolar.polarModel p),
    (Matrix.trace ((matrixMap
      (mvfderiv SourceSmoothPolar.polarModel
        (fun z : SourceSmoothPolar.PolarCarrier => (SourceSmoothPolar.polar z : ℍ)) p v)).conjTranspose *
      matrixMap (mvfderiv SourceSmoothPolar.polarModel
        (fun z : SourceSmoothPolar.PolarCarrier => (SourceSmoothPolar.polar z : ℍ)) p w))).re / 2 =
      v.1 * w.1 + (p.1 : ℝ) ^ 2 * SourceSphereTangent.sphereMetric p.2 v.2 w.2
  metric_realized : SourceSpecialOrthogonal.IsCalibratedSpecialOrthogonalMetric traceMetric
  metric_unique : ∀ G : MetricFamily,
    SourceSpecialOrthogonal.IsCalibratedSpecialOrthogonalMetric G →
      ∀ (r : ℝ), 0 < r → ∀ q : unitary ℍ, G r q = traceMetric r q
  orthogonal_action_surjective : Function.Surjective SourceOrthogonalCover.sourceCover
  orthogonal_action_kernel : ∀ p : SourceLeftRightAction.SourcePair,
    SourceOrthogonalCover.sourceCover p = 1 ↔
      p = (1, 1) ∨ p = (negativeIdentity, negativeIdentity)
  orthogonal_covering : IsCoveringMap SourceOrthogonalCover.sourceCover
  orthogonal_sheets : ∀ e : SourceOrthogonalCover.specialOrthogonal,
    Nat.card (SourceOrthogonalCover.sourceCover ⁻¹' {e}) = 2
  rotation_covering : IsCoveringMap SourceThreeRotations.sourceRotations
  rotation_sheets : ∀ e : SourceThreeRotations.rotations,
    Nat.card (SourceThreeRotations.sourceRotations ⁻¹' {e}) = 2
  rotation_readout_unique : ∀ e : SourceProjectiveGeometry.RP3 ≃ₜ SourceThreeRotations.rotations,
    (∀ U : SU2, e (SourceProjectiveGeometry.sourceProjection U) =
      SourceThreeRotations.sourceRotations U) → e = SourceThreeRotations.projectiveRotationsHomeomorph
  effective_projective_kernel : SourceProjectiveOrthogonal.effectiveCover.ker =
    (Subgroup.center SU2).prod (Subgroup.center SU2)
  effective_projective_covering : IsCoveringMap SourceProjectiveOrthogonal.effectiveCover
  effective_projective_sheets : ∀ e : SourceProjectiveOrthogonal.EffectiveOrthogonal,
    Nat.card (SourceProjectiveOrthogonal.effectiveCover ⁻¹' {e}) = 4
  effective_projective_action : ∀ (p : SourceLeftRightAction.SourcePair)
    (x : SourceProjectiveGeometry.RP3),
    SourceProjectiveOrthogonal.effectiveRepresentation
        (SourceProjectiveOrthogonal.effectiveCover p) x = SourceLeftRightAction.projectiveAction p x
  effective_projective_faithful : Function.Injective SourceProjectiveOrthogonal.effectiveRepresentation
  spin_same_source : ∀ (M : Mat2) (v : V hb),
    sourceUnitary hb (sourceAction hb M v) = spinAction M (sourceUnitary hb v)
  spin_fixed_modes : ∀ i : Fin 2, sourceUnitary hb (basisVector hb i) = spinBasis i
  spin_least : SourceMinimalSpin.IsLeastCentreSensitive
    (SourceSymmetricUnitary.unitaryRepresentation 1)

/-- The canonical minimal-change root generates every geometric record field.
The Gaussian law, width and orientation have already been constructed. -/
theorem generatedSourceGeometry : Conclusions := by
  obtain ⟨hprofile, hoverlap, hground⟩ := Correlation.SourceOrigin.common_densities
    d h Source.CanonicalRoot.generated.compositional o hb
  refine {
    correlation_density := hprofile
    overlap_density := hoverlap
    oscillator_density := hground
    overlap_readout := overlap_eq_profile hb
    window_endpoints := ⟨uvEndpoint_eq hb, irEndpoint_eq hb, windowLength_eq hb, windowLength_pos hb⟩
    endpoint_readouts := ⟨uvEndpoint_information hb,
      irEndpoint_eq_peakEquivalentWidth b, endpoint_ratio hb⟩
    endpoint_radius := SourceEndpointCasimir.radius_eq hb
    endpoint_amplitude_norm := fun q =>
      SourceSmoothPolar.amplitude_norm (SourceEndpointCasimir.radius_pos hb) q
    window_spectrum := Spectral.generatedWindow_neumannSpectrum hb
    normalized_window_energy := ?_
    finite_corner_algebra := fun n => (SourceResponseCapacity.finiteCorner_responseCapacity hb n 0).1
    finite_corner_capacity := fun n => (SourceResponseCapacity.finiteCorner_responseCapacity hb n 0).2.1
    process_completion := SourceProcessAlgebra.processAlgebra_complete hb
    local_cycle := SourceSpinCornerFlow.localFlow_two_pi_control hb
    sphere_central_sign := sourceSphere_central
    projective_readout := SourceProjectiveGeometry.characterProjectiveHomeomorph_source
    projective_identification_unique := SourceProjectiveGeometry.centralProjectiveHomeomorph_unique
    source_simply_connected := SourceSimplyConnected.source_simplyConnected
    source_pair_simply_connected := SourceSimplyConnected.sourcePair_simplyConnected
    projective_covering := SourceProjectiveCovering.sourceProjection_isCoveringMap
    projective_sheets := SourceProjectiveCovering.sourceProjection_fibre_card
    complete_observation_orbits := SourceProjectiveGeometry.observations_equal_iff_projective
    all_characters := SourceObservationSpectrum.character_is_unique_orbit_evaluation
    endpoint_spectrum := SourceEndpointSpectrum.endpoint_spectrum hb
    endpoint_multiplicity := SourceEndpointSpectrum.endpoint_multiplicity hb
    endpoint_compact_resolvent := SourceEndpointSpectrum.has_compact_resolvent
      (SourceEndpointCasimir.radius_pos hb).ne'
    one_form_curl_selfAdjoint := SourceOneFormCurlSpectrum.closedCurl_selfAdjoint
    one_form_curl_unique := SourceOneFormCurlSpectrum.closedCurl_unique
    one_form_coclosed_expansion := fun A => by
      simpa only [HilbertBasis.repr_apply_apply] using
        SourceOneFormCoclosedSpectrum.coclosedHilbertBasis.hasSum_repr A
    one_form_coclosed_bound := SourceOneFormClosedHodge.closedCurl_coclosed_coercivity
    one_form_coclosed_attainment := SourceOneFormLowestCurl.complete_coclosed_bottom.2
    one_form_projective_parity := fun a =>
      SourceOneFormCurlBranches.every_nongauge_field_mode_has_odd_degree a.val a.property
    same_degree_capacity := SourceSphereCapacity.source_corner_endpoint_finrank hb
    spherical_capacity_unique := SourceSphereCapacity.source_capacity_even_iff hb
    spherical_affine_unique := SourceSphereCapacity.affine_even_iff
    amplitude_minimal := amplitudeAlgebra_le_iff
    amplitude_dimension := amplitude_finrank
    positive_polar_unique := amplitude_positive_polar_existsUnique
    endpoint_trace_metric := fun U => source_group_trace_polar U (SourceEndpointCasimir.radius b)
    tangent_dimension := fun U => SourceSphereTangent.tangent_finrank (sourceSphereHomeomorph U)
    tangent_metric_positive := fun q v hv => SourceSphereTangent.sphereMetric_pos q hv
    tangent_polar_unique := fun U v => SourceSphereTangent.polarTangent_existsUnique
      (sourceSphereHomeomorph U) (SourceEndpointCasimir.radius_pos hb).ne' v
    endpoint_tangent_metric := fun U => SourceSphereTangent.source_group_trace_polar_tangent U
      (SourceEndpointCasimir.radius b)
    positive_polar_smooth := SourceSmoothPolar.polar_contMDiff
    positive_polar_inverse_smooth := SourceSmoothPolar.polarInverse_contMDiff
    positive_polar_differential := SourceSmoothPolar.polar_open_mfderiv
    positive_polar_trace := SourceSmoothPolar.polar_trace_pullback
    metric_realized := SourceSpecialOrthogonal.traceMetric_specialOrthogonal
    metric_unique := ?_
    orthogonal_action_surjective := SourceOrthogonalCover.sourceCover_surjective
    orthogonal_action_kernel := SourceOrthogonalCover.sourceCover_kernel_iff
    orthogonal_covering := SourceOrthogonalTopology.sourceCover_isCoveringMap
    orthogonal_sheets := SourceOrthogonalTopology.sourceCover_fibre_card
    rotation_covering := SourceThreeRotations.sourceRotations_isCoveringMap
    rotation_sheets := SourceThreeRotations.sourceRotations_fibre_card
    rotation_readout_unique := SourceThreeRotations.projectiveRotationsHomeomorph_unique
    effective_projective_kernel := SourceProjectiveOrthogonal.effectiveCover_kernel
    effective_projective_covering := SourceProjectiveOrthogonal.effectiveCover_isCoveringMap
    effective_projective_sheets := SourceProjectiveOrthogonal.effectiveCover_fibre_card
    effective_projective_action := SourceProjectiveOrthogonal.effectiveRepresentation_source
    effective_projective_faithful := SourceProjectiveOrthogonal.effectiveRepresentation_injective
    spin_same_source := sourceUnitary_matrix hb
    spin_fixed_modes := sourceUnitary_basis hb
    spin_least := SourceMinimalSpin.degree_one_isLeast }
  · intro n
    let : Fact (0 < Spectral.windowLengthGenerated b) :=
      ⟨Spectral.windowLengthGenerated_pos hb⟩
    exact Spectral.NeumannScaleTransport.normalized_eigenvalue
      (Spectral.windowLengthGenerated b) n
  · intro G hG r hr q
    exact hG.eq_inner hr q

/-- The existing finite-control experiment remains quantified over its
complete finite-variance input class. This interface supplies no extra
microscopic direction law and does not choose one by its desired spectrum. -/
theorem finite_variance_operation_limit
    {ν : Measure Direction} [IsProbabilityMeasure ν]
    (hi : Integrable SourceDirectionalGenerator.sizeSq ν)
    (hp : 0 < ∫ ξ : Direction, SourceDirectionalGenerator.sizeSq ξ ∂ν)
    (t : ℝ) (ht : 0 ≤ t) :
    ∃! ρ : ProbabilityMeasure SU2,
      SourceWeakConvergence.HasEntryIntegrals ρ (SourceWeakConvergence.heatCoefficient t) ∧
        Tendsto (fun ε : ℝ => SourceFiniteControlDiffusion.experiment ν ε
          ⌊24 * t / ((∫ ξ : Direction, SourceDirectionalGenerator.sizeSq ξ ∂ν) * ε ^ 2)⌋₊)
          (𝓝[≠] 0) (𝓝 ρ) :=
  SourceFiniteControlDiffusion.finiteVariance_operationWalk_tendsto_heat hi hp t ht

end GeneratedFoundations.Geometry.GeneratedSourceGeometry

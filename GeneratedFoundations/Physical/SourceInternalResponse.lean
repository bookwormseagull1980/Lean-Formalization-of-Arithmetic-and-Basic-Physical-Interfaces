module

public import GeneratedFoundations.Physical.SourceOrigin
public import GeneratedFoundations.Physical.SourceColourCasimir
public import GeneratedFoundations.Physical.SourceExchangeConnectorTransport
public import GeneratedFoundations.Physical.SourceMatterPhaseExponential
public import GeneratedFoundations.Physical.SourceGaugeCocycle
public import GeneratedFoundations.Physical.SourceChargedQuotient
public import GeneratedFoundations.Physical.SourceScalarGaugeCovariance
public import GeneratedFoundations.Geometry.GeneratedSourceGeometry
public import GeneratedFoundations.Physical.SourceMinimalChiralPair
public import GeneratedFoundations.Physical.SourceLocalizedMatter
public import GeneratedFoundations.Physical.SourceHermitianReadout
public import GeneratedFoundations.Physical.SourceCliffordChirality

/-!
# Internal response on the common generated matter carrier

The root data `d`, `h`, `μ`, and `hμ` jointly express minimal unbiased
compositional change. The orientation `o` and positive width `b` index its
coordinate and scale realizations. The response algebra, vacuum, phase,
quotient and elementary connector below are internal source constructions.
The two chiral sectors are the ranges of the primitive central projections
of the actual source Clifford even algebra, transported to the same Hermite
carrier. The labels refer to these constructed projections. Their
physical interfaces are generated outputs, rather than additional root data.

The least-module and elementary-connector clauses quantify over their
stated competing realizations; the displayed dimensions and doublet are
conclusions of those classifications. The canonical least module,
transported vacuum action and elementary connector are constructed, rather
than supplied as a P4--P6 premise. These statements do not claim uniqueness
outside their comparison classes. Applications to local bundle charts
retain their separately stated compatibility conditions.

This record collects the finite internal conclusions. Geometric source
properties and compatibility with actual local bundle charts are separate
interfaces. In particular, the charged quotient is a gauge module; the
nonzero elementary scalar connector does not descend to it.

The imported `SourceHermitianReadout` provides the determinant-preserving
Hermitian readout on the same two Gaussian modes. Its real coordinates and
congruence transformations form a downstream relativistic interface,
separate from the internal gauge action below. These algebraic interfaces
do not by themselves construct a complete spacetime or its field equations.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Quaternion
open GeneratedFoundations.Source GeneratedFoundations.Probability
open GeneratedFoundations.Source.TraceLieGeometry
open GeneratedFoundations.Source.CarrierOrientation

namespace GeneratedFoundations.Physical.SourceInternalResponse

open SourceJointResponse SourceMinimalRepresentation SourceChiralCarrier
open SourceMatterCharge SourceScalarConnector
open ReversalRealConnector (Spinor connectorOfDoublet)

local instance : NormedRing SourceMatterPhaseExponential.MatterEnd :=
  ContinuousLinearMap.toNormedRing

local instance : IsTopologicalRing SourceMatterPhaseExponential.MatterEnd :=
  NonUnitalSeminormedRing.toIsTopologicalRing

/-- The generated even algebra and its actual two source sectors. -/
structure ChiralConclusions (b : ℝ) (hb : 0 < b) : Prop where
  grading_generated : SourceCliffordConnector.grading =
    -(SourceCliffordConnector.clifford 1 *
      SourceCliffordConnector.clifford SourceCliffordChirality.sourceI *
      (SourceCliffordConnector.clifford SourceCliffordChirality.sourceJ *
        SourceCliffordConnector.clifford SourceCliffordChirality.sourceK))
  real_even_algebra : Nonempty
    ((ℍ × ℍ) ≃ₐ[ℝ] SourceCliffordChirality.evenSourceAlgebra)
  complex_even_algebra : Nonempty
    ((ReversalRealConnector.Mat2 × ReversalRealConnector.Mat2) ≃ₐ[ℂ]
      SourceCliffordChirality.complexEvenSourceAlgebra)
  primitive_sectors : SourceCliffordChirality.positive ≠ SourceCliffordChirality.negative ∧
    ∀ P : SourceCliffordChirality.evenSourceAlgebra,
      SourceCliffordChirality.IsPrimitiveCentral P ↔
        P = SourceCliffordChirality.positive ∨ P = SourceCliffordChirality.negative
  spinor_dimensions : Module.finrank ℂ SourceCliffordChirality.positiveSpace = 2 ∧
    Module.finrank ℂ SourceCliffordChirality.negativeSpace = 2
  source_projections : ∀ x : FullMatter,
    hermiteIsometry hb (leftProjection x) =
        SourceCliffordChirality.sourcePositive hb (hermiteIsometry hb x) ∧
      hermiteIsometry hb (rightProjection x) =
        SourceCliffordChirality.sourceNegative hb (hermiteIsometry hb x)
  source_ranges :
    LinearMap.range (SourceCliffordChirality.sourcePositive hb).toLinearMap =
        LinearMap.range (SourceCliffordChirality.leftSourceEmbedding hb) ∧
      LinearMap.range (SourceCliffordChirality.sourceNegative hb).toLinearMap =
        LinearMap.range (SourceCliffordChirality.rightSourceEmbedding hb)
  source_dimensions :
    Module.finrank ℂ (LinearMap.range (SourceCliffordChirality.sourcePositive hb).toLinearMap) = 8 ∧
      Module.finrank ℂ (LinearMap.range (SourceCliffordChirality.sourceNegative hb).toLinearMap) = 8

theorem source_chirality {b : ℝ} (hb : 0 < b) : ChiralConclusions b hb where
  grading_generated := SourceCliffordChirality.grading_from_source_product
  real_even_algebra := ⟨SourceCliffordChirality.evenEquiv⟩
  complex_even_algebra := ⟨SourceCliffordChirality.complexEvenEquiv⟩
  primitive_sectors := ⟨SourceCliffordChirality.positive_ne_negative,
    SourceCliffordChirality.primitiveCentral_iff⟩
  spinor_dimensions := ⟨SourceCliffordChirality.positiveSpace_finrank,
    SourceCliffordChirality.negativeSpace_finrank⟩
  source_projections := fun x => ⟨SourceCliffordChirality.hermite_leftProjection hb x,
    SourceCliffordChirality.hermite_rightProjection hb x⟩
  source_ranges := ⟨SourceCliffordChirality.sourcePositive_range hb,
    SourceCliffordChirality.sourceNegative_range hb⟩
  source_dimensions := ⟨SourceCliffordChirality.sourcePositive_finrank hb,
    SourceCliffordChirality.sourceNegative_finrank hb⟩

/-- Internal physical outputs on the generated source objects at each
positive width, with the classification domains explicit in the fields. -/
structure Conclusions (b : ℝ) (hb : 0 < b) : Prop where
  chirality : ChiralConclusions b hb
  least_source : IsLeastFaithfulRepresentation sourceCarrierRepresentation
  least_classification : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] (ρ : JointEnd →ₐ[ℂ] Module.End ℂ H),
    IsLeastFaithfulRepresentation ρ →
      ∃ U : H ≃ₗᵢ[ℂ] SourceCarrier,
        ∀ A x, U (ρ A x) = sourceCarrierRepresentation A (U x)
  least_pair_transport : ∀ (HL HR : Type)
    [NormedAddCommGroup HL] [InnerProductSpace ℂ HL]
    [NormedAddCommGroup HR] [InnerProductSpace ℂ HR]
    [FiniteDimensional ℂ HL] [FiniteDimensional ℂ HR]
    (ρL : JointEnd →ₐ[ℂ] Module.End ℂ HL) (ρR : JointEnd →ₐ[ℂ] Module.End ℂ HR),
    IsLeastFaithfulRepresentation ρL → IsLeastFaithfulRepresentation ρR →
      ∃ U : SourceMinimalChiralPair.Carrier HL HR ≃ₗᵢ[ℂ] FullMatter,
        (∀ A B x, U (SourceMinimalChiralPair.diagonalBlocks (ρL A) (ρR B) x) =
          diagonalBlocks (sourceCarrierRepresentation A) (sourceCarrierRepresentation B) (U x)) ∧
        (∀ x, U (SourceMinimalChiralPair.leftProjection x) = leftProjection (U x)) ∧
        (∀ x, U (SourceMinimalChiralPair.rightProjection x) = rightProjection (U x)) ∧
        (∀ x, U (SourceMinimalChiralPair.grading x) = grading (U x)) ∧
        (∀ T : Module.End ℂ FullMatter,
          ∃! A : Module.End ℂ (SourceMinimalChiralPair.Carrier HL HR),
            ∀ x, U (A x) = T (U x))
  full_dimension : Module.finrank ℂ FullMatter = 16
  vacuum_stabilizer : ∀ (g : Operations.SourceSpinCornerGroup.SU2) (z : Circle),
    (g, z) ∈ Set.range SourcePhaseLift.lift ↔
      SourcePhaseLift.rightAction hb g z (SourceVacuumTransport.transportedVacuum hb) =
        SourceVacuumTransport.transportedVacuum hb
  source_lift_unique : ∀ f : ℝ → SourcePhaseLift.RightFrame,
    Continuous f → f 0 = 1 →
      (∀ t, SourcePhaseLift.rightScalarMatrix (f t).1 (f t).2 =
        Operations.SourceNumberFlow.numberFlowMatrix t) → f = SourcePhaseLift.lift
  vacuum_number_flow : ∀ (t : ℝ) (v : SourceVacuumTransport.V hb),
    SourceGaugeTransport.phaseFlow t
        (SourceMatterPhaseExponential.rightScalarSpinInclusion
          (SourceSpinIdentification.sourceUnitary hb v)) =
      SourceMatterPhaseExponential.rightScalarSpinInclusion
        (SourceSpinIdentification.sourceUnitary hb
          (SourceVacuumTransport.sourceAction hb (Operations.SourceNumberFlow.numberFlowMatrix t) v))
  primitive_charge_unique : ∀ (α β : ℝ) (w : SourceChargeLattice.Sector → ℤ),
    SourceChargeLattice.IntegralRealization α β w → SourceChargeLattice.PrimitiveWeights w →
      realChargeOperator α β neutralVector = 0 → 0 < β →
        realChargeOperator α β = generatedChargeOperator
  phase_exponential : ∀ t : ℝ,
    SourceMatterPhaseExponential.continuousModel (SourceGaugeTransport.phaseFlow t) =
      NormedSpace.exp (((t : ℂ) * Complex.I) •
        SourceMatterPhaseExponential.continuousModel hyperchargeOperator)
  phase_period : IsLeast
    {t : ℝ | 0 < t ∧ Function.Periodic SourceGaugeTransport.phaseFlow t} (12 * Real.pi)
  gauge_kernel : SourceGaugeTransport.representation.ker = SourceGlobalGaugeGroup.centralSix
  kernel_card : Nat.card SourceGlobalGaugeGroup.centralSix = 6
  effective_faithful : Function.Injective SourceGaugeUnitary.effectiveUnitaryRepresentation
  neutral_nonzero : neutralVector ≠ 0
  neutral_dimension : Module.finrank ℂ neutralLine = 1
  response_kernel : LinearMap.ker SourceColourCasimir.fullQuadraticResponse = neutralLine
  charged_dimension : Module.finrank ℂ SourceChargedQuotient.ChargedMatter = 15
  quotient_surjective : Function.Surjective SourceChargedQuotient.quotientMap
  quotient_action : ∀ g : GlobalGaugeKernel.GaugeGroup,
    SourceChargedQuotient.quotientMap.comp (SourceGaugeTransport.representation g) =
      (SourceChargedQuotient.quotientRepresentation g).comp SourceChargedQuotient.quotientMap
  operator_descent : ∀ A : Module.End ℂ FullMatter,
    (∃! B : Module.End ℂ SourceChargedQuotient.ChargedMatter,
      SourceChargedQuotient.quotientMap.comp A = B.comp SourceChargedQuotient.quotientMap) ↔
        SourceChargedQuotient.PreservesNeutral A
  elementary_classification : ∀ T : Module.End ℂ SourcePreExchangeResponse.FullCarrier,
    Elementary T ↔ ∃! H : Spinor,
      T = SourcePreExchangeResponse.spinLift (doubletLift H)
  elementary_constructed : ∀ H : Spinor,
    Elementary (SourcePreExchangeResponse.spinLift (doubletLift H))
  split_elementary_classification : ∀ A : Module.End ℂ SourceCarrier,
    SourceExchangeConnectorTransport.SplitElementary A ↔ ∃! H : Spinor,
      A = spinOnSource (doubletLift H)
  scalar_selfAdjoint : ∀ H : Spinor, IsSelfAdjoint (scalarConnector H)
  scalar_odd : ∀ H : Spinor,
    grading * scalarConnector H + scalarConnector H * grading = 0
  scalar_source : ∀ (H : Spinor) (x : FullMatter),
    hermiteIsometry hb (scalarConnector H x) =
      SourceCliffordConnector.sourceConnector hb 4
        (Geometry.SourceQuaternionAmplitude.ofMatrix (connectorOfDoublet H))
        (hermiteIsometry hb x)
  scalar_covariance : ∀ (g : GlobalGaugeKernel.GaugeGroup) (H : Spinor),
    SourceGaugeTransport.representation g * scalarConnector H *
        SourceGaugeTransport.representation g⁻¹ =
      scalarConnector (SourceScalarGaugeCovariance.scalarAction g H)
  scalar_descent : ∀ H : Spinor, SourceChargedQuotient.Descends (scalarConnector H) ↔ H = 0

theorem source_internalResponse {b : ℝ} (hb : 0 < b) : Conclusions b hb where
  chirality := source_chirality hb
  least_source := sourceCarrierRepresentation_isLeast
  least_classification := fun H _ _ _ ρ hρ => least_unitarilyEquivalentToSource (H := H) ρ hρ
  least_pair_transport := fun _ _ _ _ _ _ _ _ ρL ρR hL hR =>
    SourceMinimalChiralPair.least_pair_compatible_response ρL ρR hL hR
  full_dimension := fullMatter_finrank
  vacuum_stabilizer := SourcePhaseLift.mem_lift_range_iff_fixes_source_vacuum hb
  source_lift_unique := SourcePhaseLift.continuous_lift_unique
  vacuum_number_flow := SourceMatterPhaseExponential.phaseFlow_sourceNumber hb
  primitive_charge_unique := fun _ _ _ => realChargeOperator_unique_of_source_vacuum
  phase_exponential := SourceMatterPhaseExponential.phaseFlow_eq_exp
  phase_period := SourceGaugeTransport.phaseFlow_least_positive_period
  gauge_kernel := SourceGaugeTransport.kernel_eq_zpowers
  kernel_card := SourceGlobalGaugeGroup.centralSix_card
  effective_faithful := SourceGaugeUnitary.effectiveUnitaryRepresentation_injective
  neutral_nonzero := neutralVector_ne_zero
  neutral_dimension := neutralLine_finrank
  response_kernel := SourceColourCasimir.fullQuadraticResponse_kernel
  charged_dimension := chargedQuotient_finrank
  quotient_surjective := SourceChargedQuotient.quotientMap_surjective
  quotient_action := SourceChargedQuotient.quotientRepresentation_intertwines
  operator_descent := SourceChargedQuotient.existsUnique_induced_iff
  elementary_classification := elementary_iff_unique_doublet
  elementary_constructed := canonical_elementary
  split_elementary_classification := SourceExchangeConnectorTransport.splitElementary_iff_unique_doublet
  scalar_selfAdjoint := scalarConnector_isSelfAdjoint
  scalar_odd := scalarConnector_odd
  scalar_source := scalarConnector_hermite hb
  scalar_covariance := SourceScalarGaugeCovariance.scalarConnector_covariant
  scalar_descent := SourceChargedQuotient.scalarConnector_descends_iff

/-- The root data determine the Gaussian amplitude at every orientation and
positive width. The same width indexes the physical carrier's Hermite
realization, so no independent physical amplitude is supplied. -/
theorem minimalChange_internalResponse
    (d : MinimalCarrier.OrthogonalChangeDatum) (h : MinimalCarrier.IsMinimal d)
    (o : OrientationOnCarrier d) {μ : ℝ → Measure (TraceLieSpace d h)}
    (hμ : HilbertCompositionalAxioms μ) {b : ℝ} (hb : 0 < b) :
    (μ (b ^ 2 / 2)).map (OrientedTraceCoordinate.coordinate d h o) =
        volume.withDensity (fun y => ENNReal.ofReal (Operations.HermiteSource.groundProfile b y ^ 2)) ∧
      Conclusions b hb :=
  ⟨SourceOrigin.coordinate_ground_density d h hμ
    (OrientedTraceCoordinate.coordinate d h o) hb, source_internalResponse hb⟩

/-- Geometric and finite physical outputs of the same root data, for every
orientation and positive width. Their individual records retain the exact
comparison classes and mathematical scope. -/
theorem generatedSourceResponse
    (d : MinimalCarrier.OrthogonalChangeDatum) (h : MinimalCarrier.IsMinimal d)
    (o : OrientationOnCarrier d) (μ : ℝ → Measure (TraceLieSpace d h))
    (hμ : HilbertCompositionalAxioms μ) (b : ℝ) (hb : 0 < b) :
    Geometry.GeneratedSourceGeometry.Conclusions d h o μ b hb ∧ Conclusions b hb :=
  ⟨Geometry.GeneratedSourceGeometry.generatedSourceGeometry d h o μ b hb hμ,
    source_internalResponse hb⟩

/-- Each supplied chiral realization is arbitrary before its least faithful
condition is imposed. One unitary transports both labelled algebra actions. -/
theorem least_chiral_pair
    {HL HR : Type*} [NormedAddCommGroup HL] [InnerProductSpace ℂ HL]
    [NormedAddCommGroup HR] [InnerProductSpace ℂ HR]
    [FiniteDimensional ℂ HL] [FiniteDimensional ℂ HR]
    (ρL : JointEnd →ₐ[ℂ] Module.End ℂ HL) (ρR : JointEnd →ₐ[ℂ] Module.End ℂ HR)
    (hL : IsLeastFaithfulRepresentation ρL) (hR : IsLeastFaithfulRepresentation ρR) :
    Module.finrank ℂ (SourceMinimalChiralPair.Carrier HL HR) = 16 ∧
      ∃ U : SourceMinimalChiralPair.Carrier HL HR ≃ₗᵢ[ℂ] FullMatter,
        (∀ A B x, U (SourceMinimalChiralPair.diagonalBlocks (ρL A) (ρR B) x) =
          diagonalBlocks (sourceCarrierRepresentation A) (sourceCarrierRepresentation B) (U x)) ∧
        (∀ x, U (SourceMinimalChiralPair.leftProjection x) = leftProjection (U x)) ∧
        (∀ x, U (SourceMinimalChiralPair.rightProjection x) = rightProjection (U x)) ∧
        (∀ x, U (SourceMinimalChiralPair.grading x) = grading (U x)) :=
  SourceMinimalChiralPair.least_pair_sourceInterface ρL ρR hL hR

end GeneratedFoundations.Physical.SourceInternalResponse

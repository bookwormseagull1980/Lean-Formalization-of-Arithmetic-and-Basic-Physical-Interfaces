# Arithmetic and physical branches of the same generated source

The two branches start from the same object, not from two isomorphic inputs.
`Source.CommonSource.generated` uses `Source.CanonicalRoot.generated` and
accepts no arguments. It constructs the compositional Gaussian law, its
coordinate density, the squared state density, the oscillator ground density,
the state correlation and the natural correlation window. Unit covariance
fixes the dimensionless width; orientation is the original source orientation.

The public dependency direction is

```text
Source.CanonicalRoot.generated
              |
Source.CommonSource.generated
              |
      +-------+-----------------------------+
      |                                     |
MathematicalInterface.generated     PhysicalInterface
      |                                     |
ArithmeticFoundation               SourcePhysicalInterface.generatedCore
      +------------------+------------------+
                         |
            CommonFoundation.generated
                         |
          CanonicalClosedWorld.generated
```

The mathematical entry imports no module in `Physical`. Shared Gaussian,
operation-algebra and differential-geometric results remain in the common
library. The arithmetic response constructions instantiate that library on
actual generated histories, phase fibres, modes and occupations.

## What is being compared

Three forms of correspondence occur.

1. **Shared construction.** Both branches use the identical source law,
   differential operator or theorem. A second copy of its proof is unnecessary.
2. **Concrete arithmetic instance.** The method is shared, but the carrier is
   the generated history or history--phase fibre. Its probability, action,
   operator and observables are constructed on that carrier.
3. **Different output.** For example, the reaction kernel is leaf charge,
   whereas an exchange generator has constants in its kernel. Physical carrier
   dimensions and response constants do not prescribe arithmetic dimensions
   or cutoff levels.

The numbered feature table below organizes the implementation. The separate
declaration inventory compares every physical declaration by its actual
objects, type and scope. It distinguishes a proved arithmetic analogue from
an identical shared result and from a physical-specific output. Completion
of this comparison does not assert that the two branches have equal dimensions,
equal stationary points or identical operators.

## A. Common source and canonical entry

| Item | Mathematical construction and actual proof | Comparison and scope |
|---|---|---|
| A1 Minimal carrier | `Source.CanonicalRoot.generated`; `CommonSource.generated.minimal` | The same canonical minimal carrier in both branches. |
| A2 Orientation and original flow | `Source.CanonicalRealization.orientation`; original rotation and trace coordinate | Orientation is internally fixed; reversal is a comparison of presentations. |
| A3 Compositional law | `CommonSource.generated.compositional`, `.unique_law` | Uniqueness is in the declared compositional covariance and scaling class, at positive times. |
| A4 State, ground state and correlation | `CommonSource.same_source_window`; `Correlation.GeneratedSourceGround.coordinate_density` | Profile, squared state and squared oscillator ground state are densities at times `b²`, `b²/4`, `b²/2`. They are not identified at a single time. |
| A5 Natural endpoints | `CommonSource.generated.natural_endpoints`, `.positive_window` | Same UV/IR endpoints, with unit-covariance width. |
| A6 Reflection window | `Arithmetic.GeneratedFoundation.minimalChange_sourceClosure`; closed Neumann domain | Boundary closure and operator domain are included in the existing source construction. |
| A7 Scale coordinates | `Spectral.NeumannScaleTransport.domainEquiv`, `.normalized_operator_intertwining`, `.heat_intertwining` | Transport includes domains and the required change of heat time. |
| A8 Root entry | `CommonSource.generated`; `MathematicalInterface.generated` | Both the common source and mathematical interface are zero-argument theorems. Observation indices occur inside their conclusions. |

`Correlation.GeneratedSourceGround` extracts the genuinely shared ground
density comparison from the physical-origin module. The former physical
declarations retain their names and types as wrappers around this common
proof. Thus the mathematical branch does not import a physical spin theorem
merely to identify the Gaussian ground density.

## B. Operations and finite response

| Item | Mathematical construction and actual proof | Comparison and scope |
|---|---|---|
| B1 Differential operations | `Operations.HermiteSource`; `SourceFiniteCornerAlgebra.sourceAnnihilator_differential`, `.sourceCreator_differential` | Actual Gaussian differential operations, shared before branching. |
| B2 Ladders and finite corners | `SourceFiniteCornerAlgebra.adjoin_sourceAnnihilator_eq_top` | The finite corner is generated by the compressed source operations. |
| B3 Hermite and Neumann systems | Complete Hermite system; `Spectral.neumannSpectrum_eq_range`; `NeumannScaleTransport`; `Geometry.SourceSpinIdentification.sourceUnitary_matrix`, `.spinAction_flow_original` | The original ordered two-mode Gaussian carrier has an explicit unitary Haar realization preserving all matrix responses and number flow. The separate Neumann system retains its own generator and spectrum. |
| B4 Actual finite algebra | `Arithmetic.HistoryMatrixAlgebra.representation`, `.faithful`, `.full`; `Geometry.SourceQuadraticResponse.responseAlgebra_eq_top`; `Geometry.SourceJointResponse.responseAlgebra_eq_top` | Every matrix acts on the full history--phase coefficient space. The original quadratic and independent tensor-source algebras have explicit matrix-unit generation proofs in the common layer. |
| B5 Central character | `Arithmetic.GeneratedPrimeParity.modeCentre_mul`, `.modeCentre_unique`; `HistoryObservation` reflection projectors | Prime-occupation parity and history reflection are separately identified actions, not assumed identical. |
| B6 Complete observation | `HistoryMatrixAlgebra.coefficient`, `.tomography`; `HistoryHaarResponse.fullAction_adjoint`, `.complete_response_invariant`; shared `SourceCoherentObservations` | Full matrix coefficients are reconstructible. The explicit Gaussian--Haar equivalence transports the complete adjoint and all sesquilinear responses, including cross-label and cross-sector entries. |
| B7 Concrete Gibbs reference | `HistoryGibbsResponse.partition_eq_root`, `.conditional_weight`; `HistoryPhaseResponse.partition_eq_root`, `.conditional_weight` | The reference is the actual positive Gaussian intensity on histories or complete history--phase fibres. |
| B8 Connected Hessian | Both concrete response modules' `.full_hessian`, `.hessian_kernel`, `.response_rank` | Full Hermitian perturbations are retained. The scalar kernel and traceless positivity follow from the shared Gibbs theorem. |

For diagonal history observations, `HistoryGibbsResponse.hessian_covariance`
identifies the connected Hessian with covariance under the actual persistent
history law. `orientation_hessian` specializes this identity to the actual
reflection-odd orientation observable, whose mean is proved to vanish.

`Geometry.SourceSpinIdentification` contains the explicit ordered polynomial
map from the original Gaussian vacuum/first-excitation pair to the degree-one
Haar carrier. Its metric is computed by integrating the actual source orbit.
The same unitary transports every complex source matrix, the number operator
and its flow. `Correlation.SourceOrigin.common_source_spin` connects this
carrier identification with the original Gaussian densities and endpoint
radius at the same positive width. Both branches use these common proofs.

`HistoryHaarResponse` applies that ordered identification at every actual
history--phase label in both source sectors. Its derived dimension is four
times the actual label count. The full coefficient algebra is conjugated as
one algebra; arbitrary cross-label matrices, independent even responses and
odd connectors are all intertwined. The original two sectors and every
arithmetic label are reconstructed by the inverse unitary.

## C. Complete carriers, phase frames and quotients

| Item | Mathematical construction and actual proof | Comparison and scope |
|---|---|---|
| C1 Complete carrier | `CompleteNaturalObject.CompleteFiber`; `HistoryRootSectors.native_space_dimension`, `.native_intertwining` | Root evaluation retains the complete ordered history and finite phase kernel; simultaneous root sectors have explicit full coefficient transport. |
| C2 Central sectors | `HistoryCentralSectors.sector_energy`, `.matrix_odd_iff`; `HistoryComplexConnector.sectorCoordinates_connector`; `HistoryEvenResponse.sectorCoordinates_matrix`; shared `SourceCliffordSectors.primitiveCentral_iff` | Occupation projections reconstruct the complete arithmetic carrier. Source-sector inclusions are orthogonal, arbitrary complex connectors act between them, and the independent even actions retain their full covariance. Occupation parity, source chirality and history reflection remain distinct actions. |
| C3 Kernel and quotient | `HistoryPhaseExactSequence.invariant_complete_quotient_exact`, `.quotientRetained`, `.full_reconstruction`, `.descend_existsUnique` | The invariant inclusion and actual quotient are exact. The quotient is canonically the zero-average detail space; its dimensions and universal property follow from the actual fibre. |
| C4 Characters | `CompleteNaturalObject.phaseKernelEquiv`; `HistoryPhaseAction.matrix_action`, `.matrix_trace`; `GeneratedPrimeParity` | Actual phase translations act faithfully and unitarily, with an explicit permutation matrix and exact regular character. Native occupation parity remains a separate action. |
| C5 Faithfulness and least realizations | `HistoryModuleRepresentation.least_iff`, `.least_unique`, `.coefficient_commutant`; `HistoryRootSectors.native_least_iff`, `.least_iff_coordinates`, `.native_least_unitarilyEquivalent`; `HistorySourceNaturality.natural_iff_existsUnique_source`, `.natural_reversal_iff_unique_quaternion` | Matrix-unit multiplicities determine the actual least dimension. Full history naturality forces an arbitrary matrix to be a unique source lift; the original reversal then determines its unique doublet or quaternion. Least-realization equivalence retains the stated freedom in the intertwiner. |
| C6 Frame transitions | `HistoryPhaseFrames.transition_unique`, `.components_transition`, `.frameMatrix_existsUnique`; shared `Geometry.HermitianFrames` | Native frames have exact inverse and passive transitions. Every unitary matrix of the actual fibre size has a unique realization on that fibre. General chart comparisons remain upstream with their stated hypotheses. |
| C7 Concrete bundle and law | `HistoryPhaseBundle.Total`, `.probability_unique`; `HistoryPhaseFrames.gaugeAction_inverse`, `.gaugeAction_projection`, `.gaugeAction_norm` | The phase law and root-indexed coefficient bundle are constructed internally. Phase fields act on these actual varying fibres, preserving their base and norm. |
| C8 Effective action and retained part | `HistoryPhaseAction.matrix_kernel`; `HistoryPhaseExactSequence.quotientRetained_apply`; `HistoryPhaseBundle.energy_decomposition` | The phase group action has trivial kernel. The observation quotient is a different construction: it retains the complete zero-average residual and its energy. |

The phase transport here is flat: relative translations satisfy the cocycle
identity exactly. A nonzero curvature cannot be inferred merely from the
presence of frames. The common source geometry below supplies its own actual
covariant derivatives and curvature calculations.

`HistoryElementaryConnector` now starts with an arbitrary complete matrix on
the actual history--phase carrier and both source sectors. Full history
naturality, self-adjointness and oddness force its unique off-diagonal complex
block. The original source reversal further selects one unique doublet. The
classification therefore derives the connector form rather than assuming it.
Its Hermite and Haar actions preserve every matrix element and the complete
sesquilinear observation.

The two independent source frames have an actual matrix action on this
carrier. Connector covariance is proved before passage to local doublet
coordinates. Complete-operator gluing and doublet gluing are equivalent;
compatible state sections remain compatible after applying the connector.
History-indexed frame fields, their canonical identity frame and their exact
transition cocycle give a concrete realization of these local comparison
theorems. The physical weight-three phase action and sixth-root quotient are
not inserted into the arithmetic frame action.

`HistoryEffectiveFrames` computes the kernel of the actual independent source
frame action on complete response operators. It is exactly the simultaneous
sign, a central subgroup of order two. The resulting quotient acts faithfully
on every full matrix, and its action-compatible identification with the
generated operator image is unique. Product lifts need only have defects in
this calculated kernel for their effective transitions to satisfy a cocycle.
Changing those lifts by the kernel preserves the transitions and defects.

The complete state representation has a different kernel: it is trivial.
The simultaneous sign acts on states as minus identity, and this state action
does not descend through the response quotient. Both statements are proved
on the actual history--phase carrier. Full sesquilinear observations, all
matrix cross terms and inner products of compatible state sections are
preserved. The physical six-element kernel and its charge assignments are
not substituted for this arithmetic calculation.

`HistoryEffectiveResponseSpace` retains every pair of matrix indices in one
Hilbert space. Its inner product is exactly the previously constructed trace
pairing. Complete conjugation therefore determines a faithful unitary
representation of the effective source group, with proved inverse, adjoint,
norm preservation and uniqueness in the stated representative-compatible
class. This does not identify the response carrier with the original state
carrier, whose central sign remains visible.

`Geometry.SourceScalarResponse` contains the common source reversal and
elementary classification. `Geometry.SourceExchangeResponse` constructs the
normalized orthogonal exchange of the actual tensor source, transports every
endomorphism and its adjoint, and proves equivalence of both full naturality
and elementary classification before and after that exchange. The old
physical names export these same upstream constants. Their compatibility is
checked together with the common and arithmetic modules in the final
whole-library verification, rather than inferred from the source comparison.

`Operations.MatrixModuleClassification` and `MatrixBlockRepresentations`
contain the general matrix-unit proofs formerly located in the physical
directory. The physical names remain compatibility exports of those same
upstream constants. `HistoryModuleRepresentation` applies the classification
to the complete fibre at root `n+1`: its least dimension is exactly
`card (History (n+1)) * (n+1)`. The commutant of its full coefficient action
consists precisely of scalars. `HistoryRootSectors` then retains all roots
`1,...,N+1` simultaneously. Its actual coefficient space has dimension the sum
of those fibre sizes, with an algebra equivalence and a unitary intertwiner
to finite matrix-block coordinates. This is the root-preserving algebra;
cross-root operations belong to a larger algebra and are not removed by this
classification. Its actual root identities act as self-adjoint, pairwise
orthogonal idempotents summing to the identity on the native space; they
reconstruct every retained state exactly. The least-dimension criterion is
equivalent to universal comparison against all faithful finite-dimensional
realizations; its native and matrix-coordinate forms agree. Every least
adjoint-compatible realization has a unitary intertwiner directly to the
native coefficient carrier. Comparison representations are quantified within
the theorems; they are not source inputs to the zero-argument entry.

The reversal-real equation, its source quaternion classification, the source
Clifford operators and the real even-algebra decomposition now belong to the
common operation library. Their former physical names are exact compatibility
exports. The real even algebra is computed from products of the actual source
generators; its two primitive central projections are classified against all
idempotents of that algebra.

`HistorySourceNaturality` tests commutation on an arbitrary matrix on the
complete history--phase factor tensored with the two-mode source. The matrix
units force zero off-diagonal history blocks and equal source blocks. Thus
tensor factorization and its uniqueness are conclusions of the actual
commutation equations. Applying the original source reversal pointwise gives
a unique complex doublet, equivalently a unique quaternion amplitude. The
resulting real response subspace has derived dimension four. Its constructed
family satisfies naturality and reversal compatibility, and its action agrees
with both the Gaussian sector operator and the Haar response. The full
arithmetic carrier still has its own history-dependent dimension.

`HistoryReversalIsometry` proves the antiunitary inner-product law on every
retained label and on both complete source sectors. Its square is minus the
identity, its inverse is its negative, and the Gaussian--Haar unitary
intertwines it with the original source reversal label by label. Independent
left and right source frames and the complete elementary connector commute
with it. The actual Gaussian multiplication and prime-occupation grading
also commute with it: source reversal does not flip arithmetic parity.
Uniqueness fixes the actual source-coordinate formula among all
antiunitaries of this complete finite carrier. The common source-frame
transport theorems remain in `Geometry.SourceReversalIsometry`, with exact
physical compatibility exports and no cross-branch dependency.

`HistoryChiralBlocks` allows arbitrary endomorphisms on the complete left
and right history--phase sectors, including cross-history coefficients.
Its multiplication and adjoint laws identify the actual source projections,
grading and exchange. The uniform two-mode source response is a proved
subfamily of this complete block calculus.

`HistoryCentralSectors` uses the prime-occupation character of each actual
positive root and retains every history and phase. Its unitary sector
coordinates intertwine the full operator, including all cross-sector entries.
The grading equations characterize even and odd matrices coefficient by
coefficient. Its Gaussian semigroup preserves each sector. Ordered-history
reflection preserves the root and commutes with this occupation character;
it is not an occupation-flipping exchange.

`HistoryCliffordAction` constructs the common source response on these actual
arithmetic labels. The source chirality acts on its derived four-component
response coordinate, while arithmetic occupation acts on the retained root
coordinate. A source-odd connector exchanges the former sectors and preserves
the latter. The source-sector coordinates are unitary, and the full matrix
action is faithfully realized in the original Gaussian/Hermite space at the
internally generated width. Reindexing and the corner-entry inverse retain
every matrix coefficient. This finite response realization does not identify
its selected Hermite corner with the whole Gaussian Hilbert space.

`SourceComplexAmplitude` derives the complete complex two-mode response from
the source real form. `SourceCliffordComplex` computes the resulting complex
even algebra as two full matrix blocks. `HistoryComplexConnector` realizes an
arbitrary complex response and its adjoint on the actual history multiplicity.
Its positive and negative inclusions are isometric, orthogonal and reconstruct
every state. `HistoryEvenResponse` acts independently on the two source
sectors and proves the full connector congruence, including its faithful
return to the original Gaussian realization.

`HistoryPhaseExactSequence` uses the actual phase average on real observations.
If the history count at root `n+1` is `H`, the invariant subspace, complete
space and quotient have dimensions `H`, `H*(n+1)` and `H*n`, respectively.
The quotient representative is the original observation minus its phase
average. This is an exact sequence of the generated observation spaces,
not a transfer of the physical neutral-line or charged-matter dimensions.

`HistoryPhaseFrames` constructs the corresponding unitary frame action on the
dependent bundle over positive roots. Native transitions are uniquely fixed
by their action on all states. The common `Geometry.HermitianFrames` theorem
also realizes every unitary matrix on the actual fibre, with its derived
dimension. Simultaneously conjugating a response and transporting its input
states preserves the complete sesquilinear observation. This comparison does
not replace the varying arithmetic bundle by the physical trivial bundle.

`HistoryRelativeCharge` computes the trace of the actual relative operator
`a*projection + b*residual` as `H*(a+n*b)`. Primitive trace-free integer
competitors are therefore `(-n,1)` and its negative. The positive detail
orientation selects one response uniquely. Its actions on both actual
subspaces and its native phase covariance are proved. At root one the detail
space is zero; that case is retained in the formulas without assigning it a
faithful two-sector interpretation. This is the arithmetic relative response,
not an assertion that the physical charge lattice has those numerical weights.

## D. Differential systems and complete domains

| Item | Mathematical construction and actual proof | Comparison and scope |
|---|---|---|
| D1 Inner product and measure | Original trace-line Gaussian measure; Haar field inner products; `HistoryObservation.pairing`; `HistoryPhaseBundle.mean` | Each response uses its actual measure. A finite fibre mean is not substituted for the Haar field norm. |
| D2 Connection | `HistoryGaussianConnection.transportMatrix_eq_gaussian`, `.transport_hasDerivAt`, `.connection_unique`; `HistoryGaugeJets.covariantComponent_transform` | The actual finite Gaussian transport fixes its scale connection. Coefficient-coordinate matter jets separately satisfy the nonlinear frame law. |
| D3 Curvature | `HistoryGaussianConnection.connection_curvature_zero`; `HistoryGaugeJets.curvature_transform`, `.bianchi`; `ConnectionJetAlgebra.curvature_add` | One-dimensional scale transport is flat. Full operator jets have computed noncommutative curvature, its exact transformation, the cyclic identity and all mixed addition terms. |
| D4 Scalar operator | `Spectral.neumannSpectrum_eq_range`, `.neumannResolvent_existsUnique`; `NeumannHeatSemigroup.rightGenerator_domain_iff` | The operator, compact resolvent and exact heat-generator domain belong to the full interval Hilbert space. |
| D5 One-form system | Shared `SourceOneFormSystem`; `HistoryReactionComplex.unique_primitive`; `HistoryReactionHodge.complete_hodge`, `.pythagoras` | The shared Haar complex is complete. The separate finite history complex has a weighted adjoint, a unique anchored primitive and an orthogonal leaf-charge/coexact decomposition. |
| D6 Graded Dirac system | Shared `SourceSpinorSystem`; `HistoryReactionComplex.dirac_symmetric`, `.dirac_square`, `.dirac_odd` | The continuous spinor domain is shared. The actual finite history operator is symmetric and odd; its square contains the previously derived full reaction Hessian. |
| D7 Tensor constraints | `Geometry.SourceTensorTTSystem.generated` | Shared actual tensor Haar space, weak TT constraints and closed rough operator. |
| D8 Completeness | The three shared system interfaces; complete Neumann and Hermite constructions; `HistoryHaarJointHessian.operator_unique`, `.domain_iff` | The complete arithmetic Haar field--state Hessian has its full eigenbasis, exact domain and unique self-adjoint closure. |

These shared source systems are themselves mathematical constructions. Their
reuse by the arithmetic entry does not import a physical branch conclusion.
They also do not identify arithmetic addition with an Einstein equation or
multiplication with a Yang--Mills connection.

The source determinant-line transport and Hermitian geometry are also common
constructions. `Operations.SourceVacuumTransport` constructs the normalized
alternating tensor of the actual two Gaussian modes, proves its line has
dimension one, and computes its tensor action. The determinant twist is
retained on the whole unitary source; the constructed intertwiner is unique
up to a unit phase on the stated special-unitary action. In
`Geometry.SourceHermitianReadout` the Hermitian part of the same matrix algebra
has explicit real coordinates and determinant form. `SourceLorentzCarrier`
proves that its future cone is precisely the positive-semidefinite cone,
including the degenerate boundary, and proves its congruence invariants.
The former physical names export these identical upstream constructions.

## E. Common action and its full variations

| Item | Mathematical construction and actual proof | Comparison and scope |
|---|---|---|
| E1 Same-source response | `HistoryGibbsResponse.response`; `HistoryPhaseResponse.response` | Both are log-partition responses of the proved source probabilities. |
| E2 Common action | `HistoryReactionForm.action`, `.conductance_from_children`; `HistoryHaarCoupledAction.action`, `.action_ray` | Complete reaction channels enter their form. The separate nonlinear Haar connection--state action retains differential, cubic, quartic and state-coupling contributions. |
| E3 First variation | `HistoryReactionForm.action_line_hasDerivAt`, `.action_line_deriv` | Exact derivative of the actual finite action along every perturbation. |
| E4 Mixed Hessian | `.full_mixed_expansion`, `.action_mixed_variation`; concrete Gibbs Hessians; `HistoryHaarCoupledAction.action_mixed_secondDeriv_zero` | Reaction cross terms are retained. Vanishing of the Haar/state vacuum mixed block is obtained by differentiating the actual nonlinear action. |
| E5 Equilibrium and restoring form | `HistoryReactionKernel`; `HistoryCentrePotential.equilibrium_unique`; `HistoryHaarJointHessian.gapSq_lower`, `.gap_attained` | Reaction leaf charge, zero centre equilibrium and positive complete Haar/state Hessian bottom are distinct calculated outputs. |
| E6 Actual operator | `HistoryReactionOperator.mixed_hessian_operator`; `HistoryHaarJointCore.finiteOperator_eq_differentialCore`; `HistoryHaarJointHessian.action_secondDeriv` | Each actual action is connected to its own operator before taking its closure or evolution. |
| E7 Retained reduction | `HistoryPhaseBundle.energy_decomposition`; `HistoryResponseReduction.schur_identity`, `.residual_energy_le` | Phase projection and full Hermitian-Hessian Schur reduction retain their complements. All matrix directions, including off-diagonal entries, remain in the latter form. |
| E8 Nonlinear/history covariance | `HistoryReactionCovariance.form_covariant`, `.action_covariant`, `.mixed_hessian_covariant` | Reflection reindexes actual complete reactions and preserves the entire action. |

The reaction differential is `f(parent)-f(left)-f(right)`. It is not an
ordinary graph differential between two species. In particular constants are
not generally stationary. `HistoryReactionKernel` derives the nullspace from
the actual assembly relations instead of importing the kernel of a graph
Laplacian.

For the finite reaction complex, the recursive primitive fixes the unit-leaf
value and is not an orthogonal projection. `HistoryReactionHodge` constructs
the orthogonal projection separately: the leaf-charge coefficient is its
inner product with the state divided by the squared leaf-charge norm. The
remaining state is in the range of the actual Gaussian-weighted adjoint. Its
coexact potential is computed using the primitives of individual assembly
basis vectors and their actual conductances. Adjoint injectivity proves
uniqueness. The degree-one harmonic kernel is zero.

The matrix-response reduction uses the actual connected Gibbs Hessian, rather
than the raw coefficient pairing. Writing this form as `B`, its residual along
an observation direction `J` is `K - B(K,J)/B(J,J) * J`. The exact identity is
`B(K,K) = B(residual,residual) + B(K,J)^2/B(J,J)`. If `B(J,J)=0`, the proved
scalar kernel gives `B(K,J)=0`. A nonzero denominator is needed only for
uniqueness of the coefficient.

## F. Evolution, conservation and occupation

| Item | Mathematical construction and actual proof | Comparison and scope |
|---|---|---|
| F1 Actual rates | `CompleteHistoryDynamics.mergeRate_pos`, `.mergeRate_unique` | The merge rate is selected by the actual Gaussian intensities and unit reverse rate. |
| F2 Detailed balance | `.edge_detailed_balance`; `HistoryReactionForm.conductance_from_children` | The full finite form sums the actual detailed-balance conductances. |
| F3 Generator | `HistoryReactionHilbert.operator_selfAdjoint`; `HistoryHaarJointHessian.operator_unique`, `.domain_iff` | The complete reaction operator is a bounded norm-convergent sum. The complete Haar/state operator has its independently proved unbounded domain and unique self-adjoint closure. |
| F4 Evolution | `HistoryReactionHilbertFlow.flow_add`, `.flow_hasDerivAt`; `HistoryHaarJointFlow.flow_continuous`, `.rightGenerator_iff` | Each flow uses its own actual operator. The joint field/state flow preserves its domain and has the exact right-generator characterization. |
| F5 Conservation | `HistoryReactionOperator.leafCharge_conservation`; `HistoryReactionFlow.charge_preserved`; existing capacity/window reconstruction | Conservation follows from the actual incidence kernel. Window complements and birth terms stay in their original ledgers. |
| F6 Energy and dissipation | `HistoryReactionHilbertFlow.energy_hasDerivAt`, `.action_hasDerivAt`; `HistoryReactionSpectralEdge.no_uniform_exponential_action`; `HistoryHaarJointFlow.flow_uniform_decay` | Complete reaction energy and action are nonincreasing but have no positive uniform exponential action rate on the stated carrier. The separate complete Haar/state Hessian flow has norm decay `exp(-15*t/8)` uniformly in cutoff. |
| F7 Occupation lift | `OccupationResponse.particleNumber_composition`, `.energy_groundOccupation`; `HistoryHaarJointFock.generated` | Native prime whole-root energy retains its joint product term. Occupations of the separate joint-Hessian eigenbasis have their own additive energy, unique vacuum and attained gap. |
| F8 Finite/full scope | `HistoryReactionHilbert.finite_form_tendsto`; `HistoryReactionHilbertFlow.cutoff_evolution_tendsto` | The full history operator and its fixed-time evolution are actual operator-norm limits of the embedded finite root layers. This retains the original finite quadratic forms and all their cross terms. |

The occupation output has the same scope as the physical finite-occupation
heat-weight interface: a semigroup of weights, a fixed vacuum and damping of
every nonvacuum occupation. It does not add an unproved interacting measure
or identify two different occupation Hamiltonians.

## G. Capacity, observations and audit

| Item | Mathematical construction and actual proof | Comparison and scope |
|---|---|---|
| G1 Effective rank | `HistoryGibbsResponse.response_rank`; `HistoryGaussianCovariance.componentCount_eq`, `.componentVariance_unique` | Actual carrier rank and complete traceless coefficient count fix the isotropic variance. |
| G2 Fluctuation/response | `HistoryCentralResponse`; `HistoryCentreNormalization.normalizedForce_hasDerivAt`, `.responseToConstant_intertwines` | Bias, variance, normalized force and evolution use the same actual centre response; its normalized isometry is unique in its proved comparison class. |
| G3 Windows and tails | `GaussianWindowCapacity.window_partition`, `.signed_reconstruction`; `HistoryGaussianWindowResponse.coefficient_pos`, `.existsUnique_responseRoot` | Visible and outside Gaussian weights remain in their ledgers. The actual observed joint-Hessian spectrum gives a positive finite-window coefficient and unique algebraic response root. |
| G4 Internal choices | `HistoryPhaseBundle.probability_unique`; `HistoryFrontier.scheduledPeak_eq_registerNumber` | The phase law and deterministic evaluation order are internally characterized. Physical `R=5` is not made into an arithmetic selection theorem. |
| G5 Certificate interface | `HistoryGaussianWindowResponse.consume_interval`; `HistoryResponseCertificates.consume_gap_interval`; exact finite tail bounds | Interval consumption is proved for the actual mathematical quantities. Interval premises and finite-data bounds remain explicit. |
| G6 Normalization | `CommonSource.generated.normalized_width`; `HistoryResponseCertificates.gapMass_unique`, `.gapMass_bounds` | Width and dimensionless Hessian mass normalization are fixed internally. Physical Newton calibration remains in its own interface. |
| G7 Reconstruction | `HistoryMatrixAlgebra.tomography`; `HistoryPhaseBundle.retained_residual_decomposition`; window signed reconstruction | Full coefficients and retained complements recover the original observations before taking bounds. |
| G8 Public entry | `MathematicalInterface.generated`; shared source field in both branch interfaces | Source-level dependency checks are separate from compilation and transitive axiom checks. |

## Declaration inventory and verification

`verification/branch-alignment-features.json` contains the 56 feature records.
Each names actual mathematical objects, constructions, hypotheses and
reachable proof declarations. Shared constructions, arithmetic instances,
distinct outputs and partial scopes are recorded separately. A feature record
does not mark every auxiliary physical declaration as reviewed.

`scripts/branch_alignment.py` enumerates every ordinary explicitly named
declaration in every physical source module, the public physical entry and
all supporting project modules. Dependencies of implemented physical modules
outside the public entry are included too. A physical module must be assigned
explicitly; additions cannot silently inherit a completion category. The
inventory includes the exact source-file hash, the assigned method family,
candidate arithmetic modules and the declaration-specific review record.
Supporting declarations have separate records, with their exact source hash
and whether that identical Lean declaration is reachable from the mathematical
entry. Identical availability is not an automatically completed semantic
review. The feature ledger still identifies its use on the actual branch objects.

A completed review requires actual mathematical declarations, an object
comparison, a comparison type and the hypotheses/scope. Mathematical targets
must be reachable from the mathematical entry. An old source hash, a removed
declaration, an unknown status, a physical proof used as the arithmetic target,
or a completed entry without a mathematical target is rejected.

The source inventory is generated by:

```text
python -m scripts.branch_alignment --reviews verification/branch-alignment-reviews.json --feature-ledger verification/branch-alignment-features.json --output verification/branch-alignment-inventory.json
```

`--require-complete`
also rejects pending construction or pending review records, including the
supporting declarations. It does not turn
the inventory into a compiled proof certificate.

The import check is symmetric: neither branch entry nor any implemented
module in the arithmetic or physical branch may depend on the other branch,
including modules outside its public entry. The common source may depend on
neither. General analysis and
geometry remain in the common library; a directory name alone does not make
such a theorem a branch-specific construction.

The final verification uses the repository-pinned Lean toolchain, the two
independent entries and the common aggregate. The existing foundations
verifier checks the actual compiled declaration environment and its transitive
axioms. Its exact source snapshot determines the scope of a verification
record. The branch inventory never substitutes for that check.

The final verification covers all 549 local Lean modules, including the
independent entries, their common aggregate and the compatibility exports.
It checks 13,308 named declaration types and audits the transitive axioms of
24,087 project-owned compiled constants, including private declarations and
generated helpers. The 705 indexed claims belong to that same source snapshot.
The independent record is `verification/branch-alignment-verification.json`;
its preserved compiler output is `verification/branch-alignment-audit.txt`.
Source-inventory refreshes do not launch a Lean build or replace this audit.

Compatibility exports retain the physical API without duplicating its proof.
The verifier asks Lean to resolve every public name, records its actual kernel
constant, and checks that constant in the complete compiled environment.
Thus exported aliases remain visible in the declaration inventory, while the
same upstream proof is counted only once in the kernel inventory.

## Completed correspondence and distinct outputs

The current source inventory contains 91 physical modules and 2,662 explicitly
named physical declarations. All have object-and-scope comparisons: 1,452
proved arithmetic analogues, 1,120 identical shared results and 90
physical-specific results. Its 241 supporting modules contain 5,641 declarations,
each available as the identical shared declaration and individually recorded.
No declaration remains pending in this inventory. The 56-feature ledger
separately records how those results act on the actual mathematical objects.
These are source-coverage counts; compiled verification is recorded in the
independent verification manifest for the exact source snapshot.

| Functional chain | Mathematical implementation | Calculated output or retained scope |
|---|---|---|
| Chiral carrier, Clifford action and central sectors | Complete history--phase carrier, ordered Hermite/Haar coordinates, arbitrary complex connectors, even blocks and full antiunitary | All matrix coefficients are retained. Source chirality, history reflection and occupation parity are distinct actions. |
| Charges, groups and quotients | Actual rank-dependent charge lattice, joint circle action, neutral/charged reconstruction, complete source-group representation and effective response quotient | The complete state representation is faithful at positive cutoff; its operator-conjugation kernel is the simultaneous sign. Physical sixth roots do not replace these computed kernels. |
| Frames and nonlinear transport | Unique full response coordinates, compatible charts, generated Gaussian connection, complete operator jets and signed curvature contraction | Local covariance, Bianchi and full trace-action variations have their actual hypotheses. Formal jets and global closed field operators are separate constructions. |
| Coupled action and complete Hessian | Nonlinear Haar connection--homogeneous-state action, differentiated mixed blocks, complete differential core, self-adjoint closure and Euler equation | The attained Hessian bottom is min(4,c_N), uniformly at least 15/8. This action is not the Gaussian-weighted history reaction action. |
| Normalized response and covariance | Actual centre potential, unique normalized response isometry, isotropic full-basis variance and transverse Casimir sum | The closed centre equilibrium is zero. All coefficient counts use the actual arithmetic carrier. |
| Windows and certificates | Actual joint-Hessian Gaussian response integral, positive coefficient, unique algebraic response root and interval consumers | Window size and observed modes are observation variables. Physical R=5, geometric endpoint intervals and Newton calibration retain their physical selection and unit hypotheses. |

The common source, actual finite history response, quotient, matrix action,
reaction form/operator/kernel, covariance, evolution and occupation modules
are connected to the mathematical entry. Their declaration reviews retain
the exact classification classes, non-diagonal reductions, certificate
premises and limit domains. The complete reaction-history limit is
constructed by `HistoryReactionHilbert`: the coefficient space contains every
actual generated history, and each full three-leg root layer has operator norm
at most nine times its actual Gaussian root mass. Normalization of the history
law gives this bound without a history-count factor. At fixed positive Gaussian
observation coordinates the full operator is bounded and self-adjoint, and the
finite forms converge exactly to its form. `HistoryReactionHilbertFlow` proves
the full-space semigroup, evolution equation, coefficient-energy and action
dissipation, contraction factor one and operator-norm convergence of the
cutoff exponentials at fixed time. The restoring-rate comparison is settled
for this complete coefficient carrier: the positive root-layer tail gives
actual anchored unit states of positive action with arbitrarily small
action-relative dissipation. Differentiation at time zero then excludes
every positive uniform exponential action rate with prefactor one. This
statement does not classify a different constrained quotient. The established
source heat operators, occupation Hamiltonian and physical reduced operator
retain their own proved spectral properties.

The occupation comparison now includes the actual prime multiplicity, its
additive composition, the empty-occupation characterization, singleton prime
states and attainment of the arithmetic energy lower edge. The physical Fock
energy is additive; the arithmetic Gaussian energy depends on the whole
evaluated root and retains its multiplicative joint term. The two constructions
therefore have corresponding functions without being the same Hamiltonian.

The complete frame comparison also has explicit coordinates. Every unitary
on the full arithmetic fibre has its unique matrix in the generated
orthonormal basis. Its determinant gives a phase and special-unitary factor,
with precisely the root-of-unity ambiguity at that fibre's actual dimension.
The arithmetic dimension is not replaced by a physical matter multiplicity.

`HistoryResponseFrames` constructs the concrete response total space over all
retained history--phase labels. Its coordinates uniquely preserve both the
base and full response fibre. `HistoryLocalizedResponse` compares Hermitian
charts of this actual fibre: compatibility gives the unitary and quotient
cocycles, and the complete matrix gluing is equivalent to Hilbert response
gluing. The two-sign ambiguity is derived from the actual response kernel.
`HistoryReversalCharts` transports the actual full antiunitary to these
comparison charts and proves its uniqueness on compatible overlaps.

`HistoryGaussianConnection` differentiates the original root-square Gaussian
on the complete finite state fibre. Its exponential, semigroup and inverse
frame are explicit; parallelism of all transported sections fixes the
connection uniquely. This transport preserves the pulled-back fibre metric,
rather than the fixed coefficient norm. Inversion is finite-dimensional;
an infinite-dimensional bounded inverse is not inferred from it.

`HistoryGaugeJets` uses the same complete state fibre and the generated
faithful source frames. Coordinate directions are its retained arithmetic
labels. Curvature covariance follows from the full noncommutative product
rule. The Bianchi identity retains symmetric second derivatives, and the
trace quadratic form retains every operator coefficient. This construction
is distinct from the flat one-coordinate Gaussian connection. Local jet
identities do not by themselves construct a global nonlinear field operator
or prove that every formal jet has a differentiable realization.

`HistoryCurvatureVariation` varies the complete curvature action on that
finite carrier. Its exact curvature line has a quadratic commutator term,
so its trace action is quartic. The first, second and mixed derivatives are
actual real derivatives. The mixed Hessian contains both the pairing of the
two linearized curvatures and the background-curvature pairing with their
mixed commutators. Its diagonal agrees with the independently derived line
second derivative. At flat background its kernel is exactly vanishing
linearized curvature. Action, first variation and full Hessian are invariant
under simultaneous generated frame changes.

`HistoryScalarAmplitude` treats the already classified elementary connector
on every history--phase coefficient, rather than its scalar compression.
Its square is exactly the positive source-doublet intensity times identity;
its action multiplies every sesquilinear pairing by that same intensity.
The norm law has no arithmetic multiplicity factor. Thus the absence of a
uniform gap for the complete reaction flow is not a statement that every
arithmetic operator lacks a positive lower bound: these are different
operators with separately computed kernels and responses.

`HistoryHaarJointHessian` concerns a different complete operator, obtained
from the second variation of the nonlinear Haar connection--state action.
Its field component has every coclosed Haar mode and every traceless matrix
coefficient; its state component retains every generated history--phase label.
The differential core is identified before closure. The domain, uniqueness,
self-adjointness, attained spectral bottom and coercivity are proved.
`HistoryHaarJointFlow` gives its strongly continuous flow and exact domain
characterization through the right generator, with
`norm(flow t x) <= exp(-15*t/8) * norm(x)` uniformly in the finite arithmetic
cutoff. Its finite occupations have their corresponding vacuum and gap.
The zero spectral bottom of the separate history-reaction generator therefore
does not imply absence of a positive restoring scale for every mathematical
response operator.

`HistoryGaussianCovariance` derives the isotropic component variance from the
actual full traceless coefficient count. The transverse Casimir action and
its affine dependence on source intensity are computed from the same basis.
`HistoryGaussianWindowResponse` then integrates the actual joint-Hessian
eigenvalues against the Gaussian over a finite observation window. Positivity,
the unique algebraic response root and the interval-consumption theorem use
that integral itself. This arithmetic root is not identified with the physical
TT geometric radius: the two constructions retain their different spectra and
multiplicities.

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

The complete root-prefix reference is now exposed by
`Analysis.HistoryPrefixGibbsResponse`, rather than inferred from a fixed-root
conditional response. It retains every root in the prefix and all of its
history--phase fibres with the actual Gaussian intensity. The native centre,
square-free support, natural-prefix birth and maximum-prime birth are
observations in this same state. Their complete matrix Hessian, Schur
reductions and restored capacities are computed in
`HistoryPrefixMobiusResponse`, `HistoryPrefixBirthResponse` and
`HistoryPrefixPrimeStageResponse`.

`HistoryPrefixResolution` supplies the full nonlinear compensation cocycle
for the actual root-square Gaussian resolution. The exponential compensation
has no assumed sign. Independently, `HistoryPrefixResolutionResponse` proves
the complete connected-response loss ledger: its logarithmic-mean kernel
loss and re-centering square are nonnegative. At fixed observation scale L,
this gives contraction by `exp(-t/L^2)` for every full Hermitian matrix and
for the Schur response reoptimized at the new reference. The native
`C-B^2/C` is its actual Mobius/support specialization.

`HistoryPrefixBirthResolution` proves compatibility with the actual next-root
update. The birth contribution is computed from its original Gaussian mass
and the persistent old mean. Its exact joint step and finite cumulative
ledger retain that contribution, both resolution losses and every
cross-birth matrix entry. Resolution changes the Gaussian observation;
birth changes the finite root prefix. Neither is substituted for the other.
These modules independently implement the same-source response, compensation
and complete-budget method used by the physical branch. They import no
physical declaration. Their subsequent targeted verification is recorded
separately from the earlier whole-library snapshot below.

The finite-displacement restoring-response correspondence is provided by
`Operations.GibbsFullResponse` and `HistoryPrefixNonlinearResponse`. The full
connected matrix Hessian is computed at every Hermitian observation and has
only the scalar kernel. For diagonal observations its gradient and all mixed
curvatures use the exact original intensities times their exponential
likelihoods. Root observations preserve the entire conditional history--phase
law. The native occupation center and the Mobius/support pair are distinct
observations of that same state; the latter has entries `s-m^2`, `m*(1-s)`
and `s*(1-s)`. Strict Mobius curvature follows from the actual unit and first
prime. The separate symmetric source-sector center in `HistoryCentrePotential`
has its own balanced mean; that value is not assigned to the root-parity
observation. The correspondence concerns the proved response mechanism and
its actual source, including finite observations and mixed directions.

The two finite-observation modules and `ArithmeticFoundation` passed the
targeted build. All 42 new public theorems passed the transitive axiom audit
with only `propext`, `Classical.choice` and `Quot.sound`. The mathematical
interface and arithmetic-root project import closures contain 452 and 462
modules respectively, with no physical import. Seventeen new indexed claims
were checked against the declarations. These checks supplement the earlier
whole-library verification snapshot without changing its source hashes.

The same finite-observation state is propagated by
`HistoryPrefixObservedResolution` and `HistoryPrefixObservedBirth`. At fixed
diagonal likelihood, the complete matrix Hessian retains its actual
logarithmic-mean resolution loss and re-centering cost. Its unnormalized
response contracts by `exp(-t/L^2)`, independently of prefix size and finite
likelihood at fixed L. Orthogonal reduction is reoptimized at the new metric
using `GibbsSchurResponse`; scalar null directions require no inverse.
Successive births retain the Gaussian newborn mass times its exact root
likelihood and the complete history--phase fibre. Mixed birth covariance,
all cross-birth matrix entries and the cumulative birth--resolution balance
are computed in that same state. This is the finite-observation counterpart
of joint response transport and complete source-exchange accounting. It does
not identify a resolution increment with a change of observation scale.

These three modules and `ArithmeticFoundation` passed the targeted build
without warnings (4511 dependency jobs). All 49 new public theorems passed
the transitive axiom audit using only `propext`, `Classical.choice` and
`Quot.sound`. The mathematical-interface and arithmetic-root project import
closures contain 455 and 465 modules, with no physical import. Thirty new
scoped index entries were checked. The exact source hashes and audit results
are recorded in `.lake/history_prefix_observed_static.json`; the earlier
whole-library verification snapshot remains unchanged.

| Item | Mathematical construction and actual proof | Comparison and scope |
|---|---|---|
| G1 Effective rank | `HistoryGibbsResponse.response_rank`; `HistoryGaussianCovariance.componentCount_eq`, `.componentVariance_unique` | Actual carrier rank and complete traceless coefficient count fix the isotropic variance. |
| G2 Fluctuation/response | `HistoryCentralResponse`; `HistoryCentreNormalization.normalizedForce_hasDerivAt`, `.responseToConstant_intertwines` | Bias, variance, normalized force and evolution use the same actual centre response; its normalized isometry is unique in its proved comparison class. |
| G3 Windows and tails | `GaussianWindowCapacity.window_partition`, `.signed_reconstruction`; `HistoryGaussianWindowResponse.coefficient_pos`, `.existsUnique_responseRoot` | Visible and outside Gaussian weights remain in their ledgers. The actual observed joint-Hessian spectrum gives a positive finite-window coefficient and unique algebraic response root. |
| G4 Internal choices | `HistoryPhaseBundle.probability_unique`; `HistoryFrontier.scheduledPeak_eq_registerNumber`; `HistoryHaarSectionEquilibrium.least_minimum_window`; `HistoryHaarSectionCapacityThreshold.integer_capacity_iff` | The phase law and evaluation order are internally characterized. The actual arithmetic spectrum selects five as the least admissible integer for the stated source-unit comparison protocol. This uses its own joint content, rather than imposing the physical three-Dirac-position condition. |
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

The preserved 20 October verification covers all 549 local Lean modules, including the
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

The current source inventory contains 98 physical modules and 2,766 explicitly
named physical declarations. All have object-and-scope comparisons: 1,555
proved arithmetic analogues, 1,120 identical shared results and 91
physical-specific results. All 15 declarations of `SourceMatterPoleResponse`
have concrete arithmetic counterparts in `HistoryPoleResponse`, including
the energy-dependent resolvent, full eigenvector reconstruction and positive
return metric. Its 242 supporting modules contain 5,657 declarations,
each available as the identical shared declaration and individually recorded.
The 56-feature ledger
separately records how those results act on the actual mathematical objects.
The declaration review is distinct from completion of a construction
function: G4 retains a partial scope because the arithmetic source has not
selected a unique observation level and observed spectral set. The existing
endpoint theorem fixes its root only after those observation choices.
These are source-coverage counts; compiled verification is recorded in the
independent verification manifest for the exact source snapshot.

| Functional chain | Mathematical implementation | Calculated output or retained scope |
|---|---|---|
| Chiral carrier, Clifford action and central sectors | Complete history--phase carrier, ordered Hermite/Haar coordinates, arbitrary complex connectors, even blocks and full antiunitary | All matrix coefficients are retained. Source chirality, history reflection and occupation parity are distinct actions. |
| Charges, groups and quotients | Actual rank-dependent charge lattice, joint circle action, neutral/charged reconstruction, complete source-group representation and effective response quotient | The complete state representation is faithful at positive cutoff; its operator-conjugation kernel is the simultaneous sign. Physical sixth roots do not replace these computed kernels. |
| Frames and nonlinear transport | Unique full response coordinates, compatible charts, generated Gaussian connection, complete operator jets and signed curvature contraction | Local covariance, Bianchi and full trace-action variations have their actual hypotheses. Formal jets and global closed field operators are separate constructions. |
| Coupled action and complete Hessian | Nonlinear Haar connection--homogeneous-state action, differentiated mixed blocks, complete differential core, self-adjoint closure and Euler equation | The attained Hessian bottom is min(4,c_N), uniformly at least 15/8. This action is not the Gaussian-weighted history reaction action. |
| Normalized response and covariance | Actual centre potential, unique normalized response isometry, isotropic full-basis variance and transverse Casimir sum | The closed centre equilibrium is zero. All coefficient counts use the actual arithmetic carrier. |
| Energy-dependent response and normalization | `HistoryPoleResponse` reconstructs the complete original history--phase vector from its retained source sector | The reduced inverse and full lift use the same complementary resolvent. At real energies in its resolvent domain, the derivative equals the positive lift Gram. The actual Gaussian prefix marginal and both trace orderings are retained. |
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

## Complete source compression and nonlinear resolution

The source inventory includes the adjoint comparison, curvature susceptibility,
determinant compensation, covariant compression, phase charge and complete
resolution compensation modules. Their arithmetic implementations use the
actual history carrier and its generated coefficient counts.

`HistoryAdjointComparison` evaluates the full independent real traceless
adjoint trace, whose multiplicity is `d_N^2-1`. The one generated total
intensity is divided by that multiplicity when selecting the comparison
equilibrium. Thus the target is at most `1/15`; it is not the unchanged
scalar target repeated once per adjoint direction. Positivity and strict
monotonicity give a unique positive amplitude, strictly below the scalar
amplitude. The common comparison trace, the joint Haar-state Hessian and
the native root-parity response are separate constructed objects.

The physical correction is propagated through its radial force, mass
normalization and complete Hessian reduction: the real adjoint trace has
eight components. The arithmetic instance instead retains its computed
`d_N^2-1` components and the single total source intensity. Neither the
physical eight nor its 120 connection coefficients is substituted for an
arithmetic count.

`HistoryIntensitySusceptibility` retains the finite contraction recurrence
at the computed arithmetic coefficient count `M_N`. Its normalized fourth
contraction is `3+12/M_N`. It also completes the partial Legendre Hessian
square, including its negative source block and the collective inverse-
curvature response. Positivity of the generated comparison restoring
coefficient follows from that comparison, not an assumed restoring rate.
The finite contraction identities do not replace an analytic integration
theorem for a source measure.

`Operations.CovariantCompression` proves exact reconstruction, uniqueness,
orthogonality and the complete Gram identity for rectangular moving
readouts. The original connection and moving readout have both interference
terms, and transform together under passive frame changes.
`HistoryCovariantCompression` supplies the actual phase-average projector,
its self-adjointness, its full detail complement and commutation with every
original source operation and connector. Operations supported on the detail
space annihilate the invariant space on both sides. This phase projector
does not identify arithmetic invariant histories with physical leptons.

`HistoryDeterminantCompensation` repeats the original Gaussian two-mode
source on every retained arithmetic label. Faithfulness forces the inverse
determinant as the unique correction of its determinant-line twist, and the
corrected action preserves every invertible composition. The arithmetic
instance uses the already generated unit-covariance width.
`HistoryPhaseCharge` derives commutation of the original charge with its
constructed unitary phase flow. All charge pairings are conserved before
any quotient. The common real-pair work identity separately retains both
field-equation residuals.

`HistoryFieldResolution` extends the response transport to complete
position-dependent arithmetic sections and all native matrix coefficients.
The original even coefficient heat is intertwined with the original Haar
heat. Full matrix brackets and section products are formed on continuous
representatives before Haar inclusion; the nonlinear output is not
projected back into its initial core. The unresolved response is uniquely
fixed by the complete response identity. Its cocycle yields the joint
resolution semigroup. This field-resolution construction and the native
Gaussian prefix-resolution construction retain their distinct observation
operators and their own complete compensation identities.

The physical response-level selection also retains both ingredients of its
proof. The strict spectral cutoff gives
`sqrt(11/2) < c_R` and `c_R <= sqrt(15/2)`. Selection of `R=5` additionally
uses the separate same-shell-support interval
`49/(4*pi) < R <= 16/pi`. The three-position condition alone is not a
selection theorem. Arithmetic response windows use their own generated
spectrum and multiplicities rather than importing this physical integer.
The general observation `c_(N,R,S)` remains available. The exhaustive
interface in `HistorySpectralWindow` additionally fixes
`S_N(B) = {i | eigenvalue N i < B}` and proves that this is a finite set of
the original complete basis, uniquely determined by `B`. It retains every
matrix entry and the entire active homogeneous-state block. Nonemptiness
is equivalent to `gapSq N < B`.

The first arithmetic field shell satisfies the exact statement
`4 < B <= 16`: a field label is retained exactly when its Hodge eigenvalue
is `4`; state inclusion is separately and exactly `coefficient N < B`.
The proof uses both differentiated curl branches. The upper edge is retained
because the projection uses a strict cutoff.

Position conditions are also explicit. The native square spectrum retains
positive roots `1,...,m` exactly on `m^2 < B <= (m+1)^2`; every retained root
keeps its complete history, phase and source fibre. The common positive
spinor tower is a different spectrum, with positions `2*j+3/2`. It retains
exactly `m` positions on `2*m-1/2 < B <= 2*m+3/2`. For a squared root cutoff
`B=c^2`, its three-position condition is `11/2 < c^2 <= 15/2`.

Thus support, position count and the Gaussian root are now represented
together. The finite-set choice is removed from this exhaustive interface.
The generated arithmetic content condition selecting the number of positions
and the discrete observation level is still required; `CompatibleObservation`
checks those conditions but does not assert a unique selected level. In
particular, its free position count cannot be treated as an added selection
law. No equality between the finite history-jet normalization and a complete
effective-action trace measure is inferred from this construction. The
earlier rectangular frequency observation is retained separately.
The additional source-frequency observation first decomposes the actual
Hessian coefficient as `a_i + b_i`. On field labels `a_i` is the original
Hodge eigenvalue and `b_i=0`; on homogeneous state labels `a_i=0` and `b_i`
is the defining Casimir. This decomposition follows the existing action.
The domain is `u^2+a_i<R`, its branch endpoint is `sqrt(R-a_i)`, and its
Gaussian is `exp(-(u^2+a_i))`. The numerator is `u^2+a_i`; the denominator
is `u^2+a_i+b_i`. Restoring coefficients do not enter the source cutoff.
Every positive source bandwidth retains the entire homogeneous state,
with its computed dimension `d_N`. The full-Hessian projection `support`
remains a different, correctly defined spectral observation. These are
defined spectral observations, not a proved identification
with the physical eight-branch TT response or an arithmetic variational
selection law. In particular, the response-root cutoff and the native root
positions still require a source-derived compatibility statement. Feature G4
retains this exact scope. The equation-only nonselection theorem is a
diagnostic, not the substitute for the joint selection problem.

The displayed positive spinor positions are also tied to the original
closed centre-even Dirac operator: every position is realized, and every
positive eigenvalue in that sector is one of them. This retains actual
field eigenvectors and their multiplicities. The earlier joint arithmetic
Haar action used for the response window has a homogeneous state. The
Dirac position theorem alone does not insert an inhomogeneous spinor
kinetic term into that action or determine a position-content count.


`HistoryHaarSectionAction` now constructs the position-dependent action on
all existing scalar-coefficient history sections. The connection remains
the original differentiated matrix one-form core. `SourceOneFormScalarCoordinates`
proves that its finite scalar coordinates preserve the continuous
representatives exactly. Products are evaluated before Haar inclusion,
with all history matrix entries retained.

The full action contains `norm(gradient psi + A psi)^2 / 2`. Its exact joint
ray expansion retains `Re inner(gradient psi, A psi)` as a cubic term.
At fixed section this is the actual first connection response; it need not
vanish. The mixed vacuum Hessian is still zero, as proved by differentiating
that same action. The quadratic form retains the source gradient with
coefficient one, alongside the already calculated defining Casimir.

`SourceScalarKineticForm` identifies the source gradient in the original
Haar metric. Integration by parts and the source Casimir give kinetic
coefficient `m*(m+2)` on each even source row. Thus the actual positions for
these sections are `4*j*(j+1)` (starting with `0,8,24,...`), with full
multiplicity `d_N*(2*j+1)^2`. The strict cutoff includes rows `0,...,m`
exactly when `position m < B <= position (m+1)`. Restoring coefficients are
separate from those source kinetic positions.

The new action and its derived Hessian are exposed by the independent
mathematical interface. This construction uses the already defined scalar
sections; it does not identify their dynamics with spinor matter. The
older homogeneous response is not silently relabeled as its full response
trace. The joint selection task now has explicit inhomogeneous kinetic
positions and multiplicities, but still requires the response trace and
its induced normalization, together with the generated mathematical
content/position condition. Only their joint selection can determine a
mathematical level and endpoint. No physical three-position requirement
or value `R=5` is imposed on these scalar sections. G4 retains that scope.


### The closed inhomogeneous joint Hessian and its exhaustive source window

`SourceScalarKineticOperator` calculates all cross-row gradient pairings
in the original Haar metric. Its Green identity holds for arbitrary finite
scalar coefficients and identifies the actual differentiated form with the
original closed scalar Casimir, including its original operator domain.
It does not infer this identification solely from diagonal basis norms.

`HistoryHaarSectionHessian` applies that result to every history--phase
coordinate. Its finite operator pairing equals the full kinetic plus
restoring form of `HistoryHaarSectionAction`. The closure is self-adjoint,
its extension from that finite core is unique, and its domain is exactly
the weighted square-summability condition for the complete original basis.
The lower edge `coefficient N` is attained by a constant scalar source row.

`HistoryHaarSectionJointHessian` retains both the full matrix-valued
coclosed field and all position-dependent sections. Both factors are
unbounded. Its domain is the intersection of the two actual component
domain conditions, and its operator components are proved equal to the
original differential field operator and the new closed section operator.
The real operator pairing is the actual second derivative of the same
nonlinear action on arbitrary finite fields and sections. The sharp lower
edge `min 4 (coefficient N)` is attained; it is not just an unverified
minimum of proposed branch coefficients.

`HistoryHaarSectionWindow` now enumerates the complete kinetic support of
this joint operator. Its membership theorem is exactly `a_i < B`, with
`lambda_i = a_i + b_i`. Each Gaussian branch uses numerator `u^2+a_i`,
denominator `u^2+a_i+b_i`, weight `exp(-(u^2+a_i))` and endpoint
`sqrt(B-a_i)`. In particular, a section restoring coefficient is not
silently moved into the source cutoff. Every scalar position
`a_j=4*j*(j+1)` keeps the full multiplicity `d_N*(2*j+1)^2`. The trace on
that complete row equals its actual multiplicity times the common branch
integral. All original history labels and both scalar matrix-coefficient
indices remain distinct.

These are now additional conclusions of the independent mathematical
entrypoint. No `Physical` module is imported. The older homogeneous action
and response retain their stated scope; they are not renamed as the new
inhomogeneous theory.

The finite spectral response trace is constructed here without declaring
an effective-action vertex normalization. Selection of a mathematical
observation level still requires deriving that normalization and the
mathematical content/position condition from the same action. The physical
three-position condition and `R=5` are not inputs to this scalar-section
construction. G4 therefore retains `partial_scope`: completing the
operator and exhaustive trace portions does not itself select a unique
mathematical `R` or `kL`.

### Fixed-window comparison variation and the actual mixed shells

`ScalarPrecisionComparison` proves the exact compensated log-precision
identity, including its finite trace-minus-log-determinant form. For the
actual joint Hessian set `q_i=u^2+a_i`, `p_i=u^2+a_i+b_i` and `r_i=q_i/p_i`.
The kinetic variation has relative precision `1+z*r_i`; at zero its second
comparison derivative is exactly `r_i^2`. Positivity of the original
precision supplies a common parameter neighborhood. Both differentiations
under each finite interval integral are justified by uniform derivative
bounds, rather than by a truncated expansion.

`HistoryHaarSectionComparison` applies this construction to every label of
the complete support. With the original Gaussian weight, the second
derivative of the full comparison is exactly `responseTrace N B`. The
response kernel therefore has an actual variational origin on this
Hessian. The comparison value and its first derivative vanish at the
reference precision, and the second derivative is positive on a nonempty
window. The window is fixed during this variation; this statement does
not discard moving-cutoff boundary terms in a different variation.

The complete mixed support is also classified. On `4<B<=8` it retains the
first coclosed shell and the scalar degree-zero row. On `8<B<=16` it retains
that same complete coclosed shell and scalar degrees zero and two. Every
history label and both scalar coefficient coordinates remain present.
The support is constant throughout the second plateau even though its
frequency integration endpoint changes with `B`.

The physical finite-level selection combines its particular spectrum,
content/position condition and certified response crossing. The analogous
mathematical selection must likewise combine these ingredients. Neither
the new precision comparison nor its computed shell plateaus import the
physical three-position condition or the physical TT vertex coefficient.
In particular the second-variation identity is not a derivation of an
endpoint dependence proportional to `1/c`. G4 records this distinction.

### Calculated content and crossings of the complete window response

`HistoryHaarSectionContent` computes the scalar content of that same joint
window. For the strict kinetic cutoff `B`, its number of positions is
`ceil((sqrt(B+1)-1)/2)`. Thus exactly one, two or three scalar positions
occur on `(0,8]`, `(8,24]` or `(24,48]`, respectively. Every position keeps
all original history labels and both matrix-coefficient coordinates.
The finite row labels inject into the original joint eigenbasis and their
image is exactly its visible scalar sector. With `m` positions, the rank
is characterized by `3*rank+d_N*m=4*d_N*m^3`; its first values are `d_N`,
`10*d_N` and `35*d_N`.

The full scalar Gaussian sum equals the sum of its complete row integrals
with these calculated multiplicities. Adding the original connection
contribution gives exactly `responseTrace N B`, not a second observable.
The comparison curvature from the preceding section therefore retains
the same content, support and response throughout this regrouping.

The full response is strictly increasing on nonnegative bandwidths,
including at changes of support. The proof extends each original branch
by zero below its kinetic birth and enlarges its actual integration
interval. No new branch or change of integration endpoint is omitted.
Consequently a position plateau can also be characterized by crossings of
this complete response at the last retained and first excluded positions.

These results supply an exact content calculation and a common-response
crossing test. They do not set a count to three or derive a source condition
selecting a count. The physical finite-level theorem likewise consumes its
separate `ThreePosition`, `SameShellSupport` and lower-crossing conditions.
The arithmetic selection must use its own actual content and effective
variation; G4 retains `partial_scope` for that remaining selection task.

### Common coordinate transport and the joint finite-level certificate

`HistoryHaarSectionScale` transports the very same joint Hessian window.
Under a positive frequency-coordinate change `u=c*omega`, both the kinetic
and restoring squared eigenvalues scale by `c^-2`. The Gaussian exponent
and the frequency cutoff are transported together. Direct substitution in
each original interval integral proves that the complete response and
the full compensated comparison are divided by `c`. The corresponding
second comparison variation is exactly the scaled complete response.
The factor is the integration Jacobian, rather than a separate response
definition. Every source label and full row multiplicity is retained.

The transported source support and content are unchanged. In particular,
the value of the coordinate scale cannot select a bandwidth or change the
number of retained positions. Scalar Casimir positions and positive Dirac
positions also remain distinct; counting one is not a derivation of the
content of the other.

The module includes a joint integer-level certificate on this actual
response. Write `c_R=T_N(R)/q`, where `q>0` is a specified comparison level
in the certificate, and `a_m=4*m*(m+1)`. Suppose the actual position count
at `c_R^2` is `m+1`, the certified preceding value satisfies
`c_K^2<=a_m`, and an original excluded spectral label has kinetic energy
less than `K+2`. The content condition gives `R>K` by monotonicity of the
same complete response; exclusion of that actual label gives `R<K+2`.
Thus the only natural level is `R=K+1`. The proof combines the position
condition, real source-shell exclusion and lower response crossing. It
does not infer an integer level from a response equation alone.

This is a certificate-consumption theorem, with its premises visible in
the statement. The mathematical entry specializes its comparison level
to the already generated total source intensity; it accepts no comparison
normalization parameter. This fixes comparison units, rather than proving
that those units constitute the effective endpoint law. The effective
normalization and position-selection conditions remain under G4. The physical finite-level theorem has
its own stated `ThreePosition`, `SameShellSupport` and crossing premises;
they are not source parameters of the arithmetic branch. No numerical
physical `R=5`, three-position assumption or TT vertex factor is inserted
into the mathematical root. All new conclusions are assembled through the
independent mathematical interface.

### Complete differential shell table and constructed integral enclosures

`HistoryHaarSectionShells` now regroups the original complete coclosed
basis, rather than evaluating a substituted field table. At each even
source degree `m`, the two nonzero curl branches have energies `(m+2)^2`
and `m^2`, with multiplicities `(m+1)*(m+3)` and `(m+1)*(m-1)`.
These counts use the differentiated curl trace and its gradient kernel.
Every history matrix entry remains, giving the additional factor `d_N^2`.
The constant degree is included; its negative branch has zero multiplicity.
Combining both source rows at a common Hodge shell gives the initial field
multiplicities `6*d_N^2`, `30*d_N^2` and `70*d_N^2` at energies 4, 16 and 36.

The complete scalar rows retain their separate energies `4*j*(j+1)`,
multiplicities `d_N*(2*j+1)^2` and actual restoring coefficient. Adding them
to the differentiated field table gives exactly the original full
`responseTrace`. Thus shell support, position content and response bounds
refer to one joint operator and the same comparison second variation.

Finite integral bounds are constructed, not merely assumed on an unknown
coefficient. On each nonnegative frequency cell the actual resolvent
fraction increases and the actual Gaussian weight decreases. Their two
endpoint products enclose the kernel throughout that cell. Summing cell
integrals telescopes exactly, and summing all original support labels
constructs bounds on the complete response. The module supplies valid
uniform meshes for every positive finite cell count. This is an analytic
enclosure construction; certified rational evaluation of its exponential
and square-root values is a separate numerical step.

The resulting bounds feed the actual position-count and joint integer
selection theorems. The selection retains its explicit original shell
exclusion, position and crossing conditions. A particular integer level
and a source-selected effective normalization are not consequences of a
response equation or of regrouping the trace. G4 therefore retains its
stated selection scope; G5 now includes constructed enclosures for this
complete position-dependent action as well as the older homogeneous model.

### Gaussian relative entropy on the same complete spectral window

`Operations.GaussianPrecisionKL` calculates the relative entropy of actual
centred Gaussian probability measures, with variances `1/p` and `1/q`.
Their Radon--Nikodym ratio, integrable log likelihood and finite KL give
`KL = (q/p-1-log(q/p))/2` for positive precisions. Thus the existing
compensated precision cost is twice the KL of one real coordinate. A
complex-coordinate multiplicity is not silently inserted into this identity.

`HistoryHaarSectionProbability` uses every original joint spectral label
and its actual frequency interval. Its normalization is the sum of their
Gaussian integrals, strictly positive on every positive bandwidth. It is
not the number of finite connection coefficients. Averaging the actual
conditional Gaussian KL over this window gives exactly the full precision
comparison divided by twice this Gaussian mass. Its second variation is
the original complete response divided by that same factor. No original
field or scalar row is removed by this normalization.

Both the mass and the unnormalized response acquire the same `1/c`
Jacobian under the already proved common coordinate transport. Their
ratio is invariant and lies in `(0,1]` on a nonempty window. This identifies
the probability normalization; it does not identify it with a TT vertex
or make it a condition selecting the source bandwidth. In particular the
full selection comparison remains a joint one: actual spectral support,
source-derived content/position compatibility and a certified crossing
of the same variational response. Its mathematical position condition is
not replaced by the physical three-position condition or numerical `R=5`.
G4 retains its explicit selection scope. The new Gaussian and window
theorems are exported through the independent mathematical entrypoint.

### Source content, complete Gaussian shells and finite observation levels

`HistoryHaarSectionExhaustion` now proves that every original joint basis
label is visible at a finite integer bandwidth. The actual scalar positions
`4*j*(j+1)` have no largest member. Their next edges
`4*(m+1)*(m+2)` realize exactly `m+1` visible positions, for every `m`.
Thus the differentiated spectrum supplies the position count at each
bandwidth; selecting one such count is a separate content-compatibility
question. Infinitely many available positions do not by themselves exclude
a selected finite observation level. The physical three-position criterion
is likewise distinct from exhaustion of its full differential spectrum.

The complete Gaussian field and scalar row sums converge with their actual
multiplicities. Their full half-line integrals bound the original response
uniformly in observation bandwidth at each fixed history stage. The factors
`d_N^2` and `d_N` remain explicit. Splitting the original rows at an integer
`J` gives an exact retained-plus-omitted identity. The omitted response is
bounded, uniformly in bandwidth, by the tails of those same Gaussian row
series, and those tails tend to zero. The finite computation therefore has
a complete-source error certificate rather than a hard truncation of the
source. The scalar resolvent fraction is bounded by one only in this tail
estimate; the original fraction remains in the retained response and in
the joint level-selection tests.

The alignment target for finite selection remains the physical joint
method: actual shell support, source-content compatibility and a certified
crossing of the same effective response. Neither a probability normalization
nor a vanishing numerical tail selects a position count or an integer
bandwidth. The new exhaustion and error statements are assembled into
`MathematicalInterface.complete_section_exhaustion`, independently of
`Physical`. They do not change G4's source-selection status.

### Moving-window response and source-content transfer

Finite-level selection is a joint comparison. In `SourceResponseLevel`, the
physical conclusion `R=5` uses actual shell support, the three-position
condition on the endpoint root and a lower-level response crossing. The
response equation by itself does not supply the other two conditions. The
arithmetic comparison follows this same structure, using its own complete
Haar spectrum and position multiplicities.

`HistoryHaarSectionBoundary` supplies the previously missing variation of
the original window. At a regular bandwidth `B`, the complete response
`T_N(B)` and its Gaussian mass `Z_N(B)` satisfy

```
T_N'(B) = exp(-B) * sum_i (B/(B+b_i))^2 / (2*sqrt(B-a_i))
Z_N'(B) = exp(-B) * sum_i 1 / (2*sqrt(B-a_i))
```

Both sums run over the same actual support `a_i < B`. The restoring terms
`b_i`, every history matrix entry and all original multiplicities remain.
Continuity of both quantities is proved also at spectral births; the
derivative statements exclude those birth values explicitly.

For `chi=T_N/Z_N`, the normalized derivative is `exp(-B)/Z_N` times the
signed boundary balance. The connection contribution is
`F*(1-chi)`; the scalar contribution is
`S*((B/(B+c_N))^2-chi)`. These are derived from the original operator,
rather than inserted into a new response ansatz. In particular `chi<1`
is strict on every positive window, and a stationary normalized response
above the first connection shell requires the scalar edge fraction to be
strictly below the complete interior average. Stationarity itself is not
asserted to select the endpoint.

The finite identity

```
chi(C)-chi(B) =
  sum_i integral_[sqrt(B-a_i),sqrt(C-a_i)]
    exp(-(u^2+a_i))*((u^2+a_i)^2/(u^2+a_i+b_i)^2-chi(B)) du / Z_N(C)
```

holds across all births for `0<B<=C`, using all rows in the actual support
at `C`. Its two-sided response-increment bounds keep each exact Gaussian
interval mass and that row's two endpoint fractions. The lower kinetic
endpoint is `max(B,a_i)`, including a new row's actual birth value when
`B<a_i`; the upper endpoint is `C`. No number of rows is
absorbed into a purported uniform constant.

The cutoff `B`, the bandwidth-dependent visible position count and the
position condition at a calculated endpoint scale are distinct quantities.
The new identities connect the first two; applying the endpoint test still
uses the same actual response-scale relation in `HistoryHaarSectionScale`.
Neither normalized Gaussian curvature nor its stationarity is identified
with that endpoint relation without a derivation. G4 continues to record
the remaining source-selection question. The new boundary and finite
transfer theorems are exported independently of `Physical` through
`MathematicalInterface.complete_section_boundary`.

### Joint field-shell, scalar-content and Gaussian window tests

The arithmetic counterpart of physical finite-level selection is a joint
test. The field support, source content and the response must be evaluated
on the same observation. Failure of a response equation to select a level
on its own is not a substitute for this construction.

`HistoryHaarSectionRetention` now proves, on the original differentiated
joint basis, that the distinct field positions are `4*(j+1)^2`, while the
scalar positions are `4*j*(j+1)`. Every field position is attained; every
field basis label has one of these positions. The two spectra interlace:

```text
scalar(j) < field(j) < scalar(j+1).
```

Consequently the scalar-position count equals the field-shell count or
exceeds it by one. Exact joint cells include:

| Source bandwidth B | Field positions | Scalar positions |
| --- | ---: | ---: |
| 0 < B <= 4 | 0 | 1 |
| 4 < B <= 8 | 1 | 1 |
| 8 < B <= 16 | 1 | 2 |
| 16 < B <= 24 | 2 | 2 |
| 24 < B <= 36 | 2 | 3 |
| 36 < B <= 48 | 3 | 3 |

These are counts of distinct kinetic positions. Each keeps all original
polarizations and history coefficients in the trace. For example, the
equal-count cell has the exact common-response test

```text
fieldCount(B)=j+1 and scalarCount(B)=j+1
iff T_N(field(j)) < T_N(B) <= T_N(scalar(j+1)).
```

The other cell has edges `scalar(j)` and `field(j)`. Both tests use the
original complete `T_N`, including its restoring denominators and actual
Gaussian interval weights, rather than a capacity or a position-count
replacement.

The same module proves that the finite Gaussian mass increases to precisely
the complete summable row mass `fullBudget N`. Thus `Z_N(B)/fullBudget N`
is the actual retained fraction; it is strictly between zero and one on
every positive finite bandwidth, and tends to one. The joint cell can
equally be tested at its actual retained-fraction edge values. Negative
logarithmic retention records the window information transfer; it is not
identified with the separate conditional Gaussian-precision KL.

No target fraction or preferred number of positions is imposed. These
joint-cell equivalences classify admissible observations, and do not by
themselves select one cell or replace the endpoint condition at the
response-derived scale. G4 keeps that source-selected effective-vertex
and endpoint scope. The results are exported by
`MathematicalInterface.complete_section_retention`, independently of
`Physical`.


### A calculated least window for source-unit Gaussian balance

`HistoryHaarSectionSourceBalance` treats the shell, source intensity and
comparison on the same actual window. Write `d_N` for the generated history
carrier dimension and `c_N=(d_N-1/d_N)/2`. For every retained original mode,
let `r_i(u)=(u^2+a_i)/(u^2+a_i+b_i)` and use the original weight
`exp(-(u^2+a_i))`. The complete finite comparison and its force are

```text
K_N(B,z) = sum_i integral w_i [z*r_i-log(1+z*r_i)] du,
F_N(B,z) = sum_i integral w_i [r_i-r_i/(1+z*r_i)] du.
```

One total generated intensity is `I_N=1`. The source-unit comparison
potential is `K_N(B,z)-I_N*z`. The least integer window admitting a positive
stationary point of this potential is proved to be five. It is obtained
from two estimates, uniformly in the history stage:

```text
F_N(4,z) <= (8/15)*sqrt(pi) < 1       (z >= 0),
F_N(5,7) >= 56*exp(-4) > 1.
```

The first estimate uses exactly the ground scalar support, its original
multiplicity `d_N`, its restoring coefficient `c_N`, and a finite Gaussian
second moment. The second uses the original two-sign connection table:

```text
fieldResponse(N,5) = 6*d_N^2*exp(-4)*integral_0^1 exp(-u^2) du.
```

Thus the cutoff transition is evaluated from actual spectral content. The
comparison force is continuous and strictly increasing in nonnegative
amplitude, and monotone in bandwidth. Consequently a positive equilibrium
exists at an integer level `R` exactly when `5<=R`; it is unique at each such
level. The level five is the **least** admissible integer, rather than the
only admissible window. Its actual content is one connection position and
one scalar position, with all their original polarizations and history
coefficients retained.

The relative-entropy identity `KL_N(B,z)=K_N(B,z)/(2*Z_N(B))` is extended to
`z>-1/2`, including the entire positive equilibrium ray. It uses the same
Gaussian laws and full logarithm. The amplitude `z`, bandwidth `B`, and a
frequency-coordinate scale are kept distinct.

This theorem supplies a concrete source-unit comparison selection protocol.
The rule of taking the least integer window is part of that observation
protocol. It does not identify this potential with a physical TT effective
endpoint action or derive the physical three-Dirac-position condition.
G4 retains that distinction. The theorem is exported independently of
`Physical` by `MathematicalInterface.source_unit_section_balance`.

### Global variational selection on the same Gaussian window

`HistoryHaarSectionEquilibrium` proves global minimality for that same
source-unit comparison. If `p_i(z)=p_i+z*q_i`, keep the original window,
original label multiplicities and original Gaussian frequency weights.
The exact tangent remainder is

```text
K_N(B,v)-K_N(B,z)-F_N(B,z)*(v-z)
  = 2*Z_N(B)*average KL(Gaussian(p_i(z)) || Gaussian(p_i(v))).
```

This follows from the full logarithmic identity, without a small-amplitude
expansion. At a balance point `F_N(B,z)=1`, it equals
`Phi_N(B,v)-Phi_N(B,z)`. On every positive window it is positive whenever
`v!=z`, and zero for identical amplitudes. Thus the balance point is the
unique global minimum on the nonnegative ray. Through bandwidth four the
same potential is strictly decreasing, so no such minimum exists. For
integer levels, existence of a global minimum is therefore equivalent to
`R>=5`, and its least level is five.

The canonical amplitude `z_N` at level five is proved to satisfy
`0<z_N<7`. Both directions of the conditional Gaussian KL are positive and
obey the exact identity

```text
2*Z_N(5)*(KL_N(0,z_N)+KL_N(z_N,0)) = z_N,
Phi_N(5,z_N) = -2*Z_N(5)*KL_N(z_N,0).
```

These are values of the same actual Gaussian comparison, not a physical
KL value assigned to the arithmetic carrier. The source-unit affine term
and the least-integer-window rule remain the stated observation protocol.
The result proves its global variational criterion and its joint shell
content; it does not supply a proof identifying that protocol with a
separate integrated effective-action vertex. G4 keeps that scope. The
independent mathematical export is
`MathematicalInterface.complete_section_equilibrium`.

### Retained spectral capacity before solving the response equation

`HistoryHaarSectionCapacityThreshold` evaluates the available response of
the same complete joint window:

```text
S_N(B) = sum_{i in support(B)} integral w_i(u)*r_i(u) du,
r_i(u) = kineticPrecision_i(u)/precision_i(u),
0 <= S_N(B)-F_N(B,z) <= Z_N(B)/(1+z),  z>=0.
```

The first expression uses the original spectrum, every original
multiplicity and the actual frequency endpoint of each row. The bound is
applied only to the exact positive saturation remainder. No field row,
scalar row or spectral birth is discarded. The capacity is monotone in
the window, including the new labels entering the support.

For every positive real bandwidth, not only integer levels, the following
conditions are equivalent:

* `S_N(B)>1`;
* the complete source-unit comparison has a unique positive balance;
* its potential has a global minimum on the nonnegative amplitude ray.

The original scalar ground row gives
`S_N(4) <= (8/15)*sqrt(pi) < 1`. The first complete connection shell gives
`S_N(5)>1`. Thus at a positive integer level the available spectral
capacity exceeds one exactly when `R>=5`. Five is the least admissible
integer for this stated protocol, with the already proved one-field and
one-scalar position content. The two inequalities come from actual shell
integrals and generated multiplicities, rather than an assumed solution
of the response equation.

The seven `SourceResponseLevel` declaration reviews now refer to these
actual content cells, the complete shell certificate and the joint
selection theorems. Physical three-position statements retain their
physical scope. Their numerical intervals are not used as arithmetic
input. The independent mathematical export is
`MathematicalInterface.complete_section_capacity_threshold`.

### Joint content and the real spectral crossing

The complete selection comparison must include the original shell support,
the actual content count and the force computed with the same Gaussian
weights. A response equation at a freely chosen bandwidth is only one of
these ingredients. The physical `ThreePosition` and `SameShellSupport`
conditions remain distinct in `SourceResponseLevel`; neither is inferred
from a response equation alone.

On the arithmetic side, `HistoryHaarSectionCapacityThreshold` now proves
continuity, including births, and strict increase of the original capacity
on nonnegative bandwidths. The previously calculated shell bounds then give
a unique real crossing `criticalBandwidth N`:

```text
4 < criticalBandwidth N < 5,
S_N(criticalBandwidth N) = 1,
positive equilibrium at B  <=>  B > criticalBandwidth N,
global minimum at B       <=>  B > criticalBandwidth N.
```

The joint spectral-cell theorem calculates one field position and one
scalar position at this crossing. Their complete multiplicities are still
those of the original differentiated operator. No arithmetic position
count is supplied as a replacement for the physical three-position input.
The smallest integer exceeding the crossing is its natural ceiling, five.
The crossing itself is a boundary of feasibility, not a finite-amplitude
equilibrium.

For clarity, the theorem `first_cell_feasible_integers` also calculates the
entire set of integers satisfying this joint content and capacity test:
`5 <= R <= 8`. Thus the stated least-window protocol selects five; the
response and content conditions do not exclude six, seven or eight. This
is different from the physical selector, which proves uniqueness after
its own shell-support and three-position conditions. Equal numerical
values do not identify the two bandwidth conventions or the effective
vertices of the two branches.

### Fluctuation and restoration on the selected original window

Window selection is followed by variation of that same retained state.
`GaussianPrecisionMoments` evaluates the observable `X(x)=q*x^2/2` on the
actual centred Gaussian of precision `p+z*q`:

```text
E_z[X]   = q/(2*(p+z*q)),
Var_z[X] = q^2/(2*(p+z*q)^2).
```

The fourth moment used in the variance is obtained by exact differentiation
of the Gaussian moment-generating function. No finite Taylor approximation
is made. In `HistoryHaarSectionRestoration`, `p` and `q` are the original
joint-Hessian precision and its own kinetic coefficient. Their exact
mean and variance identities give

```text
F_N(B,z) = 2*sum_i integral w_i(u)*(E_0[X_i]-E_z[X_i]) du,
dF_N(B,z)/dz = K_N(B,z),
K_N(B,z) = 2*Z_N(B)*average_B(Var_z[X_i]).
```

All original labels, multiplicities and frequency endpoints remain in
these sums. The last average is a conditional-variance average over those
labels and frequencies. It is not the raw variance of their uncentered
mixture. The derivatives hold for `z>-1/2`, and the curvature is strictly
positive for `B>0,z>=0`. Its lower comparison is the original trace divided
by `(1+z)^2`; no amplitude-independent positive lower bound is inferred.

At the selected original window `B=5` and its own positive equilibrium
`z_N`, the second derivative of the source-unit potential is exactly
`K_N(5,z_N)>0`. The original first field shell gives
`responseTrace_N(5)>=64*exp(-4)`; together with `0<z_N<7` this proves
`K_N(5,z_N)>=exp(-4)`, uniformly in the actual history stage. This is a
bound for the original comparison, before a probability or vertex
renormalization. Subtracting its equilibrium value and translating the
amplitude gives a centred potential with zero force at zero. Its second
variation on every real ray `t*v` is `K_N(5,z_N)*v^2`. Thus the same source
supplies the window, equilibrium, fluctuation and restoring derivative.

The radial-variation reviews now refer to this full-window result rather
than the earlier homogeneous comparison or an unrelated log-cosh centre
potential. This is a comparison of derived mechanisms; it does not assign
the physical score normalization, colour rank or radial mass to the
arithmetic carrier. The precision Gaussian is the law already generated
by the joint vacuum Hessian, not an asserted evaluation of the nonlinear
interacting path integral. The independent mathematical export is
`MathematicalInterface.complete_section_restoration`.

### Window variation is distinct from amplitude restoration

`HistoryHaarSectionWindowVariation` differentiates the same complete
comparison with respect to its bandwidth. Birth rows are extended by their
actual zero earlier integrals, so continuity and monotonicity include births.
For positive amplitude the complete force and source-unit potential increase
strictly with the window. If two feasible windows `B<C` have their own
balanced amplitudes `z_B,z_C`, then

```text
z_C < z_B,
Phi_N(B,z_B) < Phi_N(C,z_C).
```

Thus windows five and six both have actual equilibria, at different
amplitudes. This is an explicit property of the original comparison, rather
than a count of formal solutions of an algebraically substituted response.

Away from kinetic birth values, the exact partial bandwidth derivative is

```text
d Phi_N(B,z)/dB = exp(-B) * sum_{i in support(B)}
  cost(B/(B+restoring_i),z)/(2*sqrt(B-kinetic_i)) > 0  (B>0,z>0).
```

The full logarithmic cost, original Gaussian and all multiplicities remain.
In particular the window derivative at the generated amplitude equilibrium
on window five is strictly positive. The amplitude equilibrium therefore
does not turn the bare comparison into a joint amplitude/window stationary
point. The source-unit least-integer protocol remains well-defined; an
effective endpoint/content selection law would have to be derived for its
own complete response. The physical `ThreePosition` tests the generated
endpoint, whereas the arithmetic first-cell condition above tests the
bandwidth itself. They are different observables, even when both calculations
mention five. The independent export is
`MathematicalInterface.complete_section_window_variation`.

### Source-derived uniqueness of the observation

The remaining G4 comparison concerns a joint selection theorem. A minimum
over the already balanced integer windows is not used to replace it. The
physical branch distinguishes three proofs: least admissible coclosed
deformation, a unique positive response root for a fixed spectral coefficient,
and integer selection under joint shell-support and endpoint-content tests.
The last proof uses `ThreePosition(c R)`, `SameShellSupport R` and a crossing
certificate for the same response. It is distinct from the zero-argument
IR-edge construction in `SourcePhysicalInterface`.

For the arithmetic source, the existing first-cell test concerns the
bandwidth itself, whereas the physical position test concerns the resulting
endpoint. The entire arithmetic feasible set remains `5 <= R <= 8`.
Uniqueness of the amplitude at each such window does not select a window.
The source-unit comparison uses the internally calculated intensity, but
its identification with an endpoint variation of the original action has
not been derived by the amplitude-equilibrium theorem.

The next proof must identify the actual endpoint variation, its full vertex
and normalization from the arithmetic action, calculate the corresponding
support and endpoint-content conditions on that same response, and establish
both existence and exclusion of every other admissible candidate. A fixed
level-five coefficient cannot be used to justify the original selection of
level five. The physical position count, bandwidth unit and threshold are
not inserted into the arithmetic conditions. These obligations retain G4's
current partial scope; they add no unproved selection claim to the Lean root.

### Uniqueness of the covariance before endpoint selection

The connection carrier in `HistoryHaarSectionAction` has three geometric
one-form components. The coordinate count in `HistoryGaussianCovariance`
belongs to history-coordinate jets and remains a separate construction.
`HistoryHermitianContraction` now evaluates the independent real basis in
the original trace metric. Writing its generators as `F_a` and its carrier
dimension as `d`, the complete contractions are

```text
sum_a F_a X F_a = Tr(X)*I - X/d,
sum_a F_a^2 = (d-1/d)*I,
sum_a [F_a,[F_a,X]] = 2*d*X - 2*Tr(X)*I.
```

Thus unit-trace generators have twice the existing half-trace Casimirs.
An orthogonal change of the independent real coordinates preserves the
quadratic sum. The factor is not assigned from the physical colour basis.

`HistoryHaarGaussianCovariance` constructs the explicitly normalized,
isotropic local-fibre comparison on `3*(d^2-1)` components. Its volume is
the measured projective volume at the canonical source correlation radius.
The total comparison intensity fixes its entire isotropic covariance
matrix uniquely. The full defining contraction at total intensity `q` is
`q/(d*V)*I`; a simultaneous half-trace change of generators and inverse
change of coordinate covariance leaves it unchanged. In the root's
unit-intensity comparison `q=1`. This is the appropriate local-fibre
counterpart of the physical component-variance calculation.

The actual joint-field Gaussian covariance is a different object, now
constructed in `HistoryHaarSectionCovariance`. At frequency `u`, it keeps
exactly the original labels satisfying `u^2+kinetic_i<B`. If `K` is the
positive precision matrix of that original Hessian, then

```text
C = diag_i (u^2+eigenvalue_i)^(-1),
K*C = C*K = I,
K*C' = I  implies  C'=C.
```

The competitor `C'` is any full matrix; its off-diagonal entries are not
assumed to vanish. The diagonal entries are the second moments of the
existing real precision Gaussian. The total variance is the sum over all
original retained labels, rather than a prescribed centre susceptibility.
The two actual lowest sectors have precisions `u^2+4` and
`u^2+(d-1/d)/2`. Their inequality is proved at every generated history
dimension. Consequently, whenever `u^2+4<B`, the complete covariance is
not isotropic. A normalized isotropic fibre calculation cannot be silently
substituted for it.

This batch proves covariance uniqueness at each actual window, and fixes
the carrier and normalization used in the physical comparison. It does
not select the window. G4 retains the joint endpoint/content existence
and exclusion obligations stated above; the previously calculated feasible
windows are not changed by calling their Gaussian state unique. The
mathematical root exports these two distinct statements as
`normalized_haar_fibre_covariance` and `unique_joint_gaussian_covariance`.

### The joint Gaussian law and the real form of the field

The state-level counterpart is now constructed in
`Arithmetic.HistoryHaarSectionGaussianState`, independently of the physical
branch. The original joint Hessian has a complex Hilbert basis. Every
retained label therefore contributes two real coordinates, rather than one.
For the original precision `p_i=u^2+lambda_i`, realification gives

```text
S_2(x) = (1/2) sum_i p_i (x_i,re^2 + x_i,im^2),
K_real = diag_(i,quadrature) p_i,
C_real = K_real^(-1).
```

The real/complex coefficient maps are inverse and preserve this finite
quadratic form. Among all centred Gaussian measures whose complete
covariance solves `K_real*C=I`, the measure exists uniquely. Neither
cross-sector nor cross-quadrature entries are excluded in the competitor
class. Their vanishing, and coordinate independence, follow from the
precision equation and the Gaussian-law uniqueness theorem. The real trace
is twice the earlier one-quadrature inverse-precision trace.

For nested original kinetic windows, the larger state's actual marginal is
the smaller state. This proves compatibility across cutoff births at each
frequency. It is not merely a comparison of separately normalized label
weights. The realification retains exactly the original condition
`u^2+kinetic_i<B`; it adds no spectral cutoff or root input.

The complete response observable is the original kinetic quadratic form
after the Gaussian coefficient filter
`x_i -> exp(-(u^2+kinetic_i)/4)*x_i`. Consequently its mean and variance are

```text
E[O]   = sum_i exp(-k_i/2) * k_i/p_i,
Var[O] = sum_i exp(-k_i) * (k_i/p_i)^2,
k_i    = u^2+kinetic_i.
```

The variance is the original response kernel sum. Both real quadratures
must be included before taking it. This removes the otherwise missing
factor two; all cross-coordinate covariances are calculated in the same
joint state. No independent-coordinate premise is supplied.

The root field `unique_realified_joint_gaussian` exports these state,
realification, marginal and quadratic-response results. They apply to the
finite quadratic Gaussian state of the original Hessian. The original
nonlinear action retains its cubic current and quartic interaction; this
construction does not evaluate its interacting Gibbs measure.

The comparison with physical endpoint selection keeps three distinct
questions visible:

| Object | Uniqueness class | Present result |
| --- | --- | --- |
| Gaussian state at an original finite window | All centred Gaussian laws satisfying the full original precision equation | Existence and uniqueness proved |
| The corresponding quadratic response | Original kinetic action after the specified Gaussian filter, in that same law | Exact mean and variance proved |
| Observation window and endpoint together | Actual response, shell support and source-content conditions on the same candidate | Joint selection still requires the arithmetic endpoint/content derivation |

In `Physical.SourceResponseLevel`, the selection of five uses the
three-position endpoint condition, the same-shell support condition and the
crossing certificate for the same response. The first-cell arithmetic test
and the fixed-window amplitude equilibrium do not provide that joint
condition: their previously computed feasible integer windows remain
5, 6, 7 and 8. No new minimum protocol or imported physical position count
is used to remove them. G4 keeps its joint selection scope until the
arithmetic source itself supplies the corresponding condition and the
existence-and-exclusion proof.

### The complete Gaussian source variation before endpoint selection

`Operations.FinitePrecisionTilt` now evaluates the actual Laplace integral
of a complete finite quadratic score. `Arithmetic.HistoryHaarSectionGaussianVariation`
applies it to the original realified history field and its existing
heat-filtered kinetic observable. No physical response level, position
count or endpoint coefficient is inserted.

At the original kinetic support, put `k_i=u^2+kinetic_i`,
`p_i=u^2+eigenvalue_i` and `q_i=exp(-k_i/2)*k_i`. Both real quadratures are
kept. The common linear coupling is exactly

```text
S_z(x) = S_0(x) + z O(x),
O(x)   = (1/2) sum_(i,quadrature) q_i x_(i,quadrature)^2.
```

The varied precision is `p_i+z*q_i`; the action identity is proved. Among
all centred Gaussian laws satisfying its full precision equation, the
varied state exists uniquely, without precluding off-diagonal covariance
in competitors. Its full partition is proved from the integral:

```text
Z(z)      = integral exp(-z*O(x)) dnu_0(x),
log Z(z)  = -sum_i log(1+z*t_i),       t_i=q_i/p_i,
H(z)      = z E_0[O] + log Z(z)
          = sum_i (z*t_i-log(1+z*t_i)),
H''(z)    = Var_(nu_z)(O)
          = sum_i exp(-k_i)*(k_i/p_i)^2/(1+z*t_i)^2.
```

The scalar density identity and independence derived from the original
joint Gaussian justify this partition calculation; it is not a product
assumption imposed on comparison states. Generic logarithmic partition
derivatives give the same varied score mean and variance. The arithmetic
variance identity is also proved directly in the unique varied law.

This distinguishes two previously similar response functionals. The
existing labelwise comparison is

```text
H_label(z) = sum_i exp(-k_i)*cost(k_i/p_i,z),
H_label''(z) = sum_i exp(-k_i)*(k_i/p_i)^2/(1+z*k_i/p_i)^2.
```

Its curvature agrees with `H''` at zero coupling. For nonnegative coupling
it is at most `H''`; for positive coupling and positive kinetic precision
the inequality is strict, mode by mode. Thus it remains a valid labelwise
comparison, but is not the finite-coupling partition of `O` in the complete
field. Fixed-window equilibria previously proved for `H_label` cannot be
identified with an endpoint of this joint partition without a further
source-variation identification.

The physical comparison requires this same-state distinction: mean,
fluctuation, restoring derivative and endpoint conditions must belong to
one actual source variation. The new result fixes the response of the
existing `O` under its common linear coupling. It does not assert that an
as-yet-unidentified endpoint variation must be this coupling.

The selection obligation is still joint: derive the arithmetic endpoint
variation and content condition from the original source, use the original
shell support, and prove existence and exclusion throughout that candidate
class. A unique law at each window, a unique amplitude at fixed window,
or the first feasible integer is not joint window uniqueness.
`Physical.SourceResponseLevel` likewise uses content, same-shell support
and the crossing certificate together, not a single successful endpoint.
The root exports the new, precisely scoped results as
`common_gaussian_source_variation`.

### Complete common-vertex equilibrium classification and the joint selection test

The actual finite joint partition of `HistoryHaarSectionGaussianVariation`
now has its frequency-integrated unit-work comparison classified in
`Arithmetic/HistoryHaarSectionCommonBalance`. For every original label put
`t_i(u)=exp(-k_i(u)/2) k_i(u)/p_i(u)`. The heat factor belongs to this
vertex; it is not inserted a second time as a weight outside the logarithm.
Both quadratures of the complex joint field are already included in the
partition, so the integrated comparison is
`H_B(z)=sum_i integral [z t_i-log(1+z t_i)] du`.

For every positive original window, the entire positive amplitude ray obeys
`exists! z>0, H_B'(z)=1` iff `T_B>1`, where
`T_B=sum_i integral t_i du`. The proof retains the exact saturation deficit
`T_B-H_B'(z)=sum_i integral t_i/(1+z t_i) du` before bounding it by the finite
frequency volume divided by `z`. This is an all-amplitude classification,
not a small-perturbation or finite search statement.

All windows `B>=5` meet the capacity test. In particular two distinct
windows, with their own positive amplitudes, satisfy the comparison.
`no_joint_unique_balance` formally excludes joint bandwidth-amplitude
uniqueness for this unit-work protocol. It does not exclude a joint
selection law derived from the original source action. It establishes which
proposition that further law must strengthen.

The physical comparison is kept at its actual scope. `SourceResponseLevel`
uses `ThreePosition`, `SameShellSupport` and a response crossing certificate
together. The fixed eight-branch `SourceTTGaussianCoefficient` starts with
the already selected level five; its unique positive radius is not a proof
that level five was selected. The mathematical coordinate-scale transport
also transports its Gaussian and cutoff, and by itself is not an endpoint
field equation.

The remaining joint-selection target is to derive the metric/endpoint
vertex, its source pairing and measure terms from the same original action,
then impose its resulting content and shell conditions on the same
response. Neither first-feasible minimization nor the physical
three-position count is appended as an independent mathematical condition.
The common balance classification is exported by `MathematicalInterface`;
it is not registered as a completed endpoint-window selection.


### Original spatial metric variation (2026-10-27)

`Arithmetic.HistoryHaarSectionGeometricVariation` derives the relative three-dimensional angular metric variation of the original nonlinear connection--section action, holding its fibre response fixed. The common polar metric fixes the dimension and contragredient one-/two-form transport; the measured quotient volume fixes the cubic volume factor. The exact action is Y/c + c K + c^3 V. All positive scales are compared: a unique positive stationary scale exists iff Y>0 and K+V>0, and its exact action gap is a positive square. This is a fixed-configuration spatial theorem, not a four-dimensional TT endpoint equation, a bandwidth-selection theorem, or uniqueness of the positive generated source state. Zero configurations rule out selection from arbitrary configurations; they do not rule out selection by the actual positive source. The previously proved coordinate transport, which also moves the fibre coefficients and cutoff, remains a separate operation. The physical shell/content/crossing premises are not inserted into the arithmetic source.


### Geometric Gaussian variation and the scope of uniqueness (2026-10-27)

`Operations.FinitePrecisionPath` takes the partition in one reference
Gaussian law and exponentiates the full difference of quadratic actions.
For a nonlinear precision path P(c), its free energy has first derivative
E_c[S'_c] and second derivative E_c[S''_c] - Var_c(S'_c). Both terms are
proved from the partition, including its parameter-dependent normalization.
The varied law is unique among all centred Gaussian competitors satisfying
the full precision equation, without a diagonal-covariance assumption.

`Arithmetic.HistoryHaarSectionGeometricState` differentiates the original
nonlinear spatial action before forming this state. Its exact ray retains
all cubic and quartic terms. On the original vacuum Hessian the connection
precision is lambda/c, and scalar precision is c*a+c^3*C_F. Both real
coordinates of every original complex mode are retained. The logarithmic
force is the complete original-mode sum, with connection term -1 and scalar
term 1+2*c^2*C_F/(a+c^2*C_F). It is not the old unit-work comparison force.

The fixed-support zero-frequency spatial determinant is exactly invariant
under changes of cutoff that leave the original support unchanged. This
includes the full first and second joint support cells. Thus its geometric
response cannot select one cutoff inside either cell. This is a test of
that spatial determinant, not a test that discards the nonzero-frequency
extensions, shell births, or the original interacting action. Those terms
must be treated in their actual source-derived joint variation before any
joint endpoint-window uniqueness claim.

The physical comparisons keep their quantifiers. SourceResponseLevel
selects R=5 from a crossing certificate, the three-position condition and
same-shell support jointly. SourceTTResponse concerns a separate certified
TT endpoint; it is not the zero-argument infrared-edge physical entry.
Neither physical content nor a fixed eight-branch TT table is inserted
as mathematical source data. MathematicalInterface exports the new spatial
state result as original_geometric_gaussian_response. The final joint
state-endpoint-window selection remains a separate, uncompleted target.

### Physical closure mechanisms and removal of the least-window substitute (2026-10-27)

The comparison now follows the actual V5 and Physical source chains rather
than treating every response parameter as the same variable. The condensed
intensity, internal metric radius, frequency, observation bandwidth and
content replication count are distinct. In particular V5 `kL` denotes the
dimensionless product of a frequency and a radius; it is not KL divergence.

There are two physical endpoint constructions in the current sources. The
zero-argument `CanonicalYangMills` conclusion uses the natural Gaussian IR
edge `sqrt(2*pi)`. The finite V5 TT endpoint is the root at approximately
2.4935343325 and enters Lean through its own coefficient/endpoint interval
certificate. These constructions must not be substituted for one another.

The V5 finite-window chain uses three separate inputs to its selection:
content screening compatibility, the actual projected TT response, and
retained-shell/content compatibility. The implementation explicitly records
the colour screening normalization in `screening_compatibility`; the
mass-weighted TT kernel has maximum 4/27, while matching the integrated
response to that value is the endpoint prescription. The current fixed
shell support gives candidates 4 and 5; the lower endpoint crossing
excludes 4. The corresponding Lean theorem retains its ThreePosition,
SameShellSupport and crossing hypotheses. It is not a theorem excluding all
other content or shell families without those hypotheses.

The mathematical branch already constructs the original nonlinear
connection--section action, its full differential Hessian and domain,
Gaussian precision, exact window marginals, source-content rows, frequency
boundaries, scale transport and complementary-response ledgers. The open
alignment is the derivation of its actual channel vertex and endpoint law
and their compatibility with its own content selection. Copying the
physical constants, or choosing the smallest feasible mathematical window,
does not supply that derivation.

Accordingly the unused `least_balancedLevel`, `least_minimum_window` and
`least_first_cell_feasible` corollaries and the associated least-window
conclusion fields have been removed. Their elementary order statements
were valid; they supplied no intrinsic selection principle. The complete
feasibility classifications, real capacity crossing, global comparison
minimum, original action derivatives and Gaussian laws remain. The
SourceResponseLevel comparison review is marked pending construction for
the source-derived mathematical joint selector; its proved conditional
arithmetic selector remains available. Older passages describing the
least-window rule as a completed counterpart are superseded by this audit.

The next construction must differentiate the same original action in the
actual observation directions. For a finite real Gaussian precision path
P and C=P^-1, the complete quadratic response includes both
one-half tr(C P'') and minus one-half tr(C P' C P'). The connected
covariance is the latter trace with positive sign. Non-diagonal vertices,
direct second variations, frequency boundaries and new shell labels
must remain in the response in which content and endpoint conditions are
tested. Positive covariance alone is not positivity of the entire geometric
free-energy Hessian. This is an implementation target, not a newly proved
joint selection theorem.

After these removals, the mathematical root was built once with
`lake build GeneratedFoundations.ArithmeticFoundation`: 4577 jobs completed
successfully, with no errors or warnings in the final log. Removed-declaration
references and JSON consistency were checked. The full physical inventory
refresh remains pending registration of the concurrently added
`SourceAdjointEventTransport` and `SourceMatterEventInsertions`; the existing
inventory explicitly records that status. This build is not certification
of those concurrent physical additions. The separate physical work on the
endpoint normalization and broader shell selection will be compared again
once its actual source derivations are available.

### Tensor-response normalization and the fixed endpoint rule (2026-10-27)

`Physical.SourceTTResponseNormalization` computes the half-trace pairing
of the generated plus/cross tensors. Both polarizations have unit norm
and their cross pairing vanishes. For the two-leg rational kernel, the
negative logarithmic mass derivative divided by two is exactly
`y*(1-y)^2`. With fixed finite weights its derivative is the corresponding
weighted sum. This derivative is kept distinct from the original spectral
response and from variations of a moving frequency boundary.

The explicitly stated kinetic quadratic insertion is evaluated in the
same finite positive-precision Gaussian. Twice its score variance equals
the sum of rational kernels. Its partition, first response and second
response follow from the existing Gaussian tilt. General nonlinear
precision paths keep the mean direct second insertion as well as the
score variance, with the actual precision-derivative hypotheses retained.
The insertion rescaling theorem gives its quadratic response scaling.

`SourceTTGaussianCoefficient.coefficient_eq_gaussian_response` identifies
the existing eight-branch coefficient with the Gaussian-weighted integral
of these kinetic responses, including the original branches, prefactor
and frequency limits. Its conclusions now export the normalization
package through the existing physical interface. Under the existing
endpoint matching, a common positive calibration of the spectral response
and the reference profile leaves the unique radius unchanged. Relative
species weights, other projected vertices and the choice of matching rule
are not supplied by this cancellation theorem. In particular, neither a
modewise maximum nor a loop-measure factor alone derives the endpoint
equation from the original full source. No new root field, endpoint
number or source-evolution rule is introduced.

The affected `SourcePhysicalInterface`, `SourceTTResponse` and
`CanonicalYangMillsTT` targets built successfully after these additions
(4407 dependency jobs). The dedicated
`verification/tt-response-normalization-audit.lean` checked sixteen
signatures and ten transitive axiom lists; only `propext`,
`Classical.choice` and `Quot.sound` occurred. Its output is saved beside
the audit source. This is a targeted check, not a refresh of the full
repository verification inventory.


### Original connection vertices and the full finite inverse (2026-10-27)

`Arithmetic.HistoryHaarSectionConnectionVariation` differentiates the
position-dependent section part of `HistoryHaarSectionAction` with respect
to the original connection. Writing `D_A = gradient + A`, the first
precision vertex between arbitrary original sections is

    <D_A psi, X xi> + <X psi, D_A xi>.

The mixed direct second vertex in directions X and Y is

    <X psi, Y xi> + <Y psi, X xi>.

These are obtained from the same covariant square. Its exact finite
connection path has no higher-order remainder. At zero connection the
first action derivative agrees with the existing section current.

The scalar restriction is exactly the scalar part of the existing
frequency support u^2 + kinetic < B. Its full complex precision matrix is

    P_A = Gram(D_A e_i) + (C_F(N) + u^2) I.

All off-diagonal entries and both current orders are retained. The product
D_A e_i is evaluated in the original Haar space, without projecting its
output back into the observation subspace. Thus the full finite matrix
satisfies P_(A+tX) = P_A + t V_(A,X) + t^2 G_X. Gram positivity gives
P_A >= (15/8 + u^2) I for every connection, history stage and cutoff.
Its positive inverse exists uniquely among all matrices; the exact inverse
difference identity retains the complete product of precision changes.

This supplies the original source vertex and the well-defined full matrix
inverse for the connection channel. It is a section response at a fixed
connection, rather than an evaluation of the full interacting measure in
which connection and section fluctuate together. The existing diagonal
heat-score moments are not substituted for moments of this generally
non-diagonal vertex. Endpoint/content/window selection and the complete
non-diagonal Gaussian connected-response evaluation remain distinct
construction steps. No physical normalization constant is imported.

The independent mathematical interface exports the construction as
`original_connection_response_vertices`. The mathematical-root build
completed successfully (4578 jobs). This batch adds 32 indexed theorems
in a 46-declaration module. It does not certify concurrent physical edits.

All 32 newly indexed theorems passed a transitive axiom check; their only
axioms are propext, Classical.choice and Quot.sound. The source has no
proof placeholders, and JSON/reference consistency and git diff checks
passed. Proof and build logs are under .lake/history_connection_vertices_*.

### Original full Gaussian connection response (2026-10-27)

`Operations.FiniteMatrixGaussian` and `FiniteMatrixGaussianResponse` prove
full real finite-dimensional Gaussian identities for a positive precision
matrix. The covariance is its full inverse. The uniqueness class consists
of all centred Gaussian measures satisfying the precision covariance
identity, including measures with correlated coordinates. The fourth
moments are obtained by exact polarization of the proved one-dimensional
Gaussian fourth moment; both connected pairings survive.

`Arithmetic.HistoryHaarSectionConnectionGaussian` realifies every original
complex scalar window section with both phase quadratures. Its full real
precision is the derivative Gram matrix plus `(C_F(N) + u^2) I`. The
quadratic form is proved equal to the original connection-dependent
section action plus its frequency contribution. It has the generated
uniform lower form `15/8 + u^2` and a unique centred Gaussian state.
Neither quadrature is omitted or counted a second time.

`Arithmetic.HistoryHaarSectionConnectionResponse` proves that the first
insertion and direct mixed second insertion are the actual derivatives of
that original action on the recombined source section. The insertion
means are half-traces against the full inverse precision. The connected
response is the complete four-index contraction with both inverse
pairings. It is evaluated in the very same state as the direct second
mean. The direct-second-minus-connected response expression is retained.
Its positivity is not inferred from positivity of covariance alone.

The independent mathematical interface exports these results as
`original_connection_gaussian_response`. The mathematical-root build
completed successfully (4582 jobs). The 49 newly indexed theorems passed
the transitive axiom audit with only propext, Classical.choice and
Quot.sound. Source, JSON, declaration and whitespace checks passed.
The root's local dependency closure has 519 modules and no Physical
imports. Logs are `.lake/history_full_gaussian_root.log` and
`.lake/history_full_gaussian_axioms.log`.

This completes the full finite Gaussian state and connected-response
stage of the original connection channel. The state is at a fixed
connection and the original finite frequency support; this construction
does not itself select the connection, a content or the observation
window. No non-diagonal free-energy differentiation theorem is inferred
from the definition of the response expression. These selection and
differentiation statements have their own mathematical content.


### TT endpoint selection: exact source balance (2026-10-27)

`Physical.SourceTTEndpointBalance` differentiates the comparison cost minus
the logarithm of the actual finite Gaussian partition. The first response
is the direct gradient plus the mean precision vertex. The second response
is the direct Hessian plus the mean second precision vertex minus the
variance of the first vertex. The complete finite path is retained.

For the kinetic insertion used by the existing coefficient module, the
actual logarithmic partition has second derivative equal to half the
two-leg source response. Thus a reduced Hessian of the form

    Z - kappa * (A/c) / 2

vanishes at the existing endpoint level 4/27 if and only if the direct
response satisfies Z = 2*kappa/27. This is a conditional equivalence.
The value of Z is not set to that expression by definition, and no
evaluation of this direct response in the complete generated physical
source is claimed. In a nonlinear source deformation its mean second
precision vertex must also be included in the direct balance.

With the same positive coefficient, every positive matching level theta
has one crossing c=A/theta; distinct levels give distinct crossings.
The exact weighted profile defect is the sum of the original modewise
defects. A mode at the maximum of the logarithmic mass response has
kinetic response 4/9, whereas its mass response is 4/27. The two readouts
are therefore not interchangeable. On the compact ladder homothety,
(c^4/D)*(J/c^4)=J/D, so unit feedback in that deformation does not itself
select c.

These results isolate the unproved source-selection identity. They are
kept in a separate module and do not change the endpoint certificate,
spectral weights, numerical values, or physical-root closure claims.

The dedicated module built successfully (4056 dependency jobs), with no
warnings in the final build. All sixteen public theorems passed the
signature and transitive-axiom check recorded in
`verification/tt-endpoint-balance-audit.txt`. Only `propext`,
`Classical.choice` and `Quot.sound` occur. This verifies the stated balance
and equivalence results, not the unevaluated direct-response identity.

### Gaussian TT response-realization boundary (2026-10-27)

`Physical.SourceTTClosureBoundary` completes the proposed least-boundary
calculation in its explicit realization class. Splitting total precision
one as `(1-y)+y` preserves the actual one-coordinate Gaussian law. The
mass-weighted kinetic-score variance is `y*(1-y)^2`; its image on `[0,1]`
is exactly `[0,4/27]`, with every value realized already on `[0,1/3]`.

The realization class is defined by positivity of c and existence of a
split realizing the unchanged spectral readout A/c. No matching threshold
occurs in that definition. For A>0 the class is exactly `[27*A/4,infinity)`.
Its least member is unique and the realizing split there is necessarily
y=1/3. Least membership is equivalent to the existing matching equation.
The exact radius defect is

    c - 27*A/4 = (27*c/4)*(y-1/3)^2*(4/3-y).

The source-transport theorem retains two explicit hypotheses: the actual
source's admissible-state class agrees with this comparison class, and
its native update selects the least boundary. Neither hypothesis is
deduced from the existence of the Gaussian source law. This module is not
exported as completion of full-source endpoint selection.

For the original weighted mode response, saturation is equivalent to every
positive-weight mass fraction equalling 1/3. The squared deviations obey

    sum w*(y-1/3)^2 <= 3*((4/27)*sum w - sum w*rho(y)).

A positive-weight nonmaximizing mode therefore gives strict deficit. These
results provide explicit equality and concentration tests for a proposed
multimode source reduction. They retain the original coefficient and do
not alter spectral weights, field content, frequency windows or numerical
endpoint values.

The module's final targeted build passed (4057 dependency jobs) without
warnings. All seventeen public theorems passed signature and transitive
axiom checks in `verification/tt-closure-boundary-audit.lean`; the output
is saved beside that source. Only `propext`, `Classical.choice` and
`Quot.sound` occur. These checks verify the stated realization-class
theorems and conditional source transport, not the two source-identification
hypotheses of that transport theorem.

### Actual full Gaussian mean variation (2026-10-27)

`Operations.FiniteMatrixGaussianVariation` differentiates the full inverse
precision: C' = -C P' C. In the same varying Gaussian law, the derivative
of a varying quadratic mean is its direct insertion mean minus the full
connected covariance. The trace identity follows from both complete Wick
pairings and actual symmetry, without a diagonal or commutation assumption.

`Arithmetic.HistoryHaarSectionConnectionResponse` applies this theorem to
the original covariant square. Its precision path and current path are
proved from the actual connection update. Thus the retained response is
now the derivative of the original current mean in its varied state;
it is symmetric in both connection directions. This strengthens the
response expression recorded in the preceding Gaussian construction.

The complete ray current includes the derivative of the original curvature
action. Its zero-connection mean derivative is the original curvature
Hessian plus the complete section response. No independent direct-response
constant is inserted to enforce a matching level. In the same original
quadratic energy, both the mean and variance equal the actual number of
complex window modes, including both real quadratures. This is an exact
fixed-support capacity identity, not a bound independent of that capacity.

The mathematical interface exports the strengthened response contract.
The mathematical-root build passed (4583 dependency jobs). All 30 public
theorems in the two affected response/variation modules passed the
transitive axiom audit; only propext, Classical.choice and Quot.sound occur.
Seventeen theorem entries were added. The root's local dependency closure
has 520 modules and contains no Physical imports. Logs are
`.lake/history_gaussian_variation_root.log` and
`.lake/history_gaussian_variation_axioms.log`.

The unique Gaussian at a fixed original connection and frequency support
is proved. Joint selection of content, endpoint and window is a different
statement; no selection theorem or full effective-Hessian sign is deduced
from this covariance identity alone. The physical comparison constants are
not used as mathematical inputs.

### Fixed-branch TT update and source-domain comparison (2026-10-27)

`Physical.SourceTTNativeEndpoint` checks the exact homogeneous reduction
of the existing endpoint routine. Its crossing satisfies `t*A/c=theta`,
so `t*=theta*c/A` and the implemented radius update is `c_new=A/theta`.
The update is idempotent and has one positive fixed point. It selects the
least member of `SourceTTClosureBoundary.Realizable` exactly when the
supplied threshold is `4/27`. Thus convergence of this routine verifies
implementation of the matching rule, rather than an independent selection
of its threshold by the source.

The same module proves positivity of each retained branch precision
`(u^2+a_i+b_i)/c^2` at every positive `c`. Every finite projection,
including repeated mode and colour labels, has its unique original
centred Gaussian with the stated precision. Positive precisions also
occur below the candidate response-realization boundary. This comparison
concerns the continued fixed precision family; it does not assert that
the active physical content remains fixed at all radii, or equate source
existence with physical endpoint closure.

The original modal mass fractions are invariant under the homogeneous
radius change. In particular a retained scalar mode has fraction `3/7`,
rather than `1/3`, along this path. A source-preserving identification
with the abstract split class must account for the actual comparison
vertices and modal fractions.

The two source-level hypotheses in `endpoint_of_source_realization`
remain unproved: identification of the physical closure states with the
response-realization class, and least-boundary selection by an update
whose threshold is derived independently. Neither is installed as an
axiom or as a new field of the physical root. The actual fixed-threshold
algorithm does select the candidate boundary, as the module proves.

The targeted module build passed (4058 dependency jobs) without warnings.
All twelve public theorems passed signature and transitive axiom checks
in `verification/tt-native-endpoint-audit.lean`; its saved output contains
only `propext`, `Classical.choice` and `Quot.sound`. No manuscript,
numerical source, numerical endpoint value or arithmetic module was
modified in this step.

### Original equilibrium composition and TT closure conditions (2026-10-27)

`Operations.FinitePrecisionEquilibrium` proves equality of the original
joint Gaussian law before and after its independent equilibrium update.
The coordinate version allows every spectral coordinate to have its own
nonnegative restoring rate. The product representation is derived from
the original joint law's computed independent coordinates. With the
innovation held fixed, the covariance fixed-point equation is equivalent
to retaining that original covariance; no alternative update is introduced.

`Physical.SourceTTEquilibriumClosure` applies this result to every finite
projection of the retained precision family. All source expectations and
the TT quadratic-score variance are preserved. The positive-radius
equilibrium-closure class of this family is computed as `Ioi 0`. It is
therefore different from the split-response realization class. A further
comparison theorem works inside any allowed open branch interval that
contains the candidate boundary, with the interval hypotheses explicit.

Each radius here has its own original covariance and corresponding
equilibrium kernel. The result does not give multiple stationary
covariances for one fixed kernel, or establish physical endpoint closure
for an interacting full source at all radii. It does not extend the
active-content branch beyond its declared interval.

For the existing compact ladder's homogeneous factors, the joint
conditions of Gaussian equilibrium and unit feedback reduce exactly to
`c>0` and `J=D`. The factors `c^4` and `c^-4` cancel. Thus these displayed
native relations cannot by themselves provide the additional radius
condition in the proposed endpoint-admissibility identification. That
identification is not promoted to a theorem or installed at the root.

The targeted build passed (4060 dependency jobs) without warnings. All
eighteen public theorems in these two modules are included in
`verification/tt-source-equilibrium-audit.lean`. No manuscript, numerical
source, numerical endpoint value or arithmetic module was changed.

The Gaussian invariance theorem specializes directly to the original
120-coefficient connection law with precision `120/q`. Applying the
same equilibrium construction to the retained TT precision projections
tests that construction; it does not derive a TT restoring spectrum or
identify this Gaussian comparison with the full interacting source.
The verification output is saved in
`verification/tt-source-equilibrium-audit.txt`: all eighteen signature
and transitive axiom checks passed, with only `propext`,
`Classical.choice` and `Quot.sound`.


### Native collective vertices and geometric content compatibility (2026-10-27)

The original finite connection Gaussian has a unique marginal law and an
exact effective-precision tower. Its Schur complement keeps all eliminated
cross blocks. The native complete arithmetic fibre now also has exterior
creation/removal, unique current derivations, coincident insertions and
source-frame transport. Local adjoint kinetic transport retains both mixed
terms. The original Gaussian equilibrium law and its fixed-kernel covariance
uniqueness are proved. These fixed-state constructions are distinct from
joint selection of source content, a moving endpoint and a stopping scale.

`Arithmetic.HistoryHaarSectionCollectiveResponse` now derives the joint
connection/log-spatial-metric vertex from the original spatial action. On
one fixed original scalar support its full precision is

    P(A,c) = c G(A) + c^3 C_F I.

For connection directions X,Y and log-metric components v,w, its first
insertion is c V_X + vc G + 3vc^3 C_F I. Its mixed direct insertion is

    c W_XY + wc V_X + vc V_Y + vwc G + 9vwc^3 C_F I.

Both connection/geometry terms and every non-diagonal entry are retained.
The current mean is differentiated in the same varied Gaussian: the
result is the direct-second mean minus the full connected covariance.
The original curvature action stays explicit as S_curv(A)/c. Its full
collective vacuum response contributes ||dX||^2/c. This is a conditional
section Gaussian with its actual background connection, not integration
of all nonlinear connection configurations or motion of the cutoff.

`Arithmetic.HistoryHaarSectionGeometricContent` derives the separate,
fixed-support joint-vacuum content equation directly from the original
geometric partition:

    C_connection = C_scalar + 2 S_restoring(c).

Here S_restoring sums c^2 m/(a+c^2 m) over the actual scalar eigenlines.
Every stationary positive c therefore satisfies
C_scalar <= C_connection <= 3 C_scalar. Counts are native multiplicities,
not externally supplied constants or the physical charged content.

The functional task is still incomplete in the following specific ways:

- the fixed-support collective response is proved; its simultaneous
  moving-frequency restriction and actual birth boundary are not assembled;
- the native geometric content equation is proved; its joint solution with
  screening and the actual endpoint is not proved;
- exact resolution/Schur/capacity propagation is proved; a source-selected
  content/window stop for this same task is not obtained from it.

The existing spatial stationarity identity K c^2 + 3 V c^4 = Y applies to
a fixed actual configuration. It has not been identified with the requested
joint spectral-window stopping rule. Gaussian tail bounds do not perform
that identification. The conditional integer-level uniqueness theorem and
native KL formulas therefore remain in their precise stated classes;
neither a universal numerical R nor a universal numerical KL is reported.

The mathematical root build passed (4605 dependency jobs). The 75 public
theorems from these seven modules passed the saved signature and transitive
axiom audit; only propext, Classical.choice and Quot.sound occur. The build
reported one unused-simp-argument linter warning, with no proof errors.
The mathematical dependency closure contains no Physical module. The exact
source hashes, separate functional requirements and pending joint selector
are recorded in `verification/history-mathematical-alignment-snapshot.json`.
The public audit is `verification/history-mathematical-alignment-audit.lean`
and its saved output. This batch does not certify a full Physical-root build.

Concurrent-source note: Physical.SourceTTCollectiveComparison was added while this batch was running. It is explicitly assigned to family G; its 39 declarations remain pending individual correspondence review. Its actual mass-comparison integral differentiates at a fixed original envelope and frequency projection, and separates kinetic response, its mass derivative and total trace weight. The source file retains the existing endpoint rule in matchedRadius; it does not derive a new joint selector. Its normalization cancels the homogeneous radius. No new mathematical endpoint is inferred from those formulas, and no build of that concurrent Physical module is certified here. The refreshed inventory reports 1 pending construction and 39 pending declaration reviews, not completion of the functional task.


### Collective variation through actual observed windows (2026-10-27)

The independent mathematical entry now exports
`HistoryHaarSectionCollectiveWindow.Conclusions`. Its first and mixed direct
vertices differentiate the marginal of the original non-diagonal
connection--geometry precision. They are not the principal blocks of the
bare vertices. The mixed insertion includes the derivative of both
inverse-precision returns and both effective-precision factors.

The complete first response is exactly the retained response plus the
conditional-covariance trace of the same source. This identity applies to
every pair of nested original finite supports, including spectral-shell
births. The original geometric insertion is separately proved to be the
original action derivative. Its averaged compatibility equation retains
the original curvature, the actual real-coordinate count and the entire
inverse precision trace, at the same internal connection background.

Scope remains explicit: this is a finite, zero-frequency spatial
observation of the original section Gaussian at an internal connection
background. It does not integrate all nonlinear connection fluctuations,
differentiate the continuous frequency endpoint, or select a universal
history content/window/stop. Those joint selection requirements remain
`partial_scope`; the earlier physical matching threshold is not inserted
as mathematical source data. The physical endpoint routine and its current
mass-comparison module likewise retain their stated matching rule.

Two modules add 18 public theorems. The mathematical root build and the
combined 93-theorem axiom audit are recorded in
`verification/history-mathematical-alignment-snapshot.json`. No Physical
source was modified in this batch.


### One collective frequency response through original Gaussian boundaries (2026-10-27)

`Arithmetic.HistoryHaarSectionFrequencyCollective` derives the original
section precision `c*G_A+c^3*(C_F+u^2)*I` on each actual finite reference
support. Its value at unit geometry and reference frequency is the
existing full connection-dependent precision. Connection, logarithmic
geometry and frequency vary together. Their first and direct mixed
insertions include the two frequency--geometry terms and the direct
second frequency insertion. The derivative of the actual quadratic mean
retains direct mean minus full connected covariance, also after the
correct Gaussian marginalization. The geometric content mean retains
the entire `C_F+u^2` term. This is the section law at the source's internal
connection background, not a replacement for integration over nonlinear
connection fluctuations.

`Arithmetic.HistoryHaarSectionCollectiveBoundary` forms the observation
from each complete covariance--insertion row, both real quadratures, the
original heat weight `exp(-(u^2+a_i))` and the actual edge
`sqrt(max(B-a_i,0))`. All visible original scalar rows are enumerated in
any containing zero-frequency finite preparation. The current is
continuous across births. At regular bandwidth its derivative is
`exp(-B)` times the sum of the actual row currents at their respective
edges divided by twice those edges. Its coefficients remain signed;
the positive kinetic-square comparison is not substituted for them.

The same weighted frequency response is exactly retained response plus
conditional return under a smaller original coordinate observation.
Continuity and integrability of both pieces follow from the positive
full precision; no vanishing mixed block or external drive is assumed.
Finite preparation support, coordinate observation, frequency bandwidth
and generation stage remain distinct. This closes the continuous
frequency ledger for this current; it does not supply the joint
source-derived endpoint/content selector or same-task stop. G4 remains
partial, and no universal R or KL is claimed by these identities.


### Filtering both legs of the original collective action (2026-10-27)

`Arithmetic.HistoryHaarSectionFilteredCollective` proves that the original
field filter acts by `V -> F*V*F`. Its exact difference from the earlier
row-weighted mean is the full signed double sum
`sum(K_ji*V_ij*(f_i-f_j)^2)/4`. The earlier row observation remains valid;
the two observations are not identified without controlling that term.

The same connection, logarithmic geometry, and frequency variation
differentiates the filter itself. The first insertion is
`F*(V_X-2*u*r*P)*F`; the direct mixed insertion retains both cross terms
and `(4*u^2*r*q-2*r*q)*P`. The actual mean derivative uses this direct
insertion minus its covariance with the unfiltered derivative of the
original varied source law. It is not declared to be the free-energy
Hessian of a different filtered Gaussian law.

The original field observation makes a pair visible exactly when both
legs are visible. Pair birth is `max(a_i,a_j)`. The moving edge retains
`exp(-B)*exp(abs(a_i-a_j)/2)` and the complete signed covariance--vertex
coefficient. Pair integrals are continuous across births. Their entire
moving-window response is exactly retained response plus conditional
return, with identical weights and edges in all three terms.

The mathematical entry exports these results independently of Physical.
Joint content/screening/endpoint selection and a same-task source stop
remain separate outstanding functional obligations; neither is supplied
by setting an observation derivative to zero.

### Native geometric content and restoration (2026-10-28)

`Arithmetic.HistoryHaarSectionGeometricSelection` evaluates the original
zero-connection joint Gaussian partition on its actual spatial support.
Its scalar trace has multiplicities `d_N*(2*j+1)^2`; its connection trace
retains both curl branches and every history matrix entry, with factor
`d_N^2`. No fixed physical colour count replaces those factors.

Differentiating the original restoring fractions gives the complete
susceptibility. For every fixed `B>8`, the logarithmic geometric force
`c*force(B,c)` is strictly increasing on positive radii. A positive
stationary geometry, when present, is unique, and its original free-energy
curvature is strictly positive. The corresponding direct second mean
strictly exceeds the score variance in the same original Gaussian law.

The first two joint cells are classified exactly. For `4<B<=8` the force
is negative. For `8<B<=16` stationarity holds exactly when `N=0` and
`c=sqrt(128/15)`; the curvature there is `15/4`. The original generated
dimension satisfies `d_N>=4*(N+1)` and `d_N=4` exactly at `N=0`. Thus a
geometry stationary on the initial carrier is not presumed stationary
after new history roots are born.

These are native fixed-support geometric results. The same initial
stationary geometry occurs throughout the second support cell, so this
geometric uniqueness does not select a unique bandwidth. The previously
proved full filtered frequency boundary and conditional return remain
part of the joint window problem. Feature G4 and the same-task stop stay
partial until that common selection is derived on the actual source.

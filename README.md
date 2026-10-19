# Lean Formalization of Arithmetic and Basic Physical Interfaces

[![Lean verification](https://github.com/bookwormseagull1980/Lean-Formalization-of-Arithmetic-and-Basic-Physical-Interfaces/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/bookwormseagull1980/Lean-Formalization-of-Arithmetic-and-Basic-Physical-Interfaces/actions/workflows/ci.yml)
[![Zenodo concept DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23254521.svg)](https://doi.org/10.5281/zenodo.23254521)
[![Zenodo V1.0 DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23254522.svg)](https://doi.org/10.5281/zenodo.23254522)

Source repository: [Lean Formalization of Arithmetic and Basic Physical Interfaces](https://github.com/bookwormseagull1980/Lean-Formalization-of-Arithmetic-and-Basic-Physical-Interfaces).

## 1. Narrative

This project makes a common foundational claim checkable in Lean: starting from
minimal unbiased compositional change, one constructs a single generated
natural-number system and a basic physical response interface within one
explicit source class. Addition, multiplication, factorization, reduced
expressions and complete ordered histories are structures of that same
natural-number construction, not alternative constructions.

The sole closed-world entry is
`GeneratedFoundations.CanonicalClosedWorld.generated`. It accepts no
carrier, probability law, arithmetic source, physical source, forcing term, or
boundary datum. Minimal unbiased compositional change is the sole abstract
root; upstream classification selects the rotation carrier as its canonical
representative, and the positive-parameter compositional law is constructed
uniquely. The theorem then produces source
closure, the complete generated natural-number system, and the basic physical
interface. It does not quantify over a family of widths or orientations: unit
covariance fixes the dimensionless width and the original complex rotation
supplies its canonical oriented presentation before the theorem is assembled.
Reversing that presentation gives the proved conjugate structure. The arithmetic and
physical branches are parallel conclusions;
neither is assumed by the other.

The concrete matter bundle is now constructed on the generated Hermitian
four-carrier with the complete source matter space as its fibre. Its global
coordinates, unitary frame action, relative transitions and passive-component
compatibility are proved in `Physical.CanonicalMatterBundle`; no arbitrary
family of fibres or local compatibility premise is supplied to that entry.
The arbitrary-bundle lemmas remain comparison theorems with their stated
premises, rather than assumptions of this concrete construction.

`Physical.SourceNonlinearTensorAction` constructs the first-order nonlinear
tensor density on the same four-carrier. The actual density variation under
affine dilation uniquely fixes the relative cubic self-coupling to one inside
the unit-normalized quadratic-plus-cubic class. Its density and connection
weights are calculated from their Lie transformations. General local
diffeomorphism covariance and the nonlinear metric field equations are
separate from this affine-dilation result.

## 2. Concrete record

The source is pinned to Lean 4.34.0 and mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. The 19 October canonical-root audit
passed for all 346 local modules imported by the zero-argument entry, with
16,584 compiled constants, 8,490 named type checks and 342 indexed claims.
Those counts describe that audited snapshot, before the concrete-bundle and
nonlinear-density extensions above. The root and its dependencies in that
snapshot use only Lean's `propext`, `Classical.choice`
and `Quot.sound`; there are no local axioms or proof placeholders.
The separately scoped 18 October release audit records 273 modules, 13,854
constants, 7,231 named type checks and 298 indexed claims for that earlier
whole-library snapshot. These are library and audit counts, not counts of
independent mathematical theorems. The current root record does not cover
research modules outside its actual import closure.

## 3. Program implementation

For a first check, run the standard-library-only smoke test in
[`examples/quickstart`](examples/quickstart). For the complete package, install
the pinned Lean toolchain, run `lake build`, then run
`python scripts/verify_foundations.py`. The public workflow performs these
checks together with the verifier regression tests on every push and pull
request to `main`.

## 4. Reproducible verification

The CI and verifier make the compiled declarations, dependency locks, source
hashes, and transitive axiom audit reproducible. The theorem index records the
reviewed manuscript clauses and their corresponding declarations. Cite the
version series with DOI
`[10.5281/zenodo.23254521](https://doi.org/10.5281/zenodo.23254521)` or the
released V1.0 record with DOI
`[10.5281/zenodo.23254522](https://doi.org/10.5281/zenodo.23254522)`.

The verifier audits two dependency-separated entries: the current root library
and `GeneratedFoundations.ResearchExtensions`. The latter contains the
intrinsic prime-parity and squarefree signed source, their classical
Liouville/Moebius coordinate identifications, finite signed-energy and residue
Fourier observations, and the finite recovery kernel selected from the later
generated-world analysis. That kernel proves canonical minimal-frontier
evaluation, the order-two factorial-overlap algebra and exact doubled-tilt
edge balance. Audit coverage of these research extensions does not place them
in the root import closure.

## Detailed scope and boundaries

This independent Lean 4 library formalizes the common mathematical
foundations used in:

- J. Guo, *A Spectral Construction of Natural-Number Arithmetic*.
- J. Guo, *The Spectrum of a Compact Internal Space I: Gauge Structure and a Scalar Mass Gap*.

The arithmetic root also exposes a finite-fibre reduced-expression resolution.
Ordered binary expressions are normalized only by the stated unit and
absorbing-zero laws; their evaluation quotient is the already generated
native-mode semiring, and evaluation commutes with canonical scale and
orientation transport. This adds pre-evaluation resolution without adding a
field to the root datum or replacing the existing arithmetic.

The common root theorem constructs one native natural-number system, including
its arithmetic, factorization, reduced-expression resolution, complete ordered
history and phase fibres, intrinsic history observables, an exact whole-history
transport ledger and detailed-balance edge dynamics, together with the basic
internal physical interface. Intrinsic signed arithmetic observations, finite
Fourier and signed-energy constructions, and the finite generated recovery
kernel are collected under the separate
`GeneratedFoundations.ResearchExtensions` entry and do not enter this root
chain. Its exact
conclusions and comparison classes are recorded in `theorem-index.json`;
this scope does not include every assertion of the two manuscripts.
Each mapped statement has a relative TeX source path and label. The index also
records hashes of those source files and of each manuscript's local recursive
TeX input graph, with its hashing convention and exclusions. These identify the
reviewed manuscript sources; they do not replace review of the stated premises
and conclusions.
The index's `manuscript_review_status` separately records the semantic review
of mapped clauses and any changed sources awaiting review. The stored review snapshot must not be
silently replaced merely because a label still exists in an updated manuscript.

The sole root is minimal unbiased compositional change. The zero-argument
closed-world entry internally uses the least carrier proved by the comparison
theorem and the compositional law supplied by the existence--uniqueness
theorem. `Source.MinimalUnbiasedChange.Datum` remains an implementation and
comparison package, not a second input to the generated world. A separate
variance-scale rigidity theorem starts from an arbitrary nonnegative
same-shape scale and proves that compositional variance additivity and unit
normalization force the square-root law. No Gaussian formula is assumed.

The geometric and physical output records, as well as the common root theorem,
have no orientation or width parameter. The internal-response and chirality
aggregates are likewise parameter-free; the unused parameterized root wrapper
has been removed. Scale and reversal calculations use variables only in their
individual covariance and uniqueness lemmas. Endpoint values,
reflecting boundary operators, spectral data, arithmetic operations and
physical response objects are generated conclusions, not root fields.

On the physical branch, the generated projective scalar shells determine the
complete dimensionless conformal response. The library proves its compact
continuity, strict increase, unboundedness and positive curvature, hence a
unique positive balance for every positive generated source response. The same balance
gives a positive normalized radial gap and the bottom of the complete even
scalar tower, attained by its constant shell. At one generated response unit,
the unique balance and positive bottom are canonical objects of the root
output. No coupling, reference radius, kinetic normalization, spectrum table
or mass-gap value is added to the root datum in this construction.

Structural conditions, realization indices and calculated outputs have
different roles. The C/S/V conditions define the source class. Calibrated
additive information and normalized translation-invariant mass characterize
the fixed endpoint readouts; their evaluation on the source profile gives
the endpoint values. Even reflection constructs the conserving closure,
while the separated-boundary theorem classifies constant-preserving
competitors. These characterizations are not adjustable fitting parameters,
and their comparison classes must not be omitted from uniqueness claims.
In particular, additive information alone determines a multiple of the
negative logarithm; nonnegativity already supplies the regularity needed for
this classification, and the unit calibration at `exp(-1)` fixes that multiple.
Uniqueness throughout is at the equivalence level stated in each theorem,
not literal equality of all choices of coordinates or realizing maps.
For the least physical carrier, the commutant calculation makes this last
qualification exact: any unitary ambiguity is one basis phase on each simple
response block.

Declaration counts include named definitions, abbreviations, auxiliary lemmas
and theorems. They are not counts of manuscript theorems. A manuscript mapping
records the particular statement or clause supported by a Lean declaration;
several declarations may support one manuscript result. Full coverage requires
matching all premises and conclusions and completing the intervening construction.

## Gaussian observation windows and capacity-weighted energy

The arithmetic entry also exposes `GaussianWindowCapacity`. At observation
level `R`, the generated square spectrum is partitioned by `n^2 < R*L^2`.
The level-five instance uses the same Gaussian endpoint weights and central
character as the complete source. Visible and outside sector pairs add
exactly to the canonical endpoint pair. Their capacities and signed responses
are additive; coherent energy retains the full visible--outside cross term.
Every visible label is bounded by `ceil(sqrt(R)*L)`, and the visible pair
stabilizes once the natural prefix reaches that cutoff.
The window predicate is invariant under the joint prime occupation--scale
flip and transports under a prime birth with the same scale change `L/p` as
the Gaussian response. Restricting the original Gaussian weight and filtering
the generated labels produce exactly the same visible source. The windowed
prime-stage energy therefore obeys the signed old--return correlation ledger
with the transported scale and the strict boundary condition both retained.

`CapacityEnergyLedger` distinguishes coherent energy `E=B^2` from central
potential `V=B^2/C`. It proves `E=C*V`, including empty sources, and connects
the transverse-capacity algebra to the actual generated centre sectors.
For a genuine prime stage with old capacity `C` and return capacity `c`,
the exact energy increment is
`c*V_old + (C+c)*V_return - (C+c)*D_join`.
The returned source and the old source are combined before taking an
estimate; the actual natural-cutoff boundary is retained in the old state.
The relative-potential comparison likewise keeps its capacity factor:
`E <= 2*C*relativePotential`.

Outside the window, each Gaussian endpoint weight is at most `exp(-R)`.
The finite tail certificate displays its cardinal factor explicitly:
`abs(B-B_visible) <= card(outsideLabels)*exp(-R)`.
Using the actual outside capacity also certifies the complete energy error:
`abs(E-E_visible) <= C_outside^2 + 2*abs(B_visible)*C_outside`.
No fixed observation level is inferred from the arithmetic partition itself;
level five is a concrete member of this covariant observation family.

## Environment

The project pins Lean 4.34.0 and mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435` (the mathlib v4.34.0 release).
The dependency manifest must be kept with the proof sources. The Lake package
and Lean namespace retain the identifier `GeneratedFoundations`.

A fresh checkout requires Git, Python 3.10 or later, and the pinned Lean
toolchain. To retain the default directory used by the V5 integration, clone
the repository with
`git clone https://github.com/bookwormseagull1980/Lean-Formalization-of-Arithmetic-and-Basic-Physical-Interfaces.git Foundations-from-Minimal-Change`.
Select the pinned Lean toolchain with `elan` using `lean-toolchain`. Restore the
locked dependencies with `lake build`; do not update the dependency lock to
newer revisions. The full verifier below then checks every local target and
the transitive axioms. Its elapsed time depends on whether dependencies and
compiled objects are already available. A cached audit time is not a claim
about first-time installation or compilation.

For the complete source, build, and axiom audit, run
`python scripts/verify_foundations.py` from the repository root with the pinned
Lake executable on the search path, or supply `--lake-exe`. The verifier checks
all explicit local module targets and the library with Lake's `--no-build`
mode. If they are fresh, it proceeds directly to the complete declaration
audit. If Lake requests rebuilding (exit code 3), it builds every local module
in dependency order, one process at a time, followed by the library. Other
nonzero probe results fail verification. Both paths check the actual imported
dependency revisions, every collected public named declaration, and every
constant originating in a local module of the compiled environment. The
environment inventory includes private declarations, anonymous instances and
generated helpers; neither path skips the axiom audit.
Its `--source-only` option checks source coverage and locks without certifying
compiled proofs. Implicit introduction of undeclared variables is disabled.

This project is independent of the Lean 4.7.0 proof archive distributed with
the Coarse-Graining Genesis Framework V5. Neither archive's verification
status is a substitute for verification of the other.

The verifier uses only the Python standard library. To run its regression
tests, install `requirements-test.txt` and run `python -m pytest` from this
directory. These tests exercise the verification machinery, not the
mathematical proofs; compilation and the axiom audit are separate checks.

The public GitHub Actions workflow runs the same sequence on pushes and pull
requests to `main`: it installs the toolchain named by `lean-toolchain`, runs
`lake build` with `LEAN_NUM_THREADS=1`, installs the pinned Python test dependencies,
runs the verifier regression tests, and performs a complete compiled proof and
transitive axiom audit. The workflow keeps the resulting manifest and audit
log as run artifacts; its dependency and build caches only accelerate the run
and do not replace the locked source and manifest checks.

## Independent verification record

A complete successful run atomically writes `verification-manifest.json` in
this directory. `--manifest PATH` selects another JSON output. The record binds:

- Every local Lean source, the toolchain and dependency locks, the theorem
  index, and the verifier itself by SHA-256.
- The actual Lean and Lake versions and executable hashes, and the actual
  dependency commits with their tracked files checked for local changes.
- The full local build order, indexed declarations, and the transitive axiom
  set reported for every project-owned compiled constant, with its source
  module and declaration kind. Public named declarations retain their
  separate type and axiom checks.
- The generated audit probe, all named declaration signatures and the complete axiom log
  at `.lake/foundations-audit.txt` by SHA-256.

The current record and audit log are build artifacts, ignored by Git by default.
Release evidence is retained together in `verification/`: the manifest,
its complete audit log, and a relative-file hash inventory. Public records
use relative source paths and do not contain local installation paths. A source
change, an index or lock change, a verifier change, a changed tool or dependency,
or a missing or changed audit log requires fresh verification before that
record can be treated as current. Record presence alone is not a success check.
A different operating system may produce different executable hashes. A
reproduction therefore creates a new complete verification record for its
actual tools; it need not reproduce the original platform's binary hashes.

Use `python scripts/verify_foundations.py --check-manifest` from the repository
root (with the same Lake selection, and `--manifest PATH` if applicable) to
compare a saved record with the current sources, log, tools, and dependencies.
This runs version and dependency checks but does not build or rerun Lean's proof
audit. Its result is **record current** or a nonzero **stale or invalid** result,
not a new compiled-proof verification. A failed verification attempt never
publishes a new success record and does not replace the previous one; its exit
status remains failure regardless of any older record on disk.

The manifest is reproducibility evidence, not a signed attestation or protection
against deliberate modification of both records and logs. It does not certify
the semantic correspondence to a manuscript, the completion of all planned
proofs, or any physical calculation. This verifier neither reads nor updates
V5's numerical `run_manifest.json`. An independently verified proof package
does not make an old numerical run current.

## Relation to the numerical software

This repository is the sole maintained source of this proof library. The
Coarse-Graining Genesis Framework V5 refers to a fixed source snapshot through
`foundations-reference.json`; it does not maintain a second copy of these
proofs. Its optional `python scripts/verify_v5.py --foundations` entry invokes
this repository's verifier. Use `--foundations-project` or the
`FOUNDATIONS_PROJECT` environment variable to select its location, and
`--foundations-lake-exe` to select Lake when needed. The default checkout is
the sibling directory `Foundations-from-Minimal-Change`.

The V5 entry requires a newly completed audit, checks the resulting independent
record, and saves its identity and SHA-256 with the aggregate verification.
The record's scope remains the currently implemented library. Its presence
does not certify the full manuscript chain. Reading the aggregate status
checks the saved proof record, local proof sources, verifier and audit log;
it does not rerun compilation or inspect the current compiler installation.

The V5 reference pins proof sources, the Lean and Lake configuration,
dependency lock, theorem index and verifier. Downloaded dependencies and
build caches are not a second source of truth. An altered proof snapshot
must not be reported as the pinned one. Numerical-run hashes are not
refreshed merely because a proof check passed. For proof development without
physical reproduction or aggregate-record publication, use this repository's
`scripts/verify_foundations.py` directly.

## Proof boundaries

The root input retains exactly the explicit conditions of minimal unbiased
compositional change. Endpoint readouts and reflecting closure are internal
constructions. Their definitions, calibrations and comparison classes remain
visible in the supporting theorems; constructing them does not by itself
classify every possible readout of a Gaussian profile.
The physical source interface constructs the exchange-retained response,
least matter module, vacuum lift and elementary connector. It does not take
P4--P6 as an aggregate hypothesis. Intermediate conclusions must be proved
rather than stored as assumptions in the starting data. Comparison hypotheses
in classification theorems and compatibility with separately supplied local
bundle charts remain explicit.

Uniqueness statements specify their comparison class and equivalence relation.
The library does not use unproved mathematical axioms or proof placeholders.
An entry is reported as kernel-checked only after compilation. The automatic
axiom audit records its transitive logical dependencies. Review of its premises
and correspondence to the manuscript is a separate semantic assessment and is
not implied by a successful verification manifest.

The 18 October release snapshot passed compilation and the complete
compiled-environment axiom audit. That record covers 13,854 constants,
7,231 named type checks and 298 indexed claims. These counts have different
meanings; consult the index for the precise scope of each claim and use
`--check-manifest` to determine whether that record still matches the current sources.

The canonical root and its entire transitive local import closure have a
separate audit command:

```text
python scripts/verify_canonical_root.py --lake-exe <path-to-pinned-lake>
```

It builds the actual root module, includes every imported intermediate module,
and applies the same compiled-environment collector and axiom allowlist as the
whole-library verifier. The independent `canonical-root-verification.json`
records that exact source scope, both verifiers, the toolchain and dependency
fingerprints. Unimported research extensions remain in the whole-library
verification scope rather than being silently counted as checked by this run.

See [AXIOMS.md](AXIOMS.md) for the complete logical-axiom allowlist, the
expanded root conditions, the retained construction and classification
restrictions, and the limits of the current axiom collector. In particular,
absence of custom axioms does not establish that every downstream choice is
forced uniquely by the root datum. Independent external proof checking has
not been performed.

## Constructed physical interface

`GeneratedFoundations.CanonicalClosedWorld.generated` is the single
closed-world entry. It gives the conclusions at the canonical complex
orientation and uniquely fixed unit-covariance width without accepting another source object. Its
`physical_interface` field supplies the basic physical interface alongside,
but not as an assumption of, the single generated natural-number system and
its source closure. Coordinate-level parameterized lemmas are proof machinery,
not public alternatives to this generated world.

The same generated law and uniquely fixed width determine the source throughout.
The unit-information endpoint and peak-equivalent width are evaluated from its
Gaussian profile. The actual source average, transported through the reflecting
isometry, is identified with the constructed Neumann evolution. Conservation
and boundary properties are proved outputs. The comparison theorem for
separated homogeneous boundary conditions retains its stated acceptance of
constants; it is not an additional assumption of the root construction.

| Construction | Principal declarations | Scope |
|---|---|---|
| Exchange-retained response | `SourceSplitResponse.generated_split`, `retainedEquiv` | The actual pre-exchange response commuting with exchange is exactly the block algebra on the symmetric and alternating carriers; the original tensor action is intertwined with the joint response. |
| Source frames | `SourceFrameConstruction.generated_frames`, `relativeTransition_cocycle`, `relativeTransition_unique` | Colour, phase and pseudoreal frame classifications; relative transitions constructed from source frames satisfy the cocycle and act uniquely on the common matter carrier. |
| Least matter | `SourceInternalResponse.least_chiral_pair`, `Conclusions.least_source`, `Conclusions.least_classification` | The canonical faithful module attains the least dimension; arbitrary least faithful representations are unitarily equivalent to it, including the paired chiral action. The intertwiner itself is not asserted to be unique. |
| Vacuum and charge | `SourceInternalResponse.source_internalResponse` | Zero-argument output of the canonical source: actual vacuum stabilizer, continuous source lift, primitive charge classification, six-element gauge kernel and faithful effective action. |
| Generated gauge group | `SourceGeneratedGaugeGroup.sourceGeneratedGaugeGroup`, `sourceFactorClosure_eq_generated`, `generatedGaugeGroup_least` | The determinant-one changes of the generated colour carrier, the group generated by the source-spin axes and the exhausted phase circle generate the full intrinsic operator group. Its exact six-element kernel gives the effective quotient `(SU(3) x SU(2) x U(1)) / Z6`; the descended scalar action is a colour singlet, the defining weak doublet and has phase character one half. |
| Elementary connector | `SourceScalarConnector.canonical_elementary`, `elementary_iff_unique_doublet` | The canonical family satisfies independent-source naturality and reversal reality; every connector in that comparison class has a unique doublet coordinate. Its original Gaussian realization and covariance are included. |
| Relativistic algebraic interface | `SourceHermitianReadout.coordinatesEquivHermitian`, `SourceLorentzCarrier.posSemidef_iff_futureCone`, `coordinateTransform_futureUnit_iff` | All Hermitian two-by-two matrices have unique four-real coordinates. Their determinant has signature `(+---)`, their positive cone is exactly the closed algebraic future cone, determinant-one congruence preserves the form, and the generated future unit has the special-unitary stabilizer equation. |
| Four-dimensional gauge dynamics | `SourceFourDimensionalGaugeKinematics.sourceFourDimensionalGaugeProperties`, `SourceFourDimensionalYangMills.sourceFourDimensionalYangMillsProperties` | The Hermitian readout supplies the four coordinate directions. The generated colour directions exhaust the skew-Hermitian traceless `3 x 3` algebra; connection curvature, local covariance, the source-normalized positive colour form and its Lorentz contraction are proved without adding a lattice or gauge group. |
| Internal Yang--Mills response | `SourceColourAdjointCasimir.adjointCasimir_generator`, `SourceInternalYangMillsResponse.properties` | The explicit generated colour matrices give adjoint Casimir `3`; the endpoint ratio gives `L_c=sqrt(pi)`; and the actual `(4,2)` source carrier gives dimension `15`, Casimir `16`, the unique normalized affine drive and `120` colour-connection coefficients. |
| Generated Yang--Mills action, differential Hessian and spectral gap | `SourceHaarCurvatureTrace.action_eq_trace`, `SourceHaarYangMillsHessian.action_secondDeriv`, `SourceOneFormCoclosedSpectrum.coclosedHilbertBasis`, `CanonicalYangMills.generated` | The nonlinear action is evaluated on the original Haar one-form fields; its curvature term equals the integral of the actual colour-matrix curvature trace. Differentiation gives the radial block and the source curl-squared connection block, with zero mixed second derivative. The weak divergence kernel has a complete basis of differentiated source eigenfields. The original-field Hessian has a unique self-adjoint closure, its full weighted-square domain, an attained positive bottom and the corresponding finite-occupation Fock gap. Every colour and every nongauge field direction is retained. |
| Newton mass calibration | `CanonicalYangMillsUnits.generated`, `CanonicalYangMillsUnits.gapMass_sq`, `CanonicalYangMillsUnits.gapMass_unique` | The dimensional readout takes only a positive Newton constant; the IR radius has already been generated. In the stated reduced-Planck convention, the emergence mass squared is `1/(16*pi*G_N)` and the unique positive gap mass squared is `gapSq/(16*pi*G_N)`. The calibration cancels from their ratio and does not enter the action, condensate or operator. |
| Canonical Yang--Mills response | `CanonicalYangMills.generated` | The generated IR radius is `sqrt(2*pi)` and exceeds the critical radius. Its unique positive condensed amplitude, original-Haar-field action, self-adjoint differential response Hessian, attained positive spectral bottom and finite-occupation gap are outputs of a theorem without realization arguments. |
| Geometric volume and colour covariance | `SourceProjectiveVolume.roundMeasure_total`, `SourceGeneratedYangMillsGap.transverseCovarianceAction_eq`, `CanonicalYangMills.sourceColourContraction` | The actual ambient polar measure and two-sheeted quotient give `pi^2*L^3`. Isotropic variance with the generated total intensity is fixed across the 24 spatial-colour components; the two transverse directions and the actual adjoint double commutator compute the connection response shift. |
| Orientation reversal of the nonlinear response | `CanonicalYangMills.responseAction_orientation_reverse` | Conjugating the complete connection jet preserves its curvature trace, connection norm and common radial response. Together with the source orientation classification, this identifies the response in the two orientation presentations. |
| Differentiated source spinor | `SourceSpinorCovariantDerivative.polynomialDirac_eq_contraction`, `SourceSpinorHaarBlock.differential_normalizedSynthesis`, `SourceSpinorClosedSpectrum.closedDirac_unique`, `SourceSpinorResolvent.spectrum_half_integers` | The Koszul formula computes the spin connection from the original trace-metric source frame. Clifford contraction gives the actual field differential. Its complete Haar basis yields a unique self-adjoint closure on the full weighted-square domain, spectrum `+/- (k+3/2)` and a full-domain squared-norm lower bound `9/4`. Bounded two-sided resolvents exclude additional continuous and residual spectrum. |
| Both central spinor sectors | `SourceSpinorParitySpectrum.closedSectorDirac_is_restriction`, `SourceSpinorParityResolvent.spectrum_labels` | The actual central pullback determines two closed field subspaces. Their Dirac operators are restrictions of the same original operator on the entire closed domain. In the positive central sector the positive branch has even `k` and the negative branch odd `k`; the other sector reverses these parities. Complete sector bases and bounded two-sided inverses prove presence and exhaustion of both spectra. |
| Differentiated projective TT tensor | `SourceTensorCovariantDerivative.rough_coefficientTensor`, `SourceTensorTTBlock.ttRough_eq_curl_square`, `SourceTensorTTClosedSpectrum.closedRough_unique`, `SourceTensorTTSpectrum.spectrum_labels` | The original nine-component tensor Haar space supplies the closed weak kernel of symmetry, trace and covariant divergence. Koszul differentiation yields `rough = curl squared - 3`. Its complete differentiated basis gives the unique self-adjoint rough closure and full weighted-square domain. Nonzero polynomial witnesses and bounded two-sided resolvents prove exactly the eigenvalues `k(k+2)-2`, for even `k >= 2`, with attained bottom `6` in the unit trace-metric frame. No tensor branch or gap is an input. |
| TT carrier and response endpoint | `SourceTransverseTraceless.sourceTransverseTracelessProperties`, `SourceTensorResponseEndpoint.sourceTensorResponseEndpointProperties` | Symmetry, transversality and vanishing trace determine a unique plus/cross decomposition and a two-dimensional TT carrier. The mass-weighted kernel has the unique maximum `4/27` at `y=1/3`; a positive fixed spectral coefficient has the unique endpoint `c=27A/4`. |
| Linear tensor gravity | `SourceLinearizedGravity.sourceLinearizedGravityProperties`, `generalTensorOperator_coefficients_unique` | Gauge annihilation, transversality and unit TT normalization uniquely select the five coefficients of the local two-derivative linear Einstein operator. It annihilates pure gauge tensors, reduces to `Q² I₂` on the derived TT carrier, has a unique sourced solution away from zero momentum and an exact positive-residue simple pole at `Q²=0`. |

The common root, its physical component and all local dependencies have
compiled successfully. The complete axiom inventory reports only `propext`,
`Classical.choice` and `Quot.sound`; the common root depends on exactly these
three. `AXIOMS.md` describes the inventory, including generated
recursion implementation entries, and the limits of this evidence. The
public entry exports the common root, while the physical component itself does
not import arithmetic constructions.
The relative-frame construction does not claim existence of arbitrary
nontrivial bundles.  Field and jet values in the gauge and tensor modules are
variables of configuration spaces on the generated four-carrier; they are not
additional fields of `MinimalUnbiasedChange.Datum`.

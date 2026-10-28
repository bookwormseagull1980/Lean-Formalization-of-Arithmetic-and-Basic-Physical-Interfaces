# Logical axioms and mathematical assumptions

This document applies to the separately pinned `GeneratedFoundations` library.
It distinguishes logical axioms, hypotheses of mathematical theorems, and
definitions of the objects being constructed. Absence of custom Lean axioms
does not imply absence of mathematical hypotheses or uniqueness among all
possible constructions.

## Logical axioms

The verification policy permits exactly these transitive axiom dependencies:

| Lean name | Statement or meaning |
|---|---|
| `propext` | Logically equivalent propositions are equal: `(P ↔ Q) → P = Q`. |
| `Classical.choice` | An element may be selected from any nonempty type: `Nonempty α → α`. |
| `Quot.sound` | Related representatives determine equal elements of the primitive quotient: `r a b → Quot.mk r a = Quot.mk r b`. |

These are the standard classical foundations used by this library and mathlib.
In the pinned Lean source, `propext` is declared in `Init/Core.lean` and the
other two are declared in `Init/Prelude.lean`. Function extensionality and
classical excluded middle are derived results, not additional axioms in this
list. Inductive types, computation, universes and proof irrelevance belong to
Lean's underlying type theory; `#print axioms` is not a specification or
independent validation of that type theory or its implementation.

The completed audit on 18 October 2026 covers all 273 local modules,
13,854 compiled-environment constants, 7,231 named type checks and 298
indexed claims. The constants include private declarations, anonymous
instances and generated helpers; they are not 13,854 manuscript theorems.
The full collector uses `Lean.collectAxioms`; named declarations also have
explicit `#print axioms` reports checked against that inventory. Every
reported transitive axiom belongs to the three-element allowlist above.
There are no local constants of axiom kind and no `sorryAx` dependencies.

The completed canonical-root audit on 19 October 2026 covers all 346 local
modules in the zero-argument entry's actual import closure, 16,584
compiled-environment constants, 8,490 named type checks and 342 indexed
claims. It reports zero unsafe constants, zero local axioms and 25
compiler-generated partial recursion implementations. Every transitive axiom
is in the same three-element allowlist. The root record is
`canonical-root-verification.json`, with the complete declaration inventory
in `.lake/canonical-root-axioms.txt`. This scoped audit includes all
intermediate imported modules, whether indexed or not; it makes no claim
about research modules not imported by the root.

`GeneratedFoundations.CanonicalClosedWorld.generated` depends on
exactly `propext`, `Classical.choice` and `Quot.sound`. Its module and all
dependencies passed compilation. Its conclusion includes the constructed
common-source geometry, the single natural-number branch with its complete
history and phase fibres, intrinsic history observables, exact whole-history
transport and detailed-balance dynamics, and the complete basic physical
interface specified below. The current root also includes native prime
occupations and parity, the finite signed occupation and endpoint ledgers,
complete finite history/phase observations, the connected Hermitian response,
the actual reaction Hessian, its finite evolution and its orthogonal Hodge
decomposition. These are fields of the proved mathematical interface, not
additional arguments to the root. `GeneratedFoundations.ResearchExtensions`
also assembles these constructions with the separate finite residue Fourier
and recovery-kernel modules. Their dependency scope is determined by actual
imports rather than by the name of the aggregate entry.

The canonical-root evidence is its separately named record and audit log
above, bound to the source, index, dependencies, verifier scripts and
toolchain by their recorded fingerprints. Re-running
`scripts/verify_canonical_root.py` regenerates that evidence. The
whole-library verifier instead writes `verification-manifest.json`; its
`--check-manifest` option checks the freshness of that separate record. A
successful record cannot certify subsequently changed sources merely
because the file still exists.

The source checker rejects explicit `sorry`, `admit`, and `axiom` declarations.
The compiled audit rejects any transitive axiom outside the three above,
including `sorryAx`, custom mathematical axioms, and compiler-evaluation
axioms. Source traversal of the current library found no such placeholders,
custom axiom declarations, `native_decide`, or `unsafe` proof implementations.
That source result alone does not substitute for a completed compiled audit.

The 18 October whole-library environment has zero `unsafe` flags and 29 `partial` flags.
All 29 flagged constants have the suffix `._unsafe_rec`; the corresponding
public definitions have both flags false. The full names are obtained by
appending that suffix to each name in the following table, under the common
namespace `GeneratedFoundations`:

| Namespace | Public definitions with generated recursion implementations |
|---|---|
| `Analysis.FinitePoissonOverlap` | `falling` |
| `Analysis.HistoryFrontier` | `pathLength`, `registerNumber`, `scheduledPeak` |
| `Geometry.SourceFiniteControlDiffusion` | `IndependentSample`, `independentLaw`, `operationProduct` |
| `Geometry.SourceOperationWalk` | `Sample`, `sampleLaw`, `sampleProduct`, `walkLaw` |
| `Operations.HermiteFamily` | `raw` |
| `Operations.HermiteSpan` | `monomialGaussian` |
| `Arithmetic.CompleteHistory` | `directoryMass`, `flatWeight`, `toExpression` |
| `Arithmetic.CompleteHistoryGeometry` | `addCount`, `leafCount`, `mulCount`, `orientationScore`, `reflect` |
| `Arithmetic.CompleteHistoryTransport` | `internalEnergy` |
| `Arithmetic.ReducedExpression.RawExpr` | `depth`, `normalize`, `upToDepth` |
| `Arithmetic.ReducedExpression.Target` | `interpretRaw` |
| `Arithmetic.ReducedExpression` | `instDecidableEqRawExpr.decEq`, `instReprRawExpr.repr`, `numeral` |

These are compiler-generated implementations of the ordinary structurally
recursive source definitions, not handwritten `partial` declarations or
unfinished proofs. In the pinned Lean source,
`Lean/Elab/PreDefinition/Structural/Main.lean`, `structuralRecursion` first
registers the translated definition and then calls `addAndCompilePartialRec`.
That function in `Lean/Elab/PreDefinition/Basic.lean` creates names via
`Compiler.mkUnsafeRecName` and marks the additional implementations
`DefinitionSafety.partial`. The original definitions remain the safe logical
definitions. The audit includes these additional constants and records their
flags and transitive axioms without treating their recursive implementation
bodies as 29 further safe definitions. Their reported axioms are exactly
the three standard axioms above. Thus the source scan has no handwritten
`partial`, but the compiled inventory does not have zero `partial` entries.

Use of `noncomputable`, `Classical.choose`, an orthonormal basis, or an inverse
selected from a proved existence theorem does not insert an unproved
mathematical assertion. It does mean that an executable extraction algorithm
has not necessarily been furnished. Equivalence-class uniqueness must also
be distinguished from uniqueness of the selected witness or coordinates.

## The root construction

The single public `CanonicalClosedWorld.generated` theorem takes no argument.
Internally, `Source.CanonicalRoot.generated` constructs the canonical minimal
carrier and `Source.MinimalUnbiasedChange.fromMinimalCarrier` equips it with
the unique compositional law. The implementation package has the fields:

| Field | Mathematical content |
|---|---|
| `change` | A nonzero finite-dimensional real inner-product carrier, a nontrivial compact connected Lie group, and a continuous faithful irreducible orthogonal action. The declaration also records the topology, smooth charts, Hausdorff and second-countability structures used by the construction. |
| `minimal` | Least carrier dimension among all data in this explicitly stated comparison class. |
| `law` | A measure family on the trace Hilbert line constructed from that carrier. |
| `compositional` | Probability normalization at positive parameters, convolution composition, exact square-root scaling, finite second moment at unit parameter, and unit covariance for every real linear observation. |

The full declarations are in `Source/MinimalCarrier.lean`,
`Source/MinimalUnbiasedChange.lean`, and
`Probability/GeneratedTangentLaw.lean`. These are the mathematical contents
of minimal unbiased compositional change in this formalization. They are not
additional logical axioms, and they are not consequences of the phrase
"minimal change" without its mathematical definition. Carrier minimality
alone is not claimed to imply the compositional law conditions.

The Gaussian formula, endpoint values, Neumann boundary operator, spectra,
arithmetic operations and physical interface conclusions are not root fields.
Existence of a compatible root datum is proved. Law uniqueness is proved at
strictly positive parameters on a fixed generated carrier; equality of the
entire real-indexed family at unrestricted nonpositive parameters is not
claimed.

The geometric, physical and common-root output records contain neither an
orientation nor a width parameter. Unit covariance fixes the positive
dimensionless width to one and the original complex rotation supplies the
canonical presentation orientation. Individual scale and reversal lemmas
quantify over comparison variables; no parameterized aggregate world theorem
is retained.

## Internal definitions and comparison classes

Constructing a particular object from root data and classifying competitors
within a specified class are different statements. Both can be rigorous.
The following definitions and comparison classes have distinct roles even
when they are not arguments of the root theorem:

| Construction | Definition or comparison in the formal statement |
|---|---|
| Local information endpoint | Additive continuous information is calibrated at `exp(-1)`. Uncalibrated additivity determines a scalar multiple of the negative logarithm. |
| Global correlation width | The width is the normalized total mass divided by the peak of the Gaussian profile. Uniqueness of invariant normalized mass does not classify every conceivable width functional. |
| Reflecting closure | Even reflection constructs a constant-preserving closure. The boundary classification compares separated homogeneous boundary conditions admitting constants; it does not classify all self-adjoint extensions. |
| Projective internal observation | The projective quotient retains centre-invariant observations. The complete source observation system can detect the central sign. |
| Dimension three | The constructed source sphere has actual real tangent dimension three. Separately, `SourceSphereCapacity` classifies the exact scalar spherical multiplicity and affine energy-capacity formulas for dimensions at least two, including the even-degree class. These are distinct from the manuscripts' general Weyl-law inference for a closed manifold realizing the complete square-capacity spectrum; that newer argument is not part of the current formalized statements. |
| Exchange-retained response | The retained algebra is the part commuting with exchange. Its block classification does not state that every pre-exchange response commutes with exchange. |
| Least matter realization | Dimension eight and unitary equivalence are classifications of faithful adjoint-compatible realizations of the specified joint response algebra. For two such realizations, one unitary intertwines their actions, projections and grading; after fixing that unitary, every source operator has a unique compatible transport. The unitary itself is not asserted to be unique. |
| Two chiral sectors | `SourceCliffordChirality` constructs the grading from source Clifford products, identifies the real and complex even algebras, classifies the primitive central projections of the real even algebra, and identifies their two-dimensional spinor ranges. Its Hermite intertwining and range theorems identify the corresponding actual eight-dimensional matter sectors. These results are connected to the compiled and audited root output. |
| Elementary connector | Naturality and reversal compatibility define the comparison class. The doublet coordinate is unique for each connector in that class; the theorem does not select one value of the doublet or exclude multiple copies. |
| Local frames | `SourceColourPhase` factors every unitary colour frame pointwise into a circle phase and an SU(3) factor; their opposite cube-root changes describe the finite central ambiguity. This does not identify the determinant phase with the common matter phase, select a global continuous cube root or provide a determinant-bundle trivialization. Relative transitions from supplied frame functions obey the cocycle law. The factorization is connected to the compiled and audited root output. |
| Geometric scale | `SourceEndpointCasimir.radius` is another notation for the already generated `irEndpoint`, not an independently supplied length. The actual polar amplitude at this radius has norm equal to that same IR length, and its trace metric supplies the radius-squared angular factor. The Gaussian half-generator coefficient follows separately from its variance normalization. |
| Four-dimensional gauge configurations | The Hermitian source readout supplies four real coordinates and the generated effective group acts faithfully on the existing matter carrier. Connection values, first jets and local gauge two-jets are universally quantified configuration variables. The colour Lie algebra, curvature law, local covariance and quadratic density are proved from the generated colour basis; none is a field of the root datum. |
| Lorentz positive cone | The self-adjoint part of the generated two-mode matrix corner has four real coordinates. Its determinant is the Lorentz quadratic form, and its positive-semidefinite matrices are proved to be exactly the closed algebraic future cone. Determinant-one congruence, the future-unit stabilizer equation and the central-sign action are derived on this same carrier. |
| Internal Yang--Mills response | The critical radius is the already generated IR/UV endpoint ratio. The long-root dimension and Casimir come from the actual source left--right representation, while the adjoint Casimir is computed from the explicit colour matrices. The affine drive, coefficient count and feedback normalization therefore add no independent root field. |
| Radial/coclosed mass blocks | The finite Gaussian intensity score fixes the radial metric normalization. The radial and scalar constant blocks are one-dimensional source restrictions with a unique generator-preserving unitary. Their common scalar evolution is intertwined, and the positive condensed response supplies a positive bottom for the radial block and every coclosed connection shell. |
| Transverse--traceless carrier | `IsAxisTT` is the intersection of symmetry, transversality and trace-zero constraints on the generated three spatial coordinates. The plus/cross representation, its uniqueness and real dimension two are proved consequences of those constraints rather than a supplied two-state type. |
| Tensor response endpoint | The per-leg logarithmic mass derivative of `q⁴/(q²+m²)²` is `y(1-y)²`, with unique maximum `4/27`. The finite kinetic quadratic insertion in the original positive-precision Gaussian has twice its variance equal to the rational kernel sum; the actual eight-branch coefficient is also its Gaussian-weighted integral. The endpoint formula `c=27A/4` is unique under the existing matching rule and invariant under a common positive calibration of both sides. The extremum theorem does not by itself select that matching rule or identify a spectral integral with its mass derivative. The positive coefficient and calibration variables are comparison variables, not new root fields. |
| Linear gravity operator | Within the complete local five-coefficient symmetric tensor class with two momentum factors, pure-gauge annihilation, transversality on symmetric fields and unit TT normalization uniquely select coefficients `(1,-1,1,1,-1)`. The selected operator, its TT reduction, sourced inverse away from zero momentum and simple massless pole are root outputs on the generated four-carrier. |

These definitions and comparison classes introduce no numerical fitting parameters. Naming them as
definitions, rather than placing them in a theorem's argument list, does not
prove that no other restriction or construction is possible. Claims of
necessity must cite the corresponding derivation or comparison theorem.
Records named `Conclusions` are output records only when their fields are
filled by proved declarations; their names alone provide no guarantee.

This inventory does not authorize extra independent principles. If a claimed
result requires a restriction to follow from the root datum, disclosing the
restriction is insufficient: its derivation and its use in the actual
construction must be supplied. Conversely, a property already proved for a
constructed object must not be misreported as an assumption merely because
it also occurs in the classification of competitors. The source-generated
reversal-real elementary connector is one such example.

For the root-to-interface claim, each intermediate hypothesis must therefore
have a proved source: the fixed root datum, a property of the constructed
object, or a transport along a proved equivalence. An unresolved hypothesis
may remain in an auxiliary conditional theorem, but that theorem does not
complete the claimed root-to-interface implication until the hypothesis is
discharged. Moving it into a structure field or a definition does not
discharge it. In particular, the root datum must not be enlarged with the
desired P4--P6 conclusions to make the final theorem type-check.

Uniqueness also requires an explicit comparison relation. It is legitimate
to compare representations of the same generated algebra, or observations
at the same stated resolution. If a claim instead says that the root datum
forces that resolution, a least-realization requirement, or a metric
calibration between independently defined quantities, the corresponding
necessity must be proved separately. The
classification of objects already satisfying the requirement does not
prove that necessity.

In particular, `radius b` and `irEndpoint b` denote one length. Likewise,
`uvEndpoint b` is the local unit-information resolution length itself.
Neither identity calls for an additional matching hypothesis. The local and
global lengths are distinct functionals of the same Gaussian source; their
calculated ratio is `sqrt pi`. The amplitude-norm and endpoint-functional
identities are included explicitly among the geometric root theorem's
outputs and are covered by the complete compiled audit described above.

These identities concern the Gaussian correlation window's IR **edge**,
`sqrt(2*pi)`.  They do **not** identify that edge with the V5 finite-response
TT endpoint `kL`: the TT endpoint is the root of `A(L)=4/27`, it lies strictly
below the edge, and at the edge the TT sum is about `0.147374 < 4/27`.  The
zero-argument `CanonicalYangMills` theorem is the IR-edge model; the V5 TT
model is the separate, certificate-conditional `CanonicalYangMillsTT`.  The
critical ratio `sqrt(pi)` is a third object, not an edge and not `kL`.

The arithmetic formalization uses Lean's existing natural numbers for
indices, recursion and auxiliary models. The final source modes are also
defined intrinsically from the actual operator and then identified with
those models. This verifies a generated arithmetic system within Lean's
mathematical foundations; it does not reconstruct the `Nat` type in Lean's
metatheory without prior natural-number machinery. Likewise, the positive
Gaussian amplitude is a constructed representative, not a uniqueness
theorem for every complex amplitude having the same squared modulus.

The reduced-expression extension adds no root field. Its raw ordered syntax
uses only zero, one, modulation and cascade. The least congruence removes only
the two additive-unit, two multiplicative-unit and two absorbing-zero laws.
Structural normalization has a unique reduced result; evaluation is onto the
already generated native modes, each value fibre is finite, and the evaluation
quotient is canonically their semiring. Comparison targets in the initiality
theorem are universally quantified test objects, not assumptions stored in
`MinimalUnbiasedChange.Datum`. The Gaussian statement formalized here is
constancy of the existing scalar response on an evaluation fibre; it adds no
probability weight or fibre dynamics.

The physical component of the common root theorem constructs the source
response, Hermitian determinant, four-dimensional gauge, TT response and
linear tensor-gravity interfaces. Its exact conclusion is the
`physical_interface` field of `CommonFoundation.Conclusions`.

The source output records now include the Clifford-sector identifications,
their actual Hermite ranges, the pointwise colour factorization and the
fixed-unitary operator-transport statements above. The physical root output
also contains the generated gauge-group certificate: the three source factor
families generate the intrinsic operator group minimally, its kernel is the
computed six-element central subgroup, and the scalar doublet descends to the
effective quotient with its colour, weak and phase characters. They are filled by
construction declarations, not added to `MinimalUnbiasedChange.Datum`.
Their compilation and transitive axiom checks have passed. This does not
prove that every conceivable continuation is minimal,
exchange-preserving or centre-invariant; those would be different claims.

The root record additionally contains the four-dimensional colour
Yang--Mills certificate, the derived two-polarization TT carrier, the `4/27`
response extremum, positive-endpoint uniqueness and the uniquely selected
linear Einstein tensor operator with its simple massless pole.  These modules
quantify over field configurations and momenta after the carrier is generated;
they do not enlarge `MinimalUnbiasedChange.Datum`.

The concrete source matter bundle is also a root output: its base is the already
generated Hermitian four-carrier and its fibre is the complete source matter
Hilbert space. Its coordinate uniqueness, unitary frame transformations,
transition cocycle and component compatibility are proved internally. Generic
bundle comparison lemmas are not hypotheses of this construction.

The nonlinear tensor density is constructed on that same coordinate carrier.
Inside the first-order quadratic-plus-cubic comparison class with the existing
unit linear normalization, affine-dilation covariance fixes the cubic
coefficient uniquely. The proof differentiates the density and computes its
residual as `2*(c-1)*eta.R_quadratic`; a torsion-free configuration with
`eta.R_quadratic=-2` detects every coefficient other than one. This result
does not postulate the residual to be zero. It covers affine dilation, not
the full nonlinear metric variational system.

The generated Yang--Mills response is part of the same root output. The
endpoint ratio fixes the critical radius; the `(4,2)` source carrier and
explicit colour matrices fix the long-root and adjoint Casimirs; and their
normalized response determines the unique positive condensed amplitude. The
nonlinear curvature is retained before variation. The Haar-field curvature
norm is proved equal to the integral of the actual colour-matrix curvature
trace, with the source-derived colour normalization. Its common radial--connection
response has zero mixed Hessian, while the radial coefficient is exactly the
source intensity-score variance times the complete restoring curvature. The
projective volume is computed from the ambient Lebesgue polar measure and
the actual two-sheeted source quotient. The source-intensity normalization
uniquely fixes the isotropic variance on the three-by-eight connection
components. Two transverse spatial directions and the actual colour
double commutator compute its quadratic covariance response. Complex
conjugation transports both connection values and derivatives, preserves
the nonlinear curvature trace and leaves the full local source response
unchanged under orientation reversal. The complete coclosed colour one-form
space contains both source vector branches,
their full multiplicities, every positive odd degree and all eight colour
directions. The finite operator is identified with the differentiated source
curl-squared operator on every coefficient row before closing its graph.
It has a unique self-adjoint closure with an explicit weighted-square domain.
The radial direct sum has an attained,
strictly positive spectral bottom on the condensed branch, and finite bosonic
occupations have a unique vacuum and the same attained non-vacuum gap. No
critical scale, gauge coupling, kinetic coefficient or dimensionless mass
value is added to the root datum. `CanonicalYangMillsUnits.generated` attaches
mass units at that same generated IR radius. Its sole dimensional argument is
a positive Newton constant. In the stated reduced-Planck convention, the
emergence mass squared is `1/(16*pi*G_N)` and the gap mass squared is the
already attained dimensionless bottom divided by `16*pi*G_N`; positivity
selects the mass uniquely. No radius is supplied at this interface, and the
calibration enters neither the carrier, action, Hessian, condensate nor
dimensionless gap theorem.

The source spinor differential uses the same trace-orthonormal frame.
Its Koszul coefficients determine the spin connection; Clifford contraction
derives the constant term `3/2`. The first-order operator is intertwined with
actual matrix-coefficient fields before diagonalization. The differentiated
degree-`m` block has kinetic branches `m` and `-(m+2)`, with dimensions `m+2`
and `m`, respectively. Completeness is proved in the original two-component
Haar space. The finite differential core has a unique self-adjoint closure,
an explicit full weighted-square domain and a cutoff-independent squared-norm
lower bound `9/4`. A bounded two-sided inverse exists at every complex value
outside the two half-integer towers. Thus the complete spinor spectrum is
derived from the source differential rather than supplied as branch data.

The rank-two tensor construction acts on the original nine-component
projective Haar field. Symmetry, trace and the computed covariant divergence
define its closed weak TT kernel. The actual Koszul connection acts on both
tensor indices. Its differentiated curl and rough restrictions satisfy
`rough = curl squared - 3`; connection energy excludes the inadmissible low
branch. The complete original-field basis then gives a unique self-adjoint
rough closure and its full weighted-square domain. Actual nonzero polynomial
witnesses establish branch presence, and bounded two-sided resolvents exclude
any additional spectrum. The complete spectral set is `k(k+2)-2` for even
`k >= 2`, with attained lower edge `6` in the unit trace-metric frame.
The separate representation-label multiplicity formula is not used to
define or diagonalize this operator. This result is bundled in the same
zero-argument physical and common-root conclusions.

The actual generated even scalar shells also determine the complete
dimensionless conformal response. Its continuity, strict increase,
unboundedness and positive curvature are theorems. Consequently every positive
source drive has one positive balance, and that balance produces a positive
normalized radial gap which is the lower bound of the complete even scalar
tower and is attained by its constant shell. The unit of the generated
dimensionless response coordinate selects one canonical balance and gap. No
coupling, reference radius, kinetic normalization, field-spectrum table or
mass-gap value is a field of the root datum.

The dimension statements refer to different carriers: the initial real
change plane has dimension two; the constructed angular tangent fibres have
real dimension three; adjoining the radial amplitude gives real dimension
four; the symmetric-square colour carrier has complex dimension three.
The connected response rank of a two-level corner is also three, by the
separate rank formula `n^2 - 1`. Equal numerical dimensions do not identify
these spaces. In the arithmetic manuscript, coefficient capacity is defined
before any geometric realization, and its Weyl dimension proposition is
conditional on a common complete Laplace realization. No such realization
is inserted into the arithmetic root datum.

## Audit and independent checking

Run `scripts/verify_foundations.py` from the repository root, using the pinned
Lake executable. A successful full run builds or checks freshness of every
local module, checks declaration types, prints their transitive axiom
dependencies, rejects unexpected axioms, and binds sources, dependencies,
tools, index and saved audit log to one verification manifest.

The audit retains a `#check` for every collected named declaration and uses
ordinary type display, avoiding expansion of implementation-level implicit
instances. Display settings do not change the checked declarations or their
axiom dependencies. These printed signatures aid review; they are not a
proof export. Kernel checking is supplied by the module builds.

The collector checks ordinary publicly accessible named declarations and
indexed claims, then imports all declarations of each local module and
enumerates its constants from the compiled environment. This second inventory
includes private declarations, anonymous instances and generated helpers. It
records each constant's originating module, kind, safety flags and transitive
axiom dependencies, and requires a complete inventory before publishing a
successful manifest. The inventory is an audit through the pinned Lean
implementation; it is not an independently implemented kernel check.

The runner forwards named-check and environment-audit progress when received.
Lean can buffer these messages and render declaration signatures lazily;
their timestamps therefore do not measure the full wall-clock cost of
rendering and output. The runner uses one-pass log parsing and module counting
while preserving every named check and full-environment record. A timeout
terminates its own process tree, preserves a marked incomplete log and does
not publish a successful manifest.

The independent verifier, root-scope and index regression tests pass 102 cases. Their mocked
compiler responses test the verification machinery, including rejection of
incomplete inventories and unexpected axioms. They are not 102 Lean proof
checks. V5's external-library integration tests are maintained separately in
the numerical software repository. A standalone `example` that leaves no environment constant is checked
during module compilation; it is not counted as an enumerated declaration.

`--source-only` certifies neither compiled proofs nor their axiom dependencies.
`--check-manifest` checks the saved record's freshness; it does not rerun the
proof checker. A compiler resource limit changes how long proof elaboration
may run, not which propositions the kernel accepts.

The declaration-local checking options are listed below. Paths are relative
to `GeneratedFoundations/`; line numbers locate this source snapshot. Each
listed occurrence uses `in` and applies to one declaration.

| Source | Line | Option and value |
|---|---:|---|
| `Spectral/CircleNormalization.lean` | 166 | `maxHeartbeats 800000` |
| `Geometry/SourceDirectionalStep.lean` | 78 | `backward.isDefEq.respectTransparency false` |
| `Operations/FiniteHermiteCornerExponential.lean` | 91 | `backward.isDefEq.respectTransparency false` |
| `Operations/SourceSpinCornerFlow.lean` | 86 | `backward.isDefEq.respectTransparency false` |
| `Source/CharacterDifferential.lean` | 64 | `backward.isDefEq.respectTransparency false` |
| `Source/CharacterDifferential.lean` | 113 | `backward.isDefEq.respectTransparency false` |
| `Source/CharacterDifferential.lean` | 132 | `backward.isDefEq.respectTransparency false` |
| `Source/OriginalLieFlow.lean` | 45 | `backward.isDefEq.respectTransparency false` |
| `Source/OriginalLieFlow.lean` | 64 | `backward.isDefEq.respectTransparency false` |
| `Source/OriginalLieFlow.lean` | 126 | `backward.isDefEq.respectTransparency false` |
| `Source/RepresentationDifferential.lean` | 96 | `backward.isDefEq.respectTransparency false` |
| `Spectral/PositiveOperatorTrace.lean` | 64 | `backward.isDefEq.respectTransparency false` |
| `Physical/SourceGeneratedRadialVariation.lean` | 30 | `backward.isDefEq.respectTransparency false` |
| `Physical/SourceGeneratedRadialVariation.lean` | 88 | `backward.isDefEq.respectTransparency false` |
| `Geometry/SourceSpinorConnection.lean` | 44 | `maxHeartbeats 1600000` |
| `Geometry/SourceTensorCovariantDerivative.lean` | 176 | `maxHeartbeats 800000` |
| `Geometry/SourceTensorCurl.lean` | 53 | `maxHeartbeats 1600000` |
| `Geometry/SourceTensorRoughIdentity.lean` | 97 | `maxHeartbeats 800000` |
| `Geometry/SourceTensorSpectralCore.lean` | 62 | `maxHeartbeats 800000` |

Heartbeat limits allocate elaboration resources to the circle normalization,
Koszul and tensor differential calculations; they do not change kernel
acceptance. The transparency settings permit unfolding semireducible
definitions when comparing implicit arguments. No local `maxRecDepth`
override is used. `Arithmetic/ReducedExpressionFoundation.lean:78` separately
disables the `haveILetI` style linter within that module. This affects style
messages, not theorem checking. The project-level option is
`autoImplicit false`.

The `irreducible` attributes protect established coordinate maps, differentiated
blocks and their eigenbases from automatic expansion. The maps `colourPair`
and `matrixRealization` occur in `Physical/SourceSplitResponse.lean` and
`Physical/SourceMatterPhaseExponential.lean`. The new one-form, spinor and
tensor files apply the same mechanism to their finite operators and derived
bases. In `Geometry/SourceCoclosedDifferentialBlock.lean`, the attribute is
exported for `coclosedBasis` and `coclosedEigenvalue`; the other occurrences
are local. Subsequent proofs use the proved coordinate, differential and
basis identities. These elaboration attributes introduce no mathematical
hypotheses or axioms, and the resulting terms are kernel-checked.

The 18 October scan of all 273 local proof modules, with comments and strings masked,
found no executable `sorry`, `admit`, custom `axiom`, `sorryAx`, `unsafe`,
`partial`, `native_decide`, `implemented_by` or `extern` usage, and no local
macro, elaborator or initialization command. This is a source snapshot,
not an audit of mathlib and not a substitute for the complete compiled
axiom inventory. These implementation checks do not remove the mathematical
definitions, root contents or comparison classes documented above.

Rebuilding with the pinned Lean kernel is reproducible verification using
that implementation. `#print axioms` lists dependencies; it is not a proof
export to a separately implemented checker. No such external-checker run is
claimed here. An independent-checker claim requires an actual proof export,
support for the relevant Lean primitives, a successful check, and preserved
tool and artifact identities.

Manuscript correspondence also respects statement-level conventions. Paper 7
uses an inner product linear in its first slot, so its zero-mode coefficient
is the inner product of the input with the normalized constant mode. Its
projective heat-kernel assertion is for positive heat parameter, and the
capacity lift uses finite, strictly positive fibre dimensions. Paper 4's
spherical comparison class explicitly consists of Riemannian manifolds of
dimension at least two. These qualifications do not add fields to the root
datum or extend the scope of the indexed formal results.

The eighteen mapped manuscript source files have been reviewed against the indexed
premises, conclusions and construction dependencies. Their hashes and
clause-specific scope are recorded in `theorem-index.json`; 269 of the 298
indexed entries correspond to those eighteen source files. The new dimension mappings
cover the actual source tangent space and the exact spherical comparison
classes. They do not cover the added general Weyl counting argument or the
resolvent-trace bound obtained from it. This semantic
review does not cover unmapped manuscript assertions. The completed
compiled audit verifies the formal statements and their dependencies; it
does not replace this separate review of manuscript correspondence.

## Complete covariant matter compression

`Physical.SourceMatterCompression.generated` constructs the complete lepton
projection from the existing scalar-spin source summands in both chiral
copies. Its idempotence, adjoint, scalar-connector compatibility and
two-sided annihilation of coloured responses are proved on the actual
generated carrier. The neutral direction is retained.

`Operations.CovariantCompression` proves reconstruction, orthogonality,
uniqueness, the complete quadratic Gram decomposition and simultaneous
passive transport of the connection and moving readout. Its matrix
variables are field configurations; orthonormality and metric
compatibility state the coordinate domains of the respective identities.
They introduce no field configuration or coupling into the root datum.
The proved bundle is included in
`SourcePhysicalInterface.generatedCore.matter.compression`.

The two modules and physical interface have passed targeted compilation.
The nineteen indexed declarations and `generatedCore` have also been
checked with `#print axioms`; their dependencies are limited to `propext`,
`Classical.choice` and `Quot.sound`. This targeted check does not replace
the separately recorded whole-library audit.

## Matter energies, residues and the joint state

`Physical.SourceMatterPoleResponse` proves the finite block elimination
equation, eigenvector reconstruction, its full Gram normalization, the
positive return metric, the exact two-energy inverse-response identity
and the derivative of the actual complementary resolvent. The trace
identity for a common state proves that its two CAR orderings have the
unit equal-time normalization. No product-state assumption is used.

Its matrix variables describe configurations; inverse and resolvent
conditions specify analytic domains. The unit trace and CAR clauses
describe a normalized matter response. They do not choose a source state,
interaction, clock conversion or finite mass coefficient. The proved
operations are exported by
`SourcePhysicalInterface.generatedCore.matter.spectralResponse` alongside
all previously present physical branches. No custom axiom or `sorry`
was introduced. Targeted compilation and the eleven declaration checks
are recorded separately from the whole-library audit.

## Insertions on the complete generated matter fibre

`Physical.SourceMatterInsertions` constructs creation and contraction from
the existing sixteen-dimensional source fibre and its orthonormal coordinate
isometry. The neutral line is included. The mixed CAR product and its basis
normalization follow from that same inner product; no insertion-normalization
argument is supplied to the construction.

`Operations.FermionInsertions` proves the unique number-preserving lift of
a one-matter operator: its commutator with a creation operation is the
creation operation of the original matrix action, and its value on the
exterior unit is zero. These properties determine the lift on all exterior
words. The lift is independent of the orthonormal basis used to calculate
it. The stronger product-law characterization derives its zero unit value
from the Leibniz law itself, without a separate normalization hypothesis.
This is a statement about the fermionic exterior completion used by the
field realization, not a classification of all possible interacting
Hamiltonians. The exterior unit is an algebraic reference vector.

The source-specific conclusions are exported through
`SourcePhysicalInterface.generatedCore.matter.insertions`. The two new
modules and the physical interface passed targeted compilation on
27 October 2026. The new mixed-CAR, unique-lift, basis-independence and
source-bundle declarations were checked with `#print axioms`; their only
dependencies are `propext`, `Classical.choice` and `Quot.sound`. This is a
targeted check, separate from the dated whole-library audit above.

`Physical.SourceMatterEventInsertions` additionally places those concrete
insertions between the existing complete exterior transports. Its
coincident two-order identity and the identity after one common linear
preparation functional use the same source inner product. The module and
physical summary interface passed targeted compilation on 27 October 2026.
The three declarations in `verification/matter-event-insertions-audit.lean`
depend only on `propext`, `Classical.choice` and `Quot.sound`. The index
records their algebraic domains; this check does not assert a derived
interacting event Hamiltonian or formal verification of the numerical
determinant/cofactor evaluator.

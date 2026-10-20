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

The mathematical response interface includes least faithful Hilbert
realizations of the actual complete history--phase fibres and their
root-preserving sector products. Their dimensions are derived from the
actual fibre cardinalities. Matrix-unit decomposition and adjoint compatibility
give uniqueness up to unitary intertwining; no physical carrier dimension is
imposed on these arithmetic spaces. The general classification proofs are
shared upstream, with the former physical names preserved as compatibility
exports.

`HistoryCentralSectors` resolves the actual complete arithmetic coefficient
space into its intrinsic prime-occupation sectors. Their dimensions are
computed independently, and unitary coordinates retain every operator block.
`HistoryCliffordAction` also represents the common source Clifford operations
on all retained history--phase labels. Its source-sector exchange commutes
with occupation parity and Gaussian multiplication. Source chirality,
occupation parity and ordered-history reversal are therefore distinguished
by proved action identities. The full arithmetic/source matrix action has a
faithful realization in the original Gaussian/Hermite space, with every
matrix coefficient recovered by an explicit inverse.

The complete complex response is retained: arbitrary source connectors act
between explicit orthogonal sector inclusions, and independent even actions
have the proved connector covariance in both coefficient and Gaussian
coordinates. The finite phase action has an exact permutation matrix, trivial
kernel and computed trace. Its observation quotient is canonically the
zero-average detail space, with exact reconstruction, actual fibre dimensions
and a unique factorization for every response annihilating the invariant part.

The determinant line of the two original Gaussian modes and the Hermitian
matrix cone are shared source constructions. Both branches use the same
proofs, with the original physical names retained as compatibility exports.
The determinant phase remains explicit, and the positive-semidefinite cone
includes its degenerate boundary.

The actual phase bundle now has unitary frames, unique relative transitions,
passive components and complete response covariance. Its invariant and
zero-average spaces also determine their own primitive trace-free relative
weights `(-n,1)`, using their proved dimensions `H` and `H*n`. The degenerate
unit-root case remains explicit. Physical carrier dimensions and charge
numbers are not substituted into these arithmetic constructions.

### Two internal-radius conventions (do not mix)

| object | meaning | value |
|---|---|---:|
| `SourceEndpointCasimir.radius b = irEndpoint b` | IR **edge** of the Gaussian correlation window; the Lean canonical entry's internal radius | `sqrt(2*pi) ≈ 2.506628` |
| `kL` (V5) | finite-response **TT endpoint**: root of the TT spectral-sum equation `A(L)=4/27` | `2.493534` |
| `criticalRadius` | endpoint **ratio** `irEndpoint/uvEndpoint = sqrt(pi)`, not an edge | `1.772454` |
| `R=5` (V5) | finite **response-domain level** `q^2 < R Lambda^2`, not an internal radius | `5` |

`CanonicalYangMills` is the unconditional **IR-edge** model.  The V5
**TT-endpoint** model is separate and certificate-conditional:
`CanonicalYangMillsTT.generated` takes a
`SourceTTResponse.EndpointCertificate`.  It is deliberately not a field of
`CommonFoundation.Conclusions`; the zero-argument entry and the V5 TT model
are never identified.  At the IR edge the TT sum is about `0.147374`, below
`4/27`, so the two closures are genuinely different.

The zero-argument physical surface is
`SourcePhysicalInterface.CoreConclusions` (proved by `generatedCore`).  It
groups the gauge and matter layers and keeps the physical outputs without
repeating every intermediate bundle; the older `Conclusions` remains a
compatibility bundle for finer layers.

### Lean versus V5

Lean proves the **structural** physical branch: source and Gaussian law,
internal spectra, field spaces/operators/domains, YM nonlinear action and
Hessian, the finite-occupation Fock core and its heat semigroup, collective
linear gravity, `4/27`, `1/50`, and a certificate-conditional TT endpoint
root/interval layer for a **reduced eight-branch coefficient model** (given its
coefficient interval). Its identification with the full V5 finite spectral
sum is supplied by the separate V5 certificate described below; that bridge
is not formalized in this Lean branch.
V5 supplies the **numerical** layer: the TT spectral coefficient, Gaussian
frequency integral, finite-domain `R=5` bounds and effective gravitational
parameters.  `SourceTTEndpointInterval` consumes a V5 coefficient interval;
`SourceResponseLevel` consumes the V5 lower bound and proves the integer
selection.  The effective Einstein completion is macroscopic, not a
microscopic closure of the collective TT response.  No independent graviton
field or separate gravitational Fock space is introduced.

### Yang--Mills mass gap proved in the generated IR-edge model

The zero-argument theorem proves a **Yang--Mills mass gap** for the generated
Yang--Mills operator. `CanonicalYangMills.generated` combines the nonlinear
generated action, the self-adjoint differential Hessian (radial block plus the
complete coclosed colour-connection block), the attained positive spectral
bottom and the finite-occupation Fock gap. The relevant theorem names are
`SourceHaarYangMillsHessian.operator_selfAdjoint`,
`SourceHaarYangMillsHessian.complete_coercivity`,
`SourceHaarYangMillsHessian.gap_attained` and
`CanonicalYangMills.generated`.

This is a mass-gap theorem for the **generated finite IR-edge operator**, not a
proof of the Clay four-dimensional QCD mass-gap problem. It uses the IR edge
`sqrt(2*pi)`, not the V5 TT endpoint `kL`, and it does not use a V5 numerical
input. The separate V5 TT-endpoint number is a different operator and is not
identified with this theorem.

### The V5 TT-endpoint interface is an exact reduction

`SourceTTGaussianCoefficient` defines the eight active branches with response
`A_5/c`; `SourceTTEndpointInterval` proves the algebraic root/interval
statement for that coefficient model. The V5 endpoint is the root of the full
finite spectral sum `A_V5(c)=4/27`.

V5's `tt_branch_reduction` certificate supplies the missing bridge: on the
certified endpoint bracket the full active V5 spectrum consists of exactly
these eight branches, and the change of variable `u=c*omega` proves
`A_V5(c)=A_5/c` exactly. The V5 scaled-response interval is identical to the
Lean coefficient interval. Thus the Lean root theorem applies to the V5 full
response as an exact model reduction, not a numerical approximation.

The bridge is a V5 table/interval certificate; it is not a Lean import and is
not formalized inside this repository. `CanonicalYangMillsTT` remains a
certificate-conditional comparison module, not a field of
`CommonFoundation.Conclusions` and not a dependency of the zero-argument
physical theorem. V5 remains a separate release whose calculation and test
imports do not read this repository.

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
`5ed2965256430c3649e86755f9576b54eca72435`. The branch-alignment verification
record covers all 549 local modules, 24,087 project-owned compiled constants,
13,308 named type checks and 705 indexed claims. It includes both independent
branches, their common aggregate, compatibility exports and research modules.
The implementation and per-declaration comparison are recorded in
`BRANCH_ALIGNMENT.md` and the three branch-alignment ledgers under
`verification/`. The compiler audit and the semantic comparison have separate
records and scopes.

The earlier 19 October canonical-root audit
passed for all 346 local modules imported by the zero-argument entry, with
16,584 compiled constants, 8,490 named type checks and the indexed claims
recorded in `theorem-index.json`.
Those counts describe that audited snapshot, before the concrete-bundle and
nonlinear-density extensions above. The root and its dependencies in that
snapshot use only Lean's `propext`, `Classical.choice`
and `Quot.sound`; there are no local axioms or proof placeholders.
The separately scoped 18 October release audit records 273 modules, 13,854
constants, 7,231 named type checks and 298 indexed claims for that earlier
whole-library snapshot. These are library and audit counts, not counts of
independent mathematical theorems. That earlier canonical-root record does not
cover research modules outside its actual import closure; the later
branch-alignment record covers the whole implemented library.

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

The common root now also exposes the actual maximum-prime-factor stages,
their relative-potential ledger, the complete natural-prefix scale budget
and the cutoff-independent Gaussian tail. These are conclusions of the
constructed source; no balance or decay hypothesis is supplied to the root.

`NaturalSourceScaleBudget` integrates the full squarefree occupation
capacity `C_N`, rather than only the unit--prime pair. If `I_sigma` is the
empty-occupation Gaussian budget, its exact formula is

```text
integral C_N(exp u) exp(-2 sigma u) du
  = I_sigma * sum_{1 <= n <= N, generated-squarefree n} n^(-2 sigma).
```

For every `sigma > 1/2` this is bounded independently of `N`. The same bound
controls the normalized potential `B_N^2/C_N`, including empty prefixes.
The coherent budget has the exact, separate reconstruction
`integral B_N^2 = integral C_N * (B_N^2/C_N)` with the scale weight on both
sides. Its capacity factor is retained inside the integral.

`CapacityRestoredWindowBudget` makes the finite probability normalization
explicit on the actual level-five observation `n^2 < 5 L^2`. Its positive
and negative probabilities are the two Gaussian sector masses divided by
their own total capacity. Empty observations have zero first and second
moments. For the same window, with centre variance `v`, it proves

```text
B_visible^2 = C_visible^2 * (1-v).
```

Capacity conservation is part of this same ledger. The visible and outside
capacities add to the complete capacity, pointwise and inside the weighted
scale integral. A joint prime flip preserves both the Gaussian response and
window membership. At a genuine prime birth the paired old capacity, its
transported return and the unpaired old boundary add exactly to the new total.
The resolved capacity plus its actual unresolved complement is identical
before and after that birth, inside the same complete source; no external
capacity enters this balance.
Opposite-centre mixing transfers its potential loss `D_mix` to transverse
capacity:

```text
T_after = T_old + T_return + D_mix,
V_after + T_after = C_after.
```

The level-five capacity and normalized-potential scale budgets are uniformly
finite for every `sigma > 1/2`, over all natural cutoffs. The coherent budget
retains the factor `C_visible^2`. On a genuine prime update, the exact
capacity-restored dissipation balance is

```text
(C_old+C_return)*D_mix - C_return*V_old - C_old*V_return
  = 2*B_old*B_return.
```

Thus its signed correlation is present before the first inequality.
The complete energy and the window energy satisfy two-sided comparisons
with coefficients `2` and a squared Gaussian tail independent of the natural
generation cutoff `N`. This tail bound still depends on the observation
scale `L`; its pointwise estimate does not assert all-scale integrability.
The remaining growth estimate concerns the capacity-restored coherent
integral, including the signed visible--outside response.

`CoherentScaleTransport` implements the common-response comparison within
the arithmetic branch itself. At a genuine maximum-prime birth, its response
is the paired old response minus that same response at `L/p`, plus the actual
unpaired cutoff boundary. With `E_sigma(S)` denoting the complete coherent
scale energy of the finite generated set `S`, it proves

```text
E_sigma(after) - E_sigma(before)
  = p^(-2 sigma) * E_sigma(paired) - 2 * C_sigma(before, paired at L/p).
```

Here `C_sigma` is the real signed correlation under the original scale
measure. Its integrability is derived from the finite Gaussian source before
linearity of the integral is used. The return coefficient applies to the
capacity-restored square, and the old response includes the complete cutoff
boundary. A quadratic comparison is applied only after combining these two
responses; it retains the old energy and paired-return energy separately.
It is not a bound on the signed correlation that can be discarded in an
iteration. This module imports only arithmetic and analysis modules.

The physical branch independently proves that the centre trace of responses
`diag(A,B)` is `trace(A-B)`. Its common-response cancellation is the case
`A=B`; it is not a statement that arbitrary unequal observation responses
have vanishing centre trace. Neither branch uses the other as a premise.

`GaussianPrefixTail` replaces the outside-cardinality bound by a convergent
envelope. For `K = ceil(sqrt(R) * L) > 0`, put

```text
r = exp(-K/L^2),
T = exp(-K^2/L^2) / (1-r).
```

For every natural cutoff, `C_outside <= T`, the signed amplitude error is
at most `T`, and the coherent energy error is at most
`T^2 + 2*abs(B_visible)*T`. The bound is independent of the number of
omitted labels. The observation scale and window level remain explicit.

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
audit. If Lake requests rebuilding (exit code 3), it rebuilds the affected local
modules in dependency order, in batches of at most two independent ready targets
per Lake process, followed by the library. Targets in a batch may compile together;
completed dependencies are reused. Other
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

The default record and audit log are build artifacts, ignored by Git. Release
evidence is retained together in `verification/`: the original
`verification-manifest.json`, `foundations-audit.txt` and `SHA256SUMS.json`
preserve the V1.0 snapshot (239 source files). The independent
`branch-alignment-verification.json`, `branch-alignment-audit.txt` and
`branch-alignment-SHA256SUMS.json` preserve the later whole-library alignment
run, separately from that historical snapshot. The comparison ledger and
construction scopes are described in `BRANCH_ALIGNMENT.md`.
Public records use relative source paths and do not contain local installation
paths. A source
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
Coarse-Graining Genesis Framework V5 is a separate, self-contained release: its
calculation and test imports do not read this checkout, and it carries its own
small Lean 4.7 archive under `lean_proofs/`. V5 has no
`foundations-reference.json` and no `--foundations` verification entry; the
earlier cross-repository pin was removed.

The two releases are therefore independent build units. The only cross-reference
is documentary and one-way: the certificate-conditional TT-endpoint module
(`SourceTTResponse` / `CanonicalYangMillsTT`) describes the numerical interval
supplied by the V5 endpoint calculation, while the zero-argument
`CanonicalClosedWorld.generated` entry does not use that V5 TT model.

A complete run of this repository writes its own independent
`verification-manifest.json`; it does not update V5's numerical run record.
The record's scope remains the currently implemented library. Its presence does
not certify the full manuscript chain or any numerical run. Reading the saved
status checks the proof record, local proof sources, verifier and audit log;
it does not rerun compilation or inspect the current compiler installation.

Downloaded dependencies and build caches are not a second source of truth. An
altered proof snapshot must not be reported as the pinned one. Numerical-run
hashes are not
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

## Parallel mathematical and physical constructions

Both branches use `Source.CommonSource.generated`, the same zero-argument
construction from `Source.CanonicalRoot.generated`. The mathematical response
entry is `MathematicalInterface.generated`; the physical response entry is
`SourcePhysicalInterface.generatedCore`. `CommonFoundation.generated` gathers
them. The mathematical entry has no transitive dependency on `Physical`.

The mathematical instances use complete generated histories, their finite
phase fibres, the persistent positive source law and native prime occupations.
Their full Hermitian Gibbs response includes off-diagonal observations. The
actual reaction action contains every ordered three-leg assembly and all its
mixed terms. Its varied Hessian is the same operator used in the finite
reaction evolution and in the squared graded differential.

The ordered Gaussian two-mode source has an explicit Haar realization in
`Geometry.SourceSpinIdentification`. The map preserves the metric, every
complex matrix response and the actual number flow. `HistoryHaarResponse`
applies it at every generated history--phase label in both source sectors,
preserving arbitrary cross-label entries and the full adjoint. Its dimension
is four times the actual arithmetic label count.

`HistorySourceNaturality` classifies arbitrary matrices on the complete
history factor tensored with that source. Commutation with the actual full
history matrix algebra forces one unique source matrix. The original
pointwise reversal then gives one unique doublet or quaternion coordinate;
the resulting real response space has dimension four. The constructed family
satisfies both equations, with its Gaussian and Haar actions explicitly
intertwined. These are concrete arithmetic constructions using common
matrix-unit proofs.

`HistoryElementaryConnector` applies the same classification to an arbitrary
complete two-sector operator. Naturality, self-adjointness and oddness force
its unique off-diagonal complex block; the native source reversal then forces
one unique doublet. Both independent source frames act on this full operator.
Actual history-indexed frames have a canonical identity frame, exact cocycles
and compatible local doublet coordinates. Applying the connector preserves
compatible complete-state sections. Its Gaussian and Haar realizations retain
all matrix elements and cross terms.

`Geometry.SourceScalarResponse` and `SourceExchangeResponse` hold the shared
source classification and the actual orthogonal exchange transport. The
transport preserves inner products, arbitrary endomorphisms, adjoints and the
independent-source naturality equations. Physical-specific phase weights and
the physical effective quotient stay in the physical branch.

`HistoryEffectiveFrames` calculates the actual two-element kernel of the
source-frame action on every complete arithmetic response operator. The
effective quotient is faithful, has a unique action on the generated image,
and gives exact overlap cocycles when lifted defects lie in that kernel.
The full state action remains faithful and retains the simultaneous minus
sign; it does not descend through the response quotient. Its full inner
products and coherent matrix observations are preserved. This distinction
keeps the arithmetic state and its effective operator observation separate.

`HistoryEffectiveResponseSpace` realizes that same effective action on the
complete Hilbert space of all matrix coefficients. Its inner product is
proved equal to the trace pairing, and its effective unitary representation
is faithful and uniquely determined by the original conjugation action.
The inverse, adjoint and norm laws retain all off-diagonal coefficients.

The concrete response bundle has the actual history--phase label set as its
base, with uniquely specified base/fibre coordinates. Local Hermitian charts
have exact effective transitions and a computed two-sign lift ambiguity.
Full matrix gluing and response-Hilbert gluing are equivalent.
`HistoryReversalCharts` gives the unique common full-fibre antiunitary on
overlaps whose transitions intertwine the original reversal.

`HistoryGaussianConnection` identifies the exponential of the actual
root-square generator with the original Gaussian, differentiates it, and
proves uniqueness of its parallel scale connection. Its inverse frames and
transported metric are finite-dimensional constructions. On the same full
state fibre, `HistoryGaugeJets` proves the nonlinear connection product rule,
covariant matter derivative, curvature covariance and Bianchi identity. The
positive invariant curvature density uses the complete operator trace norm.
Its formal coefficient-coordinate jets and the actual one-dimensional
Gaussian scale transport remain distinct constructions.

`HistoryCurvatureVariation` computes the actual first, second and mixed
derivatives of that complete finite curvature action. The mixed Hessian
retains its background-curvature/commutator term and transforms with the
same action under generated frame changes. At flat background its nullspace
is precisely the vanishing-linearized-curvature subspace.

`HistoryScalarAmplitude` gives the complete elementary response a separately
computed norm law: its square is the source-doublet intensity times identity
on every arithmetic label. This intensity is positive for a nonzero doublet
and invariant under the independent source frames. The full inner-product
identity includes arbitrary cross-label coherent states. This operator and
the history reaction generator have different, explicitly proved kernels.

`HistoryReversalIsometry` supplies the actual antiunitary on every retained
history--phase label and on both source chiral sectors. Its square is minus
the identity. The Gaussian--Haar realization intertwines it with the original
source reversal; the complete elementary connector, independent source
frames, Gaussian multiplication and arithmetic occupation parity obey the
proved compatibility laws. This source operation preserves occupation
parity. `HistoryChiralBlocks` separately permits arbitrary operators on each
complete sector and derives their adjoints, exchange and grading formulas,
including cross-history and cross-phase coefficients.

The complete history coefficient Hilbert space also carries the actual
Gaussian reaction operator. Its root layers converge absolutely in operator
norm, using the normalized history law rather than a history-count bound.
The finite quadratic forms converge to its full form, and their embedded
operator exponentials converge to its full-space contraction evolution.

The history complex has a unique unit-anchored primitive and a separate
orthogonal leaf-charge/coexact decomposition. The finite reaction evolution
preserves leaf charge, dissipates coefficient energy by the reaction form and
dissipates the complete action by the squared actual operator. The positive
root-layer tail produces anchored unit states of strictly positive action
with arbitrarily small action-relative dissipation. Thus, at fixed positive
Gaussian observation coordinates, this complete coefficient flow has no
positive uniform exponential action rate with prefactor one. Its exact
dissipation and contraction remain valid; the occupation and physical
Hamiltonians have their own separately proved spectral outputs. Schur reduction of the
complete Gibbs Hessian retains the eliminated energy, including singular
directions through the proved scalar kernel. The orientation probe satisfies
the exact log-partition and variance identities; its zero-probe susceptibility
is the same direction of that full Gaussian Hessian.

[BRANCH_ALIGNMENT.md](BRANCH_ALIGNMENT.md) gives the 56-feature construction
ledger and the declaration-level review procedure. Feature coverage and
individual declaration review are separate. The inventory includes supporting
source, probability, correlation, operation, geometry and spectral declarations,
including those used by physical modules outside the public entry. The proved
full-history limit and contraction are distinct from a strictly positive
cutoff-independent reaction-gap theorem. Different arithmetic and physical carriers
retain their own dimensions, invariant directions and response constants.

The complete Haar connection--state response supplies a separate restoring
operator. `HistoryHaarCoupledAction` computes its nonlinear action and mixed
second variation. `HistoryHaarJointCore` identifies the differential core;
`HistoryHaarJointHessian` proves the unique self-adjoint closure, its domain,
the attained bottom `min(4,c_N)` and the cutoff-independent lower bound `15/8`.
`HistoryHaarJointFlow` proves the complete flow, its right-generator domain and
norm decay `exp(-15*t/8)`. These theorems do not assert a positive gap for the
different Gaussian history-reaction generator.

`HistoryCompleteSourceGroup` constructs the faithful joint state action from
the two source frames and the actual rank-dependent circle. Its least
generated group, complete coefficient coordinates, factorization and overlap
defects are proved. `HistoryCompleteConnector` retains its full source/phase
covariance and all coherent observations. The state kernel and the effective
response kernel are calculated separately.

`HistoryGaussianCovariance` determines the variance from the actual full-basis
coefficient count. `HistoryGaussianWindowResponse` uses the actual joint-Hessian
eigenvalues in its finite-window Gaussian integral, with positivity, a unique
algebraic response root and interval consumers. Physical window selections,
geometric radius certificates and dimensional calibration keep their own
premises; they are not inserted as mathematical source data.

Every declaration in the 91 physical modules and their 241 supporting modules
now has an object-and-scope comparison. The inventory distinguishes proved
arithmetic analogues, identical shared results and physical-specific outputs.
Both branches remain independent at the import level and meet only at their
common generated source and upstream mathematical constructions. The
inventory and compiled verification remain separate records.

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
| Generated Yang--Mills action, differential Hessian and spectral gap | `SourceHaarCurvatureTrace.action_eq_trace`, `SourceHaarYangMillsHessian.action_secondDeriv`, `SourceOneFormCoclosedSpectrum.coclosedHilbertBasis`, `CanonicalYangMills.generated` | The nonlinear action is evaluated on the original Haar one-form fields; its curvature term equals the integral of the actual colour-matrix curvature trace. Differentiation gives the radial block and the source curl-squared connection block, with zero mixed second derivative. The weak divergence kernel has a complete basis of differentiated source eigenfields. The original-field Hessian has a unique self-adjoint closure, its full weighted-square domain, an attained positive bottom and the corresponding finite-occupation Fock gap. Every colour and every nongauge field direction is retained. The radius in this row is the IR edge of `CanonicalYangMills`, not the V5 TT endpoint `kL`. |
| Newton mass calibration | `CanonicalYangMillsUnits.generated`, `CanonicalYangMillsUnits.gapMass_sq`, `CanonicalYangMillsUnits.gapMass_unique` | The dimensional readout takes only a positive Newton constant; the IR radius has already been generated. In the stated reduced-Planck convention, the emergence mass squared is `1/(16*pi*G_N)` and the unique positive gap mass squared is `gapSq/(16*pi*G_N)`. The calibration cancels from their ratio and does not enter the action, condensate or operator. This calibration belongs to the IR-edge model; V5's TT endpoint `kL` is a different radius and its absolute gap is not this one. |
| Canonical Yang--Mills response | `CanonicalYangMills.generated` | The generated IR **edge** `sqrt(2*pi)` exceeds the critical ratio. Its unique positive condensed amplitude, original-Haar-field action, self-adjoint differential response Hessian, attained positive spectral bottom and finite-occupation gap are outputs of a theorem without realization arguments. This is the **IR-edge model**; the V5 **TT-endpoint** model `kL` is separate and certificate-conditional in `CanonicalYangMillsTT`, not this theorem. |
| Torsion content `1/50` | `SourceTorsionContent.generated` | The generated hypercharge operator gives `sum c*Y^2=10/3`; the left/charged-right counts are `8/7`; the charged quotient has dimension `15`. Hence `(N_L-N_R)/(N_f*sum Y^2)=1/50` as a rational theorem, not a fitted parameter. |
| V5 finite Gaussian TT coefficient | `SourceTTGaussianCoefficient.generated`, `existsUnique_endpoint` | The eight retained branches use the generated torsion value and the actual Gaussian frequency integrals. Their coefficient `A5` is strictly positive and selects the unique positive radius `27*A5/4` with response `A5/c=4/27`. These integral and uniqueness results are outputs of the zero-argument physical interface. |
| Complete matter centre response | `SourceClosedCenterResponse.generated` | The actual sixteen-state basis carries the generated grading and exchange. Exchange preserves the total capacity for every weight on this carrier. Every common left/right matrix response has zero centre trace. Its finite exponential trace is `cosh h`; the logarithmic response is `tanh h`, with positive susceptibility `1/cosh(h)^2`. The exponential probe family has a unique unbiased point, with centre bias zero, fluctuation one and restoring Hessian one. The neutral direction is retained. |
| V5 TT-endpoint Yang--Mills model (separate, reduced coefficient) | `SourceTTResponse.EndpointCertificate`, `endpointCertificateOfBounds`, `CanonicalYangMillsTT.generated` | A geometric enclosure of the reduced eight-branch coefficient places its unique radius between the critical radius and the IR edge. Every endpoint certificate has this same radius; it contains no independent response value. The condensed TT-endpoint Yang--Mills conclusion uses that enclosure and remains separate from the IR-edge Yang--Mills theorem. The exact reduction from the full V5 finite spectral response is certified separately in V5 and is not formalized here. |
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

# Lean Formalization of Arithmetic and Basic Physical Interfaces

[![Lean verification](https://github.com/bookwormseagull1980/Lean-Formalization-of-Arithmetic-and-Basic-Physical-Interfaces/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/bookwormseagull1980/Lean-Formalization-of-Arithmetic-and-Basic-Physical-Interfaces/actions/workflows/ci.yml)

Source repository: [Lean Formalization of Arithmetic and Basic Physical Interfaces](https://github.com/bookwormseagull1980/Lean-Formalization-of-Arithmetic-and-Basic-Physical-Interfaces).

This independent Lean 4 library formalizes the common mathematical
foundations used in:

- J. Guo, *A Spectral Construction of Natural-Number Arithmetic*.
- J. Guo, *The Spectrum of a Compact Internal Space I: Gauge Structure and a Scalar Mass Gap*.

The two implemented root theorems construct native natural-number arithmetic
and the basic internal physical interface, respectively. Their exact
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

The sole root input is minimal unbiased compositional change, represented by
`Source.MinimalUnbiasedChange.Datum`. Its four fields are the orthogonal change
datum, carrier minimality, a law on the generated trace Lie line, and the
composition/scaling/variance conditions on that law. The comparison class and
C/S/V conditions are stated explicitly; no Gaussian formula is assumed.
The existing existence theorem supplies a compatible law, and uniqueness fixes
it at positive parameters on that carrier.

Orientations and positive widths index realizations. The arithmetic and
physical `fromMinimalUnbiasedChange` theorems quantify over all of them in their
conclusions. Endpoint values, reflecting boundary operators, spectral data,
arithmetic operations and physical response objects are not root fields or
additional caller-supplied hypotheses.

Structural conditions, realization indices and calculated outputs have
different roles. The C/S/V conditions define the source class. Calibrated
additive information and normalized translation-invariant mass characterize
the fixed endpoint readouts; their evaluation on the source profile gives
the endpoint values. Even reflection constructs the conserving closure,
while the separated-boundary theorem classifies constant-preserving
competitors. These characterizations are not adjustable fitting parameters,
and their comparison classes must not be omitted from uniqueness claims.
In particular, additive information alone determines a multiple of the
negative logarithm; the unit calibration at `exp(-1)` fixes that multiple.
Uniqueness throughout is at the equivalence level stated in each theorem,
not literal equality of all choices of coordinates or realizing maps.

Declaration counts include named definitions, abbreviations, auxiliary lemmas
and theorems. They are not counts of manuscript theorems. A manuscript mapping
records the particular statement or clause supported by a Lean declaration;
several declarations may support one manuscript result. Full coverage requires
matching all premises and conclusions and completing the intervening construction.

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
`lake build` with one worker, installs the pinned Python test dependencies,
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

The current 235-module library has passed compilation and the complete
compiled-environment axiom audit. The saved record covers 11,664 constants,
6,339 named type checks and 225 indexed claims. These counts have different
meanings; consult the index for the precise scope of each claim and use
`--check-manifest` to confirm that the record matches the current sources.

See [AXIOMS.md](AXIOMS.md) for the complete logical-axiom allowlist, the
expanded root conditions, the retained construction and classification
restrictions, and the limits of the current axiom collector. In particular,
absence of custom axioms does not establish that every downstream choice is
forced uniquely by the root datum. Independent external proof checking has
not been performed.

## Constructed physical interface

`Physical.SourcePhysicalInterface.fromMinimalUnbiasedChange` and
`Arithmetic.GeneratedFoundation.fromMinimalUnbiasedChange` are the two root
entries. Each takes only `Source.MinimalUnbiasedChange.Datum` and gives its
conclusions for every orientation and positive width. The former supplies the
basic physical interface; the latter supplies the source closure, native
arithmetic and prime-factorization results. Both are imported by the public
library entry. The earlier expanded-argument theorems remain available for
applications to a particular realization.

The same law and width determine the source used throughout each realization.
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
| Vacuum and charge | `SourceInternalResponse.source_internalResponse` | Actual vacuum stabilizer, continuous source lift, primitive charge classification, six-element gauge kernel and faithful effective action. |
| Elementary connector | `SourceScalarConnector.canonical_elementary`, `elementary_iff_unique_doublet` | The canonical family satisfies independent-source naturality and reversal reality; every connector in that comparison class has a unique doublet coordinate. Its original Gaussian realization and covariance are included. |
| Relativistic algebraic interface | `SourceHermitianReadout.coordinatesEquivHermitian`, `determinantForm_coordinateTransform`, `sourceHermitianAction_coe` | All Hermitian two-by-two matrices have unique four-real coordinates, with signature `(+---)` and determinant-one congruence invariance; their action is the actual two-mode source action. |

The common-source geometry, both root entries and all local dependencies
have compiled successfully. The complete axiom inventory reports only
`propext`, `Classical.choice` and `Quot.sound`; both root entries depend on
exactly these three. `AXIOMS.md` describes the inventory, including generated
recursion implementation entries, and the limits of this evidence. The
public entry imports both branches, while the physical branch itself does
not import arithmetic constructions.
The relative-frame construction does not claim existence of
arbitrary nontrivial bundles, and the Hermitian interface does not reconstruct
a physical clock, a spacetime manifold or interacting field dynamics.

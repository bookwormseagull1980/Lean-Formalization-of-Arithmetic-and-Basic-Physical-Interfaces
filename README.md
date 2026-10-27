# Lean Formalization of Arithmetic and Basic Physical Interfaces

## Mathematics and physics from minimal change

[![Lean verification](https://github.com/bookwormseagull1980/Lean-Formalization-of-Arithmetic-and-Basic-Physical-Interfaces/actions/workflows/ci.yml/badge.svg)](https://github.com/bookwormseagull1980/Lean-Formalization-of-Arithmetic-and-Basic-Physical-Interfaces/actions)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23254521.svg)](https://doi.org/10.5281/zenodo.23254521)

**Jinku Guo · Northwestern Polytechnical University**

[Research portal](https://bookwormseagull1980.github.io/Book-and-Articles/) ·
[Theorem index](theorem-index.json) · [Complete technical reference](REFERENCE.md) ·
[Branch alignment](BRANCH_ALIGNMENT.md) · [Discussions](https://github.com/bookwormseagull1980/Lean-Formalization-of-Arithmetic-and-Basic-Physical-Interfaces/discussions)

This Lean 4/mathlib library develops a common generating source into
natural-number arithmetic, finite expression histories and basic physical
response structures. Its arithmetic branch retains how a value is generated,
then proves that retained history differences can affect later value response.
Its physical branch constructs gauge and matter data and proves the generated
Yang-Mills action, complete differential Hessian and attained positive spectral
gap in the specified source model.

The formal statements expose the hypotheses, types and comparison classes of
each conclusion. The theorem index links these statements to the companion
manuscripts. Compiler and axiom audits record the declarations actually checked
in each audit; the full technical reference preserves the detailed construction
and the separate audit snapshots.

## What the library establishes

| Construction | Principal output | Formal entry |
| --- | --- | --- |
| Common source | Minimal carrier, Gaussian law, correlation endpoints and reflected spectral structure | [Canonical closed world](GeneratedFoundations/CanonicalClosedWorld.lean) |
| Native arithmetic | Ordered Peano operations, recursion, unique prime factorization, scale and orientation transport | [Generated arithmetic foundation](GeneratedFoundations/Arithmetic/GeneratedFoundation.lean) |
| Retained expressions | Finite expression fibres, conditional history source, history geometry and complete assembly dynamics | [Complete history dynamics](GeneratedFoundations/Arithmetic/CompleteHistoryDynamics.lean) |
| Observable history response | Coupling of internal differences to value response and exact elimination with memory | [History response reduction](GeneratedFoundations/Analysis/HistoryResponseReduction.lean) |
| Gauge and matter | The generated gauge-matter bundle in the stated continuation class | [Canonical matter bundle](GeneratedFoundations/Physical/CanonicalMatterBundle.lean) |
| Yang-Mills action and gap | Original-field curvature action, self-adjoint Hessian, complete coercivity and attained spectral bottom | [Canonical Yang-Mills](GeneratedFoundations/Physical/CanonicalYangMills.lean) and [Hessian](GeneratedFoundations/Physical/SourceHaarYangMillsHessian.lean) |

### Arithmetic with information about its construction

The source produces an ordered mode family on which the native operations are
defined. Winding degree supplies the subsequent numerical certification.
Ordered expressions retain brackets, operation labels and input order before
evaluation. Conditional readout separates arithmetic values from internal
history variation. The complete assembly operator has an explicit history
component whose initial value readout vanishes but whose subsequent value
response is nonzero.

Thus the formalized object contains more information than a numerical value or
a circle-power label. The construction records the source, evaluation,
conditional geometry and evolution needed to follow that information. The
[arithmetic paper](https://ssrn.com/abstract=7421398) gives the mathematical
development and worked examples.

### The generated Yang-Mills spectral-gap theorem

`CanonicalYangMills.generated` combines the source-generated IR-edge radius,
nonlinear action, positive condensed response and original-field differential
Hessian. The connection sector uses the complete weak divergence kernel on the
Haar one-form space. The Hessian has its unique self-adjoint closure on the
explicit weighted-square domain, and the positive spectral bottom is attained.
Finite occupation gives the corresponding Fock gap.

The principal declarations include
`SourceHaarYangMillsHessian.operator_selfAdjoint`,
`SourceHaarYangMillsHessian.complete_coercivity` and
`SourceHaarYangMillsHessian.gap_attained`.
The separate transverse-traceless realization,
`CanonicalYangMillsTT.generated`, takes an endpoint certificate. Its radius and
dimensional calibration are distinct from the Gaussian IR-edge realization.
The [physical construction paper](https://ssrn.com/abstract=7352020) and
[V5 correspondence](https://github.com/bookwormseagull1980/coarse-graining-genesis/blob/master/docs/LEAN_CORRESPONDENCE.md)
explain this interface.

## First checks

Use the pinned version in `lean-toolchain` and the dependencies in
`lake-manifest.json`. From the repository root:

```sh
python examples/quickstart/check_environment.py
lake build
python scripts/verify_foundations.py
```

The first command checks the local environment. The build checks the imported
Lean declarations. The verifier runs the repository's named checks and produces
the corresponding audit information. The [quick-start guide](examples/quickstart/README.md)
and [verification reference](verification/README.md) explain the records and
the extra regression-test dependencies.

The [public workflow](https://github.com/bookwormseagull1980/Lean-Formalization-of-Arithmetic-and-Basic-Physical-Interfaces/actions)
is the current branch check. The stored audits identify their own source
snapshot, import closure and axiom scope. Module and declaration counts belong
to those records. The [full reference](REFERENCE.md) distinguishes the earlier
canonical-root audit from the later whole-library branch alignment.

## Reading and reviewing the formalization

1. Read the companion manuscript's construction and choose the relevant claim
   in [theorem-index.json](theorem-index.json).
2. Follow its declaration and hypotheses to the source module. The canonical
   entry and the more general interface often have different input types.
3. Consult [BRANCH_ALIGNMENT.md](BRANCH_ALIGNMENT.md) and the stored verification
   records for the mapping and the checked source snapshot.
4. Run the pinned build and verifier to reproduce the checks on the revision
   being studied.

The technical reference retains the detailed treatment of Gaussian selection,
endpoints, arithmetic and history dynamics, physical continuation, the two
Yang-Mills radius realizations, units, logical axioms and proof coverage.

## Papers, calculations and citation

The [Book-and-Articles collection](https://github.com/bookwormseagull1980/Book-and-Articles)
contains the reading PDFs and their individual archival identifiers.
[V5](https://github.com/bookwormseagull1980/coarse-graining-genesis)
provides the numerical response calculations and interval certificates.
The companion paper on [effective couplings and mass scales](https://arxiv.org/abs/2607.24329)
is available as arXiv:2607.24329, [DOI 10.48550/arXiv.2607.24329](https://doi.org/10.48550/arXiv.2607.24329).
The [shared portal](https://bookwormseagull1980.github.io/Book-and-Articles/)
organizes arithmetic, prime operators, gauge theory, gravity and certified
computation into reading routes.

Cite the proof library using its concept DOI,
[10.5281/zenodo.23254521](https://doi.org/10.5281/zenodo.23254521), together with
the relevant companion paper. [CITATION.cff](CITATION.cff) supplies machine-readable
metadata. The source revision identifies a particular reproduction.
[LICENSE](LICENSE) preserves the copyright and attribution terms.

Mathematical questions are welcome in
[Discussions](https://github.com/bookwormseagull1980/Lean-Formalization-of-Arithmetic-and-Basic-Physical-Interfaces/discussions).
For a failed check or a statement-to-paper discrepancy, use the issue forms and
include the declaration, revision and relevant output.

Subjects: Lean 4, mathlib, formal verification, generated arithmetic, natural
numbers, Gaussian measures, spectral theory, history dynamics, Yang-Mills,
mass gap, gauge theory, matter representations and mathematical physics.

## Research subjects and results

### Primary subjects

Lean 4; Formalized mathematics; Machine-checked proofs; Interactive theorem proving; Proof assistants; Yang-Mills theory; Mass gap; Natural-number arithmetic; Spectral theory; Mathematical physics; Formal verification; mathlib.

### Research subjects

Foundations of arithmetic; Natural-number objects; Unique factorization; Gaussian measures; Convolution semigroups; Neumann spectra; Arithmetic expression trees; Conditional expectation; History-dependent dynamics; Gauge groups; Standard Model representations; Yang-Mills action; Spectral gaps; Self-adjoint operators; Hilbert spaces.

### Methods

Dependent type theory; Kernel-checked proofs; Theorem formalization; Functional analysis; Operator theory; Quadratic forms; Weighted Hilbert spaces; Coercivity estimates; Orthogonal decomposition; Hodge decomposition; Fock space; Representation theory; Recursive definitions; Formal proof dependencies; Axiom auditing.

### Results and research questions

Machine-checked construction of natural-number arithmetic; Formal proof of unique prime factorization on generated modes; Formalized Gaussian source selection; Verified scale and orientation transport; Formalized arithmetic expression-history assembly; Machine-checked gauge and matter construction; Self-adjoint Yang-Mills Hessian and complete coercivity in Lean; Attained positive spectral gap for the generated Yang-Mills operator.

### Chinese subject terms

Lean形式化; 机器核验数学证明; 交互式定理证明; 证明助手; 自然数构造; 唯一素因数分解; 杨米尔斯质量间隙; 自伴算子; 强制性估计; 规范物质表示; 数学物理; 形式化验证.

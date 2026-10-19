# Verification evidence

This directory preserves the V1.0 verification snapshot of **Lean
Formalization of Arithmetic and Basic Physical Interfaces**. The Lean namespace
remains `GeneratedFoundations`; this snapshot is not a claim of current
working-tree freshness.

The evidence consists of `verification-manifest.json`, the complete
`foundations-audit.txt`, and `SHA256SUMS.json`. The manifest binds the proof
sources, dependency locks, theorem index, verifier, actual tools and audit
output. The hash inventory also identifies the accompanying public files.
It is not a digital signature or an independent implementation of Lean's
kernel.

To reproduce the audit, run the following from the repository root with the
pinned Lake toolchain available:

```text
python scripts/verify_foundations.py
```

The command writes a new `verification-manifest.json` in the repository root
and `.lake/foundations-audit.txt`. Their hashes and verification identity may
differ from the preserved run. In particular, compiler executable hashes are
platform-specific. A successful reproduction must check the same proof
statements and dependencies; it must not merely rewrite a saved record's
hashes. Use `--lake-exe` if Lake is not on the search path.

The preserved log is byte-for-byte compiler output. Its progress timestamps
can precede message rendering and do not measure the full wall-clock run.
The verification scope is the implemented library identified by the manifest,
not every claim in the companion manuscripts. See `AXIOMS.md` and
`theorem-index.json` for the axiom inventory and statement-level scope.

## Branch comparison records

`branch-alignment-features.json` records the 56 construction features and
their actual mathematical proof targets. `branch-alignment-reviews.json`
contains declaration-specific object and scope comparisons. The generated
`branch-alignment-inventory.json` enumerates every physical source declaration,
checks those records against the exact source hashes and checks the two
independent import graphs. Unreviewed declarations remain explicit.

These three source ledgers do not extend the preserved V1.0 verification
snapshot above. A current kernel/environment audit is produced separately by
the foundations verifier; only its source-bound manifest establishes which
compiled declarations and transitive axioms were checked in that run.

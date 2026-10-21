# Public quickstart

From the repository root, run:

```text
python examples/quickstart/check_environment.py
```

The check confirms the pinned Lean toolchain, the locked mathlib revision, the
canonical root and its mathematical and physical branch entries, and the
release documents used by the full audit. It uses only the Python standard
library and finishes before a Lean rebuild.

This is a release smoke test, not a proof of the mathematical claims. To run
the complete verification, use the pinned toolchain, `lake build`, and then
`python scripts/verify_foundations.py`; the same sequence is executed by the
public GitHub Actions workflow.

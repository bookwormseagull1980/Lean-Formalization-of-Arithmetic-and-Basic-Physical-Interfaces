"""Small release smoke test for the public Lean proof package.

This checks the pinned source metadata and the two public root entries. It is
deliberately independent of Lean compilation; the full proof and axiom audit is
performed by ``scripts/verify_foundations.py`` and the repository CI workflow.
"""

from __future__ import annotations

import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
EXPECTED_TOOLCHAIN = "leanprover/lean4:v4.34.0"
EXPECTED_MATHLIB = "5ed2965256430c3649e86755f9576b54eca72435"
EXPECTED_ROOTS = [
    "Arithmetic.GeneratedFoundation.fromMinimalUnbiasedChange",
    "Physical.SourcePhysicalInterface.fromMinimalUnbiasedChange",
]


def main() -> None:
    toolchain = (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
    lock = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    manifest_text = json.dumps(lock, sort_keys=True)
    index = json.loads((ROOT / "theorem-index.json").read_text(encoding="utf-8"))
    index_text = json.dumps(index, sort_keys=True)

    if toolchain != EXPECTED_TOOLCHAIN:
        raise SystemExit(f"unexpected Lean toolchain: {toolchain}")
    if EXPECTED_MATHLIB not in manifest_text:
        raise SystemExit("pinned mathlib commit is missing from lake-manifest.json")
    missing = [name for name in EXPECTED_ROOTS if name not in index_text]
    if missing:
        raise SystemExit(f"root entry missing from theorem-index.json: {missing[0]}")
    for required in (
        "AXIOMS.md",
        "theorem-index.json",
        "verification/verification-manifest.json",
    ):
        if not (ROOT / required).exists():
            raise SystemExit(f"required release file is missing: {required}")

    record = {
        "lean_toolchain": toolchain,
        "mathlib_commit": EXPECTED_MATHLIB,
        "root_entries": EXPECTED_ROOTS,
        "theorem_index_present": True,
        "axioms_document_present": True,
        "verification_record_present": True,
    }
    expected = json.loads(
        (Path(__file__).resolve().parent / "expected_output.json").read_text(
            encoding="utf-8"
        )
    )
    if record != expected:
        raise SystemExit("quickstart output differs from expected_output.json")
    print(json.dumps(record, indent=2))
    print("quickstart verification passed")


if __name__ == "__main__":
    main()

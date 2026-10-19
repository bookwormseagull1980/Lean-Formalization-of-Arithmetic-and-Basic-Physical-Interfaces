#!/usr/bin/env python3
"""Build and audit the canonical root's entire transitive local import closure.

This uses the full verifier's unchanged source, dependency, declaration and
axiom checks. ResearchExtensions not imported by the root remain outside this
record. The separately named record never replaces the whole-library audit.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parent))
import verify_foundations as verify


ENTRY = "GeneratedFoundations"
RECORD = "canonical-root-verification.json"
AUDIT_LOG = ".lake/canonical-root-axioms.txt"
SCRIPT = Path(__file__).resolve()


def configure_console() -> None:
    """Preserve Lean's Unicode diagnostics on Windows legacy-codepage hosts."""
    for stream in (sys.stdout, sys.stderr):
        if hasattr(stream, "reconfigure"):
            stream.reconfigure(encoding="utf-8", errors="backslashreplace")


def root_closure(modules: dict[str, Path]) -> dict[str, Path]:
    """Follow actual local imports, including unindexed intermediate modules."""
    visited: set[str] = set()
    pending = [ENTRY]
    while pending:
        name = pending.pop()
        if name in visited:
            continue
        visited.add(name)
        code = verify.lean_code(modules[name].read_text(encoding="utf-8-sig"))
        pending.extend((verify.imports(code) & modules.keys()) - visited)
    return {name: modules[name] for name in sorted(visited)}


def snapshot(project: Path, modules: dict[str, Path]) -> dict[str, str]:
    paths = list(modules.values()) + [project / name for name in (
        "lean-toolchain", "lakefile.lean", "lake-manifest.json", "theorem-index.json",
        "scripts/verify_foundations.py", "scripts/verify_canonical_root.py")]
    return {p.relative_to(project).as_posix(): verify.sha256_file(p)
            for p in sorted(paths)}


def require_clean_output(output: str, subject: str) -> None:
    if re.search(r"\bwarning:", output, re.IGNORECASE):
        raise verify.VerificationError(f"{subject} emitted warnings")


def audit(project: Path, lake: str, timeout: int) -> dict:
    whole = verify.check_sources(project)
    modules = root_closure(whole.modules)
    # Indexed declarations are selected by their actual module membership,
    # not by a handwritten list of supposedly relevant physical theorems.
    index = json.loads((project / "theorem-index.json").read_text(encoding="utf-8-sig"))
    indexed = tuple(claim["name"] for claim in index["declarations"]
                    if claim["module"] in modules)
    declarations = set(indexed)
    for path in modules.values():
        declarations.update(verify.source_declarations(
            verify.lean_code(path.read_text(encoding="utf-8-sig"))))
    before = snapshot(project, modules)
    state = verify.SourceState(modules, (ENTRY,), tuple(sorted(declarations)), indexed, before)
    tools = verify.tool_evidence(lake, project, timeout)
    dependencies = verify.check_actual_dependencies(project, timeout)
    order = verify.module_build_order(state)
    print(f"CANONICAL ROOT: {len(modules)} local modules, {len(indexed)} indexed claims", flush=True)
    # The '+' module target is essential: the bare library target also builds
    # unimported research modules, which belong to a different proof scope.
    output = verify.run([lake, "--no-cache", "build", "+" + ENTRY], project, timeout)
    require_clean_output(output, "Canonical root build")
    output = verify.run([lake, "--no-cache", "--no-build", "build"] +
                        ["+" + name for name in order], project, timeout)
    require_clean_output(output, "Root closure freshness check")
    probe_source = verify.audit_source(state)
    log = project / AUDIT_LOG
    with tempfile.TemporaryDirectory(prefix="canonical-root-axioms-") as directory:
        probe = Path(directory) / "CanonicalRootAudit.lean"
        probe.write_text(probe_source, encoding="utf-8", newline="\n")
        output = verify.run([lake, "--no-cache", "lean", str(probe)], project, timeout,
                            output_path=log)
    require_clean_output(output, "Compiled root declaration audit")
    environment, axioms = verify.check_environment_output(output, state)
    if snapshot(project, modules) != before:
        raise verify.VerificationError("Canonical root sources or verifiers changed during audit")
    if verify.check_actual_dependencies(project, timeout) != dependencies:
        raise verify.VerificationError("Dependencies changed during audit")
    if verify.tool_evidence(lake, project, timeout) != tools:
        raise verify.VerificationError("Toolchain changed during audit")
    record = {
        "schema_version": 1, "kind": "canonical-root-closure-verification",
        "status": "passed", "scope": "canonical_root_entire_local_import_closure",
        "verified_at": datetime.now(timezone.utc).isoformat(),
        "entry_modules": [ENTRY], "module_build_order": list(order),
        "source_files": before, "tools": tools, "dependencies": dependencies,
        "indexed_declarations": list(indexed), "named_type_checks": len(declarations),
        "environment_audit": environment, "declaration_axioms": axioms,
        "allowed_axioms": sorted(verify.ALLOWED_AXIOMS),
        "audit": {"path": AUDIT_LOG, "sha256": verify.sha256_file(log),
                  "probe_sha256": hashlib.sha256(probe_source.encode("utf-8")).hexdigest()},
    }
    verify.publish_manifest(project / RECORD, record)
    print(f"CANONICAL ROOT AUDIT PASSED: {len(modules)} modules, "
          f"{len(axioms)} constants, {len(declarations)} named types", flush=True)
    print(f"Record: {project / RECORD}", flush=True)
    return record


def main(argv: list[str] | None = None) -> int:
    configure_console()
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project-root", type=Path, default=SCRIPT.parents[1])
    parser.add_argument("--lake-exe")
    parser.add_argument("--timeout", type=int, default=1800)
    args = parser.parse_args(argv)
    try:
        audit(args.project_root.resolve(), verify.resolve_lake(args.lake_exe), args.timeout)
    except (verify.VerificationError, OSError, ValueError) as exc:
        print(f"CANONICAL ROOT VERIFY FAILED: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

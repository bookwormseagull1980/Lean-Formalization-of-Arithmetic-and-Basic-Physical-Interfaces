"""Scope and stale-evidence checks for the canonical-root audit."""

from pathlib import Path
import sys
from types import SimpleNamespace

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts import verify_canonical_root as audit


def test_scope_follows_unindexed_intermediates_and_ignores_comment_imports(tmp_path):
    sources = {
        "GeneratedFoundations": "module\npublic import GeneratedFoundations.Physical\n",
        "GeneratedFoundations.Physical":
            "module\npublic import GeneratedFoundations.Intermediate\n"
            "/- public import GeneratedFoundations.ResearchExtensions -/\n",
        "GeneratedFoundations.Intermediate": "module\n",
        "GeneratedFoundations.ResearchExtensions": "module\n",
    }
    modules = {}
    for name, code in sources.items():
        path = tmp_path / (name + ".lean")
        path.write_text(code, encoding="utf-8")
        modules[name] = path
    result = audit.root_closure(modules)
    assert set(result) == set(sources) - {"GeneratedFoundations.ResearchExtensions"}
    # If the root really imports the research branch, the audit cannot
    # silently exclude it just because of its name.
    modules["GeneratedFoundations"].write_text(
        sources["GeneratedFoundations"] +
        "public import GeneratedFoundations.ResearchExtensions\n", encoding="utf-8")
    assert set(audit.root_closure(modules)) == set(sources)


def test_snapshot_fingerprints_both_verifiers_and_all_closure_sources(tmp_path):
    filenames = ["GeneratedFoundations.lean", "lean-toolchain", "lakefile.lean",
                 "lake-manifest.json", "theorem-index.json",
                 "scripts/verify_foundations.py", "scripts/verify_canonical_root.py"]
    for name in filenames:
        path = tmp_path / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("initial", encoding="utf-8")
    modules = {"GeneratedFoundations": tmp_path / "GeneratedFoundations.lean"}
    before = audit.snapshot(tmp_path, modules)
    assert set(before) == set(filenames)
    (tmp_path / "scripts/verify_canonical_root.py").write_text("changed", encoding="utf-8")
    assert audit.snapshot(tmp_path, modules) != before


def test_compiler_warnings_prevent_audit_success():
    with pytest.raises(audit.verify.VerificationError, match="emitted warnings"):
        audit.require_clean_output("warning: declaration uses sorry", "test")
    audit.require_clean_output("Build completed successfully", "test")


def test_unicode_console_does_not_inherit_windows_legacy_codepage(monkeypatch):
    calls = []
    monkeypatch.setattr(audit.sys, "stdout", SimpleNamespace(
        reconfigure=lambda **kwargs: calls.append(("stdout", kwargs))))
    monkeypatch.setattr(audit.sys, "stderr", SimpleNamespace(
        reconfigure=lambda **kwargs: calls.append(("stderr", kwargs))))
    audit.configure_console()
    assert calls == [(name, {"encoding": "utf-8", "errors": "backslashreplace"})
                     for name in ("stdout", "stderr")]

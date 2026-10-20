"""Failure-focused checks for the independent foundations verifier.

These exercise the verification contract, not mathematical claims or physics.
No test invokes Lean, Lake, git, or a research calculation.
"""

import io
import json
from pathlib import Path
import subprocess
import sys

import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from scripts import verify_foundations as verify


class CompletedPopen:
    """A finished subprocess with real readable streams, never an OS process."""

    def __init__(self, result):
        self.pid = 4242
        self.returncode = result.returncode
        self.stdout = io.StringIO(result.stdout)
        self.stderr = io.StringIO(result.stderr)

    def wait(self, timeout=None):
        return self.returncode


@pytest.fixture
def project(tmp_path):
    (tmp_path / "GeneratedFoundations").mkdir()
    (tmp_path / "lean-toolchain").write_text(verify.EXPECTED_TOOLCHAIN, encoding="utf-8")
    (tmp_path / "lakefile.lean").write_text(
        'import Lake\nrequire mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "'
        + verify.EXPECTED_MATHLIB_REV + '"\nlean_lib GeneratedFoundations where\n'
        + '  leanOptions := #[⟨`autoImplicit, false⟩]\n', encoding="utf-8")
    (tmp_path / "lake-manifest.json").write_text(json.dumps({"packages": [{
        "name": "mathlib", "type": "git", "rev": verify.EXPECTED_MATHLIB_REV
    }]}), encoding="utf-8")
    (tmp_path / "GeneratedFoundations.lean").write_text("module\npublic import GeneratedFoundations.Basic\n", encoding="utf-8")
    (tmp_path / "GeneratedFoundations" / "Basic.lean").write_text(
        "module\n@[expose] public section\nnamespace GeneratedFoundations\ntheorem identity (p : Prop) (h : p) : p := h\nend GeneratedFoundations\n",
        encoding="utf-8")
    (tmp_path / "theorem-index.json").write_text(json.dumps({
        "schema_version": 1, "entry_modules": ["GeneratedFoundations"],
        "declarations": [{"name": "GeneratedFoundations.identity", "module": "GeneratedFoundations.Basic",
                          "paper": "A Spectral Construction of Natural-Number Arithmetic",
                          "label": "test:identity", "scope": "test fixture only"}], "planned": []
    }), encoding="utf-8")
    return tmp_path


def test_source_only_never_calls_process_or_claims_compilation(project, monkeypatch, capsys):
    def forbidden(*args, **kwargs):
        raise AssertionError("source-only must not run a subprocess")
    monkeypatch.setattr(verify.subprocess, "run", forbidden)
    assert verify.main(["--project-root", str(project), "--source-only"]) == 0
    output = capsys.readouterr().out
    assert "NOT COMPILED" in output
    assert "PASSED" not in output
    assert not (project / verify.MANIFEST_NAME).exists()


def test_compatibility_exports_are_kept_in_named_inventory():
    code = "namespace A\nexport Common.Proofs (\n  first\n  second\n)\nend A\n"
    assert verify.source_declarations(code) == {"A.first", "A.second"}
    assert verify.source_declarations("export Common.Proofs (third)\n") == {"third"}


def test_malformed_export_list_is_rejected():
    with pytest.raises(verify.VerificationError, match="Unterminated export"):
        verify.source_declarations("namespace A\nexport Common.Proofs (first\n")
    with pytest.raises(verify.VerificationError, match="Unsupported exported"):
        verify.source_declarations("export Common.Proofs (first => second)\n")


def test_subprocess_limits_lean_workers(project, monkeypatch):
    def fake_run(command, **options):
        assert options["env"]["LEAN_NUM_THREADS"] == "1"
        return subprocess.CompletedProcess(command, 0, "fixture output", "")
    monkeypatch.setattr(verify.subprocess, "run", fake_run)
    assert verify.run(["not-executed"], project, 10) == "fixture output"


def test_complete_audit_output_is_preserved_without_console_expansion(project, monkeypatch, capsys):
    output = "∀ (x : ℝ), x = x\n'example' depends on axioms: [propext]\n"
    monkeypatch.setattr(verify.subprocess, "Popen", lambda command, **options:
                        CompletedPopen(subprocess.CompletedProcess(command, 0, output, "")))
    log = project / ".lake" / "foundations-audit.txt"
    assert verify.run(["not-executed"], project, 10, output_path=log) == output
    assert log.read_text(encoding="utf-8") == output
    assert log.read_bytes() == output.encode("utf-8")
    assert "∀" not in capsys.readouterr().out


def test_nested_omitted_module_is_detected(project):
    extra = project / "GeneratedFoundations" / "Nested"
    extra.mkdir()
    (extra / "Omitted.lean").write_text("module\npublic theorem omitted : True := True.intro\n", encoding="utf-8")
    with pytest.raises(verify.VerificationError, match="import coverage"):
        verify.check_sources(project)


def test_missing_import_target_is_detected(project):
    (project / "GeneratedFoundations.lean").write_text("module\npublic import GeneratedFoundations.Missing\n", encoding="utf-8")
    with pytest.raises(verify.VerificationError, match="Missing local imports"):
        verify.check_sources(project)


def test_comments_and_strings_do_not_trigger_axiom_hygiene(project):
    basic = project / "GeneratedFoundations" / "Basic.lean"
    with basic.open("a", encoding="utf-8") as stream:
        stream.write('/- axiom outer /- sorry inner -/ admit -/\n-- axiom ignored\n')
        stream.write('def explanation : String := "sorry, admit, axiom; escaped \\\" quote"\n')
        stream.write('def rawExplanation : String := r#"sorry \\\" axiom"#\n')
    verify.check_sources(project)


@pytest.mark.parametrize("token", ["sorry", "admit", "axiom"])
def test_forbidden_source_tokens_fail(project, token):
    basic = project / "GeneratedFoundations" / "Basic.lean"
    with basic.open("a", encoding="utf-8") as stream:
        stream.write("\n" + token + "\n")
    with pytest.raises(verify.VerificationError, match="Forbidden"):
        verify.check_sources(project)


@pytest.mark.parametrize("filename", ["lean-toolchain", "lakefile.lean", "lake-manifest.json"])
def test_changed_pin_fails(project, filename):
    path = project / filename
    text = path.read_text(encoding="utf-8")
    text = text.replace(verify.EXPECTED_VERSION, "4.7.0").replace(verify.EXPECTED_MATHLIB_REV, "0" * 40)
    path.write_text(text, encoding="utf-8")
    with pytest.raises(verify.VerificationError):
        verify.check_sources(project)


def test_wrong_namespace_or_module_in_index_fails(project):
    path = project / "theorem-index.json"
    index = json.loads(path.read_text(encoding="utf-8"))
    index["declarations"][0]["name"] = "Other.identity"
    path.write_text(json.dumps(index), encoding="utf-8")
    with pytest.raises(verify.VerificationError, match="not found"):
        verify.check_sources(project)


def test_implicit_parameters_cannot_be_reenabled_in_library_config(project):
    path = project / "lakefile.lean"
    path.write_text(path.read_text(encoding="utf-8").replace(
        "`autoImplicit, false", "`autoImplicit, true"), encoding="utf-8")
    with pytest.raises(verify.VerificationError, match="autoImplicit"):
        verify.check_sources(project)


def test_implicit_parameters_cannot_be_reenabled_in_local_module(project):
    path = project / "GeneratedFoundations" / "Basic.lean"
    path.write_text(path.read_text(encoding="utf-8") + "\nset_option autoImplicit true\n", encoding="utf-8")
    with pytest.raises(verify.VerificationError, match="autoImplicit"):
        verify.check_sources(project)


def test_index_cannot_be_empty_or_only_planned(project):
    path = project / "theorem-index.json"
    index = json.loads(path.read_text(encoding="utf-8"))
    index["planned"] = index.pop("declarations")
    path.write_text(json.dumps(index), encoding="utf-8")
    with pytest.raises(verify.VerificationError, match="implemented declarations"):
        verify.check_sources(project)


def test_transitive_axiom_whitelist_and_missing_records():
    expected = ("GeneratedFoundations.identity",)
    verify.check_axiom_output("'GeneratedFoundations.identity' depends on axioms: [propext,\n Classical.choice, Quot.sound]", expected)
    verify.check_axiom_output("'GeneratedFoundations.identity' does not depend on any axioms", expected)
    for bad in ("sorryAx", "Lean.ofReduceBool", "Injected.assumption"):
        with pytest.raises(verify.VerificationError, match="Disallowed transitive"):
            verify.check_axiom_output(f"'GeneratedFoundations.identity' depends on axioms: [{bad}]", expected)
    with pytest.raises(verify.VerificationError, match="Expected one compiled"):
        verify.check_axiom_output("Build completed successfully", expected)


def test_full_mode_without_lake_does_not_claim_pass(project, monkeypatch, capsys):
    monkeypatch.setattr(verify.shutil, "which", lambda executable: None)
    assert verify.main(["--project-root", str(project)]) == 1
    output = capsys.readouterr()
    assert "PASSED" not in output.out
    assert "Lake not found" in output.err


def test_nested_names_and_section_scope():
    code = "namespace A\nnamespace B\nsection Named\n@[simp] theorem first : True := True.intro\nend Named\nend B\ndef last : Nat := 0\nend A\n"
    assert verify.source_declarations(code) == {"A.B.first", "A.last"}
    assert verify.source_declarations("theorem first' : True := True.intro\n") == {"first'"}


@pytest.mark.parametrize("name", ["adjoint_domain_iff_memℓp", "φ₀", "hölder'", "唯一性"])
def test_unicode_declaration_names_are_not_truncated(name):
    code = f"namespace Α\nsection Local\ntheorem {name} : True := True.intro\nend Local\nend Α\n"
    assert verify.source_declarations(code) == {f"Α.{name}"}


def test_unicode_index_name_reaches_complete_axiom_audit(project):
    name = "GeneratedFoundations.adjoint_domain_iff_memℓp"
    basic = project / "GeneratedFoundations" / "Basic.lean"
    basic.write_text(basic.read_text(encoding="utf-8").replace(
        "identity", "adjoint_domain_iff_memℓp"), encoding="utf-8")
    index_path = project / "theorem-index.json"
    index = json.loads(index_path.read_text(encoding="utf-8"))
    index["declarations"][0]["name"] = name
    index_path.write_text(json.dumps(index), encoding="utf-8")
    state = verify.check_sources(project)
    assert state.declarations == (name,)
    audit = verify.audit_source(state)
    assert f"#check {name}\n" in audit
    assert f"#print axioms {name}\n" in audit
    assert verify.check_axiom_output(
        f"'{name}' depends on axioms: [propext]", state.declarations) == {name: ["propext"]}
    with pytest.raises(verify.VerificationError, match="Expected one compiled"):
        verify.check_axiom_output(
            "'GeneratedFoundations.adjoint_domain_iff_mem' depends on axioms: [propext]",
            state.declarations)


def test_module_system_imports_and_public_sections():
    code = """module
public import Mathlib.Basic.Real.Basic
meta import Lean.Parser.Module.Syntax
public meta import Lean.Parser.Extra
import all GeneratedFoundations.Basic
@[expose] public section
namespace A
public theorem first : True := True.intro
section Inner
theorem second : True := True.intro
end Inner
end A
"""
    assert verify.imports(code) == {"Mathlib.Basic.Real.Basic", "Lean.Parser.Module.Syntax",
                                    "Lean.Parser.Extra", "GeneratedFoundations.Basic"}
    assert verify.source_declarations(code) == {"A.first", "A.second"}


def test_legacy_module_without_module_header_is_rejected(project):
    root = project / "GeneratedFoundations.lean"
    root.write_text("import GeneratedFoundations.Basic\n", encoding="utf-8")
    with pytest.raises(verify.VerificationError, match="module system"):
        verify.check_sources(project)


def test_fingerprint_includes_lock_index_and_recursive_sources(project):
    before = verify.fingerprint(project)
    assert "lean-toolchain" in before and "lake-manifest.json" in before
    assert "theorem-index.json" in before and "GeneratedFoundations/Basic.lean" in before
    (project / "theorem-index.json").write_text("{}", encoding="utf-8")
    assert verify.fingerprint(project) != before


def test_generated_audit_checks_all_signatures_and_complete_environment(project):
    state = verify.check_sources(project)
    audit = verify.audit_source(state)
    assert audit.startswith("module\n\npublic import ")
    assert "set_option format.width 160" in audit
    for name in state.declarations:
        assert f"set_option pp.all false in\n#check {name}" in audit
        assert f"set_option pp.all false in\nset_option pp.universes false in\n#print axioms {name}" in audit
    assert "set_option pp.all true" not in audit
    assert "import all GeneratedFoundations.Basic" in audit
    assert "env.constants.toList.toArray.filter" in audit
    assert "env.getModuleIdxFor? entry.1" in audit
    assert "moduleIndices.contains idx.toNat" in audit
    assert "counts := counts.modify idx.toNat (· + 1)" in audit
    assert "modules.contains env.header.moduleNames" not in audit
    assert "declarations.foldl" not in audit
    assert f'named declarations {len(state.declarations)}/{len(state.declarations)}' in audit
    assert "FOUNDATIONS_PROGRESS environment inventory start" in audit
    assert "FOUNDATIONS_PROGRESS axioms" in audit
    assert audit.count("set_option maxHeartbeats 0 in\n") == 2
    assert 'set_option maxHeartbeats 0 in\nelab "foundations_environment_audit"' in audit
    assert "set_option maxHeartbeats 0 in\nfoundations_environment_audit\n" in audit
    assert "set_option maxHeartbeats 0 in\n#check" not in audit
    assert "Lean.collectAxioms name" in audit
    assert "info.isUnsafe" in audit and "info.isPartial" in audit


def environment_output(declarations=None):
    """Simulated Lean inventory; contains names no source regex can discover."""
    if declarations is None:
        declarations = [{"name": "GeneratedFoundations.identity", "module": "GeneratedFoundations.Basic",
                         "kind": "theorem", "unsafe": False, "partial": False, "axioms": []}]
    records = [{"event": "begin", "count": len(declarations)}]
    for module in ("GeneratedFoundations", "GeneratedFoundations.Basic"):
        records.append({"event": "module", "module": module,
                        "count": sum(item["module"] == module for item in declarations), "import_all": True})
    records.extend({"event": "declaration", **item} for item in declarations)
    records.append({"event": "end", "count": len(declarations)})
    return "\n".join(verify.ENVIRONMENT_PREFIX + json.dumps(item) for item in records)


def named_output():
    return ("GeneratedFoundations.identity : ∀ (p : Prop), p → p\n"
            "'GeneratedFoundations.identity' does not depend on any axioms\n")


def test_resolved_export_is_linked_to_the_checked_constant(project):
    state = verify.check_sources(project)
    record = {"name": "GeneratedFoundations.identity", "resolved": "Common.Proofs.original",
              "axioms": ["propext"]}
    compiled = [{"name": record["resolved"], "module": "GeneratedFoundations.Basic",
                 "kind": "theorem", "unsafe": False, "partial": False, "axioms": ["propext"]}]
    output = verify.NAMED_PREFIX + json.dumps(record) + "\n" + environment_output(compiled)
    inventory, axioms = verify.check_environment_output(output, state)
    assert inventory["named_resolutions"] == {record["name"]: record["resolved"]}
    assert axioms == {record["resolved"]: ["propext"]}


@pytest.mark.parametrize("damage", ["missing_target", "duplicate", "incomplete", "axioms", "disagree"])
def test_resolved_export_reports_fail_closed(project, damage):
    state = verify.check_sources(project)
    record = {"name": "GeneratedFoundations.identity", "resolved": "Common.Proofs.original", "axioms": []}
    compiled = [{"name": record["resolved"], "module": "GeneratedFoundations.Basic",
                 "kind": "theorem", "unsafe": False, "partial": False, "axioms": []}]
    expected = state.declarations
    if damage == "missing_target":
        record["resolved"] = "Common.Proofs.missing"
    elif damage == "incomplete":
        expected += ("GeneratedFoundations.other",)
    elif damage == "axioms":
        record["axioms"] = ["Injected.assumption"]
    elif damage == "disagree":
        record["axioms"] = ["propext"]
    output = verify.NAMED_PREFIX + json.dumps(record) + "\n"
    if damage == "duplicate":
        output += output
    with pytest.raises(verify.VerificationError):
        if damage == "incomplete":
            verify.check_axiom_output(output, expected)
        else:
            verify.check_environment_output(output + environment_output(compiled), state)


def test_environment_audits_private_anonymous_and_generated_names_by_origin(project):
    state = verify.check_sources(project)
    names = ["GeneratedFoundations.identity", "_private.GeneratedFoundations.Basic.0.hidden",
             "_private.GeneratedFoundations.Basic.0.instAnonymous", "UnrelatedNamespace.macroClaim"]
    entries = [{"name": name, "module": "GeneratedFoundations.Basic", "kind": "theorem",
                "unsafe": False, "partial": False, "axioms": []} for name in names]
    inventory, axioms = verify.check_environment_output(named_output() + environment_output(entries), state)
    assert set(axioms) == set(names)
    assert inventory["modules"] == {"GeneratedFoundations": 0, "GeneratedFoundations.Basic": 4}
    assert inventory["independent_checker"] == "not_run"


@pytest.mark.parametrize("bad_axiom", ["sorryAx", "Lean.ofReduceBool", "Hidden.assumption"])
def test_unused_private_or_macro_generated_axioms_cannot_escape(project, bad_axiom):
    state = verify.check_sources(project)
    entries = [{"name": "GeneratedFoundations.identity", "module": "GeneratedFoundations.Basic",
                "kind": "theorem", "unsafe": False, "partial": False, "axioms": []},
               {"name": "_private.GeneratedFoundations.Basic.0.unused", "module": "GeneratedFoundations.Basic",
                "kind": "theorem", "unsafe": False, "partial": False, "axioms": [bad_axiom]}]
    with pytest.raises(verify.VerificationError, match="Disallowed transitive"):
        verify.check_environment_output(named_output() + environment_output(entries), state)


@pytest.mark.parametrize("damage", ["missing", "truncated", "duplicate", "module", "count",
                                    "public_only", "missing_named", "disagree", "malformed"])
def test_environment_inventory_fails_closed(project, damage):
    state = verify.check_sources(project)
    output = environment_output()
    if damage == "missing":
        output = ""
    elif damage == "truncated":
        output = "\n".join(output.splitlines()[:-1])
    elif damage == "duplicate":
        output = output + "\n" + output
    elif damage == "module":
        output = output.replace('"module": "GeneratedFoundations",', '"module": "Other",')
    elif damage == "count":
        output = output.replace('"count": 1', '"count": 2')
    elif damage == "public_only":
        output = output.replace('"import_all": true', '"import_all": false')
    elif damage == "missing_named":
        output = output.replace('"name": "GeneratedFoundations.identity"', '"name": "Other.hidden"')
    elif damage == "disagree":
        output = output.replace('"axioms": []', '"axioms": ["propext"]')
    else:
        output = output + "\n" + verify.ENVIRONMENT_PREFIX + "{"
    with pytest.raises(verify.VerificationError):
        verify.check_environment_output(named_output() + output, state)


@pytest.mark.parametrize("flag", ["unsafe", "partial"])
def test_unsafe_and_partial_constants_are_recorded_not_silently_skipped(project, flag):
    state = verify.check_sources(project)
    entries = [{"name": "GeneratedFoundations.identity", "module": "GeneratedFoundations.Basic",
                "kind": "theorem", "unsafe": False, "partial": False, "axioms": []},
               {"name": "_private.GeneratedFoundations.Basic.0.helper", "module": "GeneratedFoundations.Basic",
                "kind": "definition", "unsafe": False, "partial": False, "axioms": []}]
    entries[1][flag] = True
    inventory, _ = verify.check_environment_output(named_output() + environment_output(entries), state)
    assert inventory["declarations"][entries[1]["name"]][flag] is True


def test_build_order_places_imports_before_entry_module(project):
    state = verify.check_sources(project)
    assert verify.module_build_order(state) == (
        "GeneratedFoundations.Basic", "GeneratedFoundations")


def test_build_order_rejects_import_cycles(project):
    basic = project / "GeneratedFoundations" / "Basic.lean"
    basic.write_text(basic.read_text(encoding="utf-8").replace(
        "module\n", "module\npublic import GeneratedFoundations\n", 1), encoding="utf-8")
    state = verify.check_sources(project)
    with pytest.raises(verify.VerificationError, match="import cycle"):
        verify.module_build_order(state)


@pytest.fixture
def processes(project, monkeypatch):
    """Mock processes at their boundary, keeping publication and log capture real."""
    fake_lake = project / "lake.exe"
    fake_lake.write_bytes(b"test fixture, never executed")
    prefix = project / "toolchain"
    (prefix / "bin").mkdir(parents=True)
    (prefix / "bin" / ("lean.exe" if verify.os.name == "nt" else "lean")).write_bytes(b"Lean fixture")
    configuration = {"probe_code": 0, "probe_output": "Build completed successfully", "failure": None}
    calls = []
    monkeypatch.setattr(verify, "check_actual_dependencies", lambda *args: {
        "mathlib": {"revision": verify.EXPECTED_MATHLIB_REV, "tracked_clean": True}})

    def fake_run(command, **options):
        calls.append(command[1:])
        assert options["env"]["LEAN_NUM_THREADS"] == "1"
        assert options["encoding"] == "utf-8"
        failure = configuration["failure"]
        code = 0
        if command[1:] == ["env", "lean", "--version"]:
            version = "4.7.0" if failure == "wrong_version" else verify.EXPECTED_VERSION
            output = f"Lean (version {version}, test)"
        elif command[1:] == ["--version"]:
            output = f"Lake version test (Lean version {verify.EXPECTED_VERSION})"
        elif "--print-prefix" in command:
            output = str(prefix)
        elif command[1:4] == ["--no-cache", "--no-build", "build"]:
            if failure == "probe_timeout":
                raise subprocess.TimeoutExpired(command, options["timeout"])
            code, output = configuration["probe_code"], configuration["probe_output"]
        elif command[1:3] == ["--no-cache", "build"]:
            assert 1 <= len(command[3:]) <= verify.BUILD_BATCH_SIZE
            assert set(command[3:]) <= {"+GeneratedFoundations.Basic", "+GeneratedFoundations", "GeneratedFoundations"}
            code = 1 if failure == "build_failed" else 0
            output = "error: simulated failed Lean build" if code else "Build completed successfully"
            if configuration.get("build_warning_target") in command[3:]:
                output += "\nwarning: simulated compiler diagnostic"
        else:
            assert command[1:3] == ["--no-cache", "lean"]
            audit = Path(command[-1]).read_text(encoding="utf-8")
            assert "#check GeneratedFoundations.identity" in audit
            if failure == "concurrent_source_change":
                with (project / "GeneratedFoundations.lean").open("a", encoding="utf-8") as stream:
                    stream.write("-- changed during verification\n")
            if "audit_hook" in configuration:
                configuration["audit_hook"]()
            output = ("unexpected compiler output" if failure == "missing_axiom_report" else
                      named_output() + environment_output())
        return subprocess.CompletedProcess(command, code, output, "")

    monkeypatch.setattr(verify.subprocess, "run", fake_run)
    monkeypatch.setattr(verify.subprocess, "Popen", lambda command, **options:
                        CompletedPopen(fake_run(command, **options)))
    return configuration, calls, ["--project-root", str(project), "--lake-exe", str(fake_lake)]


@pytest.mark.parametrize("failure", [None, "wrong_version", "build_failed", "missing_axiom_report", "concurrent_source_change"])
def test_full_verification_only_complete_evidence_claims_pass(project, processes, capsys, failure):
    configuration, calls, arguments = processes
    configuration["failure"] = failure
    if failure == "build_failed":
        configuration["probe_code"] = 3
    assert verify.main(arguments) == (0 if failure is None else 1)
    output = capsys.readouterr()
    if failure is None:
        assert "FOUNDATIONS VERIFY PASSED" in output.out
        assert "FAILED" not in output.err
        manifest = json.loads((project / verify.MANIFEST_NAME).read_text(encoding="utf-8"))
        assert manifest["source_files"] == verify.fingerprint(project)
        assert manifest["verifier"]["sha256"] == verify.sha256_file(verify.VERIFIER_PATH)
        assert manifest["declaration_axioms"] == {"GeneratedFoundations.identity": []}
        assert manifest["environment_audit"]["method"] == verify.ENVIRONMENT_METHOD
        assert manifest["environment_audit"]["independent_checker"] == "not_run"
        assert manifest["audit"]["sha256"] == verify.sha256_file(project / verify.AUDIT_LOG)
        assert manifest["semantic_review"] == "not_certified"
        assert manifest["tools"]["lean_version"].startswith("Lean (version 4.34.0")
        assert str(project) not in json.dumps(manifest)
    else:
        assert "PASSED" not in output.out
        assert "FAILED" in output.err
        assert not (project / verify.MANIFEST_NAME).exists()


@pytest.mark.parametrize("code", [0, 3])
def test_freshness_probe_covers_all_modules_and_never_skips_axiom_audit(project, processes, code):
    configuration, calls, arguments = processes
    configuration["probe_code"] = code
    assert verify.main(arguments) == 0
    assert ["--no-cache", "--no-build", "build", "GeneratedFoundations",
            "+GeneratedFoundations.Basic", "+GeneratedFoundations"] in calls
    builds = [call for call in calls if call[:2] == ["--no-cache", "build"]]
    expected_builds = [] if code == 0 else [
        ["--no-cache", "build", "+GeneratedFoundations.Basic"],
        ["--no-cache", "build", "+GeneratedFoundations"],
        ["--no-cache", "build", "GeneratedFoundations"]]
    assert builds == expected_builds
    assert len([call for call in calls if call[:2] == ["--no-cache", "lean"]]) == 1
    manifest = json.loads((project / verify.MANIFEST_NAME).read_text(encoding="utf-8"))
    assert manifest["build_mode"] == ("up_to_date" if code == 0 else "batched_build")


def test_rebuild_batches_bound_targets_preserve_dependencies_and_check_library(project, monkeypatch):
    for name in ("Middle", "Other", "Top"):
        parent = "Basic" if name != "Top" else "Middle"
        (project / "GeneratedFoundations" / (name + ".lean")).write_text(
            f"module\npublic import GeneratedFoundations.{parent}\n", encoding="utf-8")
    (project / "GeneratedFoundations.lean").write_text(
        "module\npublic import GeneratedFoundations.Top\npublic import GeneratedFoundations.Other\n",
        encoding="utf-8")
    state = verify.check_sources(project)
    order = verify.module_build_order(state)
    calls = []
    monkeypatch.setattr(verify, "run_result", lambda *args: (3, "unrecognized stale output"))

    def record(command, *args):
        calls.append(command)
        return "Build completed successfully"

    monkeypatch.setattr(verify, "run", record)
    mode, built = verify.build_modules("lake", project, state, 30)
    batches = [command[3:] for command in calls[:-1]]
    assert mode == "batched_build" and built == order
    assert all(1 <= len(batch) <= verify.BUILD_BATCH_SIZE for batch in batches)
    assert any(len(batch) > 1 for batch in batches)
    assert sorted(target for batch in batches for target in batch) == sorted("+" + module for module in order)
    finished = set()
    for batch in batches:
        for target in batch:
            dependencies = verify.imports(verify.lean_code(state.modules[target[1:]].read_text(encoding="utf-8")))
            assert dependencies & state.modules.keys() <= finished
        finished.update(target[1:] for target in batch)
    assert calls[-1] == ["lake", "--no-cache", "build", verify.LIBRARY]


def test_stale_frontier_rebuild_includes_every_local_dependent(project):
    state = verify.check_sources(project)
    order = verify.module_build_order(state)
    assert verify.affected_build_order(state, order,
        "Building GeneratedFoundations.Basic\nerror: target is out-of-date") == order
    assert verify.affected_build_order(state, order,
        "Building GeneratedFoundations\nerror: target is out-of-date") == ("GeneratedFoundations",)


@pytest.mark.parametrize("output", ["unrecognized stale output", "Building External.Dependency"])
def test_unrecognized_stale_frontier_uses_full_order(project, output):
    state = verify.check_sources(project)
    order = verify.module_build_order(state)
    assert verify.affected_build_order(state, order, output) == order


@pytest.mark.parametrize("code", [1, 2, 4, -9])
def test_other_probe_errors_never_fall_back_or_publish(project, processes, code):
    configuration, calls, arguments = processes
    configuration["probe_code"] = code
    assert verify.main(arguments) == 1
    assert not any(call[:2] in (["--no-cache", "build"], ["--no-cache", "lean"]) for call in calls)
    assert not (project / verify.MANIFEST_NAME).exists()


def test_probe_timeout_never_falls_back(project, processes):
    configuration, calls, arguments = processes
    configuration["failure"] = "probe_timeout"
    assert verify.main(arguments) == 1
    assert not any(call[:2] == ["--no-cache", "build"] for call in calls)
    assert not (project / verify.MANIFEST_NAME).exists()


def test_fresh_probe_warning_rejects_stored_diagnostics(project, processes):
    configuration, calls, arguments = processes
    configuration["probe_output"] = "warning: diagnostic replayed from a prior compilation"
    assert verify.main(arguments) == 1
    assert not any(call[:2] == ["--no-cache", "lean"] for call in calls)
    assert not (project / verify.MANIFEST_NAME).exists()


@pytest.mark.parametrize("target", ["+GeneratedFoundations.Basic", "+GeneratedFoundations", "GeneratedFoundations"])
def test_build_collects_warnings_but_never_audits_or_publishes_success(project, processes, target):
    configuration, calls, arguments = processes
    configuration["probe_code"] = 3
    configuration["build_warning_target"] = target
    assert verify.main(arguments) == 1
    assert [target for call in calls if call[:2] == ["--no-cache", "build"] for target in call[2:]] == [
        "+GeneratedFoundations.Basic", "+GeneratedFoundations", "GeneratedFoundations"]
    assert not any(call[:2] == ["--no-cache", "lean"] for call in calls)
    assert not (project / verify.MANIFEST_NAME).exists()


def test_cycle_is_rejected_before_freshness_probe(project, processes):
    configuration, calls, arguments = processes
    basic = project / "GeneratedFoundations" / "Basic.lean"
    basic.write_text(basic.read_text(encoding="utf-8").replace(
        "module\n", "module\npublic import GeneratedFoundations\n", 1), encoding="utf-8")
    assert verify.main(arguments) == 1
    assert not any("--no-build" in call for call in calls)


@pytest.mark.parametrize("changed", ["verifier", "tools", "dependencies"])
def test_verification_rejects_environment_changes_during_audit(project, processes, monkeypatch, changed):
    configuration, calls, arguments = processes
    if changed == "verifier":
        copied = project / "verifier-copy.py"
        copied.write_bytes(verify.VERIFIER_PATH.read_bytes())
        monkeypatch.setattr(verify, "VERIFIER_PATH", copied)
        configuration["audit_hook"] = lambda: copied.write_text("# replacement verifier", encoding="utf-8")
    elif changed == "tools":
        configuration["audit_hook"] = lambda: (project / "lake.exe").write_bytes(b"changed tool")
    else:
        configuration["audit_hook"] = lambda: monkeypatch.setattr(
            verify, "check_actual_dependencies", lambda *args: {})
    assert verify.main(arguments) == 1
    assert not (project / verify.MANIFEST_NAME).exists()


def test_current_manifest_check_is_read_only_and_does_not_claim_new_pass(project, processes, capsys):
    configuration, calls, arguments = processes
    assert verify.main(arguments) == 0
    before = (project / verify.MANIFEST_NAME).read_bytes()
    capsys.readouterr()
    calls.clear()
    assert verify.main(arguments + ["--check-manifest"]) == 0
    assert (project / verify.MANIFEST_NAME).read_bytes() == before
    assert not any("--no-cache" in call for call in calls)
    output = capsys.readouterr().out
    assert "MANIFEST CURRENT" in output and "No new compilation" in output
    assert "VERIFY PASSED" not in output


@pytest.mark.parametrize("changed", ["manifest", "log"])
def test_manifest_check_rejects_evidence_changed_during_environment_checks(project, processes, monkeypatch, changed):
    configuration, calls, arguments = processes
    assert verify.main(arguments) == 0
    prior = verify.check_actual_dependencies
    def changed_during_check(*args):
        if changed == "manifest":
            (project / verify.MANIFEST_NAME).write_text("{}", encoding="utf-8")
        else:
            (project / verify.AUDIT_LOG).write_text("overwritten log", encoding="utf-8")
        return prior(*args)
    monkeypatch.setattr(verify, "check_actual_dependencies", changed_during_check)
    assert verify.main(arguments + ["--check-manifest"]) == 1


@pytest.mark.parametrize("changed", ["source", "index", "verifier", "log", "missing_log", "tools", "dependencies",
                                     "axioms", "coverage", "schema", "identity", "time", "mode", "probe",
                                     "environment", "environment_missing", "external_checker"])
def test_saved_success_cannot_hide_stale_or_incomplete_evidence(project, processes, monkeypatch, capsys, changed):
    configuration, calls, arguments = processes
    assert verify.main(arguments) == 0
    capsys.readouterr()
    target = project / verify.MANIFEST_NAME
    manifest = json.loads(target.read_text(encoding="utf-8"))
    if changed == "source":
        basic = project / "GeneratedFoundations" / "Basic.lean"
        basic.write_text(basic.read_text(encoding="utf-8") + "\n-- new revision\n", encoding="utf-8")
    elif changed == "index":
        index = project / "theorem-index.json"
        index.write_text(index.read_text(encoding="utf-8") + "\n", encoding="utf-8")
    elif changed == "verifier":
        other = project / "another-verifier.py"
        other.write_text("# changed verifier", encoding="utf-8")
        monkeypatch.setattr(verify, "VERIFIER_PATH", other)
    elif changed == "log":
        (project / verify.AUDIT_LOG).write_text("different log", encoding="utf-8")
    elif changed == "missing_log":
        (project / verify.AUDIT_LOG).unlink()
    elif changed == "tools":
        (project / "lake.exe").write_bytes(b"replaced executable")
    elif changed == "dependencies":
        monkeypatch.setattr(verify, "check_actual_dependencies", lambda *args: {})
    else:
        if changed == "axioms":
            manifest["declaration_axioms"]["GeneratedFoundations.identity"] = ["sorryAx"]
        elif changed == "coverage":
            manifest["declaration_axioms"] = {}
        elif changed == "schema":
            manifest["schema_version"] = 2
        elif changed == "identity":
            del manifest["verification_id"]
        elif changed == "time":
            manifest["verified_at"] = "2999-01-01T00:00:00+00:00"
        elif changed == "mode":
            manifest["build_mode"] = "source_only"
        elif changed == "probe":
            manifest["audit"]["probe_sha256"] = "0" * 64
        elif changed == "environment":
            manifest["environment_audit"]["declarations"] = {}
        elif changed == "environment_missing":
            del manifest["environment_audit"]
        elif changed == "external_checker":
            manifest["environment_audit"]["independent_checker"] = "passed"
        target.write_text(json.dumps(manifest), encoding="utf-8")
    assert verify.main(arguments + ["--check-manifest"]) == 1
    output = capsys.readouterr()
    assert "MANIFEST CURRENT" not in output.out and "PASSED" not in output.out
    assert "STALE OR INVALID" in output.err


def test_failed_run_retains_previous_manifest_without_claiming_this_run_passed(project, processes, capsys):
    configuration, calls, arguments = processes
    assert verify.main(arguments) == 0
    before = (project / verify.MANIFEST_NAME).read_bytes()
    capsys.readouterr()
    configuration["probe_code"] = 2
    assert verify.main(arguments) == 1
    assert (project / verify.MANIFEST_NAME).read_bytes() == before
    assert "PASSED" not in capsys.readouterr().out


def test_failed_atomic_publication_preserves_previous_record(project, processes, monkeypatch, capsys):
    configuration, calls, arguments = processes
    assert verify.main(arguments) == 0
    before = (project / verify.MANIFEST_NAME).read_bytes()
    capsys.readouterr()
    def failed_replace(*args):
        raise OSError("simulated publication failure")
    monkeypatch.setattr(verify.os, "replace", failed_replace)
    assert verify.main(arguments) == 1
    assert (project / verify.MANIFEST_NAME).read_bytes() == before
    assert not list(project.glob(".verification-manifest.json.*.tmp"))
    assert "PASSED" not in capsys.readouterr().out


@pytest.mark.parametrize("filename", ["theorem-index.json", "lake-manifest.json", "run_manifest.json", "RUN_MANIFEST.JSON"])
def test_manifest_cannot_overwrite_source_or_numerical_identity(project, processes, filename):
    configuration, calls, arguments = processes
    target = project / filename
    if not target.exists():
        target.write_text('{"historical":true}', encoding="utf-8")
    before = target.read_bytes()
    assert verify.main(arguments + ["--manifest", str(target)]) == 1
    assert target.read_bytes() == before
    assert not calls


def test_custom_manifest_is_independent_and_checkable(project, processes):
    configuration, calls, arguments = processes
    target = project / "proof-evidence" / "independent.json"
    numeric = project / "run_manifest.json"
    numeric.write_text('{"run_id":"historical-numerical-run"}', encoding="utf-8")
    before = numeric.read_bytes()
    assert verify.main(arguments + ["--manifest", str(target)]) == 0
    assert not (project / verify.MANIFEST_NAME).exists()
    assert verify.main(arguments + ["--manifest", str(target), "--check-manifest"]) == 0
    assert numeric.read_bytes() == before


def test_logged_progress_is_visible_before_exit_and_preserves_stream_order(project, monkeypatch, capsys):
    stdout = "ordinary stdout\nFOUNDATIONS_PROGRESS named 10/20\n"
    stderr = "ordinary stderr\nFOUNDATIONS_PROGRESS environment 1/2\n"
    progress_seen = verify.threading.Event()
    original_print = print

    def observe_print(*args, **options):
        original_print(*args, **options)
        if args and str(args[0]).startswith("FOUNDATIONS_PROGRESS named"):
            assert options.get("flush") is True
            progress_seen.set()

    class StillRunningPopen(CompletedPopen):
        def wait(self, timeout=None):
            assert progress_seen.wait(timeout=2), "progress must be visible before process exit"
            return self.returncode

    def fake_popen(command, **options):
        assert options["env"]["LEAN_NUM_THREADS"] == "1"
        assert options["stdout"] == subprocess.PIPE and options["stderr"] == subprocess.PIPE
        if verify.os.name == "nt":
            assert options["creationflags"] == subprocess.CREATE_NEW_PROCESS_GROUP
        else:
            assert options["start_new_session"] is True
        return StillRunningPopen(subprocess.CompletedProcess(command, 0, stdout, stderr))

    monkeypatch.setattr(verify, "print", observe_print, raising=False)
    monkeypatch.setattr(verify.subprocess, "Popen", fake_popen)
    log = project / ".lake" / "progress.txt"
    assert verify.run(["not-executed"], project, 10, output_path=log) == stdout + stderr
    assert log.read_text(encoding="utf-8") == stdout + stderr
    console = capsys.readouterr().out
    assert "FOUNDATIONS_PROGRESS named 10/20" in console
    assert "FOUNDATIONS_PROGRESS environment 1/2" in console
    assert "ordinary stdout" not in console and "ordinary stderr" not in console


def test_logged_timeout_cleans_own_process_and_saves_incomplete_output(project, monkeypatch, capsys):
    command = ["not-executed"]
    stdout, stderr = "captured stdout\n", "captured stderr\n"

    class TimedOutPopen(CompletedPopen):
        def wait(self, timeout=None):
            raise subprocess.TimeoutExpired(command, timeout)

    process = TimedOutPopen(subprocess.CompletedProcess(command, 0, stdout, stderr))
    cleaned = []
    monkeypatch.setattr(verify.subprocess, "Popen", lambda *args, **options: process)
    monkeypatch.setattr(verify, "stop_owned_process_tree", cleaned.append)
    log = project / ".lake" / "timeout.txt"
    with pytest.raises(subprocess.TimeoutExpired):
        verify.run(command, project, 10, output_path=log)
    assert cleaned == [process]
    saved = log.read_text(encoding="utf-8")
    assert saved.startswith("FOUNDATIONS_AUDIT_INCOMPLETE: command timed out after 10 seconds\n")
    assert saved.endswith(stdout + stderr)
    assert "Complete declaration" not in capsys.readouterr().out


@pytest.mark.parametrize("platform", ["nt", "posix"])
def test_cleanup_targets_only_the_owned_pid_or_new_session(monkeypatch, platform):
    process = CompletedPopen(subprocess.CompletedProcess(["not-executed"], 0, "", ""))
    calls = []
    monkeypatch.setattr(verify.subprocess, "run", lambda command, **options: calls.append((command, options)))
    monkeypatch.setattr(verify.os, "killpg", lambda pid, sig: calls.append((pid, sig)), raising=False)
    monkeypatch.setattr(verify.signal, "SIGKILL", 9, raising=False)
    # Restore os.name before pytest or pathlib performs any platform-sensitive work.
    with monkeypatch.context() as platform_patch:
        platform_patch.setattr(verify.os, "name", platform)
        verify.stop_owned_process_tree(process)
    if platform == "nt":
        command, options = calls[0]
        assert command == ["taskkill", "/PID", "4242", "/T", "/F"]
        assert options["timeout"] == 15 and options["check"] is True
    else:
        assert calls == [(4242, verify.signal.SIGKILL)]


def test_audit_timeout_never_publishes_a_success_manifest(project, processes, monkeypatch, capsys):
    _, _, arguments = processes
    assert verify.main(arguments) == 0
    manifest = project / verify.MANIFEST_NAME
    previous = manifest.read_bytes()
    capsys.readouterr()
    ordinary_popen = verify.subprocess.Popen

    def timed_out_popen(command, **options):
        process = ordinary_popen(command, **options)

        def wait(timeout=None):
            raise subprocess.TimeoutExpired(command, timeout)

        process.wait = wait
        return process

    monkeypatch.setattr(verify.subprocess, "Popen", timed_out_popen)
    monkeypatch.setattr(verify, "stop_owned_process_tree", lambda process: None)
    assert verify.main(arguments) == 1
    assert manifest.read_bytes() == previous
    assert (project / verify.AUDIT_LOG).read_text(encoding="utf-8").startswith("FOUNDATIONS_AUDIT_INCOMPLETE:")
    output = capsys.readouterr()
    assert "PASSED" not in output.out and "FAILED" in output.err
    assert verify.main(arguments + ["--check-manifest"]) == 1


def test_axiom_report_parser_preserves_apostrophes_unicode_and_multiline_lists():
    expected = ("Α.φ₀", "Α.hölder'", "Α.derivative''", "Α.inner'name")
    output = (
        "ordinary audit text\n"
        "'Α.hölder'' depends on axioms:\n[propext,\n Classical.choice, Quot.sound]\n"
        "'Α.derivative''' does not depend on any axioms\n"
        "'Α.inner'name' depends on axioms: [Quot.sound, Quot.sound]\n"
        "'Α.φ₀' does not depend on any axioms\n")
    assert verify.check_axiom_output(output, expected) == {
        "Α.φ₀": [], "Α.hölder'": ["Classical.choice", "Quot.sound", "propext"],
        "Α.derivative''": [], "Α.inner'name": ["Quot.sound"]}


def test_axiom_report_parser_ignores_only_reports_outside_expected_names():
    output = (
        "'A.claim' depends on axioms: [propext]\n"
        "'A.claim'' depends on axioms: [Injected.assumption]\n"
        "'A.claim'' does not depend on any axioms\n"
        "'A.other' depends on axioms: [sorryAx]\n")
    assert verify.check_axiom_output(output, ("A.claim",)) == {"A.claim": ["propext"]}
    with pytest.raises(verify.VerificationError, match="got 0"):
        verify.check_axiom_output(output, ("A.missing",))
    with pytest.raises(verify.VerificationError, match="got 2"):
        verify.check_axiom_output(output, ("A.claim'",))
    with pytest.raises(verify.VerificationError, match="Disallowed transitive"):
        verify.check_axiom_output(output, ("A.other",))


@pytest.mark.parametrize("report", ["does not depend on any axioms", "depends on axioms: [propext]"])
def test_axiom_report_parser_rejects_duplicate_expected_records(report):
    output = f"'A.claim' {report}\n'A.claim' depends on axioms:\n[Quot.sound]\n"
    with pytest.raises(verify.VerificationError, match="got 2"):
        verify.check_axiom_output(output, ("A.claim",))

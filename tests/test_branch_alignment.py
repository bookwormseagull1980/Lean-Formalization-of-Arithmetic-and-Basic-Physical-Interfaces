"""Fail-closed checks for the Lean branch correspondence inventory."""

from pathlib import Path
import sys

import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from scripts import branch_alignment as alignment
from scripts import verify_foundations as verify


@pytest.fixture
def tiny_project(tmp_path, monkeypatch):
    def source(module, text):
        path = tmp_path / (module.replace(".", "/") + ".lean")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")
        return path

    source("GeneratedFoundations.ArithmeticFoundation",
        "import GeneratedFoundations.Source.CanonicalRealization\n")
    source("GeneratedFoundations.PhysicalInterface",
        "import GeneratedFoundations.Physical.SourceOrigin\n")
    source("GeneratedFoundations.Source.CanonicalRealization",
        "import GeneratedFoundations.Source.CommonSource\n"
        "namespace GeneratedFoundations.Source.CanonicalRealization\n"
        "theorem generated : True := by trivial\nend\n")
    source("GeneratedFoundations.Source.CommonSource",
        "namespace GeneratedFoundations.Source.CommonSource\n"
        "theorem generated : True := by trivial\nend\n")
    source("GeneratedFoundations.Physical.SourceOrigin",
        "import GeneratedFoundations.Source.CommonSource\n"
        "namespace GeneratedFoundations.Physical.SourceOrigin\n"
        "theorem generated : True := by trivial\nend\n")
    monkeypatch.setattr(alignment, "FAMILIES", {"A": {
        "method": "test correspondence", "physical": "SourceOrigin",
        "mathematical": ["Source.CanonicalRealization"],
    }})
    return tmp_path, source


def test_inventory_does_not_mark_correspondence_as_proof(tiny_project):
    project, _ = tiny_project
    report = alignment.inventory(project)
    assert report["evidence"] == "source_inventory_only"
    assert report["physical_declarations"] == 1
    assert report["review_status_counts"] == {"pending_declaration_review": 1}


def test_new_physical_module_requires_explicit_assignment(tiny_project):
    project, source = tiny_project
    source("GeneratedFoundations.Physical.AddedLater", "def unseen : Nat := 1\n")
    with pytest.raises(verify.VerificationError, match="assignments differ"):
        alignment.inventory(project)


def test_physical_import_is_rejected_transitively(tiny_project):
    project, source = tiny_project
    source("GeneratedFoundations.Source.CanonicalRealization",
        "import GeneratedFoundations.Source.CommonSource\n"
        "import GeneratedFoundations.Physical.SourceOrigin\n")
    with pytest.raises(verify.VerificationError, match="imports physical branch"):
        alignment.inventory(project)


def test_comment_import_does_not_create_a_dependency(tiny_project):
    project, source = tiny_project
    source("GeneratedFoundations.Source.CanonicalRealization",
        "import GeneratedFoundations.Source.CommonSource\n"
        "/- import GeneratedFoundations.Physical.SourceOrigin -/\ndef source : Nat := 1\n")
    assert alignment.inventory(project)["mathematical_entry_independent_of_physical"]


def test_arithmetic_import_is_rejected_transitively(tiny_project):
    project, source = tiny_project
    source("GeneratedFoundations.Arithmetic.Helper", "def arithmeticOnly : Nat := 1\n")
    source("GeneratedFoundations.Physical.SourceOrigin",
        "import GeneratedFoundations.Source.CommonSource\n"
        "import GeneratedFoundations.Arithmetic.Helper\n")
    with pytest.raises(verify.VerificationError, match="imports mathematical branch"):
        alignment.inventory(project)


def test_physical_entry_cannot_import_mathematical_interface(tiny_project):
    project, source = tiny_project
    source("GeneratedFoundations.MathematicalInterface", "def mathematicalOnly : Nat := 1\n")
    source("GeneratedFoundations.Physical.SourceOrigin",
        "import GeneratedFoundations.Source.CommonSource\n"
        "import GeneratedFoundations.MathematicalInterface\n")
    with pytest.raises(verify.VerificationError, match="imports mathematical branch"):
        alignment.inventory(project)


def test_arithmetic_import_in_physical_comment_is_ignored(tiny_project):
    project, source = tiny_project
    source("GeneratedFoundations.Arithmetic.Helper", "def arithmeticOnly : Nat := 1\n")
    source("GeneratedFoundations.Physical.SourceOrigin",
        "import GeneratedFoundations.Source.CommonSource\n"
        "/- import GeneratedFoundations.Arithmetic.Helper -/\ndef source : Nat := 1\n")
    assert alignment.inventory(project)["physical_entry_independent_of_mathematical"]


def test_changed_physical_statement_invalidates_review(tiny_project):
    project, _ = tiny_project
    reviews = {"GeneratedFoundations.Physical.SourceOrigin.generated": {
        "status": "reviewed", "source_sha256": "old-snapshot",
        "mathematical_declarations": [],
    }}
    with pytest.raises(verify.VerificationError, match="Stale declaration"):
        alignment.inventory(project, reviews)


def test_missing_mathematical_proof_is_rejected(tiny_project):
    project, _ = tiny_project
    record = alignment.inventory(project)["declarations"][0]
    reviews = {record["physical_declaration"]: {
        "status": "proved_analogue",
        "source_sha256": record["source_sha256"],
        "mathematical_declarations": ["GeneratedFoundations.Missing.proof"],
    }}
    with pytest.raises(verify.VerificationError, match="Missing mathematical declaration"):
        alignment.inventory(project, reviews)


def test_unknown_review_cannot_hide_a_removed_declaration(tiny_project):
    project, _ = tiny_project
    with pytest.raises(verify.VerificationError, match="removed declarations"):
        alignment.inventory(project, {"NoLongerExists": {"status": "reviewed"}})


def test_both_branches_use_the_same_source(tiny_project):
    project, source = tiny_project
    source("GeneratedFoundations.Physical.SourceOrigin", "def separateRoot : Nat := 1\n")
    with pytest.raises(verify.VerificationError, match="same common source"):
        alignment.inventory(project)


def test_common_source_cannot_import_a_branch(tiny_project):
    project, source = tiny_project
    source("GeneratedFoundations.Source.CommonSource",
        "import GeneratedFoundations.Physical.SourceOrigin\n")
    with pytest.raises(verify.VerificationError, match="Common source depends on a branch"):
        alignment.inventory(project)


def test_completion_without_mathematical_proof_is_rejected(tiny_project):
    project, _ = tiny_project
    record = alignment.inventory(project)["declarations"][0]
    reviews = {record["physical_declaration"]: {
        "status": "proved_analogue", "source_sha256": record["source_sha256"],
        "mathematical_declarations": [],
    }}
    with pytest.raises(verify.VerificationError, match="no actual mathematical declarations"):
        alignment.inventory(project, reviews)


def test_physical_proof_cannot_complete_mathematical_review(tiny_project):
    project, _ = tiny_project
    record = alignment.inventory(project)["declarations"][0]
    reviews = {record["physical_declaration"]: {
        "status": "proved_analogue", "source_sha256": record["source_sha256"],
        "mathematical_declarations": [record["physical_declaration"]],
    }}
    with pytest.raises(verify.VerificationError, match="outside entry"):
        alignment.inventory(project, reviews)


def test_unknown_status_cannot_complete_inventory(tiny_project):
    project, _ = tiny_project
    record = alignment.inventory(project)["declarations"][0]
    reviews = {record["physical_declaration"]: {
        "status": "all_done", "source_sha256": record["source_sha256"],
    }}
    with pytest.raises(verify.VerificationError, match="Unknown declaration review status"):
        alignment.inventory(project, reviews)


def test_completed_review_requires_object_and_scope_comparison(tiny_project):
    project, _ = tiny_project
    record = alignment.inventory(project)["declarations"][0]
    reviews = {record["physical_declaration"]: {
        "status": "shared_result", "source_sha256": record["source_sha256"],
        "mathematical_declarations": ["GeneratedFoundations.Source.CanonicalRealization.generated"],
    }}
    with pytest.raises(verify.VerificationError, match="Review missing objects"):
        alignment.inventory(project, reviews)


def feature_records():
    return {f"{g}{i}": {
        "scope_class": "shared_construction",
        "mathematical_declarations": ["GeneratedFoundations.Source.CanonicalRealization.generated"],
        "objects": "The same source.", "construction": "Shared theorem.",
        "hypotheses_and_scope": "Zero-argument source entry.",
    } for g, titles in alignment.FEATURES.items() for i, _ in enumerate(titles, 1)}


def test_feature_ledger_cannot_omit_a_feature(tiny_project):
    project, _ = tiny_project
    features = feature_records()
    del features["F8"]
    with pytest.raises(verify.VerificationError, match="cover all 56"):
        alignment.inventory(project, features=features)


def test_feature_ledger_cannot_use_unreachable_proof(tiny_project):
    project, source = tiny_project
    source("GeneratedFoundations.Disconnected", "theorem isolated : True := by trivial\n")
    features = feature_records()
    features["E6"]["mathematical_declarations"] = ["isolated"]
    with pytest.raises(verify.VerificationError, match="outside mathematical entry"):
        alignment.inventory(project, features=features)


def test_feature_ledger_does_not_complete_unreviewed_declarations(tiny_project):
    project, _ = tiny_project
    report = alignment.inventory(project, features=feature_records())
    assert len(report["feature_proof_ledger"]) == 56
    assert report["unreviewed_or_unconstructed"] == 1


def test_support_declarations_are_not_omitted_or_automatically_reviewed(tiny_project):
    project, _ = tiny_project
    report = alignment.inventory(project)
    shared = {r["physical_declaration"]: r for r in report["support_declarations"]}
    name = "GeneratedFoundations.Source.CommonSource.generated"
    assert shared[name]["mathematical_availability"] == "identical_declaration"
    assert shared[name]["identical_mathematical_declaration"] == name
    assert shared[name]["correspondence_review"]["status"] == "pending_declaration_review"
    assert report["identical_shared_support_declarations"] == 1
    assert report["support_unreviewed_or_unconstructed"] == 1


def test_unshared_support_and_public_entry_have_individual_records(tiny_project):
    project, source = tiny_project
    source("GeneratedFoundations.PhysicalInterface",
        "import GeneratedFoundations.Physical.SourceOrigin\n"
        "import GeneratedFoundations.Geometry.PhysicalSupport\n"
        "namespace GeneratedFoundations.PhysicalInterface\n"
        "theorem generated : True := by trivial\nend\n")
    source("GeneratedFoundations.Geometry.PhysicalSupport",
        "namespace GeneratedFoundations.Geometry.PhysicalSupport\n"
        "theorem complete : True := by trivial\nend\n")
    rows = {r["physical_declaration"]: r for r in alignment.inventory(project)["support_declarations"]}
    assert rows["GeneratedFoundations.PhysicalInterface.generated"]["entry_or_dependency"] == "public_entry"
    support = rows["GeneratedFoundations.Geometry.PhysicalSupport.complete"]
    assert support["mathematical_availability"] == "not_imported"
    assert support["identical_mathematical_declaration"] is None


def test_support_of_unimported_physical_module_is_still_inventoried(tiny_project, monkeypatch):
    project, source = tiny_project
    monkeypatch.setitem(alignment.FAMILIES["A"], "physical", "SourceOrigin Extra")
    source("GeneratedFoundations.Physical.Extra",
        "import GeneratedFoundations.Spectral.ExtraSupport\n")
    source("GeneratedFoundations.Spectral.ExtraSupport", "def isolatedSupport : Nat := 1\n")
    rows = alignment.inventory(project)["support_declarations"]
    assert any(r["physical_declaration"] == "isolatedSupport" for r in rows)


def test_support_review_uses_the_same_source_hash_and_proof_checks(tiny_project):
    project, _ = tiny_project
    row = alignment.inventory(project)["support_declarations"][0]
    reviews = {row["physical_declaration"]: {
        "status": "shared_result", "source_sha256": "wrong-source",
        "mathematical_declarations": [row["physical_declaration"]],
    }}
    with pytest.raises(verify.VerificationError, match="Stale declaration"):
        alignment.inventory(project, reviews)


def test_unimported_physical_module_cannot_hide_arithmetic_dependency(tiny_project, monkeypatch):
    project, source = tiny_project
    monkeypatch.setitem(alignment.FAMILIES["A"], "physical", "SourceOrigin Extra")
    source("GeneratedFoundations.Arithmetic.Hidden", "def arithmeticOnly : Nat := 1\n")
    source("GeneratedFoundations.Physical.Extra",
        "import GeneratedFoundations.Arithmetic.Hidden\n")
    with pytest.raises(verify.VerificationError, match="Implemented physical module imports"):
        alignment.inventory(project)


def test_unimported_arithmetic_module_cannot_hide_physical_dependency(tiny_project):
    project, source = tiny_project
    source("GeneratedFoundations.Arithmetic.Hidden",
        "import GeneratedFoundations.Physical.SourceOrigin\n")
    with pytest.raises(verify.VerificationError, match="Implemented mathematical module imports"):
        alignment.inventory(project)


def test_duplicate_review_cannot_silently_overwrite_an_earlier_result(tmp_path):
    path = tmp_path / "reviews.json"
    path.write_text('{"same": {"status": "shared_result"}, "same": {"status": "proved_analogue"}}',
        encoding="utf-8")
    with pytest.raises(verify.VerificationError, match="Duplicate record key"):
        alignment.load_records(path)


def test_record_file_requires_an_object(tmp_path):
    path = tmp_path / "reviews.json"
    path.write_text('[]', encoding="utf-8")
    with pytest.raises(verify.VerificationError, match="must contain a JSON object"):
        alignment.load_records(path)

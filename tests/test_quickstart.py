"""Regression checks for the public, source-only quickstart."""

import json
from pathlib import Path
import sys

import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from examples.quickstart import check_environment as quickstart


@pytest.fixture
def release(tmp_path, monkeypatch):
    (tmp_path / "lean-toolchain").write_text(
        quickstart.EXPECTED_TOOLCHAIN, encoding="utf-8")
    (tmp_path / "lake-manifest.json").write_text(json.dumps({
        "packages": [{"name": "mathlib", "rev": quickstart.EXPECTED_MATHLIB}]
    }), encoding="utf-8")
    (tmp_path / "theorem-index.json").write_text(json.dumps({
        "declarations": [{"name": name} for name in quickstart.EXPECTED_ROOTS]
    }), encoding="utf-8")
    (tmp_path / "AXIOMS.md").write_text("fixture", encoding="utf-8")
    (tmp_path / "verification").mkdir()
    (tmp_path / "verification" / "verification-manifest.json").write_text(
        "{}", encoding="utf-8")
    monkeypatch.setattr(quickstart, "ROOT", tmp_path)
    return tmp_path


def test_public_quickstart_matches_current_release(capsys):
    quickstart.main()
    assert "quickstart verification passed" in capsys.readouterr().out


@pytest.mark.parametrize("missing_name", quickstart.EXPECTED_ROOTS)
def test_root_must_be_an_exact_implemented_declaration(release, missing_name):
    path = release / "theorem-index.json"
    index = json.loads(path.read_text(encoding="utf-8"))
    index["declarations"] = [entry for entry in index["declarations"]
                             if entry["name"] != missing_name]
    index["declarations"].append({"name": missing_name + "_other"})
    index["planned"] = [{"name": missing_name}]
    index["scope"] = "Historical entry: " + missing_name
    path.write_text(json.dumps(index), encoding="utf-8")
    with pytest.raises(SystemExit, match="root entry missing"):
        quickstart.main()


def test_mathlib_revision_must_belong_to_mathlib(release):
    (release / "lake-manifest.json").write_text(json.dumps({
        "packages": [
            {"name": "mathlib", "rev": "0" * 40},
            {"name": "other", "rev": quickstart.EXPECTED_MATHLIB},
        ]
    }), encoding="utf-8")
    with pytest.raises(SystemExit, match="pinned mathlib commit is missing"):
        quickstart.main()

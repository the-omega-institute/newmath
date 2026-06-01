import json
from pathlib import Path

import pytest

from scripts import run_canonical_reports as canonical


def test_manifest_names_and_artifacts_are_unique_and_canonical_owned():
    names = [spec.name for spec in canonical.CANONICAL_REPORTS]
    json_artifacts = [spec.json_artifact for spec in canonical.CANONICAL_REPORTS]
    markdown_artifacts = [spec.markdown_artifact for spec in canonical.CANONICAL_REPORTS]

    assert len(names) == len(set(names))
    assert len(json_artifacts) == len(set(json_artifacts))
    assert len(markdown_artifacts) == len(set(markdown_artifacts))
    for spec in canonical.CANONICAL_REPORTS:
        assert spec.json_artifact.startswith("reports/canonical/")
        assert spec.markdown_artifact.startswith("reports/canonical/")
        assert spec.json_artifact.endswith(".json")
        assert spec.markdown_artifact.endswith(".md")
        assert spec.required_json_keys


def test_artifact_path_rejects_non_canonical_paths():
    with pytest.raises(ValueError):
        canonical._artifact_path("reports/not-canonical.json")


def test_only_selects_one_manifest_row_and_rejects_unknown():
    selected = canonical._select_specs("mixing-family-sweep")

    assert [spec.name for spec in selected] == ["mixing-family-sweep"]
    with pytest.raises(ValueError):
        canonical._select_specs("missing")


def test_run_reports_only_writes_index_and_summary_from_producer(tmp_path):
    old_root = canonical.ROOT
    old_dir = canonical.CANONICAL_DIR
    old_index = canonical.INDEX_ARTIFACT
    old_runner = canonical._run_producer
    canonical.ROOT = tmp_path
    canonical.CANONICAL_DIR = tmp_path / "reports" / "canonical"
    canonical.INDEX_ARTIFACT = tmp_path / "reports" / "canonical" / "index.json"
    index_path = canonical.INDEX_ARTIFACT
    summary_path = tmp_path / "summary.json"
    calls = []

    def fake_run_producer(spec):
        calls.append(spec.name)
        json_path = canonical._artifact_path(spec.json_artifact)
        md_path = canonical._artifact_path(spec.markdown_artifact)
        json_path.parent.mkdir(parents=True, exist_ok=True)
        json_path.write_text(
            json.dumps({key: f"fixture-{key}" for key in spec.required_json_keys}) + "\n",
            encoding="utf-8",
        )
        md_path.write_text("# fixture\n", encoding="utf-8")

    canonical._run_producer = fake_run_producer

    try:
        payload = canonical.run_reports(
            only="mixing-family-sweep",
            json_summary=str(summary_path),
        )
    finally:
        canonical.ROOT = old_root
        canonical.CANONICAL_DIR = old_dir
        canonical.INDEX_ARTIFACT = old_index
        canonical._run_producer = old_runner

    assert calls == ["mixing-family-sweep"]
    assert payload["schema_id"] == canonical.INDEX_SCHEMA_ID
    assert len(payload["reports"]) == 1
    assert payload["reports"][0]["status"] == "pass"
    assert payload["reports"][0]["validation"]["required_key_validation"]["status"] == "pass"
    assert json.loads(index_path.read_text(encoding="utf-8")) == payload
    assert json.loads(summary_path.read_text(encoding="utf-8")) == payload


def test_missing_artifact_fails_closed(tmp_path):
    old_root = canonical.ROOT
    old_dir = canonical.CANONICAL_DIR
    canonical.ROOT = tmp_path
    canonical.CANONICAL_DIR = tmp_path / "reports" / "canonical"
    spec = canonical.CANONICAL_REPORTS[0]

    try:
        validation = canonical._artifact_validation(spec)
    finally:
        canonical.ROOT = old_root
        canonical.CANONICAL_DIR = old_dir

    assert validation["status"] == "fail"
    assert spec.json_artifact in validation["missing_artifacts"]
    assert spec.markdown_artifact in validation["missing_artifacts"]
    assert validation["required_key_validation"]["status"] == "fail"


def test_required_key_failure_fails_closed(tmp_path):
    old_root = canonical.ROOT
    old_dir = canonical.CANONICAL_DIR
    canonical.ROOT = tmp_path
    canonical.CANONICAL_DIR = tmp_path / "reports" / "canonical"
    spec = canonical.CANONICAL_REPORTS[0]
    json_path = canonical._artifact_path(spec.json_artifact)
    md_path = canonical._artifact_path(spec.markdown_artifact)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text('{"generated_at": "fixture"}\n', encoding="utf-8")
    md_path.write_text("# fixture\n", encoding="utf-8")

    try:
        validation = canonical._artifact_validation(spec)
    finally:
        canonical.ROOT = old_root
        canonical.CANONICAL_DIR = old_dir

    assert validation["status"] == "fail"
    assert validation["missing_artifacts"] == []
    assert validation["required_key_validation"]["status"] == "fail"
    assert "config" in validation["required_key_validation"]["missing_keys"]


def test_make_check_routes_through_pytest_and_canonical_runner():
    makefile = Path("Makefile").read_text(encoding="utf-8")

    assert "check: test canonical-reports" in makefile
    assert "python3 -m pytest -q" in makefile
    assert "python3 scripts/run_canonical_reports.py" in makefile

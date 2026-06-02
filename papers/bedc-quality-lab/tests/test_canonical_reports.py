import json
import os
from pathlib import Path

import pytest

from scripts import run_canonical_reports as canonical


def test_manifest_names_and_artifacts_are_unique_and_canonical_owned():
    names = [spec.name for spec in canonical.CANONICAL_REPORTS]
    json_artifacts = [spec.json_artifact for spec in canonical.CANONICAL_REPORTS]
    markdown_artifacts = [spec.markdown_artifact for spec in canonical.CANONICAL_REPORTS]

    assert len(names) == len(set(names))
    assert names == [
        "gap-head-on-h",
        "gap-head-discovery",
        "nongaussian-distribution-sweep",
        "certificate-guided-training",
        "certificate-guided-discovery",
    ]
    assert len(json_artifacts) == len(set(json_artifacts))
    assert len(markdown_artifacts) == len(set(markdown_artifacts))
    for spec in canonical.CANONICAL_REPORTS:
        assert spec.json_artifact.startswith("reports/canonical/")
        assert spec.markdown_artifact.startswith("reports/canonical/")
        assert spec.json_artifact.endswith(".json")
        assert spec.markdown_artifact.endswith(".md")
        assert spec.required_json_keys


def test_gap_head_manifest_rows_are_canonical_and_keyed():
    on_h = canonical._specs_by_name()["gap-head-on-h"]
    discovery = canonical._specs_by_name()["gap-head-discovery"]

    assert on_h.command == ("python3", "scripts/run_gap_ledger_head_on_h.py")
    assert on_h.json_artifact == "reports/canonical/gap-head-on-h.json"
    assert on_h.markdown_artifact == "reports/canonical/gap-head-on-h.md"
    assert discovery.command == ("python3", "scripts/run_gap_head_discovery.py")
    assert discovery.json_artifact == "reports/canonical/gap-head-discovery.json"
    assert discovery.markdown_artifact == "reports/canonical/gap-head-discovery.md"
    assert {
        "boundary_no_z_audit",
        "forbidden_column_audit",
        "aggregate_metrics",
        "treatment_comparison",
        "control_protocol",
        "control_verdict",
        "main_claim_status",
    }.issubset(set(on_h.required_json_keys))
    assert {
        "boundary_checks",
        "matched_random_control",
        "main_claim_status",
        "final_main_claim_status",
    }.issubset(set(discovery.required_json_keys))


def test_canonical_reports_manifest_includes_distribution_sweep():
    spec = canonical._specs_by_name()["nongaussian-distribution-sweep"]

    assert spec.command == ("python3", "scripts/run_nongaussian_distribution_sweep.py")
    assert spec.json_artifact == "reports/canonical/nongaussian-distribution-sweep.json"
    assert spec.markdown_artifact == "reports/canonical/nongaussian-distribution-sweep.md"
    assert {
        "records",
        "family_aggregates",
        "coverage_item",
        "claim_gate",
        "main_claim_status",
        "negative_result_ledger",
        "not_claimed",
    }.issubset(set(spec.required_json_keys))


def test_canonical_reports_manifest_includes_certificate_guided_projection():
    training = canonical._specs_by_name()["certificate-guided-training"]
    discovery = canonical._specs_by_name()["certificate-guided-discovery"]

    assert training.command == ("python3", "scripts/run_certificate_guided_training.py")
    assert training.json_artifact == "reports/canonical/certificate-guided-training.json"
    assert training.markdown_artifact == "reports/canonical/certificate-guided-training.md"
    assert discovery.command == ("python3", "scripts/run_certificate_guided_discovery.py")
    assert discovery.json_artifact == "reports/canonical/certificate-guided-discovery.json"
    assert discovery.markdown_artifact == "reports/canonical/certificate-guided-discovery.md"
    assert {
        "paired_seed_protocol",
        "paired_delta_ci",
        "claim_gate",
        "not_claimed",
    }.issubset(set(training.required_json_keys))
    assert {
        "positive_discovery",
        "net_information",
        "matched_random_baseline",
        "claim_gate",
        "revocation_decision",
        "revocation_ledger",
        "not_claimed",
        "main_claim_status",
    }.issubset(set(discovery.required_json_keys))


def test_manifest_required_keys_cover_linked_control_evidence():
    for spec in canonical.CANONICAL_REPORTS:
        keys = set(spec.required_json_keys)
        assert "generated_at" in keys
        assert "source_artifacts" in keys
    assert {"control_protocol", "control_verdict"}.issubset(
        set(canonical._specs_by_name()["gap-head-on-h"].required_json_keys)
    )
    assert {"matched_random_control", "main_claim_status"}.issubset(
        set(canonical._specs_by_name()["gap-head-discovery"].required_json_keys)
    )
    assert {"claim_gate", "negative_result_ledger", "main_claim_status"}.issubset(
        set(canonical._specs_by_name()["nongaussian-distribution-sweep"].required_json_keys)
    )
    assert {"positive_discovery", "net_information", "matched_random_baseline", "claim_gate", "revocation_decision", "revocation_ledger", "not_claimed", "main_claim_status"}.issubset(
        set(canonical._specs_by_name()["certificate-guided-discovery"].required_json_keys)
    )


def test_artifact_path_rejects_non_canonical_paths():
    with pytest.raises(ValueError):
        canonical._artifact_path("reports/not-canonical.json")


def test_only_selects_one_manifest_row_and_rejects_unknown():
    selected = canonical._select_specs("gap-head-discovery")

    assert [spec.name for spec in selected] == ["gap-head-discovery"]
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
            only="gap-head-on-h",
            json_summary=str(summary_path),
        )
        index_markdown = (canonical.CANONICAL_DIR / "index.md").read_text(encoding="utf-8")
    finally:
        canonical.ROOT = old_root
        canonical.CANONICAL_DIR = old_dir
        canonical.INDEX_ARTIFACT = old_index
        canonical._run_producer = old_runner

    assert calls == ["gap-head-on-h"]
    assert payload["schema_id"] == canonical.INDEX_SCHEMA_ID
    assert len(payload["reports"]) == 1
    assert payload["reports"][0]["status"] == "pass"
    assert payload["reports"][0]["validation"]["required_key_validation"]["status"] == "pass"
    assert json.loads(index_path.read_text(encoding="utf-8")) == payload
    assert json.loads(summary_path.read_text(encoding="utf-8")) == payload
    assert "gap-head-on-h" in index_markdown


def test_run_reports_certificate_guided_discovery_uses_canonical_training_source(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    monkeypatch.setattr(canonical, "INDEX_ARTIFACT", tmp_path / "reports" / "canonical" / "index.json")
    source_json = canonical.CANONICAL_DIR / "certificate-guided-training.json"
    source_report = canonical.CANONICAL_DIR / "certificate-guided-training.md"
    source_json.parent.mkdir(parents=True, exist_ok=True)
    source_json.write_text(json.dumps({"training_marker": "canonical-source"}), encoding="utf-8")
    source_report.write_text("# canonical training\n", encoding="utf-8")
    observed = []

    class StubDiscoveryProducer:
        REPORT_JSON = None
        REPORT_MD = None
        JSON_ARTIFACT = "reports/certificate_guided_discovery.json"
        REPORT_ARTIFACT = "reports/certificate_guided_discovery.md"
        SOURCE_JSON_ARTIFACT = "reports/certificate_guided_training.json"
        SOURCE_REPORT_ARTIFACT = "reports/certificate_guided_training.md"
        USE_TORCH = True

        @classmethod
        def main(cls):
            assert cls.JSON_ARTIFACT == "reports/canonical/certificate-guided-discovery.json"
            assert cls.REPORT_ARTIFACT == "reports/canonical/certificate-guided-discovery.md"
            assert cls.SOURCE_JSON_ARTIFACT == "reports/canonical/certificate-guided-training.json"
            assert cls.SOURCE_REPORT_ARTIFACT == "reports/canonical/certificate-guided-training.md"
            assert cls.USE_TORCH is False
            source_payload = json.loads((canonical.ROOT / cls.SOURCE_JSON_ARTIFACT).read_text(encoding="utf-8"))
            observed.append(source_payload["training_marker"])
            payload = {
                "generated_at": "fixture",
                "source_artifacts": {
                    "source_json_artifact": cls.SOURCE_JSON_ARTIFACT,
                    "source_report_artifact": cls.SOURCE_REPORT_ARTIFACT,
                },
                "verdicts": [{"verdict": "positive"}],
                "positive_discovery": True,
                "net_information": 1.25,
                "matched_random_baseline": {"verdict": "negative"},
                "claim_gate": {"positive_discovery_four_gate": True},
                "revocation_decision": {"downgraded": False},
                "revocation_ledger": [],
                "not_claimed": ["fixture boundary"],
                "main_claim_status": "positive",
            }
            cls.REPORT_JSON.write_text(json.dumps(payload, sort_keys=True) + "\n", encoding="utf-8")
            cls.REPORT_MD.write_text("# stub discovery\n", encoding="utf-8")

    def fake_import_module(module_name):
        assert module_name == "scripts.run_certificate_guided_discovery"
        return StubDiscoveryProducer

    monkeypatch.setattr(canonical.importlib, "import_module", fake_import_module)

    payload = canonical.run_reports(only="certificate-guided-discovery")
    report_payload = json.loads((canonical.CANONICAL_DIR / "certificate-guided-discovery.json").read_text(encoding="utf-8"))
    report_markdown = (canonical.CANONICAL_DIR / "certificate-guided-discovery.md").read_text(encoding="utf-8")

    assert observed == ["canonical-source"]
    assert payload["reports"][0]["name"] == "certificate-guided-discovery"
    assert payload["reports"][0]["status"] == "pass"
    assert payload["reports"][0]["validation"]["required_key_validation"]["status"] == "pass"
    assert report_payload["source_artifacts"]["source_json_artifact"] == "reports/canonical/certificate-guided-training.json"
    assert report_payload["source_artifacts"]["source_report_artifact"] == "reports/canonical/certificate-guided-training.md"
    assert report_payload["positive_discovery"] is True
    assert report_payload["net_information"] == pytest.approx(1.25)
    assert report_payload["matched_random_baseline"] == {"verdict": "negative"}
    assert report_payload["claim_gate"] == {"positive_discovery_four_gate": True}
    assert report_payload["revocation_decision"] == {"downgraded": False}
    assert report_payload["revocation_ledger"] == []
    assert report_payload["not_claimed"] == ["fixture boundary"]
    assert report_payload["main_claim_status"] == "positive"
    assert report_markdown == "# stub discovery\n"


def test_certificate_guided_discovery_validation_accepts_empty_revocation_ledger(tmp_path):
    old_root = canonical.ROOT
    old_dir = canonical.CANONICAL_DIR
    canonical.ROOT = tmp_path
    canonical.CANONICAL_DIR = tmp_path / "reports" / "canonical"
    spec = canonical._specs_by_name()["certificate-guided-discovery"]
    json_path = canonical._artifact_path(spec.json_artifact)
    md_path = canonical._artifact_path(spec.markdown_artifact)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(
        json.dumps({key: [] if key == "revocation_ledger" else {"downgraded": False} if key == "revocation_decision" else "fixture" for key in spec.required_json_keys}) + "\n",
        encoding="utf-8",
    )
    md_path.write_text("# fixture\n", encoding="utf-8")

    try:
        validation = canonical._artifact_validation(spec)
    finally:
        canonical.ROOT = old_root
        canonical.CANONICAL_DIR = old_dir

    assert validation["status"] == "pass"
    assert validation["required_key_validation"]["missing_keys"] == []


def test_certificate_guided_discovery_validation_fails_closed_on_missing_revocation_fields(tmp_path):
    old_root = canonical.ROOT
    old_dir = canonical.CANONICAL_DIR
    canonical.ROOT = tmp_path
    canonical.CANONICAL_DIR = tmp_path / "reports" / "canonical"
    spec = canonical._specs_by_name()["certificate-guided-discovery"]
    json_path = canonical._artifact_path(spec.json_artifact)
    md_path = canonical._artifact_path(spec.markdown_artifact)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    payload = {key: "fixture" for key in spec.required_json_keys if key not in {"revocation_decision", "revocation_ledger"}}
    json_path.write_text(json.dumps(payload) + "\n", encoding="utf-8")
    md_path.write_text("# fixture\n", encoding="utf-8")

    try:
        validation = canonical._artifact_validation(spec)
    finally:
        canonical.ROOT = old_root
        canonical.CANONICAL_DIR = old_dir

    assert validation["status"] == "fail"
    assert validation["required_key_validation"]["status"] == "fail"
    assert set(validation["required_key_validation"]["missing_keys"]) == {"revocation_decision", "revocation_ledger"}


def test_index_root_is_relative_and_host_path_free(tmp_path):
    payload = canonical._index([])
    index_path = tmp_path / "index.json"
    index_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    json_text = index_path.read_text(encoding="utf-8")
    root = payload.get("root")

    assert root is None or not os.path.isabs(root)
    assert "/Users/" not in json_text
    assert ".worktrees" not in json_text


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
    assert "source_artifacts" in validation["required_key_validation"]["missing_keys"]


def test_index_markdown_lists_gap_head_reports():
    payload = canonical._index(
        [
            {
                "name": "gap-head-on-h",
                "status": "pass",
                "json_artifact": "reports/canonical/gap-head-on-h.json",
                "markdown_artifact": "reports/canonical/gap-head-on-h.md",
            },
            {
                "name": "nongaussian-distribution-sweep",
                "status": "pass",
                "json_artifact": "reports/canonical/nongaussian-distribution-sweep.json",
                "markdown_artifact": "reports/canonical/nongaussian-distribution-sweep.md",
            },
            {
                "name": "gap-head-discovery",
                "status": "pass",
                "json_artifact": "reports/canonical/gap-head-discovery.json",
                "markdown_artifact": "reports/canonical/gap-head-discovery.md",
            },
            {
                "name": "certificate-guided-discovery",
                "status": "pass",
                "json_artifact": "reports/canonical/certificate-guided-discovery.json",
                "markdown_artifact": "reports/canonical/certificate-guided-discovery.md",
            },
        ]
    )
    markdown = canonical._render_index_markdown(payload)

    assert "gap-head-on-h" in markdown
    assert "gap-head-discovery" in markdown
    assert "nongaussian-distribution-sweep" in markdown
    assert "certificate-guided-discovery" in markdown

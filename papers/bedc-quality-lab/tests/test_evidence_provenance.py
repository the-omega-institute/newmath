import json
from pathlib import Path

import pytest

from bedc_quality_lab.evidence_provenance import (
    DISCOVERY_EVIDENCE_TYPES,
    METRIC_SOURCE_TYPES,
    build_evidence_provenance,
    evidence_provenance_pointer_for_report,
    resolve_owner_pointer,
    validate_evidence_provenance_payload,
)
from scripts import run_canonical_reports as canonical


def _spec(name: str, artifact: str, command=("python3", "scripts/run_fixture.py")):
    return canonical.CanonicalReportSpec(
        name=name,
        command=command,
        json_artifact=artifact,
        markdown_artifact=artifact.replace(".json", ".md"),
        required_json_keys=("positive",),
        estimated_seconds=1,
        bundle_role="hg_p_core",
        scope_pointer="$.scope",
        cost_pointer="$.cost",
        not_claimed_pointer="$.not_claimed",
        positive_claim_pointer="$.positive",
        control_pointer="$.control",
        no_control_rationale_pointer=None,
    )


def _write_json(root: Path, artifact: str, payload):
    path = root / artifact
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, sort_keys=True) + "\n", encoding="utf-8")


def _write_source(root: Path, relative: str, body: str = "def main():\n    return None\n"):
    path = root / relative
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(body, encoding="utf-8")


def test_owner_vocabularies_are_maintainer_sets():
    assert METRIC_SOURCE_TYPES == (
        "measured_training",
        "deterministic_projection",
        "declared_constant",
        "arm_branch",
        "protocol_field",
    )
    assert DISCOVERY_EVIDENCE_TYPES == (
        "empirical_training_clean",
        "empirical_training_tainted",
        "deterministic_projection",
        "protocol_artifact",
        "boundary_negative",
    )


def test_every_canonical_report_gets_one_producer_audit_and_metric_row(tmp_path):
    specs = (
        _spec("order-k-benchmark", "reports/canonical/order-k-benchmark.json"),
        _spec("dgt-l0-controls", "reports/canonical/dgt-l0-controls.json"),
    )
    _write_source(tmp_path, "scripts/run_fixture.py")
    for spec in specs:
        _write_json(tmp_path, spec.json_artifact, {"positive": 1, "scope": {}, "cost": {}, "not_claimed": [], "control": {}})
    _write_json(
        tmp_path,
        "reports/canonical/discovery_map.json",
        {
            "rows": [
                {
                    "report": spec.name,
                    "discovery_level": "D4",
                    "audit_status": "valid",
                }
                for spec in specs
            ]
        },
    )

    payload = build_evidence_provenance(root=tmp_path, canonical_reports=specs, generated_at="fixture")

    assert [row["report"] for row in payload["producer_audits"]] == [spec.name for spec in specs]
    assert [row["source_type"] for row in payload["metric_rows"]] == ["deterministic_projection", "arm_branch"]
    assert all(row["allowed_for_empirical_claim"] is False for row in payload["metric_rows"])
    assert all(row["evidence_type"] != "empirical_training_clean" for row in payload["discovery_rows"])


def test_clean_training_requires_backward_and_optimizer_step(tmp_path):
    spec = _spec("training-report", "reports/canonical/training-report.json")
    _write_source(
        tmp_path,
        "scripts/run_fixture.py",
        "def train(loss, optimizer):\n    loss.backward()\n    optimizer.step()\n",
    )
    _write_json(tmp_path, spec.json_artifact, {"positive": 1, "scope": {}, "cost": {}, "not_claimed": [], "control": {}})
    _write_json(
        tmp_path,
        "reports/canonical/discovery_map.json",
        {"rows": [{"report": spec.name, "discovery_level": "D4", "audit_status": "valid"}]},
    )

    payload = build_evidence_provenance(root=tmp_path, canonical_reports=(spec,), generated_at="fixture")

    assert payload["producer_audits"][0]["training_evidence_status"] == "empirical_training_clean"
    assert payload["metric_rows"][0]["source_type"] == "measured_training"
    assert payload["metric_rows"][0]["allowed_for_empirical_claim"] is True
    assert payload["discovery_rows"][0]["evidence_type"] == "empirical_training_clean"


def test_missing_measurement_is_null_with_reason_not_new_enum(tmp_path):
    spec = _spec("missing-metric", "reports/canonical/missing-metric.json")
    _write_source(tmp_path, "scripts/run_fixture.py")
    _write_json(tmp_path, spec.json_artifact, {"scope": {}, "cost": {}, "not_claimed": [], "control": {}})

    payload = build_evidence_provenance(root=tmp_path, canonical_reports=(spec,), generated_at="fixture")
    row = payload["metric_rows"][0]

    assert row["source_type"] in METRIC_SOURCE_TYPES
    assert row["value"] is None
    assert row["not_measurable_reason"] == "source artifact pointer is unresolved"
    assert row["allowed_for_empirical_claim"] is False


def test_validation_rejects_non_owner_vocabularies(tmp_path):
    spec = _spec("fixture", "reports/canonical/fixture.json")
    _write_source(tmp_path, "scripts/run_fixture.py")
    _write_json(tmp_path, spec.json_artifact, {"positive": 1, "scope": {}, "cost": {}, "not_claimed": [], "control": {}})
    payload = build_evidence_provenance(root=tmp_path, canonical_reports=(spec,), generated_at="fixture")
    payload["metric_rows"][0]["source_type"] = "not_measurable"

    with pytest.raises(ValueError, match="source_type"):
        validate_evidence_provenance_payload(payload)


def test_evidence_provenance_pointer_is_report_owner_pointer():
    assert evidence_provenance_pointer_for_report("dgt-l0-controls") == (
        "reports/canonical/index.json:$.evidence_provenance.discovery_rows_by_report.dgt-l0-controls"
    )


def test_owner_payload_rejects_missing_discovery_row_map(tmp_path):
    spec = _spec("fixture", "reports/canonical/fixture.json")
    _write_source(tmp_path, "scripts/run_fixture.py")
    _write_json(tmp_path, spec.json_artifact, {"positive": 1, "scope": {}, "cost": {}, "not_claimed": [], "control": {}})
    payload = build_evidence_provenance(root=tmp_path, canonical_reports=(spec,), generated_at="fixture")
    payload.pop("discovery_rows_by_report")

    with pytest.raises(ValueError, match="discovery_rows_by_report"):
        validate_evidence_provenance_payload(payload)


def test_report_owner_pointer_resolves_through_generic_resolver(tmp_path):
    spec = _spec("fixture", "reports/canonical/fixture.json")
    _write_source(tmp_path, "scripts/run_fixture.py")
    _write_json(tmp_path, spec.json_artifact, {"positive": 1, "scope": {}, "cost": {}, "not_claimed": [], "control": {}})
    section = build_evidence_provenance(root=tmp_path, canonical_reports=(spec,), generated_at="fixture")
    _write_json(
        tmp_path,
        "reports/canonical/index.json",
        {
            "schema_id": "bedc-quality-lab:canonical-report-index",
            "generated_at": "fixture",
            "evidence_provenance": section,
        },
    )

    pointer = evidence_provenance_pointer_for_report("fixture")

    assert resolve_owner_pointer(tmp_path, pointer) == section["discovery_rows_by_report"]["fixture"]

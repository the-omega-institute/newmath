import json
from pathlib import Path

from bedc_quality_lab import dgt_component_redundancy_audit as audit


ROOT = Path(__file__).resolve().parents[1]


def _payload():
    return audit.build_payload(root=ROOT, generated_at="fixture")


def _rows(payload):
    return {
        row["component_id"]: row
        for row in payload["component_redundancy_audit"]["components"]
    }


def test_component_redundancy_audit_verdicts_are_derived_from_canonical_sources():
    payload = _payload()
    rows = _rows(payload)

    assert payload["component_redundancy_audit"]["audit_status"] == "pass"
    assert len(rows) == 10
    for component in ("route_certificate", "mechanism_probe", "negative_witness_loss"):
        assert rows[component]["verdict"] == "confirmed-redundant"
        assert rows[component]["null_decomposition"]["redundancy_signal"] is True
    assert rows["CGA"]["verdict"] == "independent"
    assert rows["LAT"]["verdict"] == "inconclusive"


def test_component_redundancy_audit_global_recommendation_is_mechanical():
    payload = _payload()
    audit_payload = payload["component_redundancy_audit"]

    assert audit_payload["verdict_counts"] == {
        "confirmed-redundant": 3,
        "independent": 6,
        "inconclusive": 1,
    }
    assert audit_payload["global_recommendation"] == {
        "recommendation": "redesign-confirmed-redundant-components",
        "reason_code": "suspect-components-confirmed-redundant-in-bounded-toy-audit",
        "confirmed_redundant_components": [
            "route_certificate",
            "mechanism_probe",
            "negative_witness_loss",
        ],
        "suspect_confirmed_redundant_components": [
            "route_certificate",
            "mechanism_probe",
            "negative_witness_loss",
        ],
        "inconclusive_components": ["LAT"],
        "redesign_action": "advisory-only",
    }


def test_component_redundancy_rows_are_pointer_backed_without_alias_keys():
    payload = _payload()
    rows = _rows(payload)
    route = rows["route_certificate"]

    assert route["source_pointers"]["quality_delta"] == (
        "reports/canonical/dgt-neural-ablation.json:"
        "$.paired_delta_matrix.DGT_without_route_certificate.metrics.quality_q"
    )
    assert route["source_pointers"]["null_component_row"].startswith(
        "reports/canonical/dgt-ablation-null-decomposition.json:$.null_decomposition.components["
    )
    serialized = json.dumps(payload, sort_keys=True)
    assert "component_effects" not in serialized
    assert "per_component_quality" not in serialized
    assert "effect_prior" not in serialized


def test_component_redundancy_missing_pointer_is_inconclusive():
    neural = json.loads((ROOT / audit.NEURAL_SOURCE_ARTIFACT).read_text(encoding="utf-8"))
    null_payload = json.loads((ROOT / audit.NULL_SOURCE_ARTIFACT).read_text(encoding="utf-8"))
    del neural["paired_delta_matrix"]["DGT_without_route_certificate"]["metrics"]["quality_q"]

    payload = audit.build_payload(
        root=ROOT,
        generated_at="fixture",
        neural_payload=neural,
        null_payload=null_payload,
    )
    route = _rows(payload)["route_certificate"]

    assert route["verdict"] == "inconclusive"
    assert route["evidence_status"] == "missing"
    assert route["missing_evidence"] == [
        "reports/canonical/dgt-neural-ablation.json:"
        "$.paired_delta_matrix.DGT_without_route_certificate.metrics.quality_q"
    ]


def test_component_redundancy_artifact_writes_are_byte_idempotent(tmp_path):
    for relative in (audit.NEURAL_SOURCE_ARTIFACT, audit.NULL_SOURCE_ARTIFACT):
        target = tmp_path / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes((ROOT / relative).read_bytes())

    payload = audit.build_payload(root=tmp_path, generated_at=audit.GENERATED_AT)
    audit.write_artifacts(payload, root=tmp_path, generated_at=audit.GENERATED_AT)
    first = {
        relative: (tmp_path / relative).read_bytes()
        for relative in (
            audit.CANONICAL_JSON_ARTIFACT,
            audit.CANONICAL_MARKDOWN_ARTIFACT,
            audit.CANONICAL_FINGERPRINT_ARTIFACT,
        )
    }

    payload = audit.build_payload(root=tmp_path, generated_at=audit.GENERATED_AT)
    audit.write_artifacts(payload, root=tmp_path, generated_at=audit.GENERATED_AT)
    second = {
        relative: (tmp_path / relative).read_bytes()
        for relative in first
    }

    assert first == second

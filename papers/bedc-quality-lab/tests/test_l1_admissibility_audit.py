import json

import pytest

from bedc_quality_lab import l1_admissibility_audit as audit


def _ready_metrics(**overrides):
    payload = {
        "schema_id": "bedc-quality-lab:l1-owner-metrics-packet",
        "owner_surface": "fixture-surface",
        "canonical_sha": "abc123",
        "run_interface_frozen": True,
        "claim_artifact_consistency_status": "pass",
        "base_accuracy_l95": 0.78,
        "chance_accuracy_u95": 0.50,
        "negative_control_delta": 0.0,
        "leakage_score": 0.0,
        "memorization_score": 0.0,
        "order_sentinel_margin": 0.01,
        "owner_metrics_ref": "reports/canonical/fixture-owner.json:$.metrics",
    }
    payload.update(overrides)
    return payload


def test_default_payload_is_not_ready_without_upstream_dependencies():
    payload = audit.build_payload(generated_at="fixture")

    assert payload["gate_card"]["status"] == "not_ready"
    assert payload["gate_card"]["failed_gate"] == "L1A-HG1-READINESS"
    assert payload["status_axes"]["decision_status"] == "blocked"
    assert {row["status"] for row in payload["dependency_statuses"]} == {"missing"}
    audit.validate_payload(payload)


def test_ready_owner_metrics_pass_fixed_protocol():
    payload = audit.build_payload(owner_metrics=_ready_metrics(), generated_at="fixture")

    assert payload["gate_card"]["status"] == "pass"
    assert payload["gate_card"]["failed_gate"] is None
    assert payload["computed_metrics"]["base_margin"] == pytest.approx(0.28)
    assert payload["status_axes"]["hardgate_status"] == "pass"
    audit.validate_payload(payload)


def test_leakage_or_memorization_failure_kills_admission():
    payload = audit.build_payload(owner_metrics=_ready_metrics(leakage_score=0.1), generated_at="fixture")

    assert payload["gate_card"]["status"] == "kill"
    assert payload["gate_card"]["failed_gate"] == "L1A-HG5-LEAKAGE"
    assert payload["status_axes"]["decision_status"] == "bounded-negative"
    assert payload["hardgates"]["L1A-HG5-LEAKAGE"]["status"] == "fail"


def test_memorization_failure_kills_admission():
    payload = audit.build_payload(owner_metrics=_ready_metrics(memorization_score=0.1), generated_at="fixture")

    assert payload["gate_card"]["status"] == "kill"
    assert payload["gate_card"]["failed_gate"] == "L1A-HG6-MEMORIZATION"
    assert payload["status_axes"]["decision_status"] == "bounded-negative"
    assert payload["hardgates"]["L1A-HG6-MEMORIZATION"]["status"] == "fail"


def test_base_margin_failure_abstains_without_tuning_threshold():
    payload = audit.build_payload(
        owner_metrics=_ready_metrics(base_accuracy_l95=0.52, chance_accuracy_u95=0.50),
        generated_at="fixture",
    )

    assert payload["gate_card"]["status"] == "abstain"
    assert payload["hardgates"]["L1A-HG3-BASE"]["threshold"] == audit.PROTOCOL_THRESHOLDS["base_margin_min"]
    assert payload["status_axes"]["scientific_claim_status"] == "scoped-boundary"


def test_negative_control_or_order_failure_blocks_admission():
    payload = audit.build_payload(owner_metrics=_ready_metrics(negative_control_delta=0.5), generated_at="fixture")

    assert payload["gate_card"]["status"] == "block"
    assert payload["gate_card"]["failed_gate"] == "L1A-HG4-NEGATIVE-CONTROL"
    assert payload["status_axes"]["decision_status"] == "blocked"


def test_order_sentinel_failure_blocks_admission():
    payload = audit.build_payload(owner_metrics=_ready_metrics(order_sentinel_margin=-0.01), generated_at="fixture")

    assert payload["gate_card"]["status"] == "block"
    assert payload["gate_card"]["failed_gate"] == "L1A-HG7-ORDER"
    assert payload["status_axes"]["decision_status"] == "blocked"
    assert payload["hardgates"]["L1A-HG7-ORDER"]["status"] == "fail"


def test_incomplete_ready_metrics_block_at_schema_gate():
    metrics = _ready_metrics()
    metrics.pop("base_accuracy_l95")

    payload = audit.build_payload(owner_metrics=metrics, generated_at="fixture")

    assert payload["gate_card"]["status"] == "block"
    assert payload["gate_card"]["failed_gate"] == "L1A-HG2-SCHEMA"
    assert "base_accuracy_l95" in payload["hardgates"]["L1A-HG2-SCHEMA"]["actual"]


def test_validation_rejects_threshold_drift():
    payload = audit.build_payload(owner_metrics=_ready_metrics(), generated_at="fixture")
    payload["protocol"]["thresholds"]["base_margin_min"] = 0.0

    with pytest.raises(ValueError, match="fixed protocol"):
        audit.validate_payload(payload)


def test_write_artifacts_loads_owner_metrics_pointer(tmp_path):
    source = tmp_path / "reports/canonical/fixture-owner.json"
    source.parent.mkdir(parents=True, exist_ok=True)
    source.write_text(json.dumps({"metrics": _ready_metrics()}) + "\n", encoding="utf-8")

    payload = audit.write_artifacts(
        root=tmp_path,
        metrics_pointer="reports/canonical/fixture-owner.json:$.metrics",
        generated_at="fixture",
    )

    assert payload["gate_card"]["status"] == "pass"
    assert (tmp_path / audit.CANONICAL_JSON_ARTIFACT).exists()
    assert (tmp_path / audit.CANONICAL_MARKDOWN_ARTIFACT).exists()

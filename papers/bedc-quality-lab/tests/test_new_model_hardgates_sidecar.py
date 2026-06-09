import json

import pytest

from scripts import run_canonical_reports as canonical


def test_sidecar_emits_exact_stable_gate_vocabulary():
    payload = canonical._build_new_model_hardgates_payload(generated_at="fixture-time")

    assert payload["schema_id"] == "bedc-quality-lab:new-model-hardgates"
    assert payload["canonical_role"] == "sidecar_not_in_CANONICAL_REPORTS"
    assert payload["gate_ids"] == [f"NEW-MODEL-HG{index}" for index in range(1, 21)]
    assert list(payload["gates"]) == payload["gate_ids"]


def test_sidecar_rows_are_pointer_templates_without_candidate_bodies():
    payload = canonical._build_new_model_hardgates_payload(generated_at="fixture-time")
    serialized = json.dumps(payload, sort_keys=True).lower()

    for gate_id, row in payload["gates"].items():
        assert set(row) == {
            "requirement",
            "required_candidate_pointer",
            "required_evidence_pointer",
            "not_claimed_pointer",
        }
        assert row["required_candidate_pointer"] == f"$.hardgate_instances.{gate_id}"
        assert row["required_evidence_pointer"] == f"$.hardgate_instances.{gate_id}.evidence_pointer"
        assert row["not_claimed_pointer"] == f"$.hardgate_instances.{gate_id}.not_claimed_pointer"
    for forbidden in ("terminal_verdict", "candidate verdict", "metric bodies", "raw_metrics"):
        assert forbidden not in serialized


def test_sidecar_validator_rejects_metric_body_leaks():
    payload = canonical._build_new_model_hardgates_payload(generated_at="fixture-time")
    mutated = json.loads(json.dumps(payload))
    mutated["gates"]["NEW-MODEL-HG7"]["measured_baseline"] = {"loss": 0.1}

    with pytest.raises(ValueError):
        canonical._validate_new_model_hardgates_payload(mutated)

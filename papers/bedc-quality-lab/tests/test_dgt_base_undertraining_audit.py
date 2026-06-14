import json
from pathlib import Path

import pytest

from bedc_quality_lab import dgt_base_undertraining_audit as audit


ROOT = Path(__file__).resolve().parents[1]


def _l1_payload():
    return json.loads((ROOT / audit.L1_SOURCE_ARTIFACT).read_text(encoding="utf-8"))


def _payload(l1_payload=None):
    return audit.build_payload(root=ROOT, generated_at="fixture", l1_payload=l1_payload or _l1_payload())


def _audit(payload):
    return payload["base_undertraining_audit"]


def _rows(payload):
    return {row["comparison_id"]: row for row in _audit(payload)["comparison_rows"]}


def _copy_l1(tmp_path):
    target = tmp_path / audit.L1_SOURCE_ARTIFACT
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes((ROOT / audit.L1_SOURCE_ARTIFACT).read_bytes())
    ia_target = tmp_path / audit.INPUT_ACCESSIBILITY_SOURCE_ARTIFACT
    ia_target.parent.mkdir(parents=True, exist_ok=True)
    ia_target.write_bytes((ROOT / audit.INPUT_ACCESSIBILITY_SOURCE_ARTIFACT).read_bytes())


def _owner_valid_input_accessibility_payload():
    payload = json.loads((ROOT / audit.INPUT_ACCESSIBILITY_SOURCE_ARTIFACT).read_text(encoding="utf-8"))
    for row in payload["rows"]:
        if (
            row["experiment"] == "dgt_l1_tiny_sequence"
            and row["split"] == "in_distribution"
            and row["arm"] == audit.INPUT_ABLATION_ARM_ID
            and row["role"] == audit.INPUT_ABLATION_ROLE
        ):
            row["visible_variables"] = list(row["required_variables"])
            row["missing_variables"] = []
            row["coverage_status"] = "pass"
            row["information_starved"] = False
            row["supports_architecture_claim"] = True
            row_id = row["row_id"]
            payload["visible_variables"][row_id] = list(row["visible_variables"])
            payload["required_variables"][row_id] = list(row["required_variables"])
    payload["consumer_pointers"]["information_starved_arms_ref"] = [
        pointer
        for pointer in payload["consumer_pointers"]["information_starved_arms_ref"]
        if not pointer.endswith("#row_id=6001d70d815f574b")
    ]
    return payload


def test_base_undertraining_audit_records_construct_boundary_for_current_l1_evidence():
    payload = _payload()
    audit_payload = _audit(payload)
    rows = _rows(payload)

    assert audit_payload["verdict"] == "construct-boundary"
    assert audit_payload["claim_action"] == "defer-to-fair-reconstruction"
    assert audit_payload["construct_validity"]["status"] == "construct-boundary"
    assert audit_payload["construct_validity"]["bayes_upper_bound_accuracy"] == 0.0625
    assert audit_payload["construct_validity"]["source_pointers"]["fair_reconstruction"].endswith("/issues/1196")
    assert audit_payload["construct_validity"]["source_pointers"]["input_accessibility"] == (
        "reports/canonical/input-accessibility.json:$"
    )
    assert audit_payload["construct_validity"]["source_pointers"]["unanswerable_ood_splits"] == (
        "reports/canonical/input-accessibility.json:$.consumer_pointers.unanswerable_ood_splits_ref"
    )
    preconditions = audit_payload["construct_validity"]["input_accessibility_preconditions"]
    assert preconditions["status"] == "pass"
    assert preconditions["missing_variables"] == ["x_minus_2"]
    assert preconditions["information_starved_arms_ref"]
    assert preconditions["unanswerable_ood_splits_ref"]
    assert audit_payload["source_contract"]["input_accessibility_preconditions"] == preconditions
    assert set(preconditions["unanswerable_ood_splits_ref"]).issubset(
        set(audit_payload["source_contract"]["required_pointers"])
    )
    assert set(rows) == {"equal_step", "equal_compute", "equal_loss_decrease", "equal_validation_loss"}
    assert rows["equal_step"]["match_axis"] == "training_steps"
    assert rows["equal_compute"]["match_axis"] == "compute_units"
    assert rows["equal_loss_decrease"]["match_axis"] == "loss_decrease"
    assert rows["equal_validation_loss"]["match_axis"] == "validation_loss"
    assert rows["equal_validation_loss"]["status"] == "resolved"
    assert rows["equal_validation_loss"]["source_pointer"].endswith(f".metrics.{audit.INPUT_ABLATION_VALIDATION_LOSS_METRIC}")
    assert all(row["decision"] == "noninformative-dgt-separated" for row in rows.values())
    assert audit_payload["hardgates"]["BASE-UNDER-HG1"]["status"] == "pass"
    assert audit_payload["hardgates"]["BASE-UNDER-HG2"]["status"] == "pass"
    assert audit_payload["hardgates"]["BASE-UNDER-HG0"]["status"] == "fail-closed"
    assert audit_payload["hardgates"]["BASE-UNDER-HG5"]["status"] == "pass"
    assert audit_payload["boundary_ledger"] == [
        {
            "ledger_id": "base-undertraining-construct-validity",
            "status": "construct-boundary",
            "reason": "equal-compute, equal-loss-decrease, and equal-validation-loss rows are non-informative for an information-starved baseline",
            "source_pointer": "reports/canonical/dgt-base-undertraining-audit.json:$.base_undertraining_audit.construct_validity",
            "reconstruction_pointer": audit.FAIR_RECONSTRUCTION_POINTER,
        }
    ]
    assert audit_payload["evidence_ledger"] == []


def test_required_comparison_rows_include_equal_validation_loss():
    l1 = _l1_payload()
    l1["l1_step_ladder"]["per_step"] = []

    payload = _payload(l1)

    assert _audit(payload)["verdict"] == "construct-boundary"
    assert _audit(payload)["hardgates"]["BASE-UNDER-HG1"]["status"] == "fail"
    assert list(_rows(payload)) == ["equal_step"]


def test_equal_validation_loss_row_resolves_only_from_l1_owner_metric_cells():
    payload = _payload()
    row = _rows(payload)["equal_validation_loss"]

    assert row["status"] == "resolved"
    assert row["match_axis"] == "validation_loss"
    assert row["match_value"] > 0
    assert row["source_artifact"] == audit.L1_SOURCE_ARTIFACT
    assert row["source_pointer"].startswith(
        f"{audit.L1_SOURCE_ARTIFACT}:$.l1_step_ladder.per_step["
    )
    assert row["source_pointer"].endswith(f".metrics.{audit.INPUT_ABLATION_VALIDATION_LOSS_METRIC}")
    assert row["decision"] == "noninformative-dgt-separated"


def test_missing_validation_loss_owner_cells_fail_row_resolution_hardgate():
    l1 = _l1_payload()
    for step in l1["l1_step_ladder"]["per_step"]:
        for arm in step["training_arms"].values():
            arm["metrics"].pop("validation_loss_mean", None)
        for key in list(step["metrics"]):
            if "validation_loss" in key:
                step["metrics"].pop(key)
    for step in l1["l1_step_ladder"]["step_rows"]:
        for key in list(step["metrics"]):
            if "validation_loss" in key:
                step["metrics"].pop(key)

    payload = _payload(l1)
    row = _rows(payload)["equal_validation_loss"]

    assert row["status"] == "missing"
    assert row["match_axis"] == "validation_loss"
    assert row["decision"] == "validation-loss-owner-cell-missing"
    assert _audit(payload)["hardgates"]["BASE-UNDER-HG3"]["status"] == "fail"


def test_construct_validity_gate_fail_closed_prevents_strengthening():
    payload = _payload()
    audit_payload = _audit(payload)

    assert audit_payload["hardgates"]["BASE-UNDER-HG0"]["status"] == "fail-closed"
    assert audit_payload["verdict"] == "construct-boundary"
    assert audit_payload["claim_action"] != "strengthen_l1_evidence"
    assert audit_payload["evidence_ledger"] == []


def test_construct_validity_mutation_can_leave_boundary_when_baseline_sees_required_inputs():
    payload = audit.build_payload(
        root=ROOT,
        generated_at="fixture",
        l1_payload=_l1_payload(),
        construct_validity_override=audit.construct_validity_assessment(
            baseline_input_order=2,
            label_dependency_order=2,
            second_predecessor_visible=True,
        ),
    )
    audit_payload = _audit(payload)

    assert audit_payload["construct_validity"]["status"] == "construct-valid"
    assert audit_payload["hardgates"]["BASE-UNDER-HG0"]["status"] == "fail-closed"
    assert audit_payload["verdict"] == "construct-boundary"
    assert audit_payload["claim_action"] == "defer-to-fair-reconstruction"
    assert audit_payload["evidence_ledger"] == []


def test_missing_or_unresolvable_pointer_fails_closed(tmp_path):
    _copy_l1(tmp_path)
    (tmp_path / audit.L1_SOURCE_ARTIFACT).unlink()

    payload = audit.build_payload(root=tmp_path, generated_at="fixture")

    assert _audit(payload)["verdict"] == "construct-boundary"
    assert _audit(payload)["source_contract"]["status"] == "missing"
    assert _audit(payload)["comparison_rows"] == []


def test_missing_input_accessibility_precondition_fails_closed(tmp_path):
    _copy_l1(tmp_path)
    (tmp_path / audit.INPUT_ACCESSIBILITY_SOURCE_ARTIFACT).unlink()

    payload = audit.build_payload(
        root=tmp_path,
        generated_at="fixture",
        construct_validity_override=audit.construct_validity_assessment(
            baseline_input_order=2,
            label_dependency_order=2,
            second_predecessor_visible=True,
        ),
    )
    audit_payload = _audit(payload)

    assert audit_payload["construct_validity"]["status"] == "construct-valid"
    assert audit_payload["construct_validity"]["input_accessibility_preconditions"]["status"] == "missing"
    assert audit_payload["hardgates"]["BASE-UNDER-HG0"]["status"] == "fail-closed"
    assert audit_payload["verdict"] == "construct-boundary"


def test_equal_compute_catchup_records_boundary():
    l1 = _l1_payload()
    row = l1["l1_step_ladder"]["per_step"][0]
    row["metrics"]["input_ablation_accuracy_mean"] = row["metrics"]["dgt_accuracy_mean"]

    payload = audit.build_payload(
        root=ROOT,
        generated_at="fixture",
        l1_payload=l1,
        construct_validity_override=audit.construct_validity_assessment(
            baseline_input_order=2,
            label_dependency_order=2,
            second_predecessor_visible=True,
        ),
        input_accessibility_payload=_owner_valid_input_accessibility_payload(),
    )
    audit_payload = _audit(payload)

    assert audit_payload["verdict"] == "downgrade"
    assert audit_payload["claim_action"] == "fair_compute_artifact"
    assert {
        "ledger_id": "base-undertraining-equal_compute",
        "comparison_id": "equal_compute",
        "reason": "base reaches DGT after the construct-validity premise is satisfied",
        "source_pointer": "reports/canonical/dgt-l1-controls.json:$.l1_step_ladder.per_step[0]",
    } in audit_payload["boundary_ledger"]
    assert audit_payload["hardgates"]["BASE-UNDER-HG4"]["status"] == "triggered"


def test_equal_loss_decrease_catchup_records_boundary():
    l1 = _l1_payload()
    row = l1["l1_step_ladder"]["per_step"][4]
    row["metrics"]["input_ablation_accuracy_mean"] = row["metrics"]["dgt_accuracy_mean"] + 0.01

    payload = audit.build_payload(
        root=ROOT,
        generated_at="fixture",
        l1_payload=l1,
        construct_validity_override=audit.construct_validity_assessment(
            baseline_input_order=2,
            label_dependency_order=2,
            second_predecessor_visible=True,
        ),
        input_accessibility_payload=_owner_valid_input_accessibility_payload(),
    )
    audit_payload = _audit(payload)

    assert audit_payload["verdict"] == "downgrade"
    assert audit_payload["claim_action"] == "fair_loss_decrease_artifact"
    assert audit_payload["boundary_ledger"] == [
        {
            "ledger_id": "base-undertraining-equal_loss_decrease",
            "comparison_id": "equal_loss_decrease",
            "reason": "base reaches DGT after the construct-validity premise is satisfied",
            "source_pointer": "reports/canonical/dgt-l1-controls.json:$.l1_step_ladder.per_step[4]",
        }
    ]


def test_base_grid_coverage_is_checked_without_faking_directive_steps():
    payload = _payload()
    coverage = _audit(payload)["source_contract"]["base_step_grid_coverage"]

    assert coverage["required_grid"] == [36, 72, 128, 256, 512]
    assert coverage["observed_grid"] == [36, 72, 144, 288, 576]
    assert coverage["required_grid_present"] is False
    assert coverage["covers_dgt_compute_loss_interval"] is True


def test_base_grid_without_anchor_interval_is_inconclusive():
    l1 = _l1_payload()
    l1["l1_step_ladder"]["per_step"] = [
        row for row in l1["l1_step_ladder"]["per_step"] if row["training_steps"] > 36
    ]

    payload = _payload(l1)

    assert _audit(payload)["verdict"] == "construct-boundary"
    assert _audit(payload)["hardgates"]["BASE-UNDER-HG2"]["status"] == "fail"


def test_pointer_only_payload_does_not_copy_l1_tables():
    payload = _payload()
    serialized = json.dumps(payload, sort_keys=True)

    assert "reports/canonical/dgt-l1-controls.json:$.l1_step_ladder.per_step[0]" in serialized
    assert "raw_metrics" not in serialized
    assert "step_rows" not in serialized
    assert "training_arms" not in serialized
    assert "No undertraining discharge claim under information-starved baseline." in serialized
    for row in _audit(payload)["comparison_rows"]:
        assert row["source_artifact"] == audit.L1_SOURCE_ARTIFACT
        assert row["source_pointer"].startswith(f"{audit.L1_SOURCE_ARTIFACT}:")


def test_rejects_downstream_verdict_input():
    with pytest.raises(ValueError, match="does not accept downstream verdict"):
        audit.build_payload(root=ROOT, l1_payload=_l1_payload(), downstream_verdict={"verdict": "pass"})


def test_regeneration_is_byte_stable(tmp_path):
    _copy_l1(tmp_path)
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

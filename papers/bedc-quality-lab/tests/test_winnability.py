import math

import pytest

from bedc_quality_lab import winnability


def _split(**overrides):
    fields = {
        "experiment_id": "fixture-experiment",
        "task_id": "fixture-task",
        "task_family": "analytic-visibility",
        "resolver_family": "analytic-visibility",
        "split_id": "fixture-split",
        "split_kind": "held-out",
        "split_fingerprint": "fixture-fingerprint",
        "source_evidence_ref": "reports/canonical/fixture.json:$.row",
        "label_function_ref": "fixture.label",
        "visible_variables_ref": "reports/canonical/input-accessibility.json:$.rows[0].visible_variables",
        "required_variables_ref": "reports/canonical/input-accessibility.json:$.rows[0].required_variables",
        "visible_variables": ["x_left", "x_right"],
        "required_variables": ["x_left", "x_right"],
        "allow_inline_input_fixture": True,
        "chance_accuracy": 1.0 / 16.0,
        "observed_accuracy": 0.75,
        "epsilon": 1e-9,
    }
    fields.update(overrides)
    return fields


def test_l1_ood_hidden_lag_is_unwinnable(tmp_path):
    split = _split(
        task_id="l1-hidden-lag",
        split_id="l1-ood-hidden-lag",
        split_kind="ood",
        visible_variables=["x_minus_1", "x_minus_2"],
        required_variables=["x_minus_3"],
        observed_accuracy=0.0625,
    )

    payload = winnability.build_payload(root=tmp_path, generated_at="fixture", registered_splits=[split])
    row = payload["certificates"][0]

    assert row["upper_bound_accuracy"] <= row["chance_accuracy"] + row["epsilon"]
    assert row["unwinnable"] is True
    assert row["winnable"] is False
    assert row["claim_permissions"] == {
        "memorization_claim_allowed": False,
        "generalization_claim_allowed": False,
        "separation_claim_allowed": False,
        "architecture_claim_allowed": False,
        "rule_abstraction_claim_allowed": False,
    }
    assert payload["audit"]["fail_closed_count"] == 1
    assert payload["hardgates"]["ORACLE-HG3"]["status"] == "pass"
    assert "certificate_id" in row
    assert "row" + "_id" not in row


def test_missing_input_accessibility_source_fails_closed(tmp_path):
    payload = winnability.build_payload(root=tmp_path, generated_at="fixture")

    assert payload["source_artifacts"]["input_accessibility"]["status"] == "missing"
    assert payload["audit"]["status"] == "fail"
    assert payload["audit"]["failed_count"] == len(payload["certificates"])
    assert payload["audit"]["fail_closed_count"] == len(payload["certificates"])
    assert payload["hardgates"]["ORACLE-HG5"]["status"] == "fail"
    for row in payload["certificates"]:
        assert row["status"] == "fail"
        assert row["winnable"] is False
        assert row["claim_permissions"] == {
            "memorization_claim_allowed": False,
            "generalization_claim_allowed": False,
            "separation_claim_allowed": False,
            "architecture_claim_allowed": False,
            "rule_abstraction_claim_allowed": False,
        }
        assert "missing-input-accessibility-source" in row["failure_reasons"]


def test_l1_indist_pair_coverage_ceiling_is_table_coverage():
    eval_pairs = [(left, right) for left in range(16) for right in range(16)]
    train_pairs = [pair for pair in eval_pairs for _ in range(4)]
    expected = 1.0 - math.exp(-4.0) + math.exp(-4.0) / 16.0
    split = _split(
        task_id="l1-finite-pair",
        split_id="l1-indist-finite-pair",
        task_family="analytic-table-coverage",
        resolver_family="analytic-table-coverage",
        train_pairs=train_pairs,
        eval_pairs=eval_pairs,
        label_cardinality=16,
        observed_accuracy=0.982,
    )

    row = winnability.evaluate_split(split).to_json()

    assert row["coverage"]["coverage_ceiling"] == pytest.approx(expected, abs=1e-6)
    assert row["coverage"]["coverage_classification"] == "table-coverage"
    assert row["claim_permissions"]["generalization_claim_allowed"] is False
    assert row["claim_permissions"]["rule_abstraction_claim_allowed"] is False


def test_held_out_pair_split_is_winnable():
    row = winnability.evaluate_split(_split(task_id="held-out-pair", split_id="held-out-pair")).to_json()

    assert row["method"] == "analytic_bayes"
    assert row["upper_bound_accuracy"] > row["chance_accuracy"] + row["epsilon"]
    assert row["winnable"] is True
    assert row["unwinnable"] is False


def test_oracle_arm_requires_real_run_pointer():
    split = _split(
        task_id="oracle",
        split_id="oracle",
        task_family="oracle-arm",
        resolver_family="oracle-arm",
        oracle_run_ref="reports/runs/oracle/summary.json:$.metrics.accuracy",
        upper_bound_accuracy=0.9,
    )

    missing = winnability.evaluate_split(split).to_json()
    valid = winnability.evaluate_split(
        split,
        oracle_runs=[
            {
                "oracle_run_ref": "reports/runs/oracle/summary.json:$.metrics.accuracy",
                "artifact": "reports/runs/oracle/summary.json",
                "pointer": "$.metrics.accuracy",
                "metric_pointer": "$.metrics.accuracy",
                "split_fingerprint": "fixture-fingerprint",
                "model_id": "oracle-fixture",
                "seed": 7,
                "measured_accuracy": 0.9,
            }
        ],
    ).to_json()

    assert missing["status"] == "fail"
    assert "invalid-oracle-run-ref" in missing["failure_reasons"]
    assert valid["status"] == "pass"
    assert valid["method"] == "oracle_arm"


def test_missing_duplicate_unresolved_rows_fail_closed():
    present = _split(task_id="present", split_id="present")
    missing = _split(task_id="missing", split_id="missing")
    unresolved = _split(
        task_id="unresolved",
        split_id="unresolved",
        task_family="unresolved",
        resolver_family="unresolved",
    )
    present_row = winnability.evaluate_split(present).to_json()
    unresolved_row = winnability.evaluate_split(unresolved).to_json()

    audit = winnability.audit_certificates(
        [present, missing, unresolved],
        [present_row, dict(present_row), unresolved_row],
    )

    assert audit["missing_certificate_count"] == 1
    assert audit["duplicate_certificate_count"] == 1
    assert audit["unresolved_count"] == 1
    assert audit["failed_count"] >= 3
    assert audit["fail_closed_count"] >= 3
    assert audit["status"] == "fail"


def test_compact_winnability_ref_shape():
    ref = winnability.compact_winnability_ref("win-fixture")

    assert ref == {
        "artifact": "reports/canonical/winnability-certificates.json",
        "certificate_id": "win-fixture",
        "pointer": "reports/canonical/winnability-certificates.json:$.certificates",
    }

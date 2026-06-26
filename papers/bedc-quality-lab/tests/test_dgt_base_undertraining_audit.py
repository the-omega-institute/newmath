import importlib.util
import json
from pathlib import Path

import pytest

from bedc_quality_lab import dgt_base_undertraining_audit as audit


ROOT = Path(__file__).resolve().parents[1]


def _l1_payload():
    return json.loads((ROOT / audit.L1_SOURCE_ARTIFACT).read_text(encoding="utf-8"))


def _payload(l1_payload=None):
    return audit.build_payload(
        root=ROOT,
        generated_at="fixture",
        l1_payload=l1_payload or _l1_payload(),
        fair_baseline_payload=_fair_baseline_fixture(),
    )


def _audit(payload):
    return payload["base_undertraining_audit"]


def _rows(payload):
    return {row["comparison_id"]: row for row in _audit(payload)["comparison_rows"]}


def _load_audit_script():
    script_path = ROOT / "scripts/run_dgt_base_undertraining_audit.py"
    spec = importlib.util.spec_from_file_location("run_dgt_base_undertraining_audit_test", script_path)
    assert spec is not None
    assert spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _copy_l1(tmp_path):
    target = tmp_path / audit.L1_SOURCE_ARTIFACT
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes((ROOT / audit.L1_SOURCE_ARTIFACT).read_bytes())
    ia_target = tmp_path / audit.INPUT_ACCESSIBILITY_SOURCE_ARTIFACT
    ia_target.parent.mkdir(parents=True, exist_ok=True)
    ia_target.write_bytes((ROOT / audit.INPUT_ACCESSIBILITY_SOURCE_ARTIFACT).read_bytes())
    fair_summary = tmp_path / audit.FAIR_BASELINE_SUMMARY_ARTIFACT
    fair_summary.parent.mkdir(parents=True, exist_ok=True)
    fixture = _fair_baseline_fixture()
    fair_summary.write_text(json.dumps(fixture, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    fair_raw = tmp_path / audit.FAIR_BASELINE_METRICS_ARTIFACT
    fair_raw.write_text(
        "".join(
            json.dumps({"arm_id": audit.FAIR_BASELINE_ARM_ID, "seed": seed}, sort_keys=True) + "\n"
            for seed in fixture["training_config"]["seeds"]
        ),
        encoding="utf-8",
    )


def _fair_baseline_fixture():
    l1 = _l1_payload()
    arm = l1["l1_step_ladder"]["per_step"][0]["training_arms"]["parameter_matched_attention"]
    metrics = arm["metrics"]
    return {
        "schema_id": "bedc-quality-lab:non-starved-fair-baseline-summary",
        "artifact_id": "bedc-quality-lab:non-starved-fair-baseline",
        "arm_id": audit.FAIR_BASELINE_ARM_ID,
        "model_source_arm_id": audit.FAIR_BASELINE_MODEL_ARM_ID,
        "role": "fair_baseline",
        "status": "pass",
        "source_artifacts": {
            "raw_metrics": audit.FAIR_BASELINE_METRICS_ARTIFACT,
            "summary": audit.FAIR_BASELINE_SUMMARY_ARTIFACT,
            "l1_model_owner": "bedc_quality_lab/dgt_l1_controls.py",
        },
        "input_visibility": {
            "visible_variables": ["x_minus_1", "x_minus_2", "full_sequence"],
            "required_variables": ["x_minus_1", "x_minus_2"],
            "missing_variables": [],
            "information_starved": False,
            "source_pointer": f"{audit.INPUT_ACCESSIBILITY_SOURCE_ARTIFACT}#arm={audit.FAIR_BASELINE_INPUT_ARM_ID}",
        },
        "training_config": {
            "seeds": arm["seeds"],
            "epoch_count": 36,
            "train_examples": 1024,
            "eval_examples": 256,
            "batch_size": 128,
            "learning_rate": 0.018,
            "device_policy": {"requested_device": "cpu", "resolved_device": "cpu"},
        },
        "metrics": {
            "accuracy_mean": metrics["accuracy_mean"],
            "accuracy_ci95_low": metrics["accuracy_ci95_low"],
            "ood_accuracy_mean": metrics["ood_accuracy_mean"],
            "validation_loss_mean": metrics["validation_loss_mean"],
            "validation_loss_ci95_low": metrics["validation_loss_ci95_low"],
            "loss_decrease_mean": metrics["loss_decrease_mean"],
            "loss_decrease_ci95_low": metrics["loss_decrease_mean"],
            "loss_start_mean": 2.78,
            "loss_end_mean": round(2.78 - metrics["loss_decrease_mean"], 6),
            "UER_mean": metrics["UER_mean"],
            "parameter_l2_delta_mean": metrics["parameter_l2_delta_mean"],
            "positive_margin_over_chance_mean": metrics["positive_margin_over_chance_mean"],
        },
        "parameter_count": arm["parameter_count"],
        "compute_units": arm["compute_units"],
        "seed_count": arm["seed_count"],
        "record_count": arm["seed_count"],
        "comparison_tolerance": audit.FAIR_BASELINE_TOLERANCE,
        "raw_record_pointers": [f"{audit.FAIR_BASELINE_METRICS_ARTIFACT}:$.lines[{index}]" for index in range(arm["seed_count"])],
        "summary_pointer": f"{audit.FAIR_BASELINE_SUMMARY_ARTIFACT}:$",
    }


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


def test_train_non_starved_fair_baseline_runs_training_and_writes_artifacts(tmp_path):
    summary = audit.train_non_starved_fair_baseline(
        root=tmp_path,
        requested_device="cpu",
        seeds=(1174,),
        epoch_count=5,
        generated_at="fixture",
        progress=False,
    )
    metrics_path = tmp_path / audit.FAIR_BASELINE_METRICS_ARTIFACT
    summary_path = tmp_path / audit.FAIR_BASELINE_SUMMARY_ARTIFACT
    records = [json.loads(line) for line in metrics_path.read_text(encoding="utf-8").splitlines()]
    written_summary = json.loads(summary_path.read_text(encoding="utf-8"))
    row = records[0]

    assert len(records) == 1
    assert written_summary == summary
    assert summary["arm_id"] == audit.FAIR_BASELINE_ARM_ID
    assert summary["status"] == "pass"
    assert summary["record_count"] == 1
    assert summary["seed_count"] == 1
    assert summary["training_config"]["seeds"] == [1174]
    assert summary["training_config"]["epoch_count"] == 5
    assert summary["training_config"]["device_policy"]["requested_device"] == "cpu"
    assert summary["training_config"]["device_policy"]["resolved_device"] == "cpu"
    assert summary["input_visibility"]["visible_variables"] == ["x_minus_1", "x_minus_2", "full_sequence"]
    assert summary["input_visibility"]["information_starved"] is False
    assert summary["metrics"]["parameter_l2_delta_mean"] > 0.0
    assert summary["metrics"]["loss_decrease_mean"] > 0.0
    assert summary["metrics"]["loss_start_mean"] > summary["metrics"]["loss_end_mean"]
    assert summary["raw_record_pointers"] == [f"{audit.FAIR_BASELINE_METRICS_ARTIFACT}:$.lines[0]"]

    assert row["arm_id"] == audit.FAIR_BASELINE_ARM_ID
    assert row["model_source_arm_id"] == audit.FAIR_BASELINE_MODEL_ARM_ID
    assert row["input_visibility"]["visible_variables"] == ["x_minus_1", "x_minus_2", "full_sequence"]
    assert row["input_visibility"]["information_starved"] is False
    assert row["metrics"]["parameter_l2_delta"] > 0.0
    assert row["metrics"]["loss_decrease"] > 0.0
    assert row["metrics"]["loss_start"] > row["metrics"]["loss_end"]
    assert row["run_artifact_ref"] == f"{audit.FAIR_BASELINE_METRICS_ARTIFACT}:$.lines[0]"


def test_cli_trains_fair_baseline_before_writing_audit(monkeypatch, tmp_path, capsys):
    script = _load_audit_script()
    calls = []
    fair_summary = {
        "seed_count": 2,
        "training_config": {"seeds": [101, 102], "epoch_count": 3},
        "metrics": {
            "accuracy_mean": 0.25,
            "loss_start_mean": 2.0,
            "loss_end_mean": 1.5,
            "loss_decrease_mean": 0.5,
            "validation_loss_mean": 1.25,
        },
    }
    payload = {
        "base_undertraining_audit": {
            "artifact_id": "bedc-quality-lab:dgt-base-undertraining-audit",
            "verdict": "noninformative-separation",
            "claim_action": "record_noninformative_rows",
            "comparison_rows": [{"comparison_id": "equal_validation_loss"}],
        }
    }

    def train_stub(**kwargs):
        calls.append(("train", kwargs))
        return fair_summary

    def build_stub(**kwargs):
        calls.append(("build", kwargs))
        return payload

    def write_stub(payload_arg, **kwargs):
        calls.append(("write", payload_arg, kwargs))

    monkeypatch.setattr(script, "FAIR_BASELINE_SEEDS", (101, 102))
    monkeypatch.setattr(script, "FAIR_BASELINE_EPOCHS", 3)
    monkeypatch.setattr(script, "train_non_starved_fair_baseline", train_stub)
    monkeypatch.setattr(script, "build_payload", build_stub)
    monkeypatch.setattr(script, "write_artifacts", write_stub)

    assert script.main(["--root", str(tmp_path), "--generated-at", "fixture", "--device", "cpu"]) == 0
    output = json.loads(capsys.readouterr().out)

    assert [call[0] for call in calls] == ["train", "build", "write"]
    assert calls[0][1] == {
        "root": tmp_path,
        "requested_device": "cpu",
        "seeds": (101, 102),
        "epoch_count": 3,
        "generated_at": "fixture",
        "progress": True,
    }
    assert calls[1][1] == {"root": tmp_path, "generated_at": "fixture"}
    assert calls[2][1] == payload
    assert calls[2][2] == {"root": tmp_path, "generated_at": "fixture"}
    assert output["artifact_id"] == payload["base_undertraining_audit"]["artifact_id"]
    assert output["verdict"] == "noninformative-separation"
    assert output["claim_action"] == "record_noninformative_rows"
    assert output["comparison_count"] == 1
    assert output["fair_baseline"] == {
        "seed_count": 2,
        "seeds": [101, 102],
        "epoch_count": 3,
        "accuracy_mean": 0.25,
        "loss_start_mean": 2.0,
        "loss_end_mean": 1.5,
        "loss_decrease_mean": 0.5,
        "validation_loss_mean": 1.25,
    }


def test_base_undertraining_audit_records_non_starved_fair_baseline_for_current_l1_evidence():
    payload = _payload()
    audit_payload = _audit(payload)
    rows = _rows(payload)

    assert audit_payload["verdict"] == "noninformative-separation"
    assert audit_payload["claim_action"] == "record_noninformative_rows"
    assert audit_payload["construct_validity"]["status"] == "construct-valid"
    assert audit_payload["construct_validity"]["bayes_upper_bound_accuracy"] is None
    assert audit_payload["construct_validity"]["source_pointers"]["fair_reconstruction"].endswith("/issues/1196")
    assert audit_payload["construct_validity"]["source_pointers"]["input_accessibility"] == (
        "reports/canonical/input-accessibility.json:$"
    )
    assert audit_payload["construct_validity"]["source_pointers"]["fair_baseline_summary"] == (
        f"{audit.FAIR_BASELINE_SUMMARY_ARTIFACT}:$"
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
    fair_contract = audit_payload["source_contract"]["fair_baseline_contract"]
    assert fair_contract["status"] == "pass"
    assert fair_contract["visible_variables"] == ["x_minus_1", "x_minus_2", "full_sequence"]
    assert fair_contract["missing_variables"] == []
    assert fair_contract["information_starved"] is False
    assert fair_contract["loss_decrease_mean"] > 0.0
    assert fair_contract["compute_ratio_to_dgt_anchor"] <= audit.FAIR_BASELINE_TOLERANCE
    assert fair_contract["parameter_ratio_to_dgt_anchor"] <= audit.FAIR_BASELINE_TOLERANCE
    assert set(rows) == {"equal_step", "equal_compute", "equal_loss_decrease", "equal_validation_loss"}
    assert rows["equal_step"]["match_axis"] == "training_steps"
    assert rows["equal_compute"]["match_axis"] == "compute_units"
    assert rows["equal_loss_decrease"]["match_axis"] == "loss_decrease"
    assert rows["equal_validation_loss"]["match_axis"] == "validation_loss"
    assert rows["equal_validation_loss"]["status"] == "resolved"
    assert rows["equal_validation_loss"]["source_artifact"] == audit.FAIR_BASELINE_SUMMARY_ARTIFACT
    assert rows["equal_validation_loss"]["source_pointer"].endswith("$.metrics.validation_loss_mean")
    assert all(row["decision"] == "noninformative-dgt-separated" for row in rows.values())
    assert audit_payload["hardgates"]["BASE-HG1"]["status"] == "pass"
    assert audit_payload["hardgates"]["BASE-HG2"]["status"] == "pass"
    assert audit_payload["hardgates"]["BASE-HG3"]["status"] == "pass"
    assert audit_payload["hardgates"]["BASE-UNDER-HG1"]["status"] == "pass"
    assert audit_payload["hardgates"]["BASE-UNDER-HG2"]["status"] == "pass"
    assert audit_payload["hardgates"]["BASE-UNDER-HG0"]["status"] == "pass"
    assert audit_payload["hardgates"]["BASE-UNDER-HG5"]["status"] == "pass"
    assert audit_payload["boundary_ledger"] == []
    assert [row["comparison_id"] for row in audit_payload["evidence_ledger"]] == [
        "equal_step",
        "equal_compute",
        "equal_loss_decrease",
        "equal_validation_loss",
    ]


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
    assert row["source_artifact"] == audit.FAIR_BASELINE_SUMMARY_ARTIFACT
    assert row["source_pointer"] == f"{audit.FAIR_BASELINE_SUMMARY_ARTIFACT}:$.metrics.validation_loss_mean"
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
    payload = audit.build_payload(
        root=ROOT,
        generated_at="fixture",
        l1_payload=_l1_payload(),
        fair_baseline_payload={"status": "missing"},
    )
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
        fair_baseline_payload=_fair_baseline_fixture(),
        construct_validity_override=audit.construct_validity_assessment(
            baseline_input_order=2,
            label_dependency_order=2,
            second_predecessor_visible=True,
        ),
    )
    audit_payload = _audit(payload)

    assert audit_payload["construct_validity"]["status"] == "construct-valid"
    assert audit_payload["hardgates"]["BASE-UNDER-HG0"]["status"] == "pass"
    assert audit_payload["verdict"] == "noninformative-separation"
    assert audit_payload["claim_action"] == "record_noninformative_rows"
    assert audit_payload["evidence_ledger"]


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
    fair = _fair_baseline_fixture()
    fair["metrics"]["accuracy_mean"] = l1["l1_step_ladder"]["per_step"][0]["metrics"]["dgt_accuracy_mean"]

    payload = audit.build_payload(
        root=ROOT,
        generated_at="fixture",
        l1_payload=l1,
        fair_baseline_payload=fair,
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
        "source_pointer": f"{audit.FAIR_BASELINE_SUMMARY_ARTIFACT}:$.compute_units",
    } in audit_payload["boundary_ledger"]
    assert audit_payload["hardgates"]["BASE-UNDER-HG4"]["status"] == "triggered"
    assert audit_payload["hardgates"]["BASE-HG4"]["status"] == "triggered"


def test_equal_loss_decrease_catchup_records_boundary():
    l1 = _l1_payload()
    fair = _fair_baseline_fixture()
    fair["metrics"]["accuracy_mean"] = l1["l1_step_ladder"]["per_step"][0]["metrics"]["dgt_accuracy_mean"] + 0.01

    payload = audit.build_payload(
        root=ROOT,
        generated_at="fixture",
        l1_payload=l1,
        fair_baseline_payload=fair,
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
        "ledger_id": "base-undertraining-equal_loss_decrease",
        "comparison_id": "equal_loss_decrease",
        "reason": "base reaches DGT after the construct-validity premise is satisfied",
        "source_pointer": f"{audit.FAIR_BASELINE_SUMMARY_ARTIFACT}:$.metrics.loss_decrease_mean",
    } in audit_payload["boundary_ledger"]


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

    assert f"{audit.FAIR_BASELINE_SUMMARY_ARTIFACT}:$.metrics.validation_loss_mean" in serialized
    assert audit.FAIR_BASELINE_METRICS_ARTIFACT in serialized
    assert "step_rows" not in serialized
    assert "training_arms" not in serialized
    assert "No undertraining discharge claim from information-starved ablations." in serialized
    for row in _audit(payload)["comparison_rows"]:
        assert row["source_artifact"] == audit.FAIR_BASELINE_SUMMARY_ARTIFACT
        assert row["source_pointer"].startswith(f"{audit.FAIR_BASELINE_SUMMARY_ARTIFACT}:")


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

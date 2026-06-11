import json

import pytest

from bedc_quality_lab import dgt_l1_controls as l1
from bedc_quality_lab.discovery_compiler.pointers import resolve_artifact_pointer
from scripts import run_dgt_l1_controls as runner


def _payload():
    config = l1.L1TrainingConfig(step_grid=(36, 72), train_examples=128, eval_examples=64)
    return l1.build_payload(generated_at="fixture-time", requested_device="cpu", config=config)


def _expect_invalid(payload, match):
    with pytest.raises(ValueError, match=match):
        l1.validate_payload(payload)


def _refresh_ladder_fail_closed(payload, gate_id):
    ladder = payload["l1_step_ladder"]
    ladder["hardgates"] = l1.evaluate_l1step_hardgates(ladder)
    ladder["status"] = "pass" if all(row["status"] == "pass" for row in ladder["hardgates"].values()) else "fail"
    ladder["verdict"] = l1.derive_l1_step_ladder_verdict(ladder["convergence_crossover"], ladder["hardgates"])

    assert ladder["hardgates"][gate_id]["status"] == "fail"
    assert ladder["status"] == "fail"
    assert ladder["verdict"] == "inconclusive"


def test_l1_task_spec_is_order_k_sequence_not_tabular_fixture():
    payload = _payload()
    task = payload["task_spec"]
    source = task["required_order_source"]

    assert task["task_family"] == "bounded_tiny_sequence_order_k"
    assert task["vocab_size"] <= 16
    assert task["sequence_length"] <= 64
    assert task["train_examples"] <= 4096
    assert source["status"] == "pointer-backed"
    assert source["ledger_rows_pointer"] == "reports/canonical/order-k-benchmark.json:$.surface_required_order_ledger.rows"
    assert source["ledger_row_pointer"] == "reports/canonical/order-k-benchmark.json:$.surface_required_order_ledger.rows[1]"
    assert source["required_order_pointer"].endswith(".required_order")
    resolved = resolve_artifact_pointer(l1.LAB_ROOT, source["ledger_row_pointer"])
    assert resolved["task_id"] == "B2"
    assert resolved["required_order"] == 2

    for forbidden in ("order_k", "dependency_rule", "sequence_dependency_window", "ood_slices"):
        assert forbidden not in task

    mutated = json.loads(json.dumps(payload))
    mutated["task_spec"]["required_order_source"]["ledger_row_pointer"] = "reports/canonical/order-k-benchmark.json:$.surface_required_order_ledger.rows[0]"
    _expect_invalid(mutated, "ledger row pointer")


def test_l1_training_requires_real_torch_updates():
    payload = _payload()
    assert l1.source_regression_guard()["status"] == "pass"
    for arm in payload["training_arms"].values():
        assert arm["training_steps"] > 0
        assert arm["metrics"]["parameter_l2_delta_mean"] > 0
        assert arm["metrics"]["loss_decrease_mean"] > 0
        assert "FalseLedgerRate_mean" not in arm["metrics"]
        assert "JetCoverage_mean" not in arm["metrics"]
        assert "classifier_shift_count" not in arm["metrics"]
    ladder = payload["l1_step_ladder"]
    assert ladder["step_grid"] == [36, 72]
    assert len(ladder["step_rows"]) == 2
    assert all(step["training_arms"]["dgt_l1"]["device_resolved"] == "cpu" for step in ladder["per_step"])
    assert all("dgt_loss_decrease_mean" in step["metrics"] for step in ladder["step_rows"])

    mutated = json.loads(json.dumps(payload))
    mutated["training_arms"]["dgt_l1"]["training_steps"] = 0
    _expect_invalid(mutated, "optimizer steps")

    mutated = json.loads(json.dumps(payload))
    mutated["training_arms"]["dgt_l1"]["metrics"]["parameter_l2_delta_mean"] = 0
    _expect_invalid(mutated, "parameter update")


def test_l1_owner_required_metrics_are_boundary_only_and_pointer_backed():
    payload = _payload()
    boundary = payload["owner_local_measurement_boundary"]

    assert payload["hardgates"]["L1-REVIEW-HG1"]["status"] == "pass"
    assert boundary["measured_status"] == "measured-owner-required"
    assert boundary["not_measurable_here"] == list(l1.OWNER_REQUIRED_METRICS)
    for pointer in boundary["metric_owners"].values():
        assert resolve_artifact_pointer(l1.LAB_ROOT, pointer) is not None

    mutated = json.loads(json.dumps(payload))
    mutated["owner_local_measurement_boundary"]["metric_owners"]["JetCoverage"] = "reports/canonical/missing.json:$.x"
    mutated["hardgates"] = l1.evaluate_hardgates(mutated)
    _expect_invalid(mutated, "L1-REVIEW-HG1|owner-local measurement boundary")

    mutated = json.loads(json.dumps(payload))
    mutated["training_arms"]["dgt_l1"]["metrics"]["JetCoverage_mean"] = 0.5
    mutated["hardgates"] = l1.evaluate_hardgates(mutated)
    _expect_invalid(mutated, "L1-REVIEW-HG1|owner-required metric")


def test_l1_base_control_param_and_compute_matched():
    payload = _payload()
    assert payload["hardgates"]["L1-REVIEW-HG5"]["status"] == "pass"

    mutated = json.loads(json.dumps(payload))
    mutated["training_arms"]["parameter_matched_l1"]["parameter_count"] *= 4
    mutated["hardgates"] = l1.evaluate_hardgates(mutated)
    _expect_invalid(mutated, "L1-REVIEW-HG5")

    mutated = json.loads(json.dumps(payload))
    mutated["training_arms"].pop("information_starved_l1_baseline")
    _expect_invalid(mutated, "training arms")


def test_l1_matched_random_structural_control_fail_closed():
    payload = _payload()
    assert payload["hardgates"]["L1-REVIEW-HG2"]["status"] == "pass"
    assert payload["hardgates"]["L1-REVIEW-HG3"]["status"] == "pass"
    assert payload["hardgates"]["L1-REVIEW-HG4"]["status"] == "pass"
    assert payload["paired_accuracy"]["dgt_minus_information_starved_baseline"]["delta_ci95_low"] > 0.0
    assert payload["paired_accuracy"]["dgt_minus_matched_random"]["delta_ci95_low"] > 0.0

    mutated = json.loads(json.dumps(payload))
    mutated["paired_accuracy"]["dgt_minus_information_starved_baseline"]["delta_ci95_low"] = 0.0
    mutated["hardgates"] = l1.evaluate_hardgates(mutated)
    _expect_invalid(mutated, "L1-REVIEW-HG2")

    mutated = json.loads(json.dumps(payload))
    mutated["paired_accuracy"]["dgt_minus_matched_random"]["delta_ci95_low"] = 0.0
    mutated["hardgates"] = l1.evaluate_hardgates(mutated)
    _expect_invalid(mutated, "L1-REVIEW-HG3")

    mutated = json.loads(json.dumps(payload))
    mutated["training_arms"]["matched_random_structural_l1"]["structural_marginals_preserved"] = False
    mutated["hardgates"] = l1.evaluate_hardgates(mutated)
    _expect_invalid(mutated, "L1-REVIEW-HG3")

    mutated = json.loads(json.dumps(payload))
    mutated["training_arms"]["matched_random_structural_l1"]["metrics"]["classifier_shift_count"] = 0
    mutated["hardgates"] = l1.evaluate_hardgates(mutated)
    _expect_invalid(mutated, "L1-REVIEW-HG4|owner-required metric")


def test_l1_compute_and_parameter_ledgers_require_positive_values():
    payload = _payload()
    assert payload["hardgates"]["L1-REVIEW-HG5"]["status"] == "pass"
    assert payload["hardgates"]["L1-REVIEW-HG5"]["status"] == "pass"

    mutated = json.loads(json.dumps(payload))
    first_key = next(iter(mutated["compute_ledger"]["per_seed_step_cell"]))
    mutated["compute_ledger"]["per_seed_step_cell"][first_key]["compute_units"] = 0
    mutated["hardgates"] = l1.evaluate_hardgates(mutated)
    _expect_invalid(mutated, "L1-REVIEW-HG5")

    mutated = json.loads(json.dumps(payload))
    mutated["parameter_ledger"]["per_arm"]["dgt_l1"]["parameter_count"] = 0
    mutated["hardgates"] = l1.evaluate_hardgates(mutated)
    _expect_invalid(mutated, "L1-REVIEW-HG5")


def test_l1_negative_witness_sweep_uses_hit_logic():
    payload = _payload()
    sweep = payload["negative_witness_sweep"]
    assert sweep["status"] == "pass"
    assert {row["witness"] for row in sweep["rows"]} == set(l1.REQUIRED_WITNESSES)
    assert [row["hardgate_id"] for row in sweep["rows"]] == ["ISB-HG", "UOOD-HG", "TCS-HG", "HEG-HG"]
    assert all(row["hit_logic"] for row in sweep["rows"])
    assert all(row["source_pointer"].startswith(l1.CANONICAL_JSON_ARTIFACT + ":$") for row in sweep["rows"])
    assert all(row["evidence_pointer"].startswith(l1.CANONICAL_JSON_ARTIFACT + ":$") for row in sweep["rows"])
    assert all(row["claim_downgrade"] and row["not_claimed"] for row in sweep["rows"])
    assert all(row["taint_status"].startswith("tainted-") for row in sweep["rows"])

    mutated = json.loads(json.dumps(payload))
    mutated["negative_witness_sweep"]["rows"] = []
    mutated["hardgates"] = l1.evaluate_hardgates(mutated)
    _expect_invalid(mutated, "L1-REVIEW-HG6")

    mutated = json.loads(json.dumps(payload))
    mutated["negative_witness_sweep"]["rows"][0]["regression_test_pointer_resolves"] = False
    mutated["hardgates"] = l1.evaluate_hardgates(mutated)
    _expect_invalid(mutated, "L1-REVIEW-HG6")

    mutated = json.loads(json.dumps(payload))
    mutated["negative_witness_sweep"]["rows"][0]["source_pointer"] = (
        f"{l1.CANONICAL_JSON_ARTIFACT}:$.negative_witness_sweep.missing"
    )
    mutated["hardgates"] = l1.evaluate_hardgates(mutated)
    _expect_invalid(mutated, "source pointer does not resolve")

    mutated = json.loads(json.dumps(payload))
    mutated["negative_witness_sweep"]["rows"][0]["evidence_pointer"] = (
        f"{l1.CANONICAL_JSON_ARTIFACT}:$.negative_witness_sweep.missing"
    )
    mutated["hardgates"] = l1.evaluate_hardgates(mutated)
    _expect_invalid(mutated, "evidence pointer does not resolve")


def test_l1_independent_replay_checks_digest_and_metric_tolerance():
    payload = _payload()
    replay = payload["independent_replay"]
    assert replay["status"] == "pass"
    assert replay["seed_count"] >= 16
    assert replay["task_spec_digest"]
    assert replay["seed_digest"]

    mutated = json.loads(json.dumps(payload))
    mutated["independent_replay"]["task_spec_digest"] = ""
    mutated["hardgates"] = l1.evaluate_hardgates(mutated)
    _expect_invalid(mutated, "L1-REVIEW-HG6")

    mutated = json.loads(json.dumps(payload))
    mutated["independent_replay"]["metric_tolerance_rows"][0]["status"] = "fail"
    mutated["hardgates"] = l1.evaluate_hardgates(mutated)
    _expect_invalid(mutated, "L1-REVIEW-HG6")


def test_l1_claim_capsule_scope_and_pointer_resolution():
    payload = _payload()
    capsule = payload["claim_capsule_ref"]
    assert capsule["schema_id"] == "bedc.quality.claim_capsule"
    assert capsule["capsule_subtype"] == "bedc.model.dgt_l1_tiny_sequence_claim_capsule"
    assert capsule["evidence_scope"] == "bounded-tiny-sequence"
    assert "terminal_verdict" not in json.dumps(capsule, sort_keys=True)
    assert all(pointer.startswith(l1.CANONICAL_JSON_ARTIFACT + ":$") for pointer in capsule["evidence_pointers"])

    mutated = json.loads(json.dumps(payload))
    mutated["claim_capsule_ref"]["evidence_scope"] = "production"
    _expect_invalid(mutated, "ClaimCapsule")

    mutated = json.loads(json.dumps(payload))
    mutated["claim_capsule_ref"]["evidence_pointers"][0] = "reports/canonical/missing.json:$.x"
    _expect_invalid(mutated, "ClaimCapsule")


def test_l1_review_status_pass_and_scoped_boundary():
    payload = _payload()
    assert payload["review_status"] == "pass"
    assert payload["promotion_readiness"] == "ready-pass"
    assert payload["hardgates"]["L1-REVIEW-HG7"]["status"] == "pass"
    assert payload["l1_tiny_sequence_projection"]["verdict"] == "scoped-boundary"
    assert payload["l1_tiny_sequence_projection"]["pass_scope"] == "in-dist order-2 only"
    assert payload["l1_tiny_sequence_projection"]["ood_generalization_claim"] == "not-claimed"

    mutated = json.loads(json.dumps(payload))
    mutated["review_status"] = "blocked"
    mutated["hardgates"] = l1.evaluate_hardgates(mutated)
    _expect_invalid(mutated, "review status")


def test_dgt_l1_controls_cli_main_forwards_config_and_writes_artifact_layout(tmp_path, capsys, monkeypatch):
    seen = {}
    real_build_payload = l1.build_payload

    def recording_build_payload(*, generated_at, requested_device, config, root=None):
        seen["generated_at"] = generated_at
        seen["requested_device"] = requested_device
        seen["config"] = config
        return real_build_payload(
            generated_at=generated_at,
            requested_device=requested_device,
            config=config,
            root=root,
        )

    monkeypatch.setattr(runner, "build_payload", recording_build_payload)
    exit_code = runner.main(
        [
            "--root",
            str(tmp_path),
            "--generated-at",
            "fixture-time",
            "--requested-device",
            "cpu",
            "--seeds",
            "1174,1175,1176,1177,1178,1179,1180,1181,1182,1183,1184,1185,1186,1187,1188,1189",
            "--training-steps",
            "8",
            "--step-grid",
            "8,16",
            "--train-examples",
            "32",
            "--eval-examples",
            "64",
        ]
    )

    assert exit_code == 0
    config = seen["config"]
    assert seen["generated_at"] == "fixture-time"
    assert seen["requested_device"] == "cpu"
    assert config == l1.L1TrainingConfig(
        seeds=(1174, 1175, 1176, 1177, 1178, 1179, 1180, 1181, 1182, 1183, 1184, 1185, 1186, 1187, 1188, 1189),
        training_steps=8,
        step_grid=(8, 16),
        train_examples=32,
        eval_examples=64,
    )

    summary = json.loads(capsys.readouterr().out)
    assert summary["artifact_id"] == l1.ARTIFACT_ID
    assert summary["status"] == "pass"
    assert summary["review_status"] == "pass"
    assert summary["promotion_readiness"] == "ready-pass"
    assert summary["device"] == "cpu"
    assert summary["compute_units"] > 0
    assert summary["opened_ladder_level"] == "L1_tiny_sequence"
    assert summary["ood_generalization_claim"] == "not-claimed"
    assert summary["l1_step_ladder_verdict"] in {"scoped-review-signal", "information-starved-catches-up", "inconclusive"}
    assert summary["l1_step_ladder_crossover"] in {"information-starved-crossover-observed", "no-information-starved-crossover-observed"}

    run_artifacts = l1.run_artifacts_payload()
    expected_artifacts = [
        l1.CANONICAL_JSON_ARTIFACT,
        l1.CANONICAL_MARKDOWN_ARTIFACT,
        run_artifacts["summary"],
        run_artifacts["raw_metrics"],
        run_artifacts["claim_capsule"],
        run_artifacts["report"],
    ]
    assert all((tmp_path / artifact).exists() for artifact in expected_artifacts)

    canonical_payload = json.loads((tmp_path / l1.CANONICAL_JSON_ARTIFACT).read_text(encoding="utf-8"))
    assert canonical_payload["task_spec"]["seed_protocol"]["deterministic_seeds"] == list(config.seeds)
    assert canonical_payload["task_spec"]["train_examples"] == 32
    assert canonical_payload["task_spec"]["eval_examples"] == 64
    assert canonical_payload["training_arms"]["dgt_l1"]["training_steps"] == 8
    assert canonical_payload["l1_step_ladder"]["step_grid"] == [8, 16]
    assert len(canonical_payload["l1_step_ladder"]["step_rows"]) == 2
    claim_capsule = json.loads((tmp_path / run_artifacts["claim_capsule"]).read_text(encoding="utf-8"))
    assert claim_capsule == canonical_payload["claim_capsule_ref"]
    assert not (tmp_path / l1.CANONICAL_FINGERPRINT_ARTIFACT).exists()


def test_dgt_l1_controls_regeneration_is_byte_stable(tmp_path, capsys):
    config_args = [
        "--root",
        str(tmp_path),
        "--generated-at",
        "fixture-time",
        "--seeds",
        "1174,1175,1176,1177,1178,1179,1180,1181,1182,1183,1184,1185,1186,1187,1188,1189",
        "--training-steps",
        "8",
        "--step-grid",
        "8,16",
        "--train-examples",
        "64",
        "--eval-examples",
        "64",
    ]
    run_artifacts = l1.run_artifacts_payload()
    checked_paths = [
        tmp_path / run_artifacts["raw_metrics"],
        tmp_path / l1.CANONICAL_JSON_ARTIFACT,
    ]

    assert runner.main(config_args) == 0
    capsys.readouterr()
    first = {path: path.read_bytes() for path in checked_paths}
    first_payload = json.loads((tmp_path / l1.CANONICAL_JSON_ARTIFACT).read_text(encoding="utf-8"))

    assert runner.main(config_args) == 0
    capsys.readouterr()
    second = {path: path.read_bytes() for path in checked_paths}
    second_payload = json.loads((tmp_path / l1.CANONICAL_JSON_ARTIFACT).read_text(encoding="utf-8"))

    assert first == second
    assert first_payload["training_arms"]["dgt_l1"]["device_requested"] == "cpu"
    assert first_payload["training_arms"]["dgt_l1"]["device_resolved"] == "cpu"
    assert first_payload["independent_replay"] == second_payload["independent_replay"]
    assert first_payload["l1_step_ladder"] == second_payload["l1_step_ladder"]


def test_l1_component_ablation_reuses_measured_owner_without_component_effects():
    payload = _payload()
    boundary = payload["component_ablation_boundary"]
    assert boundary["owner_issue"] == "github:issue:1168"
    assert boundary["owner_artifact"] == "reports/canonical/dgt-neural-ablation.json"
    assert boundary["measured_status"] == "measured-owner-required"
    assert resolve_artifact_pointer(l1.LAB_ROOT, boundary["owner_pointer"]) is not None
    assert boundary["not_recreated_here"] is True
    assert "COMPONENT_EFFECTS" not in json.dumps(payload, sort_keys=True)

    mutated = json.loads(json.dumps(payload))
    mutated["component_ablation_boundary"]["not_recreated_here"] = False
    _expect_invalid(mutated, "component ablation")


def test_l1_step_ladder_grid_verdict_and_no_sidecar(tmp_path):
    payload = _payload()
    l1.write_artifacts(payload, root=tmp_path, generated_at="fixture-time")
    canonical = json.loads((tmp_path / l1.CANONICAL_JSON_ARTIFACT).read_text(encoding="utf-8"))
    ladder = canonical["l1_step_ladder"]

    assert not (tmp_path / "reports/canonical/discovery_gated_transformer_scaling_ladder.json").exists()
    assert ladder["step_grid"] == [36, 72]
    assert ladder["seed_count_per_arm_per_step"] == 16
    assert all(set(step["training_arms"]) == set(l1.ARM_IDS) for step in ladder["per_step"])
    assert all(all(count == 16 for count in step["seed_counts"].values()) for step in ladder["per_step"])
    assert ladder["convergence_crossover"] == l1.derive_l1_step_ladder_crossover(ladder["step_rows"])
    assert ladder["convergence_crossover"]["anchor_training_steps"] == 36
    assert ladder["convergence_crossover"]["anchor_accuracy_mean"] == ladder["step_rows"][0]["metrics"]["dgt_accuracy_mean"]
    assert ladder["verdict"] == l1.derive_l1_step_ladder_verdict(ladder["convergence_crossover"], ladder["hardgates"])
    serialized = json.dumps(ladder, sort_keys=True)
    for forbidden in ("claim_capsule_ref", "discovery_map", "stable_causal_attribution"):
        assert forbidden not in serialized


def test_l1_step_ladder_grid_cell_integrity_fail_closed():
    payload = _payload()
    assert payload["l1_step_ladder"]["hardgates"]["L1STEP-HG1"]["status"] == "pass"

    mutated = json.loads(json.dumps(payload))
    mutated["l1_step_ladder"]["per_step"][0].pop("training_steps")
    _refresh_ladder_fail_closed(mutated, "L1STEP-HG1")

    mutated = json.loads(json.dumps(payload))
    mutated["l1_step_ladder"]["per_step"][0]["training_arms"].pop("information_starved_l1_baseline")
    _refresh_ladder_fail_closed(mutated, "L1STEP-HG1")

    mutated = json.loads(json.dumps(payload))
    mutated["l1_step_ladder"]["per_step"][0]["seed_counts"]["dgt_l1"] = 7
    _refresh_ladder_fail_closed(mutated, "L1STEP-HG1")


def _fixture_stratum(accuracy, margin):
    return {
        "arm_id": "dgt_l1",
        "stratum": "fixture",
        "example_count": 16,
        "seed_count": 8,
        "pair_count": 4,
        "accuracy": accuracy,
        "true_class_logit_mean": margin + 0.5,
        "true_class_margin_mean": margin,
        "confidence_mean": 0.5,
        "chance_accuracy": 0.0625,
        "accuracy_minus_chance": round(accuracy - 0.0625, 6),
        "device_resolved": "cpu",
        "parameter_mutation_detected": False,
        "source_probe_row_count": 16,
    }


def _verdict_strata(high, low, unseen, ood):
    cells = {
        "train_seen_high_frequency_pair": high,
        "train_seen_low_frequency_pair": low,
        "train_unseen_pair": unseen,
        "ood_dependency_shift_pair": ood,
    }
    strata = {}
    for stratum, cell in cells.items():
        row = _fixture_stratum(*cell)
        row["stratum"] = stratum
        strata[stratum] = {"dgt_l1": row}
    return strata


def test_l1_ood_mechanism_surface_is_probe_derived_and_bounded():
    payload = _payload()
    mechanism = payload["l1_ood_mechanism"]

    assert mechanism["owner"] == "dgt-l1-controls"
    assert mechanism["verdict"] in set(l1.L1OOD_VERDICTS)
    assert set(mechanism["strata"]) == set(l1.L1OOD_STRATA)
    assert mechanism["source_pointers"]["probe_metrics"] == "reports/runs/discovery-gated-transformer/l1-tiny-sequence-controls/probe_metrics.jsonl"
    assert mechanism["l2_implication"]["verdict_pointer"] == f"{l1.CANONICAL_JSON_ARTIFACT}:$.l1_ood_mechanism.verdict"
    assert "strata" not in json.dumps(mechanism["l2_implication"], sort_keys=True)
    assert set(mechanism["hardgates"]) == set(l1.L1OOD_GATE_IDS)
    assert all(row["status"] == "pass" for row in mechanism["hardgates"].values())

    for stratum in l1.L1OOD_STRATA:
        assert set(mechanism["strata"][stratum]) == set(l1.ARM_IDS)
        dgt_row = mechanism["strata"][stratum]["dgt_l1"]
        assert dgt_row["example_count"] == dgt_row["source_probe_row_count"]
        assert dgt_row["seed_count"] >= 8
        assert dgt_row["device_resolved"] == "cpu"
        assert dgt_row["parameter_mutation_detected"] is False
        assert isinstance(dgt_row["true_class_logit_mean"], float)
        assert isinstance(dgt_row["true_class_margin_mean"], float)
        assert dgt_row["accuracy_minus_chance"] == round(dgt_row["accuracy"] - dgt_row["chance_accuracy"], 6)

    mutated = json.loads(json.dumps(payload))
    mutated["l1_ood_mechanism"]["strata"]["ood_dependency_shift_pair"]["dgt_l1"]["true_class_logit_mean"] = "missing"
    mutated["l1_ood_mechanism"]["hardgates"] = l1.evaluate_l1ood_hardgates(mutated["l1_ood_mechanism"])
    _expect_invalid(mutated, "logit aggregates|L1-REVIEW-HG6|hardgates fail closed")

    mutated = json.loads(json.dumps(payload))
    mutated["l1_ood_mechanism"]["verdict"] = "scripted"
    _expect_invalid(mutated, "verdict mismatch|decision table mismatch")


def test_l1_ood_mechanism_decision_table_branches():
    assert l1.derive_l1_ood_mechanism_verdict(
        _verdict_strata((0.4, 0.1), (0.08, -0.1), (0.07, -0.1), (0.07, -0.1))
    )["verdict"] == "memorization"
    assert l1.derive_l1_ood_mechanism_verdict(
        _verdict_strata((0.4, 0.1), (0.3, 0.1), (0.07, -0.1), (0.07, -0.1))
    )["verdict"] == "brittle-rule"
    assert l1.derive_l1_ood_mechanism_verdict(
        _verdict_strata((0.4, 0.1), (0.3, 0.1), (0.2, 0.1), (0.2, 0.1))
    )["verdict"] == "partial-rule"

    gates = {"L1OOD-HG1": {"status": "fail"}}
    decision = l1.derive_l1_ood_mechanism_verdict(
        _verdict_strata((0.4, 0.1), (0.08, -0.1), (0.07, -0.1), (0.07, -0.1)),
        gates,
    )
    assert decision["verdict"] in set(l1.L1OOD_VERDICTS)
    assert decision["diagnostic_confidence"] == "low"


def test_l1_ood_mechanism_probe_metrics_are_run_local_and_idempotent(tmp_path, capsys):
    config_args = [
        "--root",
        str(tmp_path),
        "--generated-at",
        "fixture-time",
        "--seeds",
        "1174,1175,1176,1177,1178,1179,1180,1181,1182,1183,1184,1185,1186,1187,1188,1189",
        "--training-steps",
        "8",
        "--step-grid",
        "8,16",
        "--train-examples",
        "64",
        "--eval-examples",
        "64",
    ]
    run_artifacts = l1.run_artifacts_payload()
    checked_paths = [
        tmp_path / run_artifacts["raw_metrics"],
        tmp_path / run_artifacts["probe_metrics"],
        tmp_path / l1.CANONICAL_JSON_ARTIFACT,
    ]

    assert runner.main(config_args) == 0
    first_summary = json.loads(capsys.readouterr().out)
    first = {path: path.read_bytes() for path in checked_paths}
    assert first_summary["l1_ood_mechanism_verdict"] in set(l1.L1OOD_VERDICTS)

    assert runner.main(config_args) == 0
    second_summary = json.loads(capsys.readouterr().out)
    second = {path: path.read_bytes() for path in checked_paths}

    assert first == second
    assert not (tmp_path / l1.CANONICAL_FINGERPRINT_ARTIFACT).exists()
    assert second_summary["l1_ood_mechanism_verdict"] == first_summary["l1_ood_mechanism_verdict"]
    raw_text = (tmp_path / run_artifacts["raw_metrics"]).read_text(encoding="utf-8")
    probe_text = (tmp_path / run_artifacts["probe_metrics"]).read_text(encoding="utf-8")
    assert "_probe_rows" not in raw_text
    assert "true_class_logit" in probe_text
    assert "true_class_margin" in probe_text


def test_l1_step_ladder_cpu_training_evidence_fail_closed():
    payload = _payload()
    assert payload["l1_step_ladder"]["hardgates"]["L1STEP-HG2"]["status"] == "pass"

    mutated = json.loads(json.dumps(payload))
    mutated["l1_step_ladder"]["per_step"][0]["training_arms"]["dgt_l1"]["device_resolved"] = "mps"
    _refresh_ladder_fail_closed(mutated, "L1STEP-HG2")

    mutated = json.loads(json.dumps(payload))
    metrics = mutated["l1_step_ladder"]["per_step"][0]["training_arms"]["dgt_l1"]["metrics"]
    metrics["loss_decrease_mean"] = 0.0
    metrics["parameter_l2_delta_mean"] = 0.0
    _refresh_ladder_fail_closed(mutated, "L1STEP-HG2")


def test_l1_step_ladder_compute_parameter_ledger_fail_closed():
    payload = _payload()
    assert payload["l1_step_ladder"]["hardgates"]["L1STEP-HG3"]["status"] == "pass"

    mutated = json.loads(json.dumps(payload))
    mutated["l1_step_ladder"]["per_step"][0]["compute_ledger"]["compute_units"] = 0.0
    _refresh_ladder_fail_closed(mutated, "L1STEP-HG3")

    mutated = json.loads(json.dumps(payload))
    mutated["l1_step_ladder"]["per_step"][0]["parameter_ledger"]["parameter_count"] = 0
    _refresh_ladder_fail_closed(mutated, "L1STEP-HG3")

    mutated = json.loads(json.dumps(payload))
    mutated["l1_step_ladder"]["per_step"][0].pop("compute_ledger")
    _refresh_ladder_fail_closed(mutated, "L1STEP-HG3")


def test_l1_step_ladder_crossover_derivation_fail_closed():
    payload = _payload()
    assert payload["l1_step_ladder"]["hardgates"]["L1STEP-HG4"]["status"] == "pass"

    mutated = json.loads(json.dumps(payload))
    mutated["l1_step_ladder"]["convergence_crossover"]["rows"][0]["information_starved_accuracy_mean"] = 1.0
    _refresh_ladder_fail_closed(mutated, "L1STEP-HG4")

    mutated = json.loads(json.dumps(payload))
    mutated["l1_step_ladder"]["step_rows"][0]["metrics"]["information_starved_accuracy_mean"] = (
        mutated["l1_step_ladder"]["step_rows"][0]["metrics"]["dgt_accuracy_mean"]
    )
    _refresh_ladder_fail_closed(mutated, "L1STEP-HG4")


def test_l1_step_ladder_crossover_uses_dgt_36_step_anchor_not_same_step_gap():
    rows = [
        {
            "training_steps": 36,
            "metrics": {
                "dgt_accuracy_mean": 0.8,
                "information_starved_accuracy_mean": 0.5,
                "matched_random_accuracy_mean": 0.4,
            },
        },
        {
            "training_steps": 72,
            "metrics": {
                "dgt_accuracy_mean": 0.95,
                "information_starved_accuracy_mean": 0.79,
                "matched_random_accuracy_mean": 0.4,
            },
        },
    ]
    crossover = l1.derive_l1_step_ladder_crossover(rows)
    gates = {gate_id: {"status": "pass"} for gate_id in l1.L1STEP_GATE_IDS}

    assert crossover["anchor_accuracy_mean"] == 0.8
    assert crossover["crossover_threshold_accuracy"] == 0.78
    assert crossover["information_starved_catches_up"] is True
    assert crossover["first_information_starved_crossover_step"] == 72
    assert crossover["rows"][1]["same_step_dgt_minus_information_starved_accuracy"] > l1.L1_CROSSOVER_TOLERANCE_ACC
    assert l1.derive_l1_step_ladder_verdict(crossover, gates) == "information-starved-catches-up"


def test_l1_step_ladder_verdict_table_branches():
    rows = [
        {
            "training_steps": 36,
            "metrics": {
                "dgt_accuracy_mean": 0.8,
                "information_starved_accuracy_mean": 0.5,
                "matched_random_accuracy_mean": 0.4,
            },
        }
    ]
    crossover = l1.derive_l1_step_ladder_crossover(rows)
    gates = {gate_id: {"status": "pass"} for gate_id in l1.L1STEP_GATE_IDS}
    assert l1.derive_l1_step_ladder_verdict(crossover, gates) == "scoped-review-signal"

    rows[0]["metrics"]["information_starved_accuracy_mean"] = 0.79
    crossover = l1.derive_l1_step_ladder_crossover(rows)
    assert l1.derive_l1_step_ladder_verdict(crossover, gates) == "information-starved-catches-up"

    rows[0]["metrics"]["matched_random_accuracy_mean"] = 0.79
    crossover = l1.derive_l1_step_ladder_crossover(rows)
    assert l1.derive_l1_step_ladder_verdict(crossover, gates) == "inconclusive"

    gates["L1STEP-HG1"] = {"status": "fail"}
    rows[0]["metrics"]["information_starved_accuracy_mean"] = 0.5
    rows[0]["metrics"]["matched_random_accuracy_mean"] = 0.4
    crossover = l1.derive_l1_step_ladder_crossover(rows)
    assert l1.derive_l1_step_ladder_verdict(crossover, gates) == "inconclusive"


def test_l1_step_ladder_matched_random_crossover_blocks_clean_result():
    payload = _payload()
    mutated = json.loads(json.dumps(payload))
    mutated["l1_step_ladder"]["step_rows"][0]["metrics"]["matched_random_accuracy_mean"] = (
        mutated["l1_step_ladder"]["step_rows"][0]["metrics"]["dgt_accuracy_mean"]
    )
    mutated["l1_step_ladder"]["convergence_crossover"] = l1.derive_l1_step_ladder_crossover(mutated["l1_step_ladder"]["step_rows"])
    mutated["l1_step_ladder"]["hardgates"] = l1.evaluate_l1step_hardgates(mutated["l1_step_ladder"])
    mutated["l1_step_ladder"]["status"] = "fail"
    mutated["l1_step_ladder"]["verdict"] = l1.derive_l1_step_ladder_verdict(
        mutated["l1_step_ladder"]["convergence_crossover"],
        mutated["l1_step_ladder"]["hardgates"],
    )

    assert mutated["l1_step_ladder"]["hardgates"]["L1STEP-HG5"]["status"] == "fail"
    assert mutated["l1_step_ladder"]["verdict"] == "inconclusive"
    mutated["hardgates"] = l1.evaluate_hardgates(mutated)
    with pytest.raises(ValueError, match="L1-REVIEW-HG6|hardgates fail closed"):
        l1.validate_payload(mutated)

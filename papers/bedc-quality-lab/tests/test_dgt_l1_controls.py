import json

import pytest

from bedc_quality_lab import dgt_l1_controls as l1
from bedc_quality_lab.discovery_compiler.pointers import resolve_artifact_pointer
from scripts import run_canonical_reports as canonical
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
        assert arm["metrics"]["validation_loss_mean"] > 0
        assert "FalseLedgerRate_mean" not in arm["metrics"]
        assert "JetCoverage_mean" not in arm["metrics"]
        assert "classifier_shift_count" not in arm["metrics"]
    ladder = payload["l1_step_ladder"]
    assert ladder["step_grid"] == [36, 72]
    assert len(ladder["step_rows"]) == 2
    assert all(step["training_arms"]["dgt_l1"]["device_resolved"] == "cpu" for step in ladder["per_step"])
    assert all("dgt_loss_decrease_mean" in step["metrics"] for step in ladder["step_rows"])
    assert all("dgt_validation_loss_mean" in step["metrics"] for step in ladder["step_rows"])
    assert all(
        step["training_arms"][arm_id]["metrics"]["validation_loss_mean"] > 0
        for step in ladder["per_step"]
        for arm_id in l1.ARM_IDS
    )

    mutated = json.loads(json.dumps(payload))
    mutated["training_arms"]["dgt_l1"]["training_steps"] = 0
    _expect_invalid(mutated, "optimizer steps")

    mutated = json.loads(json.dumps(payload))
    mutated["training_arms"]["dgt_l1"]["metrics"]["parameter_l2_delta_mean"] = 0
    _expect_invalid(mutated, "parameter update")

    mutated = json.loads(json.dumps(payload))
    mutated["training_arms"]["dgt_l1"]["metrics"].pop("validation_loss_mean")
    _expect_invalid(mutated, "required metric missing")

    mutated = json.loads(json.dumps(payload))
    mutated["training_arms"]["dgt_l1"]["metrics"]["validation_loss_mean"] = 0
    _expect_invalid(mutated, "validation_loss")


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
    mutated["training_arms"]["parameter_matched_attention"]["parameter_count"] *= 4
    mutated["hardgates"] = l1.evaluate_hardgates(mutated)
    _expect_invalid(mutated, "L1-REVIEW-HG5")

    mutated = json.loads(json.dumps(payload))
    mutated["training_arms"].pop("input_ablation_masked_tail")
    _expect_invalid(mutated, "training arms")


def test_l1_parameter_matched_attention_structural_control_fail_closed():
    payload = _payload()
    assert payload["hardgates"]["L1-REVIEW-HG2"]["status"] == "pass"
    assert payload["hardgates"]["L1-REVIEW-HG3"]["status"] == "pass"
    assert payload["hardgates"]["L1-REVIEW-HG4"]["status"] == "pass"
    assert payload["training_arms"]["input_ablation_masked_tail"]["role"] == "ablation"
    assert payload["training_arms"]["input_ablation_masked_tail"]["eligible_for_advantage_claims"] is False
    assert payload["training_arms"]["parameter_matched_attention"]["self_attention_layers"] == 1
    assert payload["training_arms"]["compute_matched_attention"]["self_attention_layers"] == 1

    mutated = json.loads(json.dumps(payload))
    mutated["training_arms"]["input_ablation_masked_tail"]["arm_id"] = "wrong"
    mutated["hardgates"] = l1.evaluate_hardgates(mutated)
    _expect_invalid(mutated, "L1-REVIEW-HG2")

    mutated = json.loads(json.dumps(payload))
    mutated["training_arms"]["parameter_matched_attention"]["self_attention_layers"] = 0
    mutated["hardgates"] = l1.evaluate_hardgates(mutated)
    _expect_invalid(mutated, "L1-REVIEW-HG3")

    mutated = json.loads(json.dumps(payload))
    mutated["training_arms"]["parameter_matched_attention"]["metrics"]["classifier_shift_count"] = 0
    mutated["hardgates"] = l1.evaluate_hardgates(mutated)
    _expect_invalid(mutated, "L1-REVIEW-HG4|owner-required metric")


def test_l1_construct_validity_ledger_records_input_and_split_protocol():
    payload = _payload()
    ledger = payload["construct_validity_ledger"]
    folded = payload["fair_l1_construction"]["construct_validity"]
    split = ledger["split_protocol"]
    bandwidth = ledger["input_bandwidth_by_arm"]

    assert ledger["status"] == "pass"
    assert folded["status"] == "construct-valid"
    assert folded["source_pointer"] == "reports/canonical/dgt-l1-controls.json:$.construct_validity_ledger"
    assert folded["folded_into_pointer"] == (
        "reports/canonical/dgt-l1-controls.json:$.fair_l1_construction.construct_validity"
    )
    assert folded["bayes_full_input_accuracy"] == 1.0
    assert split["heldout_pair_rule"] == "balanced_label_stratified_pairs_via_seeded_enumeration"
    assert split["pair_key"] == ["x_last_1", "x_last_2"]
    assert split["heldout_pair_count"] == 64
    assert split["train_pair_count"] == 192
    assert set(map(tuple, split["train_pairs"])).isdisjoint(set(map(tuple, split["heldout_pairs"])))
    assert {int(value) for value in split["heldout_label_histogram"].values()} == {4}
    assert {int(value) for value in split["train_label_histogram"].values()} == {12}
    assert set(bandwidth) == set(l1.ARM_IDS)
    assert all(row["input_positions"] == list(range(l1.SEQUENCE_LENGTH)) for row in bandwidth.values())
    assert bandwidth["input_ablation_masked_tail"]["masked_positions"] == [l1.SEQUENCE_LENGTH - 2]
    assert bandwidth["input_ablation_masked_tail"]["role"] == "ablation"

    mutated = json.loads(json.dumps(payload))
    mutated["construct_validity_ledger"]["split_protocol"]["heldout_pair_count"] = 63
    _expect_invalid(mutated, "construct validity ledger")


@pytest.mark.parametrize("masked_positions", ([], [0], [l1.SEQUENCE_LENGTH - 1]))
def test_l1_construct_validity_rejects_wrong_masked_tail_positions(masked_positions):
    payload = _payload()

    mutated = json.loads(json.dumps(payload))
    mutated["construct_validity_ledger"]["input_bandwidth_by_arm"]["input_ablation_masked_tail"]["masked_positions"] = masked_positions

    _expect_invalid(mutated, "construct validity ledger")


def test_l1_construct_validity_rejects_masked_tail_role_drift():
    payload = _payload()

    mutated = json.loads(json.dumps(payload))
    mutated["construct_validity_ledger"]["input_bandwidth_by_arm"]["input_ablation_masked_tail"]["role"] = "candidate"

    _expect_invalid(mutated, "construct validity ledger")


def test_l1_construct_validity_owner_projection_failure_is_rejected():
    payload = _payload()

    mutated = json.loads(json.dumps(payload))
    projection = mutated["construct_validity_ledger"]["construct_validity_projection"]
    projection["status"] = "fail"
    projection["failed_gates"] = ["CV-HG3"]
    projection["gates"]["CV-HG3"]["status"] = "fail"
    projection["gates"]["CV-HG3"]["reason"] = "synthetic owner failure"

    _expect_invalid(mutated, "owner projection")


def test_ablation_canonical_id_is_masked_tail_only():
    payload = _payload()

    assert "input_ablation_masked_tail" in payload["training_arms"]
    assert payload["training_arms"]["input_ablation_masked_tail"]["role"] == "ablation"
    assert payload["construct_validity_ledger"]["claim_comparison_policy"]["excluded_from_positive_claims"] == [
        "input_ablation_masked_tail",
        "diagnostic_step_ladder",
    ]


def test_retired_baseline_names_absent_from_canonical_payload():
    payload = _payload()
    text = json.dumps(payload, sort_keys=True)

    assert "base" + "_transformer_l1" not in text
    assert "input_ablation" + "_last_token_only" not in text


def test_split_protocol_uses_seeded_balanced_enumeration():
    split = _payload()["construct_validity_ledger"]["split_protocol"]

    assert split["heldout_pair_rule"] == "balanced_label_stratified_pairs_via_seeded_enumeration"
    assert split["seed"] == l1.HELDOUT_PAIR_SPLIT_SEED
    assert split["pair_key"] == ["x_last_1", "x_last_2"]


def test_pair_split_has_zero_train_eval_overlap():
    split = _payload()["construct_validity_ledger"]["split_protocol"]

    assert set(map(tuple, split["train_pairs"])).isdisjoint(set(map(tuple, split["heldout_pairs"])))


def test_heldout_pair_counts_and_label_histograms_are_balanced():
    split = _payload()["construct_validity_ledger"]["split_protocol"]

    assert split["heldout_pair_count"] == 64
    assert split["train_pair_count"] == 192
    assert len(split["heldout_label_histogram"]) == 16
    assert len(split["train_label_histogram"]) == 16
    assert set(split["heldout_label_histogram"].values()) == {4}
    assert set(split["train_label_histogram"].values()) == {12}


def test_split_fingerprint_is_stable_for_seed():
    first = _payload()["construct_validity_ledger"]["split_protocol"]
    second = _payload()["construct_validity_ledger"]["split_protocol"]

    assert first["train_pair_fingerprint"] == second["train_pair_fingerprint"]
    assert first["heldout_pair_fingerprint"] == second["heldout_pair_fingerprint"]
    assert first["all_pair_fingerprint"] == second["all_pair_fingerprint"]


def test_ood_same_rule_oracle_wins():
    ood = _payload()["construct_validity_ledger"]["ood_winnability"]

    assert ood["label_rule"] == "same_rule_heldout_pairs"
    assert ood["chance_accuracy"] == 0.0625
    assert ood["oracle_accuracy"] == 1.0


def test_ablation_and_diagnostic_step_ladder_are_excluded_from_claim_policy():
    policy = _payload()["construct_validity_ledger"]["claim_comparison_policy"]

    assert policy["eligible_positive_claim_controls"] == ["parameter_matched_attention", "compute_matched_attention"]
    assert "input_ablation_masked_tail" not in policy["eligible_positive_claim_controls"]
    assert "diagnostic_step_ladder" not in policy["eligible_positive_claim_controls"]


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
    assert {"model_claim", "allowed_claim", "forbidden_claims", "not_claimed"}.isdisjoint(capsule)
    assert {"allowed_claim", "forbidden_claims", "not_claimed"}.isdisjoint(capsule["claim_projection"])
    owner_projection = payload["construct_validity_ledger"]["construct_validity_projection"]
    owner_claim_projection = owner_projection["claim_capsule_projection"]
    assert capsule["construct_validity"] == {
        "artifact": owner_claim_projection["artifact"],
        "pointer": owner_claim_projection["pointer"],
        "status": owner_projection["status"],
        "failed_gates": owner_projection["failed_gates"],
        "owner_pointer": owner_projection["owner_pointer"],
    }
    assert capsule["claim_projection"]["allowed_claim_pointer"] == (
        l1.CANONICAL_JSON_ARTIFACT + ":$.l1_tiny_sequence_projection.review_status"
    )
    assert capsule["claim_projection"]["claim_boundary_pointer"] == l1.CANONICAL_JSON_ARTIFACT + ":$.not_claimed"
    assert all(pointer.startswith(l1.CANONICAL_JSON_ARTIFACT + ":$") for pointer in capsule["evidence_pointers"])

    mutated = json.loads(json.dumps(payload))
    mutated["claim_capsule_ref"]["evidence_scope"] = "production"
    _expect_invalid(mutated, "ClaimCapsule")

    mutated = json.loads(json.dumps(payload))
    mutated["claim_capsule_ref"]["evidence_pointers"][0] = "reports/canonical/missing.json:$.x"
    _expect_invalid(mutated, "ClaimCapsule")

    mutated = json.loads(json.dumps(payload))
    mutated["claim_capsule_ref"]["allowed_claim"] = l1.ALLOWED_CLAIM
    _expect_invalid(mutated, "ClaimCapsule")


def test_l1_review_status_pass_and_scoped_boundary():
    payload = _payload()
    assert payload["review_status"] == "pass"
    assert payload["promotion_readiness"] == "ready-pass"
    assert payload["hardgates"]["L1-REVIEW-HG7"]["status"] == "pass"
    assert payload["l1_tiny_sequence_projection"]["verdict"] == "scoped-boundary"
    assert payload["l1_tiny_sequence_projection"]["pass_scope"] == "in-dist order-2 only"
    assert payload["l1_tiny_sequence_projection"]["ood_generalization_claim"] == "not-claimed"
    assert payload["l1_tiny_sequence_projection"]["fair_l1_decision"] == (
        payload["fair_l1_construction"]["fair_l1_decision"]
    )
    assert payload["l1_tiny_sequence_projection"]["fair_l1_decision"]["standing_verdict"] == "bounded-negative"
    assert payload["l1_tiny_sequence_projection"]["fair_l1_decision"]["canonical_axis_action"] == "hold-current"

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
    assert summary["l1_step_ladder_verdict"] in {"diagnostic-only", "diagnostic-ablation-catches-up", "inconclusive"}
    assert summary["l1_step_ladder_crossover"] in {"diagnostic-crossover-observed", "no-diagnostic-crossover-observed"}
    assert summary["fair_l1_ood_survivor"] is False
    assert summary["fair_l1_standing_verdict"] == "bounded-negative"
    assert summary["fair_l1_canonical_axis_action"] == "hold-current"

    run_artifacts = l1.run_artifacts_payload()
    expected_artifacts = [
        l1.CANONICAL_JSON_ARTIFACT,
        l1.CANONICAL_MARKDOWN_ARTIFACT,
        run_artifacts["summary"],
        run_artifacts["probe_metrics"],
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
    assert "fair_l1_construction" in canonical_payload
    assert canonical_payload["l1_tiny_sequence_projection"]["fair_l1_decision"]["standing_verdict"] == "bounded-negative"
    claim_capsule = json.loads((tmp_path / run_artifacts["claim_capsule"]).read_text(encoding="utf-8"))
    assert claim_capsule == canonical_payload["claim_capsule_ref"]
    assert not (tmp_path / l1.CANONICAL_FINGERPRINT_ARTIFACT).exists()


def test_dgt_l1_controls_fingerprint_rejects_tampered_probe_metrics(tmp_path, monkeypatch):
    spec = next(row for row in canonical.CANONICAL_REPORTS if row.name == "dgt-l1-controls")
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    payload = _payload()
    l1.write_artifacts(payload, root=tmp_path, generated_at="fixture-time")
    fingerprint = canonical._write_fingerprint_sidecar(spec, generated_at="fixture-time")

    source_paths = {
        row["path"]
        for row in fingerprint["inputs"]["source_artifacts"]
    }
    assert l1.run_artifacts_payload()["probe_metrics"] in source_paths
    assert canonical._fingerprint_matches(spec) == (True, "match")

    probe_path = tmp_path / l1.run_artifacts_payload()["probe_metrics"]
    probe_path.write_text('{"tampered":true}\n', encoding="utf-8")

    assert canonical._fingerprint_matches(spec) == (False, "input-fingerprint")


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
    mutated["l1_step_ladder"]["per_step"][0]["training_arms"].pop("input_ablation_masked_tail")
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
        "heldout_pair": ood,
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
    mutated["l1_ood_mechanism"]["strata"]["heldout_pair"]["dgt_l1"]["true_class_logit_mean"] = "missing"
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
    mutated["l1_step_ladder"]["convergence_crossover"]["rows"][0]["input_ablation_accuracy_mean"] = 1.0
    _refresh_ladder_fail_closed(mutated, "L1STEP-HG4")

    mutated = json.loads(json.dumps(payload))
    mutated["l1_step_ladder"]["step_rows"][0]["metrics"]["input_ablation_accuracy_mean"] = (
        mutated["l1_step_ladder"]["step_rows"][0]["metrics"]["dgt_accuracy_mean"]
    )
    _refresh_ladder_fail_closed(mutated, "L1STEP-HG4")


def test_l1_step_ladder_crossover_uses_dgt_36_step_anchor_not_same_step_gap():
    rows = [
        {
            "training_steps": 36,
            "metrics": {
                "dgt_accuracy_mean": 0.8,
                "input_ablation_accuracy_mean": 0.5,
                "parameter_matched_attention_accuracy_mean": 0.4,
            },
        },
        {
            "training_steps": 72,
            "metrics": {
                "dgt_accuracy_mean": 0.95,
                "input_ablation_accuracy_mean": 0.79,
                "parameter_matched_attention_accuracy_mean": 0.4,
            },
        },
    ]
    crossover = l1.derive_l1_step_ladder_crossover(rows)
    gates = {gate_id: {"status": "pass"} for gate_id in l1.L1STEP_GATE_IDS}

    assert crossover["anchor_accuracy_mean"] == 0.8
    assert crossover["crossover_threshold_accuracy"] == 0.78
    assert crossover["input_ablation_catches_up"] is True
    assert crossover["first_input_ablation_crossover_step"] == 72
    assert crossover["rows"][1]["same_step_dgt_minus_input_ablation_accuracy"] > l1.L1_CROSSOVER_TOLERANCE_ACC
    assert l1.derive_l1_step_ladder_verdict(crossover, gates) == "diagnostic-ablation-catches-up"


def test_l1_step_ladder_verdict_table_branches():
    rows = [
        {
            "training_steps": 36,
            "metrics": {
                "dgt_accuracy_mean": 0.8,
                "input_ablation_accuracy_mean": 0.5,
                "parameter_matched_attention_accuracy_mean": 0.4,
            },
        }
    ]
    crossover = l1.derive_l1_step_ladder_crossover(rows)
    gates = {gate_id: {"status": "pass"} for gate_id in l1.L1STEP_GATE_IDS}
    assert l1.derive_l1_step_ladder_verdict(crossover, gates) == "diagnostic-only"

    rows[0]["metrics"]["input_ablation_accuracy_mean"] = 0.79
    crossover = l1.derive_l1_step_ladder_crossover(rows)
    assert l1.derive_l1_step_ladder_verdict(crossover, gates) == "diagnostic-ablation-catches-up"

    rows[0]["metrics"]["parameter_matched_attention_accuracy_mean"] = 0.79
    crossover = l1.derive_l1_step_ladder_crossover(rows)
    assert crossover["parameter_matched_attention_catches_up"] is True
    assert l1.derive_l1_step_ladder_verdict(crossover, gates) == "diagnostic-ablation-catches-up"

    gates["L1STEP-HG1"] = {"status": "fail"}
    rows[0]["metrics"]["input_ablation_accuracy_mean"] = 0.5
    rows[0]["metrics"]["parameter_matched_attention_accuracy_mean"] = 0.4
    crossover = l1.derive_l1_step_ladder_crossover(rows)
    assert l1.derive_l1_step_ladder_verdict(crossover, gates) == "inconclusive"


def test_l1_step_ladder_parameter_matched_attention_crossover_is_diagnostic_only():
    payload = _payload()
    mutated = json.loads(json.dumps(payload))
    mutated["l1_step_ladder"]["step_rows"][0]["metrics"]["parameter_matched_attention_accuracy_mean"] = (
        mutated["l1_step_ladder"]["step_rows"][0]["metrics"]["dgt_accuracy_mean"]
    )
    mutated["l1_step_ladder"]["convergence_crossover"] = l1.derive_l1_step_ladder_crossover(mutated["l1_step_ladder"]["step_rows"])
    mutated["l1_step_ladder"]["hardgates"] = l1.evaluate_l1step_hardgates(mutated["l1_step_ladder"])
    mutated["l1_step_ladder"]["status"] = "pass"
    mutated["l1_step_ladder"]["verdict"] = l1.derive_l1_step_ladder_verdict(
        mutated["l1_step_ladder"]["convergence_crossover"],
        mutated["l1_step_ladder"]["hardgates"],
    )

    assert mutated["l1_step_ladder"]["hardgates"]["L1STEP-HG5"]["status"] == "pass"
    assert mutated["l1_step_ladder"]["convergence_crossover"]["parameter_matched_attention_catches_up"] is True
    assert mutated["l1_step_ladder"]["verdict"] in {"diagnostic-only", "diagnostic-ablation-catches-up"}
    mutated["hardgates"] = l1.evaluate_hardgates(mutated)
    l1.validate_payload(mutated)

import json

import pytest

from bedc_quality_lab import dgt_l1_controls as l1
from bedc_quality_lab.discovery_compiler.pointers import resolve_artifact_pointer


def _payload():
    return l1.build_payload(generated_at="fixture-time", requested_device="cpu")


def _expect_invalid(payload, match):
    with pytest.raises(ValueError, match=match):
        l1.validate_payload(payload)


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

    mutated = json.loads(json.dumps(payload))
    mutated["training_arms"]["dgt_l1"]["training_steps"] = 0
    _expect_invalid(mutated, "optimizer steps")

    mutated = json.loads(json.dumps(payload))
    mutated["training_arms"]["dgt_l1"]["metrics"]["parameter_l2_delta_mean"] = 0
    _expect_invalid(mutated, "parameter update")


def test_l1_base_control_param_and_compute_matched():
    payload = _payload()
    assert payload["hardgates"]["L1-HG1"]["status"] == "pass"

    mutated = json.loads(json.dumps(payload))
    mutated["training_arms"]["base_transformer_l1"]["parameter_count"] *= 4
    mutated["hardgates"] = l1.evaluate_hardgates(mutated)
    _expect_invalid(mutated, "L1-HG1")

    mutated = json.loads(json.dumps(payload))
    mutated["training_arms"].pop("base_transformer_l1")
    _expect_invalid(mutated, "training arms")


def test_l1_matched_random_structural_control_fail_closed():
    payload = _payload()
    assert payload["hardgates"]["L1-HG2"]["status"] == "pass"

    mutated = json.loads(json.dumps(payload))
    mutated["training_arms"]["matched_random_structural_l1"]["metrics"]["accuracy_mean"] = payload["training_arms"]["dgt_l1"]["metrics"]["accuracy_mean"]
    mutated["hardgates"] = l1.evaluate_hardgates(mutated)
    _expect_invalid(mutated, "L1-HG2")

    mutated = json.loads(json.dumps(payload))
    mutated["training_arms"]["matched_random_structural_l1"]["structural_marginals_preserved"] = False
    mutated["hardgates"] = l1.evaluate_hardgates(mutated)
    _expect_invalid(mutated, "L1-HG2")


def test_l1_compute_and_parameter_ledgers_require_positive_values():
    payload = _payload()
    assert payload["hardgates"]["L1-HG3"]["status"] == "pass"
    assert payload["hardgates"]["L1-HG4"]["status"] == "pass"

    mutated = json.loads(json.dumps(payload))
    first_key = next(iter(mutated["compute_ledger"]["per_seed_step_cell"]))
    mutated["compute_ledger"]["per_seed_step_cell"][first_key]["compute_units"] = 0
    mutated["hardgates"] = l1.evaluate_hardgates(mutated)
    _expect_invalid(mutated, "L1-HG3")

    mutated = json.loads(json.dumps(payload))
    mutated["parameter_ledger"]["per_arm"]["dgt_l1"]["parameter_count"] = 0
    mutated["hardgates"] = l1.evaluate_hardgates(mutated)
    _expect_invalid(mutated, "L1-HG4")


def test_l1_negative_witness_sweep_uses_hit_logic():
    payload = _payload()
    sweep = payload["negative_witness_sweep"]
    assert sweep["status"] == "pass"
    assert {row["witness"] for row in sweep["witness_rows"]} == set(l1.REQUIRED_WITNESSES)
    assert all(row["hit_logic"] for row in sweep["witness_rows"])

    mutated = json.loads(json.dumps(payload))
    mutated["negative_witness_sweep"]["witness_rows"] = []
    mutated["hardgates"] = l1.evaluate_hardgates(mutated)
    _expect_invalid(mutated, "L1-HG5")

    mutated = json.loads(json.dumps(payload))
    mutated["negative_witness_sweep"]["witness_rows"][0]["regression_test_pointer_resolves"] = False
    mutated["hardgates"] = l1.evaluate_hardgates(mutated)
    _expect_invalid(mutated, "L1-HG5")


def test_l1_independent_replay_checks_digest_and_metric_tolerance():
    payload = _payload()
    replay = payload["independent_replay"]
    assert replay["status"] == "pass"
    assert replay["seed_count"] >= 8
    assert replay["task_spec_digest"]
    assert replay["seed_digest"]

    mutated = json.loads(json.dumps(payload))
    mutated["independent_replay"]["task_spec_digest"] = ""
    mutated["hardgates"] = l1.evaluate_hardgates(mutated)
    _expect_invalid(mutated, "L1-HG6")

    mutated = json.loads(json.dumps(payload))
    mutated["independent_replay"]["metric_tolerance_rows"][0]["status"] = "fail"
    mutated["hardgates"] = l1.evaluate_hardgates(mutated)
    _expect_invalid(mutated, "L1-HG6")


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
    mutated["hardgates"] = l1.evaluate_hardgates(mutated)
    _expect_invalid(mutated, "L1-HG7")

    mutated = json.loads(json.dumps(payload))
    mutated["claim_capsule_ref"]["evidence_pointers"][0] = "reports/canonical/missing.json:$.x"
    mutated["hardgates"] = l1.evaluate_hardgates(mutated)
    _expect_invalid(mutated, "L1-HG7")


def test_l1_review_status_ready_not_pass():
    payload = _payload()
    assert payload["review_status"] == "ready"
    assert payload["promotion_readiness"] == "ready-for-independent-review"
    assert payload["hardgates"]["L1-HG8"]["status"] == "pass"

    mutated = json.loads(json.dumps(payload))
    mutated["review_status"] = "pass"
    mutated["hardgates"] = l1.evaluate_hardgates(mutated)
    _expect_invalid(mutated, "review status")


def test_l1_component_ablation_reuses_measured_owner_without_component_effects():
    payload = _payload()
    boundary = payload["component_ablation_boundary"]
    assert boundary["owner_issue"] == "github:issue:1168"
    assert boundary["owner_artifact"] == "reports/canonical/dgt-neural-ablation.json"
    assert boundary["not_recreated_here"] is True
    assert "COMPONENT_EFFECTS" not in json.dumps(payload, sort_keys=True)

    mutated = json.loads(json.dumps(payload))
    mutated["component_ablation_boundary"]["not_recreated_here"] = False
    _expect_invalid(mutated, "component ablation")


def test_ladder_l1_pointer_only(tmp_path):
    payload = _payload()
    l1.write_artifacts(payload, root=tmp_path, generated_at="fixture-time")
    ladder = json.loads((tmp_path / l1.LADDER_JSON_ARTIFACT).read_text(encoding="utf-8"))

    assert ladder["levels"]["L1_tiny_sequence"]["pointer"] == "reports/canonical/dgt-l1-controls.json:$.l1_tiny_sequence_projection"
    assert "L1_tiny_sequence" in ladder["opened_levels"]
    serialized = json.dumps(ladder, sort_keys=True)
    for forbidden in ("accuracy_mean", "hardgates", "claim_capsule_ref", "discovery_map", "stable_causal_attribution"):
        assert forbidden not in serialized

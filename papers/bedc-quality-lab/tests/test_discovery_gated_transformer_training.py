import json
from pathlib import Path

from bedc_quality_lab.discovery_compiler.pointers import is_resolvable_artifact_pointer, pointer_value
from bedc_quality_lab.discovery_gated_transformer_training import (
    ARMS,
    CONTROL_FAMILIES,
    TRAINING_REPLAY_ARTIFACT,
    evaluate_training_hardgates,
    public_training_replay_ref,
)
from scripts import run_discovery_gated_transformer_training as runner


def _write_payload(tmp_path: Path) -> dict:
    payload = runner.build_payload(generated_at="2030-01-01T00:00:00+00:00")
    runner.write_artifacts(payload, root=tmp_path)
    return json.loads((tmp_path / payload["run_artifacts"]["training_replay"]).read_text(encoding="utf-8"))


def _walk_forbidden(value, forbidden):
    if isinstance(value, dict):
        for key, item in value.items():
            assert key not in forbidden
            _walk_forbidden(item, forbidden)
    elif isinstance(value, list):
        for item in value:
            _walk_forbidden(item, forbidden)
    elif isinstance(value, str):
        lowered = value.lower()
        for term in forbidden:
            assert term.lower() not in lowered


def test_replay_digest_is_deterministic_and_recomputed():
    first = runner.build_payload(generated_at="2030-01-01T00:00:00+00:00")
    second = runner.build_payload(generated_at="2030-01-01T00:00:00+00:00")

    assert first["replay_digest"] == second["replay_digest"]
    assert evaluate_training_hardgates(first)["TRAIN-HG1"]["status"] == "pass"


def test_exact_nine_arm_grid_and_committed_json_round_trip(tmp_path):
    payload = _write_payload(tmp_path)

    assert payload["run_artifacts"]["training_replay"] == TRAINING_REPLAY_ARTIFACT
    assert set(payload["config"]["arms"]) == set(ARMS)
    assert {row["arm_id"] for row in payload["records"]} == set(ARMS)
    assert len(payload["records"]) == len(ARMS) * len(payload["config"]["seeds"])
    assert evaluate_training_hardgates(payload) == payload["hardgates"]


def test_compute_ledger_has_one_row_per_arm_seed_and_resolving_pointers(tmp_path):
    payload = _write_payload(tmp_path)
    expected_pairs = {(arm, seed) for arm in ARMS for seed in payload["config"]["seeds"]}
    ledger_pairs = {(row["arm_id"], row["seed"]) for row in payload["compute_ledger"]["rows"]}

    assert ledger_pairs == expected_pairs
    assert payload["hardgates"]["TRAIN-HG2"]["status"] == "pass"
    for row in payload["compute_ledger"]["rows"]:
        assert pointer_value(payload, row["cost_protocol_pointer"]) is not None
        assert pointer_value(payload, row["raw_metric_pointer"]) is not None


def test_matched_random_is_not_loss_ablation():
    payload = runner.build_payload(generated_at="2030-01-01T00:00:00+00:00")

    assert CONTROL_FAMILIES["dgt_matched_random"] == "structural_random_control"
    assert payload["summary"]["control_families"]["dgt_matched_random"] == "structural_random_control"
    assert {
        payload["summary"]["control_families"][arm]
        for arm in ("dgt_no_discovery_loss", "dgt_no_ledger_loss", "dgt_no_certificate_loss")
    } == {"loss_ablation"}
    assert payload["hardgates"]["TRAIN-HG4"]["status"] == "pass"


def test_train_hg5_uer_comparison_passes_against_controls():
    payload = runner.build_payload(generated_at="2030-01-01T00:00:00+00:00")
    means = payload["summary"]["metric_means"]

    assert means["dgt_full"]["uer"] < means["task_only"]["uer"]
    assert means["dgt_full"]["uer"] < means["lat"]["uer"]
    assert means["dgt_full"]["uer"] < means["cga"]["uer"]
    assert means["dgt_full"]["uer"] < means["drt"]["uer"]
    assert means["dgt_full"]["uer"] < means["dgt_matched_random"]["uer"]
    assert payload["hardgates"]["TRAIN-HG5"]["status"] == "pass"


def test_train_hg6_false_ledger_rate_is_non_worse():
    payload = runner.build_payload(generated_at="2030-01-01T00:00:00+00:00")
    means = payload["summary"]["metric_means"]

    assert means["dgt_full"]["false_ledger_rate"] <= means["task_only"]["false_ledger_rate"]
    assert means["dgt_full"]["false_ledger_rate"] <= means["dgt_matched_random"]["false_ledger_rate"]
    assert payload["hardgates"]["TRAIN-HG6"]["status"] == "pass"


def test_train_hg7_benefit_and_debt_direction():
    payload = runner.build_payload(generated_at="2030-01-01T00:00:00+00:00")
    means = payload["summary"]["metric_means"]

    assert means["dgt_full"]["benefit"] >= means["task_only"]["benefit"]
    assert means["dgt_full"]["benefit"] >= means["dgt_matched_random"]["benefit"]
    assert means["dgt_full"]["debt"] < means["task_only"]["debt"]
    assert means["dgt_full"]["debt"] < means["dgt_matched_random"]["debt"]
    assert payload["hardgates"]["TRAIN-HG7"]["status"] == "pass"


def test_train_hg8_classifier_shift_pointer_is_positive():
    payload = runner.build_payload(generated_at="2030-01-01T00:00:00+00:00")
    pointer = payload["hardgates"]["TRAIN-HG8"]["evidence_pointer"]

    assert pointer_value(payload, pointer) > 0
    assert payload["hardgates"]["TRAIN-HG8"]["status"] == "pass"


def test_train_hg9_sidecar_pointers_resolve_after_write(tmp_path):
    payload = _write_payload(tmp_path)

    assert payload["hardgates"]["TRAIN-HG9"]["status"] == "pass"
    for key in ("claim_capsule", "evidence_envelope", "cost_protocol", "not_claimed"):
        pointer = payload["sidecar_pointers"][key]
        assert is_resolvable_artifact_pointer(tmp_path, pointer)


def test_train_hg10_forbidden_keys_and_public_ref_are_pointer_only(tmp_path):
    payload = _write_payload(tmp_path)
    summary = json.loads((tmp_path / payload["run_artifacts"]["summary"]).read_text(encoding="utf-8"))

    _walk_forbidden(payload, {"terminal_verdict", "host.env", ".refactor-loop", "DGT-v0", "issue-", "route-a"})
    _walk_forbidden(summary, {"terminal_verdict", "host.env", ".refactor-loop", "DGT-v0", "issue-", "route-a"})
    assert public_training_replay_ref(payload) == {
        "artifact": payload["run_artifacts"]["training_replay"],
        "pointer": "$",
    }
    assert set(summary["training_replay_ref"]) == {"artifact", "pointer"}
    assert "records" not in summary
    assert "compute_ledger" not in summary
    assert payload["hardgates"]["TRAIN-HG10"]["status"] == "pass"

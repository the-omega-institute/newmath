import copy
import json

from bedc_quality_lab.discovery_compiler.pointers import pointer_value
from bedc_quality_lab.order_k_benchmark import (
    ARTIFACT_ID,
    LEDGER_VIEW_SCHEMA_ID,
    SCHEMA_ID,
    OrderKBenchmarkProjection,
)
from scripts import run_order_k_benchmark as runner


def _payload():
    return OrderKBenchmarkProjection.project(generated_at="2030-01-01T00:00:00+00:00", seed=1004)


def _assert_failed_hardgate(payload, failed_gate):
    verdict = OrderKBenchmarkProjection.hardgate_verdicts(payload)

    assert verdict["status"] == "fail"
    assert verdict["failed_gate"] == failed_gate
    assert verdict["gates"][failed_gate]["status"] == "fail"


def test_deterministic_replay_and_single_task_spec_owner():
    left = _payload()
    right = _payload()

    assert left == right
    assert left["schema_id"] == SCHEMA_ID
    assert left["artifact_id"] == ARTIFACT_ID
    assert left["task_spec_owner"]["status"] == "single-owner"
    assert left["source_artifacts"]["task_spec_owner"].endswith("OrderKBenchmarkProjection.default_specs")


def test_b1_is_solved_by_order_one():
    summary = _payload()["minimal_order_summary"]["by_task"]["B1"]

    assert summary["status"] == "pass"
    assert summary["required_order"] == 1
    assert summary["minimal_sufficient_order"] == 1


def test_b2_d2_positive_and_matched_random_non_positive():
    payload = _payload()
    b2 = payload["minimal_order_summary"]["by_task"]["B2"]
    control = next(row for row in payload["matched_random_controls"] if row["task_id"] == "B2")

    assert b2["minimal_sufficient_order"] == 2
    assert b2["status"] == "pass"
    assert control["order"] == 2
    assert control["positive"] is False
    assert control["status"] == "non-positive"


def test_b3_lower_orders_fail_and_shuffle_removes_classifier_shift():
    rows = [row for row in _payload()["order_rows"] if row["task_id"] == "B3"]
    lower_rows = [row for row in rows if row["order"] < 3]

    assert lower_rows
    assert all(row["positive"] is False for row in lower_rows)
    assert all(row["classifier_shift_count"] == 1 for row in lower_rows)
    assert all(row["shuffle_control_classifier_shift_count"] == 0 for row in lower_rows)


def test_b4_declares_and_detects_required_order_at_least_four():
    payload = _payload()
    spec = next(row for row in payload["task_specs"] if row["task_id"] == "B4")
    summary = payload["minimal_order_summary"]["by_task"]["B4"]

    assert spec["required_order"] >= 4
    assert summary["minimal_sufficient_order"] >= 4
    assert summary["minimal_sufficient_order"] == spec["required_order"]


def test_ood_true_order_passes_and_lower_order_fails():
    rows = _payload()["ood_stability"]["rows"]

    assert rows
    assert all(row["true_order_status"] == "pass" for row in rows)
    assert all(row["lower_order_status"] == "fail" for row in rows)


def test_margin_entropy_proxy_is_not_an_explanation():
    proxy = _payload()["margin_entropy_proxy_check"]

    assert proxy["status"] == "pass"
    assert all(row["explains_required_order"] is False for row in proxy["rows"])
    assert proxy["max_abs_margin_delta"] < 0.02
    assert proxy["max_abs_entropy_delta"] < 0.01


def test_embedded_ledger_pointer_resolves_without_standalone_owner():
    payload = _payload()
    ref = payload["surface_required_order_ledger_ref"]
    artifact, pointer = ref["artifact_pointer"].split(":", 1)

    assert artifact == "reports/canonical/order-k-benchmark.json"
    assert pointer_value(payload, pointer) == payload["surface_required_order_ledger"]["rows"]
    assert payload["surface_required_order_ledger"]["schema_id"] == LEDGER_VIEW_SCHEMA_ID
    assert payload["surface_required_order_ledger"]["artifact_id"] is None


def test_hardgate_mutation_demotes_without_deleting_raw_evidence():
    payload = _payload()
    mutated = OrderKBenchmarkProjection.demote_for_hardgate_mutation(
        payload,
        failed_gate="OK-HG2-minimal-order-detected",
    )

    assert payload["hardgate"]["status"] == "pass"
    assert mutated["hardgate"]["status"] == "fail"
    assert mutated["discovery_map_signal"]["status"] == "demoted"
    assert mutated["order_rows"] == payload["order_rows"]
    assert mutated["matched_random_controls"] == payload["matched_random_controls"]
    assert mutated["ood_stability"] == payload["ood_stability"]


def test_hardgate_fails_closed_without_single_task_spec_owner():
    payload = copy.deepcopy(_payload())
    payload["task_spec_owner"]["status"] = "multi-owner"

    _assert_failed_hardgate(payload, "OK-HG1-task-spec-single-owner")


def test_hardgate_fails_closed_without_detected_minimal_orders():
    payload = copy.deepcopy(_payload())
    payload["minimal_order_summary"]["all_detected"] = False

    _assert_failed_hardgate(payload, "OK-HG2-minimal-order-detected")


def test_hardgate_fails_closed_without_matched_random_negative_controls():
    payload = copy.deepcopy(_payload())
    payload["matched_random_controls"] = []

    _assert_failed_hardgate(payload, "OK-HG3-matched-random-negative")


def test_hardgate_fails_closed_for_positive_matched_random_control():
    payload = copy.deepcopy(_payload())
    payload["matched_random_controls"][0]["positive"] = True
    payload["matched_random_controls"][0]["status"] = "positive"

    _assert_failed_hardgate(payload, "OK-HG3-matched-random-negative")


def test_hardgate_fails_closed_for_failed_ood_stability():
    payload = copy.deepcopy(_payload())
    payload["ood_stability"]["status"] = "fail"

    _assert_failed_hardgate(payload, "OK-HG4-ood-stability")


def test_hardgate_fails_closed_for_failed_proxy_check():
    payload = copy.deepcopy(_payload())
    payload["margin_entropy_proxy_check"]["status"] = "fail"

    _assert_failed_hardgate(payload, "OK-HG5-proxy-non-explanation")


def test_hardgate_fails_closed_for_forbidden_claim_terms():
    payload = copy.deepcopy(_payload())
    payload["positive_claim"]["text"] = "global-superiority"

    _assert_failed_hardgate(payload, "OK-HG6-forbidden-claim-audit")


def test_forbidden_recursive_verdict_and_global_superiority_terms_absent():
    payload = _payload()
    serialized = json.dumps(payload, sort_keys=True).lower()

    assert payload["forbidden_claim_term_audit"]["status"] == "pass"
    assert "terminal_verdict" not in serialized
    assert "global-superiority" not in serialized
    assert "global superiority" not in serialized


def test_runner_markdown_is_pointer_only_for_formulas_and_orders():
    payload = _payload()
    markdown = runner.render_markdown(payload)
    formulas = {row["formula"] for row in payload["task_specs"]}
    required_orders = {str(row["required_order"]) for row in payload["task_specs"]}

    assert "reports/canonical/order-k-benchmark.json:$.surface_required_order_ledger.rows" in markdown
    assert not any(formula in markdown for formula in formulas)
    assert not any(f"required_order: {order}" in markdown for order in required_orders)


def test_forbidden_audit_fails_closed_on_mutation():
    payload = copy.deepcopy(_payload())
    payload["positive_claim"]["text"] = "global-superiority"

    audit = OrderKBenchmarkProjection.assert_no_forbidden_claim_terms(payload)

    assert audit["status"] == "fail"
    assert "global-superiority" in audit["hits"]


def test_public_writer_writes_order_k_json_and_markdown_artifacts(tmp_path):
    generated_at = "2031-02-03T04:05:06+00:00"
    seed = 4404

    payload = runner.write_order_k_benchmark(root=tmp_path, generated_at=generated_at, seed=seed)
    json_path = tmp_path / runner.JSON_ARTIFACT
    markdown_path = tmp_path / runner.REPORT_ARTIFACT
    written_payload = json.loads(json_path.read_text(encoding="utf-8"))
    markdown = markdown_path.read_text(encoding="utf-8")

    assert payload == written_payload
    assert written_payload["generated_at"] == generated_at
    assert written_payload["seed"] == seed
    assert written_payload["hardgate"]["status"] == "pass"
    assert f"- Generated at: `{generated_at}`" in markdown
    assert f"- HardGate verdicts: `{runner.JSON_ARTIFACT}:$.hardgate`" in markdown

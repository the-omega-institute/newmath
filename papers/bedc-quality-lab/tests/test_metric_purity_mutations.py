import json
from pathlib import Path

from bedc_quality_lab import metric_purity


def test_registered_hardgate_mutations_fail_through_owner_contract():
    cases = metric_purity.iter_registered_hardgate_mutations(Path.cwd())

    assert cases
    for case in cases:
        result = metric_purity.evaluate_hardgate_mutation(Path.cwd(), case)
        assert result["status"] == "pass"
        assert result["failed_gate"] == case.expected_failed_gate


def test_new_hardgate_without_mutation_row_is_mut_hg1(tmp_path):
    target = {
        "id": "fixture-hardgate",
        "kind": "hardgate",
        "module": "bedc_quality_lab.order_k_benchmark",
        "callable": "OrderKBenchmarkProjection.hardgate_verdicts",
        "owner_pointer": "bedc_quality_lab/order_k_benchmark.py:OrderKBenchmarkProjection.hardgate_verdicts",
        "report_artifact": "reports/canonical/order-k-benchmark.json",
        "evidence_pointer": "reports/canonical/order-k-benchmark.json:$.hardgate",
        "empirical_metric_keys": [],
        "mutation_contract_refs": ["fixture-hardgate"],
        "allowlist_refs": [],
    }
    targets_path = tmp_path / "targets.json"
    allowlist_path = tmp_path / "allowlist.json"
    targets_path.write_text(
        json.dumps({"schema_id": metric_purity.TARGETS_SCHEMA_ID, "targets": [target], "hardgate_mutations": []}) + "\n",
        encoding="utf-8",
    )
    allowlist_path.write_text(json.dumps({"schema_id": metric_purity.ALLOWLIST_SCHEMA_ID, "rows": []}) + "\n", encoding="utf-8")

    payload = metric_purity.run_metric_purity_audit(Path.cwd(), targets_path, allowlist_path)

    assert payload["status"] == "fail"
    assert any(finding["code"] == "MUT-HG1" for finding in payload["findings"])


def test_mutation_output_must_match_expected_gate_and_reason(tmp_path):
    case = metric_purity.iter_registered_hardgate_mutations(Path.cwd())[0]
    wrong = metric_purity.HardgateMutationCase(
        gate_id=case.gate_id,
        mutation_id="wrong-expected-gate",
        owner_pointer=case.owner_pointer,
        apply=case.apply,
        expected_failed_gate="different-gate",
        expected_reason_regex=case.expected_reason_regex,
        source_payload_pointer=case.source_payload_pointer,
    )

    result = metric_purity.evaluate_hardgate_mutation(Path.cwd(), wrong)

    assert result["status"] == "fail"
    assert result["code"] == "MUT-HG4"


def test_registered_mutation_iterator_is_deterministic():
    first = metric_purity.iter_registered_hardgate_mutations(Path.cwd())
    second = metric_purity.iter_registered_hardgate_mutations(Path.cwd())

    assert first == second

import json
from pathlib import Path

import pytest

from scripts import run_canonical_reports as canonical
from scripts import run_discovery_map as discovery_map


def _write_payload(root: Path, spec, payload):
    path = root / spec.json_artifact
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload) + "\n", encoding="utf-8")


def _minimal_payload(spec):
    payload = {key: f"fixture-{key}" for key in spec.required_json_keys}
    if spec.name == "gap-head-on-h":
        payload.update({
            "treatment_verdict": {"positive": True},
            "control_protocol": {"same_budget_as_treatment": True},
            "control_verdict": {"positive": False},
        })
        return payload
    if spec.name == "gap-head-discovery":
        payload.update({
            "positive_discovery": True,
            "matched_random_control": {
                "control_verdict": {"positive": False},
                "control_projection": {"positive_discovery": True},
            },
        })
        return payload
    if spec.name == "gap-head-ablation":
        payload.update({"hardgate": {"status": "fail", "gates": {"learned_head": {"status": "pass"}}}})
        return payload
    if spec.name == "spectral-ablation-hinge":
        payload.update({
            "ledger_summary": {"status": "negative"},
            "negative_control_summary": {"treatment_better_than_all_controls": False},
        })
        return payload
    if spec.name == "certificate-guided-training":
        payload.update({
            "result": {"status": "negative"},
            "deltas": {"after_minus_before": {"debt_delta": -0.25}},
            "claim_gate": {"audit_improvement_tradeoff": True},
        })
        return payload
    if spec.name == "certificate-guided-discovery":
        payload.update({
            "main_claim_status": "observed-negative",
            "positive_discovery": False,
            "verdicts": [{"deltas": {"debt_delta": -0.25}}],
            "claim_gate": {"training_audit_improvement_tradeoff": True},
        })
        return payload
    if spec.name == "anisotropic-ou-sweep":
        payload.update({"transition_debt_by_grid": {"cell": {"status": "open-or-partial"}}})
        return payload
    if spec.name == "nongaussian-distribution-sweep":
        payload.update({
            "negative_result_ledger": [{"status": "negative"}],
            "coverage_item": {"debt_item": {"status": "open"}},
        })
        return payload
    if spec.name == "mixing-family-sweep":
        payload.update({"coverage_item": {"debt_item": {"status": "open"}}})
        return payload
    return payload


def _write_all_payloads(root: Path):
    for spec in canonical.CANONICAL_REPORTS:
        _write_payload(root, spec, _minimal_payload(spec))


def _row_by_report(payload):
    return {row["report"]: row for row in payload["rows"]}


def test_discovery_map_has_one_row_per_canonical_report(tmp_path):
    _write_all_payloads(tmp_path)

    payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)

    assert [row["report"] for row in payload["rows"]] == [spec.name for spec in canonical.CANONICAL_REPORTS]
    assert payload["row_count"] == len(canonical.CANONICAL_REPORTS)
    assert all(row["discovery_level"] in discovery_map.DISCOVERY_LEVELS for row in payload["rows"])


@pytest.mark.parametrize("report", ["gap-head-on-h", "gap-head-discovery"])
def test_d4_rows_have_resolvable_control_pointer(tmp_path, report):
    spec = canonical._specs_by_name()[report]
    payload = _minimal_payload(spec)
    projected = discovery_map.projection_payload(spec, payload)
    evidence = discovery_map._projection_evidence(spec, payload)
    verdict = discovery_map.assign_discovery_level(projected)

    assert verdict.discovery_level == "D4"
    assert evidence.control_pointer
    assert discovery_map.pointer_value(payload, evidence.control_pointer) is not None


@pytest.mark.parametrize(
    ("report", "expected_pointer"),
    [
        ("certificate-guided-training", "$.result.status"),
        ("certificate-guided-discovery", "$.positive_discovery"),
        ("gap-head-ablation", "$.hardgate.status"),
        ("spectral-ablation-hinge", "$.negative_control_summary.treatment_better_than_all_controls"),
    ],
)
def test_dn_rows_have_failed_gate_pointing_to_negative_cell(tmp_path, report, expected_pointer):
    spec = canonical._specs_by_name()[report]
    payload = _minimal_payload(spec)
    projected = discovery_map.projection_payload(spec, payload)
    evidence = discovery_map._projection_evidence(spec, payload)
    verdict = discovery_map.assign_discovery_level(projected)

    assert verdict.discovery_level == "DN"
    assert evidence.failed_gate == expected_pointer
    assert discovery_map.pointer_value(payload, expected_pointer) is not None


@pytest.mark.parametrize(
    ("report", "expected_pointer"),
    [
        ("mixing-family-sweep", "$.coverage_item.debt_item"),
        ("anisotropic-ou-sweep", "$.transition_debt_by_grid"),
        ("nongaussian-distribution-sweep", "$.negative_result_ledger"),
    ],
)
def test_d1_rows_have_debt_row_pointer_to_real_evidence(tmp_path, report, expected_pointer):
    spec = canonical._specs_by_name()[report]
    payload = _minimal_payload(spec)
    projected = discovery_map.projection_payload(spec, payload)
    evidence = discovery_map._projection_evidence(spec, payload)
    verdict = discovery_map.assign_discovery_level(projected)

    assert verdict.discovery_level == "D1"
    assert evidence.debt_row_pointer == expected_pointer
    assert discovery_map.pointer_value(payload, expected_pointer) is not None


def test_run_reports_index_contains_discovery_map(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    monkeypatch.setattr(canonical, "INDEX_ARTIFACT", tmp_path / "reports" / "canonical" / "index.json")

    def fake_run_producer(spec):
        _write_payload(tmp_path, spec, _minimal_payload(spec))
        markdown = tmp_path / spec.markdown_artifact
        markdown.write_text("# fixture\n", encoding="utf-8")

    monkeypatch.setattr(canonical, "_run_producer", fake_run_producer)

    payload = canonical.run_reports(generated_at="2026-01-02T03:04:05+00:00")

    assert payload["discovery_map"]["json_artifact"] == "reports/canonical/discovery_map.json"
    assert payload["discovery_map"]["markdown_artifact"] == "reports/canonical/discovery_map.md"
    assert (tmp_path / "reports" / "canonical" / "discovery_map.json").exists()
    assert (tmp_path / "reports" / "canonical" / "discovery_map.md").exists()


def test_strict_manifest_audit_marks_missing_control_invalid(tmp_path):
    spec = canonical._specs_by_name()["gap-head-on-h"]
    payload = {"treatment_verdict": {"positive": True}, "control_verdict": {"positive": False}}
    row = discovery_map.discovery_row(spec, payload)

    assert row["discovery_level"] == "D4"
    assert row["audit_status"] == "invalid"
    assert row["audit_reason"] == "unresolved-control-pointer"

    _write_all_payloads(tmp_path)
    _write_payload(tmp_path, spec, payload)
    discovery_map.write_discovery_map(root=tmp_path, generated_at="fixture-time")
    with pytest.raises(SystemExit):
        old_root = discovery_map.ROOT
        try:
            discovery_map.ROOT = tmp_path
            discovery_map.main(["--strict-manifest-audit"])
        finally:
            discovery_map.ROOT = old_root

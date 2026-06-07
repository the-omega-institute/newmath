from __future__ import annotations

import copy
import json
from pathlib import Path

from scripts import run_toy_safety_backend as backend


ROOT = Path(__file__).resolve().parents[1]


def _load_json(root: Path, artifact: str):
    return json.loads((root / artifact).read_text(encoding="utf-8"))


def _load_jsonl(root: Path, artifact: str):
    return [json.loads(line) for line in (root / artifact).read_text(encoding="utf-8").splitlines()]


def _write_fixture(root: Path, *, cases=None, omit_metrics=()):
    backend.write_artifacts(root=root, cases=cases, omit_metrics=omit_metrics)
    assert backend.validate_artifacts(root)["status"] == "pass"
    return {
        "cases": _load_jsonl(root, backend.RAW_CASES_ARTIFACT),
        "metrics": _load_json(root, backend.RAW_METRICS_ARTIFACT),
        "summary": _load_json(root, backend.SUMMARY_ARTIFACT),
        "capsule": _load_json(root, backend.CLAIM_CAPSULE_ARTIFACT),
    }


def _canonical_bytes(payload):
    return json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")


def _with_decision(cases, case_id: str, decision: str):
    mutated = copy.deepcopy(cases)
    for row in mutated:
        if row["case_id"] == case_id:
            row["decision"] = decision
            return mutated
    raise AssertionError(f"{case_id} not found")


def test_schema_has_three_label_classes_and_owned_denominators(tmp_path):
    payload = _write_fixture(tmp_path)
    cases = payload["cases"]
    raw_metrics = payload["metrics"]
    summary = payload["summary"]

    assert {row["label"] for row in cases} == {"allowed", "disallowed", "ambiguous"}
    assert all(row["decision"] in {"allow", "refuse", "defer"} for row in cases)
    assert all(row["expected_decision_set"] for row in cases)
    assert all(row.get("ledger_ref") or row.get("ambiguous_log_ref") for row in cases)
    assert all(row.get("ambiguous_log_ref") for row in cases if row["label"] == "ambiguous")
    assert raw_metrics["case_count"] == len(cases)
    assert raw_metrics["source_case_table"] == backend.RAW_CASES_ARTIFACT
    assert raw_metrics["label_denominators"] == {
        label: sum(1 for row in cases if row["label"] == label)
        for label in ("allowed", "disallowed", "ambiguous")
    }
    assert summary["hardgates"]["TS-HG1"]["status"] == "pass"


def test_build_artifacts_is_pure_no_disk_state_dependency(tmp_path):
    fresh = backend.build_artifacts(root=tmp_path)
    fresh_bytes = _canonical_bytes(
        {
            "claim_capsule": fresh["claim_capsule"],
            "hardgates": fresh["summary"]["hardgates"],
            "raw_cases": fresh["raw_cases"],
            "raw_metrics": fresh["raw_metrics"],
            "safety_claim_gate": fresh["summary"]["safety_claim_gate"],
        }
    )

    raw_cases_path = tmp_path / backend.RAW_CASES_ARTIFACT
    raw_cases_path.parent.mkdir(parents=True, exist_ok=True)
    raw_cases_path.write_text(
        json.dumps(
            {
                "case_id": "toy-safety-disallowed-001",
                "label": "disallowed",
                "decision": "allow",
                "expected_decision_set": ["refuse"],
            },
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )
    polluted = backend.build_artifacts(root=tmp_path)
    assert _canonical_bytes(
        {
            "claim_capsule": polluted["claim_capsule"],
            "hardgates": polluted["summary"]["hardgates"],
            "raw_cases": polluted["raw_cases"],
            "raw_metrics": polluted["raw_metrics"],
            "safety_claim_gate": polluted["summary"]["safety_claim_gate"],
        }
    ) == fresh_bytes

    raw_cases_path.unlink()
    deleted = backend.build_artifacts(root=tmp_path)
    assert _canonical_bytes(
        {
            "claim_capsule": deleted["claim_capsule"],
            "hardgates": deleted["summary"]["hardgates"],
            "raw_cases": deleted["raw_cases"],
            "raw_metrics": deleted["raw_metrics"],
            "safety_claim_gate": deleted["summary"]["safety_claim_gate"],
        }
    ) == fresh_bytes


def test_write_artifacts_single_pass(monkeypatch, tmp_path):
    calls = 0
    original = backend.build_artifacts

    def spy_build_artifacts(*, root=backend.ROOT, cases=None, omit_metrics=()):
        nonlocal calls
        calls += 1
        return original(root=root, cases=cases, omit_metrics=omit_metrics)

    monkeypatch.setattr(backend, "build_artifacts", spy_build_artifacts)
    artifacts = backend.write_artifacts(root=tmp_path)

    assert calls == 1
    assert artifacts["summary"]["safety_claim_gate"]["claim_status"] == "claimed"
    assert backend.validate_artifacts(tmp_path)["status"] == "pass"


def test_hardgate_requires_unsafe_false_negative_and_over_refusal_metric_cells(tmp_path):
    payload = _write_fixture(tmp_path)
    raw_metrics = payload["metrics"]
    summary = payload["summary"]

    for metric, gate, label in (
        ("unsafe_false_negative", "TS-HG2", "disallowed"),
        ("over_refusal", "TS-HG3", "allowed"),
    ):
        cell = raw_metrics["metrics"][metric]
        assert set(cell) == {"count", "denominator", "rate", "source_case_pointer"}
        assert backend.resolve_pointer(tmp_path, f"{backend.RAW_METRICS_ARTIFACT}:$.metrics.{metric}") == cell
        source_row = backend.resolve_pointer(tmp_path, cell["source_case_pointer"])
        assert source_row["label"] == label
        assert summary["hardgates"][gate]["status"] == "pass"

    missing = backend.build_artifacts(root=tmp_path, omit_metrics=("unsafe_false_negative",))
    assert missing["summary"]["hardgates"]["TS-HG2"]["status"] == "fail"
    assert missing["summary"]["safety_claim_gate"]["claim_status"] == "not_claimed"

    missing = backend.build_artifacts(root=tmp_path, omit_metrics=("over_refusal",))
    assert missing["summary"]["hardgates"]["TS-HG3"]["status"] == "fail"
    assert missing["summary"]["safety_claim_gate"]["claim_status"] == "not_claimed"


def test_nonzero_unsafe_false_negative_downgrades_positive_claim(tmp_path):
    payload = _write_fixture(tmp_path)
    cases = _with_decision(payload["cases"], "toy-safety-disallowed-001", "allow")
    artifacts = _write_fixture(tmp_path, cases=cases)
    raw_metrics = artifacts["metrics"]
    summary = artifacts["summary"]
    gate = summary["safety_claim_gate"]
    cell = raw_metrics["metrics"]["unsafe_false_negative"]

    assert cell["count"] == 1
    assert raw_metrics["metrics"]["over_refusal"]["count"] == 0
    assert raw_metrics["metrics"]["ambiguous_unlogged_error"]["count"] == 0
    assert set(raw_metrics["metrics"]) == set(backend.METRICS)
    assert set(cell) == {"count", "denominator", "rate", "source_case_pointer"}
    assert backend.resolve_pointer(tmp_path, f"{backend.RAW_METRICS_ARTIFACT}:$.metrics.unsafe_false_negative") == cell
    assert backend.resolve_pointer(tmp_path, cell["source_case_pointer"])["label"] == "disallowed"
    assert all(summary["hardgates"][gate_name]["status"] == "pass" for gate_name in backend.HARDGATES)
    assert gate["required_metric_cells_present"] is True
    assert gate["zero_required_error_counts"] is False
    assert gate["status"] == "fail"
    assert gate["claim_status"] == "not_claimed"
    assert artifacts["capsule"]["claim_status"] == "not_claimed"


def test_nonzero_over_refusal_downgrades_positive_claim(tmp_path):
    payload = _write_fixture(tmp_path)
    cases = _with_decision(payload["cases"], "toy-safety-allowed-001", "refuse")
    artifacts = _write_fixture(tmp_path, cases=cases)
    raw_metrics = artifacts["metrics"]
    summary = artifacts["summary"]
    gate = summary["safety_claim_gate"]
    cell = raw_metrics["metrics"]["over_refusal"]

    assert cell["count"] == 1
    assert raw_metrics["metrics"]["unsafe_false_negative"]["count"] == 0
    assert raw_metrics["metrics"]["ambiguous_unlogged_error"]["count"] == 0
    assert set(raw_metrics["metrics"]) == set(backend.METRICS)
    assert set(cell) == {"count", "denominator", "rate", "source_case_pointer"}
    assert backend.resolve_pointer(tmp_path, f"{backend.RAW_METRICS_ARTIFACT}:$.metrics.over_refusal") == cell
    assert backend.resolve_pointer(tmp_path, cell["source_case_pointer"])["label"] == "allowed"
    assert all(summary["hardgates"][gate_name]["status"] == "pass" for gate_name in backend.HARDGATES)
    assert gate["required_metric_cells_present"] is True
    assert gate["zero_required_error_counts"] is False
    assert gate["status"] == "fail"
    assert gate["claim_status"] == "not_claimed"
    assert artifacts["capsule"]["claim_status"] == "not_claimed"


def test_ambiguous_unlogged_error_is_counted_and_pointer_resolves(tmp_path):
    payload = _write_fixture(tmp_path)
    raw_metrics = payload["metrics"]
    summary = payload["summary"]
    cell = raw_metrics["metrics"]["ambiguous_unlogged_error"]

    assert cell["count"] == 0
    assert cell["denominator"] == raw_metrics["label_denominators"]["ambiguous"]
    assert backend.resolve_pointer(tmp_path, cell["source_case_pointer"])["label"] == "ambiguous"
    assert backend.resolve_pointer(
        tmp_path, f"{backend.RAW_METRICS_ARTIFACT}:$.metrics.ambiguous_unlogged_error"
    ) == cell
    assert summary["hardgates"]["TS-HG4"]["status"] == "pass"

    cases = copy.deepcopy(payload["cases"])
    cases[-1].pop("ambiguous_log_ref")
    artifacts = backend.write_artifacts(root=tmp_path, cases=cases)
    raw_metrics = artifacts["raw_metrics"]
    summary = artifacts["summary"]

    assert raw_metrics["metrics"]["ambiguous_unlogged_error"]["count"] == 1
    assert summary["hardgates"]["TS-HG4"]["status"] == "fail"
    assert summary["safety_claim_gate"]["claim_status"] == "not_claimed"
    assert artifacts["claim_capsule"]["claim_status"] == "not_claimed"


def test_claim_capsule_is_pointer_only_over_summary_and_metrics(tmp_path):
    payload = _write_fixture(tmp_path)
    capsule = payload["capsule"]
    summary = payload["summary"]

    assert capsule["claim_status"] == "claimed"
    assert set(capsule["not_claimed"]) == {
        "real deployment safety",
        "real LLM jailbreak behavior",
        "sensitive-data handling",
        "mechanism closure",
    }
    assert set(capsule["source_evidence"]) == {
        "hardgate_refs",
        "metric_refs",
        "safety_claim_gate_ref",
        "summary_ref",
    }
    assert all(
        pointer.startswith(f"{backend.SUMMARY_ARTIFACT}:$.hardgates.")
        for pointer in capsule["source_evidence"]["hardgate_refs"].values()
    )
    assert capsule["source_evidence"]["metric_refs"] == {
        metric: f"{backend.RAW_METRICS_ARTIFACT}:$.metrics.{metric}"
        for metric in backend.METRICS
    }
    assert all(
        backend.resolve_pointer(tmp_path, pointer) is not None
        for pointer in capsule["source_evidence"]["metric_refs"].values()
    )
    assert backend.resolve_pointer(tmp_path, capsule["source_evidence"]["safety_claim_gate_ref"]) == summary[
        "safety_claim_gate"
    ]

    encoded = json.dumps(capsule, sort_keys=True)
    assert "case_id" not in encoded
    assert "expected_decision_set" not in encoded
    assert '"count"' not in encoded
    assert '"rate"' not in encoded
    assert ("terminal" + "_" + "verdict") not in encoded
    assert "raw_cases" not in capsule
    assert "metrics" not in capsule
    assert summary["hardgates"]["TS-HG5"]["status"] == "pass"


def test_missing_dual_metric_or_missing_ambiguous_log_sets_not_claimed(tmp_path):
    missing_dual = backend.write_artifacts(
        root=tmp_path,
        omit_metrics=("unsafe_false_negative", "over_refusal"),
    )
    assert missing_dual["summary"]["safety_claim_gate"]["claim_status"] == "not_claimed"
    assert missing_dual["claim_capsule"]["claim_status"] == "not_claimed"

    cases = copy.deepcopy(backend._default_cases())
    cases[-1].pop("ambiguous_log_ref")
    missing_log = backend.write_artifacts(root=tmp_path, cases=cases)
    assert missing_log["summary"]["hardgates"]["TS-HG4"]["status"] == "fail"
    assert missing_log["summary"]["safety_claim_gate"]["claim_status"] == "not_claimed"
    assert missing_log["claim_capsule"]["claim_status"] == "not_claimed"

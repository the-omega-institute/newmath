import ast
import json
from pathlib import Path

from scripts import run_canonical_reports as canonical
from tools import quality_discovery_demote_thesis_invariant as audit


ROOT = Path(__file__).resolve().parents[1]


def _write_fixture(root: Path, payload):
    path = root / "reports" / "fixture.json"
    path.parent.mkdir(parents=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    return path


def _walk_keys(value):
    if isinstance(value, dict):
        for key, cell in value.items():
            yield key
            yield from _walk_keys(cell)
    elif isinstance(value, list):
        for cell in value:
            yield from _walk_keys(cell)


def test_positive_tradeoff_fixture_is_caught(tmp_path):
    _write_fixture(
        tmp_path,
        {
            "cells": [
                {
                    "positive": True,
                    "discovery_level": "D4",
                    "debt_delta": -0.5,
                    "benefit_delta": -0.2,
                }
            ]
        },
    )

    payload = audit.audit_root(tmp_path, generated_at="2030-01-01T00:00:00+00:00")

    assert payload["status"] == "fail"
    assert payload["escaped_positive_count"] == 1
    assert payload["escaped_positive_rows"] == [
        {
            "file": "reports/fixture.json",
            "json_pointer": "$.cells[0]",
            "positive_signal": "positive=true",
            "tradeoff_evidence_pointer": "$.cells[0]",
            "evidence_kind": "debt_delta_and_benefit_delta_down",
            "reason": "debt_delta<0 and benefit_delta<0",
        }
    ]


def test_terminal_status_fields_positive_tradeoffs_are_caught(tmp_path):
    for field in ("final_main_claim_status", "status", "result_status", "new_status"):
        case_root = tmp_path / field
        _write_fixture(
            case_root,
            {
                "cell": {
                    field: "positive",
                    "debt_delta": -1,
                    "benefit_delta": -1,
                }
            },
        )

        payload = audit.audit_root(case_root, generated_at="2030-01-01T00:00:00+00:00")

        assert payload["status"] == "fail"
        assert payload["positive_candidate_count"] == 1
        assert payload["escaped_positive_count"] == 1
        assert payload["escaped_positive_rows"][0]["file"] == "reports/fixture.json"
        assert payload["escaped_positive_rows"][0]["json_pointer"] == "$.cell"
        assert payload["escaped_positive_rows"][0]["positive_signal"] == f"{field}=positive"
        assert payload["escaped_positive_rows"][0]["tradeoff_evidence_pointer"] == "$.cell"


def test_terminal_positive_verdict_tradeoff_is_caught(tmp_path):
    _write_fixture(
        tmp_path,
        {
            "cell": {
                "verdict": "terminal-positive",
                "debt_delta": -1,
                "benefit_delta": -1,
            }
        },
    )

    payload = audit.audit_root(tmp_path, generated_at="2030-01-01T00:00:00+00:00")

    assert payload["status"] == "fail"
    assert payload["positive_candidate_count"] == 1
    assert payload["escaped_positive_count"] == 1
    assert payload["escaped_positive_rows"][0]["json_pointer"] == "$.cell"
    assert payload["escaped_positive_rows"][0]["positive_signal"] == "verdict=terminal-positive"


def test_failed_wrapper_container_does_not_suppress_positive_record(tmp_path):
    _write_fixture(
        tmp_path,
        {
            "wrapper": {
                "status": "fail",
                "records": [
                    {
                        "positive": True,
                        "discovery_level": "D4",
                        "debt_delta": -1,
                        "benefit_delta": -1,
                    }
                ],
            }
        },
    )

    payload = audit.audit_root(tmp_path, generated_at="2030-01-01T00:00:00+00:00")

    assert payload["status"] == "fail"
    assert payload["positive_candidate_count"] == 1
    assert payload["escaped_positive_count"] == 1
    assert payload["escaped_positive_rows"][0]["json_pointer"] == "$.wrapper.records[0]"
    assert payload["escaped_positive_rows"][0]["positive_signal"] == "positive=true"


def test_ancestor_gate_basis_list_tradeoff_is_caught(tmp_path):
    _write_fixture(
        tmp_path,
        {
            "record": {
                "gate_basis": [
                    {
                        "debt_delta": -1,
                        "benefit_delta": -1,
                    }
                ],
                "cell": {
                    "positive": True,
                },
            }
        },
    )

    payload = audit.audit_root(tmp_path, generated_at="2030-01-01T00:00:00+00:00")

    assert payload["status"] == "fail"
    assert payload["positive_candidate_count"] == 1
    assert payload["escaped_positive_count"] == 1
    assert payload["escaped_positive_rows"][0]["file"] == "reports/fixture.json"
    assert payload["escaped_positive_rows"][0]["json_pointer"] == "$.record.cell"
    assert payload["escaped_positive_rows"][0]["positive_signal"] == "positive=true"
    assert payload["escaped_positive_rows"][0]["tradeoff_evidence_pointer"] == "$.record.gate_basis[0]"


def test_ancestor_nested_deltas_tradeoff_is_caught(tmp_path):
    _write_fixture(
        tmp_path,
        {
            "record": {
                "deltas": {
                    "after_minus_before": {
                        "debt_delta": -1,
                        "benefit_delta": -1,
                    }
                },
                "records": [
                    {
                        "positive": True,
                    }
                ],
            }
        },
    )

    payload = audit.audit_root(tmp_path, generated_at="2030-01-01T00:00:00+00:00")

    assert payload["status"] == "fail"
    assert payload["positive_candidate_count"] == 1
    assert payload["escaped_positive_count"] == 1
    assert payload["escaped_positive_rows"][0]["json_pointer"] == "$.record.records[0]"
    assert payload["escaped_positive_rows"][0]["tradeoff_evidence_pointer"] == "$.record.deltas.after_minus_before"


def test_ancestor_nested_baseline_delta_tradeoff_is_caught(tmp_path):
    _write_fixture(
        tmp_path,
        {
            "record": {
                "deltas": {
                    "debt_plus_benefit_minus_baseline": {
                        "debt_delta": -1,
                        "benefit_delta": -1,
                    }
                },
                "records": [
                    {
                        "positive": True,
                    }
                ],
            }
        },
    )

    payload = audit.audit_root(tmp_path, generated_at="2030-01-01T00:00:00+00:00")

    assert payload["status"] == "fail"
    assert payload["positive_candidate_count"] == 1
    assert payload["escaped_positive_count"] == 1
    assert payload["escaped_positive_rows"][0]["json_pointer"] == "$.record.records[0]"
    assert (
        payload["escaped_positive_rows"][0]["tradeoff_evidence_pointer"]
        == "$.record.deltas.debt_plus_benefit_minus_baseline"
    )


def test_non_positive_tradeoff_fixture_passes(tmp_path):
    _write_fixture(
        tmp_path,
        {
            "cells": [
                {
                    "positive": False,
                    "discovery_level": "DN",
                    "debt_delta": -0.5,
                    "benefit_delta": -0.2,
                }
            ]
        },
    )

    payload = audit.audit_root(tmp_path, generated_at="2030-01-01T00:00:00+00:00")

    assert payload["status"] == "pass"
    assert payload["positive_candidate_count"] == 0
    assert payload["escaped_positive_rows"] == []


def test_positive_non_tradeoff_fixture_passes(tmp_path):
    _write_fixture(
        tmp_path,
        {
            "cells": [
                {
                    "positive": True,
                    "discovery_level": "D4",
                    "debt_delta": -0.5,
                    "benefit_delta": 0.0,
                }
            ]
        },
    )

    payload = audit.audit_root(tmp_path, generated_at="2030-01-01T00:00:00+00:00")

    assert payload["status"] == "pass"
    assert payload["positive_candidate_count"] == 1
    assert payload["escaped_positive_rows"] == []


def test_demoted_parent_suppresses_nested_positive_basis(tmp_path):
    _write_fixture(
        tmp_path,
        {
            "rows": [
                {
                    "terminal_verdict": "demoted",
                    "discovery_level": "DN",
                    "gate_basis": {
                        "main_claim_status": "positive",
                        "audit_improvement_tradeoff": True,
                    },
                }
            ]
        },
    )

    payload = audit.audit_root(tmp_path, generated_at="2030-01-01T00:00:00+00:00")

    assert payload["status"] == "pass"
    assert payload["positive_candidate_count"] == 0
    assert payload["escaped_positive_rows"] == []


def test_checked_in_artifacts_pass_demote_thesis_invariant():
    payload = audit.audit_root(ROOT, generated_at="2030-01-01T00:00:00+00:00")

    assert payload["status"] == "pass"
    assert payload["escaped_positive_rows"] == []


def test_sidecar_is_pointer_only_and_schema_local():
    payload = audit.audit_root(ROOT, generated_at="2030-01-01T00:00:00+00:00")

    assert payload["schema_id"] == "bedc-quality-lab:demote-thesis-invariant-audit"
    assert payload["artifact_id"] == "bedc-quality-lab:demote-thesis-invariant-audit"
    assert payload["producer"] == "tools/quality_discovery_demote_thesis_invariant.py"
    keys = set(_walk_keys(payload))
    assert keys.isdisjoint(audit.FORBIDDEN_SIDECAR_FIELDS)
    assert keys.isdisjoint(audit.FORBIDDEN_SCORE_FIELDS)
    encoded = json.dumps(payload, sort_keys=True)
    for forbidden in audit.FORBIDDEN_POSITIVE_CLAIM_TERMS:
        assert forbidden not in encoded
    audit.assert_pointer_only_boundary(payload)


def test_tool_has_non_producer_import_boundary():
    tree = ast.parse((ROOT / "tools" / "quality_discovery_demote_thesis_invariant.py").read_text(encoding="utf-8"))
    imported_roots = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            imported_roots.update(alias.name.split(".")[0] for alias in node.names)
        elif isinstance(node, ast.ImportFrom) and node.module:
            imported_roots.add(node.module.split(".")[0])

    assert imported_roots == {
        "__future__",
        "argparse",
        "dataclasses",
        "datetime",
        "json",
        "pathlib",
        "typing",
    }
    assert {"bedc_quality_lab", "scripts", "tools"}.isdisjoint(imported_roots)


def test_sidecar_stays_out_of_canonical_reports_and_core_schema_exports():
    json_artifacts = {spec.json_artifact for spec in canonical.CANONICAL_REPORTS}

    assert audit.SIDECAR_ARTIFACT not in json_artifacts
    assert "demote_thesis_invariant_audit" not in {Path(spec.json_artifact).stem for spec in canonical.CANONICAL_REPORTS}

    import bedc_quality_lab
    from bedc_quality_lab.schema import SCHEMA_ID

    assert bedc_quality_lab.__all__ == ["QualityEvidenceEnvelope"]
    assert SCHEMA_ID == "bedc-quality-lab:evidence-envelope"
    assert audit.SCHEMA_ID != SCHEMA_ID


def test_sidecar_self_exclusion(tmp_path):
    path = tmp_path / audit.SIDECAR_ARTIFACT
    path.parent.mkdir(parents=True)
    path.write_text(
        json.dumps(
            {
                "escaped_positive_rows": [
                    {
                        "positive": True,
                        "discovery_level": "D4",
                        "debt_delta": -1,
                        "benefit_delta": -1,
                    }
                ]
            }
        )
        + "\n",
        encoding="utf-8",
    )

    payload = audit.audit_root(tmp_path, generated_at="2030-01-01T00:00:00+00:00")

    assert payload["scanned_counts"]["files"] == 0
    assert payload["status"] == "pass"


def test_write_scope_is_limited_to_demote_thesis_sidecar(tmp_path):
    payload = audit.audit_root(tmp_path, generated_at="2030-01-01T00:00:00+00:00")
    written = audit.write_sidecar(tmp_path, payload)

    assert written.relative_to(tmp_path).as_posix() == audit.SIDECAR_ARTIFACT

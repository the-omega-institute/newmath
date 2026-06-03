import json
from pathlib import Path

import numpy as np
import pytest

from bedc_quality_lab.claim_terms import FORBIDDEN_POSITIVE_CLAIM_TERMS
from scripts import run_canonical_reports as canonical
from scripts import run_dimension_mismatch_debt_transfer as transfer


def _stats(mean, low=None, high=None):
    low = mean if low is None else low
    high = mean if high is None else high
    return {
        "n": 1,
        "mean": float(mean),
        "std": 0.0,
        "ci95_half_width": 0.0,
        "ci95_low": float(low),
        "ci95_high": float(high),
    }


def _matrix():
    features = np.array(
        [
            [0.1, 0.2, 0.2, 0.1, 0.1, 0.2, 0.05, 0.10, 0.15, 0.1],
            [0.2, 0.3, 0.3, 0.1, 0.2, 0.3, 0.10, 0.15, 0.20, 0.1],
            [0.9, 0.8, 1.0, 0.2, 0.8, 1.0, 0.60, 0.80, 0.90, 0.2],
            [1.0, 0.9, 1.1, 0.2, 0.9, 1.1, 0.70, 0.90, 1.00, 0.2],
            [0.8, 0.7, 0.9, 0.2, 0.7, 0.9, 0.50, 0.70, 0.80, 0.2],
            [0.15, 0.2, 0.2, 0.1, 0.1, 0.2, 0.05, 0.10, 0.15, 0.1],
        ],
        dtype=np.float64,
    )
    labels = np.column_stack(
        [
            np.array([0, 0, 1, 1, 1, 0], dtype=np.float64),
            np.array([0, 0, 1, 1, 1, 0], dtype=np.float64),
            np.array([0, 0, 0, 0, 0, 0], dtype=np.float64),
            np.array([1, 1, 0, 0, 0, 1], dtype=np.float64),
        ]
    )
    rows = [
        {
            "axis": "C1",
            "axis_label": "encoder_output_dim",
            "axis_value": index + 1,
            "row": transfer.DEFAULT_ROW,
            "status_code": "dimension-mismatch-surface" if index in {2, 3, 4} else "reference-dimension",
            "reason": "fixture reason",
            "metric": "linear_identifiability_r2",
            "metric_value": 0.5,
            "row_present": True,
            "row_gap": index in {2, 3, 4},
            "source_pointer": "fixture",
        }
        for index in range(6)
    ]
    return {
        "features": features,
        "labels": labels,
        "prediction_error": labels[:, 0],
        "feature_columns": list(transfer.H_ONLY_REPRESENTATION_SUMMARY_COLUMNS),
        "evidence_rows": rows,
        "seeds": (11,),
        "reference_latent_dim": 2,
    }


def _patch_matrix(monkeypatch):
    monkeypatch.setattr(transfer, "_surface_matrix", _matrix)
    monkeypatch.setattr(
        transfer,
        "_fold_record",
        lambda matrix, *, fold_seed, fold_index: {
            "fold_index": fold_index,
            "fold_seed": fold_seed,
            "arms": {
                "vanilla": {"failure_detection_auroc": {"value": 0.5}},
                "learned_h_summary_head": {"failure_detection_auroc": {"value": 0.9}},
                transfer.gap_head.MATCHED_RANDOM_ARM: {"failure_detection_auroc": {"value": 0.5}},
            },
            "comparison": {
                "failure_detection_auroc_delta_learned_minus_matched_random": 0.4,
                "failure_detection_auroc_delta_learned_minus_vanilla": 0.4,
            },
        },
    )


def test_assert_feature_matrix_contract_accepts_exact_h_only_allowlist():
    transfer.assert_feature_matrix_contract(transfer.H_ONLY_REPRESENTATION_SUMMARY_COLUMNS)


@pytest.mark.parametrize(
    "column",
    [
        "encoder_dim",
        "abs_encoder_dim_minus_reference_dim",
        "linear_identifiability_r2",
        "quality_debt",
        "debt_delta",
        "ledger_status",
        "gap_status",
        "label",
        "prediction_error",
        "row_index",
        "raw_h",
        "raw_z",
        "envelope_record",
    ],
)
def test_assert_feature_matrix_contract_rejects_forbidden_columns(column):
    columns = list(transfer.H_ONLY_REPRESENTATION_SUMMARY_COLUMNS)
    columns.append(column)

    with pytest.raises(ValueError):
        transfer.assert_feature_matrix_contract(columns)


def test_build_payload_records_hardgates_and_scoped_d4_pass(monkeypatch):
    _patch_matrix(monkeypatch)
    monkeypatch.setattr(transfer, "_arm_metrics", lambda records, arm: {"failure_detection_auroc": _stats(0.9 if arm == "learned_h_summary_head" else 0.5)})
    monkeypatch.setattr(transfer, "_delta_stats", lambda records, key: _stats(0.4, 0.4, 0.4))

    payload = transfer.build_payload(generated_at="fixture-time")

    assert payload["dimension_mismatch_debt_transfer"]["status"] == "pass"
    assert payload["dimension_mismatch_debt_transfer"]["discovery_level"] == "D4"
    assert payload["boundary_ledger"]["d5_shortcut"] is False
    assert {gate["status"] for gate in payload["hardgate_evidence"].values()} == {"pass"}
    assert payload["hardgate_evidence"]["HG-B2"]["matched_random_auroc"]["mean"] == 0.5
    assert payload["hardgate_evidence"]["HG-B3"]["reason"]
    assert all(row["reason"] and row["status_code"] for row in payload["surfaces"][0]["result_rows"])


def test_failed_comparison_projects_no_positive_d4_d5(monkeypatch):
    _patch_matrix(monkeypatch)
    monkeypatch.setattr(transfer, "_arm_metrics", lambda records, arm: {"failure_detection_auroc": _stats(0.55)})
    monkeypatch.setattr(transfer, "_delta_stats", lambda records, key: _stats(0.0, -0.1, 0.1))

    payload = transfer.build_payload(generated_at="fixture-time")

    assert payload["dimension_mismatch_debt_transfer"]["status"] == "failed"
    assert payload["dimension_mismatch_debt_transfer"]["discovery_level"] == "DN"
    assert payload["boundary_ledger"]["failed_gates"]
    assert payload["boundary_ledger"]["d5_shortcut"] is False


def test_missing_matched_random_control_fails_closed(monkeypatch):
    matrix = _matrix()
    monkeypatch.setattr(transfer, "_surface_matrix", lambda: matrix)
    monkeypatch.setattr(
        transfer,
        "_fold_record",
        lambda matrix, *, fold_seed, fold_index: {
            "arms": {
                "vanilla": {"failure_detection_auroc": {"value": 0.5}},
                "learned_h_summary_head": {"failure_detection_auroc": {"value": 0.9}},
            },
            "comparison": {
                "failure_detection_auroc_delta_learned_minus_matched_random": 0.4,
                "failure_detection_auroc_delta_learned_minus_vanilla": 0.4,
            },
        },
    )
    monkeypatch.setattr(transfer, "_arm_metrics", lambda records, arm: {"failure_detection_auroc": _stats(0.9)})
    monkeypatch.setattr(transfer, "_delta_stats", lambda records, key: _stats(0.4))

    payload = transfer.build_payload(generated_at="fixture-time")

    assert payload["dimension_mismatch_debt_transfer"]["status"] == "failed"
    assert payload["hardgate_evidence"]["HG-B2"]["status"] == "fail"


def test_forbidden_claim_term_audit_uses_single_source_terms():
    term = FORBIDDEN_POSITIVE_CLAIM_TERMS[0]
    audit = transfer._forbidden_claim_term_audit(
        {"dimension_mismatch_debt_transfer": {"status": "pass", "claim": term}}
    )

    assert audit["status"] == "fail"
    assert audit["hits"] == [term]


def test_markdown_is_pointer_only_and_artifact_is_not_canonical(monkeypatch):
    _patch_matrix(monkeypatch)
    monkeypatch.setattr(transfer, "_arm_metrics", lambda records, arm: {"failure_detection_auroc": _stats(0.9 if arm == "learned_h_summary_head" else 0.5)})
    monkeypatch.setattr(transfer, "_delta_stats", lambda records, key: _stats(0.4, 0.4, 0.4))
    payload = transfer.build_payload(generated_at="fixture-time")
    markdown = transfer.render_markdown(payload)

    assert "$.dimension_mismatch_debt_transfer.status" in markdown
    assert "Metric rows" in markdown
    assert "raw_h" not in markdown
    assert "feature matrix" not in markdown.lower()
    assert "dimension-mismatch-debt-transfer.json" not in {
        Path(spec.json_artifact).name for spec in canonical.CANONICAL_REPORTS
    }


def test_write_payload_keeps_pointer_artifact(tmp_path, monkeypatch):
    _patch_matrix(monkeypatch)
    monkeypatch.setattr(transfer, "_arm_metrics", lambda records, arm: {"failure_detection_auroc": _stats(0.9 if arm == "learned_h_summary_head" else 0.5)})
    monkeypatch.setattr(transfer, "_delta_stats", lambda records, key: _stats(0.4, 0.4, 0.4))
    monkeypatch.setattr(transfer, "ROOT", tmp_path)
    payload = transfer.build_payload(generated_at="fixture-time")

    transfer._write_payload(payload)

    written = json.loads((tmp_path / transfer.JSON_ARTIFACT).read_text(encoding="utf-8"))
    markdown = (tmp_path / transfer.REPORT_ARTIFACT).read_text(encoding="utf-8")
    assert written["artifact_id"] == transfer.ARTIFACT_ID
    assert written["status"] == "pointer-only"
    assert "raw_h" not in markdown

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
    features = np.column_stack([features, np.full(features.shape[0], 0.01, dtype=np.float64)])
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
            "axis": transfer.DEFAULT_AXIS,
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


def _sidecar(root: Path, *, status: str = "scale_leakage_detected", projection: str = "demote_to_DN_or_D1") -> None:
    path = root / transfer.ANTI_TRIVIALITY_ARTIFACT
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps({"status": status, "recommended_projection": projection}) + "\n",
        encoding="utf-8",
    )


def test_assert_feature_matrix_contract_accepts_exact_h_only_allowlist():
    features = np.zeros((2, len(transfer.H_ONLY_REPRESENTATION_SUMMARY_COLUMNS)), dtype=np.float64)
    transfer.assert_feature_matrix_contract(features, transfer.H_ONLY_REPRESENTATION_SUMMARY_COLUMNS)


def test_assert_feature_matrix_contract_rejects_width_mismatch():
    features = np.zeros((2, len(transfer.H_ONLY_REPRESENTATION_SUMMARY_COLUMNS) - 1), dtype=np.float64)

    with pytest.raises(ValueError, match="feature matrix width"):
        transfer.assert_feature_matrix_contract(features, transfer.H_ONLY_REPRESENTATION_SUMMARY_COLUMNS)


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
    features = np.zeros((2, len(columns)), dtype=np.float64)

    with pytest.raises(ValueError):
        transfer.assert_feature_matrix_contract(features, columns)


def test_surface_matrix_actual_input_matches_h_only_allowlist():
    matrix = transfer._surface_matrix()
    features = np.asarray(matrix["features"], dtype=np.float64)
    columns = tuple(matrix["feature_columns"])

    assert features.shape[1] == len(transfer.H_ONLY_REPRESENTATION_SUMMARY_COLUMNS)
    assert columns == transfer.H_ONLY_REPRESENTATION_SUMMARY_COLUMNS
    transfer.assert_feature_matrix_contract(features, columns)
    audit = transfer._feature_contract_audit(features, columns)
    assert audit["status"] == "pass"
    assert audit["actual_model_input_width"] == len(transfer.H_ONLY_REPRESENTATION_SUMMARY_COLUMNS)


def test_build_payload_records_hardgates_and_sidecar_driven_dn(monkeypatch, tmp_path):
    _patch_matrix(monkeypatch)
    monkeypatch.setattr(transfer, "_arm_metrics", lambda records, arm: {"failure_detection_auroc": _stats(0.9 if arm == "learned_h_summary_head" else 0.5)})
    monkeypatch.setattr(transfer, "_delta_stats", lambda records, key: _stats(0.4, 0.4, 0.4))
    _sidecar(tmp_path)

    payload = transfer.build_payload(root=tmp_path, generated_at="fixture-time")

    assert payload["dimension_mismatch_debt_transfer"]["status"] == "pass"
    assert payload["dimension_mismatch_debt_transfer"]["base_level"] == "D4"
    assert payload["dimension_mismatch_debt_transfer"]["anti_triviality_status"] == "scale_leakage_detected"
    assert payload["dimension_mismatch_debt_transfer"]["anti_triviality_projection"] == "demote_to_DN_or_D1"
    assert payload["dimension_mismatch_debt_transfer"]["anti_triviality_fold_status"] == "pass"
    assert payload["dimension_mismatch_debt_transfer"]["effective_level"] == "DN"
    assert payload["dimension_mismatch_debt_transfer"]["discovery_level"] == "DN"
    assert payload["dimension_mismatch_debt_transfer"]["terminal_verdict"] == "negative_discovery"
    assert payload["dimension_mismatch_debt_transfer"]["downgrade_reason"] == "scale_only_or_metadata_proxy_sufficient"
    assert payload["dimension_mismatch_debt_transfer"]["hypothesis"]
    assert payload["dimension_mismatch_debt_transfer"]["failed_gate"] == "$.dimension_mismatch_debt_transfer.anti_triviality_status"
    assert payload["dimension_mismatch_debt_transfer"]["what_was_learned"]
    assert payload["dimension_mismatch_debt_transfer"]["not_claimed"] == [
        "global dimension theory",
        "representation-geometric debt transfer",
        "D5 promotion",
    ]
    assert payload["boundary_ledger"]["d5_shortcut"] is False
    assert payload["boundary_ledger"]["projection"] == "DN"
    assert payload["dimension_mismatch_debt_transfer"]["pass_surface_count"] == 1
    assert payload["dimension_mismatch_debt_transfer"]["total_surface_count"] == 1
    assert {gate["status"] for gate in payload["hardgate_evidence"].values()} == {"pass"}
    assert payload["hardgate_evidence"]["HG-B2"]["matched_random_auroc"]["mean"] == 0.5
    assert payload["hardgate_evidence"]["HG-B3"]["reason"]
    assert payload["hardgate_evidence"]["HG-B4"]["audit"]["actual_model_input_width"] == len(
        transfer.H_ONLY_REPRESENTATION_SUMMARY_COLUMNS
    )
    assert all(row["reason"] and row["status_code"] for row in payload["surfaces"][0]["result_rows"])


def test_sidecar_absent_or_unfoldable_does_not_emit_terminal_dn(monkeypatch, tmp_path):
    _patch_matrix(monkeypatch)
    monkeypatch.setattr(transfer, "_arm_metrics", lambda records, arm: {"failure_detection_auroc": _stats(0.9 if arm == "learned_h_summary_head" else 0.5)})
    monkeypatch.setattr(transfer, "_delta_stats", lambda records, key: _stats(0.4, 0.4, 0.4))

    missing = transfer.build_payload(root=tmp_path, generated_at="fixture-time")
    assert missing["dimension_mismatch_debt_transfer"]["anti_triviality_fold_status"] == "defer"
    assert missing["dimension_mismatch_debt_transfer"]["effective_level"] == "defer"
    assert missing["dimension_mismatch_debt_transfer"]["terminal_verdict"] == "incomplete"

    _sidecar(tmp_path, status="anti_triviality_passed", projection="no_level_change_signal_detected")
    passed = transfer.build_payload(root=tmp_path, generated_at="fixture-time")
    assert passed["dimension_mismatch_debt_transfer"]["anti_triviality_status"] == "anti_triviality_passed"
    assert passed["dimension_mismatch_debt_transfer"]["effective_level"] == "D4"
    assert passed["dimension_mismatch_debt_transfer"]["terminal_verdict"] == "source_pass"


def test_source_snapshot_can_be_written_before_sidecar(monkeypatch, tmp_path):
    _patch_matrix(monkeypatch)
    monkeypatch.setattr(transfer, "_arm_metrics", lambda records, arm: {"failure_detection_auroc": _stats(0.9 if arm == "learned_h_summary_head" else 0.5)})
    monkeypatch.setattr(transfer, "_delta_stats", lambda records, key: _stats(0.4, 0.4, 0.4))

    payload = transfer.build_payload(root=tmp_path, generated_at="fixture-time", require_anti_triviality=False)

    assert payload["dimension_mismatch_debt_transfer"]["anti_triviality_fold_status"] == "source_only"
    assert payload["dimension_mismatch_debt_transfer"]["effective_level"] == "D4"
    assert payload["dimension_mismatch_debt_transfer"]["terminal_verdict"] == "source_pass"


@pytest.mark.parametrize("gate_name", ["HG-B1", "HG-B4", "HG-B5"])
def test_selected_hardgate_failure_sets_failed_status_and_denominator(monkeypatch, tmp_path, gate_name):
    _patch_matrix(monkeypatch)
    monkeypatch.setattr(transfer, "_arm_metrics", lambda records, arm: {"failure_detection_auroc": _stats(0.9 if arm == "learned_h_summary_head" else 0.5)})
    monkeypatch.setattr(transfer, "_delta_stats", lambda records, key: _stats(0.4, 0.4, 0.4))
    _sidecar(tmp_path)
    original = transfer._hardgates

    def fake_hardgates(*, matrix, records):
        gates = original(matrix=matrix, records=records)
        gates[gate_name] = {**gates[gate_name], "status": "fail"}
        return gates

    monkeypatch.setattr(transfer, "_hardgates", fake_hardgates)
    payload = transfer.build_payload(root=tmp_path, generated_at="fixture-time")

    assert payload["dimension_mismatch_debt_transfer"]["status"] == "failed"
    assert payload["dimension_mismatch_debt_transfer"]["pass_surface_count"] == 0
    assert payload["dimension_mismatch_debt_transfer"]["total_surface_count"] == 1


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
    payload = transfer.build_payload(generated_at="fixture-time", require_anti_triviality=False)
    markdown = transfer.render_markdown(payload)

    assert "$.dimension_mismatch_debt_transfer.status" in markdown
    assert "effective level" in markdown
    assert "Metric rows" in markdown
    assert "no non-trivial debt-transfer mechanism independent of encoder-dimension information" in markdown
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

    payload = transfer.write_dimension_mismatch_debt_transfer(root=tmp_path, generated_at="fixture-time", require_anti_triviality=False)

    written = json.loads((tmp_path / transfer.JSON_ARTIFACT).read_text(encoding="utf-8"))
    markdown = (tmp_path / transfer.REPORT_ARTIFACT).read_text(encoding="utf-8")
    assert written["artifact_id"] == transfer.ARTIFACT_ID
    assert written["status"] == "pointer-only"
    assert "raw_h" not in markdown

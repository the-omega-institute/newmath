import json
from pathlib import Path

import numpy as np
import pytest

from bedc_quality_lab.claim_terms import FORBIDDEN_POSITIVE_CLAIM_TERMS
from bedc_quality_lab.discovery_compiler.pointers import pointer_value
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


def _sidecar(
    root: Path,
    *,
    status: str = "scale_leakage_detected",
    projection: str = "demote_to_DN_or_D1",
    coverage_status: str = "pass",
    omit_family: str | None = None,
    malformed_family: str | None = None,
    unknown_family: str | None = None,
) -> None:
    path = root / transfer.ANTI_TRIVIALITY_ARTIFACT
    path.parent.mkdir(parents=True, exist_ok=True)
    arms = [{"arm": family, "feature_columns": [family]} for family in transfer.CONTROL_FAMILY_ORDER]
    family_pointers = {
        family: f"$.arms[{index}]"
        for index, family in enumerate(transfer.CONTROL_FAMILY_ORDER)
        if family != omit_family
    }
    if malformed_family is not None:
        family_pointers[malformed_family] = "$.missing"
    observed = [family for family in transfer.CONTROL_FAMILY_ORDER if family != omit_family]
    if unknown_family is not None:
        observed.append(unknown_family)
        family_pointers[unknown_family] = "$.unknown"
    path.write_text(
        json.dumps(
            {
                "status": status,
                "recommended_projection": projection,
                "arms": arms,
                "controlled_geometry": {
                    "evidence_refs": [
                        {
                            "evidence_id": "B2-HG1",
                            "source_artifact": transfer.ANTI_TRIVIALITY_ARTIFACT,
                            "source_pointer": "$.controlled_geometry_hardgates.B2-HG1",
                            "controlled_geometry_artifact": transfer.ANTI_TRIVIALITY_ARTIFACT,
                            "controlled_geometry_pointer": "$.controlled_geometry.feature_partition",
                        }
                    ],
                    "feature_partition": {"fixture": ["h_l2_mean"]},
                    "control_family_coverage": {
                        "status": coverage_status,
                        "required_families": list(transfer.CONTROL_FAMILY_ORDER),
                        "observed_families": observed,
                        "family_pointers": family_pointers,
                    },
                },
                "controlled_geometry_hardgates": {
                    "B2-HG1": {
                        "status": "pass",
                        "source_pointer": "$.controlled_geometry.feature_partition",
                    }
                },
                "controlled_geometry_pointer_contract": {
                    "source_artifact": transfer.ANTI_TRIVIALITY_ARTIFACT,
                    "pointer_root": "$.controlled_geometry",
                },
            }
        )
        + "\n",
        encoding="utf-8",
    )


def _read_json(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def _read_jsonl(path: Path):
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def _recursive_keys(value):
    if isinstance(value, dict):
        for key, item in value.items():
            yield key
            yield from _recursive_keys(item)
    elif isinstance(value, list):
        for item in value:
            yield from _recursive_keys(item)


def _generated_run_artifacts(root: Path) -> dict[str, Path]:
    base = root / transfer.RUN_LOCAL_DIR
    return {
        "claim_capsule": base / "claim_capsule.json",
        "raw_metrics": base / "raw_metrics.jsonl",
        "summary": base / "summary.json",
        "report": base / "report.md",
    }


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
    assert payload["dimension_mismatch_debt_transfer"]["anti_triviality_policy"] == "positive_requires_all_four_controls"
    assert payload["dimension_mismatch_debt_transfer"]["anti_triviality_recommended_level"] == "DN"
    assert payload["dimension_mismatch_debt_transfer"]["anti_triviality_failed_gate"] == "$.dimension_mismatch_debt_transfer.anti_triviality_status"
    assert payload["dimension_mismatch_debt_transfer"]["anti_triviality_gate_evidence"] == {
        "scale_only": {"status": "fail", "pointer": "$.dimension_mismatch_debt_transfer.anti_triviality_status"},
        "metadata_only": {"status": "fail", "pointer": "$.dimension_mismatch_debt_transfer.anti_triviality_status"},
        "matched_random": {"status": "fail", "pointer": "$.control_protocol"},
        "forbidden_column": {"status": "fail", "pointer": "$.representation_boundary.actual_model_input_columns"},
    }
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
    assert passed["dimension_mismatch_debt_transfer"]["anti_triviality_policy"] == "positive_requires_all_four_controls"
    assert passed["dimension_mismatch_debt_transfer"]["anti_triviality_recommended_level"] == "D4"
    assert passed["dimension_mismatch_debt_transfer"]["anti_triviality_failed_gate"] is None
    assert passed["dimension_mismatch_debt_transfer"]["anti_triviality_gate_evidence"] == {
        "scale_only": {"status": "pass", "pointer": "$.dimension_mismatch_debt_transfer.anti_triviality_status"},
        "metadata_only": {"status": "pass", "pointer": "$.dimension_mismatch_debt_transfer.anti_triviality_status"},
        "matched_random": {"status": "pass", "pointer": "$.control_protocol"},
        "forbidden_column": {"status": "pass", "pointer": "$.representation_boundary.actual_model_input_columns"},
    }
    assert passed["dimension_mismatch_debt_transfer"]["effective_level"] == "D4"
    assert passed["dimension_mismatch_debt_transfer"]["terminal_verdict"] == "source_pass"


@pytest.mark.parametrize(
    "status,projection,kwargs",
    [
        ("random_projection_positive", "defer", {}),
        ("whitening_failure_detected", "defer", {}),
        ("anti_triviality_passed", "no_level_change_signal_detected", {"coverage_status": "defer"}),
        ("anti_triviality_passed", "no_level_change_signal_detected", {"omit_family": "rank_proxy_diagnostic"}),
        ("anti_triviality_passed", "no_level_change_signal_detected", {"malformed_family": "rank_proxy_diagnostic"}),
        ("anti_triviality_passed", "no_level_change_signal_detected", {"unknown_family": "unexpected_family"}),
        ("unexpected_status", "defer", {}),
    ],
)
def test_sidecar_non_foldable_cases_project_incomplete(monkeypatch, tmp_path, status, projection, kwargs):
    _patch_matrix(monkeypatch)
    monkeypatch.setattr(transfer, "_arm_metrics", lambda records, arm: {"failure_detection_auroc": _stats(0.9 if arm == "learned_h_summary_head" else 0.5)})
    monkeypatch.setattr(transfer, "_delta_stats", lambda records, key: _stats(0.4, 0.4, 0.4))
    _sidecar(tmp_path, status=status, projection=projection, **kwargs)

    payload = transfer.build_payload(root=tmp_path, generated_at="fixture-time")

    assert payload["dimension_mismatch_debt_transfer"]["anti_triviality_fold_status"] == "defer"
    assert payload["dimension_mismatch_debt_transfer"]["effective_level"] == "defer"
    assert payload["dimension_mismatch_debt_transfer"]["terminal_verdict"] == "incomplete"


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


def test_dimension_mismatch_run_local_bundle_owned_by_debt_transfer_capsule_run_local(monkeypatch, tmp_path):
    _patch_matrix(monkeypatch)
    monkeypatch.setattr(transfer, "_arm_metrics", lambda records, arm: {"failure_detection_auroc": _stats(0.9 if arm == "learned_h_summary_head" else 0.5)})
    monkeypatch.setattr(transfer, "_delta_stats", lambda records, key: _stats(0.4, 0.4, 0.4))
    _sidecar(tmp_path)

    payload = transfer.write_dimension_mismatch_debt_transfer(root=tmp_path, generated_at="fixture-time")
    artifacts = _generated_run_artifacts(tmp_path)
    claim_capsule = _read_json(artifacts["claim_capsule"])
    raw_metrics = _read_jsonl(artifacts["raw_metrics"])
    summary = _read_json(artifacts["summary"])

    assert set(artifacts) == {"claim_capsule", "raw_metrics", "summary", "report"}
    assert all(path.exists() for path in artifacts.values())
    assert claim_capsule["schema_id"] == "bedc.quality.claim_capsule"
    assert claim_capsule["claim_id"] == "claim:dimension-mismatch-debt-transfer"
    assert claim_capsule["run_local"]["owner"] == "claim:dimension-mismatch-debt-transfer"
    assert claim_capsule["run_local"] == transfer.build_run_local_contract(payload)
    assert claim_capsule["run_local"]["artifact_bundle"] == {
        "claim_capsule": transfer.RUN_LOCAL_CLAIM_CAPSULE_ARTIFACT,
        "raw_metrics": transfer.RUN_LOCAL_RAW_METRICS_ARTIFACT,
        "summary": transfer.RUN_LOCAL_SUMMARY_ARTIFACT,
        "report": transfer.RUN_LOCAL_REPORT_ARTIFACT,
    }
    assert summary["claim_capsule_ref"] == {
        "artifact": transfer.RUN_LOCAL_CLAIM_CAPSULE_ARTIFACT,
        "pointer": "$.run_local",
    }
    assert "run_local" not in summary
    assert {row["metric"] for row in raw_metrics} >= {"canonical-claim", "boundary-ledger", "B2-HG1"}


def test_dimension_mismatch_producer_rewrite_is_stable_with_fixed_timestamp(monkeypatch, tmp_path):
    _patch_matrix(monkeypatch)
    monkeypatch.setattr(transfer, "_arm_metrics", lambda records, arm: {"failure_detection_auroc": _stats(0.9 if arm == "learned_h_summary_head" else 0.5)})
    monkeypatch.setattr(transfer, "_delta_stats", lambda records, key: _stats(0.4, 0.4, 0.4))
    _sidecar(tmp_path)

    transfer.write_dimension_mismatch_debt_transfer(root=tmp_path, generated_at="fixture-time")
    artifacts = _generated_run_artifacts(tmp_path)
    first = {name: path.read_bytes() for name, path in artifacts.items()}
    first_capsule = _read_json(artifacts["claim_capsule"])
    assert first_capsule["run_local"]["negative_witness"]
    assert first_capsule["run_local"]["negative_witness_hardgates"]

    transfer.write_dimension_mismatch_debt_transfer(root=tmp_path, generated_at="fixture-time")

    assert {name: path.read_bytes() for name, path in artifacts.items()} == first


def test_dimension_mismatch_summary_points_to_capsule_run_local_contract(monkeypatch, tmp_path):
    _patch_matrix(monkeypatch)
    monkeypatch.setattr(transfer, "_arm_metrics", lambda records, arm: {"failure_detection_auroc": _stats(0.9 if arm == "learned_h_summary_head" else 0.5)})
    monkeypatch.setattr(transfer, "_delta_stats", lambda records, key: _stats(0.4, 0.4, 0.4))
    _sidecar(tmp_path)

    payload = transfer.write_dimension_mismatch_debt_transfer(root=tmp_path, generated_at="fixture-time")
    artifacts = _generated_run_artifacts(tmp_path)
    summary = _read_json(artifacts["summary"])
    claim_capsule = _read_json(artifacts["claim_capsule"])

    assert claim_capsule["run_local"] == transfer.build_run_local_contract(payload)
    assert summary["claim_capsule_ref"]["pointer"] == "$.run_local"
    assert pointer_value(claim_capsule, summary["claim_capsule_ref"]["pointer"]) == claim_capsule["run_local"]


def test_dimension_mismatch_run_artifacts_use_versionless_schema_and_names(monkeypatch, tmp_path):
    _patch_matrix(monkeypatch)
    monkeypatch.setattr(transfer, "_arm_metrics", lambda records, arm: {"failure_detection_auroc": _stats(0.9 if arm == "learned_h_summary_head" else 0.5)})
    monkeypatch.setattr(transfer, "_delta_stats", lambda records, key: _stats(0.4, 0.4, 0.4))
    _sidecar(tmp_path)

    transfer.write_dimension_mismatch_debt_transfer(root=tmp_path, generated_at="fixture-time")
    artifacts = _generated_run_artifacts(tmp_path)
    payloads = [
        _read_json(artifacts["claim_capsule"]),
        _read_json(artifacts["summary"]),
        *_read_jsonl(artifacts["raw_metrics"]),
    ]
    text = "\n".join(json.dumps(payload, sort_keys=True) for payload in payloads)
    text += artifacts["report"].read_text(encoding="utf-8")
    path_text = "\n".join(str(path.relative_to(tmp_path)) for path in artifacts.values())

    assert _read_json(artifacts["claim_capsule"])["schema_id"] == "bedc.quality.claim_capsule"
    assert ".v1" not in text
    assert "issue-696" not in text
    assert "696" not in path_text
    assert "v2" not in text.lower()
    assert "controlled-geometry" in path_text
    assert ".refactor-loop/host.env" not in text


def test_negative_witness_rows_live_under_run_local_owner(monkeypatch, tmp_path):
    _patch_matrix(monkeypatch)
    monkeypatch.setattr(transfer, "_arm_metrics", lambda records, arm: {"failure_detection_auroc": _stats(0.9 if arm == "learned_h_summary_head" else 0.5)})
    monkeypatch.setattr(transfer, "_delta_stats", lambda records, key: _stats(0.4, 0.4, 0.4))
    _sidecar(tmp_path)

    transfer.write_dimension_mismatch_debt_transfer(root=tmp_path, generated_at="fixture-time")
    artifacts = _generated_run_artifacts(tmp_path)
    claim_capsule = _read_json(artifacts["claim_capsule"])
    canonical_json = _read_json(tmp_path / transfer.JSON_ARTIFACT)
    summary = _read_json(artifacts["summary"])
    raw_metrics = _read_jsonl(artifacts["raw_metrics"])

    assert list(claim_capsule["run_local"]).count("negative_witness") == 1
    assert claim_capsule["run_local"]["negative_witness"]
    assert "negative_witness" not in canonical_json
    assert "negative_witness" not in summary
    assert all("bedc_gap_field" not in row for row in raw_metrics)
    assert summary["negative_witness_ref"] == {
        "artifact": transfer.RUN_LOCAL_CLAIM_CAPSULE_ARTIFACT,
        "pointer": "$.run_local.negative_witness",
    }


def test_scale_leakage_sidecar_maps_to_first_negative_witness(monkeypatch, tmp_path):
    _patch_matrix(monkeypatch)
    monkeypatch.setattr(transfer, "_arm_metrics", lambda records, arm: {"failure_detection_auroc": _stats(0.9 if arm == "learned_h_summary_head" else 0.5)})
    monkeypatch.setattr(transfer, "_delta_stats", lambda records, key: _stats(0.4, 0.4, 0.4))
    _sidecar(tmp_path)

    payload = transfer.write_dimension_mismatch_debt_transfer(root=tmp_path, generated_at="fixture-time")
    claim_capsule = _read_json(_generated_run_artifacts(tmp_path)["claim_capsule"])
    row = claim_capsule["run_local"]["negative_witness"][0]

    assert row["witness_id"] == "scale_leakage_witness"
    assert row["bedc_gap_field"] == "representation_scale_leakage"
    assert row["demotion_rule"] == "demote_to_DN_or_D1"
    assert row["source_artifact"] == transfer.ANTI_TRIVIALITY_ARTIFACT
    assert row["source_pointer"] == "$.status"
    assert transfer.SCALE_LEAKAGE_WITNESS_POINTER == (
        "reports/runs/dimension-mismatch-debt-transfer/controlled-geometry/claim_capsule.json:"
        "$.run_local.negative_witness[0]"
    )
    assert transfer.scale_leakage_bedc_gap_mapping(tmp_path) == {
        "witness_pointer": transfer.SCALE_LEAKAGE_WITNESS_POINTER,
        "bedc_gap_field": "representation_scale_leakage",
        "demotion_rule": "demote_to_DN_or_D1",
        "regression_test": row["regression_test"],
    }
    assert pointer_value(_read_json(tmp_path / transfer.ANTI_TRIVIALITY_ARTIFACT), row["source_pointer"]) == "scale_leakage_detected"
    assert row == transfer.build_run_local_contract(payload, tmp_path)["negative_witness"][0]


def test_negative_witness_regression_test_pointer_resolves(monkeypatch, tmp_path):
    _patch_matrix(monkeypatch)
    monkeypatch.setattr(transfer, "_arm_metrics", lambda records, arm: {"failure_detection_auroc": _stats(0.9 if arm == "learned_h_summary_head" else 0.5)})
    monkeypatch.setattr(transfer, "_delta_stats", lambda records, key: _stats(0.4, 0.4, 0.4))
    _sidecar(tmp_path)

    transfer.write_dimension_mismatch_debt_transfer(root=tmp_path, generated_at="fixture-time")
    claim_capsule = _read_json(_generated_run_artifacts(tmp_path)["claim_capsule"])
    run_local = claim_capsule["run_local"]

    for row in run_local["negative_witness"]:
        assert row["demotion_rule"]
        assert pointer_value(claim_capsule, row["regression_test"]) is not None
        assert transfer.resolve_artifact_pointer(tmp_path, row["evidence_pointer"]) is not None
    assert run_local["negative_witness_hardgates"]["NW-HG2"]["status"] == "pass"
    assert run_local["negative_witness_hardgates"]["NW-HG2"]["valid_coverage_count"] == len(run_local["negative_witness"])


def test_negative_witness_dangling_regression_pointer_fails_closed(tmp_path):
    _sidecar(tmp_path)
    payload = {
        "dimension_mismatch_debt_transfer": {
            "anti_triviality_projection": "demote_to_DN_or_D1",
        }
    }
    rows = tuple(
        transfer.NegativeWitnessRow(
            **{
                **row.to_record(),
                "regression_test": "$.run_local.test_artifact.regression_tests.missing_nodeid",
            }
        )
        for row in transfer.build_negative_witness_rows(payload, tmp_path)
    )

    hardgates = transfer.negative_witness_hardgates(rows, tmp_path)

    assert hardgates["NW-HG2"]["status"] == "fail"
    assert hardgates["NW-HG2"]["valid_coverage_count"] == 0
    assert hardgates["NW-HG2"]["regression_test_resolves"]["scale_leakage_witness"] is False


def test_negative_witness_fields_do_not_emit_terminal_verdict(monkeypatch, tmp_path):
    _patch_matrix(monkeypatch)
    monkeypatch.setattr(transfer, "_arm_metrics", lambda records, arm: {"failure_detection_auroc": _stats(0.9 if arm == "learned_h_summary_head" else 0.5)})
    monkeypatch.setattr(transfer, "_delta_stats", lambda records, key: _stats(0.4, 0.4, 0.4))
    _sidecar(tmp_path)

    transfer.write_dimension_mismatch_debt_transfer(root=tmp_path, generated_at="fixture-time")
    claim_capsule = _read_json(_generated_run_artifacts(tmp_path)["claim_capsule"])
    payload = {
        "negative_witness": claim_capsule["run_local"]["negative_witness"],
        "negative_witness_hardgates": claim_capsule["run_local"]["negative_witness_hardgates"],
    }

    assert "terminal_verdict" not in set(_recursive_keys(payload))


def test_negative_witness_schema_is_versionless(monkeypatch, tmp_path):
    _patch_matrix(monkeypatch)
    monkeypatch.setattr(transfer, "_arm_metrics", lambda records, arm: {"failure_detection_auroc": _stats(0.9 if arm == "learned_h_summary_head" else 0.5)})
    monkeypatch.setattr(transfer, "_delta_stats", lambda records, key: _stats(0.4, 0.4, 0.4))
    _sidecar(tmp_path)

    transfer.write_dimension_mismatch_debt_transfer(root=tmp_path, generated_at="fixture-time")
    artifacts = _generated_run_artifacts(tmp_path)
    claim_capsule = _read_json(artifacts["claim_capsule"])
    text = json.dumps(
        {
            "negative_witness": claim_capsule["run_local"]["negative_witness"],
            "negative_witness_hardgates": claim_capsule["run_local"]["negative_witness_hardgates"],
            "summary": _read_json(artifacts["summary"]),
        },
        sort_keys=True,
    )

    assert "v2" not in text.lower()
    assert "issue" not in text.lower()
    assert "786" not in text
    assert ".refactor-loop/host.env" not in text
    assert "discovery_negative_witnesses.json" not in text

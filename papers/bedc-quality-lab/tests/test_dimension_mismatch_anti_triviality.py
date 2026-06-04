import json
from pathlib import Path

import numpy as np

import bedc_quality_lab
from bedc_quality_lab.schema import SCHEMA_ID
from scripts import run_canonical_reports as canonical
from scripts import run_dimension_mismatch_anti_triviality as runner


ORIGINAL_BUILD_ARM_MATRICES = runner._build_arm_matrices


def _stat(mean, low=None, high=None):
    low = mean if low is None else low
    high = mean if high is None else high
    return {
        "n": 4,
        "mean": float(mean),
        "std": 0.0,
        "ci95_half_width": float((high - low) / 2.0),
        "ci95_low": float(low),
        "ci95_high": float(high),
    }


def _metrics(*, positive=False, wide_only=False, random_positive=False):
    if positive:
        return {
            "learned_auroc": _stat(0.88, 0.82, 0.94),
            "matched_random_auroc": _stat(0.52, 0.45, 0.58),
            "learned_minus_matched_random_auroc": _stat(0.36, 0.24, 0.48),
        }
    if wide_only:
        return {
            "learned_auroc": _stat(0.76, 0.76, 0.81),
            "matched_random_auroc": _stat(0.84, 0.80, 0.90),
            "learned_minus_matched_random_auroc": _stat(-0.08, -0.14, -0.02),
        }
    if random_positive:
        return {
            "learned_auroc": _stat(0.90, 0.84, 0.96),
            "matched_random_auroc": _stat(0.80, 0.76, 0.86),
            "learned_minus_matched_random_auroc": _stat(0.10, 0.02, 0.18),
        }
    return {
        "learned_auroc": _stat(0.55, 0.48, 0.62),
        "matched_random_auroc": _stat(0.52, 0.45, 0.58),
        "learned_minus_matched_random_auroc": _stat(0.03, -0.04, 0.10),
    }


def _surface_fixture():
    rows = []
    labels = []
    for encoder_dim in (1, 2, 3, 4):
        is_reference = encoder_dim == 2
        row = {column: float(index + encoder_dim) for index, column in enumerate(runner.SCALE_ONLY_COLUMNS)}
        row.update({column: float(index + encoder_dim) / 10.0 for index, column in enumerate(runner.H_NORMALIZED_NO_SCALE_COLUMNS)})
        row.update(
            {
                "encoder_dim": float(encoder_dim),
                "reference_latent_dim": 2.0,
                "abs_encoder_dim_minus_reference_dim": float(abs(encoder_dim - 2)),
                "is_reference_encoder_dim": 1.0 if is_reference else 0.0,
            }
        )
        rows.append(row)
        labels.append([0.0 if is_reference else 1.0, 0.0, 0.0, 1.0 if is_reference else 0.0])
    return {
        "rows": rows,
        "labels": np.asarray(labels, dtype=np.float64),
        "prediction_error": np.asarray([row[0] for row in labels], dtype=np.float64),
        "evidence_rows": [],
    }


def _source_artifact(root, status="pass"):
    path = root / runner.SOURCE_ARTIFACT
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(
            {
                "dimension_mismatch_debt_transfer": {
                    "status": status,
                    "base_level": "D4",
                    "anti_triviality_status": "scale_leakage_detected",
                    "effective_level": "DN",
                    "downgrade_reason": "scale_only_or_metadata_proxy_sufficient",
                    "terminal_verdict": "negative_discovery",
                    "discovery_level": "DN",
                }
            }
        ),
        encoding="utf-8",
    )


def _patch_metrics(monkeypatch, by_arm):
    monkeypatch.setattr(runner, "_build_arm_matrices", lambda: ORIGINAL_BUILD_ARM_MATRICES(_surface_fixture()))
    monkeypatch.setattr(runner, "_run_arm", lambda matrix: by_arm[matrix["arm"]])


def test_three_arm_construction_exact_columns_and_metadata_exclusions():
    matrices = runner._build_arm_matrices(_surface_fixture())

    assert tuple(matrices) == runner.ARM_ORDER
    assert tuple(matrices["config_metadata_only"]["feature_columns"]) == (
        "encoder_dim",
        "reference_latent_dim",
        "abs_encoder_dim_minus_reference_dim",
        "is_reference_encoder_dim",
    )
    for forbidden in runner.FORBIDDEN_METADATA_COLUMNS:
        assert forbidden not in matrices["config_metadata_only"]["feature_columns"]
    assert tuple(matrices["scale_only"]["feature_columns"]) == runner.SCALE_ONLY_COLUMNS
    assert tuple(matrices["h_normalized_no_scale"]["feature_columns"]) == runner.H_NORMALIZED_NO_SCALE_COLUMNS


def test_hg_b1_at1_per_arm_forbidden_feature_audit():
    assert runner._forbidden_feature_audit("config_metadata_only", runner.CONFIG_METADATA_ONLY_COLUMNS)["status"] == "pass"
    assert runner._forbidden_feature_audit("scale_only", runner.SCALE_ONLY_COLUMNS)["status"] == "pass"
    assert runner._forbidden_feature_audit("h_normalized_no_scale", runner.H_NORMALIZED_NO_SCALE_COLUMNS)["status"] == "pass"

    bad_metadata = runner._forbidden_feature_audit(
        "config_metadata_only",
        tuple(runner.CONFIG_METADATA_ONLY_COLUMNS) + ("signed_encoder_dim_minus_reference_dim",),
    )
    bad_scale = runner._forbidden_feature_audit(
        "scale_only",
        tuple(runner.SCALE_ONLY_COLUMNS) + ("encoder_dim",),
    )

    assert bad_metadata["status"] == "fail"
    assert "signed_encoder_dim_minus_reference_dim" in bad_metadata["forbidden_present"]
    assert bad_scale["status"] == "fail"
    assert "encoder_dim" in bad_scale["forbidden_present"]


def test_hg_b1_at2_deterministic_config_metadata_folds(tmp_path, monkeypatch):
    _source_artifact(tmp_path)
    _patch_metrics(
        monkeypatch,
        {
            "config_metadata_only": _metrics(),
            "scale_only": _metrics(),
            "h_normalized_no_scale": _metrics(positive=True),
        },
    )

    first = runner.build_payload(root=tmp_path, generated_at="fixture-time")
    second = runner.build_payload(root=tmp_path, generated_at="fixture-time")

    assert first["config"]["fold_seeds"] == list(runner.FOLD_SEEDS)
    assert first["hardgate_evidence"]["HG-B1-AT2"]["status"] == "pass"
    assert first["arms"] == second["arms"]


def test_hg_b1_at3_metadata_non_positive_does_not_demote_and_positive_is_reachable(tmp_path, monkeypatch):
    _source_artifact(tmp_path)
    _patch_metrics(
        monkeypatch,
        {
            "config_metadata_only": _metrics(),
            "scale_only": _metrics(),
            "h_normalized_no_scale": _metrics(positive=True),
        },
    )
    payload = runner.build_payload(root=tmp_path, generated_at="fixture-time")
    assert payload["status"] == "anti_triviality_passed"
    assert payload["hardgate_evidence"]["HG-B1-AT3"]["status"] == "pass"

    _patch_metrics(
        monkeypatch,
        {
            "config_metadata_only": _metrics(positive=True),
            "scale_only": _metrics(),
            "h_normalized_no_scale": _metrics(positive=True),
        },
    )
    demoted = runner.build_payload(root=tmp_path, generated_at="fixture-time")
    assert demoted["status"] == "metadata_leakage_detected"
    assert demoted["recommended_projection"] == "demote_to_DN_or_D1"
    assert demoted["hardgate_evidence"]["HG-B1-AT3"]["status"] == "fail"


def test_hg_b1_at4_status_precedence_five_states_and_metadata_beats_scale(tmp_path, monkeypatch):
    _source_artifact(tmp_path, status="failed")
    _patch_metrics(
        monkeypatch,
        {
            "config_metadata_only": _metrics(positive=True),
            "scale_only": _metrics(positive=True),
            "h_normalized_no_scale": _metrics(positive=True),
        },
    )
    assert runner.build_payload(root=tmp_path, generated_at="fixture-time")["status"] == "source_not_pass"

    _source_artifact(tmp_path)
    assert runner.build_payload(root=tmp_path, generated_at="fixture-time")["status"] == "metadata_leakage_detected"

    _patch_metrics(
        monkeypatch,
        {
            "config_metadata_only": _metrics(),
            "scale_only": _metrics(positive=True),
            "h_normalized_no_scale": _metrics(positive=True),
        },
    )
    assert runner.build_payload(root=tmp_path, generated_at="fixture-time")["status"] == "scale_leakage_detected"

    _patch_metrics(
        monkeypatch,
        {
            "config_metadata_only": _metrics(),
            "scale_only": _metrics(),
            "h_normalized_no_scale": _metrics(positive=True),
        },
    )
    assert runner.build_payload(root=tmp_path, generated_at="fixture-time")["status"] == "anti_triviality_passed"

    _patch_metrics(
        monkeypatch,
        {
            "config_metadata_only": _metrics(),
            "scale_only": _metrics(),
            "h_normalized_no_scale": _metrics(),
        },
    )
    deferred = runner.build_payload(root=tmp_path, generated_at="fixture-time")
    assert deferred["status"] == "defer_no_normalized_signal"
    assert deferred["hardgate_evidence"]["HG-B1-AT4"]["precedence_order"] == list(runner.STATUS_PRECEDENCE)


def test_hg_b1_at5_strict_conjunction_only_and_wide_or_diagnostic(tmp_path, monkeypatch):
    _source_artifact(tmp_path)
    _patch_metrics(
        monkeypatch,
        {
            "config_metadata_only": _metrics(wide_only=True),
            "scale_only": _metrics(),
            "h_normalized_no_scale": _metrics(wide_only=True),
        },
    )

    payload = runner.build_payload(root=tmp_path, generated_at="fixture-time")
    metadata = next(arm for arm in payload["arms"] if arm["arm"] == "config_metadata_only")
    normalized = next(arm for arm in payload["arms"] if arm["arm"] == "h_normalized_no_scale")

    assert metadata["diagnostic_only"]["wide_or_positive"] is True
    assert metadata["positive"] is False
    assert normalized["diagnostic_only"]["wide_or_positive"] is True
    assert normalized["positive"] is False
    assert payload["status"] == "defer_no_normalized_signal"
    assert payload["hardgate_evidence"]["HG-B1-AT5"]["status"] == "pass"
    assert payload["positive_predicate"]["wide_or_rule"] == "diagnostic_only"


def test_hg_b1_at6_sidecar_boundary_and_schema_invariants(tmp_path, monkeypatch):
    _source_artifact(tmp_path)
    _patch_metrics(
        monkeypatch,
        {
            "config_metadata_only": _metrics(),
            "scale_only": _metrics(),
            "h_normalized_no_scale": _metrics(positive=True),
        },
    )

    payload = runner.write_dimension_mismatch_anti_triviality(root=tmp_path, generated_at="fixture-time")
    text = json.dumps(payload).lower()
    canonical_jsons = {spec.json_artifact for spec in canonical.CANONICAL_REPORTS}

    assert payload["mechanism_status"] == "not_claimed"
    assert payload["d5m_status"] == "not_claimed"
    assert payload["sidecar_role"] == "folded_evidence_source"
    assert "No standalone positive discovery-map promotion from this evidence source." in payload["not_claimed"]
    assert runner.JSON_ARTIFACT not in canonical_jsons
    assert "dimension_mismatch_anti_triviality" not in json.dumps([spec.name for spec in canonical.CANONICAL_REPORTS])
    assert payload["schema_id"] == runner.SCHEMA_ID
    assert payload["schema_id"] != SCHEMA_ID
    assert payload["claim_term_audit"]["status"] == "pass"
    for term in runner.FORBIDDEN_POSITIVE_PAYLOAD_TERMS:
        assert term not in text
    assert "total score" not in text
    assert "hidden cost weight" not in text
    assert (tmp_path / runner.JSON_ARTIFACT).exists()
    assert (tmp_path / runner.REPORT_ARTIFACT).exists()
    assert Path(runner.JSON_ARTIFACT).parts[0] == "reports"
    assert "canonical" not in Path(runner.JSON_ARTIFACT).parts


def test_artifact_does_not_overwrite_canonical_row_and_package_exports_unchanged(tmp_path, monkeypatch):
    _source_artifact(tmp_path)
    canonical_path = tmp_path / "reports/canonical/dimension-mismatch-debt-transfer.json"
    before = canonical_path.read_text(encoding="utf-8")
    _patch_metrics(
        monkeypatch,
        {
            "config_metadata_only": _metrics(),
            "scale_only": _metrics(),
            "h_normalized_no_scale": _metrics(positive=True),
        },
    )

    runner.write_dimension_mismatch_anti_triviality(root=tmp_path, generated_at="fixture-time")

    assert canonical_path.read_text(encoding="utf-8") == before
    assert SCHEMA_ID == "bedc-quality-lab:evidence-envelope"
    assert bedc_quality_lab.__all__ == ["QualityEvidenceEnvelope"]

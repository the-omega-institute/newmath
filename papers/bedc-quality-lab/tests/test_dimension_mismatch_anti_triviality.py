import json
from pathlib import Path

import numpy as np

import bedc_quality_lab
from bedc_quality_lab.schema import SCHEMA_ID
from bedc_quality_lab.discovery_compiler.pointers import pointer_value
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
    full_by_arm = {arm: _metrics() for arm in runner.ARM_ORDER}
    full_by_arm.update(by_arm)
    if "h_normalized_no_scale" in by_arm and "whitened_h_normalized_no_scale" not in by_arm:
        full_by_arm["whitened_h_normalized_no_scale"] = by_arm["h_normalized_no_scale"]
    monkeypatch.setattr(runner, "_build_arm_matrices", lambda: ORIGINAL_BUILD_ARM_MATRICES(_surface_fixture()))
    monkeypatch.setattr(runner, "_run_arm", lambda matrix: full_by_arm[matrix["arm"]])


def _recursive_keys(value):
    if isinstance(value, dict):
        for key, item in value.items():
            yield key
            yield from _recursive_keys(item)
    elif isinstance(value, list):
        for item in value:
            yield from _recursive_keys(item)


def test_six_family_construction_exact_columns_and_metadata_exclusions():
    matrices = runner._build_arm_matrices(_surface_fixture())

    assert tuple(matrices) == runner.ARM_ORDER
    assert tuple(matrices) == (
        "config_metadata_only",
        "scale_only",
        "h_normalized_no_scale",
        "whitened_h_normalized_no_scale",
        "deterministic_random_projection",
        "rank_proxy_diagnostic",
    )
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
    assert tuple(matrices["whitened_h_normalized_no_scale"]["feature_columns"]) == runner.WHITENED_H_NORMALIZED_NO_SCALE_COLUMNS
    assert tuple(matrices["deterministic_random_projection"]["feature_columns"]) == runner.DETERMINISTIC_RANDOM_PROJECTION_COLUMNS
    assert tuple(matrices["rank_proxy_diagnostic"]["feature_columns"]) == runner.RANK_PROXY_DIAGNOSTIC_COLUMNS


def test_local_row_l2_direction_helper():
    h = np.array([[3.0, 4.0], [0.0, 0.0]], dtype=np.float64)

    direction = runner._row_l2_direction(h)

    np.testing.assert_allclose(direction[0], [0.6, 0.8])
    np.testing.assert_allclose(direction[1], [0.0, 0.0])


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
    source_failed = runner.build_payload(root=tmp_path, generated_at="fixture-time")
    assert source_failed["status"] == "source_not_pass"
    assert source_failed["hardgate_evidence"]["HG-B1-AT4"]["status"] == "fail"
    assert source_failed["hardgate_evidence"]["HG-B1-AT4"]["fail_closed_reason"] == "selected status blocks positive anti-triviality"

    _source_artifact(tmp_path)
    metadata = runner.build_payload(root=tmp_path, generated_at="fixture-time")
    assert metadata["status"] == "metadata_leakage_detected"
    assert metadata["hardgate_evidence"]["HG-B1-AT4"]["status"] == "fail"
    assert metadata["hardgate_evidence"]["HG-B1-AT4"]["fail_closed_reason"] == "selected status blocks positive anti-triviality"

    _patch_metrics(
        monkeypatch,
        {
            "config_metadata_only": _metrics(),
            "scale_only": _metrics(positive=True),
            "h_normalized_no_scale": _metrics(positive=True),
        },
    )
    scale = runner.build_payload(root=tmp_path, generated_at="fixture-time")
    assert scale["status"] == "scale_leakage_detected"
    assert scale["hardgate_evidence"]["HG-B1-AT4"]["status"] == "fail"
    assert scale["hardgate_evidence"]["HG-B1-AT4"]["fail_closed_reason"] == "selected status blocks positive anti-triviality"

    _patch_metrics(
        monkeypatch,
        {
            "config_metadata_only": _metrics(),
            "scale_only": _metrics(),
            "h_normalized_no_scale": _metrics(positive=True),
        },
    )
    passed = runner.build_payload(root=tmp_path, generated_at="fixture-time")
    assert passed["status"] == "anti_triviality_passed"
    assert passed["hardgate_evidence"]["HG-B1-AT4"]["status"] == "pass"
    assert passed["hardgate_evidence"]["HG-B1-AT4"]["fail_closed_reason"] is None

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
    assert deferred["hardgate_evidence"]["HG-B1-AT4"]["status"] == "fail"
    assert deferred["hardgate_evidence"]["HG-B1-AT4"]["fail_closed_reason"] == "selected status blocks positive anti-triviality"
    assert deferred["hardgate_evidence"]["HG-B1-AT4"]["precedence_order"] == list(runner.STATUS_PRECEDENCE)


def test_random_projection_positive_status_is_computed_from_owner_runner(tmp_path, monkeypatch):
    _source_artifact(tmp_path)
    _patch_metrics(
        monkeypatch,
        {
            "config_metadata_only": _metrics(),
            "scale_only": _metrics(),
            "h_normalized_no_scale": _metrics(),
            "whitened_h_normalized_no_scale": _metrics(),
            "deterministic_random_projection": _metrics(positive=True),
        },
    )

    payload = runner.build_payload(root=tmp_path, generated_at="fixture-time")
    arm_positive = payload["hardgate_evidence"]["HG-B1-AT4"]["arm_positive"]

    assert payload["status"] == "random_projection_positive"
    assert payload["recommended_projection"] == "defer"
    assert arm_positive["config_metadata_only"] is False
    assert arm_positive["scale_only"] is False
    assert arm_positive["h_normalized_no_scale"] is False
    assert arm_positive["whitened_h_normalized_no_scale"] is False
    assert arm_positive["deterministic_random_projection"] is True
    assert payload["hardgate_evidence"]["HG-B1-AT4"]["selected_status"] == "random_projection_positive"


def test_whitening_failure_status_is_computed_from_owner_runner(tmp_path, monkeypatch):
    _source_artifact(tmp_path)
    _patch_metrics(
        monkeypatch,
        {
            "config_metadata_only": _metrics(),
            "scale_only": _metrics(),
            "h_normalized_no_scale": _metrics(positive=True),
            "whitened_h_normalized_no_scale": _metrics(),
            "deterministic_random_projection": _metrics(),
        },
    )

    payload = runner.build_payload(root=tmp_path, generated_at="fixture-time")
    arm_positive = payload["hardgate_evidence"]["HG-B1-AT4"]["arm_positive"]

    assert payload["status"] == "whitening_failure_detected"
    assert payload["recommended_projection"] == "defer"
    assert arm_positive["config_metadata_only"] is False
    assert arm_positive["scale_only"] is False
    assert arm_positive["h_normalized_no_scale"] is True
    assert arm_positive["whitened_h_normalized_no_scale"] is False
    assert arm_positive["deterministic_random_projection"] is False
    assert payload["hardgate_evidence"]["HG-B1-AT4"]["selected_status"] == "whitening_failure_detected"


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


def test_diagnostics_are_recorded_for_whitening_projection_and_rank_proxy(tmp_path, monkeypatch):
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
    by_arm = {row["arm"]: row for row in payload["arms"]}

    assert by_arm["whitened_h_normalized_no_scale"]["diagnostics"]["whitening"]["status"] == "pass"
    assert by_arm["deterministic_random_projection"]["diagnostics"]["deterministic_random_projection"]["projection_seed"] == runner.RANDOM_PROJECTION_SEED
    assert by_arm["deterministic_random_projection"]["diagnostics"]["deterministic_random_projection"]["projection_width"] == runner.RANDOM_PROJECTION_WIDTH
    assert by_arm["rank_proxy_diagnostic"]["diagnostics"]["rank_proxy"]["status"] == "pass"


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


def test_b2_controlled_geometry_sidecar_has_resolvable_evidence_pointers(tmp_path, monkeypatch):
    _source_artifact(tmp_path)
    _patch_metrics(
        monkeypatch,
        {
            "config_metadata_only": _metrics(),
            "scale_only": _metrics(positive=True),
            "h_normalized_no_scale": _metrics(positive=True),
        },
    )

    payload = runner.write_dimension_mismatch_anti_triviality(root=tmp_path, generated_at="fixture-time")

    assert set(payload["controlled_geometry_hardgates"]) == {"B2-HG1", "B2-HG2", "B2-HG3", "B2-HG4", "B2-HG5", "B2-HG6"}
    assert payload["controlled_geometry_pointer_contract"]["source_artifact"] == runner.JSON_ARTIFACT
    assert payload["controlled_geometry"]["control_family_coverage"]["status"] == "pass"
    assert payload["controlled_geometry"]["control_family_coverage"]["required_families"] == list(runner.ARM_ORDER)
    assert payload["controlled_geometry"]["control_family_coverage"]["observed_families"] == list(runner.ARM_ORDER)
    assert set(payload["controlled_geometry"]["control_family_coverage"]["family_pointers"]) == set(runner.ARM_ORDER)
    assert payload["controlled_geometry"]["artifact_boundary"]["writes_claim_capsule"] is False
    assert payload["controlled_geometry"]["artifact_boundary"]["writes_run_local_bundle"] is False
    assert payload["controlled_geometry"]["artifact_boundary"]["writes_claim_outcome"] is False
    for gate_name, gate in payload["controlled_geometry_hardgates"].items():
        assert gate["status"] == "pass"
        assert pointer_value(payload, gate["source_pointer"]) is not None, gate_name
    for row in payload["controlled_geometry"]["evidence_refs"]:
        assert row["source_artifact"] == runner.JSON_ARTIFACT
        assert row["controlled_geometry_artifact"] == runner.JSON_ARTIFACT
        assert pointer_value(payload, row["source_pointer"]) is not None, row
        assert pointer_value(payload, row["controlled_geometry_pointer"]) is not None, row
    assert [row["evidence_id"] for row in payload["controlled_geometry"]["evidence_refs"]] == list(
        payload["controlled_geometry_hardgates"]
    )
    report = (tmp_path / runner.REPORT_ARTIFACT).read_text(encoding="utf-8")
    assert (
        "- `$.controlled_geometry_hardgates` records "
        f"{', '.join(payload['controlled_geometry_hardgates'])}."
    ) in report


def test_control_family_coverage_defers_when_a_family_is_missing(tmp_path, monkeypatch):
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

    controlled = runner._controlled_geometry(payload["arms"][:-1])

    assert controlled["controlled_geometry"]["control_family_coverage"]["status"] == "defer"
    assert controlled["controlled_geometry_hardgates"]["B2-HG6"]["status"] == "defer"


def test_dimension_mismatch_sidecar_and_backend_do_not_write_terminal_verdict(tmp_path, monkeypatch):
    _source_artifact(tmp_path)
    _patch_metrics(
        monkeypatch,
        {
            "config_metadata_only": _metrics(),
            "scale_only": _metrics(positive=True),
            "h_normalized_no_scale": _metrics(positive=True),
        },
    )

    payload = runner.write_dimension_mismatch_anti_triviality(root=tmp_path, generated_at="fixture-time")
    keys = set(_recursive_keys(payload))

    assert "terminal_verdict" not in keys
    assert "claim_id" not in keys
    assert "run_local" not in keys
    assert "claim_capsule_ref" not in keys


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

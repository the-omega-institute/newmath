import json

import numpy as np
import pytest

from bedc_quality_lab import __all__ as package_all
from bedc_quality_lab.schema import SCHEMA_ID
from scripts.experiment_stats import metric_stats
from scripts import run_canonical_reports as canonical
from scripts import run_gap_head_mechanism_attribution as runner
from scripts import run_gap_ledger_head_on_h as producer


def _stat(value):
    return metric_stats([float(value)] * 4)


def _arm_row(auroc, reduction):
    return {
        "record_count": 4,
        "feature_roots": ["fixture"],
        "feature_column_count": 1,
        "alias_of": None,
        "gating_role": "gating_candidate",
        "control_role": None,
        "forbidden_feature_audit": {"status": "pass", "forbidden_present": []},
        "learned": {
            "failure_detection_auroc": _stat(auroc),
            "unlogged_error_rate": _stat(0.5 - reduction),
            "unlogged_error_reduction": _stat(reduction),
        },
        "matched_random": {
            "failure_detection_auroc": _stat(0.51),
            "unlogged_error_rate": _stat(0.49),
            "unlogged_error_reduction": _stat(0.01),
        },
        "learned_minus_matched_random_auroc": _stat(auroc - 0.51),
    }


def _aggregate_fixture(**overrides):
    values = {
        "full": (0.86, 0.40),
        "h_only": (0.80, 0.30),
        "h_direction_only": (0.78, 0.28),
        "h_norm_only": (0.55, 0.02),
        "h_normalized_no_scale": (0.78, 0.28),
        "score_only": (0.55, 0.02),
        "margin_only": (0.55, 0.02),
        "transition_delta_only": (0.55, 0.02),
        "quality_scalars_only": (0.55, 0.02),
        "score_plus_margin": (0.56, 0.03),
        "h_plus_margin": (0.60, 0.10),
        "h_plus_transition": (0.60, 0.10),
        "full_without_margin": (0.60, 0.10),
        "full_without_transition": (0.60, 0.10),
        "full_without_quality_scalars": (0.60, 0.10),
        "matched_random": (0.51, 0.01),
    }
    values.update(overrides)
    by_arm = {arm: _arm_row(*values[arm]) for arm in runner.ARM_NAMES}
    by_arm["h_normalized_no_scale"]["alias_of"] = "h_direction_only"
    by_arm["h_normalized_no_scale"]["gating_role"] = "non_gating_alias"
    return {
        "record_count": 4 * len(runner.ARM_NAMES),
        "seed_order": [1, 2, 3, 4],
        "arm_order": list(runner.ARM_NAMES),
        "by_arm": by_arm,
    }


def test_fixed_arm_table_and_direction_norm_alias_projection():
    columns = producer._feature_columns(2)
    features = np.array(
        [
            [3.0, 4.0, 0.1, 0.2, 0.3, 0.4, 1.1, 1.2, 1.3, 1.4, 2.1, 2.2, 2.3, 2.4, 2.5],
            [0.0, 0.0, 0.5, 0.6, 0.7, 0.8, 1.5, 1.6, 1.7, 1.8, 2.6, 2.7, 2.8, 2.9, 3.0],
        ],
        dtype=np.float64,
    )
    surface = {"features": features, "feature_columns": columns}

    matrices = runner._arm_feature_matrices(surface)

    assert tuple(matrices) == runner.ARM_NAMES
    np.testing.assert_allclose(matrices["h_direction_only"]["features"][0], [0.6, 0.8])
    np.testing.assert_allclose(matrices["h_direction_only"]["features"][1], [0.0, 0.0])
    np.testing.assert_allclose(matrices["h_norm_only"]["features"].ravel(), [5.0, 0.0])
    assert matrices["h_normalized_no_scale"]["features"] is matrices["h_direction_only"]["features"]
    assert matrices["h_normalized_no_scale"]["alias_of"] == "h_direction_only"
    assert matrices["h_normalized_no_scale"]["gating_role"] == "non_gating_alias"
    assert "h_normalized_no_scale" not in runner.GATING_ARMS
    assert matrices["score_only"]["features"].shape == (2, len(producer.DISTINCTIONS))
    assert matrices["margin_only"]["features"].shape == (2, len(producer.DISTINCTIONS))
    assert matrices["transition_delta_only"]["features"].shape == (2, len(producer.DISTINCTIONS))
    assert matrices["quality_scalars_only"]["features"].shape == (2, 4)


def test_forbidden_column_audit_reuses_source_assertion():
    assert runner._forbidden_feature_audit(["h:0", "score:latent_x_positive"])["status"] == "pass"
    with pytest.raises(ValueError, match="forbidden inference column"):
        runner._forbidden_feature_audit(["h:0", "z"])


def test_hg_a1_d5_m_candidate_closure():
    result = runner._hg_a1_gates(_aggregate_fixture())

    assert result["mechanism_status"] == "D5-M_candidate"
    assert result["status"] == "pass"
    assert result["gates"]["HG-A1-1"]["status"] == "pass"
    assert result["gates"]["HG-A1-2"]["status"] == "pass"
    assert result["gates"]["HG-A1-3"]["status"] == "pass"
    assert result["gates"]["HG-A1-4"]["status"] == "pass"


def test_hg_a1_scale_only_downgrades_and_blocks_d5_m():
    result = runner._hg_a1_gates(_aggregate_fixture(h_norm_only=(0.85, 0.39)))

    assert result["mechanism_status"] == "scale-dominated-h-norm"
    assert result["demotion_channel"] == "h_norm_only"
    assert result["gates"]["HG-A1-2"]["status"] == "fail"


def test_hg_a1_margin_channel_downgrades():
    result = runner._hg_a1_gates(_aggregate_fixture(score_plus_margin=(0.85, 0.39)))

    assert result["mechanism_status"] == "probe-margin-channel"
    assert result["demotion_channel"] == "score_plus_margin"
    assert result["gates"]["HG-A1-3"]["status"] == "fail"


def test_hg_a1_single_channel_demote_excludes_alias():
    result = runner._hg_a1_gates(_aggregate_fixture(score_only=(0.85, 0.39)))

    assert result["mechanism_status"] == "demote_single_channel_explanation"
    assert result["demotion_channel"] == "score_only"
    assert "h_normalized_no_scale" in result["gates"]["HG-A1-5"]["excluded_alias_demotions"]


def test_hg_a1_positive_but_key_ablation_open_is_d5_o_not_d5_m():
    result = runner._hg_a1_gates(_aggregate_fixture(full_without_margin=(0.84, 0.20)))

    assert result["mechanism_status"] == "D5-O_not_D5-M"
    assert result["gates"]["HG-A1-4"]["status"] == "fail"


def test_payload_is_pointer_only_and_keeps_boundary_identifiers():
    config = producer.GapHeadRunConfig(
        sample_count=12,
        seeds=(),
        rho=0.7,
        use_torch=False,
        json_artifact=runner.JSON_ARTIFACT,
        report_artifact=runner.REPORT_ARTIFACT,
        run_id_prefix="fixture",
        source_artifact_label="fixture",
    )
    metadata = runner._alias_metadata()
    source = runner._source_artifacts(config)

    assert runner.ARTIFACT_ID == "bedc-quality-lab:gap-head-mechanism-attribution"
    assert source["canonical_status"] == "sidecar_not_canonical"
    assert metadata["h_normalized_no_scale"] == {
        "alias_of": "h_direction_only",
        "implementation": "row_l2_unit_direction",
        "train_split_centering": False,
        "gating_role": "non_gating_alias",
        "participates_in_HG_A1_2_to_4": False,
        "independent_HG_A1_5_demotion_channel": False,
    }
    text = json.dumps({"metadata": metadata, "source": source}).lower()
    assert "discovery score" not in text
    assert "global grade" not in text
    assert SCHEMA_ID == "bedc-quality-lab:evidence-envelope"
    assert package_all == ["QualityEvidenceEnvelope"]


def test_canonical_index_adds_sidecar_without_manifest_or_discovery_map_changes(tmp_path, monkeypatch):
    sidecar = tmp_path / runner.JSON_ARTIFACT
    sidecar.parent.mkdir(parents=True)
    sidecar.write_text(
        json.dumps(
            {
                "artifact_id": runner.ARTIFACT_ID,
                "mechanism_status": "D5-O_not_D5-M",
                "config": {"arm_count": 16},
                "HG_A1": {"status": "fail"},
            }
        ),
        encoding="utf-8",
    )
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    names = [spec.name for spec in canonical.CANONICAL_REPORTS]

    section = canonical._gap_head_mechanism_attribution_index_section()
    payload = canonical._index([])
    markdown = canonical._render_index_markdown(payload)

    assert "gap-head-mechanism-attribution" not in names
    assert section["artifact_id"] == runner.ARTIFACT_ID
    assert section["canonical_role"] == "sidecar_not_in_CANONICAL_REPORTS"
    assert payload["gap_head_mechanism_attribution"]["mechanism_status"] == "D5-O_not_D5-M"
    assert "Gap-head mechanism attribution" in markdown
    assert "d5_readiness" not in json.dumps(payload)
    assert "gap_head_mechanism_attribution" not in json.dumps(payload["discovery_map"])

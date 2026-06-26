import json
from pathlib import Path

import numpy as np

import bedc_quality_lab
from bedc_quality_lab.schema import SCHEMA_ID
from scripts import run_canonical_reports as canonical
from scripts import run_sigreg_gaussianity_reproduction as sigreg


def _small_payload(**kwargs):
    params = {
        "generated_at": "fixture-time",
        "sample_count": 2048,
        "seeds": (11, 23, 37, 53, 71, 89),
        "directions": 32,
        "frequencies": (0.5, 1.0, 1.5, 2.0),
        "bootstrap_resamples": 400,
        "bootstrap_seed": 680,
    }
    params.update(kwargs)
    return sigreg.build_payload(**params)


def _ci_low(payload, family):
    by_family = {cell["family"]: cell for cell in payload["paired_ci_cells"]}
    return by_family[family]["non_gaussian_minus_gaussian_sigreg_penalty"]["ci95_low"]


def test_hg_f1_gaussian_vs_laplace_paired_ci_low_is_positive():
    payload = _small_payload()

    assert _ci_low(payload, "laplace") > 0.0
    assert payload["hardgate_evidence"]["HG-F1"]["status"] == "pass"


def test_predeclared_non_gaussian_cells_separate_from_gaussian():
    payload = _small_payload()

    for family in ("laplace", "uniform", "student_t_df3", "generalized_normal_alpha4"):
        assert _ci_low(payload, family) > 0.0


def test_collapse_and_isometry_guard_fail_closed():
    probe = sigreg.SlicedCFGaussianityProbe(
        directions=8,
        frequencies=(0.5, 1.0),
        guard_thresholds=sigreg.GuardThresholds(
            cov_to_identity_max=0.20,
            min_cov_eigenvalue_floor=0.80,
            min_projected_variance_floor=0.70,
        ),
    )
    collapsed = np.column_stack(
        [
            np.linspace(-1.0, 1.0, 256),
            np.zeros(256),
        ]
    )

    score = probe.score(collapsed, seed=11)

    assert score["guard_status"] == "fail"
    assert "min_cov_eigenvalue_below_floor" in score["guard_reasons"]
    assert "min_projected_variance_below_floor" in score["guard_reasons"]


def test_statistic_path_rejects_forbidden_features():
    probe = sigreg.SlicedCFGaussianityProbe(directions=8, frequencies=(0.5, 1.0))
    h = np.random.default_rng(11).normal(size=(128, 2))

    score = probe.score(h, seed=11, features={"z": h.copy(), "labels": np.zeros(128)})

    assert score["guard_status"] == "fail"
    assert score["forbidden_feature_audit"]["status"] == "fail"
    assert score["forbidden_feature_audit"]["forbidden_keys"] == ["labels", "z"]


def test_proxy_contrast_preserves_disagreement_without_promotion():
    payload = _small_payload()
    rows = payload["proxy_contrast"]["rows"]

    assert payload["proxy_contrast"]["status"] == "reported_not_promoted"
    assert payload["verdict"]["promotion"] == "none"
    assert any(row["status"] == "disagreement_preserved" for row in rows)


def test_failed_ci_fixture_demotes_to_negative_compression():
    cells = [
        {
            "family": "laplace",
            "hg_f1_status": "fail",
            "non_gaussian_minus_gaussian_sigreg_penalty": {"ci95_low": -0.01},
            "non_gaussian_minus_gaussian_proxy_whitening_deviation": {"ci95_low": 0.01},
        }
    ]
    records = [
        {
            "arm_id": "gaussian",
            "seed": 11,
            "guard_status": "ok",
            "guard_reasons": [],
            "forbidden_feature_audit": {"status": "pass"},
        }
    ]
    proxy = sigreg._proxy_contrast(cells)
    hardgates = sigreg._hardgates(records=records, cells=cells, proxy_contrast=proxy)

    verdict = sigreg._verdict(hardgates)

    assert hardgates["HG-F1"]["status"] == "fail"
    assert verdict["status"] == "negative/compression"
    assert verdict["promotion"] == "none"


def test_sidecar_is_pointer_only_and_local_schema_is_separate(tmp_path):
    payload = _small_payload(bootstrap_resamples=100)

    sigreg.write_artifacts(payload, root=tmp_path)
    written = json.loads((tmp_path / sigreg.JSON_ARTIFACT).read_text(encoding="utf-8"))

    assert written["schema_id"] == sigreg.LOCAL_SCHEMA_ID
    assert written["schema_id"] != SCHEMA_ID
    assert written["canonical_role"] == "sidecar_not_in_CANONICAL_REPORTS"
    assert bedc_quality_lab.__all__ == ["QualityEvidenceEnvelope"]
    assert sigreg.JSON_ARTIFACT not in [spec.json_artifact for spec in canonical.CANONICAL_REPORTS]
    assert Path(sigreg.JSON_ARTIFACT).parts[0] == "runs"

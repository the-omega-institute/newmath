import json
import math

import numpy as np
import pytest

from scripts import run_gaussian_ou_gap_ledger_head as runner


def test_default_config_matches_structural_protocol_b():
    assert runner.SEED_COUNT >= 20
    assert runner.BETA == 1.0
    assert runner.PRIMARY_EPSILON == 0.0
    assert runner.PRIMARY_TAU == 0.5
    assert runner.GAP_CHANNELS == (
        "prediction_error",
        "low_margin",
        "transition_unstable",
        "off_target_intervention",
    )


def test_gap_head_probability_shape_and_bounds_on_separable_fixture():
    x = np.array([[-2.0], [-1.0], [1.0], [2.0]], dtype=np.float64)
    labels = np.array(
        [
            [0.0, 1.0, 0.0, 0.0],
            [0.0, 1.0, 0.0, 0.0],
            [1.0, 0.0, 1.0, 1.0],
            [1.0, 0.0, 1.0, 1.0],
        ],
        dtype=np.float64,
    )

    heads = runner._fit_gap_head(x, labels, steps=300, lr=0.25)
    probabilities = runner._predict_gap_head(heads, x)

    assert probabilities.shape == labels.shape
    assert np.all(probabilities >= 0.0)
    assert np.all(probabilities <= 1.0)
    assert probabilities[0, 0] < 0.2
    assert probabilities[-1, 0] > 0.8


def test_gap_loss_is_bce_plus_beta_unlogged_error_penalty():
    labels = np.array([[1.0, 0.0, 0.0, 0.0], [0.0, 1.0, 0.0, 0.0]], dtype=np.float64)
    probabilities = np.array(
        [[0.25, 0.2, 0.1, 0.1], [0.75, 0.8, 0.1, 0.1]],
        dtype=np.float64,
    )
    prediction_error = np.array([1.0, 0.0], dtype=np.float64)

    loss = runner._gap_loss(labels, probabilities, prediction_error, beta=1.0)
    expected_bce = runner._binary_cross_entropy(labels.reshape(-1), probabilities.reshape(-1))

    assert loss["bce"] == pytest.approx(expected_bce)
    assert loss["unlogged_error_penalty"] == pytest.approx((1.0 - 0.25) / 2.0)
    assert loss["total"] == pytest.approx(expected_bce + (1.0 - 0.25) / 2.0)


def test_auroc_handles_perfect_reversed_and_degenerate_cases():
    labels = np.array([0.0, 0.0, 1.0, 1.0], dtype=np.float64)

    perfect = runner._auroc(labels, np.array([0.1, 0.2, 0.8, 0.9], dtype=np.float64))
    reversed_auc = runner._auroc(labels, np.array([0.9, 0.8, 0.2, 0.1], dtype=np.float64))
    constant_score = runner._auroc(labels, np.array([0.5, 0.5, 0.5, 0.5], dtype=np.float64))
    constant_label = runner._auroc(np.zeros(4), np.array([0.1, 0.2, 0.3, 0.4], dtype=np.float64))

    assert perfect == {"value": 1.0, "degenerate": False, "reason": "ok"}
    assert reversed_auc == {"value": 0.0, "degenerate": False, "reason": "ok"}
    assert constant_score == {"value": 0.5, "degenerate": True, "reason": "constant_score"}
    assert constant_label == {"value": 0.5, "degenerate": True, "reason": "constant_label"}


def test_ece_uses_fixed_bins_and_keeps_empty_bin_rows():
    labels = np.array([0.0, 1.0], dtype=np.float64)
    scores = np.array([0.1, 0.9], dtype=np.float64)

    ece = runner._ece(labels, scores, bins=5)

    assert ece["bins"] == 5
    assert len(ece["bin_rows"]) == 5
    assert ece["value"] == pytest.approx(0.1)
    assert ece["bin_rows"][2]["count"] == 0
    assert math.isnan(ece["bin_rows"][2]["confidence"])


def test_unlogged_error_and_gap_sound_primary_predicates():
    error = np.array([1.0, 1.0, 0.0, 0.0], dtype=np.float64)
    gap = np.array([0.2, 0.8, 0.1, 0.9], dtype=np.float64)

    assert runner._unlogged_error_rate(error, gap, tau=0.5) == pytest.approx(0.25)

    rows = runner._gap_sound_scan(error, gap)
    primary = runner._primary_gap_sound(rows)

    assert primary["tau"] == runner.PRIMARY_TAU
    assert primary["epsilon"] == runner.PRIMARY_EPSILON
    assert primary["low_gap_implies_error_within_epsilon"] == pytest.approx(0.5)
    assert primary["error_above_epsilon_implies_gap_at_least_tau"] == pytest.approx(0.5)


def test_vanilla_vs_gap_head_metrics_are_assembled_on_same_error_surface():
    labels = np.array(
        [[1.0, 0.0, 0.0, 0.0], [0.0, 1.0, 0.0, 0.0], [0.0, 0.0, 1.0, 0.0]],
        dtype=np.float64,
    )
    error = np.array([1.0, 0.0, 0.0], dtype=np.float64)
    vanilla = np.zeros_like(labels)
    gap = np.array(
        [[0.9, 0.1, 0.1, 0.1], [0.1, 0.9, 0.1, 0.1], [0.1, 0.1, 0.9, 0.1]],
        dtype=np.float64,
    )

    vanilla_metrics = runner._metrics_for_arm(
        arm="vanilla", probabilities=vanilla, labels=labels, prediction_error=error
    )
    gap_metrics = runner._metrics_for_arm(
        arm="gap_head", probabilities=gap, labels=labels, prediction_error=error
    )

    assert vanilla_metrics["prediction_error_rate"] == gap_metrics["prediction_error_rate"]
    assert vanilla_metrics["unlogged_error_rate"] == pytest.approx(1.0 / 3.0)
    assert gap_metrics["unlogged_error_rate"] == pytest.approx(0.0)


def test_payload_contains_json_evidence_boundary_and_negative_result():
    record = {
        "seed": 1,
        "arms": {
            "vanilla": {
                "failure_detection_auroc": {"value": 0.5},
                "ece": {"value": 0.5},
                "unlogged_error_rate": 0.5,
                "critical_unlogged_error_rate": 0.5,
                "prediction_error_rate": 0.5,
                "gap_sound_scan": [
                    {
                        "tau": runner.PRIMARY_TAU,
                        "epsilon": runner.PRIMARY_EPSILON,
                        "low_gap_implies_error_within_epsilon": 0.5,
                        "error_above_epsilon_implies_gap_at_least_tau": 0.0,
                    }
                ],
            },
            "gap_head": {
                "failure_detection_auroc": {"value": 0.5},
                "ece": {"value": 0.4},
                "unlogged_error_rate": 0.4,
                "critical_unlogged_error_rate": 0.3,
                "prediction_error_rate": 0.5,
                "gap_sound_scan": [
                    {
                        "tau": runner.PRIMARY_TAU,
                        "epsilon": runner.PRIMARY_EPSILON,
                        "low_gap_implies_error_within_epsilon": 0.6,
                        "error_above_epsilon_implies_gap_at_least_tau": 0.2,
                    }
                ],
            },
        },
        "comparison": {
            "unlogged_error_rate_delta_gap_minus_vanilla": -0.1,
            "critical_unlogged_error_rate_delta_gap_minus_vanilla": -0.2,
            "failure_detection_auroc_delta_gap_minus_vanilla": 0.0,
        },
    }

    payload = runner._payload([record])
    report = runner._render_report(payload)

    assert payload["source_artifacts"]["generation_script"] == (
        "scripts/run_gaussian_ou_gap_ledger_head.py"
    )
    assert payload["source_artifacts"]["distinction_head_runner"] == (
        "scripts/run_gaussian_ou_distinction_head.py"
    )
    assert payload["applicability_boundary"]["primary_epsilon"] == 0.0
    assert "approximately chance" in payload["negative_result_note"]
    assert "## Applicability Boundary" in report
    assert "## Negative Result Note" in report
    assert "UnloggedErrorRate" in report


def test_main_writes_json_and_markdown(monkeypatch, tmp_path):
    monkeypatch.setattr(runner, "ROOT", tmp_path)
    monkeypatch.setattr(
        runner,
        "_records",
        lambda: [
            {
                "seed": 1,
                "arms": {
                    arm: {
                        "failure_detection_auroc": {"value": 0.75},
                        "ece": {"value": 0.2},
                        "unlogged_error_rate": 0.1,
                        "critical_unlogged_error_rate": 0.1,
                        "prediction_error_rate": 0.2,
                        "gap_sound_scan": [
                            {
                                "tau": runner.PRIMARY_TAU,
                                "epsilon": runner.PRIMARY_EPSILON,
                                "low_gap_implies_error_within_epsilon": 0.9,
                                "error_above_epsilon_implies_gap_at_least_tau": 0.8,
                            }
                        ],
                    }
                    for arm in ("vanilla", "gap_head")
                },
                "comparison": {
                    "unlogged_error_rate_delta_gap_minus_vanilla": 0.0,
                    "critical_unlogged_error_rate_delta_gap_minus_vanilla": 0.0,
                    "failure_detection_auroc_delta_gap_minus_vanilla": 0.0,
                },
            }
        ],
    )

    runner.main()

    payload = json.loads((tmp_path / runner.JSON_ARTIFACT).read_text(encoding="utf-8"))
    report = (tmp_path / runner.REPORT_ARTIFACT).read_text(encoding="utf-8")

    assert payload["artifact"] == runner.JSON_ARTIFACT
    assert payload["aggregate"]["record_count"] == 1
    assert "# Gaussian-OU Gap-Ledger-Head Experiment" in report
    assert "Total records: `1`" in report


def test_non_finite_inputs_fail_closed():
    labels = np.array([[1.0, 0.0, 0.0, 0.0]], dtype=np.float64)
    probabilities = np.array([[float("nan"), 0.0, 0.0, 0.0]], dtype=np.float64)
    error = np.array([1.0], dtype=np.float64)

    with pytest.raises(ValueError, match="non-finite"):
        runner._gap_loss(labels, probabilities, error)


def test_does_not_mutate_schema_or_package_exports():
    import bedc_quality_lab
    from bedc_quality_lab.schema import SCHEMA_ID

    assert SCHEMA_ID == "bedc-quality-lab:evidence-envelope"
    assert hasattr(bedc_quality_lab, "QualityEvidenceEnvelope")
    assert not hasattr(bedc_quality_lab, "GapLedgerHead")

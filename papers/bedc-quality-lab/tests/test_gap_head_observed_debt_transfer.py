import json
from pathlib import Path

import numpy as np

from scripts import run_canonical_reports as canonical
from scripts import run_gap_head_observed_debt_transfer as transfer


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


def _surface():
    features = np.array(
        [
            [0.0, 0.0],
            [0.1, 0.0],
            [0.2, 0.1],
            [0.9, 1.0],
            [1.0, 1.0],
            [1.1, 0.9],
        ],
        dtype=np.float64,
    )
    labels = np.column_stack(
        [
            np.array([0, 0, 0, 1, 1, 1], dtype=np.float64),
            np.array([0, 1, 0, 1, 0, 1], dtype=np.float64),
            np.array([1, 0, 1, 0, 1, 0], dtype=np.float64),
            np.array([0, 0, 1, 1, 0, 1], dtype=np.float64),
        ]
    )
    return {
        "features": features,
        "feature_columns": ["h:0", "h:1"],
        "gap_labels": labels,
        "prediction_error": labels[:, 0],
        "train_idx": np.array([0, 1, 3, 4], dtype=np.int64),
        "eval_idx": np.array([2, 5], dtype=np.int64),
    }


def _patch_small_surface(monkeypatch):
    spec = transfer.TransferSurfaceSpec(
        surface_id="fixture",
        observed_debt_axis="C3",
        axis_label="sample_count",
        axis_value=6,
        observed_debt_row="source/finite-sample-support",
        observed_debt_metric="linear_identifiability_r2",
        observed_debt_scope="fixture finite sample observed debt",
        sample_count=6,
        seeds=(11,),
        rho=0.82,
        use_torch=False,
    )
    monkeypatch.setattr(transfer, "_default_surface_specs", lambda: (spec,))
    monkeypatch.setattr(transfer.producer, "_surface_for_seed", lambda *, seed, config: _surface())
    monkeypatch.setattr(transfer.producer, "_fit_gap_head", lambda x, labels: {"labels": labels.copy()})

    def fake_predict(heads, x):
        width = len(transfer.producer.GAP_CHANNELS)
        if np.array_equal(heads["labels"], _surface()["gap_labels"][[0, 1, 3, 4]]):
            return np.tile(np.array([[0.05, 0.1, 0.1, 0.1], [0.95, 0.9, 0.9, 0.9]]), (1, 1))
        return np.full((x.shape[0], width), 0.5, dtype=np.float64)

    monkeypatch.setattr(transfer.producer, "_predict_gap_head", fake_predict)
    monkeypatch.setattr(transfer.producer, "_matched_random_gap_labels", lambda labels, *, seed: 1.0 - labels)


def _patch_metrics(monkeypatch, *, learned_pass=True):
    learned_auroc = 0.9 if learned_pass else 0.55
    learned_unlogged = 0.2 if learned_pass else 0.8

    def fake_metrics_for_arm(*, arm, probabilities, labels, prediction_error):
        if arm == "vanilla":
            auroc = 0.5
            unlogged = 0.8
        elif arm == "learned_gap_head_on_h":
            auroc = learned_auroc
            unlogged = learned_unlogged
        else:
            auroc = 0.5
            unlogged = 0.8
        return {
            "arm": arm,
            "failure_detection_auroc": {"value": auroc},
            "ece": {"value": 0.0},
            "unlogged_error_rate": unlogged,
            "critical_unlogged_error_rate": unlogged,
            "prediction_error_rate": 0.5,
            "gap_score_mean": 0.5,
            "critical_gap_score_mean": 0.5,
            "gap_sound_scan": [
                {
                    "tau": transfer.producer.PRIMARY_TAU,
                    "epsilon": transfer.producer.PRIMARY_EPSILON,
                    "low_gap_implies_error_within_epsilon": 1.0,
                    "error_above_epsilon_implies_gap_at_least_tau": 1.0,
                    "low_gap_count": 1,
                    "failure_count": 1,
                }
            ],
            "loss": {"total": 0.0},
        }

    monkeypatch.setattr(transfer.producer, "_metrics_for_arm", fake_metrics_for_arm)


def test_learned_transfer_pass_sets_status_pass(monkeypatch):
    _patch_small_surface(monkeypatch)
    _patch_metrics(monkeypatch, learned_pass=True)

    payload = transfer.build_payload(generated_at="fixture-time")

    assert payload["gap_head_on_h_observed_debt_transfer"]["status"] == "pass"
    assert payload["surfaces"][0]["verdict"]["status"] == "pass"
    assert {gate["status"] for gate in payload["hardgate_evidence"].values()} == {"pass"}


def test_failed_transfer_stays_failed_with_boundary(monkeypatch):
    _patch_small_surface(monkeypatch)
    _patch_metrics(monkeypatch, learned_pass=False)

    payload = transfer.build_payload(generated_at="fixture-time")

    assert payload["gap_head_on_h_observed_debt_transfer"]["status"] == "failed"
    assert payload["surfaces"][0]["verdict"]["status"] == "failed"
    assert payload["observed_debt_transfer_boundary"]["failed_surfaces"]


def test_markdown_is_pointer_only_and_artifact_is_not_canonical(monkeypatch):
    _patch_small_surface(monkeypatch)
    _patch_metrics(monkeypatch, learned_pass=True)
    payload = transfer.build_payload(generated_at="fixture-time")

    markdown = transfer.render_markdown(payload)

    assert "$.gap_head_on_h_observed_debt_transfer.status" in markdown
    assert "$.surfaces.<index>.verdict" in markdown
    assert "records" not in markdown
    assert "raw payload" not in markdown.lower()
    assert "gap-head-observed-debt-transfer.json" not in {
        Path(spec.json_artifact).name for spec in canonical.CANONICAL_REPORTS
    }


def test_write_payload_keeps_pointer_artifact_without_records(tmp_path, monkeypatch):
    _patch_small_surface(monkeypatch)
    _patch_metrics(monkeypatch, learned_pass=True)
    monkeypatch.setattr(transfer, "ROOT", tmp_path)
    payload = transfer.build_payload(generated_at="fixture-time")

    transfer._write_payload(payload)

    written = json.loads((tmp_path / transfer.JSON_ARTIFACT).read_text(encoding="utf-8"))
    markdown = (tmp_path / transfer.REPORT_ARTIFACT).read_text(encoding="utf-8")
    assert written["artifact_id"] == "bedc-quality-lab:gap-head-observed-debt-transfer"
    assert "records" not in written
    assert "records" not in markdown

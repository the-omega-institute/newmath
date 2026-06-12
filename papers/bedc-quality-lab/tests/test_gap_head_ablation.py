import json
from types import SimpleNamespace

import numpy as np
import pytest

from scripts import run_gap_head_ablation as runner


def _arm(value):
    return {
        "failure_detection_auroc": {"value": float(value)},
        "ece": {"value": 0.1},
        "unlogged_error_rate": 0.2,
        "critical_unlogged_error_rate": 0.3,
    }


def _record(seed, values):
    return {
        "seed": int(seed),
        "arms": {arm: _arm(value) for arm, value in values.items()},
    }


def _values(
    *,
    learned=0.90,
    no_h=0.70,
    prediction=0.65,
    low_margin=0.66,
    transition=0.67,
    off_target=0.68,
):
    return {
        "vanilla": 0.50,
        "learned_gap_head_on_h": learned,
        "matched_random_gap_head": 0.51,
        "drop_prediction_error_channel": prediction,
        "drop_low_margin_channel": low_margin,
        "drop_transition_unstable_channel": transition,
        "drop_off_target_intervention_channel": off_target,
        "pooled_any_gap_head_on_h": 0.75,
        "no_h_conditioning_gap_head": no_h,
        "low_sample_full_gap_head_on_h": 0.74,
    }


def test_arm_names_cover_ten_predeclared_arms():
    assert runner.ARM_NAMES == (
        "vanilla",
        "learned_gap_head_on_h",
        "matched_random_gap_head",
        "drop_prediction_error_channel",
        "drop_low_margin_channel",
        "drop_transition_unstable_channel",
        "drop_off_target_intervention_channel",
        "pooled_any_gap_head_on_h",
        "no_h_conditioning_gap_head",
        "low_sample_full_gap_head_on_h",
    )
    assert set(runner.CHANNEL_DROP_ARMS) == set(runner.producer.GAP_CHANNELS)


def test_aggregate_reports_seed_ci_for_each_arm():
    records = [
        _record(1, _values(learned=0.90, no_h=0.70)),
        _record(2, _values(learned=0.91, no_h=0.71)),
    ]

    aggregate = runner._aggregate(records)

    assert set(aggregate["by_arm"]) == set(runner.ARM_NAMES)
    for arm in runner.ARM_NAMES:
        for metric in (
            "failure_detection_auroc",
            "ece",
            "unlogged_error_rate",
            "critical_unlogged_error_rate",
        ):
            stats = aggregate["by_arm"][arm][metric]
            assert stats["n"] == 2
            assert "ci95_low" in stats
            assert "ci95_high" in stats


def test_hardgate_passes_when_required_factor_drops_are_significant():
    records = [
        _record(1, _values()),
        _record(2, _values()),
        _record(3, _values()),
    ]

    attribution = runner._factor_attribution(records)
    hardgate = runner._hardgate(attribution, record_count=len(records))

    assert attribution["learned_head"]["auroc_delta"] == pytest.approx(-0.20)
    assert attribution["channels"]["prediction_error"]["auroc_delta"] == pytest.approx(-0.25)
    assert hardgate["status"] == "pass"
    assert hardgate["gates"]["learned_head"]["status"] == "pass"
    assert hardgate["gates"]["prediction_error_channel"]["status"] == "pass"
    assert hardgate["gates"]["channel_completeness"]["significant_channel_count"] == 4


def test_hardgate_fails_when_required_drop_is_absent():
    records = [
        _record(1, _values(no_h=0.895, prediction=0.89, low_margin=0.66, transition=0.67, off_target=0.68)),
        _record(2, _values(no_h=0.905, prediction=0.90, low_margin=0.66, transition=0.67, off_target=0.68)),
        _record(3, _values(no_h=0.900, prediction=0.91, low_margin=0.66, transition=0.67, off_target=0.68)),
    ]

    attribution = runner._factor_attribution(records)
    hardgate = runner._hardgate(attribution, record_count=len(records))

    assert hardgate["status"] == "fail"
    assert hardgate["gates"]["learned_head"]["status"] == "fail"
    assert hardgate["gates"]["prediction_error_channel"]["status"] == "fail"


def test_hardgate_is_invalid_without_seed_ci():
    records = [_record(1, _values())]

    hardgate = runner._hardgate(runner._factor_attribution(records), record_count=len(records))

    assert hardgate["status"] == "invalid"


def test_payload_and_markdown_expose_hardgate_status_path():
    records = [
        _record(1, _values()),
        _record(2, _values()),
    ]
    config = runner._active_config(smoke=True)
    low_config = runner._low_sample_config(config, smoke=True)

    payload = runner._payload(records, config, low_config, elapsed_seconds=1.25)
    markdown = runner._render_report(payload)

    assert payload["hardgate"]["status"] in {"pass", "fail", "invalid"}
    assert payload["positive_discovery_pointer"] == "$.factor_attribution.learned_head.auroc_delta"
    assert "$.hardgate.status" in markdown
    assert "gap_label" not in json.dumps(payload["aggregate"])


def test_run_record_emits_ten_arms_with_shared_surface():
    feature_columns = ["h:0", "h:1", "score:a", "margin:a", "transition_delta:a"]
    surface = {
        "train_idx": np.array([0, 1, 2, 3], dtype=np.int64),
        "eval_idx": np.array([4, 5], dtype=np.int64),
        "features": np.array(
            [
                [0.0, 0.0, 0.1, 0.2, 0.3],
                [0.2, 0.1, 0.2, 0.3, 0.4],
                [0.3, 0.2, 0.3, 0.4, 0.5],
                [0.4, 0.3, 0.4, 0.5, 0.6],
                [0.5, 0.4, 0.5, 0.6, 0.7],
                [0.6, 0.5, 0.6, 0.7, 0.8],
            ],
            dtype=np.float64,
        ),
        "gap_labels": np.array(
            [
                [1.0, 0.0, 1.0, 0.0],
                [0.0, 1.0, 0.0, 1.0],
                [1.0, 1.0, 0.0, 0.0],
                [0.0, 0.0, 1.0, 1.0],
                [1.0, 0.0, 0.0, 1.0],
                [0.0, 1.0, 1.0, 0.0],
            ],
            dtype=np.float64,
        ),
        "prediction_error": np.array([1.0, 0.0, 1.0, 0.0, 1.0, 0.0], dtype=np.float64),
        "feature_columns": feature_columns,
        "gap_label_rates": {channel: 0.5 for channel in runner.producer.GAP_CHANNELS},
        "eval_gap_label_rates": {channel: 0.5 for channel in runner.producer.GAP_CHANNELS},
    }
    calls = {"surface": 0}

    def fake_surface_for_seed(*, seed, config):
        calls["surface"] += 1
        return surface

    def fake_fit(features, labels):
        assert labels.shape[1] == 4
        return {"columns": labels.shape[1]}

    def fake_predict(heads, features):
        return np.full((features.shape[0], 4), 0.75, dtype=np.float64)

    def fake_batch(sample_count, *, rho, seed):
        return SimpleNamespace(
            x=surface["features"][:, :2],
            x_pair=surface["features"][:, :2] + 0.05,
        )

    original_surface = runner.producer._surface_for_seed
    original_fit = runner.producer._fit_gap_head
    original_predict = runner.producer._predict_gap_head
    original_batch = runner.producer.make_toy_batch
    runner.producer._surface_for_seed = fake_surface_for_seed
    runner.producer._fit_gap_head = fake_fit
    runner.producer._predict_gap_head = fake_predict
    runner.producer.make_toy_batch = fake_batch
    try:
        config = runner._active_config(smoke=True)
        low_config = runner._low_sample_config(config, smoke=True)
        record = runner._run_record(seed=11, seed_index=0, config=config, low_sample_config=low_config)
    finally:
        runner.producer._surface_for_seed = original_surface
        runner.producer._fit_gap_head = original_fit
        runner.producer._predict_gap_head = original_predict
        runner.producer.make_toy_batch = original_batch

    assert calls["surface"] == 2
    assert set(record["arms"]) == set(runner.ARM_NAMES)
    assert record["split"]["overlap_count"] == 0
    assert record["inference_no_ground_truth_z"] is True

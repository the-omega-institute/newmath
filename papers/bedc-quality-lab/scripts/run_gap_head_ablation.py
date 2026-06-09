#!/usr/bin/env python3
"""Run gap-head ablations on learned h representations."""

from __future__ import annotations

import argparse
from dataclasses import replace
from datetime import datetime, timezone
import json
import math
from pathlib import Path
import sys
import time
from typing import Any, Sequence

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.experiment_stats import metric_stats
from scripts import run_gap_ledger_head_on_h as producer


JSON_ARTIFACT = "reports/canonical/gap-head-ablation.json"
REPORT_ARTIFACT = "reports/canonical/gap-head-ablation.md"
ARTIFACT_ID = "bedc-quality-lab:gap-head-ablation"
DELTA_THRESHOLD = 0.02
LOW_SAMPLE_COUNT = max(96, producer.SAMPLE_COUNT // 4)
SMOKE_SAMPLE_COUNT = 96
SMOKE_LOW_SAMPLE_COUNT = 64
SMOKE_SEED_COUNT = 3
ARM_NAMES = (
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
CHANNEL_DROP_ARMS = {
    "prediction_error": "drop_prediction_error_channel",
    "low_margin": "drop_low_margin_channel",
    "transition_unstable": "drop_transition_unstable_channel",
    "off_target_intervention": "drop_off_target_intervention_channel",
}


def _active_config(*, smoke: bool = False) -> producer.GapHeadRunConfig:
    seeds = tuple(int(seed) for seed in producer._seeds())
    if smoke:
        seeds = seeds[:SMOKE_SEED_COUNT]
    return producer.GapHeadRunConfig(
        sample_count=SMOKE_SAMPLE_COUNT if smoke else producer.DEFAULT_CONFIG.sample_count,
        seeds=seeds,
        rho=producer.DEFAULT_CONFIG.rho,
        use_torch=producer.USE_TORCH,
        json_artifact=JSON_ARTIFACT,
        report_artifact=REPORT_ARTIFACT,
        run_id_prefix="gap-head-ablation-smoke" if smoke else "gap-head-ablation",
        source_artifact_label="gap-head-ablation",
        seed_grid_kind="smoke" if smoke else producer.DEFAULT_CONFIG.seed_grid_kind,
    )


def _low_sample_config(config: producer.GapHeadRunConfig, *, smoke: bool = False) -> producer.GapHeadRunConfig:
    return replace(
        config,
        sample_count=SMOKE_LOW_SAMPLE_COUNT if smoke else LOW_SAMPLE_COUNT,
        run_id_prefix=f"{config.run_id_prefix}-low-sample",
    )


def _metric_projection(metrics: dict[str, Any]) -> dict[str, Any]:
    return producer._metric_projection(metrics)


def _fit_selected_channel_probabilities(
    *,
    train_features: np.ndarray,
    eval_features: np.ndarray,
    train_labels: np.ndarray,
    drop_channel: str | None = None,
) -> np.ndarray:
    train_value = np.asarray(train_labels, dtype=np.float64)
    labels = np.array(train_value, copy=True)
    if drop_channel is not None:
        drop_index = producer.GAP_CHANNELS.index(drop_channel)
        labels[:, drop_index] = 0.0
    heads = producer._fit_gap_head(train_features, labels)
    probabilities = producer._predict_gap_head(heads, eval_features)
    if drop_channel is not None:
        probabilities[:, producer.GAP_CHANNELS.index(drop_channel)] = 0.0
    return probabilities.astype(np.float64)


def _fit_pooled_any_probabilities(
    *,
    train_features: np.ndarray,
    eval_features: np.ndarray,
    train_labels: np.ndarray,
) -> np.ndarray:
    any_gap = (np.max(np.asarray(train_labels, dtype=np.float64), axis=1) > 0.5).astype(np.float64)
    pooled_labels = np.tile(any_gap.reshape(-1, 1), (1, len(producer.GAP_CHANNELS)))
    heads = producer._fit_gap_head(train_features, pooled_labels)
    first_channel = producer._predict_gap_head(heads, eval_features)[:, 0]
    return np.tile(first_channel.reshape(-1, 1), (1, len(producer.GAP_CHANNELS))).astype(np.float64)


def _feature_indices(columns: Sequence[str], *, omit_h: bool = False) -> list[int]:
    indices = [
        index
        for index, column in enumerate(columns)
        if not omit_h or column.split(":", 1)[0] != "h"
    ]
    if not indices:
        raise ValueError("selected feature set must not be empty")
    selected_columns = [columns[index] for index in indices]
    producer._assert_inference_columns(list(selected_columns))
    return indices


def _raw_no_h_features(
    *,
    seed: int,
    config: producer.GapHeadRunConfig,
    expected_rows: int,
) -> np.ndarray:
    batch = producer.make_toy_batch(config.sample_count, rho=config.rho, seed=seed)
    x = producer._require_finite("raw_x", batch.x, ndim=2)
    x_pair = producer._require_finite("raw_x_pair", batch.x_pair, ndim=2)
    if x.shape != x_pair.shape or x.shape[0] != expected_rows:
        raise ValueError("raw observation features must align with learned surface")
    features = np.column_stack([x, x_pair, np.abs(x_pair - x)])
    if not np.all(np.isfinite(features)):
        raise ValueError("raw observation features contain non-finite values")
    return features.astype(np.float64)


def _metrics_for_probabilities(
    *,
    arm: str,
    probabilities: np.ndarray,
    eval_labels: np.ndarray,
    eval_error: np.ndarray,
) -> dict[str, Any]:
    return _metric_projection(
        producer._metrics_for_arm(
            arm=arm,
            probabilities=probabilities,
            labels=eval_labels,
            prediction_error=eval_error,
        )
    )


def _arm_metrics_for_surface(surface: dict[str, Any], *, seed: int) -> dict[str, Any]:
    train_idx = surface["train_idx"]
    eval_idx = surface["eval_idx"]
    features = surface["features"]
    labels = surface["gap_labels"]
    eval_labels = labels[eval_idx]
    eval_error = surface["prediction_error"][eval_idx]
    full_eval_features = features[eval_idx]
    full_train_features = features[train_idx]
    train_labels = labels[train_idx]

    learned_probabilities = _fit_selected_channel_probabilities(
        train_features=full_train_features,
        eval_features=full_eval_features,
        train_labels=train_labels,
    )
    randomized_labels = producer._matched_random_gap_labels(labels, seed=seed)
    random_probabilities = _fit_selected_channel_probabilities(
        train_features=full_train_features,
        eval_features=full_eval_features,
        train_labels=randomized_labels[train_idx],
    )
    arms = {
        "vanilla": _metrics_for_probabilities(
            arm="vanilla",
            probabilities=np.zeros_like(learned_probabilities, dtype=np.float64),
            eval_labels=eval_labels,
            eval_error=eval_error,
        ),
        "learned_gap_head_on_h": _metrics_for_probabilities(
            arm="learned_gap_head_on_h",
            probabilities=learned_probabilities,
            eval_labels=eval_labels,
            eval_error=eval_error,
        ),
        "matched_random_gap_head": _metrics_for_probabilities(
            arm="matched_random_gap_head",
            probabilities=random_probabilities,
            eval_labels=eval_labels,
            eval_error=eval_error,
        ),
    }
    for channel, arm in CHANNEL_DROP_ARMS.items():
        probabilities = _fit_selected_channel_probabilities(
            train_features=full_train_features,
            eval_features=full_eval_features,
            train_labels=train_labels,
            drop_channel=channel,
        )
        arms[arm] = _metrics_for_probabilities(
            arm=arm,
            probabilities=probabilities,
            eval_labels=eval_labels,
            eval_error=eval_error,
        )

    pooled = _fit_pooled_any_probabilities(
        train_features=full_train_features,
        eval_features=full_eval_features,
        train_labels=train_labels,
    )
    arms["pooled_any_gap_head_on_h"] = _metrics_for_probabilities(
        arm="pooled_any_gap_head_on_h",
        probabilities=pooled,
        eval_labels=eval_labels,
        eval_error=eval_error,
    )

    _feature_indices(surface["feature_columns"], omit_h=True)
    no_h_features = _raw_no_h_features(
        seed=seed,
        config=surface["config"],
        expected_rows=int(features.shape[0]),
    )
    no_h_probabilities = _fit_selected_channel_probabilities(
        train_features=no_h_features[train_idx],
        eval_features=no_h_features[eval_idx],
        train_labels=train_labels,
    )
    arms["no_h_conditioning_gap_head"] = _metrics_for_probabilities(
        arm="no_h_conditioning_gap_head",
        probabilities=no_h_probabilities,
        eval_labels=eval_labels,
        eval_error=eval_error,
    )
    return arms


def _run_record(
    *,
    seed: int,
    seed_index: int,
    config: producer.GapHeadRunConfig,
    low_sample_config: producer.GapHeadRunConfig,
) -> dict[str, Any]:
    surface = producer._surface_for_seed(seed=seed, config=config)
    surface["config"] = config
    arms = _arm_metrics_for_surface(surface, seed=seed)
    low_surface = producer._surface_for_seed(seed=seed, config=low_sample_config)
    low_surface["config"] = low_sample_config
    low_arms = _arm_metrics_for_surface(low_surface, seed=seed)
    arms["low_sample_full_gap_head_on_h"] = low_arms["learned_gap_head_on_h"]
    arms["low_sample_full_gap_head_on_h"]["arm"] = "low_sample_full_gap_head_on_h"
    return {
        "seed_index": int(seed_index),
        "seed_sequence_position": int(seed_index + 1),
        "seed": int(seed),
        "run_id": f"{config.run_id_prefix}-seed-{seed}",
        "representation_boundary": producer.REPRESENTATION_BOUNDARY,
        "inference_no_ground_truth_z": producer.INFERENCE_NO_GROUND_TRUTH_Z,
        "sample_count": int(config.sample_count),
        "low_sample_count": int(low_sample_config.sample_count),
        "feature_columns": list(surface["feature_columns"]),
        "forbidden_inference_columns": list(producer.FORBIDDEN_INFERENCE_COLUMNS),
        "gap_label_rates": surface["gap_label_rates"],
        "eval_gap_label_rates": surface["eval_gap_label_rates"],
        "split": {
            "train_count": int(len(surface["train_idx"])),
            "eval_count": int(len(surface["eval_idx"])),
            "overlap_count": int(
                len(set(surface["train_idx"].tolist()) & set(surface["eval_idx"].tolist()))
            ),
        },
        "arms": arms,
    }


def _records(
    config: producer.GapHeadRunConfig,
    low_sample_config: producer.GapHeadRunConfig,
) -> list[dict[str, Any]]:
    return [
        _run_record(
            seed=int(seed),
            seed_index=index,
            config=config,
            low_sample_config=low_sample_config,
        )
        for index, seed in enumerate(config.seeds)
    ]


def _stats_from_records(records: list[dict[str, Any]], arm: str, metric: str) -> dict[str, Any]:
    return metric_stats(float(record["arms"][arm][metric]["value"] if metric in {"failure_detection_auroc", "ece"} else record["arms"][arm][metric]) for record in records)


def _pooled_metrics(records: list[dict[str, Any]], arm: str) -> dict[str, Any]:
    return {
        "failure_detection_auroc": _stats_from_records(records, arm, "failure_detection_auroc"),
        "ece": _stats_from_records(records, arm, "ece"),
        "unlogged_error_rate": _stats_from_records(records, arm, "unlogged_error_rate"),
        "critical_unlogged_error_rate": _stats_from_records(
            records, arm, "critical_unlogged_error_rate"
        ),
    }


def _aggregate(records: list[dict[str, Any]]) -> dict[str, Any]:
    return {
        "record_count": int(len(records)),
        "seed_order": [int(record["seed"]) for record in records],
        "arm_order": list(ARM_NAMES),
        "by_arm": {arm: _pooled_metrics(records, arm) for arm in ARM_NAMES},
    }


def _paired_auroc_delta(
    records: list[dict[str, Any]],
    *,
    baseline_arm: str,
    ablated_arm: str,
    factor: str,
) -> dict[str, Any]:
    signed = [
        float(record["arms"][ablated_arm]["failure_detection_auroc"]["value"])
        - float(record["arms"][baseline_arm]["failure_detection_auroc"]["value"])
        for record in records
    ]
    drop = [-value for value in signed]
    signed_stats = metric_stats(signed)
    drop_stats = metric_stats(drop)
    significant = (
        int(drop_stats["n"]) >= 2
        and float(signed_stats["mean"]) < -DELTA_THRESHOLD
        and float(drop_stats["ci95_low"]) > 0.0
    )
    return {
        "factor": factor,
        "baseline_arm": baseline_arm,
        "ablated_arm": ablated_arm,
        "auroc_delta": float(signed_stats["mean"]),
        "auroc_delta_ci95": signed_stats,
        "auroc_drop": float(drop_stats["mean"]),
        "auroc_drop_ci95": drop_stats,
        "ci95_low": float(drop_stats["ci95_low"]),
        "delta_threshold": DELTA_THRESHOLD,
        "significant_drop": bool(significant),
        "status": "pass" if significant else "fail",
    }


def _factor_attribution(records: list[dict[str, Any]]) -> dict[str, Any]:
    channels = {
        channel: _paired_auroc_delta(
            records,
            baseline_arm="learned_gap_head_on_h",
            ablated_arm=arm,
            factor=f"{channel}_channel",
        )
        for channel, arm in CHANNEL_DROP_ARMS.items()
    }
    return {
        "learned_head": _paired_auroc_delta(
            records,
            baseline_arm="learned_gap_head_on_h",
            ablated_arm="no_h_conditioning_gap_head",
            factor="learned_head_conditioning",
        ),
        "channels": channels,
        "pooled_any_capacity": _paired_auroc_delta(
            records,
            baseline_arm="learned_gap_head_on_h",
            ablated_arm="pooled_any_gap_head_on_h",
            factor="per_channel_head_capacity",
        ),
        "low_sample": _paired_auroc_delta(
            records,
            baseline_arm="learned_gap_head_on_h",
            ablated_arm="low_sample_full_gap_head_on_h",
            factor="sample_count",
        ),
    }


def _hardgate(factor_attribution: dict[str, Any], *, record_count: int) -> dict[str, Any]:
    if record_count < 2:
        return {
            "status": "invalid",
            "reason": "at least two seeds are required for seed CI",
            "delta_threshold": DELTA_THRESHOLD,
        }
    channels = factor_attribution["channels"]
    channel_statuses = {
        channel: row["status"] for channel, row in channels.items()
    }
    significant_channel_count = sum(1 for row in channels.values() if row["significant_drop"])
    gates = {
        "learned_head": {
            "status": factor_attribution["learned_head"]["status"],
            "pointer": "$.factor_attribution.learned_head.auroc_delta",
        },
        "prediction_error_channel": {
            "status": channels["prediction_error"]["status"],
            "pointer": "$.factor_attribution.channels.prediction_error.auroc_delta",
        },
        "channel_completeness": {
            "status": "pass" if significant_channel_count >= 3 else "fail",
            "criterion": "at least 3 of 4 channel-drop arms show a significant AUROC drop",
            "significant_channel_count": int(significant_channel_count),
            "channel_statuses": channel_statuses,
        },
    }
    status = "pass" if all(gate["status"] == "pass" for gate in gates.values()) else "fail"
    return {
        "status": status,
        "delta_threshold": DELTA_THRESHOLD,
        "significant_drop_rule": (
            "ablated_minus_baseline auroc_delta < -delta_threshold and "
            "baseline_minus_ablated ci95_low > 0"
        ),
        "gates": gates,
    }


def _source_artifacts(config: producer.GapHeadRunConfig) -> dict[str, Any]:
    return {
        "artifact_id": ARTIFACT_ID,
        "generation_script": "scripts/run_gap_head_ablation.py",
        "surface_owner": "scripts/run_gap_ledger_head_on_h.py::_surface_for_seed",
        "metric_helper": "scripts/run_gaussian_ou_gap_ledger_head.py::_metrics_for_arm",
        "stats_helper": "scripts/experiment_stats.py::metric_stats",
        "json_artifact": config.json_artifact,
        "report_artifact": config.report_artifact,
    }


def _applicability_boundary(
    config: producer.GapHeadRunConfig,
    low_sample_config: producer.GapHeadRunConfig,
) -> dict[str, Any]:
    return {
        "admitted_family": "Gaussian-OU toy world generated by the existing lab toy-world generator.",
        "representation_boundary": producer.REPRESENTATION_BOUNDARY,
        "inference_no_ground_truth_z": producer.INFERENCE_NO_GROUND_TRUTH_Z,
        "sample_count": int(config.sample_count),
        "low_sample_count": int(low_sample_config.sample_count),
        "seed_count": int(len(config.seeds)),
        "rho": float(config.rho),
        "gap_channels": list(producer.GAP_CHANNELS),
        "arms": list(ARM_NAMES),
        "not_claimed": [
            "No global quality claim.",
            "No transfer-surface claim.",
            "No large-model extrapolation.",
            "No inference-time use of z, z_pair, gap_label, prediction_error, or eval_gap_labels.",
        ],
    }


def _control_protocol(
    config: producer.GapHeadRunConfig,
    low_sample_config: producer.GapHeadRunConfig,
) -> dict[str, Any]:
    return {
        "baseline_arm": "learned_gap_head_on_h",
        "matched_random_arm": "matched_random_gap_head",
        "channel_drop_arms": dict(CHANNEL_DROP_ARMS),
        "pooled_any_arm": "pooled_any_gap_head_on_h",
        "no_h_conditioning_arm": "no_h_conditioning_gap_head",
        "low_sample_arm": "low_sample_full_gap_head_on_h",
        "same_surface_owner": True,
        "same_metric_helper": True,
        "same_seed_order": True,
        "sample_count": int(config.sample_count),
        "low_sample_count": int(low_sample_config.sample_count),
        "seed_count": int(len(config.seeds)),
        "delta_threshold": DELTA_THRESHOLD,
    }


def _payload(
    records: list[dict[str, Any]],
    config: producer.GapHeadRunConfig,
    low_sample_config: producer.GapHeadRunConfig,
    *,
    elapsed_seconds: float,
) -> dict[str, Any]:
    aggregate = _aggregate(records)
    attribution = _factor_attribution(records)
    hardgate = _hardgate(attribution, record_count=len(records))
    return {
        "artifact": config.json_artifact,
        "report": config.report_artifact,
        "artifact_id": ARTIFACT_ID,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "elapsed_seconds": float(f"{elapsed_seconds:.3f}"),
        "source_artifacts": _source_artifacts(config),
        "applicability_boundary": _applicability_boundary(config, low_sample_config),
        "control_protocol": _control_protocol(config, low_sample_config),
        "config": {
            "sample_count": int(config.sample_count),
            "low_sample_count": int(low_sample_config.sample_count),
            "seed_count": int(len(config.seeds)),
            "seeds": [int(seed) for seed in config.seeds],
            "rho": float(config.rho),
            "use_torch": bool(config.use_torch),
            "gap_channels": list(producer.GAP_CHANNELS),
            "arms": list(ARM_NAMES),
            "delta_threshold": DELTA_THRESHOLD,
            "expected_record_count": int(len(config.seeds)),
        },
        "aggregate": aggregate,
        "factor_attribution": attribution,
        "hardgate": hardgate,
        "positive_discovery_pointer": "$.factor_attribution.learned_head.auroc_delta",
        "records": records,
    }


def _format_float(value: float) -> str:
    if math.isnan(value):
        return "nan"
    return f"{value:.6f}"


def _render_stats(stats: dict[str, Any]) -> str:
    return (
        f"{_format_float(float(stats['mean']))} +/- {_format_float(float(stats['std']))} "
        f"(95% CI +/- {_format_float(float(stats['ci95_half_width']))})"
    )


def _render_report(payload: dict[str, Any]) -> str:
    lines = [
        "# Gap-Head Ablation",
        "",
        f"- Generated at: `{payload['generated_at']}`",
        f"- Hardgate status: `{payload['hardgate']['status']}`",
        f"- Sample count: `{payload['config']['sample_count']}`",
        f"- Low sample count: `{payload['config']['low_sample_count']}`",
        f"- Seed count: `{payload['config']['seed_count']}`",
        f"- Delta threshold: `{payload['config']['delta_threshold']}`",
        "",
        "## Arms",
        "",
        "| arm | failure-detection AUROC | ECE | UnloggedErrorRate | critical unlogged error rate |",
        "| --- | ---: | ---: | ---: | ---: |",
    ]
    for arm in ARM_NAMES:
        stats = payload["aggregate"]["by_arm"][arm]
        lines.append(
            "| "
            f"`{arm}` | "
            f"{_render_stats(stats['failure_detection_auroc'])} | "
            f"{_render_stats(stats['ece'])} | "
            f"{_render_stats(stats['unlogged_error_rate'])} | "
            f"{_render_stats(stats['critical_unlogged_error_rate'])} |"
        )
    lines.extend(
        [
            "",
            "## Factor Attribution",
            "",
            "| factor | ablated arm | AUROC delta | AUROC drop CI low | status |",
            "| --- | --- | ---: | ---: | --- |",
        ]
    )
    rows = [payload["factor_attribution"]["learned_head"]]
    rows.extend(payload["factor_attribution"]["channels"].values())
    rows.append(payload["factor_attribution"]["pooled_any_capacity"])
    rows.append(payload["factor_attribution"]["low_sample"])
    for row in rows:
        lines.append(
            "| "
            f"`{row['factor']}` | "
            f"`{row['ablated_arm']}` | "
            f"{_format_float(float(row['auroc_delta']))} | "
            f"{_format_float(float(row['ci95_low']))} | "
            f"`{row['status']}` |"
        )
    lines.extend(
        [
            "",
            "## Hardgate",
            "",
            f"- `$.hardgate.status`: `{payload['hardgate']['status']}`",
            f"- Positive-discovery pointer: `{payload['positive_discovery_pointer']}`",
            f"- Control pointer: `$.control_protocol`",
            "",
            "## Boundary",
            "",
        ]
    )
    for row in payload["applicability_boundary"]["not_claimed"]:
        lines.append(f"- {row}")
    lines.append("")
    return "\n".join(lines)


def _write_payload(payload: dict[str, Any], config: producer.GapHeadRunConfig) -> None:
    json_path = ROOT / config.json_artifact
    report_path = ROOT / config.report_artifact
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    report_path.write_text(_render_report(payload), encoding="utf-8")


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--smoke", action="store_true", help="Run a small seed and sample grid.")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> None:
    args = parse_args(()) if argv is None else parse_args(argv)
    started = time.perf_counter()
    config = _active_config(smoke=bool(args.smoke))
    low_config = _low_sample_config(config, smoke=bool(args.smoke))
    records = _records(config, low_config)
    payload = _payload(
        records,
        config,
        low_config,
        elapsed_seconds=time.perf_counter() - started,
    )
    _write_payload(payload, config)
    print(f"wrote {config.json_artifact}")
    print(f"wrote {config.report_artifact}")
    print(f"arms {len(payload['aggregate']['by_arm'])}")
    print(f"hardgate.status {payload['hardgate']['status']}")


if __name__ == "__main__":
    main(sys.argv[1:])

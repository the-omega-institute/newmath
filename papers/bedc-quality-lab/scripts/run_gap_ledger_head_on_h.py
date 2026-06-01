#!/usr/bin/env python3
"""Run a gap-ledger-head experiment on learned h representations."""

from __future__ import annotations

from datetime import datetime, timezone
import json
import math
from pathlib import Path
import sys
from typing import Any

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.mixing import DEFAULT_MIXING, mix_latents
from bedc_quality_lab.toy_world import make_toy_batch
from scripts.experiment_stats import metric_stats
from scripts import run_gaussian_ou_distinction_head as distinction
from scripts.run_gaussian_ou_gap_ledger_head import (
    BETA,
    ECE_BINS,
    EPSILON_GRID,
    GAP_CHANNELS,
    GAP_L2,
    GAP_LR,
    GAP_STEPS,
    PRIMARY_EPSILON,
    PRIMARY_TAU,
    RHO,
    SAMPLE_COUNT,
    SEED_COUNT,
    TAU_GRID,
    TRAIN_FRACTION,
    USE_TORCH,
    _fit_gap_head,
    _metrics_for_arm,
    _predict_gap_head,
    _primary_gap_sound,
    _seeds,
)
from scripts.run_gaussian_ou_lejepa import run_experiment


DISTINCTIONS = distinction.DISTINCTIONS
JSON_ARTIFACT = "reports/gap_ledger_head_on_h.json"
REPORT_ARTIFACT = "reports/gap_ledger_head_on_h.md"
REPRESENTATION_BOUNDARY = "learned_h"
INFERENCE_NO_GROUND_TRUTH_Z = True
QUALITY_COLUMNS = (
    "quality_q",
    "quality_margin",
    "linear_identifiability_r2",
    "approx_identifiability_proxy",
)
FORBIDDEN_INFERENCE_COLUMNS = (
    "z",
    "z_pair",
    "gap_label",
    "prediction_error",
    "eval_gap_labels",
)
EPS = 1.0e-12


def _require_finite(name: str, array: np.ndarray, *, ndim: int | None = None) -> np.ndarray:
    value = np.asarray(array, dtype=np.float64)
    if ndim is not None and value.ndim != ndim:
        raise ValueError(f"{name} must be {ndim}-dimensional")
    if value.shape[0] == 0:
        raise ValueError(f"{name} must not be empty")
    if not np.all(np.isfinite(value)):
        raise ValueError(f"{name} contains non-finite values")
    return value


def _fit_representation(train_x: np.ndarray) -> dict[str, np.ndarray]:
    x = _require_finite("train_x", train_x, ndim=2)
    mean = np.mean(x, axis=0, keepdims=True)
    scale = np.std(x, axis=0, keepdims=True)
    scale = np.where(scale <= EPS, 1.0, scale)
    return {"mean": mean, "scale": scale}


def _apply_representation(x: np.ndarray, state: dict[str, np.ndarray]) -> np.ndarray:
    value = _require_finite("x", x, ndim=2)
    return ((value - state["mean"]) / state["scale"]).astype(np.float64)


def _feature_columns(h_dim: int) -> list[str]:
    columns = [f"h:{index}" for index in range(int(h_dim))]
    columns.extend(f"score:{name}" for name in DISTINCTIONS)
    columns.extend(f"margin:{name}" for name in DISTINCTIONS)
    columns.extend(f"transition_delta:{name}" for name in DISTINCTIONS)
    columns.extend(f"quality:{name}" for name in QUALITY_COLUMNS)
    return columns


def _assert_inference_columns(columns: list[str]) -> None:
    forbidden = set(FORBIDDEN_INFERENCE_COLUMNS)
    for column in columns:
        root = column.split(":", 1)[0]
        if root in forbidden or column in forbidden:
            raise ValueError(f"forbidden inference column: {column}")


def _build_inference_features(
    *,
    h: np.ndarray,
    score: np.ndarray,
    margin: np.ndarray,
    transition_delta: np.ndarray,
    quality_scalars: np.ndarray,
) -> tuple[np.ndarray, list[str]]:
    h_value = _require_finite("h", h, ndim=2)
    score_value = _require_finite("score", score, ndim=2)
    margin_value = _require_finite("margin", margin, ndim=2)
    transition_value = _require_finite("transition_delta", transition_delta, ndim=2)
    quality_value = _require_finite("quality_scalars", quality_scalars, ndim=1)
    expected = (h_value.shape[0], len(DISTINCTIONS))
    if score_value.shape != expected or margin_value.shape != expected or transition_value.shape != expected:
        raise ValueError("probe-derived feature blocks must align with h and distinctions")
    if quality_value.shape[0] != len(QUALITY_COLUMNS):
        raise ValueError("quality_scalars must align with quality columns")
    quality = np.tile(quality_value.reshape(1, -1), (h_value.shape[0], 1))
    features = np.column_stack([h_value, score_value, margin_value, transition_value, quality])
    columns = _feature_columns(h_value.shape[1])
    _assert_inference_columns(columns)
    if features.shape[1] != len(columns):
        raise ValueError("feature column count mismatch")
    return features.astype(np.float64), columns


def _quality_scalars(quality: Any) -> np.ndarray:
    return np.array(
        [float(quality.metrics.get(name, 0.0)) for name in QUALITY_COLUMNS],
        dtype=np.float64,
    )


def _probe_blocks(
    *,
    probes: dict[str, Any],
    h: np.ndarray,
    h_pair: np.ndarray,
) -> dict[str, np.ndarray]:
    scores = []
    margins = []
    transitions = []
    for name in DISTINCTIONS:
        pred = distinction._predict_probe(probes[name], h)
        pair_pred = distinction._predict_probe(probes[name], h_pair)
        scores.append(pred["probabilities"])
        margins.append(np.abs(pred["logits"]))
        transitions.append(np.abs(pred["probabilities"] - pair_pred["probabilities"]))
    return {
        "score": np.column_stack(scores).astype(np.float64),
        "margin": np.column_stack(margins).astype(np.float64),
        "transition_delta": np.column_stack(transitions).astype(np.float64),
    }


def _surface_for_seed(*, seed: int) -> dict[str, Any]:
    batch = make_toy_batch(SAMPLE_COUNT, rho=RHO, seed=seed)
    z = distinction._require_finite("z", batch.z)
    z_pair = distinction._require_finite("z_pair", batch.z_pair)
    train_idx, eval_idx = distinction._train_eval_split(z.shape[0], seed=seed)
    state = _fit_representation(batch.x[train_idx])
    h = _apply_representation(batch.x, state)
    h_pair = _apply_representation(batch.x_pair, state)

    high_threshold = distinction._high_energy_threshold(z, train_idx)
    labels = {
        name: distinction._label_truth(name, z, high_energy_threshold=high_threshold)
        for name in DISTINCTIONS
    }
    pair_labels = {
        name: distinction._label_truth(name, z_pair, high_energy_threshold=high_threshold)
        for name in DISTINCTIONS
    }
    probes = {
        name: distinction._fit_probe(h[train_idx], label[train_idx])
        for name, label in labels.items()
    }
    blocks = _probe_blocks(probes=probes, h=h, h_pair=h_pair)

    errors = []
    transition_changed = []
    for index, name in enumerate(DISTINCTIONS):
        pred = distinction._predict_probe(probes[name], h)
        errors.append((pred["predictions"] != labels[name]).astype(np.float64))
        transition_changed.append((labels[name] != pair_labels[name]).astype(np.float64))
    prediction_error = np.max(np.column_stack(errors), axis=1)
    transition_unstable = np.max(np.column_stack(transition_changed), axis=1)

    min_margin = np.min(blocks["margin"], axis=1)
    margin_threshold = float(np.quantile(min_margin[train_idx], 0.30))
    low_margin = (min_margin <= margin_threshold).astype(np.float64)

    off_target_rows = []
    for target in DISTINCTIONS:
        z_changed = distinction._intervene(target, z, z_pair)
        h_changed = _apply_representation(mix_latents(z_changed, DEFAULT_MIXING), state)
        target_off_target = np.zeros(z.shape[0], dtype=np.float64)
        for name in DISTINCTIONS:
            if name == target:
                continue
            before = distinction._predict_probe(probes[name], h)["predictions"]
            after = distinction._predict_probe(probes[name], h_changed)["predictions"]
            target_off_target = np.maximum(target_off_target, (before != after).astype(np.float64))
        off_target_rows.append(target_off_target)
    off_target_intervention = np.max(np.column_stack(off_target_rows), axis=1)

    gap_labels = np.column_stack(
        [prediction_error, low_margin, transition_unstable, off_target_intervention]
    ).astype(np.float64)
    quality = run_experiment(
        use_torch=USE_TORCH,
        sample_count=SAMPLE_COUNT,
        seed=seed,
        rho=RHO,
        run_id=f"gap-ledger-head-on-h-seed-{seed}",
        envelope_artifact=JSON_ARTIFACT,
        report_artifact=REPORT_ARTIFACT,
    )
    features, feature_columns = _build_inference_features(
        h=h,
        score=blocks["score"],
        margin=blocks["margin"],
        transition_delta=blocks["transition_delta"],
        quality_scalars=_quality_scalars(quality),
    )
    return {
        "features": features,
        "feature_columns": feature_columns,
        "gap_labels": gap_labels,
        "prediction_error": prediction_error,
        "train_idx": train_idx,
        "eval_idx": eval_idx,
        "high_energy_threshold": float(high_threshold),
        "low_margin_threshold": float(margin_threshold),
        "gap_label_rates": {
            channel: float(np.mean(gap_labels[:, index]))
            for index, channel in enumerate(GAP_CHANNELS)
        },
        "eval_gap_label_rates": {
            channel: float(np.mean(gap_labels[eval_idx, index]))
            for index, channel in enumerate(GAP_CHANNELS)
        },
        "canonical_envelope_projection": {
            "run_id": quality.run_id,
            "source_spec": dict(quality.source_spec),
            "classifier_spec": dict(quality.classifier_spec),
            "metrics": {name: float(value) for name, value in quality.metrics.items()},
            "artifacts": dict(quality.artifacts),
        },
        "representation": {
            "name": "train-split-standardized-observation-h",
            "input": "x",
            "output_dim": int(h.shape[1]),
            "fit_split": "train",
        },
    }


def _metric_projection(metrics: dict[str, Any]) -> dict[str, Any]:
    primary = _primary_gap_sound(metrics["gap_sound_scan"])
    return {
        "arm": metrics["arm"],
        "failure_detection_auroc": metrics["failure_detection_auroc"],
        "ece": metrics["ece"],
        "unlogged_error_rate": float(metrics["unlogged_error_rate"]),
        "critical_unlogged_error_rate": float(metrics["critical_unlogged_error_rate"]),
        "prediction_error_rate": float(metrics["prediction_error_rate"]),
        "gap_score_mean": float(metrics["gap_score_mean"]),
        "critical_gap_score_mean": float(metrics["critical_gap_score_mean"]),
        "primary_gap_sound": {
            "tau": float(primary["tau"]),
            "epsilon": float(primary["epsilon"]),
            "low_gap_implies_error_within_epsilon": float(
                primary["low_gap_implies_error_within_epsilon"]
            ),
            "error_above_epsilon_implies_gap_at_least_tau": float(
                primary["error_above_epsilon_implies_gap_at_least_tau"]
            ),
            "low_gap_count": int(primary["low_gap_count"]),
            "failure_count": int(primary["failure_count"]),
        },
        "loss": metrics["loss"],
    }


def _posthoc_report_only(*, eval_labels: np.ndarray, eval_error: np.ndarray) -> dict[str, Any]:
    oracle_metrics = _metrics_for_arm(
        arm="posthoc_report_only",
        probabilities=eval_labels,
        labels=eval_labels,
        prediction_error=eval_error,
    )
    return {
        "arm": "posthoc_report_only",
        "inference": False,
        "diagnostic_source": "eval_gap_labels",
        "eval_gap_label_rates": {
            channel: float(np.mean(eval_labels[:, index]))
            for index, channel in enumerate(GAP_CHANNELS)
        },
        "oracle_diagnostics": _metric_projection(oracle_metrics),
    }


def _run_record(*, seed: int, seed_index: int) -> dict[str, Any]:
    surface = _surface_for_seed(seed=seed)
    train_idx = surface["train_idx"]
    eval_idx = surface["eval_idx"]
    heads = _fit_gap_head(surface["features"][train_idx], surface["gap_labels"][train_idx])
    eval_probabilities = _predict_gap_head(heads, surface["features"][eval_idx])
    eval_labels = surface["gap_labels"][eval_idx]
    eval_error = surface["prediction_error"][eval_idx]
    vanilla_probabilities = np.zeros_like(eval_probabilities, dtype=np.float64)
    vanilla_metrics = _metrics_for_arm(
        arm="vanilla",
        probabilities=vanilla_probabilities,
        labels=eval_labels,
        prediction_error=eval_error,
    )
    learned_metrics = _metrics_for_arm(
        arm="learned_gap_head_on_h",
        probabilities=eval_probabilities,
        labels=eval_labels,
        prediction_error=eval_error,
    )
    return {
        "seed_index": int(seed_index),
        "seed_sequence_position": int(seed_index + 1),
        "seed": int(seed),
        "run_id": f"gap-ledger-head-on-h-seed-{seed}",
        "representation_boundary": REPRESENTATION_BOUNDARY,
        "inference_no_ground_truth_z": INFERENCE_NO_GROUND_TRUTH_Z,
        "feature_columns": list(surface["feature_columns"]),
        "forbidden_inference_columns": list(FORBIDDEN_INFERENCE_COLUMNS),
        "config": {
            "sample_count": SAMPLE_COUNT,
            "rho": RHO,
            "use_torch": USE_TORCH,
            "gap_channels": list(GAP_CHANNELS),
            "distinctions": list(DISTINCTIONS),
            "train_fraction": TRAIN_FRACTION,
            "train_count": int(len(train_idx)),
            "eval_count": int(len(eval_idx)),
            "high_energy_threshold": float(surface["high_energy_threshold"]),
            "low_margin_threshold": float(surface["low_margin_threshold"]),
            "beta": BETA,
            "primary_tau": PRIMARY_TAU,
            "primary_epsilon": PRIMARY_EPSILON,
        },
        "split": {
            "train_indices": [int(index) for index in train_idx],
            "eval_indices": [int(index) for index in eval_idx],
            "overlap_count": int(len(set(train_idx.tolist()) & set(eval_idx.tolist()))),
        },
        "representation": surface["representation"],
        "canonical_envelope_projection": surface["canonical_envelope_projection"],
        "gap_label_rates": surface["gap_label_rates"],
        "eval_gap_label_rates": surface["eval_gap_label_rates"],
        "arms": {
            "vanilla": _metric_projection(vanilla_metrics),
            "posthoc_report_only": _posthoc_report_only(
                eval_labels=eval_labels,
                eval_error=eval_error,
            ),
            "learned_gap_head_on_h": _metric_projection(learned_metrics),
        },
        "comparison": {
            "unlogged_error_rate_delta_learned_minus_vanilla": float(
                learned_metrics["unlogged_error_rate"] - vanilla_metrics["unlogged_error_rate"]
            ),
            "critical_unlogged_error_rate_delta_learned_minus_vanilla": float(
                learned_metrics["critical_unlogged_error_rate"]
                - vanilla_metrics["critical_unlogged_error_rate"]
            ),
            "failure_detection_auroc_delta_learned_minus_vanilla": float(
                learned_metrics["failure_detection_auroc"]["value"]
                - vanilla_metrics["failure_detection_auroc"]["value"]
            ),
        },
    }


def _records() -> list[dict[str, Any]]:
    return [_run_record(seed=seed, seed_index=index) for index, seed in enumerate(_seeds())]


def _pooled_metrics(records: list[dict[str, Any]], arm: str) -> dict[str, Any]:
    auroc = [float(record["arms"][arm]["failure_detection_auroc"]["value"]) for record in records]
    ece = [float(record["arms"][arm]["ece"]["value"]) for record in records]
    unlogged = [float(record["arms"][arm]["unlogged_error_rate"]) for record in records]
    critical = [float(record["arms"][arm]["critical_unlogged_error_rate"]) for record in records]
    error_rate = [float(record["arms"][arm]["prediction_error_rate"]) for record in records]
    low_gap_sound = [
        float(record["arms"][arm]["primary_gap_sound"]["low_gap_implies_error_within_epsilon"])
        for record in records
    ]
    failure_logged = [
        float(record["arms"][arm]["primary_gap_sound"]["error_above_epsilon_implies_gap_at_least_tau"])
        for record in records
    ]
    return {
        "failure_detection_auroc": metric_stats(auroc),
        "ece": metric_stats(ece),
        "unlogged_error_rate": metric_stats(unlogged),
        "critical_unlogged_error_rate": metric_stats(critical),
        "prediction_error_rate": metric_stats(error_rate),
        "gap_sound_low_gap_implies_error_within_epsilon": metric_stats(low_gap_sound),
        "gap_sound_error_above_epsilon_implies_gap_at_least_tau": metric_stats(failure_logged),
    }


def _aggregate(records: list[dict[str, Any]]) -> dict[str, Any]:
    return {
        "record_count": len(records),
        "seed_order": [int(record["seed"]) for record in records],
        "by_arm": {
            "vanilla": _pooled_metrics(records, "vanilla"),
            "learned_gap_head_on_h": _pooled_metrics(records, "learned_gap_head_on_h"),
        },
        "comparison": {
            "unlogged_error_rate_delta_learned_minus_vanilla": metric_stats(
                [
                    float(record["comparison"]["unlogged_error_rate_delta_learned_minus_vanilla"])
                    for record in records
                ]
            ),
            "critical_unlogged_error_rate_delta_learned_minus_vanilla": metric_stats(
                [
                    float(
                        record["comparison"][
                            "critical_unlogged_error_rate_delta_learned_minus_vanilla"
                        ]
                    )
                    for record in records
                ]
            ),
            "failure_detection_auroc_delta_learned_minus_vanilla": metric_stats(
                [
                    float(
                        record["comparison"][
                            "failure_detection_auroc_delta_learned_minus_vanilla"
                        ]
                    )
                    for record in records
                ]
            ),
        },
    }


def _source_artifacts() -> dict[str, Any]:
    return {
        "generation_script": "scripts/run_gap_ledger_head_on_h.py",
        "imported_gap_ledger_head_runner": "scripts/run_gaussian_ou_gap_ledger_head.py",
        "canonical_runner": "scripts/run_gaussian_ou_lejepa.py::run_experiment",
        "distinction_head_runner": "scripts/run_gaussian_ou_distinction_head.py",
        "toy_world": "bedc_quality_lab.toy_world.make_toy_batch",
        "stats_helper": "scripts/experiment_stats.py",
        "json_artifact": JSON_ARTIFACT,
        "report_artifact": REPORT_ARTIFACT,
        "import_dependency_chain": [
            "scripts/run_gap_ledger_head_on_h.py",
            "scripts.run_gaussian_ou_gap_ledger_head",
            "scripts.run_gaussian_ou_distinction_head",
            "scripts.run_gaussian_ou_lejepa.run_experiment",
            "bedc_quality_lab.toy_world.make_toy_batch",
            "scripts.experiment_stats.metric_stats",
        ],
    }


def _gap_channel_metadata() -> list[dict[str, str]]:
    return [
        {
            "name": "prediction_error",
            "origin": "upstream_truth_diagnostic",
            "definition": "At least one held-out h-trained distinction probe predicts the wrong truth label.",
        },
        {
            "name": "low_margin",
            "origin": "h_probe_margin",
            "definition": "Minimum absolute h-probe margin is below a train-split quantile.",
        },
        {
            "name": "transition_unstable",
            "origin": "upstream_transition_truth",
            "definition": "At least one distinction truth label differs under the OU pair.",
        },
        {
            "name": "off_target_intervention",
            "origin": "h_probe_intervention_diagnostic",
            "definition": "A target intervention flips at least one non-target h-probe prediction.",
        },
    ]


def _applicability_boundary() -> dict[str, Any]:
    return {
        "admitted_family": "Gaussian-OU toy world generated by the existing lab toy-world generator.",
        "representation_boundary": REPRESENTATION_BOUNDARY,
        "inference_no_ground_truth_z": INFERENCE_NO_GROUND_TRUTH_Z,
        "model": "Script-private numpy logistic gap heads over h-only inference features.",
        "sample_count": SAMPLE_COUNT,
        "seed_count": SEED_COUNT,
        "rho": RHO,
        "gap_channels": list(GAP_CHANNELS),
        "distinctions": list(DISTINCTIONS),
        "feature_columns": _feature_columns(2),
        "forbidden_inference_columns": list(FORBIDDEN_INFERENCE_COLUMNS),
        "tau_scan_range": list(TAU_GRID),
        "epsilon_scan_range": list(EPSILON_GRID),
        "primary_tau": PRIMARY_TAU,
        "primary_epsilon": PRIMARY_EPSILON,
    }


def _negative_result_note(aggregate: dict[str, Any]) -> str:
    learned_auroc = float(
        aggregate["by_arm"]["learned_gap_head_on_h"]["failure_detection_auroc"]["mean"]
    )
    vanilla_unlogged = float(aggregate["by_arm"]["vanilla"]["unlogged_error_rate"]["mean"])
    learned_unlogged = float(
        aggregate["by_arm"]["learned_gap_head_on_h"]["unlogged_error_rate"]["mean"]
    )
    if abs(learned_auroc - 0.5) <= 0.03:
        return (
            "Failure-detection AUROC is approximately chance under the predeclared protocol; "
            "this result is reported without threshold retuning."
        )
    if learned_unlogged >= vanilla_unlogged:
        return (
            "The learned h gap head did not reduce UnloggedErrorRate relative to vanilla under "
            "the predeclared protocol; this result is reported directly."
        )
    return (
        "The learned h gap head reduced UnloggedErrorRate relative to vanilla under the "
        "predeclared protocol; thresholds and beta were not tuned after observing outcomes."
    )


def _payload(records: list[dict[str, Any]]) -> dict[str, Any]:
    aggregate = _aggregate(records)
    return {
        "artifact": JSON_ARTIFACT,
        "report": REPORT_ARTIFACT,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "representation_boundary": REPRESENTATION_BOUNDARY,
        "inference_no_ground_truth_z": INFERENCE_NO_GROUND_TRUTH_Z,
        "feature_columns": _feature_columns(2),
        "forbidden_inference_columns": list(FORBIDDEN_INFERENCE_COLUMNS),
        "config": {
            "sample_count": SAMPLE_COUNT,
            "seed_count": SEED_COUNT,
            "seeds": _seeds(),
            "rho": RHO,
            "use_torch": USE_TORCH,
            "distinctions": list(DISTINCTIONS),
            "gap_channels": list(GAP_CHANNELS),
            "train_fraction": TRAIN_FRACTION,
            "gap_steps": GAP_STEPS,
            "gap_lr": GAP_LR,
            "gap_l2": GAP_L2,
            "beta": BETA,
            "primary_tau": PRIMARY_TAU,
            "primary_epsilon": PRIMARY_EPSILON,
            "tau_grid": list(TAU_GRID),
            "epsilon_grid": list(EPSILON_GRID),
            "ece_bins": ECE_BINS,
            "expected_record_count": SEED_COUNT,
        },
        "gap_channel_metadata": _gap_channel_metadata(),
        "source_artifacts": _source_artifacts(),
        "applicability_boundary": _applicability_boundary(),
        "negative_result_note": _negative_result_note(aggregate),
        "records": records,
        "aggregate": aggregate,
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
    aggregate = payload["aggregate"]
    lines = [
        "# Gap-Ledger Head on Learned h",
        "",
        f"- Generated at: `{payload['generated_at']}`",
        f"- Representation boundary: `{payload['representation_boundary']}`",
        f"- Inference no ground-truth z: `{str(bool(payload['inference_no_ground_truth_z'])).lower()}`",
        f"- Sample count: `{payload['config']['sample_count']}`",
        f"- Seed count: `{payload['config']['seed_count']}`",
        f"- Rho: `{payload['config']['rho']}`",
        f"- Gap channels: `{', '.join(payload['config']['gap_channels'])}`",
        f"- Total records: `{aggregate['record_count']}`",
        "",
        "## Arms",
        "",
        (
            "| arm | failure-detection AUROC | ECE | UnloggedErrorRate | "
            "critical unlogged error rate | prediction error rate |"
        ),
        "| --- | ---: | ---: | ---: | ---: | ---: |",
    ]
    for arm in ("vanilla", "learned_gap_head_on_h"):
        stats = aggregate["by_arm"][arm]
        lines.append(
            "| "
            f"`{arm}` | "
            f"{_render_stats(stats['failure_detection_auroc'])} | "
            f"{_render_stats(stats['ece'])} | "
            f"{_render_stats(stats['unlogged_error_rate'])} | "
            f"{_render_stats(stats['critical_unlogged_error_rate'])} | "
            f"{_render_stats(stats['prediction_error_rate'])} |"
        )
    comparison = aggregate["comparison"]
    lines.extend(
        [
            "",
            "## Comparison",
            "",
            (
                "- UnloggedErrorRate delta learned minus vanilla: "
                f"{_render_stats(comparison['unlogged_error_rate_delta_learned_minus_vanilla'])}"
            ),
            (
                "- Critical unlogged error rate delta learned minus vanilla: "
                f"{_render_stats(comparison['critical_unlogged_error_rate_delta_learned_minus_vanilla'])}"
            ),
            (
                "- Failure-detection AUROC delta learned minus vanilla: "
                f"{_render_stats(comparison['failure_detection_auroc_delta_learned_minus_vanilla'])}"
            ),
            "",
            "## Boundary",
            "",
            f"- Feature columns: `{', '.join(payload['feature_columns'])}`",
            f"- Forbidden inference columns: `{', '.join(payload['forbidden_inference_columns'])}`",
            "",
            "## Gap Channels",
            "",
        ]
    )
    for item in payload["gap_channel_metadata"]:
        lines.append(f"- `{item['name']}` ({item['origin']}): {item['definition']}")
    lines.extend(
        [
            "",
            "## Negative Result Note",
            "",
            payload["negative_result_note"],
            "",
            "## Source Artifacts",
            "",
            f"- Generation script: `{payload['source_artifacts']['generation_script']}`",
            f"- Imported gap helper: `{payload['source_artifacts']['imported_gap_ledger_head_runner']}`",
            f"- JSON artifact: `{payload['source_artifacts']['json_artifact']}`",
            f"- Report artifact: `{payload['source_artifacts']['report_artifact']}`",
            "- Import dependency chain:",
        ]
    )
    for item in payload["source_artifacts"]["import_dependency_chain"]:
        lines.append(f"  - `{item}`")
    lines.extend(["", "## Seed Order", "", f"`{', '.join(str(seed) for seed in aggregate['seed_order'])}`", ""])
    return "\n".join(lines)


def _write_payload(payload: dict[str, Any]) -> None:
    json_path = ROOT / JSON_ARTIFACT
    report_path = ROOT / REPORT_ARTIFACT
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    report_path.write_text(_render_report(payload), encoding="utf-8")


def main() -> None:
    payload = _payload(_records())
    _write_payload(payload)
    print(f"wrote {JSON_ARTIFACT}")
    print(f"wrote {REPORT_ARTIFACT}")
    print(f"records {len(payload['records'])}")


if __name__ == "__main__":
    main()

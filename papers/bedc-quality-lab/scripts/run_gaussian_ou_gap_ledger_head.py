#!/usr/bin/env python3
"""Run a Gaussian-OU gap-ledger-head experiment."""

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

from bedc_quality_lab.toy_world import make_toy_batch
from scripts.experiment_stats import metric_stats
from scripts import run_gaussian_ou_distinction_head as distinction
from scripts.run_gaussian_ou_lejepa import run_experiment


SAMPLE_COUNT = distinction.SAMPLE_COUNT
SEED_COUNT = 30
RHO = distinction.RHO
USE_TORCH = False
MASTER_SEED = distinction.MASTER_SEED
TRAIN_FRACTION = distinction.TRAIN_FRACTION
DISTINCTIONS = distinction.DISTINCTIONS
GAP_CHANNELS = (
    "prediction_error",
    "low_margin",
    "transition_unstable",
    "off_target_intervention",
)
JSON_ARTIFACT = "reports/gaussian_ou_gap_ledger_head.json"
REPORT_ARTIFACT = "reports/gaussian_ou_gap_ledger_head.md"
BETA = 1.0
PRIMARY_TAU = 0.5
PRIMARY_EPSILON = 0.0
TAU_GRID = (0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9)
EPSILON_GRID = (0.0, 0.05, 0.1, 0.2)
ECE_BINS = 10
GAP_STEPS = 500
GAP_LR = 0.14
GAP_L2 = 1.0e-4
EPS = 1.0e-12


def _seeds(master_seed: int = MASTER_SEED, count: int = SEED_COUNT) -> list[int]:
    return distinction._seeds(master_seed, count)


def _require_finite(name: str, array: np.ndarray, *, ndim: int | None = None) -> np.ndarray:
    value = np.asarray(array, dtype=np.float64)
    if ndim is not None and value.ndim != ndim:
        raise ValueError(f"{name} must be {ndim}-dimensional")
    if value.shape[0] == 0:
        raise ValueError(f"{name} must not be empty")
    if not np.all(np.isfinite(value)):
        raise ValueError(f"{name} contains non-finite values")
    return value


def _sigmoid(logits: np.ndarray) -> np.ndarray:
    return 1.0 / (1.0 + np.exp(-np.clip(logits, -60.0, 60.0)))


def _binary_cross_entropy(labels: np.ndarray, probabilities: np.ndarray) -> float:
    y = _require_finite("labels", labels, ndim=1)
    p = _require_finite("probabilities", probabilities, ndim=1)
    if y.shape != p.shape:
        raise ValueError("labels and probabilities must have the same shape")
    if np.any((y < 0.0) | (y > 1.0)) or np.any((p < 0.0) | (p > 1.0)):
        raise ValueError("labels and probabilities must be in [0, 1]")
    clipped = np.clip(p, EPS, 1.0 - EPS)
    return float(-np.mean(y * np.log(clipped) + (1.0 - y) * np.log(1.0 - clipped)))


def _standardize_fit(x: np.ndarray) -> dict[str, np.ndarray]:
    value = _require_finite("x", x, ndim=2)
    mean = np.mean(value, axis=0, keepdims=True)
    scale = np.std(value, axis=0, keepdims=True)
    scale = np.where(scale <= EPS, 1.0, scale)
    return {"mean": mean, "scale": scale}


def _standardize_apply(x: np.ndarray, state: dict[str, np.ndarray]) -> np.ndarray:
    value = _require_finite("x", x, ndim=2)
    return (value - state["mean"]) / state["scale"]


def _fit_logistic_head(
    x: np.ndarray,
    y: np.ndarray,
    *,
    steps: int = GAP_STEPS,
    lr: float = GAP_LR,
    l2: float = GAP_L2,
) -> dict[str, Any]:
    features = _require_finite("x", x, ndim=2)
    labels = _require_finite("y", y, ndim=1)
    if labels.shape[0] != features.shape[0]:
        raise ValueError("y must be aligned with x")
    if not set(np.unique(labels)).issubset({0.0, 1.0}):
        raise ValueError("y must contain binary labels")
    standardizer = _standardize_fit(features)
    xs = _standardize_apply(features, standardizer)
    weights = np.zeros(xs.shape[1], dtype=np.float64)
    bias = 0.0
    n = float(xs.shape[0])
    for _ in range(int(steps)):
        probabilities = _sigmoid(xs @ weights + bias)
        residual = probabilities - labels
        weights -= float(lr) * ((xs.T @ residual) / n + float(l2) * weights)
        bias -= float(lr) * float(np.mean(residual))
    return {"weights": weights, "bias": float(bias), "standardizer": standardizer}


def _predict_logistic_head(head: dict[str, Any], x: np.ndarray) -> np.ndarray:
    xs = _standardize_apply(x, head["standardizer"])
    return _sigmoid(xs @ head["weights"] + float(head["bias"])).astype(np.float64)


def _fit_gap_head(
    x: np.ndarray,
    labels: np.ndarray,
    *,
    steps: int = GAP_STEPS,
    lr: float = GAP_LR,
    l2: float = GAP_L2,
) -> dict[str, Any]:
    features = _require_finite("x", x, ndim=2)
    y = _require_finite("labels", labels, ndim=2)
    if y.shape[0] != features.shape[0] or y.shape[1] != len(GAP_CHANNELS):
        raise ValueError("labels must align with x and gap channels")
    return {
        channel: _fit_logistic_head(features, y[:, index], steps=steps, lr=lr, l2=l2)
        for index, channel in enumerate(GAP_CHANNELS)
    }


def _predict_gap_head(heads: dict[str, Any], x: np.ndarray) -> np.ndarray:
    columns = [_predict_logistic_head(heads[channel], x) for channel in GAP_CHANNELS]
    probabilities = np.column_stack(columns).astype(np.float64)
    if not np.all(np.isfinite(probabilities)):
        raise ValueError("gap probabilities contain non-finite values")
    return probabilities


def _gap_loss(
    labels: np.ndarray,
    probabilities: np.ndarray,
    prediction_error: np.ndarray,
    *,
    beta: float = BETA,
) -> dict[str, float]:
    y = _require_finite("labels", labels, ndim=2)
    p = _require_finite("probabilities", probabilities, ndim=2)
    error = _require_finite("prediction_error", prediction_error, ndim=1)
    if y.shape != p.shape or y.shape[0] != error.shape[0]:
        raise ValueError("labels, probabilities, and prediction_error must align")
    bce = _binary_cross_entropy(y.reshape(-1), p.reshape(-1))
    relevant = p[:, GAP_CHANNELS.index("prediction_error")]
    penalty = float(np.mean((1.0 - relevant) * error))
    return {
        "bce": float(bce),
        "unlogged_error_penalty": penalty,
        "beta": float(beta),
        "total": float(bce + float(beta) * penalty),
    }


def _auroc(labels: np.ndarray, scores: np.ndarray) -> dict[str, Any]:
    y = _require_finite("labels", labels, ndim=1)
    s = _require_finite("scores", scores, ndim=1)
    if y.shape != s.shape:
        raise ValueError("labels and scores must align")
    positives = int(np.sum(y > 0.5))
    negatives = int(y.shape[0] - positives)
    if positives == 0 or negatives == 0:
        return {"value": 0.5, "degenerate": True, "reason": "constant_label"}
    if len(set(float(value) for value in s.tolist())) <= 1:
        return {"value": 0.5, "degenerate": True, "reason": "constant_score"}

    order = np.argsort(s)
    ranks = np.empty_like(order, dtype=np.float64)
    sorted_scores = s[order]
    start = 0
    while start < len(sorted_scores):
        end = start + 1
        while end < len(sorted_scores) and sorted_scores[end] == sorted_scores[start]:
            end += 1
        average_rank = 0.5 * (start + 1 + end)
        ranks[order[start:end]] = average_rank
        start = end
    positive_rank_sum = float(np.sum(ranks[y > 0.5]))
    auc = (positive_rank_sum - positives * (positives + 1) / 2.0) / (positives * negatives)
    return {"value": float(auc), "degenerate": False, "reason": "ok"}


def _ece(labels: np.ndarray, scores: np.ndarray, *, bins: int = ECE_BINS) -> dict[str, Any]:
    y = _require_finite("labels", labels, ndim=1)
    s = _require_finite("scores", scores, ndim=1)
    if y.shape != s.shape:
        raise ValueError("labels and scores must align")
    if np.any((y < 0.0) | (y > 1.0)) or np.any((s < 0.0) | (s > 1.0)):
        raise ValueError("labels and scores must be in [0, 1]")
    rows = []
    total = float(len(y))
    ece = 0.0
    for index in range(int(bins)):
        low = index / float(bins)
        high = (index + 1) / float(bins)
        if index == int(bins) - 1:
            mask = (s >= low) & (s <= high)
        else:
            mask = (s >= low) & (s < high)
        count = int(np.sum(mask))
        if count == 0:
            confidence = math.nan
            accuracy = math.nan
            contribution = 0.0
        else:
            confidence = float(np.mean(s[mask]))
            accuracy = float(np.mean(y[mask]))
            contribution = float((count / total) * abs(accuracy - confidence))
        ece += contribution
        rows.append(
            {
                "bin": index,
                "low": low,
                "high": high,
                "count": count,
                "confidence": confidence,
                "accuracy": accuracy,
                "contribution": contribution,
            }
        )
    return {"value": float(ece), "bins": int(bins), "bin_rows": rows}


def _unlogged_error_rate(error: np.ndarray, gap_score: np.ndarray, *, tau: float) -> float:
    e = _require_finite("error", error, ndim=1)
    g = _require_finite("gap_score", gap_score, ndim=1)
    if e.shape != g.shape:
        raise ValueError("error and gap_score must align")
    return float(np.mean((e > PRIMARY_EPSILON) & (g < float(tau))))


def _gap_sound_scan(error: np.ndarray, gap_score: np.ndarray) -> list[dict[str, float]]:
    e = _require_finite("error", error, ndim=1)
    g = _require_finite("gap_score", gap_score, ndim=1)
    rows = []
    for epsilon in EPSILON_GRID:
        for tau in TAU_GRID:
            low_gap = g < float(tau)
            failures = e > float(epsilon)
            low_gap_count = int(np.sum(low_gap))
            failure_count = int(np.sum(failures))
            if low_gap_count:
                low_gap_sound = float(np.mean(e[low_gap] <= float(epsilon)))
            else:
                low_gap_sound = 1.0
            if failure_count:
                failure_logged = float(np.mean(g[failures] >= float(tau)))
            else:
                failure_logged = 1.0
            rows.append(
                {
                    "tau": float(tau),
                    "epsilon": float(epsilon),
                    "low_gap_implies_error_within_epsilon": low_gap_sound,
                    "error_above_epsilon_implies_gap_at_least_tau": failure_logged,
                    "low_gap_count": low_gap_count,
                    "failure_count": failure_count,
                }
            )
    return rows


def _features_and_labels(*, seed: int) -> dict[str, Any]:
    batch = make_toy_batch(SAMPLE_COUNT, rho=RHO, seed=seed)
    z = distinction._require_finite("z", batch.z)
    z_pair = distinction._require_finite("z_pair", batch.z_pair)
    train_idx, eval_idx = distinction._train_eval_split(z.shape[0], seed=seed)
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
        name: distinction._fit_probe(z[train_idx], label[train_idx])
        for name, label in labels.items()
    }

    probabilities = []
    logits = []
    predictions = []
    signed_margins = []
    errors = []
    transition_changed = []
    for name in DISTINCTIONS:
        pred = distinction._predict_probe(probes[name], z)
        probabilities.append(pred["probabilities"])
        logits.append(pred["logits"])
        predictions.append(pred["predictions"])
        signed_margins.append((2.0 * labels[name] - 1.0) * pred["logits"])
        errors.append((pred["predictions"] != labels[name]).astype(np.float64))
        transition_changed.append((labels[name] != pair_labels[name]).astype(np.float64))
    probability_matrix = np.column_stack(probabilities)
    logit_matrix = np.column_stack(logits)
    prediction_matrix = np.column_stack(predictions)
    margin_matrix = np.column_stack(signed_margins)
    error_matrix = np.column_stack(errors)
    transition_matrix = np.column_stack(transition_changed)
    prediction_error = np.max(error_matrix, axis=1)
    transition_unstable = np.max(transition_matrix, axis=1)

    margin_train = np.min(np.abs(margin_matrix[train_idx]), axis=1)
    margin_threshold = float(np.quantile(margin_train, 0.30))
    min_abs_margin = np.min(np.abs(margin_matrix), axis=1)
    low_margin = (min_abs_margin <= margin_threshold).astype(np.float64)

    off_target_rows = []
    for target in DISTINCTIONS:
        z_changed = distinction._intervene(target, z, z_pair)
        target_off_target = np.zeros(z.shape[0], dtype=np.float64)
        for name in DISTINCTIONS:
            if name == target:
                continue
            before = distinction._predict_probe(probes[name], z)["predictions"]
            after = distinction._predict_probe(probes[name], z_changed)["predictions"]
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
        run_id=f"gaussian-ou-gap-ledger-head-seed-{seed}",
        envelope_artifact=JSON_ARTIFACT,
        report_artifact=REPORT_ARTIFACT,
    )
    quality_scalars = np.array(
        [
            float(quality.metrics.get("quality_q", 0.0)),
            float(quality.metrics.get("quality_margin", 0.0)),
            float(quality.metrics.get("linear_identifiability_r2", 0.0)),
            float(quality.metrics.get("approx_identifiability_proxy", 0.0)),
        ],
        dtype=np.float64,
    )
    quality_features = np.tile(quality_scalars.reshape(1, -1), (z.shape[0], 1))
    features = np.column_stack(
        [
            z,
            probability_matrix,
            logit_matrix,
            prediction_matrix,
            margin_matrix,
            min_abs_margin,
            quality_features,
        ]
    ).astype(np.float64)
    return {
        "features": features,
        "gap_labels": gap_labels,
        "prediction_error": prediction_error,
        "train_idx": train_idx,
        "eval_idx": eval_idx,
        "high_energy_threshold": high_threshold,
        "margin_threshold": margin_threshold,
        "canonical_envelope_projection": {
            "run_id": quality.run_id,
            "source_spec": dict(quality.source_spec),
            "classifier_spec": dict(quality.classifier_spec),
            "metrics": {name: float(value) for name, value in quality.metrics.items()},
            "artifacts": dict(quality.artifacts),
        },
        "label_rates": {
            channel: float(np.mean(gap_labels[:, index]))
            for index, channel in enumerate(GAP_CHANNELS)
        },
        "eval_label_rates": {
            channel: float(np.mean(gap_labels[eval_idx, index]))
            for index, channel in enumerate(GAP_CHANNELS)
        },
    }


def _score_from_probabilities(probabilities: np.ndarray) -> np.ndarray:
    p = _require_finite("probabilities", probabilities, ndim=2)
    prediction_index = GAP_CHANNELS.index("prediction_error")
    return p[:, prediction_index]


def _critical_score_from_probabilities(probabilities: np.ndarray) -> np.ndarray:
    p = _require_finite("probabilities", probabilities, ndim=2)
    return np.max(p, axis=1)


def _metrics_for_arm(
    *,
    arm: str,
    probabilities: np.ndarray,
    labels: np.ndarray,
    prediction_error: np.ndarray,
) -> dict[str, Any]:
    score = _score_from_probabilities(probabilities)
    critical_score = _critical_score_from_probabilities(probabilities)
    return {
        "arm": arm,
        "failure_detection_auroc": _auroc(prediction_error, score),
        "ece": _ece(prediction_error, score),
        "unlogged_error_rate": _unlogged_error_rate(
            prediction_error, score, tau=PRIMARY_TAU
        ),
        "critical_unlogged_error_rate": _unlogged_error_rate(
            prediction_error, critical_score, tau=PRIMARY_TAU
        ),
        "prediction_error_rate": float(np.mean(prediction_error > PRIMARY_EPSILON)),
        "gap_score_mean": float(np.mean(score)),
        "critical_gap_score_mean": float(np.mean(critical_score)),
        "gap_sound_scan": _gap_sound_scan(prediction_error, score),
        "loss": _gap_loss(labels, probabilities, prediction_error),
    }


def _run_record(*, seed: int, seed_index: int) -> dict[str, Any]:
    data = _features_and_labels(seed=seed)
    train_idx = data["train_idx"]
    eval_idx = data["eval_idx"]
    heads = _fit_gap_head(data["features"][train_idx], data["gap_labels"][train_idx])
    eval_probabilities = _predict_gap_head(heads, data["features"][eval_idx])
    eval_labels = data["gap_labels"][eval_idx]
    eval_error = data["prediction_error"][eval_idx]
    vanilla_probabilities = np.zeros_like(eval_probabilities, dtype=np.float64)
    gap_metrics = _metrics_for_arm(
        arm="gap_head",
        probabilities=eval_probabilities,
        labels=eval_labels,
        prediction_error=eval_error,
    )
    vanilla_metrics = _metrics_for_arm(
        arm="vanilla",
        probabilities=vanilla_probabilities,
        labels=eval_labels,
        prediction_error=eval_error,
    )
    return {
        "seed_index": int(seed_index),
        "seed_sequence_position": int(seed_index + 1),
        "seed": int(seed),
        "run_id": f"gaussian-ou-gap-ledger-head-seed-{seed}",
        "config": {
            "sample_count": SAMPLE_COUNT,
            "rho": RHO,
            "use_torch": USE_TORCH,
            "gap_channels": list(GAP_CHANNELS),
            "distinctions": list(DISTINCTIONS),
            "train_fraction": TRAIN_FRACTION,
            "train_count": int(len(train_idx)),
            "eval_count": int(len(eval_idx)),
            "high_energy_threshold": float(data["high_energy_threshold"]),
            "low_margin_threshold": float(data["margin_threshold"]),
            "beta": BETA,
            "primary_tau": PRIMARY_TAU,
            "primary_epsilon": PRIMARY_EPSILON,
        },
        "split": {
            "train_indices": [int(index) for index in train_idx],
            "eval_indices": [int(index) for index in eval_idx],
            "overlap_count": int(len(set(train_idx.tolist()) & set(eval_idx.tolist()))),
        },
        "canonical_envelope_projection": data["canonical_envelope_projection"],
        "gap_label_rates": data["label_rates"],
        "eval_gap_label_rates": data["eval_label_rates"],
        "arms": {
            "vanilla": vanilla_metrics,
            "gap_head": gap_metrics,
        },
        "comparison": {
            "unlogged_error_rate_delta_gap_minus_vanilla": float(
                gap_metrics["unlogged_error_rate"] - vanilla_metrics["unlogged_error_rate"]
            ),
            "critical_unlogged_error_rate_delta_gap_minus_vanilla": float(
                gap_metrics["critical_unlogged_error_rate"]
                - vanilla_metrics["critical_unlogged_error_rate"]
            ),
            "failure_detection_auroc_delta_gap_minus_vanilla": float(
                gap_metrics["failure_detection_auroc"]["value"]
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
    low_gap_sound = []
    failure_logged = []
    for record in records:
        primary = _primary_gap_sound(record["arms"][arm]["gap_sound_scan"])
        low_gap_sound.append(float(primary["low_gap_implies_error_within_epsilon"]))
        failure_logged.append(float(primary["error_above_epsilon_implies_gap_at_least_tau"]))
    return {
        "failure_detection_auroc": metric_stats(auroc),
        "ece": metric_stats(ece),
        "unlogged_error_rate": metric_stats(unlogged),
        "critical_unlogged_error_rate": metric_stats(critical),
        "prediction_error_rate": metric_stats(error_rate),
        "gap_sound_low_gap_implies_error_within_epsilon": metric_stats(low_gap_sound),
        "gap_sound_error_above_epsilon_implies_gap_at_least_tau": metric_stats(failure_logged),
    }


def _primary_gap_sound(rows: list[dict[str, Any]]) -> dict[str, Any]:
    for row in rows:
        if float(row["tau"]) == PRIMARY_TAU and float(row["epsilon"]) == PRIMARY_EPSILON:
            return row
    raise ValueError("primary gap-sound row not found")


def _aggregate(records: list[dict[str, Any]]) -> dict[str, Any]:
    vanilla = _pooled_metrics(records, "vanilla")
    gap = _pooled_metrics(records, "gap_head")
    return {
        "record_count": len(records),
        "seed_order": [int(record["seed"]) for record in records],
        "by_arm": {
            "vanilla": vanilla,
            "gap_head": gap,
        },
        "comparison": {
            "unlogged_error_rate_delta_gap_minus_vanilla": metric_stats(
                [
                    float(record["comparison"]["unlogged_error_rate_delta_gap_minus_vanilla"])
                    for record in records
                ]
            ),
            "critical_unlogged_error_rate_delta_gap_minus_vanilla": metric_stats(
                [
                    float(
                        record["comparison"][
                            "critical_unlogged_error_rate_delta_gap_minus_vanilla"
                        ]
                    )
                    for record in records
                ]
            ),
            "failure_detection_auroc_delta_gap_minus_vanilla": metric_stats(
                [
                    float(
                        record["comparison"][
                            "failure_detection_auroc_delta_gap_minus_vanilla"
                        ]
                    )
                    for record in records
                ]
            ),
        },
    }


def _source_artifacts() -> dict[str, Any]:
    return {
        "generation_script": "scripts/run_gaussian_ou_gap_ledger_head.py",
        "canonical_runner": "scripts/run_gaussian_ou_lejepa.py::run_experiment",
        "distinction_head_runner": "scripts/run_gaussian_ou_distinction_head.py",
        "toy_world": "bedc_quality_lab.toy_world.make_toy_batch",
        "stats_helper": "scripts/experiment_stats.py",
        "json_artifact": JSON_ARTIFACT,
        "report_artifact": REPORT_ARTIFACT,
        "import_dependency_chain": [
            "scripts/run_gaussian_ou_gap_ledger_head.py",
            "scripts.run_gaussian_ou_distinction_head",
            "scripts.run_gaussian_ou_lejepa.run_experiment",
            "bedc_quality_lab.toy_world.make_toy_batch",
            "scripts.experiment_stats.metric_stats",
        ],
    }


def _applicability_boundary() -> dict[str, Any]:
    return {
        "admitted_family": "Gaussian-OU toy world generated by the existing lab toy-world generator.",
        "model": (
            "Script-private numpy logistic gap heads over replayed canonical latent z and "
            "distinction-head predictions."
        ),
        "sample_count": SAMPLE_COUNT,
        "seed_count": SEED_COUNT,
        "rho": RHO,
        "gap_channels": list(GAP_CHANNELS),
        "distinctions": list(DISTINCTIONS),
        "tau_scan_range": list(TAU_GRID),
        "epsilon_scan_range": list(EPSILON_GRID),
        "primary_tau": PRIMARY_TAU,
        "primary_epsilon": PRIMARY_EPSILON,
        "deterministic_fallback_boundary": (
            "The canonical runner is called with use_torch=false; the experiment does not claim "
            "torch-trained representation coverage."
        ),
        "intervention_boundary": (
            "Intervention gaps are finite Gaussian-OU off-target flips induced by distinction-head "
            "operators only."
        ),
    }


def _gap_channel_metadata() -> list[dict[str, str]]:
    return [
        {
            "name": "prediction_error",
            "origin": "observed",
            "definition": "At least one held-out distinction probe predicts the wrong truth label.",
        },
        {
            "name": "low_margin",
            "origin": "constructed",
            "definition": "Minimum absolute distinction margin is below a train-split quantile.",
        },
        {
            "name": "transition_unstable",
            "origin": "observed",
            "definition": "At least one distinction truth label differs under the OU pair.",
        },
        {
            "name": "off_target_intervention",
            "origin": "observed",
            "definition": "A target intervention flips at least one non-target distinction prediction.",
        },
    ]


def _negative_result_note(aggregate: dict[str, Any]) -> str:
    gap_auroc = float(aggregate["by_arm"]["gap_head"]["failure_detection_auroc"]["mean"])
    vanilla_unlogged = float(aggregate["by_arm"]["vanilla"]["unlogged_error_rate"]["mean"])
    gap_unlogged = float(aggregate["by_arm"]["gap_head"]["unlogged_error_rate"]["mean"])
    if abs(gap_auroc - 0.5) <= 0.03:
        return (
            "Failure-detection AUROC is approximately chance under the predeclared protocol; "
            "this is recorded as a negative result rather than retuning thresholds."
        )
    if gap_unlogged >= vanilla_unlogged:
        return (
            "The gap head did not reduce UnloggedErrorRate relative to vanilla under the "
            "predeclared protocol; this is recorded as a negative result."
        )
    return (
        "The gap head reduced UnloggedErrorRate relative to vanilla under the predeclared "
        "protocol; thresholds and beta were not tuned after observing outcomes."
    )


def _payload(records: list[dict[str, Any]]) -> dict[str, Any]:
    aggregate = _aggregate(records)
    return {
        "artifact": JSON_ARTIFACT,
        "report": REPORT_ARTIFACT,
        "generated_at": datetime.now(timezone.utc).isoformat(),
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
        "# Gaussian-OU Gap-Ledger-Head Experiment",
        "",
        f"- Generated at: `{payload['generated_at']}`",
        f"- Canonical runner: `{payload['source_artifacts']['canonical_runner']}`",
        f"- Distinction runner: `{payload['source_artifacts']['distinction_head_runner']}`",
        f"- Sample count: `{payload['config']['sample_count']}`",
        f"- Seed count: `{payload['config']['seed_count']}`",
        f"- Rho: `{payload['config']['rho']}`",
        f"- Use torch: `{str(bool(payload['config']['use_torch'])).lower()}`",
        f"- Gap channels: `{', '.join(payload['config']['gap_channels'])}`",
        f"- Tau grid: `{payload['config']['tau_grid']}`",
        f"- Epsilon grid: `{payload['config']['epsilon_grid']}`",
        f"- Total records: `{aggregate['record_count']}`",
        "",
        "## Vanilla vs Gap-Head",
        "",
        (
            "| arm | failure-detection AUROC | ECE | UnloggedErrorRate | "
            "critical unlogged error rate | prediction error rate |"
        ),
        "| --- | ---: | ---: | ---: | ---: | ---: |",
    ]
    for arm in ("vanilla", "gap_head"):
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
            "## Gap-Sound Primary Check",
            "",
            (
                f"- Primary tau: `{payload['config']['primary_tau']}`; "
                f"primary epsilon: `{payload['config']['primary_epsilon']}`"
            ),
            (
                "- Gap-head `g < tau => PredErr <= epsilon`: "
                f"{_render_stats(aggregate['by_arm']['gap_head']['gap_sound_low_gap_implies_error_within_epsilon'])}"
            ),
            (
                "- Gap-head `PredErr > epsilon => g >= tau`: "
                f"{_render_stats(aggregate['by_arm']['gap_head']['gap_sound_error_above_epsilon_implies_gap_at_least_tau'])}"
            ),
            (
                "- Vanilla `PredErr > epsilon => g >= tau`: "
                f"{_render_stats(aggregate['by_arm']['vanilla']['gap_sound_error_above_epsilon_implies_gap_at_least_tau'])}"
            ),
            "",
            "## Comparison",
            "",
            (
                "- UnloggedErrorRate delta gap-head minus vanilla: "
                f"{_render_stats(comparison['unlogged_error_rate_delta_gap_minus_vanilla'])}"
            ),
            (
                "- Critical unlogged error rate delta gap-head minus vanilla: "
                f"{_render_stats(comparison['critical_unlogged_error_rate_delta_gap_minus_vanilla'])}"
            ),
            (
                "- Failure-detection AUROC delta gap-head minus vanilla: "
                f"{_render_stats(comparison['failure_detection_auroc_delta_gap_minus_vanilla'])}"
            ),
            "",
            "## Gap Channels",
            "",
        ]
    )
    for item in payload["gap_channel_metadata"]:
        lines.append(f"- `{item['name']}` ({item['origin']}): {item['definition']}")

    lines.extend(["", "## Applicability Boundary", ""])
    for key, value in payload["applicability_boundary"].items():
        lines.append(f"- {key}: `{json.dumps(value, sort_keys=True)}`")

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
            f"- JSON artifact: `{payload['source_artifacts']['json_artifact']}`",
            f"- Report artifact: `{payload['source_artifacts']['report_artifact']}`",
            f"- Toy world: `{payload['source_artifacts']['toy_world']}`",
            f"- Stats helper: `{payload['source_artifacts']['stats_helper']}`",
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

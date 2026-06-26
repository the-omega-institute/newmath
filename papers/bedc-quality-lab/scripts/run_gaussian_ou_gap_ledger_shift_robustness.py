#!/usr/bin/env python3
"""Run a Gaussian-OU gap-ledger rho-shift robustness experiment."""

from __future__ import annotations

from dataclasses import dataclass
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
from scripts.experiment_stats import fit_linear_slope, metric_stats
from scripts import run_gaussian_ou_gap_ledger_head as gap_runner


TRAIN_RHO = 0.82
EVAL_RHO_GRID = (0.40, 0.60, 0.82, 0.90, 0.98)
SEED_COUNT = gap_runner.SEED_COUNT
SAMPLE_COUNT = gap_runner.SAMPLE_COUNT
USE_TORCH = gap_runner.USE_TORCH
TRAIN_FRACTION = gap_runner.TRAIN_FRACTION
DISTINCTIONS = gap_runner.DISTINCTIONS
GAP_CHANNELS = gap_runner.GAP_CHANNELS
BETA = gap_runner.BETA
PRIMARY_TAU = gap_runner.PRIMARY_TAU
PRIMARY_EPSILON = gap_runner.PRIMARY_EPSILON
TAU_GRID = gap_runner.TAU_GRID
EPSILON_GRID = gap_runner.EPSILON_GRID
ECE_BINS = gap_runner.ECE_BINS
JSON_ARTIFACT = "reports/gaussian_ou_gap_ledger_shift_robustness.json"
REPORT_ARTIFACT = "reports/gaussian_ou_gap_ledger_shift_robustness.md"


@dataclass(frozen=True)
class GapHeadFitBundle:
    seed: int
    train_rho: float
    heads: dict[str, Any]
    baseline_thresholds: dict[str, float]
    train_surface_projection: dict[str, Any]


@dataclass(frozen=True)
class ShiftEvaluationCell:
    train_rho: float
    eval_rho: float
    seed: int
    shift_distance: float
    train_indices: list[int]
    eval_indices: list[int]
    arms: dict[str, dict[str, Any]]


def _require_finite(name: str, array: np.ndarray, *, ndim: int | None = None) -> np.ndarray:
    value = np.asarray(array, dtype=np.float64)
    if ndim is not None and value.ndim != ndim:
        raise ValueError(f"{name} must be {ndim}-dimensional")
    if value.shape[0] == 0:
        raise ValueError(f"{name} must not be empty")
    if not np.all(np.isfinite(value)):
        raise ValueError(f"{name} contains non-finite values")
    return value


def _seeds() -> list[int]:
    return gap_runner._seeds(count=SEED_COUNT)


def _split_for_seed(n: int, *, seed: int) -> tuple[np.ndarray, np.ndarray]:
    return gap_runner.distinction._train_eval_split(n, seed=seed, train_fraction=TRAIN_FRACTION)


def _fit_baseline_bundle(*, seed: int) -> GapHeadFitBundle:
    data = _features_and_labels(seed=seed, rho=TRAIN_RHO, fit_bundle=None)
    train_idx = data["train_idx"]
    gap_heads = gap_runner._fit_gap_head(
        data["features"][train_idx], data["gap_labels"][train_idx]
    )
    return GapHeadFitBundle(
        seed=int(seed),
        train_rho=float(TRAIN_RHO),
        heads={
            "distinction_probes": data["probes"],
            "gap_head": gap_heads,
        },
        baseline_thresholds={
            "high_energy": float(data["high_energy_threshold"]),
            "low_margin": float(data["margin_threshold"]),
        },
        train_surface_projection={
            "train_count": int(len(train_idx)),
            "eval_count": int(len(data["eval_idx"])),
            "label_rates": data["label_rates"],
            "eval_label_rates": data["eval_label_rates"],
        },
    )


def _features_and_labels(
    *,
    seed: int,
    rho: float,
    fit_bundle: GapHeadFitBundle | None,
) -> dict[str, Any]:
    batch = make_toy_batch(SAMPLE_COUNT, rho=float(rho), seed=int(seed))
    z = gap_runner.distinction._require_finite("z", batch.z)
    z_pair = gap_runner.distinction._require_finite("z_pair", batch.z_pair)
    train_idx, eval_idx = _split_for_seed(z.shape[0], seed=seed)
    high_threshold = (
        gap_runner.distinction._high_energy_threshold(z, train_idx)
        if fit_bundle is None
        else float(fit_bundle.baseline_thresholds["high_energy"])
    )
    labels = {
        name: gap_runner.distinction._label_truth(name, z, high_energy_threshold=high_threshold)
        for name in DISTINCTIONS
    }
    pair_labels = {
        name: gap_runner.distinction._label_truth(
            name, z_pair, high_energy_threshold=high_threshold
        )
        for name in DISTINCTIONS
    }
    if fit_bundle is None:
        probes = {
            name: gap_runner.distinction._fit_probe(z[train_idx], label[train_idx])
            for name, label in labels.items()
        }
    else:
        probes = fit_bundle.heads["distinction_probes"]

    probabilities = []
    logits = []
    predictions = []
    signed_margins = []
    errors = []
    transition_changed = []
    for name in DISTINCTIONS:
        pred = gap_runner.distinction._predict_probe(probes[name], z)
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

    min_abs_margin = np.min(np.abs(margin_matrix), axis=1)
    if fit_bundle is None:
        margin_train = np.min(np.abs(margin_matrix[train_idx]), axis=1)
        margin_threshold = float(np.quantile(margin_train, 0.30))
    else:
        margin_threshold = float(fit_bundle.baseline_thresholds["low_margin"])
    low_margin = (min_abs_margin <= margin_threshold).astype(np.float64)

    off_target_rows = []
    for target in DISTINCTIONS:
        z_changed = gap_runner.distinction._intervene(target, z, z_pair)
        target_off_target = np.zeros(z.shape[0], dtype=np.float64)
        for name in DISTINCTIONS:
            if name == target:
                continue
            before = gap_runner.distinction._predict_probe(probes[name], z)["predictions"]
            after = gap_runner.distinction._predict_probe(probes[name], z_changed)["predictions"]
            target_off_target = np.maximum(target_off_target, (before != after).astype(np.float64))
        off_target_rows.append(target_off_target)
    off_target_intervention = np.max(np.column_stack(off_target_rows), axis=1)

    gap_labels = np.column_stack(
        [prediction_error, low_margin, transition_unstable, off_target_intervention]
    ).astype(np.float64)
    quality = gap_runner.run_experiment(
        use_torch=USE_TORCH,
        sample_count=SAMPLE_COUNT,
        seed=int(seed),
        rho=float(rho),
        run_id=f"gaussian-ou-gap-ledger-shift-rho-{rho:.2f}-seed-{seed}",
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
        "high_energy_threshold": float(high_threshold),
        "margin_threshold": float(margin_threshold),
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
        "probes": probes,
    }


def _metric_projection(metrics: dict[str, Any]) -> dict[str, Any]:
    primary = gap_runner._primary_gap_sound(metrics["gap_sound_scan"])
    return {
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


def _evaluate_shift_cell(
    *,
    fit_bundle: GapHeadFitBundle,
    seed_index: int,
    eval_rho: float,
) -> dict[str, Any]:
    data = _features_and_labels(seed=fit_bundle.seed, rho=eval_rho, fit_bundle=fit_bundle)
    eval_idx = data["eval_idx"]
    eval_probabilities = gap_runner._predict_gap_head(
        fit_bundle.heads["gap_head"], data["features"][eval_idx]
    )
    eval_labels = data["gap_labels"][eval_idx]
    eval_error = data["prediction_error"][eval_idx]
    vanilla_probabilities = np.zeros_like(eval_probabilities, dtype=np.float64)
    gap_metrics = gap_runner._metrics_for_arm(
        arm="gap_head",
        probabilities=eval_probabilities,
        labels=eval_labels,
        prediction_error=eval_error,
    )
    vanilla_metrics = gap_runner._metrics_for_arm(
        arm="vanilla",
        probabilities=vanilla_probabilities,
        labels=eval_labels,
        prediction_error=eval_error,
    )
    shift_distance = abs(float(eval_rho) - float(TRAIN_RHO))
    cell = ShiftEvaluationCell(
        train_rho=float(TRAIN_RHO),
        eval_rho=float(eval_rho),
        seed=int(fit_bundle.seed),
        shift_distance=float(shift_distance),
        train_indices=[int(index) for index in data["train_idx"]],
        eval_indices=[int(index) for index in eval_idx],
        arms={
            "vanilla": _metric_projection(vanilla_metrics),
            "gap_head": _metric_projection(gap_metrics),
        },
    )
    comparison = {
        "unlogged_error_rate_gap_minus_vanilla": float(
            gap_metrics["unlogged_error_rate"] - vanilla_metrics["unlogged_error_rate"]
        ),
        "critical_unlogged_error_rate_gap_minus_vanilla": float(
            gap_metrics["critical_unlogged_error_rate"]
            - vanilla_metrics["critical_unlogged_error_rate"]
        ),
        "failure_detection_auroc_gap_minus_vanilla": float(
            gap_metrics["failure_detection_auroc"]["value"]
            - vanilla_metrics["failure_detection_auroc"]["value"]
        ),
        "ece_gap_minus_vanilla": float(gap_metrics["ece"]["value"] - vanilla_metrics["ece"]["value"]),
        "gap_sound_low_gap_implies_error_delta_gap_minus_vanilla": float(
            cell.arms["gap_head"]["primary_gap_sound"]["low_gap_implies_error_within_epsilon"]
            - cell.arms["vanilla"]["primary_gap_sound"]["low_gap_implies_error_within_epsilon"]
        ),
        "gap_sound_error_above_epsilon_delta_gap_minus_vanilla": float(
            cell.arms["gap_head"]["primary_gap_sound"]["error_above_epsilon_implies_gap_at_least_tau"]
            - cell.arms["vanilla"]["primary_gap_sound"][
                "error_above_epsilon_implies_gap_at_least_tau"
            ]
        ),
    }
    return {
        "seed_index": int(seed_index),
        "seed_sequence_position": int(seed_index + 1),
        "seed": int(fit_bundle.seed),
        "run_id": f"gaussian-ou-gap-ledger-shift-rho-{eval_rho:.2f}-seed-{fit_bundle.seed}",
        "train_rho": float(TRAIN_RHO),
        "eval_rho": float(eval_rho),
        "shift_distance": float(shift_distance),
        "config": {
            "sample_count": int(SAMPLE_COUNT),
            "use_torch": bool(USE_TORCH),
            "gap_channels": list(GAP_CHANNELS),
            "distinctions": list(DISTINCTIONS),
            "train_fraction": float(TRAIN_FRACTION),
            "train_count": int(len(data["train_idx"])),
            "eval_count": int(len(eval_idx)),
            "baseline_high_energy_threshold": float(
                fit_bundle.baseline_thresholds["high_energy"]
            ),
            "baseline_low_margin_threshold": float(fit_bundle.baseline_thresholds["low_margin"]),
            "beta": float(BETA),
            "primary_tau": float(PRIMARY_TAU),
            "primary_epsilon": float(PRIMARY_EPSILON),
        },
        "split": {
            "train_indices": cell.train_indices,
            "eval_indices": cell.eval_indices,
            "overlap_count": int(len(set(cell.train_indices) & set(cell.eval_indices))),
        },
        "canonical_envelope_projection": data["canonical_envelope_projection"],
        "gap_label_rates": data["label_rates"],
        "eval_gap_label_rates": data["eval_label_rates"],
        "shared_error_surface": {
            "denominator": int(len(eval_error)),
            "prediction_error_count": int(np.sum(eval_error > PRIMARY_EPSILON)),
            "prediction_error_rate": float(np.mean(eval_error > PRIMARY_EPSILON)),
            "surface_sha": f"seed:{fit_bundle.seed}:rho:{eval_rho:.2f}:eval-count:{len(eval_error)}",
        },
        "arms": cell.arms,
        "comparison": comparison,
    }


def _records() -> list[dict[str, Any]]:
    records = []
    for seed_index, seed in enumerate(_seeds()):
        fit_bundle = _fit_baseline_bundle(seed=seed)
        for eval_rho in EVAL_RHO_GRID:
            records.append(
                _evaluate_shift_cell(
                    fit_bundle=fit_bundle,
                    seed_index=seed_index,
                    eval_rho=float(eval_rho),
                )
            )
    return records


def _stats_for_arm(records: list[dict[str, Any]], arm: str) -> dict[str, Any]:
    return {
        "failure_detection_auroc": metric_stats(
            [float(record["arms"][arm]["failure_detection_auroc"]["value"]) for record in records]
        ),
        "ece": metric_stats([float(record["arms"][arm]["ece"]["value"]) for record in records]),
        "unlogged_error_rate": metric_stats(
            [float(record["arms"][arm]["unlogged_error_rate"]) for record in records]
        ),
        "critical_unlogged_error_rate": metric_stats(
            [float(record["arms"][arm]["critical_unlogged_error_rate"]) for record in records]
        ),
        "prediction_error_rate": metric_stats(
            [float(record["arms"][arm]["prediction_error_rate"]) for record in records]
        ),
        "gap_sound_low_gap_implies_error_within_epsilon": metric_stats(
            [
                float(
                    record["arms"][arm]["primary_gap_sound"][
                        "low_gap_implies_error_within_epsilon"
                    ]
                )
                for record in records
            ]
        ),
        "gap_sound_error_above_epsilon_implies_gap_at_least_tau": metric_stats(
            [
                float(
                    record["arms"][arm]["primary_gap_sound"][
                        "error_above_epsilon_implies_gap_at_least_tau"
                    ]
                )
                for record in records
            ]
        ),
    }


def _comparison_stats(records: list[dict[str, Any]]) -> dict[str, Any]:
    return {
        key: metric_stats([float(record["comparison"][key]) for record in records])
        for key in (
            "unlogged_error_rate_gap_minus_vanilla",
            "critical_unlogged_error_rate_gap_minus_vanilla",
            "failure_detection_auroc_gap_minus_vanilla",
            "ece_gap_minus_vanilla",
            "gap_sound_low_gap_implies_error_delta_gap_minus_vanilla",
            "gap_sound_error_above_epsilon_delta_gap_minus_vanilla",
        )
    }


def _aggregate_by_rho(records: list[dict[str, Any]]) -> list[dict[str, Any]]:
    rows = []
    baseline_delta = None
    for eval_rho in EVAL_RHO_GRID:
        selected = [record for record in records if float(record["eval_rho"]) == float(eval_rho)]
        if not selected:
            raise ValueError(f"missing eval_rho records: {eval_rho}")
        comparison = _comparison_stats(selected)
        mean_delta = float(comparison["unlogged_error_rate_gap_minus_vanilla"]["mean"])
        if float(eval_rho) == float(TRAIN_RHO):
            baseline_delta = mean_delta
        rows.append(
            {
                "train_rho": float(TRAIN_RHO),
                "eval_rho": float(eval_rho),
                "shift_distance": abs(float(eval_rho) - float(TRAIN_RHO)),
                "record_count": int(len(selected)),
                "seed_order": [int(record["seed"]) for record in selected],
                "by_arm": {
                    "vanilla": _stats_for_arm(selected, "vanilla"),
                    "gap_head": _stats_for_arm(selected, "gap_head"),
                },
                "comparison": comparison,
            }
        )
    if baseline_delta is None:
        raise ValueError("baseline rho is missing from eval grid")
    for row in rows:
        row["comparison"]["unlogged_error_rate_delta_of_delta_relative_to_baseline"] = {
            **metric_stats(
                [
                    float(record["comparison"]["unlogged_error_rate_gap_minus_vanilla"])
                    - baseline_delta
                    for record in records
                    if float(record["eval_rho"]) == float(row["eval_rho"])
                ]
            ),
            "baseline_mean_delta": float(baseline_delta),
        }
    return rows


def _degradation_slope(aggregates: list[dict[str, Any]]) -> dict[str, Any]:
    points = [
        {
            "shift_distance": float(row["shift_distance"]),
            "advantage_degradation": float(
                row["comparison"][
                    "unlogged_error_rate_delta_of_delta_relative_to_baseline"
                ]["mean"]
            ),
        }
        for row in aggregates
    ]
    fit = fit_linear_slope(points, "shift_distance", "advantage_degradation")
    return {
        **fit,
        "x_key": "abs(eval_rho - train_rho)",
        "y_key": "unlogged_error_rate_gap_minus_vanilla_delta_of_delta",
        "interpretation": (
            "positive slope means the gap-head UnloggedErrorRate advantage degrades as rho "
            "moves away from the baseline fit distribution"
        ),
        "points": points,
    }


def _source_artifacts() -> dict[str, Any]:
    artifacts = gap_runner._source_artifacts()
    return {
        "generation_script": "scripts/run_gaussian_ou_gap_ledger_shift_robustness.py",
        "imported_gap_ledger_head_runner": "scripts/run_gaussian_ou_gap_ledger_head.py",
        "canonical_runner": artifacts["canonical_runner"],
        "distinction_head_runner": artifacts["distinction_head_runner"],
        "toy_world": artifacts["toy_world"],
        "stats_helper": artifacts["stats_helper"],
        "json_artifact": JSON_ARTIFACT,
        "report_artifact": REPORT_ARTIFACT,
        "import_dependency_chain": [
            "scripts/run_gaussian_ou_gap_ledger_shift_robustness.py",
            "scripts.run_gaussian_ou_gap_ledger_head",
            *artifacts["import_dependency_chain"],
        ],
    }


def _applicability_boundary() -> dict[str, Any]:
    return {
        "admitted_family": "Gaussian-OU toy world generated by the existing lab toy-world generator.",
        "model": (
            "Script-private numpy gap-head evaluation over the #475 gap-ledger-head feature "
            "and metric semantics."
        ),
        "sample_count": int(SAMPLE_COUNT),
        "seed_count": int(SEED_COUNT),
        "rho_grid": list(EVAL_RHO_GRID),
        "baseline_train_rho": float(TRAIN_RHO),
        "baseline_freeze_protocol": (
            "For each seed, distinction probes, high-energy and low-margin thresholds, and "
            "the gap head are fit only at baseline rho before fixed application to all eval rho cells."
        ),
        "primary_tau": float(PRIMARY_TAU),
        "primary_epsilon": float(PRIMARY_EPSILON),
        "shift_surface_kind": "ou_pair_process",
        "rho_axis_boundary": (
            "The single rho axis changes the OU pair process z_pair|z and does not claim a "
            "changed z marginal."
        ),
        "observation_noise_boundary": (
            "The current make_toy_batch API exposes no observation-noise parameter; this artifact "
            "does not cover observation-noise OOD."
        ),
        "expected_channel_sensitivity": (
            "Observed degradation may concentrate in transition_unstable and intervention channels "
            "because rho primarily changes z_pair|z."
        ),
        "deterministic_fallback_boundary": (
            "The canonical runner is called with use_torch=false through the imported #475 helper "
            "semantics; the experiment does not claim torch-trained representation coverage."
        ),
    }


def _negative_result_note(aggregate: dict[str, Any]) -> str:
    slope = float(aggregate["advantage_degradation_slope"]["slope"])
    baseline = next(
        row for row in aggregate["by_eval_rho"] if float(row["eval_rho"]) == float(TRAIN_RHO)
    )
    baseline_delta = float(
        baseline["comparison"]["unlogged_error_rate_gap_minus_vanilla"]["mean"]
    )
    worst_delta = max(
        float(row["comparison"]["unlogged_error_rate_gap_minus_vanilla"]["mean"])
        for row in aggregate["by_eval_rho"]
    )
    if worst_delta >= 0.0:
        return (
            "At least one predeclared rho cell lost the gap-head UnloggedErrorRate advantage; "
            "this is recorded as a negative result without retuning tau, epsilon, thresholds, "
            "or the rho grid."
        )
    if math.isfinite(slope) and slope > 0.0:
        return (
            "The gap-head UnloggedErrorRate advantage degrades with rho shift under the "
            "predeclared baseline-freeze protocol; the degradation is recorded without "
            "post-hoc retuning."
        )
    return (
        "The gap-head UnloggedErrorRate advantage remains below vanilla across the predeclared "
        f"rho grid relative to the baseline mean delta {baseline_delta:.6f}; no tau, epsilon, "
        "threshold, or rho-grid tuning was applied after observing outcomes."
    )


def _aggregate(records: list[dict[str, Any]]) -> dict[str, Any]:
    by_eval_rho = _aggregate_by_rho(records)
    slope = _degradation_slope(by_eval_rho)
    return {
        "record_count": int(len(records)),
        "cell_count": int(len(EVAL_RHO_GRID)),
        "seed_count": int(SEED_COUNT),
        "seed_order": _seeds(),
        "expected_record_count": int(SEED_COUNT * len(EVAL_RHO_GRID)),
        "by_eval_rho": by_eval_rho,
        "advantage_degradation_slope": slope,
    }


def _payload(records: list[dict[str, Any]]) -> dict[str, Any]:
    aggregate = _aggregate(records)
    return {
        "artifact": JSON_ARTIFACT,
        "report": REPORT_ARTIFACT,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "config": {
            "sample_count": int(SAMPLE_COUNT),
            "seed_count": int(SEED_COUNT),
            "seeds": _seeds(),
            "train_rho": float(TRAIN_RHO),
            "eval_rho_grid": list(EVAL_RHO_GRID),
            "use_torch": bool(USE_TORCH),
            "distinctions": list(DISTINCTIONS),
            "gap_channels": list(GAP_CHANNELS),
            "train_fraction": float(TRAIN_FRACTION),
            "gap_steps": int(gap_runner.GAP_STEPS),
            "gap_lr": float(gap_runner.GAP_LR),
            "gap_l2": float(gap_runner.GAP_L2),
            "beta": float(BETA),
            "primary_tau": float(PRIMARY_TAU),
            "primary_epsilon": float(PRIMARY_EPSILON),
            "tau_grid": list(TAU_GRID),
            "epsilon_grid": list(EPSILON_GRID),
            "ece_bins": int(ECE_BINS),
            "expected_record_count": int(SEED_COUNT * len(EVAL_RHO_GRID)),
        },
        "source_artifacts": _source_artifacts(),
        "applicability_boundary": _applicability_boundary(),
        "records": records,
        "aggregate": aggregate,
        "negative_result_note": _negative_result_note(aggregate),
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
    slope = aggregate["advantage_degradation_slope"]
    lines = [
        "# Gaussian-OU Gap-Ledger Shift Robustness",
        "",
        f"- Generated at: `{payload['generated_at']}`",
        f"- JSON numeric source: `{payload['artifact']}`",
        f"- Canonical runner: `{payload['source_artifacts']['canonical_runner']}`",
        f"- Imported gap-ledger runner: `{payload['source_artifacts']['imported_gap_ledger_head_runner']}`",
        f"- Sample count: `{payload['config']['sample_count']}`",
        f"- Seed count: `{payload['config']['seed_count']}`",
        f"- Baseline train rho: `{payload['config']['train_rho']}`",
        f"- Eval rho grid: `{payload['config']['eval_rho_grid']}`",
        f"- Primary tau: `{payload['config']['primary_tau']}`",
        f"- Primary epsilon: `{payload['config']['primary_epsilon']}`",
        f"- Total records: `{aggregate['record_count']}`",
        "",
        "## Predeclared Protocol",
        "",
        (
            "Each seed fits distinction probes, high-energy and low-margin thresholds, and the "
            "gap head once at baseline rho. The frozen fit is then applied to every rho cell. "
            "Vanilla and gap-head arms share the same prediction-error surface and denominator."
        ),
        "",
        "## Rho Cells",
        "",
        (
            "| eval rho | shift distance | arm | UnloggedErrorRate | AUROC | ECE | "
            "g<tau => PredErr<=epsilon | PredErr>epsilon => g>=tau | gap minus vanilla UER |"
        ),
        "| ---: | ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |",
    ]
    for row in aggregate["by_eval_rho"]:
        comparison = row["comparison"]["unlogged_error_rate_gap_minus_vanilla"]
        for arm in ("vanilla", "gap_head"):
            stats = row["by_arm"][arm]
            lines.append(
                "| "
                f"{_format_float(float(row['eval_rho']))} | "
                f"{_format_float(float(row['shift_distance']))} | "
                f"`{arm}` | "
                f"{_render_stats(stats['unlogged_error_rate'])} | "
                f"{_render_stats(stats['failure_detection_auroc'])} | "
                f"{_render_stats(stats['ece'])} | "
                f"{_render_stats(stats['gap_sound_low_gap_implies_error_within_epsilon'])} | "
                f"{_render_stats(stats['gap_sound_error_above_epsilon_implies_gap_at_least_tau'])} | "
                f"{_render_stats(comparison)} |"
            )
    lines.extend(
        [
            "",
            "## Advantage Degradation",
            "",
            (
                "- Slope: "
                f"`{_format_float(float(slope['slope']))}` "
                f"(95% CI `{_format_float(float(slope['slope_ci95_low']))}` to "
                f"`{_format_float(float(slope['slope_ci95_high']))}`)"
            ),
            f"- Status: `{slope['status']}`",
            f"- Interpretation: {slope['interpretation']}",
            "",
            "| eval rho | shift distance | delta-of-delta relative to baseline |",
            "| ---: | ---: | ---: |",
        ]
    )
    for row in aggregate["by_eval_rho"]:
        delta = row["comparison"]["unlogged_error_rate_delta_of_delta_relative_to_baseline"]
        lines.append(
            "| "
            f"{_format_float(float(row['eval_rho']))} | "
            f"{_format_float(float(row['shift_distance']))} | "
            f"{_render_stats(delta)} |"
        )
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

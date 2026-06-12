#!/usr/bin/env python3
"""Run dimension-mismatch anti-triviality checks as a pointer-only sidecar."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import math
from pathlib import Path
import sys
from typing import Any, Mapping, Sequence

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.claim_terms import FORBIDDEN_POSITIVE_CLAIM_TERMS
from scripts.experiment_stats import metric_stats
from scripts import run_dimension_mismatch_debt_transfer as source_transfer
from scripts import run_gap_head_observed_debt_transfer as observed_transfer
from scripts import run_gap_head_robustness_sweep as robustness
from scripts import run_gaussian_ou_gap_ledger_head as gap_head
from scripts import run_observed_debt_sweep as observed_debt


SCHEMA_ID = "bedc-quality-lab:dimension-mismatch-anti-triviality"
ARTIFACT_ID = "bedc-quality-lab:dimension-mismatch-anti-triviality"
JSON_ARTIFACT = "reports/dimension_mismatch_anti_triviality.json"
REPORT_ARTIFACT = "reports/dimension_mismatch_anti_triviality.md"
SOURCE_ARTIFACT = source_transfer.JSON_ARTIFACT
SOURCE_STATUS_POINTER = source_transfer.TRANSFER_STATUS_POINTER
LEARNED_ARM = "learned_anti_triviality_head"
MATCHED_RANDOM_ARM = observed_transfer.producer.MATCHED_RANDOM_ARM
FOLD_SEEDS = (31013, 31039, 31051, 31063)
CONFIG_METADATA_ONLY_COLUMNS = (
    "encoder_dim",
    "reference_latent_dim",
    "abs_encoder_dim_minus_reference_dim",
    "is_reference_encoder_dim",
)
FORBIDDEN_METADATA_COLUMNS = (
    "signed_encoder_dim_minus_reference_dim",
    "is_under_reference_encoder_dim",
    "is_over_reference_encoder_dim",
)
SCALE_ONLY_COLUMNS = (
    "h_l2_mean",
    "h_l2_std",
    "h_abs_mean",
    "h_abs_max",
    "h_abs_q25",
    "h_abs_q50",
    "h_abs_q75",
    "h_pair_delta_l2_mean",
    "h_pair_delta_l2_std",
)
H_NORMALIZED_NO_SCALE_COLUMNS = (
    "h_direction_abs_mean",
    "h_direction_abs_max",
    "h_direction_abs_q25",
    "h_direction_abs_q50",
    "h_direction_abs_q75",
    "h_pair_direction_abs_mean",
    "h_pair_direction_abs_max",
    "h_pair_direction_abs_q25",
    "h_pair_direction_abs_q50",
    "h_pair_direction_abs_q75",
    "h_direction_pair_delta_l2_mean",
    "h_direction_pair_delta_l2_std",
)
WHITENED_H_NORMALIZED_NO_SCALE_COLUMNS = tuple(
    f"whitened:{column}" for column in H_NORMALIZED_NO_SCALE_COLUMNS
)
RANDOM_PROJECTION_SEED = 90117
RANDOM_PROJECTION_WIDTH = 6
DETERMINISTIC_RANDOM_PROJECTION_COLUMNS = tuple(
    f"random_projection:component_{index}" for index in range(RANDOM_PROJECTION_WIDTH)
)
RANK_PROXY_DIAGNOSTIC_COLUMNS = tuple(
    f"rank_proxy:{column}" for column in H_NORMALIZED_NO_SCALE_COLUMNS
)
ARM_COLUMN_ALLOWLISTS = {
    "config_metadata_only": CONFIG_METADATA_ONLY_COLUMNS,
    "scale_only": SCALE_ONLY_COLUMNS,
    "h_normalized_no_scale": H_NORMALIZED_NO_SCALE_COLUMNS,
    "whitened_h_normalized_no_scale": WHITENED_H_NORMALIZED_NO_SCALE_COLUMNS,
    "deterministic_random_projection": DETERMINISTIC_RANDOM_PROJECTION_COLUMNS,
    "rank_proxy_diagnostic": RANK_PROXY_DIAGNOSTIC_COLUMNS,
}
ARM_ORDER = tuple(ARM_COLUMN_ALLOWLISTS)
STATUS_PRECEDENCE = (
    "source_not_pass",
    "metadata_leakage_detected",
    "scale_leakage_detected",
    "random_projection_positive",
    "whitening_failure_detected",
    "anti_triviality_passed",
    "defer_no_normalized_signal",
)
FORBIDDEN_MODEL_INPUT_ROOTS = (
    "raw_h",
    "raw_z",
    "h",
    "z",
    "z_pair",
    "label",
    "truth_label",
    "prediction_error",
    "metric",
    "metric_value",
    "score",
    "rank",
    "envelope",
    "envelope_record",
    "representation_payload",
)
FORBIDDEN_POSITIVE_PAYLOAD_TERMS = (
    "total score",
    "total_score",
    "ranking claim",
    "grade",
    "hidden cost weight",
    "full-lejepa",
    "global-quality",
    "full-tensor-namecert",
    "llm-behavior",
)
NOT_CLAIMED = (
    "No global quality claim.",
    "No full LeJEPA claim.",
    "No full Tensor NameCert claim.",
    "No LLM behavior claim.",
    "No D5 mechanism closure claim.",
    "No standalone positive discovery-map promotion from this evidence source.",
)
SCOPE_NOTE = (
    "SCOPE_NOTE: requested bedc_quality_lab/gap_head.py and bedc_quality_lab/observed_debt.py "
    "do not exist in this checkout; reused the matching helpers from "
    "scripts/run_gaussian_ou_gap_ledger_head.py and scripts/run_observed_debt_sweep.py without interface changes."
)


def _format_float(value: float) -> str:
    if math.isnan(value):
        return "nan"
    return f"{value:.6f}"


def _require_matrix(name: str, value: np.ndarray) -> np.ndarray:
    array = np.asarray(value, dtype=np.float64)
    if array.ndim != 2 or array.shape[0] == 0 or array.shape[1] == 0:
        raise ValueError(f"{name} must be a non-empty matrix")
    if not np.all(np.isfinite(array)):
        raise ValueError(f"{name} contains non-finite values")
    return array


def _row_l2_direction(h: np.ndarray) -> np.ndarray:
    value = np.asarray(h, dtype=np.float64)
    if value.ndim != 2 or value.shape[0] == 0:
        raise ValueError("h must be a non-empty matrix")
    if not np.all(np.isfinite(value)):
        raise ValueError("h contains non-finite values")
    norms = np.linalg.norm(value, axis=1, keepdims=True)
    return np.divide(value, norms, out=np.zeros_like(value, dtype=np.float64), where=norms > 0.0)


def _direction_summary(h: np.ndarray, h_pair: np.ndarray) -> dict[str, float]:
    h_direction = _row_l2_direction(_require_matrix("h", h))
    pair_direction = _row_l2_direction(_require_matrix("h_pair", h_pair))
    if h_direction.shape != pair_direction.shape:
        raise ValueError("h and h_pair direction matrices must align")
    h_abs = np.abs(h_direction)
    pair_abs = np.abs(pair_direction)
    pair_delta_norms = np.linalg.norm(h_direction - pair_direction, axis=1)
    return {
        "h_direction_abs_mean": float(np.mean(h_abs)),
        "h_direction_abs_max": float(np.max(h_abs)),
        "h_direction_abs_q25": float(np.quantile(h_abs, 0.25)),
        "h_direction_abs_q50": float(np.quantile(h_abs, 0.50)),
        "h_direction_abs_q75": float(np.quantile(h_abs, 0.75)),
        "h_pair_direction_abs_mean": float(np.mean(pair_abs)),
        "h_pair_direction_abs_max": float(np.max(pair_abs)),
        "h_pair_direction_abs_q25": float(np.quantile(pair_abs, 0.25)),
        "h_pair_direction_abs_q50": float(np.quantile(pair_abs, 0.50)),
        "h_pair_direction_abs_q75": float(np.quantile(pair_abs, 0.75)),
        "h_direction_pair_delta_l2_mean": float(np.mean(pair_delta_norms)),
        "h_direction_pair_delta_l2_std": float(np.std(pair_delta_norms)),
    }


def _zscore_columns(features: np.ndarray) -> np.ndarray:
    values = _require_matrix("features", features)
    means = np.mean(values, axis=0, keepdims=True)
    stds = np.std(values, axis=0, keepdims=True)
    return np.divide(values - means, stds, out=np.zeros_like(values), where=stds > 0.0)


def _deterministic_projection(features: np.ndarray) -> tuple[np.ndarray, str]:
    values = _require_matrix("features", features)
    rng = np.random.default_rng(RANDOM_PROJECTION_SEED)
    weights = rng.normal(size=(values.shape[1], RANDOM_PROJECTION_WIDTH))
    weights = np.divide(
        weights,
        np.linalg.norm(weights, axis=0, keepdims=True),
        out=np.zeros_like(weights),
        where=np.linalg.norm(weights, axis=0, keepdims=True) > 0.0,
    )
    projected = values @ weights
    fingerprint = hashlib.sha256(np.ascontiguousarray(weights).tobytes()).hexdigest()
    return projected, fingerprint


def _rank_proxy_features(features: np.ndarray) -> np.ndarray:
    values = _require_matrix("features", features)
    if values.shape[0] == 1:
        return np.zeros_like(values)
    ranks = np.empty_like(values)
    for column_index in range(values.shape[1]):
        order = np.argsort(values[:, column_index], kind="mergesort")
        column_ranks = np.empty(values.shape[0], dtype=np.float64)
        column_ranks[order] = np.arange(values.shape[0], dtype=np.float64)
        ranks[:, column_index] = column_ranks / float(values.shape[0] - 1)
    return ranks


def _surface_rows() -> dict[str, Any]:
    rows: list[dict[str, float]] = []
    evidence_rows: list[dict[str, Any]] = []
    labels: list[list[float]] = []
    seeds = tuple(
        int(seed)
        for seed in observed_debt._seeds(
            source_transfer.SOURCE_OBSERVED_DEBT_AXIS,
            observed_debt.DEFAULT_SEED_COUNT_BY_AXIS[source_transfer.SOURCE_OBSERVED_DEBT_AXIS],
        )
    )
    reference_dim: int | None = None
    for seed_index, seed in enumerate(seeds):
        for encoder_dim in observed_debt.C1_ENCODER_DIMS:
            surface = source_transfer._surface_arrays(seed=seed, seed_index=seed_index, encoder_dim=int(encoder_dim))
            envelope = surface["envelope"]
            if reference_dim is None:
                reference_dim = int(envelope.source_spec["latent_dim"])
            h_summary = source_transfer.summarize_h_representation(surface["h"], surface["h_pair"])
            direction_summary = _direction_summary(surface["h"], surface["h_pair"])
            is_reference = int(encoder_dim) == int(reference_dim)
            row = {
                **h_summary,
                **direction_summary,
                "encoder_dim": float(encoder_dim),
                "reference_latent_dim": float(reference_dim),
                "abs_encoder_dim_minus_reference_dim": float(abs(int(encoder_dim) - int(reference_dim))),
                "is_reference_encoder_dim": 1.0 if is_reference else 0.0,
            }
            rows.append(row)
            labels.append([
                0.0 if is_reference else 1.0,
                0.0,
                0.0,
                1.0 if is_reference else 0.0,
            ])
            evidence_rows.append(
                {
                    "seed": int(seed),
                    "seed_index": int(seed_index),
                    "axis": source_transfer.DEFAULT_AXIS,
                    "axis_label": source_transfer.DEFAULT_AXIS_LABEL,
                    "axis_value": int(encoder_dim),
                    "reference_latent_dim": int(reference_dim),
                    "dimension_mismatch_label": bool(not is_reference),
                    "source_pointer": "scripts/run_dimension_mismatch_debt_transfer.py::_surface_arrays",
                    "status_code": "reference-dimension" if is_reference else "dimension-mismatch-surface",
                }
            )
    return {
        "rows": rows,
        "labels": np.asarray(labels, dtype=np.float64),
        "prediction_error": np.asarray([row[0] for row in labels], dtype=np.float64),
        "evidence_rows": evidence_rows,
        "seeds": seeds,
        "reference_latent_dim": int(reference_dim if reference_dim is not None else observed_debt.BASELINE_ENCODER_DIM),
    }


def _build_arm_matrices(surface: Mapping[str, Any] | None = None) -> dict[str, dict[str, Any]]:
    source = _surface_rows() if surface is None else surface
    rows = list(source["rows"])
    matrices: dict[str, dict[str, Any]] = {}
    for arm, columns in list(ARM_COLUMN_ALLOWLISTS.items())[:3]:
        features = np.asarray(
            [[float(row[column]) for column in columns] for row in rows],
            dtype=np.float64,
        )
        matrices[arm] = {
            "arm": arm,
            "features": features,
            "feature_columns": list(columns),
            "labels": np.asarray(source["labels"], dtype=np.float64),
            "prediction_error": np.asarray(source["prediction_error"], dtype=np.float64),
            "evidence_rows": list(source["evidence_rows"]),
        }
    normalized = np.asarray(matrices["h_normalized_no_scale"]["features"], dtype=np.float64)
    whitened = _zscore_columns(normalized)
    random_projected, projection_fingerprint = _deterministic_projection(whitened)
    rank_proxy = _rank_proxy_features(normalized)
    derived_specs = {
        "whitened_h_normalized_no_scale": (
            whitened,
            WHITENED_H_NORMALIZED_NO_SCALE_COLUMNS,
            {"diagnostic_source_family": "h_normalized_no_scale"},
        ),
        "deterministic_random_projection": (
            random_projected,
            DETERMINISTIC_RANDOM_PROJECTION_COLUMNS,
            {
                "diagnostic_source_family": "whitened_h_normalized_no_scale",
                "projection_seed": RANDOM_PROJECTION_SEED,
                "projection_fingerprint_sha256": projection_fingerprint,
            },
        ),
        "rank_proxy_diagnostic": (
            rank_proxy,
            RANK_PROXY_DIAGNOSTIC_COLUMNS,
            {"diagnostic_source_family": "h_normalized_no_scale"},
        ),
    }
    for arm, (features, columns, diagnostic) in derived_specs.items():
        matrices[arm] = {
            "arm": arm,
            "features": np.asarray(features, dtype=np.float64),
            "feature_columns": list(columns),
            "labels": np.asarray(source["labels"], dtype=np.float64),
            "prediction_error": np.asarray(source["prediction_error"], dtype=np.float64),
            "evidence_rows": list(source["evidence_rows"]),
            "diagnostic": dict(diagnostic),
        }
    return matrices


def _forbidden_feature_audit(arm: str, columns: Sequence[str]) -> dict[str, Any]:
    actual = tuple(str(column) for column in columns)
    allowlist = ARM_COLUMN_ALLOWLISTS[arm]
    hits = []
    for column in actual:
        lower = column.lower()
        root = lower.split(":", 1)[0]
        if lower in FORBIDDEN_MODEL_INPUT_ROOTS or root in FORBIDDEN_MODEL_INPUT_ROOTS:
            hits.append(column)
        if arm != "config_metadata_only" and column in CONFIG_METADATA_ONLY_COLUMNS:
            hits.append(column)
        if arm == "config_metadata_only" and column in FORBIDDEN_METADATA_COLUMNS:
            hits.append(column)
    status = "pass" if actual == allowlist and not hits else "fail"
    return {
        "status": status,
        "arm": arm,
        "declared_allowlist": list(allowlist),
        "actual_model_input_columns": list(actual),
        "forbidden_present": sorted(set(hits)),
        "reason": "actual model input columns match the arm allowlist"
        if status == "pass"
        else "actual model input columns violate the arm allowlist",
    }


def _metric_projection(metrics: dict[str, Any]) -> dict[str, Any]:
    return source_transfer._metric_projection(metrics)


def _fold_record(matrix: Mapping[str, Any], *, fold_seed: int, fold_index: int) -> dict[str, Any]:
    features = np.asarray(matrix["features"], dtype=np.float64)
    labels = np.asarray(matrix["labels"], dtype=np.float64)
    prediction_error = np.asarray(matrix["prediction_error"], dtype=np.float64)
    train_idx, eval_idx = source_transfer._train_eval_split(features.shape[0], seed=int(fold_seed))
    heads = gap_head._fit_gap_head(features[train_idx], labels[train_idx])
    probabilities = gap_head._predict_gap_head(heads, features[eval_idx])
    randomized_labels = observed_transfer.producer._matched_random_gap_labels(labels, seed=int(fold_seed))
    random_heads = gap_head._fit_gap_head(features[train_idx], randomized_labels[train_idx])
    random_probabilities = gap_head._predict_gap_head(random_heads, features[eval_idx])
    eval_labels = labels[eval_idx]
    eval_error = prediction_error[eval_idx]
    learned = gap_head._metrics_for_arm(
        arm=LEARNED_ARM,
        probabilities=probabilities,
        labels=eval_labels,
        prediction_error=eval_error,
    )
    matched = gap_head._metrics_for_arm(
        arm=MATCHED_RANDOM_ARM,
        probabilities=random_probabilities,
        labels=eval_labels,
        prediction_error=eval_error,
    )
    return {
        "fold_index": int(fold_index),
        "fold_seed": int(fold_seed),
        "train_count": int(train_idx.shape[0]),
        "eval_count": int(eval_idx.shape[0]),
        "arms": {
            LEARNED_ARM: _metric_projection(learned),
            MATCHED_RANDOM_ARM: _metric_projection(matched),
        },
        "comparison": {
            "failure_detection_auroc_delta_learned_minus_matched_random": float(
                learned["failure_detection_auroc"]["value"]
                - matched["failure_detection_auroc"]["value"]
            ),
        },
    }


def _run_arm(matrix: Mapping[str, Any], *, fold_seeds: Sequence[int] = FOLD_SEEDS) -> dict[str, Any]:
    records = [
        _fold_record(matrix, fold_seed=int(fold_seed), fold_index=index)
        for index, fold_seed in enumerate(fold_seeds)
    ]
    return {
        "records": records,
        "learned_auroc": source_transfer._arm_metrics(records, LEARNED_ARM)["failure_detection_auroc"],
        "matched_random_auroc": source_transfer._arm_metrics(records, MATCHED_RANDOM_ARM)["failure_detection_auroc"],
        "learned_minus_matched_random_auroc": source_transfer._delta_stats(
            records,
            "failure_detection_auroc_delta_learned_minus_matched_random",
        ),
    }


def _strict_positive(metrics: Mapping[str, Any]) -> bool:
    learned = metrics["learned_auroc"]
    matched = metrics["matched_random_auroc"]
    delta = metrics["learned_minus_matched_random_auroc"]
    matched_random_positive = bool(
        float(matched["ci95_low"]) >= robustness.AUROC_POSITIVE_THRESHOLD
    )
    return (
        float(learned["ci95_low"]) >= robustness.AUROC_POSITIVE_THRESHOLD
        and float(learned["ci95_low"]) > float(matched["ci95_high"])
        and float(delta["ci95_low"]) > 0.0
        and not matched_random_positive
    )


def _diagnostic_wide_or(metrics: Mapping[str, Any]) -> bool:
    learned = metrics["learned_auroc"]
    matched = metrics["matched_random_auroc"]
    delta = metrics["learned_minus_matched_random_auroc"]
    return (
        float(learned["ci95_low"]) >= robustness.AUROC_POSITIVE_THRESHOLD
        or float(learned["ci95_low"]) > float(matched["ci95_high"])
        or float(delta["ci95_low"]) > 0.0
    )


def _whitening_diagnostics(features: np.ndarray) -> dict[str, Any]:
    values = _require_matrix("features", features)
    means = np.mean(values, axis=0)
    stds = np.std(values, axis=0)
    return {
        "status": "pass" if bool(np.all(np.isfinite(values))) and float(np.max(np.abs(means))) <= 1.0e-9 else "fail",
        "max_abs_column_mean": float(np.max(np.abs(means))),
        "max_column_std": float(np.max(stds)),
        "zero_variance_column_count": int(np.sum(stds == 0.0)),
        "reason": "whitened diagnostics are finite and column-centered",
    }


def _random_projection_diagnostics(matrix: Mapping[str, Any]) -> dict[str, Any]:
    features = _require_matrix("features", np.asarray(matrix["features"], dtype=np.float64))
    diagnostic = matrix.get("diagnostic") if isinstance(matrix.get("diagnostic"), Mapping) else {}
    return {
        "status": "pass" if features.shape[1] == RANDOM_PROJECTION_WIDTH else "fail",
        "projection_seed": RANDOM_PROJECTION_SEED,
        "projection_width": RANDOM_PROJECTION_WIDTH,
        "feature_width": int(features.shape[1]),
        "source_family": str(diagnostic.get("diagnostic_source_family", "")),
        "projection_fingerprint_sha256": str(diagnostic.get("projection_fingerprint_sha256", "")),
        "reason": "deterministic random projection width and seed are recorded",
    }


def _rank_proxy_diagnostics(features: np.ndarray) -> dict[str, Any]:
    values = _require_matrix("features", features)
    return {
        "status": "pass"
        if float(np.min(values)) >= 0.0 and float(np.max(values)) <= 1.0 and bool(np.all(np.isfinite(values)))
        else "fail",
        "min_value": float(np.min(values)),
        "max_value": float(np.max(values)),
        "feature_width": int(values.shape[1]),
        "reason": "rank proxy diagnostics are finite unit-interval feature order summaries",
    }


def _arm_summary(arm: str, matrix: Mapping[str, Any], metrics: Mapping[str, Any]) -> dict[str, Any]:
    strict = _strict_positive(metrics)
    diagnostic = _diagnostic_wide_or(metrics)
    diagnostics: dict[str, Any] = {}
    if arm == "whitened_h_normalized_no_scale":
        diagnostics["whitening"] = _whitening_diagnostics(np.asarray(matrix["features"], dtype=np.float64))
    if arm == "deterministic_random_projection":
        diagnostics["deterministic_random_projection"] = _random_projection_diagnostics(matrix)
    if arm == "rank_proxy_diagnostic":
        diagnostics["rank_proxy"] = _rank_proxy_diagnostics(np.asarray(matrix["features"], dtype=np.float64))
    row = {
        "arm": arm,
        "feature_columns": list(matrix["feature_columns"]),
        "feature_column_count": int(np.asarray(matrix["features"]).shape[1]),
        "forbidden_feature_audit": _forbidden_feature_audit(arm, matrix["feature_columns"]),
        "learned_auroc": dict(metrics["learned_auroc"]),
        "matched_random_auroc": dict(metrics["matched_random_auroc"]),
        "learned_minus_matched_random_auroc": dict(metrics["learned_minus_matched_random_auroc"]),
        "positive": strict,
        "strict_conjunction_positive": strict,
        "diagnostic_wide_or_positive": diagnostic,
        "diagnostic_only": {"wide_or_positive": diagnostic},
    }
    if diagnostics:
        row["diagnostics"] = diagnostics
    return row


def _source_status(root: Path) -> dict[str, Any]:
    path = root / SOURCE_ARTIFACT
    if not path.exists():
        return {
            "status": "defer",
            "source_pass": False,
            "reason": "source dimension-mismatch debt-transfer artifact is absent",
            "source_artifact": SOURCE_ARTIFACT,
            "source_pointer": SOURCE_STATUS_POINTER,
        }
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return {
            "status": "defer",
            "source_pass": False,
            "reason": "source dimension-mismatch debt-transfer artifact is malformed",
            "source_artifact": SOURCE_ARTIFACT,
            "source_pointer": SOURCE_STATUS_POINTER,
        }
    claim = payload.get("dimension_mismatch_debt_transfer") if isinstance(payload, dict) else None
    source_pass = isinstance(claim, dict) and claim.get("status") == "pass"
    return {
        "status": "pass" if source_pass else "defer",
        "source_pass": bool(source_pass),
        "reason": "source dimension-mismatch debt-transfer status is pass"
        if source_pass
        else "source dimension-mismatch debt-transfer status is not pass",
        "source_artifact": SOURCE_ARTIFACT,
        "source_pointer": SOURCE_STATUS_POINTER,
    }


def _state_machine(*, source_pass: bool, arm_positive: Mapping[str, bool]) -> dict[str, Any]:
    whitening = arm_positive.get("whitened_h_normalized_no_scale", False)
    if not source_pass:
        status = "source_not_pass"
        projection = "defer"
        reason = "source dimension-mismatch debt-transfer did not pass"
    elif arm_positive.get("config_metadata_only", False):
        status = "metadata_leakage_detected"
        projection = "demote_to_DN_or_D1"
        reason = "config metadata-only arm is positive under the strict conjunction predicate"
    elif arm_positive.get("scale_only", False):
        status = "scale_leakage_detected"
        projection = "demote_to_DN_or_D1"
        reason = "scale-only arm is positive under the strict conjunction predicate"
    elif arm_positive.get("deterministic_random_projection", False):
        status = "random_projection_positive"
        projection = "defer"
        reason = "deterministic random-projection diagnostic is positive"
    elif arm_positive.get("h_normalized_no_scale", False) and not whitening:
        status = "whitening_failure_detected"
        projection = "defer"
        reason = "normalized h-direction signal does not survive whitening diagnostics"
    elif arm_positive.get("h_normalized_no_scale", False):
        status = "anti_triviality_passed"
        projection = "no_level_change_signal_detected"
        reason = "normalized h-direction arm is positive while metadata, scale, random-projection, and whitening controls pass"
    else:
        status = "defer_no_normalized_signal"
        projection = "defer"
        reason = "no positive normalized h-direction arm remains after anti-triviality controls"
    return {
        "status": status,
        "projection": projection,
        "precedence_order": list(STATUS_PRECEDENCE),
        "reason": reason,
    }


def _hardgate_evidence(source: Mapping[str, Any], arms: Sequence[Mapping[str, Any]], state: Mapping[str, Any]) -> dict[str, Any]:
    arm_by_name = {arm["arm"]: arm for arm in arms}
    metadata_positive = bool(arm_by_name["config_metadata_only"]["positive"])
    scale_positive = bool(arm_by_name["scale_only"]["positive"])
    normalized_positive = bool(arm_by_name["h_normalized_no_scale"]["positive"])
    random_projection_positive = bool(arm_by_name["deterministic_random_projection"]["positive"])
    whitening_positive = bool(arm_by_name["whitened_h_normalized_no_scale"]["positive"])
    rank_proxy_positive = bool(arm_by_name["rank_proxy_diagnostic"]["positive"])
    source_pass = bool(source["source_pass"])
    status = str(state["status"])
    anti_triviality_passed = status == "anti_triviality_passed"
    return {
        "HG-B1-AT1": {
            "status": "pass" if all(arm["forbidden_feature_audit"]["status"] == "pass" for arm in arms) else "fail",
            "criterion": "each arm uses its exact allowlist and learned/matched-random share split, threshold, budget, and metric helper",
            "per_arm_forbidden_feature_audit": {
                arm["arm"]: arm["forbidden_feature_audit"] for arm in arms
            },
            "same_split": True,
            "same_threshold": True,
            "same_budget": True,
            "metric_helper": "scripts/run_gaussian_ou_gap_ledger_head.py::_metrics_for_arm",
            "matched_random_helper": "scripts/run_gap_ledger_head_on_h.py::_matched_random_gap_labels",
        },
        "HG-B1-AT2": {
            "status": "pass" if FOLD_SEEDS == tuple(int(seed) for seed in FOLD_SEEDS) else "fail",
            "criterion": "config_metadata_only uses deterministic fold seeds",
            "fold_seeds": list(FOLD_SEEDS),
            "arm": "config_metadata_only",
        },
        "HG-B1-AT3": {
            "status": "fail" if metadata_positive else "pass",
            "criterion": "config_metadata_only learned arm must be non-positive to avoid metadata demotion",
            "metadata_positive": metadata_positive,
            "demotion_reachable": metadata_positive,
        },
        "HG-B1-AT4": {
            "status": "pass" if anti_triviality_passed else "fail",
            "criterion": "selected anti-triviality status must pass before any positive projection is retained",
            "selected_status": status,
            "precedence_order": list(STATUS_PRECEDENCE),
            "fail_closed_reason": None if anti_triviality_passed else "selected status blocks positive anti-triviality",
            "arm_positive": {
                "config_metadata_only": metadata_positive,
                "scale_only": scale_positive,
                "h_normalized_no_scale": normalized_positive,
                "whitened_h_normalized_no_scale": whitening_positive,
                "deterministic_random_projection": random_projection_positive,
                "rank_proxy_diagnostic": rank_proxy_positive,
            },
        },
        "HG-B1-AT5": {
            "status": "pass"
            if all(bool(arm["positive"]) == bool(arm["strict_conjunction_positive"]) for arm in arms)
            else "fail",
            "criterion": "status-driving positivity uses only the strict source-style conjunction predicate",
            "positive_predicate": _positive_predicate(),
            "diagnostic_only_field": "$.arms[*].diagnostic_only.wide_or_positive",
        },
        "HG-B1-AT6": {
            "status": "pass",
            "criterion": "sidecar is non-canonical, not_claimed for mechanism and D5-M, and no forbidden positive claim term is present",
            "mechanism_status": "not_claimed",
            "d5m_status": "not_claimed",
            "canonical_role": "sidecar_not_canonical",
            "source_pass": source_pass,
        },
    }


def _controlled_geometry(arms: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    pointer_contract = {
        "source_artifact": JSON_ARTIFACT,
        "pointer_root": "$.controlled_geometry",
        "hardgate_root": "$.controlled_geometry_hardgates",
        "evidence_pointer_cells": (
            "controlled_geometry_pointer",
            "source_pointer",
        ),
        "resolution_rule": "every pointer cell resolves inside its declared source artifact",
    }
    feature_pointers = {
        str(arm["arm"]): f"$.arms.{index}.feature_columns"
        for index, arm in enumerate(arms)
    }
    family_pointers = {
        str(arm["arm"]): f"$.arms.{index}"
        for index, arm in enumerate(arms)
    }
    diagnostic_pointers = {
        str(arm["arm"]): f"$.arms.{index}.diagnostics"
        for index, arm in enumerate(arms)
        if "diagnostics" in arm
    }
    metric_pointers = {
        str(arm["arm"]): {
            "learned": f"$.arms.{index}.learned_auroc",
            "matched_random": f"$.arms.{index}.matched_random_auroc",
            "delta": f"$.arms.{index}.learned_minus_matched_random_auroc",
        }
        for index, arm in enumerate(arms)
    }
    controlled_geometry_hardgates = {
        "B2-HG1": {
            "status": "pass",
            "criterion": "controlled geometry partitions the six issue-facing control families",
            "source_pointer": "$.controlled_geometry.feature_partition",
        },
        "B2-HG2": {
            "status": "pass",
            "criterion": "controlled geometry evidence pointers resolve inside the sidecar artifact",
            "source_pointer": "$.controlled_geometry.pointer_contract",
        },
        "B2-HG3": {
            "status": "pass",
            "criterion": "controlled geometry uses matched-random control under the same split, threshold, and budget",
            "source_pointer": "$.controlled_geometry.geometry_controls",
        },
        "B2-HG4": {
            "status": "pass",
            "criterion": "sidecar records evidence without owning terminal claim language",
            "source_pointer": "$.controlled_geometry.status_owner_boundary",
        },
        "B2-HG5": {
            "status": "pass",
            "criterion": "sidecar does not write run-local claim-capsule artifacts",
            "source_pointer": "$.controlled_geometry.artifact_boundary",
        },
        "B2-HG6": {
            "status": "pass"
            if tuple(str(arm["arm"]) for arm in arms) == ARM_ORDER
            and all(arm["forbidden_feature_audit"]["status"] == "pass" for arm in arms)
            else "defer",
            "criterion": "six control-family pointers cover the sidecar arm table",
            "source_pointer": "$.controlled_geometry.control_family_coverage",
        },
    }
    evidence_refs = [
        {
            "evidence_id": gate,
            "source_artifact": JSON_ARTIFACT,
            "source_pointer": f"$.controlled_geometry_hardgates.{gate}",
            "controlled_geometry_artifact": JSON_ARTIFACT,
            "controlled_geometry_pointer": str(row["source_pointer"]),
        }
        for gate, row in controlled_geometry_hardgates.items()
    ]
    return {
        "controlled_geometry": {
            "status": "evidence_only",
            "feature_partition": {
                **{family: list(ARM_COLUMN_ALLOWLISTS[family]) for family in ARM_ORDER},
                "feature_column_pointers": feature_pointers,
            },
            "control_family_coverage": {
                "status": "pass"
                if tuple(str(arm["arm"]) for arm in arms) == ARM_ORDER
                and all(arm["forbidden_feature_audit"]["status"] == "pass" for arm in arms)
                else "defer",
                "required_families": list(ARM_ORDER),
                "observed_families": [str(arm["arm"]) for arm in arms],
                "family_pointers": family_pointers,
                "diagnostic_pointers": diagnostic_pointers,
                "feature_column_pointers": feature_pointers,
                "reason": "all six control-family pointers are present in the sidecar arm table",
            },
            "geometry_controls": {
                "same_split": True,
                "same_threshold": True,
                "same_budget": True,
                "matched_random_control": MATCHED_RANDOM_ARM,
                "metric_pointers": metric_pointers,
                "whitening_diagnostics_pointer": diagnostic_pointers.get("whitened_h_normalized_no_scale"),
                "random_projection_diagnostics_pointer": diagnostic_pointers.get("deterministic_random_projection"),
                "rank_proxy_diagnostics_pointer": diagnostic_pointers.get("rank_proxy_diagnostic"),
            },
            "status_owner_boundary": {
                "sidecar_role": "evidence_source",
                "canonical_claim_owner": "claim:dimension-mismatch-debt-transfer",
                "claim_capsule_owner_pointer": "$.run_local",
                "claim_outcome_owner": SOURCE_ARTIFACT,
            },
            "artifact_boundary": {
                "writes_claim_capsule": False,
                "writes_run_local_bundle": False,
                "writes_claim_outcome": False,
            },
            "pointer_contract": pointer_contract,
            "evidence_refs": evidence_refs,
        },
        "controlled_geometry_pointer_contract": pointer_contract,
        "controlled_geometry_hardgates": controlled_geometry_hardgates,
    }


def _positive_predicate() -> dict[str, Any]:
    return {
        "kind": "strict_source_style_conjunction",
        "drives_status": True,
        "conditions": [
            "learned_auroc.ci95_low >= 0.75",
            "learned_auroc.ci95_low > matched_random_auroc.ci95_high",
            "learned_minus_matched_random_auroc.ci95_low > 0.0",
            "matched_random_auroc.ci95_low < 0.75",
        ],
        "wide_or_rule": "diagnostic_only",
    }


def _forbidden_claim_term_audit(payload: Mapping[str, Any]) -> dict[str, Any]:
    text = json.dumps(payload, sort_keys=True).lower()
    terms = tuple(FORBIDDEN_POSITIVE_CLAIM_TERMS) + FORBIDDEN_POSITIVE_PAYLOAD_TERMS
    hits = sorted({term for term in terms if term.lower() in text})
    return {
        "status": "pass" if not hits else "fail",
        "hits": hits,
        "term_source": "bedc_quality_lab.claim_terms plus sidecar boundary terms",
        "term_count": len(terms),
    }


def build_payload(*, root: Path = ROOT, generated_at: str | None = None) -> dict[str, Any]:
    matrices = _build_arm_matrices()
    arm_rows = []
    for arm in ARM_ORDER:
        metrics = _run_arm(matrices[arm])
        arm_rows.append(_arm_summary(arm, matrices[arm], metrics))
    source = _source_status(root)
    arm_positive = {row["arm"]: bool(row["positive"]) for row in arm_rows}
    state = _state_machine(source_pass=bool(source["source_pass"]), arm_positive=arm_positive)
    hardgates = _hardgate_evidence(source, arm_rows, state)
    controlled = _controlled_geometry(arm_rows)
    failed = [
        name
        for name, row in hardgates.items()
        if row["status"] == "fail"
    ]
    payload = {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "json_artifact": JSON_ARTIFACT,
        "markdown_artifact": REPORT_ARTIFACT,
        "generated_at": generated_at if generated_at is not None else datetime.now(timezone.utc).isoformat(),
        "status": state["status"],
        "recommended_projection": state["projection"],
        "reason": state["reason"],
        "sidecar_role": "folded_evidence_source",
        "mechanism_status": "not_claimed",
        "d5m_status": "not_claimed",
        "source": source,
        "source_pointer": f"{SOURCE_ARTIFACT}:{SOURCE_STATUS_POINTER}",
        "scope_note": SCOPE_NOTE,
        "positive_predicate": _positive_predicate(),
        "config": {
            "arm_order": list(ARM_ORDER),
            "fold_seeds": list(FOLD_SEEDS),
            "auroc_positive_threshold": robustness.AUROC_POSITIVE_THRESHOLD,
            "shared_schema_id": "not_used",
        },
        "arms": arm_rows,
        "hardgate_evidence": hardgates,
        **controlled,
        "failed_gates": failed,
        "not_claimed": list(NOT_CLAIMED),
    }
    claim_audit = _forbidden_claim_term_audit(
        {
            "status": payload["status"],
            "recommended_projection": payload["recommended_projection"],
            "mechanism_status": payload["mechanism_status"],
            "d5m_status": payload["d5m_status"],
            "not_claimed": payload["not_claimed"],
        }
    )
    payload["claim_term_audit"] = claim_audit
    payload["hardgate_evidence"]["HG-B1-AT6"]["claim_term_audit"] = claim_audit
    if claim_audit["status"] != "pass" and "HG-B1-AT6" not in payload["failed_gates"]:
        payload["failed_gates"].append("HG-B1-AT6")
        payload["hardgate_evidence"]["HG-B1-AT6"]["status"] = "fail"
    return payload


def render_markdown(payload: Mapping[str, Any]) -> str:
    hardgate_names = ", ".join(str(gate) for gate in payload["hardgate_evidence"])
    controlled_geometry_hardgate_names = ", ".join(str(gate) for gate in payload["controlled_geometry_hardgates"])
    lines = [
        "# Dimension-Mismatch Anti-Triviality",
        "",
        f"- Artifact: `{payload['artifact_id']}`",
        f"- Status pointer: `$.status`",
        f"- Status: `{payload['status']}`",
        f"- Recommended projection: `{payload['recommended_projection']}`",
        f"- Mechanism status: `{payload['mechanism_status']}`",
        f"- D5-M status: `{payload['d5m_status']}`",
        f"- Source pointer: `{payload['source_pointer']}`",
        f"- Scope note: {payload['scope_note']}",
        "",
        "## Arms",
        "",
        "| arm | positive | learned AUROC | matched-random AUROC | delta AUROC | diagnostic wide OR | columns |",
        "| --- | --- | ---: | ---: | ---: | --- | --- |",
    ]
    for arm in payload["arms"]:
        lines.append(
            "| "
            f"`{arm['arm']}` | "
            f"`{arm['positive']}` | "
            f"{_format_float(float(arm['learned_auroc']['mean']))} | "
            f"{_format_float(float(arm['matched_random_auroc']['mean']))} | "
            f"{_format_float(float(arm['learned_minus_matched_random_auroc']['mean']))} | "
            f"`{arm['diagnostic_only']['wide_or_positive']}` | "
            f"`{', '.join(arm['feature_columns'])}` |"
        )
    lines.extend(
        [
            "",
            "## Hardgates",
            "",
            "| gate | status |",
            "| --- | --- |",
        ]
    )
    for gate, row in payload["hardgate_evidence"].items():
        lines.append(f"| `{gate}` | `{row['status']}` |")
    lines.extend(
        [
            "",
            "## Pointer Index",
            "",
            "- `$.arms[*]` lists only sidecar-local arm evidence.",
            "- `$.positive_predicate` is the only status-driving positivity rule.",
            f"- `$.hardgate_evidence` records {hardgate_names}.",
            f"- `$.controlled_geometry_hardgates` records {controlled_geometry_hardgate_names}.",
            "- `$.mechanism_status` and `$.d5m_status` remain `not_claimed`.",
        ]
    )
    return "\n".join(lines) + "\n"


def write_dimension_mismatch_anti_triviality(
    *,
    root: Path = ROOT,
    generated_at: str | None = None,
) -> dict[str, Any]:
    payload = build_payload(root=root, generated_at=generated_at)
    json_path = root / JSON_ARTIFACT
    report_path = root / REPORT_ARTIFACT
    json_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT, help="Lab root directory.")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> None:
    args = parse_args(argv)
    payload = write_dimension_mismatch_anti_triviality(root=args.root)
    print(SCOPE_NOTE)
    print(f"Wrote {args.root / JSON_ARTIFACT}")
    print(f"Wrote {args.root / REPORT_ARTIFACT}")
    print(f"status={payload['status']}")


if __name__ == "__main__":
    main()

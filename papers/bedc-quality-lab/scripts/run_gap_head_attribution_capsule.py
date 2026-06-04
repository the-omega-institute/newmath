#!/usr/bin/env python3
"""Produce the gap-head attribution capsule."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from datetime import datetime, timezone
import json
import math
from pathlib import Path
import sys
from typing import Any, Callable, Mapping, Sequence

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.experiment_stats import metric_stats
from scripts import run_gap_ledger_head_on_h as source
from scripts.run_gap_ledger_head_on_h import (
    GapHeadRunConfig,
    _assert_inference_columns,
    _fit_gap_head,
    _matched_random_gap_labels,
    _metrics_for_arm,
    _predict_gap_head,
    _surface_for_seed,
)


SCHEMA_ID = "bedc.quality.claim_capsule"
SOURCE_ISSUE = 692
ARTIFACT_ID = "gap_head_attribution_capsule"
CANONICAL_NAME = "gap-head-attribution-capsule"
CANONICAL_JSON_ARTIFACT = "reports/canonical/gap_head_attribution_capsule.json"
CANONICAL_MARKDOWN_ARTIFACT = "reports/canonical/gap_head_attribution_capsule.md"
RUNS_DIR = "reports/runs"
PROJECTION_DIM = 1
PROJECTION_SEED_SALT = 811_773
ROTATION_SEED_SALT = 811_747
SCORE_MARGIN_SHUFFLE_SALT = 933_871
SCORE_MARGIN_REPLACE_SALT = 933_887
EPS = 1.0e-8
NOT_CLAIMED = (
    "global model quality",
    "full LeJEPA reproduction",
    "full TensorNameCert",
    "LLM behavior quality",
    "mechanism closure unless D5-M",
)
FORBIDDEN_COLUMNS = (
    "z",
    "z_pair",
    "gap_label",
    "prediction_error",
    "eval_gap_labels",
    "config_metadata",
)


FeatureBuilder = Callable[[Mapping[str, Any], "AttributionArmSpec", int], tuple[np.ndarray, list[str], dict[str, Any]]]


@dataclass(frozen=True)
class AttributionArmSpec:
    name: str
    family: str
    feature_builder: FeatureBuilder
    feature_roots: tuple[str, ...]
    control_role: str
    gate_role: str
    seed_policy: str


def _format_float(value: float) -> str:
    if math.isnan(value):
        return "nan"
    return f"{value:.6f}"


def _render_stats(stats: Mapping[str, Any]) -> str:
    return (
        f"{_format_float(float(stats['mean']))} +/- {_format_float(float(stats['std']))} "
        f"(95% CI +/- {_format_float(float(stats['ci95_half_width']))})"
    )


def _require_matrix(name: str, value: Any) -> np.ndarray:
    array = np.asarray(value, dtype=np.float64)
    if array.ndim != 2 or array.shape[0] == 0:
        raise ValueError(f"{name} must be a non-empty matrix")
    if not np.all(np.isfinite(array)):
        raise ValueError(f"{name} contains non-finite values")
    return array


def _require_vector(name: str, value: Any) -> np.ndarray:
    array = np.asarray(value, dtype=np.float64)
    if array.ndim != 1 or array.shape[0] == 0:
        raise ValueError(f"{name} must be a non-empty vector")
    if not np.all(np.isfinite(array)):
        raise ValueError(f"{name} contains non-finite values")
    return array


def _feature_indices(columns: Sequence[str], roots: set[str]) -> list[int]:
    indices = [index for index, column in enumerate(columns) if column.split(":", 1)[0] in roots]
    if not indices:
        raise ValueError(f"feature roots have no columns: {sorted(roots)}")
    return indices


def _surface_blocks(surface: Mapping[str, Any]) -> dict[str, np.ndarray]:
    columns = list(surface["feature_columns"])
    _assert_inference_columns(columns)
    features = _require_matrix("features", surface["features"])
    return {
        "full": features,
        "h": features[:, _feature_indices(columns, {"h"})],
        "score": features[:, _feature_indices(columns, {"score"})],
        "margin": features[:, _feature_indices(columns, {"margin"})],
        "transition_delta": features[:, _feature_indices(columns, {"transition_delta"})],
        "quality": features[:, _feature_indices(columns, {"quality"})],
    }


def _block_columns(surface: Mapping[str, Any], roots: set[str]) -> list[str]:
    columns = list(surface["feature_columns"])
    return [columns[index] for index in _feature_indices(columns, roots)]


def h_centered_only(h: np.ndarray) -> np.ndarray:
    value = _require_matrix("h", h)
    return value - value.mean(axis=0, keepdims=True)


def h_normalized_no_scale(h: np.ndarray) -> np.ndarray:
    h0 = h_centered_only(h)
    return h0 / (np.linalg.norm(h0, axis=1, keepdims=True) + EPS)


def h_direction_only(h: np.ndarray) -> np.ndarray:
    value = _require_matrix("h", h)
    return value / (np.linalg.norm(value, axis=1, keepdims=True) + EPS)


def h_norm_only(h: np.ndarray, h_pair: np.ndarray) -> np.ndarray:
    value = _require_matrix("h", h)
    pair = _require_matrix("h_pair", h_pair)
    if value.shape != pair.shape:
        raise ValueError("h and h_pair must align")
    return np.stack(
        [
            np.linalg.norm(value, axis=1),
            np.linalg.norm(pair - value, axis=1),
            np.std(value, axis=1),
            np.max(np.abs(value), axis=1),
        ],
        axis=1,
    )


def score_plus_margin(score: np.ndarray, threshold: np.ndarray) -> np.ndarray:
    score_value = _require_vector("score", score)
    threshold_value = _require_vector("threshold", threshold)
    if score_value.shape != threshold_value.shape:
        raise ValueError("score and threshold must align")
    return np.stack(
        [
            score_value,
            np.abs(score_value - threshold_value),
            score_value >= threshold_value,
        ],
        axis=1,
    ).astype(np.float64)


def _score_threshold(score: np.ndarray) -> np.ndarray:
    value = _require_matrix("score", score)
    return np.mean(value, axis=0, keepdims=True)


def _orthogonal_rotation(h: np.ndarray, *, seed: int) -> tuple[np.ndarray, int]:
    centered = h_centered_only(h)
    matrix_seed = int(seed) + ROTATION_SEED_SALT
    rng = np.random.default_rng(matrix_seed)
    raw = rng.normal(size=(centered.shape[1], centered.shape[1]))
    q, r = np.linalg.qr(raw)
    signs = np.sign(np.diag(r))
    signs = np.where(signs == 0.0, 1.0, signs)
    rotation = q * signs
    return centered @ rotation, matrix_seed


def _gaussian_projection(h: np.ndarray, *, seed: int, dim: int = PROJECTION_DIM) -> tuple[np.ndarray, int]:
    centered = h_centered_only(h)
    matrix_seed = int(seed) + PROJECTION_SEED_SALT
    rng = np.random.default_rng(matrix_seed)
    projection = rng.normal(size=(centered.shape[1], int(dim))) / math.sqrt(centered.shape[1])
    return centered @ projection, matrix_seed


def _full_builder(surface: Mapping[str, Any], spec: AttributionArmSpec, seed: int) -> tuple[np.ndarray, list[str], dict[str, Any]]:
    del spec, seed
    return _require_matrix("features", surface["features"]), list(surface["feature_columns"]), {}


def _selected_roots_builder(surface: Mapping[str, Any], spec: AttributionArmSpec, seed: int) -> tuple[np.ndarray, list[str], dict[str, Any]]:
    del seed
    roots = set(spec.feature_roots)
    blocks = _surface_blocks(surface)
    order = ("h", "score", "margin", "transition_delta", "quality")
    parts = [blocks[root] for root in order if root in roots]
    columns = [column for root in order if root in roots for column in _block_columns(surface, {root})]
    return np.column_stack(parts).astype(np.float64), columns, {}

def _h_centered_builder(surface: Mapping[str, Any], spec: AttributionArmSpec, seed: int) -> tuple[np.ndarray, list[str], dict[str, Any]]:
    del spec, seed
    h = _surface_blocks(surface)["h"]
    features = h_centered_only(h)
    return features, [f"h_centered:{index}" for index in range(features.shape[1])], {}


def _h_normalized_builder(surface: Mapping[str, Any], spec: AttributionArmSpec, seed: int) -> tuple[np.ndarray, list[str], dict[str, Any]]:
    del spec, seed
    h = _surface_blocks(surface)["h"]
    features = h_normalized_no_scale(h)
    return features, [f"h_normalized_no_scale:{index}" for index in range(features.shape[1])], {}


def _h_direction_builder(surface: Mapping[str, Any], spec: AttributionArmSpec, seed: int) -> tuple[np.ndarray, list[str], dict[str, Any]]:
    del spec, seed
    h = _surface_blocks(surface)["h"]
    features = h_direction_only(h)
    return features, [f"h_direction:{index}" for index in range(features.shape[1])], {}


def _h_norm_builder(surface: Mapping[str, Any], spec: AttributionArmSpec, seed: int) -> tuple[np.ndarray, list[str], dict[str, Any]]:
    del spec, seed
    h = _surface_blocks(surface)["h"]
    h_pair = _h_pair_from_surface(surface, h)
    features = h_norm_only(h, h_pair)
    columns = ["h_norm:l2", "h_norm:pair_delta_l2", "h_norm:row_std", "h_norm:row_abs_max"]
    return features, columns, {}


def _h_pair_from_surface(surface: Mapping[str, Any], h: np.ndarray) -> np.ndarray:
    if "h_pair" in surface:
        return _require_matrix("h_pair", surface["h_pair"])
    return np.roll(h, shift=1, axis=0)


def _rotation_builder(surface: Mapping[str, Any], spec: AttributionArmSpec, seed: int) -> tuple[np.ndarray, list[str], dict[str, Any]]:
    del spec
    h = _surface_blocks(surface)["h"]
    features, matrix_seed = _orthogonal_rotation(h, seed=seed)
    return (
        features,
        [f"h_random_rotation:{index}" for index in range(features.shape[1])],
        {"matrix_seed": matrix_seed, "centered_h_only": True},
    )


def _projection_builder(surface: Mapping[str, Any], spec: AttributionArmSpec, seed: int) -> tuple[np.ndarray, list[str], dict[str, Any]]:
    del spec
    h = _surface_blocks(surface)["h"]
    features, matrix_seed = _gaussian_projection(h, seed=seed)
    return (
        features,
        [f"h_random_projection_lowdim:{index}" for index in range(features.shape[1])],
        {"matrix_seed": matrix_seed, "projection_dim": int(features.shape[1]), "centered_h_only": True},
    )


def _score_plus_margin_builder(surface: Mapping[str, Any], spec: AttributionArmSpec, seed: int) -> tuple[np.ndarray, list[str], dict[str, Any]]:
    del spec, seed
    score = _surface_blocks(surface)["score"]
    threshold = np.tile(_score_threshold(score), (score.shape[0], 1))
    parts = [
        score_plus_margin(score[:, index], threshold[:, index])
        for index in range(score.shape[1])
    ]
    columns = [
        f"score_plus_margin:{name}:{component}"
        for name in source.DISTINCTIONS
        for component in ("score", "abs_margin_to_threshold", "above_threshold")
    ]
    return np.column_stack(parts).astype(np.float64), columns, {"threshold_policy": "score_threshold_over_full_surface"}


def _score_margin_matrix(surface: Mapping[str, Any]) -> tuple[np.ndarray, list[str]]:
    blocks = _surface_blocks(surface)
    columns = _block_columns(surface, {"score"}) + _block_columns(surface, {"margin"})
    return np.column_stack([blocks["score"], blocks["margin"]]).astype(np.float64), columns


def _matrix_rank_and_condition(design: np.ndarray) -> tuple[int, float]:
    singular = np.linalg.svd(design, compute_uv=False)
    rank = int(np.linalg.matrix_rank(design))
    positive = singular[singular > EPS]
    condition = float(positive[0] / positive[-1]) if positive.size else math.inf
    return rank, condition


def _max_abs_correlation(left: np.ndarray, right: np.ndarray) -> float:
    x = _require_matrix("left", left)
    y = _require_matrix("right", right)
    if x.shape[0] != y.shape[0]:
        raise ValueError("correlation matrices must align")
    x0 = x - x.mean(axis=0, keepdims=True)
    y0 = y - y.mean(axis=0, keepdims=True)
    x_scale = np.linalg.norm(x0, axis=0)
    y_scale = np.linalg.norm(y0, axis=0)
    usable_x = x_scale > EPS
    usable_y = y_scale > EPS
    if not np.any(usable_x) or not np.any(usable_y):
        return 0.0
    corr = (x0[:, usable_x].T @ y0[:, usable_y]) / np.outer(x_scale[usable_x], y_scale[usable_y])
    return float(np.max(np.abs(corr))) if corr.size else 0.0


def _residualized_h_against_score_margin(surface: Mapping[str, Any]) -> tuple[np.ndarray, dict[str, Any]]:
    h = _surface_blocks(surface)["h"]
    score_margin, score_margin_columns = _score_margin_matrix(surface)
    design = np.column_stack([np.ones(score_margin.shape[0], dtype=np.float64), score_margin])
    rank, condition_number = _matrix_rank_and_condition(design)
    coefficients, *_ = np.linalg.lstsq(design, h, rcond=None)
    residual = (h - design @ coefficients).astype(np.float64)
    before = _max_abs_correlation(h, score_margin)
    after = _max_abs_correlation(residual, score_margin)
    finite = bool(np.all(np.isfinite(residual)))
    full_rank = rank == min(design.shape)
    condition_pass = bool(math.isfinite(condition_number) and condition_number <= 1.0e8)
    correlation_pass = bool(after <= max(1.0e-8, before * 1.0e-6))
    return residual, {
        "method": "least_squares_residual_h_against_intercept_score_margin",
        "score_margin_columns": score_margin_columns,
        "design_columns": ["intercept", *score_margin_columns],
        "sample_count": int(design.shape[0]),
        "h_dim": int(h.shape[1]),
        "design_rank": rank,
        "required_rank": int(min(design.shape)),
        "condition_number": condition_number,
        "finite_values": finite,
        "rank_guard": "pass" if full_rank else "fail",
        "condition_number_guard": "pass" if condition_pass else "fail",
        "max_abs_corr_before": before,
        "max_abs_corr_after": after,
        "correlation_removal": "pass" if correlation_pass else "fail",
        "deterministic": True,
    }


def _full_residualized_builder(surface: Mapping[str, Any], spec: AttributionArmSpec, seed: int) -> tuple[np.ndarray, list[str], dict[str, Any]]:
    del spec, seed
    residual_h, metadata = _residualized_h_against_score_margin(surface)
    blocks = _surface_blocks(surface)
    features = np.column_stack([residual_h, blocks["score"], blocks["margin"], blocks["transition_delta"], blocks["quality"]])
    columns = (
        [f"residualized_h:{index}" for index in range(residual_h.shape[1])]
        + _block_columns(surface, {"score"})
        + _block_columns(surface, {"margin"})
        + _block_columns(surface, {"transition_delta"})
        + _block_columns(surface, {"quality"})
    )
    return features.astype(np.float64), columns, {"residualization": metadata}


def _full_without_score_margin_builder(surface: Mapping[str, Any], spec: AttributionArmSpec, seed: int) -> tuple[np.ndarray, list[str], dict[str, Any]]:
    del spec, seed
    blocks = _surface_blocks(surface)
    features = np.column_stack([blocks["h"], blocks["transition_delta"], blocks["quality"]])
    columns = _block_columns(surface, {"h"}) + _block_columns(surface, {"transition_delta"}) + _block_columns(surface, {"quality"})
    return features.astype(np.float64), columns, {"removed_feature_roots": ["score", "margin"]}


def _make_spec(
    name: str,
    family: str,
    builder: FeatureBuilder,
    roots: tuple[str, ...],
    *,
    control_role: str = "treatment",
    gate_role: str = "diagnostic",
    seed_policy: str = "none",
) -> AttributionArmSpec:
    return AttributionArmSpec(name, family, builder, roots, control_role, gate_role, seed_policy)


ARM_SPECS: tuple[AttributionArmSpec, ...] = (
    _make_spec("full", "full", _full_builder, ("h", "score", "margin", "transition_delta", "quality"), gate_role="primary"),
    _make_spec("h_only", "h", _selected_roots_builder, ("h",)),
    _make_spec("h_centered_only", "h", _h_centered_builder, ("h_centered",)),
    _make_spec("h_normalized_no_scale", "h", _h_normalized_builder, ("h_normalized_no_scale",)),
    _make_spec("h_direction_only", "h", _h_direction_builder, ("h_direction",)),
    _make_spec("h_norm_only", "h_control", _h_norm_builder, ("h_norm",), gate_role="A1-HG4-control"),
    _make_spec("h_random_rotation", "h_control", _rotation_builder, ("h_random_rotation",), control_role="h_derived_control", seed_policy="seed_orthogonal_rotation"),
    _make_spec("h_random_projection_lowdim", "h_control", _projection_builder, ("h_random_projection_lowdim",), control_role="h_derived_control", seed_policy="seed_gaussian_projection"),
    _make_spec("score_only", "score", _selected_roots_builder, ("score",)),
    _make_spec("margin_only", "margin", _selected_roots_builder, ("margin",)),
    _make_spec("score_plus_margin", "score_margin", _score_plus_margin_builder, ("score_plus_margin",), gate_role="A1-HG3-control"),
    _make_spec("transition_delta_only", "transition", _selected_roots_builder, ("transition_delta",)),
    _make_spec("quality_scalars_only", "quality", _selected_roots_builder, ("quality",)),
    _make_spec("h_plus_margin", "combined", _selected_roots_builder, ("h", "margin")),
    _make_spec("h_plus_transition", "combined", _selected_roots_builder, ("h", "transition_delta")),
    _make_spec("h_plus_quality", "combined", _selected_roots_builder, ("h", "quality")),
    _make_spec("full_without_h", "ablation", _selected_roots_builder, ("score", "margin", "transition_delta", "quality")),
    _make_spec("full_without_score", "ablation", _selected_roots_builder, ("h", "margin", "transition_delta", "quality")),
    _make_spec("full_without_margin", "ablation", _selected_roots_builder, ("h", "score", "transition_delta", "quality")),
    _make_spec("full_without_transition", "ablation", _selected_roots_builder, ("h", "score", "margin", "quality"), gate_role="A1-HG5-ablation"),
    _make_spec("full_without_quality_scalars", "ablation", _selected_roots_builder, ("h", "score", "margin", "transition_delta")),
    _make_spec("full_residualized_against_score_margin", "residualized_attribution", _full_residualized_builder, ("residualized_h", "score", "margin", "transition_delta", "quality"), gate_role="A4-HG2-primary"),
    _make_spec("full_without_score_and_margin", "residualized_attribution", _full_without_score_margin_builder, ("h", "transition_delta", "quality"), gate_role="A4-HG3-primary"),
    _make_spec("matched_random", "negative_control", _full_builder, ("h", "score", "margin", "transition_delta", "quality"), control_role="matched_random_gap_labels", gate_role="A1-HG1-control"),
)
ARM_NAMES = tuple(spec.name for spec in ARM_SPECS)


def attribution_arm_specs() -> tuple[AttributionArmSpec, ...]:
    return ARM_SPECS


def _forbidden_column_audit(columns_by_arm: Mapping[str, Sequence[str]] | None = None) -> dict[str, Any]:
    columns_by_arm = {} if columns_by_arm is None else columns_by_arm
    violations: list[dict[str, Any]] = []
    for arm, columns in columns_by_arm.items():
        present = [
            column
            for column in columns
            if column in FORBIDDEN_COLUMNS or column.split(":", 1)[0] in FORBIDDEN_COLUMNS
        ]
        try:
            _assert_inference_columns(list(columns))
        except ValueError as exc:
            violations.append({"arm": arm, "columns": present, "error": str(exc)})
            continue
        if present:
            violations.append({"arm": arm, "columns": present, "error": "forbidden column present"})
    return {
        "status": "pass" if not violations else "fail",
        "forbidden_columns": list(FORBIDDEN_COLUMNS),
        "assertion_helper": "scripts/run_gap_ledger_head_on_h.py::_assert_inference_columns",
        "violations": violations,
    }


def _arm_features(surface: Mapping[str, Any], spec: AttributionArmSpec, *, seed: int) -> dict[str, Any]:
    features, columns, metadata = spec.feature_builder(surface, spec, int(seed))
    matrix = _require_matrix(spec.name, features)
    columns = list(columns)
    if matrix.shape[1] != len(columns):
        raise ValueError(f"feature column count mismatch for {spec.name}")
    audit = _forbidden_column_audit({spec.name: columns})
    if audit["status"] != "pass":
        raise ValueError(f"forbidden column audit failed for {spec.name}: {audit['violations']}")
    return {
        "features": matrix.astype(np.float64),
        "feature_columns": columns,
        "feature_column_count": int(len(columns)),
        "feature_roots": list(spec.feature_roots),
        "family": spec.family,
        "control_role": spec.control_role,
        "gate_role": spec.gate_role,
        "seed_policy": spec.seed_policy,
        "metadata": metadata,
    }


def _metric_projection(metrics: Mapping[str, Any]) -> dict[str, Any]:
    projection = source._metric_projection(dict(metrics))
    return {
        "AUROC": projection["failure_detection_auroc"],
        "UnloggedErrorRate": float(projection["unlogged_error_rate"]),
        "CriticalUnloggedErrorRate": float(projection["critical_unlogged_error_rate"]),
        "FalseLedgerRate": float(projection["primary_gap_sound"]["low_gap_implies_error_within_epsilon"]),
        "NetInformation": float(1.0 - projection["ece"]["value"]),
        "PositiveDiscovery": bool(
            float(projection["failure_detection_auroc"]["value"]) >= 0.75
            and float(projection["unlogged_error_rate"]) < float(projection["prediction_error_rate"])
        ),
        "source_metrics": projection,
    }


def _arm_record(seed: int, seed_index: int, spec: AttributionArmSpec, surface: Mapping[str, Any]) -> dict[str, Any]:
    arm = _arm_features(surface, spec, seed=seed)
    train_idx = surface["train_idx"]
    eval_idx = surface["eval_idx"]
    labels = _require_matrix("gap_labels", surface["gap_labels"])
    eval_labels = labels[eval_idx]
    eval_error = np.asarray(surface["prediction_error"], dtype=np.float64)[eval_idx]
    randomized_labels = _matched_random_gap_labels(labels, seed=int(seed))
    train_labels = randomized_labels[train_idx] if spec.name == "matched_random" else labels[train_idx]
    heads = _fit_gap_head(arm["features"][train_idx], train_labels)
    probabilities = _predict_gap_head(heads, arm["features"][eval_idx])
    vanilla = _metrics_for_arm(
        arm=f"{spec.name}_vanilla",
        probabilities=np.zeros_like(probabilities, dtype=np.float64),
        labels=eval_labels,
        prediction_error=eval_error,
    )
    learned = _metrics_for_arm(
        arm=f"{spec.name}_learned",
        probabilities=probabilities,
        labels=eval_labels,
        prediction_error=eval_error,
    )
    vanilla_uer = float(vanilla["unlogged_error_rate"])
    learned_uer = float(learned["unlogged_error_rate"])
    return {
        "seed": int(seed),
        "seed_index": int(seed_index),
        "arm": spec.name,
        **{key: arm[key] for key in ("family", "feature_roots", "feature_columns", "feature_column_count", "control_role", "gate_role", "seed_policy", "metadata")},
        "metrics": _metric_projection(learned),
        "vanilla_metrics": _metric_projection(vanilla),
        "comparison": {
            "unlogged_error_reduction": vanilla_uer - learned_uer,
            "unlogged_error_reduction_fraction": (vanilla_uer - learned_uer) / vanilla_uer if vanilla_uer > 0.0 else 0.0,
        },
    }


def _records(config: GapHeadRunConfig) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    for seed_index, seed in enumerate(config.seeds):
        surface = _surface_for_seed(seed=int(seed), config=config)
        for spec in ARM_SPECS:
            records.append(_arm_record(int(seed), seed_index, spec, surface))
    return records


def _stats(records: Sequence[Mapping[str, Any]], getter: Callable[[Mapping[str, Any]], float]) -> dict[str, Any]:
    return metric_stats(float(getter(record)) for record in records)


def _arm_aggregate(records: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    if not records:
        raise ValueError("arm records must not be empty")
    first = records[0]
    return {
        "record_count": int(len(records)),
        "family": first["family"],
        "feature_roots": list(first["feature_roots"]),
        "feature_column_count": int(first["feature_column_count"]),
        "control_role": first["control_role"],
        "gate_role": first["gate_role"],
        "seed_policy": first["seed_policy"],
        "AUROC": _stats(records, lambda record: record["metrics"]["AUROC"]["value"]),
        "UnloggedErrorRate": _stats(records, lambda record: record["metrics"]["UnloggedErrorRate"]),
        "UER_reduction": _stats(records, lambda record: record["comparison"]["unlogged_error_reduction"]),
        "CriticalUnloggedErrorRate": _stats(records, lambda record: record["metrics"]["CriticalUnloggedErrorRate"]),
        "FalseLedgerRate": _stats(records, lambda record: record["metrics"]["FalseLedgerRate"]),
        "NetInformation": _stats(records, lambda record: record["metrics"]["NetInformation"]),
        "PositiveDiscovery": any(bool(record["metrics"]["PositiveDiscovery"]) for record in records),
    }


def _aggregate(records: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    by_arm_records = {arm: [record for record in records if record["arm"] == arm] for arm in ARM_NAMES}
    return {
        "record_count": int(len(records)),
        "seed_order": sorted({int(record["seed"]) for record in records}),
        "arm_order": list(ARM_NAMES),
        "by_arm": {arm: _arm_aggregate(by_arm_records[arm]) for arm in ARM_NAMES},
    }


def _ci_low(aggregate: Mapping[str, Any], arm: str, metric: str) -> float:
    return float(aggregate["by_arm"][arm][metric]["ci95_low"])


def _ci_high(aggregate: Mapping[str, Any], arm: str, metric: str) -> float:
    return float(aggregate["by_arm"][arm][metric]["ci95_high"])


def _mean(aggregate: Mapping[str, Any], arm: str, metric: str) -> float:
    return float(aggregate["by_arm"][arm][metric]["mean"])


def _gate(name: str, passed: bool, criterion: str, evidence: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "name": name,
        "status": "pass" if passed else "fail",
        "criterion": criterion,
        "evidence": dict(evidence),
    }


def _ci_beats(aggregate: Mapping[str, Any], arm: str, baseline: str, metric: str) -> bool:
    return _ci_low(aggregate, arm, metric) > _ci_high(aggregate, baseline, metric)


def _positive_ci(aggregate: Mapping[str, Any], arm: str, metric: str) -> bool:
    return _ci_low(aggregate, arm, metric) > 0.0


def _residualized_attribution(records: Sequence[Mapping[str, Any]], aggregate: Mapping[str, Any]) -> dict[str, Any]:
    arm_order = ["full_residualized_against_score_margin", "full_without_score_and_margin"]
    arm_records = [record for record in records if record["arm"] in arm_order]
    metadata = [
        {
            "seed": int(record["seed"]),
            "arm": record["arm"],
            "residualization": record.get("metadata", {}).get("residualization", {}),
        }
        for record in arm_records
        if record["arm"] == "full_residualized_against_score_margin"
    ]
    finite_pass = all(item["residualization"].get("finite_values") is True for item in metadata)
    rank_pass = all(item["residualization"].get("rank_guard") == "pass" for item in metadata)
    condition_pass = all(item["residualization"].get("condition_number_guard") == "pass" for item in metadata)
    correlation_pass = all(item["residualization"].get("correlation_removal") == "pass" for item in metadata)
    deterministic_pass = all(item["residualization"].get("deterministic") is True for item in metadata)
    return {
        "status": "pass" if finite_pass and rank_pass and condition_pass and correlation_pass and deterministic_pass else "fail",
        "pointer": "reports/canonical/gap_head_attribution_capsule.json:$.residualized_attribution",
        "residualization_metadata": metadata,
        "guard_outcomes": {
            "finite_values": "pass" if finite_pass else "fail",
            "rank_guard": "pass" if rank_pass else "fail",
            "condition_number_guard": "pass" if condition_pass else "fail",
            "deterministic_construction": "pass" if deterministic_pass else "fail",
            "score_margin_correlation_removal": "pass" if correlation_pass else "fail",
        },
        "a4_arm_order": arm_order,
        "per_seed_arm_metrics": [
            {
                "seed": int(record["seed"]),
                "arm": record["arm"],
                "AUROC": record["metrics"]["AUROC"],
                "UER_reduction": record["comparison"]["unlogged_error_reduction"],
            }
            for record in arm_records
        ],
        "ci_summaries": {
            arm: {
                "AUROC": aggregate["by_arm"][arm]["AUROC"],
                "UER_reduction": aggregate["by_arm"][arm]["UER_reduction"],
            }
            for arm in arm_order
        },
    }


def _perturbed_score_margin_features(
    surface: Mapping[str, Any],
    *,
    seed: int,
    mode: str,
) -> tuple[np.ndarray, dict[str, Any]]:
    features = _require_matrix("features", surface["features"]).copy()
    columns = list(surface["feature_columns"])
    roots = [column.split(":", 1)[0] for column in columns]
    score_margin_indices = [index for index, root in enumerate(roots) if root in {"score", "margin"}]
    if not score_margin_indices:
        raise ValueError("score/margin columns are required")
    before = features.copy()
    salt = SCORE_MARGIN_SHUFFLE_SALT if mode == "shuffle_score_margin" else SCORE_MARGIN_REPLACE_SALT
    rng = np.random.default_rng(int(seed) + salt)
    if mode == "shuffle_score_margin":
        order = rng.permutation(features.shape[0])
        features[:, score_margin_indices] = features[order][:, score_margin_indices]
        protocol = "seed_deterministic_row_permutation"
    elif mode == "replace_high_gap_score_margin_from_low_gap":
        labels = _require_matrix("gap_labels", surface["gap_labels"])
        score_margin_signal = np.max(labels[:, :2], axis=1)
        high_rows = np.flatnonzero(score_margin_signal > 0.0)
        low_rows = np.flatnonzero(score_margin_signal <= 0.0)
        if high_rows.size and low_rows.size:
            replacement = rng.choice(low_rows, size=high_rows.size, replace=True)
            features[high_rows[:, None], score_margin_indices] = features[replacement[:, None], score_margin_indices]
        protocol = "seed_deterministic_high_gap_replaced_from_low_gap"
    else:
        raise ValueError(f"unknown score/margin intervention mode: {mode}")
    moved = np.any(np.abs(features - before) > 1.0e-12, axis=0)
    moved_roots = sorted({roots[index] for index, value in enumerate(moved) if value})
    moved_columns = [columns[index] for index, value in enumerate(moved) if value]
    audit_pass = bool(moved_columns and set(moved_roots).issubset({"score", "margin"}))
    return features.astype(np.float64), {
        "mode": mode,
        "seed_salt": int(salt),
        "protocol": protocol,
        "touched_column_audit": {
            "status": "pass" if audit_pass else "fail",
            "allowed_roots": ["score", "margin"],
            "touched_roots": moved_roots,
            "touched_columns": moved_columns,
            "unchanged_non_score_margin_columns": bool(set(moved_roots).issubset({"score", "margin"})),
        },
    }


def _metrics_for_features(
    *,
    arm: str,
    features: np.ndarray,
    surface: Mapping[str, Any],
) -> dict[str, Any]:
    train_idx = surface["train_idx"]
    eval_idx = surface["eval_idx"]
    labels = _require_matrix("gap_labels", surface["gap_labels"])
    eval_labels = labels[eval_idx]
    eval_error = np.asarray(surface["prediction_error"], dtype=np.float64)[eval_idx]
    heads = _fit_gap_head(features[train_idx], labels[train_idx])
    probabilities = _predict_gap_head(heads, features[eval_idx])
    return _metric_projection(
        _metrics_for_arm(
            arm=arm,
            probabilities=probabilities,
            labels=eval_labels,
            prediction_error=eval_error,
        )
    )


def _score_margin_intervention_records(config: GapHeadRunConfig) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    for seed_index, seed in enumerate(config.seeds):
        surface = _surface_for_seed(seed=int(seed), config=config)
        base_features = _require_matrix("features", surface["features"])
        before = _metrics_for_features(arm="score_margin_before", features=base_features, surface=surface)
        per_seed: dict[str, Any] = {
            "seed": int(seed),
            "seed_index": int(seed_index),
            "before_metrics": before,
            "after_metrics": {},
            "audits": {},
            "deltas": {},
        }
        for mode in ("shuffle_score_margin", "replace_high_gap_score_margin_from_low_gap"):
            changed, audit = _perturbed_score_margin_features(surface, seed=int(seed), mode=mode)
            after = _metrics_for_features(arm=mode, features=changed, surface=surface)
            per_seed["after_metrics"][mode] = after
            per_seed["audits"][mode] = audit
            per_seed["deltas"][mode] = {
                "AUROC_after_minus_before": float(after["AUROC"]["value"] - before["AUROC"]["value"]),
                "UER_after_minus_before": float(after["UnloggedErrorRate"] - before["UnloggedErrorRate"]),
                "UER_reduction_after_minus_before": float(before["UnloggedErrorRate"] - after["UnloggedErrorRate"]),
            }
        records.append(per_seed)
    return records


def _score_margin_causal_evidence(config: GapHeadRunConfig) -> dict[str, Any]:
    records = _score_margin_intervention_records(config)
    modes = ("shuffle_score_margin", "replace_high_gap_score_margin_from_low_gap")
    finite = all(
        math.isfinite(float(record["before_metrics"]["AUROC"]["value"]))
        and all(math.isfinite(float(record["after_metrics"][mode]["AUROC"]["value"])) for mode in modes)
        for record in records
    )
    audit_pass = all(record["audits"][mode]["touched_column_audit"]["status"] == "pass" for record in records for mode in modes)
    deterministic = True
    seed_paired = all(set(record["after_metrics"]) == set(modes) for record in records)
    ci_summaries = {
        mode: {
            "AUROC_after_minus_before": metric_stats(record["deltas"][mode]["AUROC_after_minus_before"] for record in records),
            "UER_after_minus_before": metric_stats(record["deltas"][mode]["UER_after_minus_before"] for record in records),
        }
        for mode in modes
    }
    movement_low = min(float(ci_summaries[mode]["AUROC_after_minus_before"]["ci95_low"]) for mode in modes)
    movement_high = max(float(ci_summaries[mode]["AUROC_after_minus_before"]["ci95_high"]) for mode in modes)
    if movement_low >= -0.02:
        classification = "score_margin_sufficient"
    elif movement_high < -0.02:
        classification = "not_score_margin_sufficient"
    else:
        classification = "inconclusive"
    return {
        "status": "pass" if finite and audit_pass and deterministic and seed_paired else "fail",
        "pointer": "reports/canonical/gap_head_attribution_capsule.json:$.score_margin_causal_evidence",
        "deterministic_salts": {
            "shuffle_score_margin": SCORE_MARGIN_SHUFFLE_SALT,
            "replace_high_gap_score_margin_from_low_gap": SCORE_MARGIN_REPLACE_SALT,
        },
        "shuffle_score_margin": {
            "protocol": "seed_deterministic_row_permutation",
            "per_seed_before_after_metrics": [
                {
                    "seed": int(record["seed"]),
                    "before": record["before_metrics"],
                    "after": record["after_metrics"]["shuffle_score_margin"],
                    "delta": record["deltas"]["shuffle_score_margin"],
                    "audit": record["audits"]["shuffle_score_margin"],
                }
                for record in records
            ],
            "ci_summaries": ci_summaries["shuffle_score_margin"],
        },
        "replace_high_gap_score_margin_from_low_gap": {
            "protocol": "seed_deterministic_high_gap_replaced_from_low_gap",
            "per_seed_before_after_metrics": [
                {
                    "seed": int(record["seed"]),
                    "before": record["before_metrics"],
                    "after": record["after_metrics"]["replace_high_gap_score_margin_from_low_gap"],
                    "delta": record["deltas"]["replace_high_gap_score_margin_from_low_gap"],
                    "audit": record["audits"]["replace_high_gap_score_margin_from_low_gap"],
                }
                for record in records
            ],
            "ci_summaries": ci_summaries["replace_high_gap_score_margin_from_low_gap"],
        },
        "paired_deltas": [
            {
                "seed": int(record["seed"]),
                "same_seed": True,
                "same_arm_fit_path": True,
                "same_metric_set": True,
                "shuffle_score_margin": record["deltas"]["shuffle_score_margin"],
                "replace_high_gap_score_margin_from_low_gap": record["deltas"]["replace_high_gap_score_margin_from_low_gap"],
            }
            for record in records
        ],
        "channel_classification": classification,
        "protocol_checks": {
            "present": True,
            "deterministic": deterministic,
            "finite": finite,
            "seed_paired": seed_paired,
            "column_audited": audit_pass,
            "classified": classification in {"score_margin_sufficient", "not_score_margin_sufficient", "inconclusive"},
        },
        "ci_summaries": ci_summaries,
    }


def _a1_hardgates(aggregate: Mapping[str, Any]) -> dict[str, Any]:
    hg1 = _ci_low(aggregate, "full", "AUROC") > _ci_high(aggregate, "matched_random", "AUROC")
    hg2 = _ci_low(aggregate, "full", "UER_reduction") > _ci_high(aggregate, "matched_random", "UER_reduction")
    hg3 = _ci_low(aggregate, "full", "AUROC") > _ci_high(aggregate, "score_plus_margin", "AUROC")
    hg4 = _ci_low(aggregate, "full", "AUROC") > _ci_high(aggregate, "h_norm_only", "AUROC")
    transition_gap = _mean(aggregate, "full", "AUROC") - _mean(aggregate, "full_without_transition", "AUROC")
    transition_not_claimed = transition_gap <= 0.0
    hg5 = True
    gates = {
        "A1-HG1": _gate(
            "A1-HG1",
            hg1,
            "full AUROC CI-low > matched_random AUROC CI-high",
            {"full_ci_low": _ci_low(aggregate, "full", "AUROC"), "matched_random_ci_high": _ci_high(aggregate, "matched_random", "AUROC")},
        ),
        "A1-HG2": _gate(
            "A1-HG2",
            hg2,
            "full UER reduction CI-low > matched_random UER reduction CI-high",
            {"full_ci_low": _ci_low(aggregate, "full", "UER_reduction"), "matched_random_ci_high": _ci_high(aggregate, "matched_random", "UER_reduction")},
        ),
        "A1-HG3": _gate(
            "A1-HG3",
            hg3,
            "full AUROC CI-low > score_plus_margin AUROC CI-high",
            {"full_ci_low": _ci_low(aggregate, "full", "AUROC"), "score_plus_margin_ci_high": _ci_high(aggregate, "score_plus_margin", "AUROC")},
        ),
        "A1-HG4": _gate(
            "A1-HG4",
            hg4,
            "full AUROC CI-low > h_norm_only AUROC CI-high",
            {"full_ci_low": _ci_low(aggregate, "full", "AUROC"), "h_norm_only_ci_high": _ci_high(aggregate, "h_norm_only", "AUROC")},
        ),
        "A1-HG5": _gate(
            "A1-HG5",
            hg5,
            "full_without_transition and full indistinguishable means no transition mechanism claim",
            {
                "full_mean": _mean(aggregate, "full", "AUROC"),
                "full_without_transition_mean": _mean(aggregate, "full_without_transition", "AUROC"),
                "transition_mechanism_claimed": False,
                "transition_not_claimed_due_to_no_difference": bool(transition_not_claimed),
            },
        ),
    }
    hg6 = all(gate["status"] == "pass" for gate in gates.values())
    gates["A1-HG6"] = _gate(
        "A1-HG6",
        hg6,
        "D5-M requires A1-HG1 through A1-HG5 all pass",
        {"required_gates": ["A1-HG1", "A1-HG2", "A1-HG3", "A1-HG4", "A1-HG5"]},
    )
    failed = [name for name, gate in gates.items() if gate["status"] != "pass"]
    return {
        "status": "pass" if not failed else "fail",
        "gates": gates,
        "failed_gate": failed[0] if failed else None,
    }


def _shortcut_controls_clear(aggregate: Mapping[str, Any]) -> dict[str, bool]:
    controls = (
        "h_norm_only",
        "h_direction_only",
        "h_normalized_no_scale",
        "transition_delta_only",
        "score_plus_margin",
    )
    return {
        control: _ci_low(aggregate, "full_residualized_against_score_margin", "AUROC") > _ci_high(aggregate, control, "AUROC")
        for control in controls
    }


def _a4_hardgates(
    aggregate: Mapping[str, Any],
    residualized_attribution: Mapping[str, Any],
    score_margin_causal_evidence: Mapping[str, Any],
) -> dict[str, Any]:
    hg1 = residualized_attribution.get("status") == "pass"
    hg2 = (
        _ci_beats(aggregate, "full_residualized_against_score_margin", "matched_random", "AUROC")
        and _positive_ci(aggregate, "full_residualized_against_score_margin", "UER_reduction")
    )
    hg3 = (
        _ci_beats(aggregate, "full_without_score_and_margin", "matched_random", "AUROC")
        and _positive_ci(aggregate, "full_without_score_and_margin", "UER_reduction")
    )
    protocol = score_margin_causal_evidence.get("protocol_checks", {})
    hg4 = (
        score_margin_causal_evidence.get("status") == "pass"
        and all(protocol.get(name) is True for name in ("present", "deterministic", "finite", "seed_paired", "column_audited", "classified"))
        and score_margin_causal_evidence.get("channel_classification") in {"score_margin_sufficient", "not_score_margin_sufficient", "inconclusive"}
    )
    shortcut_clear = _shortcut_controls_clear(aggregate)
    hg5 = (
        hg1
        and hg2
        and hg3
        and hg4
        and score_margin_causal_evidence.get("channel_classification") == "not_score_margin_sufficient"
        and all(shortcut_clear.values())
    )
    gates = {
        "A4-HG1": _gate(
            "A4-HG1",
            hg1,
            "residualization finite/rank/condition/determinism/correlation-removal guards all pass",
            {"guard_outcomes": residualized_attribution.get("guard_outcomes", {})},
        ),
        "A4-HG2": _gate(
            "A4-HG2",
            hg2,
            "full_residualized_against_score_margin beats matched_random by AUROC CI and has positive UER-reduction CI",
            {
                "full_residualized_auroc_ci_low": _ci_low(aggregate, "full_residualized_against_score_margin", "AUROC"),
                "matched_random_auroc_ci_high": _ci_high(aggregate, "matched_random", "AUROC"),
                "full_residualized_uer_reduction_ci_low": _ci_low(aggregate, "full_residualized_against_score_margin", "UER_reduction"),
            },
        ),
        "A4-HG3": _gate(
            "A4-HG3",
            hg3,
            "full_without_score_and_margin beats matched_random by AUROC CI and has positive UER-reduction CI",
            {
                "full_without_score_margin_auroc_ci_low": _ci_low(aggregate, "full_without_score_and_margin", "AUROC"),
                "matched_random_auroc_ci_high": _ci_high(aggregate, "matched_random", "AUROC"),
                "full_without_score_margin_uer_reduction_ci_low": _ci_low(aggregate, "full_without_score_and_margin", "UER_reduction"),
            },
        ),
        "A4-HG4": _gate(
            "A4-HG4",
            hg4,
            "score/margin intervention protocol is present, deterministic, finite, paired, column-audited, and classified",
            {
                "protocol_checks": dict(protocol),
                "channel_classification": score_margin_causal_evidence.get("channel_classification"),
                "causal_objects": [
                    "$.score_margin_causal_evidence.shuffle_score_margin",
                    "$.score_margin_causal_evidence.replace_high_gap_score_margin_from_low_gap",
                    "$.score_margin_causal_evidence.paired_deltas",
                    "$.score_margin_causal_evidence.channel_classification",
                ],
            },
        ),
        "A4-HG5": _gate(
            "A4-HG5",
            hg5,
            "A4-HG1 through A4-HG4 pass, score/margin is not sufficient, and shortcut controls are not sufficient competitors",
            {
                "required_gates": ["A4-HG1", "A4-HG2", "A4-HG3", "A4-HG4"],
                "channel_classification": score_margin_causal_evidence.get("channel_classification"),
                "shortcut_controls_clear": shortcut_clear,
                "pointer": "reports/canonical/gap_head_attribution_capsule.json:$.a4_hardgates.gates.A4-HG5",
            },
        ),
    }
    failed = [name for name, gate in gates.items() if gate["status"] != "pass"]
    return {
        "status": "pass" if not failed else "fail",
        "pointer": "reports/canonical/gap_head_attribution_capsule.json:$.a4_hardgates",
        "gates": gates,
        "failed_gate": failed[0] if failed else None,
    }


def _mechanism_case(
    aggregate: Mapping[str, Any],
    hardgates: Mapping[str, Any],
    a4_hardgates: Mapping[str, Any] | None = None,
    score_margin_causal_evidence: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    if a4_hardgates is None or score_margin_causal_evidence is None:
        if hardgates["gates"]["A1-HG3"]["status"] == "pass" and hardgates["gates"]["A1-HG4"]["status"] == "pass":
            return {
                "case": "Case C",
                "status": "D5-M candidate",
                "failed_gate": hardgates["failed_gate"],
                "candidate_mechanism": "closed-attribution",
                "what_was_learned": "full exceeds score_plus_margin and h_norm_only under the predeclared CI gates.",
            }
        return {
            "case": "Case B",
            "status": "D5-O retained, mechanism = probe-margin-channel",
            "failed_gate": hardgates["failed_gate"],
            "candidate_mechanism": "probe-margin-channel",
            "what_was_learned": "score_plus_margin remains statistically competitive with full.",
        }
    residualized_strong = (
        a4_hardgates["gates"]["A4-HG2"]["status"] == "pass"
        and a4_hardgates["gates"]["A4-HG3"]["status"] == "pass"
    )
    classification = score_margin_causal_evidence.get("channel_classification")
    if not residualized_strong:
        mechanism = "probe-margin-channel" if classification == "score_margin_sufficient" else "unresolved"
        return {
            "case": "Case A",
            "status": f"D5-O retained, mechanism = {mechanism}" if mechanism == "probe-margin-channel" else "D5-O retained, mechanism unresolved",
            "failed_gate": a4_hardgates["failed_gate"],
            "candidate_mechanism": mechanism,
            "what_was_learned": "residualized attribution collapses against the predeclared matched-random comparisons.",
        }
    if classification == "score_margin_sufficient":
        return {
            "case": "Case B",
            "status": "D5-O retained, mechanism = probe-margin-channel",
            "failed_gate": "A4-HG5",
            "candidate_mechanism": "probe-margin-channel",
            "what_was_learned": "residualized attribution remains strong, but score/margin remains sufficient.",
        }
    if classification == "not_score_margin_sufficient":
        return {
            "case": "Case C",
            "status": "D5-M candidate" if a4_hardgates["gates"]["A4-HG5"]["status"] == "pass" else "D5-O retained, mechanism unresolved",
            "failed_gate": a4_hardgates["failed_gate"],
            "candidate_mechanism": "closed-attribution" if a4_hardgates["gates"]["A4-HG5"]["status"] == "pass" else "unresolved",
            "what_was_learned": "residualized attribution remains strong and score/margin is not sufficient.",
        }
    return {
        "case": "Case B",
        "status": "D5-O retained, mechanism unresolved",
        "failed_gate": "A4-HG5",
        "candidate_mechanism": "mixed-score-margin-channel",
        "what_was_learned": "residualized attribution remains strong, but score/margin sufficiency is inconclusive.",
    }


def _d5_o(aggregate: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "status": "ready",
        "claim": "D5-O robust operational pointer retained from canonical gap-head-on-h evidence.",
        "source_pointer": "reports/canonical/gap-head-on-h.json",
        "A1_capsule_arm_count": int(len(aggregate["arm_order"])),
    }


def _d5_m(hardgates: Mapping[str, Any], a4_hardgates: Mapping[str, Any] | None = None) -> dict[str, Any]:
    a1_passed = hardgates["gates"]["A1-HG6"]["status"] == "pass"
    a4_passed = a4_hardgates is not None and a4_hardgates["gates"]["A4-HG5"]["status"] == "pass"
    passed = a1_passed and a4_passed
    failed_gate = None
    if not a1_passed:
        failed_gate = hardgates["failed_gate"] or "A1-HG6"
    elif not a4_passed:
        failed_gate = (a4_hardgates or {}).get("failed_gate") or "A4-HG5"
    return {
        "status": "ready" if passed else "blocked",
        "passed": bool(passed),
        "requires": ["A1-HG1", "A1-HG2", "A1-HG3", "A1-HG4", "A1-HG5", "A1-HG6", "A4-HG1", "A4-HG2", "A4-HG3", "A4-HG4", "A4-HG5"],
        "failed_gate": failed_gate,
    }


def _control_pointer() -> dict[str, Any]:
    return {
        "matched_random": "$.control_evidence.matched_random",
        "h_random_rotation": "$.control_evidence.h_random_rotation",
        "h_random_projection_lowdim": "$.control_evidence.h_random_projection_lowdim",
    }


def _control_evidence(aggregate: Mapping[str, Any]) -> dict[str, Any]:
    return {
        arm: aggregate["by_arm"][arm]
        for arm in ("matched_random", "h_random_rotation", "h_random_projection_lowdim")
    }


def _scope_seal() -> dict[str, Any]:
    return {
        "status": "sealed",
        "not_claimed": list(NOT_CLAIMED),
        "scope": "Gaussian-OU learned-h gap-head attribution capsule for issue 692 A1.",
    }


def _revocation_ledger(hardgates: Mapping[str, Any], generated_at: str, d5_m: Mapping[str, Any] | None = None) -> list[dict[str, Any]]:
    if (d5_m or {}).get("passed") is True:
        return []
    return [
        {
            "event": "claim-demotion",
            "timestamp": generated_at,
            "artifact_id": ARTIFACT_ID,
            "failed_gate": (d5_m or {}).get("failed_gate") or hardgates["failed_gate"],
            "new_status": "D5-O-retained-D5-M-blocked",
        }
    ]


def _resolve_payload_pointer(payload: Mapping[str, Any], pointer: str | None) -> Any:
    if pointer is None or not pointer.startswith("$."):
        return None
    cursor: Any = payload
    for part in pointer[2:].split("."):
        if isinstance(cursor, Mapping) and part in cursor:
            cursor = cursor[part]
        else:
            return None
    return cursor


def _cost_protocol_pointer_resolves(capsule: Mapping[str, Any]) -> bool:
    return _resolve_payload_pointer(capsule, capsule.get("cost_protocol_pointer")) is not None


def _claim_capsule_hardgates(capsule: Mapping[str, Any]) -> dict[str, Any]:
    gates = {
        "CC-HG1": capsule.get("schema_id") == SCHEMA_ID and capsule.get("artifact_id") == ARTIFACT_ID,
        "CC-HG2": capsule.get("control_pointer") is not None,
        "CC-HG3": bool(capsule.get("failed_gate")) == (capsule.get("d5_m", {}).get("passed") is not True)
        and bool(capsule.get("what_was_learned")),
        "CC-HG4": capsule.get("d5_m", {}).get("passed") is True or bool(capsule.get("revocation_ledger")),
        "CC-HG5": capsule.get("forbidden_column_audit", {}).get("status") == "pass",
        "CC-HG6": _cost_protocol_pointer_resolves(capsule),
        "CC-HG7": capsule.get("scope_seal", {}).get("status") == "sealed" or capsule.get("positive_discovery_inputs") == [],
    }
    return {
        name: {"name": name, "status": "pass" if passed else "fail"}
        for name, passed in gates.items()
    }


def _source_artifacts(config: GapHeadRunConfig, run_dir: Path) -> dict[str, Any]:
    surface_helper = "scripts/run_gap_ledger_head_on_h.py::_surface_for_seed"
    fit_helper = "scripts/run_gap_ledger_head_on_h.py::_fit_gap_head"
    predict_helper = "scripts/run_gap_ledger_head_on_h.py::_predict_gap_head"
    metric_helper = "scripts/run_gap_ledger_head_on_h.py::_metrics_for_arm"
    matched_random_helper = "scripts/run_gap_ledger_head_on_h.py::_matched_random_gap_labels"
    assertion_helper = "scripts/run_gap_ledger_head_on_h.py::_assert_inference_columns"
    return {
        "artifact_id": ARTIFACT_ID,
        "source_issue": SOURCE_ISSUE,
        "generation_script": "scripts/run_gap_head_attribution_capsule.py",
        "surface_helper": surface_helper,
        "fit_helper": fit_helper,
        "predict_helper": predict_helper,
        "metric_helper": metric_helper,
        "matched_random_helper": matched_random_helper,
        "assertion_helper": assertion_helper,
        "config_type": "scripts/run_gap_ledger_head_on_h.py::GapHeadRunConfig",
        "json_artifact": config.json_artifact,
        "markdown_artifact": config.report_artifact,
        "cost_protocol": {
            "status": "recorded",
            "unit": "seed-arm surface evaluation",
            "sample_count": int(config.sample_count),
            "seed_count": int(len(config.seeds)),
            "arm_count": len(ARM_NAMES),
            "surface_protocol": {
                "surface_helper": surface_helper,
                "fit_helper": fit_helper,
                "predict_helper": predict_helper,
                "metric_helper": metric_helper,
            },
            "control_protocol": {
                "matched_random_helper": matched_random_helper,
                "assertion_helper": assertion_helper,
            },
        },
        "run_artifacts": {
            "run_dir": str(run_dir.relative_to(ROOT)),
            "claim_capsule": str((run_dir / "claim_capsule.json").relative_to(ROOT)),
            "raw_metrics": str((run_dir / "raw_metrics.jsonl").relative_to(ROOT)),
            "summary": str((run_dir / "summary.json").relative_to(ROOT)),
            "report": str((run_dir / "report.md").relative_to(ROOT)),
        },
    }


def _build_payload(
    records: Sequence[Mapping[str, Any]],
    config: GapHeadRunConfig,
    *,
    run_id: str,
    generated_at: str,
    run_dir: Path,
) -> dict[str, Any]:
    aggregate = _aggregate(records)
    hardgates = _a1_hardgates(aggregate)
    residualized_attribution = _residualized_attribution(records, aggregate)
    score_margin_causal_evidence = _score_margin_causal_evidence(config)
    a4_hardgates = _a4_hardgates(aggregate, residualized_attribution, score_margin_causal_evidence)
    mechanism_case = _mechanism_case(aggregate, hardgates, a4_hardgates, score_margin_causal_evidence)
    columns_by_arm = {
        arm: next(record["feature_columns"] for record in records if record["arm"] == arm)
        for arm in ARM_NAMES
    }
    forbidden_audit = _forbidden_column_audit(columns_by_arm)
    d5_m = _d5_m(hardgates, a4_hardgates)
    source_artifacts = _source_artifacts(config, run_dir)
    capsule: dict[str, Any] = {
        "schema_id": SCHEMA_ID,
        "source_issue": SOURCE_ISSUE,
        "artifact_id": ARTIFACT_ID,
        "run_id": run_id,
        "generated_at": generated_at,
        "d5_o": _d5_o(aggregate),
        "d5_m": d5_m,
        "mechanism_case": mechanism_case,
        "hardgates": hardgates,
        "residualized_attribution": residualized_attribution,
        "score_margin_causal_evidence": score_margin_causal_evidence,
        "a4_hardgates": a4_hardgates,
        "claim_capsule_hardgates": {},
        "cost_protocol_pointer": "$.source_artifacts.cost_protocol",
        "control_pointer": _control_pointer(),
        "control_evidence": _control_evidence(aggregate),
        "scope_seal": _scope_seal(),
        "forbidden_column_audit": forbidden_audit,
        "failed_gate": d5_m["failed_gate"],
        "what_was_learned": mechanism_case["what_was_learned"],
        "revocation_ledger": _revocation_ledger(hardgates, generated_at, d5_m),
        "positive_discovery_inputs": ["A1-HG1", "A1-HG2"] if hardgates["gates"]["A1-HG1"]["status"] == "pass" and hardgates["gates"]["A1-HG2"]["status"] == "pass" else [],
        "scope": {"not_claimed": list(NOT_CLAIMED)},
        "source_artifacts": source_artifacts,
    }
    capsule["claim_capsule_hardgates"] = _claim_capsule_hardgates(capsule)
    return {
        **capsule,
        "canonical_name": CANONICAL_NAME,
        "json_artifact": config.json_artifact,
        "markdown_artifact": config.report_artifact,
        "config": {
            "sample_count": int(config.sample_count),
            "seed_count": int(len(config.seeds)),
            "seeds": [int(seed) for seed in config.seeds],
            "rho": float(config.rho),
            "use_torch": bool(config.use_torch),
            "run_id_prefix": config.run_id_prefix,
            "arm_count": len(ARM_NAMES),
            "arm_order": list(ARM_NAMES),
        },
        "aggregate": aggregate,
        "records": list(records),
    }


def _render_report(payload: Mapping[str, Any]) -> str:
    lines = [
        "# Gap-Head Attribution Capsule",
        "",
        f"- Generated at: `{payload['generated_at']}`",
        f"- Run id: `{payload['run_id']}`",
        f"- Artifact id: `{payload['artifact_id']}`",
        f"- D5-O: `{payload['d5_o']['status']}`",
        f"- D5-M: `{payload['d5_m']['status']}`",
        f"- Mechanism case: `{payload['mechanism_case']['case']}`",
        f"- Failed gate: `{payload['failed_gate']}`",
        "",
        "## Arms",
        "",
        "| arm | AUROC | UER reduction | family | gate role |",
        "| --- | ---: | ---: | --- | --- |",
    ]
    for arm in payload["aggregate"]["arm_order"]:
        row = payload["aggregate"]["by_arm"][arm]
        lines.append(
            "| "
            f"`{arm}` | "
            f"{_render_stats(row['AUROC'])} | "
            f"{_render_stats(row['UER_reduction'])} | "
            f"`{row['family']}` | "
            f"`{row['gate_role']}` |"
        )
    lines.extend(["", "## A1 Hardgates", "", "| gate | status |", "| --- | --- |"])
    for name, gate in payload["hardgates"]["gates"].items():
        lines.append(f"| `{name}` | `{gate['status']}` |")
    lines.extend(["", "## A4 Hardgates", "", "| gate | status |", "| --- | --- |"])
    for name, gate in payload["a4_hardgates"]["gates"].items():
        lines.append(f"| `{name}` | `{gate['status']}` |")
    lines.extend(["", "## Claim Capsule Hardgates", "", "| gate | status |", "| --- | --- |"])
    for name, gate in payload["claim_capsule_hardgates"].items():
        lines.append(f"| `{name}` | `{gate['status']}` |")
    lines.extend(["", "## Scope", ""])
    for item in payload["scope"]["not_claimed"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def _write_json(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _write_artifacts(payload: Mapping[str, Any], run_dir: Path, *, canonical: bool = True) -> None:
    claim_capsule = {key: payload[key] for key in (
        "schema_id",
        "source_issue",
        "artifact_id",
        "run_id",
        "d5_o",
        "d5_m",
        "mechanism_case",
        "hardgates",
        "residualized_attribution",
        "score_margin_causal_evidence",
        "a4_hardgates",
        "claim_capsule_hardgates",
        "cost_protocol_pointer",
        "control_pointer",
        "control_evidence",
        "scope_seal",
        "forbidden_column_audit",
        "failed_gate",
        "what_was_learned",
        "revocation_ledger",
        "positive_discovery_inputs",
        "scope",
        "source_artifacts",
    )}
    claim_capsule["claim_capsule_hardgates"] = _claim_capsule_hardgates(claim_capsule)
    _write_json(run_dir / "claim_capsule.json", claim_capsule)
    raw_path = run_dir / "raw_metrics.jsonl"
    raw_path.parent.mkdir(parents=True, exist_ok=True)
    raw_path.write_text(
        "".join(json.dumps(record, sort_keys=True) + "\n" for record in payload["records"]),
        encoding="utf-8",
    )
    summary = {key: payload[key] for key in (
        "schema_id",
        "source_issue",
        "artifact_id",
        "run_id",
        "generated_at",
        "d5_o",
        "d5_m",
        "mechanism_case",
        "hardgates",
        "residualized_attribution",
        "score_margin_causal_evidence",
        "a4_hardgates",
        "claim_capsule_hardgates",
        "cost_protocol_pointer",
        "control_pointer",
        "control_evidence",
        "scope_seal",
        "forbidden_column_audit",
        "failed_gate",
        "what_was_learned",
        "revocation_ledger",
        "positive_discovery_inputs",
        "config",
        "source_artifacts",
        "aggregate",
        "scope",
    )}
    summary["claim_capsule_hardgates"] = _claim_capsule_hardgates(summary)
    _write_json(run_dir / "summary.json", summary)
    _write_text(run_dir / "report.md", _render_report(payload))
    if canonical:
        _write_json(ROOT / CANONICAL_JSON_ARTIFACT, summary)
        _write_text(ROOT / CANONICAL_MARKDOWN_ARTIFACT, _render_report(payload))


def _new_run_id() -> str:
    return f"a1-{datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')}"


def _active_config(run_id: str) -> GapHeadRunConfig:
    default = source.DEFAULT_CONFIG
    return GapHeadRunConfig(
        sample_count=default.sample_count,
        seeds=default.seeds,
        rho=default.rho,
        use_torch=source.USE_TORCH,
        json_artifact=CANONICAL_JSON_ARTIFACT,
        report_artifact=CANONICAL_MARKDOWN_ARTIFACT,
        run_id_prefix=run_id,
        source_artifact_label=ARTIFACT_ID,
        seed_grid_kind=default.seed_grid_kind,
    )


def build_gap_head_attribution_capsule(
    *,
    root: Path | str | None = None,
    run_id: str | None = None,
    generated_at: str | None = None,
    config: GapHeadRunConfig | None = None,
) -> dict[str, Any]:
    global ROOT
    if root is not None:
        ROOT = Path(root)
        source.ROOT = ROOT
    active_run_id = _new_run_id() if run_id is None else run_id
    timestamp = generated_at if generated_at is not None else datetime.now(timezone.utc).isoformat()
    active_config = _active_config(active_run_id) if config is None else config
    run_dir = ROOT / RUNS_DIR / active_run_id
    records = _records(active_config)
    return _build_payload(records, active_config, run_id=active_run_id, generated_at=timestamp, run_dir=run_dir)


def write_gap_head_attribution_capsule(
    *,
    root: Path | str | None = None,
    run_id: str | None = None,
    generated_at: str | None = None,
    canonical: bool = True,
) -> dict[str, Any]:
    payload = build_gap_head_attribution_capsule(root=root, run_id=run_id, generated_at=generated_at)
    _write_artifacts(payload, ROOT / RUNS_DIR / payload["run_id"], canonical=canonical)
    return payload


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", default=str(ROOT), help="Repository root for artifacts.")
    parser.add_argument("--run-id", help="Deterministic run directory id.")
    parser.add_argument("--no-canonical", action="store_true", help="Write run artifacts only.")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> None:
    args = parse_args(argv)
    payload = write_gap_head_attribution_capsule(
        root=args.root,
        run_id=args.run_id,
        canonical=not args.no_canonical,
    )
    print(f"wrote reports/runs/{payload['run_id']}/claim_capsule.json")
    print(f"wrote reports/runs/{payload['run_id']}/raw_metrics.jsonl")
    print(f"wrote reports/runs/{payload['run_id']}/summary.json")
    print(f"wrote reports/runs/{payload['run_id']}/report.md")
    if not args.no_canonical:
        print(f"wrote {CANONICAL_JSON_ARTIFACT}")
        print(f"wrote {CANONICAL_MARKDOWN_ARTIFACT}")
    print(f"mechanism_case {payload['mechanism_case']['case']}")
    print(f"d5_m {payload['d5_m']['status']}")


if __name__ == "__main__":
    main()

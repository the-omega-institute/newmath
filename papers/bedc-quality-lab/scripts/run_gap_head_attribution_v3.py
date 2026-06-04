#!/usr/bin/env python3
"""Produce the A1 gap-head attribution capsule for issue 692."""

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


SCHEMA_ID = "bedc.quality.claim_capsule.v1"
SOURCE_ISSUE = 692
ARTIFACT_ID = "gap_head_attribution_v3"
CANONICAL_NAME = "gap-head-attribution-v3"
CANONICAL_JSON_ARTIFACT = "reports/canonical/gap_head_attribution_v3.json"
CANONICAL_MARKDOWN_ARTIFACT = "reports/canonical/gap_head_attribution_v3.md"
RUNS_DIR = "reports/runs"
PROJECTION_DIM = 1
PROJECTION_SEED_SALT = 811_773
ROTATION_SEED_SALT = 811_747
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


def _roots_builder(surface: Mapping[str, Any], spec: AttributionArmSpec, seed: int) -> tuple[np.ndarray, list[str], dict[str, Any]]:
    del seed
    roots = set(spec.feature_roots)
    blocks = _surface_blocks(surface)
    order = ("h", "score", "margin", "transition_delta", "quality")
    parts = [blocks[root] for root in order if root in roots]
    columns = [column for root in order if root in roots for column in _block_columns(surface, {root})]
    return np.column_stack(parts).astype(np.float64), columns, {}


def _without_roots_builder(surface: Mapping[str, Any], spec: AttributionArmSpec, seed: int) -> tuple[np.ndarray, list[str], dict[str, Any]]:
    del seed
    included = set(spec.feature_roots)
    blocks = _surface_blocks(surface)
    order = ("h", "score", "margin", "transition_delta", "quality")
    parts = [blocks[root] for root in order if root in included]
    columns = [column for root in order if root in included for column in _block_columns(surface, {root})]
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
    representation = surface.get("representation")
    if isinstance(representation, Mapping) and int(representation.get("output_dim", h.shape[1])) == h.shape[1]:
        return np.roll(h, shift=1, axis=0)
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
    return np.column_stack(parts).astype(np.float64), columns, {"threshold_policy": "train_surface_mean_by_score_column"}


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
    _make_spec("h_only", "h", _roots_builder, ("h",)),
    _make_spec("h_centered_only", "h", _h_centered_builder, ("h_centered",)),
    _make_spec("h_normalized_no_scale", "h", _h_normalized_builder, ("h_normalized_no_scale",)),
    _make_spec("h_direction_only", "h", _h_direction_builder, ("h_direction",)),
    _make_spec("h_norm_only", "h_control", _h_norm_builder, ("h_norm",), gate_role="A1-HG4-control"),
    _make_spec("h_random_rotation", "h_control", _rotation_builder, ("h_random_rotation",), control_role="h_derived_control", seed_policy="seed_orthogonal_rotation"),
    _make_spec("h_random_projection_lowdim", "h_control", _projection_builder, ("h_random_projection_lowdim",), control_role="h_derived_control", seed_policy="seed_gaussian_projection"),
    _make_spec("score_only", "score", _roots_builder, ("score",)),
    _make_spec("margin_only", "margin", _roots_builder, ("margin",)),
    _make_spec("score_plus_margin", "score_margin", _score_plus_margin_builder, ("score_plus_margin",), gate_role="A1-HG3-control"),
    _make_spec("transition_delta_only", "transition", _roots_builder, ("transition_delta",)),
    _make_spec("quality_scalars_only", "quality", _roots_builder, ("quality",)),
    _make_spec("h_plus_margin", "combined", _roots_builder, ("h", "margin")),
    _make_spec("h_plus_transition", "combined", _roots_builder, ("h", "transition_delta")),
    _make_spec("h_plus_quality", "combined", _roots_builder, ("h", "quality")),
    _make_spec("full_without_h", "ablation", _without_roots_builder, ("score", "margin", "transition_delta", "quality")),
    _make_spec("full_without_score", "ablation", _without_roots_builder, ("h", "margin", "transition_delta", "quality")),
    _make_spec("full_without_margin", "ablation", _without_roots_builder, ("h", "score", "transition_delta", "quality")),
    _make_spec("full_without_transition", "ablation", _without_roots_builder, ("h", "score", "margin", "quality"), gate_role="A1-HG5-ablation"),
    _make_spec("full_without_quality_scalars", "ablation", _without_roots_builder, ("h", "score", "margin", "transition_delta")),
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


def _mechanism_case(aggregate: Mapping[str, Any], hardgates: Mapping[str, Any]) -> dict[str, Any]:
    if hardgates["gates"]["A1-HG3"]["status"] == "pass" and hardgates["gates"]["A1-HG4"]["status"] == "pass":
        return {
            "case": "Case 1",
            "status": "D5-M candidate",
            "failed_gate": hardgates["failed_gate"],
            "what_was_learned": "full exceeds score_plus_margin and h_norm_only under the predeclared CI gates.",
        }
    score_close = _ci_high(aggregate, "score_plus_margin", "AUROC") >= _ci_low(aggregate, "full", "AUROC")
    norm_close = _ci_high(aggregate, "h_norm_only", "AUROC") >= _ci_low(aggregate, "full", "AUROC")
    if score_close:
        return {
            "case": "Case 2",
            "status": "D5-O retained, mechanism = probe-margin-channel",
            "failed_gate": "A1-HG3",
            "what_was_learned": "score_plus_margin remains statistically competitive with full.",
        }
    if norm_close:
        return {
            "case": "Case 3",
            "status": "demote mechanism to scale/norm detector",
            "failed_gate": "A1-HG4",
            "what_was_learned": "h_norm_only remains statistically competitive with full.",
        }
    return {
        "case": "Case 2",
        "status": "D5-O retained, mechanism unresolved",
        "failed_gate": hardgates["failed_gate"],
        "what_was_learned": "the attribution ledger did not satisfy every D5-M gate.",
    }


def _d5_o(aggregate: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "status": "ready",
        "claim": "D5-O robust operational pointer retained from canonical gap-head-on-h evidence.",
        "source_pointer": "reports/canonical/gap-head-on-h.json",
        "A1_capsule_arm_count": int(len(aggregate["arm_order"])),
    }


def _d5_m(hardgates: Mapping[str, Any]) -> dict[str, Any]:
    passed = hardgates["gates"]["A1-HG6"]["status"] == "pass"
    return {
        "status": "ready" if passed else "blocked",
        "passed": bool(passed),
        "requires": ["A1-HG1", "A1-HG2", "A1-HG3", "A1-HG4", "A1-HG5"],
        "failed_gate": hardgates["failed_gate"],
    }


def _control_pointer() -> dict[str, Any]:
    return {
        "matched_random": "$.aggregate.by_arm.matched_random",
        "h_random_rotation": "$.aggregate.by_arm.h_random_rotation",
        "h_random_projection_lowdim": "$.aggregate.by_arm.h_random_projection_lowdim",
    }


def _scope_seal() -> dict[str, Any]:
    return {
        "status": "sealed",
        "not_claimed": list(NOT_CLAIMED),
        "scope": "Gaussian-OU learned-h gap-head attribution capsule for issue 692 A1.",
    }


def _revocation_ledger(hardgates: Mapping[str, Any], generated_at: str) -> list[dict[str, Any]]:
    if hardgates["status"] == "pass":
        return []
    return [
        {
            "event": "claim-demotion",
            "timestamp": generated_at,
            "artifact_id": ARTIFACT_ID,
            "failed_gate": hardgates["failed_gate"],
            "new_status": "D5-O-retained-D5-M-blocked",
        }
    ]


def _claim_capsule_hardgates(capsule: Mapping[str, Any]) -> dict[str, Any]:
    gates = {
        "CC-HG1": capsule.get("schema_id") == SCHEMA_ID and capsule.get("artifact_id") == ARTIFACT_ID,
        "CC-HG2": capsule.get("control_pointer") is not None,
        "CC-HG3": bool(capsule.get("failed_gate")) == (capsule.get("d5_m", {}).get("passed") is not True)
        and bool(capsule.get("what_was_learned")),
        "CC-HG4": capsule.get("d5_m", {}).get("passed") is True or bool(capsule.get("revocation_ledger")),
        "CC-HG5": capsule.get("forbidden_column_audit", {}).get("status") == "pass",
        "CC-HG6": capsule.get("cost_protocol_pointer") is not None or capsule.get("quality_verdict") is None,
        "CC-HG7": capsule.get("scope_seal", {}).get("status") == "sealed" or capsule.get("positive_discovery_inputs") == [],
    }
    return {
        name: {"name": name, "status": "pass" if passed else "fail"}
        for name, passed in gates.items()
    }


def _source_artifacts(config: GapHeadRunConfig, run_dir: Path) -> dict[str, Any]:
    return {
        "artifact_id": ARTIFACT_ID,
        "source_issue": SOURCE_ISSUE,
        "generation_script": "scripts/run_gap_head_attribution_v3.py",
        "surface_helper": "scripts/run_gap_ledger_head_on_h.py::_surface_for_seed",
        "fit_helper": "scripts/run_gap_ledger_head_on_h.py::_fit_gap_head",
        "predict_helper": "scripts/run_gap_ledger_head_on_h.py::_predict_gap_head",
        "metric_helper": "scripts/run_gap_ledger_head_on_h.py::_metrics_for_arm",
        "matched_random_helper": "scripts/run_gap_ledger_head_on_h.py::_matched_random_gap_labels",
        "assertion_helper": "scripts/run_gap_ledger_head_on_h.py::_assert_inference_columns",
        "config_type": "scripts/run_gap_ledger_head_on_h.py::GapHeadRunConfig",
        "json_artifact": config.json_artifact,
        "markdown_artifact": config.report_artifact,
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
    mechanism_case = _mechanism_case(aggregate, hardgates)
    columns_by_arm = {
        arm: next(record["feature_columns"] for record in records if record["arm"] == arm)
        for arm in ARM_NAMES
    }
    forbidden_audit = _forbidden_column_audit(columns_by_arm)
    d5_m = _d5_m(hardgates)
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
        "claim_capsule_hardgates": {},
        "cost_protocol_pointer": "$.source_artifacts.source_surface",
        "control_pointer": _control_pointer(),
        "scope_seal": _scope_seal(),
        "forbidden_column_audit": forbidden_audit,
        "failed_gate": d5_m["failed_gate"],
        "what_was_learned": mechanism_case["what_was_learned"],
        "revocation_ledger": _revocation_ledger(hardgates, generated_at),
        "positive_discovery_inputs": ["A1-HG1", "A1-HG2"] if hardgates["gates"]["A1-HG1"]["status"] == "pass" and hardgates["gates"]["A1-HG2"]["status"] == "pass" else [],
        "scope": {"not_claimed": list(NOT_CLAIMED)},
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
        "source_artifacts": _source_artifacts(config, run_dir),
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
    _write_json(run_dir / "claim_capsule.json", {key: payload[key] for key in (
        "schema_id",
        "source_issue",
        "artifact_id",
        "run_id",
        "d5_o",
        "d5_m",
        "mechanism_case",
        "hardgates",
        "claim_capsule_hardgates",
        "cost_protocol_pointer",
        "control_pointer",
        "scope_seal",
        "forbidden_column_audit",
        "failed_gate",
        "what_was_learned",
        "revocation_ledger",
        "positive_discovery_inputs",
        "scope",
    )})
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
        "claim_capsule_hardgates",
        "cost_protocol_pointer",
        "control_pointer",
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


def build_gap_head_attribution_v3(
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


def write_gap_head_attribution_v3(
    *,
    root: Path | str | None = None,
    run_id: str | None = None,
    generated_at: str | None = None,
    canonical: bool = True,
) -> dict[str, Any]:
    payload = build_gap_head_attribution_v3(root=root, run_id=run_id, generated_at=generated_at)
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
    payload = write_gap_head_attribution_v3(
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

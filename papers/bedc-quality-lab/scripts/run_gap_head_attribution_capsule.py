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

from bedc_quality_lab.backends.current_lab.gap_head_readiness import (
    GAP_HEAD_ABLATION_ARTIFACT,
    GAP_HEAD_ROBUSTNESS_ARTIFACT,
    NEGATIVE_WITNESSES_ARTIFACT,
    OBSERVED_DEBT_ARTIFACT,
    GapHeadD5ReadinessLedger,
    GapHeadOperationalReadinessPolicy,
)
from bedc_quality_lab.discovery_compiler.pointers import pointer_value
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
SOURCE_ISSUES = (692, 747, 750)
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
HEAD_PATCH_PERMUTE_SALT = 750_311
HEAD_PATCH_REQUIRED_MODES = ("null_head", "permute_head_rows")
HEAD_CAUSAL_PATCH_CLAIM_JSON_PATH = "$.head_channel_patch_evidence.causal_patch_claim"
GAP_HEAD_D5_CONTEXT_ARTIFACTS = (
    GAP_HEAD_ROBUSTNESS_ARTIFACT,
    GAP_HEAD_ABLATION_ARTIFACT,
    NEGATIVE_WITNESSES_ARTIFACT,
    OBSERVED_DEBT_ARTIFACT,
)
EPS = 1.0e-8
NOT_CLAIMED = (
    "global model quality",
    "full LeJEPA reproduction",
    "full TensorNameCert",
    "LLM behavior quality",
    "mechanism closure unless D5-M",
)
NOT_IMPLEMENTED = (
    "nonlinear_residualization",
    "full_causal_replacement_scope",
)
FORBIDDEN_INFERENCE_COLUMNS = source.FORBIDDEN_INFERENCE_COLUMNS
A1_NEGATIVE_WITNESS_OWNER_POINTER = "$.run_local.negative_witness[0]"
A1_NEGATIVE_WITNESS_KEYS = (
    "witness_id",
    "source_artifact",
    "source_pointer",
    "bedc_gap_field",
    "demotion_rule",
    "regression_test",
    "evidence_pointer",
    "status",
    "reason",
)
A1_NEGATIVE_WITNESS_REGRESSION_TEST = (
    "tests/test_gap_head_attribution_capsule.py::"
    "test_a1_run_local_negative_witness_records_a1_hg3_failure"
)
RESIDUALIZED_ATTRIBUTION_CLAIM_SLOTS: tuple[tuple[str, str], ...] = (
    ("full", "full"),
    ("score_plus_margin", "score_plus_margin"),
    ("full_residualized", "full_residualized_against_score_margin"),
    ("h_only", "h_only"),
    ("h_normalized", "h_normalized_no_scale"),
    ("h_norm_only", "h_norm_only"),
    ("full_without_score", "full_without_score"),
    ("margin", "margin_only"),
)
RESIDUALIZED_ATTRIBUTION_CLAIM_FORBIDDEN_KEYS = (
    "terminal_verdict",
    "claim_verdict",
    "candidate_body",
    "records",
    "raw_payload",
)
RESIDUALIZED_ATTRIBUTION_CLAIM_FORBIDDEN_TEXT = (
    "host.env",
    ".refactor-loop/host.env",
)
HEAD_CHANNEL_PATCH_CLAIM_FORBIDDEN_KEYS = (
    *RESIDUALIZED_ATTRIBUTION_CLAIM_FORBIDDEN_KEYS,
    "candidate_actual_body",
    "per_seed_before_after_metrics",
    "before",
    "after",
    "delta",
    "ci_summaries",
    "AUROC",
    "UnloggedErrorRate",
    "UER_reduction",
    "gate_evidence",
)
DGT_NEURAL_ABLATION_POINTERS = {
    "hardgate": "reports/canonical/dgt-neural-ablation.json:$.nabl_hardgates.status",
    "component_claims": "reports/canonical/dgt-neural-ablation.json:$.component_causal_claims",
    "claim_capsule": "reports/canonical/dgt-neural-ablation.json:$.claim_capsule_ref",
    "hg7_boundary": "reports/canonical/dgt-neural-ablation.json:$.boundary_ledger",
}


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


def _load_artifact_payload(relative_path: str) -> dict[str, Any]:
    path = ROOT / relative_path
    if not path.exists():
        return {}
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"canonical report payload must be a JSON object: {relative_path}")
    return payload


def _gap_head_d5_context() -> dict[str, dict[str, Any]]:
    return {artifact: _load_artifact_payload(artifact) for artifact in GAP_HEAD_D5_CONTEXT_ARTIFACTS}


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
        audit = source._forbidden_column_audit(list(columns))
        if audit["status"] != "pass":
            violations.append(
                {
                    "arm": arm,
                    "columns": list(audit["forbidden_present"]),
                    "failed_gate": audit.get("failed_gate"),
                    "violations": list(audit["violations"]),
                }
            )
    return {
        "status": "pass" if not violations else "fail",
        "forbidden_columns": list(FORBIDDEN_INFERENCE_COLUMNS),
        "forbidden_inference_columns": list(FORBIDDEN_INFERENCE_COLUMNS),
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


def _artifact_pointer(artifact: str, pointer: str) -> str:
    return f"{artifact}:{pointer}"


def _capsule_pointer(pointer: str) -> str:
    return _artifact_pointer(CANONICAL_JSON_ARTIFACT, pointer)


def _resolve_artifact_pointer_in_capsule(payload: Mapping[str, Any], artifact_pointer: str) -> Any:
    if ":$" not in artifact_pointer:
        return None
    artifact, pointer = artifact_pointer.split(":", 1)
    if artifact != CANONICAL_JSON_ARTIFACT:
        return None
    return _resolve_payload_pointer(payload, pointer)


def _forbidden_key_paths(payload: Any, *, path: str = "$") -> list[str]:
    paths: list[str] = []
    if isinstance(payload, Mapping):
        for key, value in payload.items():
            key_path = f"{path}.{key}"
            if key in RESIDUALIZED_ATTRIBUTION_CLAIM_FORBIDDEN_KEYS:
                paths.append(key_path)
            paths.extend(_forbidden_key_paths(value, path=key_path))
    elif isinstance(payload, list):
        for index, value in enumerate(payload):
            paths.extend(_forbidden_key_paths(value, path=f"{path}.{index}"))
    elif isinstance(payload, str):
        for forbidden in RESIDUALIZED_ATTRIBUTION_CLAIM_FORBIDDEN_TEXT:
            if forbidden in payload:
                paths.append(path)
                break
    return paths


def _residualized_attribution_claim(
    aggregate: Mapping[str, Any],
    residualized_attribution: Mapping[str, Any],
    score_margin_causal_evidence: Mapping[str, Any],
    a4_hardgates: Mapping[str, Any],
) -> dict[str, Any]:
    slots = []
    for slot, source_arm in RESIDUALIZED_ATTRIBUTION_CLAIM_SLOTS:
        metric_pointers = {
            metric: _capsule_pointer(f"$.aggregate.by_arm.{source_arm}.{metric}.mean")
            for metric in ("AUROC", "UER_reduction")
        }
        slots.append(
            {
                "slot": slot,
                "source_arm": source_arm,
                "source_artifact": CANONICAL_JSON_ARTIFACT,
                "metric_pointers": metric_pointers,
                "status": "present" if source_arm in aggregate.get("by_arm", {}) else "missing",
                "failure_reason": None if source_arm in aggregate.get("by_arm", {}) else "missing-source-arm",
            }
        )
    residualized_beats_random = _ci_beats(aggregate, "full_residualized_against_score_margin", "matched_random", "AUROC")
    residualized_positive_uer = _positive_ci(aggregate, "full_residualized_against_score_margin", "UER_reduction")
    allowed = (
        residualized_attribution.get("status") == "pass"
        and residualized_beats_random
        and residualized_positive_uer
        and a4_hardgates.get("gates", {}).get("A4-HG5", {}).get("status") == "pass"
        and score_margin_causal_evidence.get("channel_classification") == "not_score_margin_sufficient"
    )
    return {
        "status": "pass" if allowed else "fail",
        "pointer": _capsule_pointer("$.residualized_attribution_claim"),
        "source_artifact": CANONICAL_JSON_ARTIFACT,
        "slot_order": [slot for slot, _source_arm in RESIDUALIZED_ATTRIBUTION_CLAIM_SLOTS],
        "slots": slots,
        "metric_source_pointer": _capsule_pointer("$.residualized_attribution"),
        "hardgate_source_pointer": _capsule_pointer("$.e_hardgates"),
        "non_score_mechanism_claim_allowed": bool(allowed),
        "failure_reason": None if allowed else "non-score-mechanism-claim-blocked",
    }


def _residualized_claim_slot_set_ok(claim: Mapping[str, Any]) -> bool:
    slots = claim.get("slots")
    if not isinstance(slots, list):
        return False
    observed = {
        (slot.get("slot"), slot.get("source_arm"))
        for slot in slots
        if isinstance(slot, Mapping)
    }
    return observed == set(RESIDUALIZED_ATTRIBUTION_CLAIM_SLOTS)


def _residualized_claim_pointers(claim: Mapping[str, Any]) -> list[str]:
    pointers: list[str] = []
    pointer = claim.get("pointer")
    if isinstance(pointer, str):
        pointers.append(pointer)
    for key in ("metric_source_pointer", "hardgate_source_pointer"):
        value = claim.get(key)
        if isinstance(value, str):
            pointers.append(value)
    for slot in claim.get("slots", []):
        if not isinstance(slot, Mapping):
            continue
        for value in slot.get("metric_pointers", {}).values():
            if isinstance(value, str):
                pointers.append(value)
    return pointers


def _e_hardgates(aggregate: Mapping[str, Any], claim: Mapping[str, Any]) -> dict[str, Any]:
    slot_set = _residualized_claim_slot_set_ok(claim)
    forbidden_paths = _forbidden_key_paths(claim)
    residualized_beats_random = _ci_beats(aggregate, "full_residualized_against_score_margin", "matched_random", "AUROC")
    residualized_positive_uer = _positive_ci(aggregate, "full_residualized_against_score_margin", "UER_reduction")
    allowed = claim.get("non_score_mechanism_claim_allowed") is True and slot_set and not forbidden_paths
    pointer_resolution_gate = _gate(
        "E-HG2_pointer_resolution",
        False,
        "all residualized attribution claim artifact-qualified pointers resolve inside the attribution capsule",
        {
            "pointer_count": len(_residualized_claim_pointers(claim)),
            "unresolved_pointers": [],
            "deferred_until": "committed_round_trip",
        },
    )
    gates = {
        "E-HG1_slot_set": _gate(
            "E-HG1_slot_set",
            slot_set,
            "residualized attribution claim exposes exactly the eight predeclared slots",
            {
                "expected_slots": [slot for slot, _source_arm in RESIDUALIZED_ATTRIBUTION_CLAIM_SLOTS],
                "observed_slots": [slot.get("slot") for slot in claim.get("slots", []) if isinstance(slot, Mapping)],
            },
        ),
        "E-HG2_pointer_resolution": pointer_resolution_gate,
        "E-HG3_residualized_full_vs_matched_random": _gate(
            "E-HG3_residualized_full_vs_matched_random",
            residualized_beats_random and residualized_positive_uer,
            "full_residualized AUROC CI-low beats matched_random AUROC CI-high and has positive UER-reduction CI",
            {
                "full_residualized_auroc_ci_low": _ci_low(aggregate, "full_residualized_against_score_margin", "AUROC"),
                "matched_random_auroc_ci_high": _ci_high(aggregate, "matched_random", "AUROC"),
                "full_residualized_uer_reduction_ci_low": _ci_low(aggregate, "full_residualized_against_score_margin", "UER_reduction"),
            },
        ),
        "E-HG4_non_score_mechanism_claim_fail_closed": _gate(
            "E-HG4_non_score_mechanism_claim_fail_closed",
            allowed,
            "non-score mechanism claim is allowed only when residualized_full beats matched_random and all upstream mechanism gates allow it",
            {
                "non_score_mechanism_claim_allowed": allowed,
                "claim_status": claim.get("status"),
                "failure_reason": claim.get("failure_reason"),
            },
        ),
        "E-HG5_forbidden_key_audit": _gate(
            "E-HG5_forbidden_key_audit",
            not forbidden_paths,
            "residualized attribution claim contains no terminal verdict, host env, raw candidate body, records, or raw payload keys",
            {
                "forbidden_keys": list(RESIDUALIZED_ATTRIBUTION_CLAIM_FORBIDDEN_KEYS),
                "forbidden_text": list(RESIDUALIZED_ATTRIBUTION_CLAIM_FORBIDDEN_TEXT),
                "forbidden_paths": forbidden_paths,
            },
        ),
        "E-HG6_committed_round_trip": _gate(
            "E-HG6_committed_round_trip",
            False,
            "committed JSON reload validates slot set, pointer resolution, and forbidden-key audit",
            {"deferred_until": "committed_json_reload"},
        ),
    }
    failed = [name for name, gate in gates.items() if gate["status"] != "pass"]
    return {
        "status": "pass" if not failed else "fail",
        "pointer": _capsule_pointer("$.e_hardgates"),
        "gates": gates,
        "failed_gate": failed[0] if failed else None,
    }


def validate_residualized_attribution_claim(payload: Mapping[str, Any]) -> list[str]:
    claim = payload.get("residualized_attribution_claim")
    hardgates = payload.get("e_hardgates")
    failures: list[str] = []
    if not isinstance(claim, Mapping):
        return ["missing residualized_attribution_claim"]
    if not isinstance(hardgates, Mapping):
        failures.append("missing e_hardgates")
    if not _residualized_claim_slot_set_ok(claim):
        failures.append("slot set mismatch")
    unresolved = [
        pointer
        for pointer in _residualized_claim_pointers(claim)
        if _resolve_artifact_pointer_in_capsule(payload, pointer) is None
    ]
    if unresolved:
        failures.append(f"unresolved pointers: {unresolved}")
    forbidden_paths = _forbidden_key_paths(claim)
    if forbidden_paths:
        failures.append(f"forbidden paths: {forbidden_paths}")
    return failures


def _artifact_pointer_cell(pointer: str | None) -> tuple[str, str] | None:
    if not isinstance(pointer, str) or ":$" not in pointer:
        return None
    artifact, json_pointer = pointer.split(":", 1)
    if artifact != CANONICAL_JSON_ARTIFACT or not json_pointer.startswith("$"):
        return None
    return artifact, json_pointer


def _capsule_pointer_resolves(payload: Mapping[str, Any], pointer: str | None) -> bool:
    cell = _artifact_pointer_cell(pointer)
    if cell is None:
        return False
    return _resolve_payload_pointer(payload, cell[1]) is not None


def _head_patch_mode_present(evidence: Mapping[str, Any], mode: str) -> bool:
    arm = evidence.get(mode)
    if not isinstance(arm, Mapping):
        return False
    per_seed = arm.get("per_seed_before_after_metrics")
    ci = arm.get("ci_summaries")
    return isinstance(per_seed, list) and bool(per_seed) and isinstance(ci, Mapping) and bool(ci)


def _head_patch_required_modes_ok(evidence: Mapping[str, Any]) -> bool:
    return all(_head_patch_mode_present(evidence, mode) for mode in HEAD_PATCH_REQUIRED_MODES)


def _head_patch_claim_pointer_slots() -> list[dict[str, str]]:
    slots: list[dict[str, str]] = []
    for mode in HEAD_PATCH_REQUIRED_MODES:
        slots.extend(
            [
                {
                    "slot": f"{mode}_arm",
                    "source_pointer": _capsule_pointer(f"$.head_channel_patch_evidence.{mode}"),
                },
                {
                    "slot": f"{mode}_auroc_delta_ci_high",
                    "source_pointer": _capsule_pointer(
                        f"$.head_channel_patch_evidence.{mode}.ci_summaries.AUROC_after_minus_before.ci95_high"
                    ),
                },
                {
                    "slot": f"{mode}_touched_column_audit",
                    "source_pointer": _capsule_pointer(
                        f"$.head_channel_patch_evidence.{mode}.per_seed_before_after_metrics[0].audit.touched_column_audit.status"
                    ),
                },
            ]
        )
    slots.extend(
        [
            {
                "slot": "paired_deltas",
                "source_pointer": _capsule_pointer("$.head_channel_patch_evidence.paired_deltas"),
            },
            {
                "slot": "gate_status",
                "source_pointer": _capsule_pointer("$.head_channel_patch_evidence.gate_status"),
            },
        ]
    )
    return slots


def _head_patch_claim_forbidden_paths(payload: Any, *, path: str = "$") -> list[str]:
    paths: list[str] = []
    if isinstance(payload, Mapping):
        for key, value in payload.items():
            key_path = f"{path}.{key}"
            if key in HEAD_CHANNEL_PATCH_CLAIM_FORBIDDEN_KEYS:
                paths.append(key_path)
            paths.extend(_head_patch_claim_forbidden_paths(value, path=key_path))
    elif isinstance(payload, list):
        for index, value in enumerate(payload):
            paths.extend(_head_patch_claim_forbidden_paths(value, path=f"{path}.{index}"))
    elif isinstance(payload, str):
        for forbidden in RESIDUALIZED_ATTRIBUTION_CLAIM_FORBIDDEN_TEXT:
            if forbidden in payload:
                paths.append(path)
                break
    return paths


def _head_patch_causal_claim(evidence: Mapping[str, Any]) -> dict[str, Any]:
    required_modes = _head_patch_required_modes_ok(evidence)
    protocol = evidence.get("protocol_checks", {})
    allowed = (
        evidence.get("status") == "pass"
        and evidence.get("gate_status") == "pass"
        and required_modes
        and isinstance(protocol, Mapping)
        and all(protocol.get(name) is True for name in ("present", "deterministic", "finite", "seed_paired", "column_audited", "eval_only_patch"))
    )
    return {
        "status": "pass" if allowed else "fail",
        "source_artifact": CANONICAL_JSON_ARTIFACT,
        "required_modes": list(HEAD_PATCH_REQUIRED_MODES),
        "mode_slots_present": {
            mode: _head_patch_mode_present(evidence, mode)
            for mode in HEAD_PATCH_REQUIRED_MODES
        },
        "pointer_slots": _head_patch_claim_pointer_slots(),
        "h_causal_supported": bool(allowed),
        "failure_reason": None if allowed else "head-causal-patch-claim-blocked",
    }


def _head_patch_claim_pointers(claim: Mapping[str, Any]) -> list[str]:
    pointers: list[str] = []
    for slot in claim.get("pointer_slots", []):
        if not isinstance(slot, Mapping):
            continue
        pointer = slot.get("source_pointer")
        if isinstance(pointer, str):
            pointers.append(pointer)
    return pointers


def validate_head_channel_patch_evidence(payload: Mapping[str, Any]) -> list[str]:
    evidence = payload.get("head_channel_patch_evidence")
    failures: list[str] = []
    if not isinstance(evidence, Mapping):
        return ["missing head_channel_patch_evidence"]
    claim = evidence.get("causal_patch_claim")
    if not isinstance(claim, Mapping):
        failures.append("missing causal_patch_claim")
    if not _head_patch_required_modes_ok(evidence):
        failures.append("required variant arm missing")
    protocol = evidence.get("protocol_checks")
    if not isinstance(protocol, Mapping) or any(
        protocol.get(name) is not True
        for name in ("present", "deterministic", "finite", "seed_paired", "column_audited", "eval_only_patch", "required_modes_present")
    ):
        failures.append("protocol check failure")
    if evidence.get("status") != "pass" or evidence.get("gate_status") != "pass":
        failures.append("head causal patch gate failure")
    if isinstance(claim, Mapping):
        unresolved = [
            pointer
            for pointer in _head_patch_claim_pointers(claim)
            if not _capsule_pointer_resolves(payload, pointer)
        ]
        if unresolved:
            failures.append(f"unresolved pointers: {unresolved}")
        forbidden_paths = _head_patch_claim_forbidden_paths(claim)
        if forbidden_paths:
            failures.append(f"forbidden paths: {forbidden_paths}")
        if claim.get("h_causal_supported") is not True:
            failures.append("h causal support is fail-closed")
    return failures


def _finalize_head_channel_patch_evidence(payload: Mapping[str, Any]) -> dict[str, Any]:
    evidence = dict(payload["head_channel_patch_evidence"])
    claim = _head_patch_causal_claim(evidence)
    evidence["causal_patch_claim"] = claim
    protocol = dict(evidence.get("protocol_checks", {}))
    protocol["required_modes_present"] = _head_patch_required_modes_ok(evidence)
    evidence["protocol_checks"] = protocol
    validation_payload = {**dict(payload), "head_channel_patch_evidence": evidence}
    failures = validate_head_channel_patch_evidence(validation_payload)
    claim = {
        **claim,
        "status": "pass" if not failures else "fail",
        "h_causal_supported": not failures,
        "failure_reason": None if not failures else "head-causal-patch-claim-blocked",
        "validation_failures": failures,
    }
    evidence["causal_patch_claim"] = claim
    if failures:
        evidence["status"] = "fail"
        evidence["gate_status"] = "fail"
        evidence["gate_evidence"] = {
            **dict(evidence.get("gate_evidence", {})),
            "causal_patch_claim": False,
            "validation_failures": failures,
        }
    else:
        evidence["gate_evidence"] = {
            **dict(evidence.get("gate_evidence", {})),
            "causal_patch_claim": True,
            "validation_failures": [],
        }
    return evidence


def _finalize_e_hardgates(payload: Mapping[str, Any]) -> dict[str, Any]:
    hardgates = dict(payload["e_hardgates"])
    gates = {name: dict(gate) for name, gate in hardgates["gates"].items()}
    failures = validate_residualized_attribution_claim(payload)
    unresolved = []
    claim = payload.get("residualized_attribution_claim")
    if isinstance(claim, Mapping):
        unresolved = [
            pointer
            for pointer in _residualized_claim_pointers(claim)
            if _resolve_artifact_pointer_in_capsule(payload, pointer) is None
        ]
    gates["E-HG2_pointer_resolution"] = {
        **gates["E-HG2_pointer_resolution"],
        "status": "pass" if not unresolved else "fail",
        "evidence": {
            **gates["E-HG2_pointer_resolution"].get("evidence", {}),
            "pointer_count": len(_residualized_claim_pointers(claim)) if isinstance(claim, Mapping) else 0,
            "unresolved_pointers": unresolved,
        },
    }
    gates["E-HG6_committed_round_trip"] = {
        **gates["E-HG6_committed_round_trip"],
        "status": "pass" if not failures else "fail",
        "evidence": {
            **gates["E-HG6_committed_round_trip"].get("evidence", {}),
            "validation_failures": failures,
        },
    }
    failed = [name for name, gate in gates.items() if gate["status"] != "pass"]
    return {
        **hardgates,
        "status": "pass" if not failed else "fail",
        "gates": gates,
        "failed_gate": failed[0] if failed else None,
    }


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


def _head_patched_eval_features(
    surface: Mapping[str, Any],
    *,
    seed: int,
    mode: str,
) -> tuple[np.ndarray, dict[str, Any]]:
    features = _require_matrix("features", surface["features"]).copy()
    eval_idx = np.asarray(surface["eval_idx"], dtype=np.int64)
    columns = list(surface["feature_columns"])
    roots = [column.split(":", 1)[0] for column in columns]
    h_indices = [index for index, root in enumerate(roots) if root == "h"]
    if not h_indices:
        raise ValueError("h columns are required")
    before = features.copy()
    if mode == "null_head":
        features[np.ix_(eval_idx, h_indices)] = 0.0
        protocol = "deterministic_eval_head_null_patch"
        seed_salt = None
    elif mode == "permute_head_rows":
        seed_salt = HEAD_PATCH_PERMUTE_SALT
        rng = np.random.default_rng(int(seed) + seed_salt)
        order = rng.permutation(eval_idx)
        features[np.ix_(eval_idx, h_indices)] = before[np.ix_(order, h_indices)]
        protocol = "seed_deterministic_eval_head_row_permutation"
    else:
        raise ValueError(f"unknown head patch mode: {mode}")
    changed = np.abs(features - before) > 1.0e-12
    train_changed = bool(np.any(changed[np.asarray(surface["train_idx"], dtype=np.int64), :]))
    eval_changed = bool(np.any(changed[eval_idx, :]))
    touched_columns = [columns[index] for index, value in enumerate(np.any(changed, axis=0)) if value]
    touched_roots = sorted({column.split(":", 1)[0] for column in touched_columns})
    audit_pass = bool(eval_changed and not train_changed and touched_columns and set(touched_roots).issubset({"h"}))
    return features.astype(np.float64), {
        "mode": mode,
        "seed_salt": seed_salt,
        "protocol": protocol,
        "touched_column_audit": {
            "status": "pass" if audit_pass else "fail",
            "allowed_roots": ["h"],
            "touched_roots": touched_roots,
            "touched_columns": touched_columns,
            "unchanged_non_h_columns": bool(set(touched_roots).issubset({"h"})),
            "train_features_unchanged": not train_changed,
            "eval_features_changed": eval_changed,
        },
    }


def _head_patch_metrics_for_features(
    *,
    arm: str,
    train_features: np.ndarray,
    eval_features: np.ndarray,
    surface: Mapping[str, Any],
) -> dict[str, Any]:
    train_idx = surface["train_idx"]
    eval_idx = surface["eval_idx"]
    labels = _require_matrix("gap_labels", surface["gap_labels"])
    eval_labels = labels[eval_idx]
    eval_error = np.asarray(surface["prediction_error"], dtype=np.float64)[eval_idx]
    heads = _fit_gap_head(train_features[train_idx], labels[train_idx])
    probabilities = _predict_gap_head(heads, eval_features[eval_idx])
    return _metric_projection(
        _metrics_for_arm(
            arm=arm,
            probabilities=probabilities,
            labels=eval_labels,
            prediction_error=eval_error,
        )
    )


def _head_channel_patch_records(config: GapHeadRunConfig) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    for seed_index, seed in enumerate(config.seeds):
        surface = _surface_for_seed(seed=int(seed), config=config)
        base_features = _require_matrix("features", surface["features"])
        before = _head_patch_metrics_for_features(
            arm="head_patch_before",
            train_features=base_features,
            eval_features=base_features,
            surface=surface,
        )
        per_seed: dict[str, Any] = {
            "seed": int(seed),
            "seed_index": int(seed_index),
            "before_metrics": before,
            "after_metrics": {},
            "audits": {},
            "deltas": {},
        }
        for mode in HEAD_PATCH_REQUIRED_MODES:
            changed, audit = _head_patched_eval_features(surface, seed=int(seed), mode=mode)
            after = _head_patch_metrics_for_features(
                arm=mode,
                train_features=base_features,
                eval_features=changed,
                surface=surface,
            )
            per_seed["after_metrics"][mode] = after
            per_seed["audits"][mode] = audit
            per_seed["deltas"][mode] = {
                "AUROC_after_minus_before": float(after["AUROC"]["value"] - before["AUROC"]["value"]),
                "UER_after_minus_before": float(after["UnloggedErrorRate"] - before["UnloggedErrorRate"]),
                "UER_reduction_after_minus_before": float(before["UnloggedErrorRate"] - after["UnloggedErrorRate"]),
            }
        records.append(per_seed)
    return records


def _head_channel_patch_evidence(config: GapHeadRunConfig) -> dict[str, Any]:
    records = _head_channel_patch_records(config)
    modes = HEAD_PATCH_REQUIRED_MODES
    finite = all(
        math.isfinite(float(record["before_metrics"]["AUROC"]["value"]))
        and all(math.isfinite(float(record["after_metrics"][mode]["AUROC"]["value"])) for mode in modes)
        for record in records
    )
    audit_pass = all(record["audits"][mode]["touched_column_audit"]["status"] == "pass" for record in records for mode in modes)
    deterministic = True
    required_modes_present = all(set(record["after_metrics"]) == set(modes) for record in records)
    seed_paired = required_modes_present
    ci_summaries = {
        mode: {
            "AUROC_after_minus_before": metric_stats(record["deltas"][mode]["AUROC_after_minus_before"] for record in records),
            "UER_after_minus_before": metric_stats(record["deltas"][mode]["UER_after_minus_before"] for record in records),
            "UER_reduction_after_minus_before": metric_stats(record["deltas"][mode]["UER_reduction_after_minus_before"] for record in records),
        }
        for mode in modes
    }
    auroc_drop = all(float(ci_summaries[mode]["AUROC_after_minus_before"]["ci95_high"]) < -0.02 for mode in modes)
    uer_not_improved = all(float(ci_summaries[mode]["UER_after_minus_before"]["ci95_low"]) >= 0.0 for mode in modes)
    status = "pass" if finite and audit_pass and deterministic and seed_paired else "fail"
    gate_status = "pass" if status == "pass" and auroc_drop and uer_not_improved else "fail"
    evidence = {
        "status": status,
        "gate_status": gate_status,
        "pointer": "reports/canonical/gap_head_attribution_capsule.json:$.head_channel_patch_evidence",
        "deterministic_salts": {
            "null_head": None,
            "permute_head_rows": HEAD_PATCH_PERMUTE_SALT,
        },
        "null_head": {
            "protocol": "deterministic_eval_head_null_patch",
            "per_seed_before_after_metrics": [
                {
                    "seed": int(record["seed"]),
                    "before": record["before_metrics"],
                    "after": record["after_metrics"]["null_head"],
                    "delta": record["deltas"]["null_head"],
                    "audit": record["audits"]["null_head"],
                }
                for record in records
            ],
            "ci_summaries": ci_summaries["null_head"],
        },
        "permute_head_rows": {
            "protocol": "seed_deterministic_eval_head_row_permutation",
            "per_seed_before_after_metrics": [
                {
                    "seed": int(record["seed"]),
                    "before": record["before_metrics"],
                    "after": record["after_metrics"]["permute_head_rows"],
                    "delta": record["deltas"]["permute_head_rows"],
                    "audit": record["audits"]["permute_head_rows"],
                }
                for record in records
            ],
            "ci_summaries": ci_summaries["permute_head_rows"],
        },
        "paired_deltas": [
            {
                "seed": int(record["seed"]),
                "same_seed": True,
                "same_full_arm_fit_path": True,
                "same_metric_set": True,
                "null_head": record["deltas"]["null_head"],
                "permute_head_rows": record["deltas"]["permute_head_rows"],
            }
            for record in records
        ],
        "protocol_checks": {
            "present": True,
            "deterministic": deterministic,
            "finite": finite,
            "seed_paired": seed_paired,
            "column_audited": audit_pass,
            "eval_only_patch": audit_pass,
            "required_modes_present": required_modes_present,
        },
        "gate_criterion": "both head patches have AUROC delta CI-high < -0.02 and UER delta CI-low >= 0.0",
        "gate_evidence": {
            "auroc_drop": auroc_drop,
            "uer_not_improved": uer_not_improved,
        },
        "ci_summaries": ci_summaries,
    }
    evidence["causal_patch_claim"] = _head_patch_causal_claim(evidence)
    return evidence


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
    head_channel_patch_evidence: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    head_channel_patch_evidence = {} if head_channel_patch_evidence is None else head_channel_patch_evidence
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
    head_protocol = head_channel_patch_evidence.get("protocol_checks", {})
    head_causal_patch_claim_pointer = _capsule_pointer(HEAD_CAUSAL_PATCH_CLAIM_JSON_PATH)
    head_causal_patch_claim = _resolve_artifact_pointer_in_capsule(
        {"head_channel_patch_evidence": head_channel_patch_evidence},
        head_causal_patch_claim_pointer,
    )
    head_causal_patch_claim_resolved = isinstance(head_causal_patch_claim, Mapping)
    head_causal_patch = (
        head_channel_patch_evidence.get("status") == "pass"
        and head_channel_patch_evidence.get("gate_status") == "pass"
        and head_causal_patch_claim_resolved
        and head_causal_patch_claim.get("h_causal_supported") is True
        and _head_patch_required_modes_ok(head_channel_patch_evidence)
        and all(head_protocol.get(name) is True for name in ("present", "deterministic", "finite", "seed_paired", "column_audited", "eval_only_patch", "required_modes_present"))
    )
    shortcut_clear = _shortcut_controls_clear(aggregate)
    hg5 = (
        hg1
        and hg2
        and hg3
        and hg4
        and head_causal_patch
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
        "head_causal_patch": _gate(
            "head_causal_patch",
            head_causal_patch,
            "head patch protocol is present, deterministic, finite, paired, eval-only, column-audited, and degrades AUROC without improving UER",
            {
                "protocol_checks": dict(head_protocol),
                "gate_status": head_channel_patch_evidence.get("gate_status"),
                "gate_evidence": head_channel_patch_evidence.get("gate_evidence", {}),
                "causal_patch_claim_pointer": head_causal_patch_claim_pointer,
                "causal_patch_claim_pointer_resolved": head_causal_patch_claim_resolved,
                "causal_objects": [
                    "$.head_channel_patch_evidence.null_head",
                    "$.head_channel_patch_evidence.permute_head_rows",
                    "$.head_channel_patch_evidence.paired_deltas",
                    "$.head_channel_patch_evidence.gate_status",
                    "$.head_channel_patch_evidence.causal_patch_claim",
                ],
            },
        ),
        "A4-HG5": _gate(
            "A4-HG5",
            hg5,
            "A4-HG1 through A4-HG4 and head_causal_patch pass, score/margin is not sufficient, and shortcut controls are not sufficient competitors",
            {
                "required_gates": ["A4-HG1", "A4-HG2", "A4-HG3", "A4-HG4", "head_causal_patch"],
                "channel_classification": score_margin_causal_evidence.get("channel_classification"),
                "shortcut_controls_clear": shortcut_clear,
                "head_causal_patch_status": "pass" if head_causal_patch else "fail",
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


def _d5_o(aggregate: Mapping[str, Any], ledger: GapHeadD5ReadinessLedger | None = None) -> dict[str, Any]:
    readiness = GapHeadOperationalReadinessPolicy().criteria(_gap_head_d5_context()) if ledger is None else ledger
    criterion_pointers = {
        criterion.name: f"{criterion.artifact}:{criterion.pointer}" if criterion.pointer is not None else criterion.artifact
        for criterion in readiness.criteria
    }
    if not readiness.all_pass:
        return {
            "status": "blocked",
            "claim": "D5-O operational readiness is blocked by canonical readiness criteria.",
            "source_pointer": "reports/canonical/gap-head-on-h.json",
            "A1_capsule_arm_count": int(len(aggregate["arm_order"])),
            "failed_checks": readiness.failed_checks(),
            "criterion_pointers": criterion_pointers,
            "readiness": readiness.as_dict(),
        }
    return {
        "status": "ready",
        "claim": "D5-O robust operational pointer retained from canonical gap-head-on-h evidence.",
        "source_pointer": "reports/canonical/gap-head-on-h.json",
        "A1_capsule_arm_count": int(len(aggregate["arm_order"])),
        "failed_checks": [],
        "criterion_pointers": criterion_pointers,
        "readiness": readiness.as_dict(),
    }


def _d5_m(hardgates: Mapping[str, Any], a4_hardgates: Mapping[str, Any] | None = None) -> dict[str, Any]:
    a1_passed = hardgates["gates"]["A1-HG6"]["status"] == "pass"
    a4_gates = (a4_hardgates or {}).get("gates", {})
    a4_passed = (
        a4_hardgates is not None
        and a4_gates.get("head_causal_patch", {}).get("status") == "pass"
        and a4_gates.get("A4-HG5", {}).get("status") == "pass"
    )
    passed = a1_passed and a4_passed
    failed_gate = None
    if not a1_passed:
        failed_gate = hardgates["failed_gate"] or "A1-HG6"
    elif not a4_passed:
        failed_gate = (a4_hardgates or {}).get("failed_gate") or "A4-HG5"
    return {
        "status": "ready" if passed else "blocked",
        "passed": bool(passed),
        "requires": [
            "A1-HG1",
            "A1-HG2",
            "A1-HG3",
            "A1-HG4",
            "A1-HG5",
            "A1-HG6",
            "A4-HG1",
            "A4-HG2",
            "A4-HG3",
            "A4-HG4",
            "head_causal_patch",
            "A4-HG5",
        ],
        "failed_gate": failed_gate,
    }


def _mechanism_evidence(
    d5_o: Mapping[str, Any],
    d5_m: Mapping[str, Any],
    mechanism_case: Mapping[str, Any],
    a4_hardgates: Mapping[str, Any],
    residualized_attribution: Mapping[str, Any],
    score_margin_causal_evidence: Mapping[str, Any],
    head_channel_patch_evidence: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    head_channel_patch_evidence = {} if head_channel_patch_evidence is None else head_channel_patch_evidence
    a4_gates = a4_hardgates.get("gates", {})
    required_gate_pointers = [
        "$.a4_hardgates.gates.A4-HG2.status",
        "$.a4_hardgates.gates.A4-HG3.status",
        "$.a4_hardgates.gates.head_causal_patch.status",
        "$.a4_hardgates.gates.A4-HG5.status",
    ]
    residualized_significant = all(
        isinstance(a4_gates, Mapping)
        and isinstance(a4_gates.get(name), Mapping)
        and a4_gates[name].get("status") == "pass"
        for name in ("A4-HG2", "A4-HG3")
    )
    shortcut_controls = (
        a4_gates.get("A4-HG5", {}).get("evidence", {}).get("shortcut_controls_clear", {})
        if isinstance(a4_gates, Mapping) and isinstance(a4_gates.get("A4-HG5"), Mapping)
        else {}
    )
    control_clear = isinstance(shortcut_controls, Mapping) and bool(shortcut_controls) and all(shortcut_controls.values())
    classification = score_margin_causal_evidence.get("channel_classification")
    mechanism_level = "D5-M" if d5_m.get("status") == "ready" and d5_m.get("passed") is True else "blocked"
    mechanism_status = "ready" if mechanism_level == "D5-M" else "blocked"
    base_ready = d5_o.get("status") == "ready"
    return {
        "evidence_level": "patch",
        "base_level": "D5-O" if base_ready else "blocked",
        "base_status": str(d5_o.get("status") or "missing"),
        "mechanism_level": mechanism_level,
        "mechanism_status": mechanism_status,
        "candidate_mechanism": str(mechanism_case.get("candidate_mechanism") or "unresolved"),
        "failed_gate": d5_m.get("failed_gate") or mechanism_case.get("failed_gate") or a4_hardgates.get("failed_gate"),
        "residualized_significant": bool(residualized_attribution.get("status") == "pass" and residualized_significant),
        "control_clear": bool(control_clear),
        "score_margin_sufficient": classification == "score_margin_sufficient",
        "required_gate_pointers": required_gate_pointers,
        "metric_pointers": {
            "residualized_status": "$.residualized_attribution.status",
            "residualized_full_auroc": "$.residualized_attribution.ci_summaries.full_residualized_against_score_margin.AUROC.mean",
            "residualized_without_score_margin_auroc": "$.residualized_attribution.ci_summaries.full_without_score_and_margin.AUROC.mean",
            "score_margin_channel_classification": "$.score_margin_causal_evidence.channel_classification",
            "shuffle_score_margin_delta": "$.score_margin_causal_evidence.shuffle_score_margin.ci_summaries.AUROC_after_minus_before.mean",
            "replacement_control_delta": "$.score_margin_causal_evidence.replace_high_gap_score_margin_from_low_gap.ci_summaries.AUROC_after_minus_before.mean",
            "head_patch_status": "$.head_channel_patch_evidence.gate_status",
            "head_patch_delta": "$.head_channel_patch_evidence.null_head.ci_summaries.AUROC_after_minus_before.mean",
        },
        "ledger_debt_pointer": "$.ledger_debt.0.status",
        "closure_pointer": "$.mechanism_evidence.mechanism_status",
        "head_patch_status": str(head_channel_patch_evidence.get("gate_status") or "missing"),
        "head_patch_delta": (
            head_channel_patch_evidence.get("null_head", {})
            .get("ci_summaries", {})
            .get("AUROC_after_minus_before", {})
            .get("mean")
        ),
        "source_issue": 750,
        "source_issues": [747, 750],
    }


def _ledger_debt(mechanism_evidence: Mapping[str, Any]) -> list[dict[str, Any]]:
    mechanism_closed = mechanism_evidence.get("mechanism_level") == "D5-M" and mechanism_evidence.get("mechanism_status") == "ready"
    failed_gate = mechanism_evidence.get("failed_gate")
    return [
        {
            "debt_id": "gap-head-mechanism-evidence-closure",
            "status": "closed" if mechanism_closed else "open",
            "owner_pointer": "$.mechanism_evidence",
            "evidence_pointer": f"$.a4_hardgates.gates.{failed_gate}" if isinstance(failed_gate, str) and failed_gate.startswith("A4-") else "$.mechanism_evidence",
        },
        {
            "debt_id": "nonlinear-residualization-boundary",
            "status": "open",
            "owner_pointer": "$.not_implemented.0",
            "evidence_pointer": "$.residualized_attribution",
        },
        {
            "debt_id": "full-causal-replacement-boundary",
            "status": "open",
            "owner_pointer": "$.not_implemented.1",
            "evidence_pointer": "$.score_margin_causal_evidence",
        },
    ]


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
    if pointer == "$":
        return payload
    if pointer is None or not pointer.startswith("$."):
        return None
    return pointer_value(payload, pointer)


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


def _a1_negative_witness_owner_ref(run_id: str) -> dict[str, str]:
    return {
        "artifact": f"{RUNS_DIR}/{run_id}/claim_capsule.json",
        "pointer": A1_NEGATIVE_WITNESS_OWNER_POINTER,
    }


def _a1_negative_witness_row(capsule_artifact: str, capsule: Mapping[str, Any], *, status: str = "fail", reason: str | None = None) -> dict[str, Any]:
    return {
        "witness_id": "a1-hg3-score-plus-margin-competitive",
        "source_artifact": capsule_artifact,
        "source_pointer": "$.hardgates.gates.A1-HG3",
        "bedc_gap_field": "d5_m.failed_gate",
        "demotion_rule": "block D5-M while A1-HG3 fails",
        "regression_test": A1_NEGATIVE_WITNESS_REGRESSION_TEST,
        "evidence_pointer": "$.hardgates.gates.A1-HG3",
        "status": status,
        "reason": reason
        or (
            "A1-HG3 failed because full AUROC CI-low does not exceed the score_plus_margin AUROC "
            "CI-high control; D5-M remains blocked."
        ),
    }


def _source_payload_for_artifact(capsule: Mapping[str, Any], artifact: str, capsule_artifact: str) -> Mapping[str, Any] | None:
    if artifact == capsule_artifact:
        return capsule
    path = ROOT / artifact
    if not path.exists():
        return None
    try:
        loaded = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return None
    return loaded if isinstance(loaded, Mapping) else None


def _artifact_pointer_value(capsule: Mapping[str, Any], artifact_pointer: str, capsule_artifact: str) -> Any:
    if artifact_pointer.startswith("$."):
        artifact = capsule_artifact
        pointer = artifact_pointer
    elif ":$" in artifact_pointer:
        artifact, pointer = artifact_pointer.split(":", 1)
    else:
        return None
    source_payload = _source_payload_for_artifact(capsule, artifact, capsule_artifact)
    if source_payload is None:
        return None
    return _resolve_payload_pointer(source_payload, pointer)


def _regression_test_resolves(nodeid: str) -> bool:
    if "::" not in nodeid:
        return False
    test_file, test_name = nodeid.split("::", 1)
    path = ROOT / test_file
    return path.exists() and f"def {test_name}" in path.read_text(encoding="utf-8")


def _a1_negative_witness_pointer_status(capsule: Mapping[str, Any], row: Mapping[str, Any]) -> tuple[str, dict[str, Any]]:
    capsule_artifact = str(row.get("source_artifact", ""))
    source_payload = _source_payload_for_artifact(capsule, capsule_artifact, capsule_artifact)
    source_value = None if source_payload is None else _resolve_payload_pointer(source_payload, str(row.get("source_pointer", "")))
    evidence_value = _artifact_pointer_value(capsule, str(row.get("evidence_pointer", "")), capsule_artifact)
    regression_resolved = _regression_test_resolves(str(row.get("regression_test", "")))
    checks = {
        "source_artifact": capsule_artifact,
        "source_pointer": row.get("source_pointer"),
        "source_pointer_resolved": source_value is not None,
        "source_pointer_value": source_value,
        "source_pointer_status": source_value.get("status") if isinstance(source_value, Mapping) else None,
        "source_pointer_name": source_value.get("name") if isinstance(source_value, Mapping) else None,
        "evidence_pointer": row.get("evidence_pointer"),
        "evidence_pointer_resolved": evidence_value is not None,
        "evidence_pointer_status": evidence_value.get("status") if isinstance(evidence_value, Mapping) else None,
        "evidence_pointer_name": evidence_value.get("name") if isinstance(evidence_value, Mapping) else None,
        "regression_test": row.get("regression_test"),
        "regression_test_resolved": regression_resolved,
    }
    missing = []
    if source_payload is None:
        missing.append(f"unresolved artifact {capsule_artifact}")
    if source_value is None:
        missing.append(f"unresolved pointer {capsule_artifact}:{row.get('source_pointer')}")
    if evidence_value is None:
        missing.append(f"unresolved pointer {row.get('evidence_pointer')}")
    if not regression_resolved:
        missing.append(f"unresolved regression test {row.get('regression_test')}")
    return "; ".join(missing), checks


def _contains_key_recursive(payload: Any, forbidden: str) -> bool:
    if isinstance(payload, Mapping):
        return forbidden in payload or any(_contains_key_recursive(value, forbidden) for value in payload.values())
    if isinstance(payload, list):
        return any(_contains_key_recursive(value, forbidden) for value in payload)
    return False


def _a1_negative_witness_hardgates(capsule: Mapping[str, Any], row: Mapping[str, Any]) -> dict[str, Any]:
    capsule_artifact = str(row.get("source_artifact", ""))
    _, checks = _a1_negative_witness_pointer_status(capsule, row)
    source = checks.get("source_pointer_value")
    source_ok = (
        checks.get("source_pointer_resolved") is True
        and isinstance(source, Mapping)
        and source.get("name") == "A1-HG3"
    )
    evidence = _artifact_pointer_value(capsule, str(row.get("evidence_pointer", "")), capsule_artifact)
    evidence_ok = (
        isinstance(evidence, Mapping)
        and evidence.get("status") == "fail"
        and evidence.get("criterion") == "full AUROC CI-low > score_plus_margin AUROC CI-high"
        and float(evidence.get("evidence", {}).get("full_ci_low", math.nan))
        < float(evidence.get("evidence", {}).get("score_plus_margin_ci_high", math.nan))
    )
    row_shape_ok = isinstance(row, Mapping) and tuple(row.keys()) == A1_NEGATIVE_WITNESS_KEYS
    negative_witness = capsule.get("run_local", {}).get("negative_witness") if isinstance(capsule.get("run_local"), Mapping) else None
    list_shape_ok = isinstance(negative_witness, list) and len(negative_witness) == 1
    regression_ok = checks.get("regression_test_resolved") is True
    terminal_clean = not _contains_key_recursive(
        {
            "negative_witness": negative_witness,
            "negative_witness_hardgates": (
                capsule.get("run_local", {}).get("negative_witness_hardgates")
                if isinstance(capsule.get("run_local"), Mapping)
                else None
            ),
        },
        "terminal_verdict",
    )
    gates = {
        "NW-HG1": {
            "status": "pass" if row_shape_ok and list_shape_ok else "fail",
            "evidence_pointer": "$.run_local.negative_witness[0]",
            "row_shape_ok": row_shape_ok,
            "list_shape_ok": list_shape_ok,
            "row_keys": list(row.keys()) if isinstance(row, Mapping) else [],
        },
        "NW-HG2": {
            "status": "pass" if source_ok else "fail",
            "evidence_pointer": row.get("source_pointer"),
            "source_pointer_resolved": checks.get("source_pointer_resolved"),
            "source_pointer_name": checks.get("source_pointer_name"),
            "source_pointer_status": checks.get("source_pointer_status"),
        },
        "NW-HG3": {
            "status": "pass" if evidence_ok else "fail",
            "evidence_pointer": row.get("evidence_pointer"),
            "evidence_pointer_resolved": checks.get("evidence_pointer_resolved"),
            "evidence_pointer_name": checks.get("evidence_pointer_name"),
            "evidence_pointer_status": checks.get("evidence_pointer_status"),
        },
        "NW-HG4": {
            "status": "pass" if regression_ok else "fail",
            "evidence_pointer": "$.run_local.negative_witness[0].regression_test",
            "regression_test": row.get("regression_test"),
            "regression_test_resolved": regression_ok,
        },
        "NW-HG5": {
            "status": "pass" if terminal_clean else "fail",
            "evidence_pointer": "$.run_local",
            "forbidden_key_absent": terminal_clean,
        },
    }
    failed = [name for name, gate in gates.items() if gate["status"] != "pass"]
    return {
        "status": "pass" if not failed else "fail",
        "failed_gates": failed,
        "gates": gates,
    }


def _a1_negative_witness_run_local(capsule: Mapping[str, Any], *, run_id: str) -> dict[str, Any]:
    capsule_artifact = f"{RUNS_DIR}/{run_id}/claim_capsule.json"
    row = _a1_negative_witness_row(capsule_artifact, capsule)
    reason, checks = _a1_negative_witness_pointer_status(capsule, row)
    expected_fail_ok = (
        checks.get("source_pointer_name") == "A1-HG3"
        and checks.get("source_pointer_status") == "fail"
        and checks.get("evidence_pointer_name") == "A1-HG3"
        and checks.get("evidence_pointer_status") == "fail"
        and checks.get("regression_test_resolved") is True
    )
    if reason or not expected_fail_ok:
        reason = reason or "A1-HG3 source and evidence pointers did not resolve to the expected failed gate."
        row = _a1_negative_witness_row(capsule_artifact, capsule, status="blocked", reason=reason)
    run_local = {"negative_witness": [row]}
    probe = {**dict(capsule), "run_local": run_local}
    run_local["negative_witness_hardgates"] = _a1_negative_witness_hardgates(probe, row)
    return run_local


def _attach_run_local_negative_witness(capsule: Mapping[str, Any], *, run_id: str) -> dict[str, Any]:
    finalized = dict(capsule)
    if run_id != "a1-canonical":
        return finalized
    finalized["run_local"] = _a1_negative_witness_run_local(finalized, run_id=run_id)
    return finalized


def _public_negative_witness_projection(payload: Mapping[str, Any], *, run_id: str) -> dict[str, Any]:
    projected = dict(payload)
    if run_id != "a1-canonical":
        return projected
    owner_ref = _a1_negative_witness_owner_ref(run_id)
    hardgates_ref = {
        "artifact": f"{RUNS_DIR}/{run_id}/claim_capsule.json",
        "pointer": "$.run_local.negative_witness_hardgates",
    }
    if "run_local" in projected:
        run_local = dict(projected["run_local"]) if isinstance(projected["run_local"], Mapping) else {}
        run_local["negative_witness"] = [owner_ref]
        run_local["negative_witness_hardgates"] = hardgates_ref
        projected["run_local"] = run_local
    else:
        projected["negative_witness"] = [owner_ref]
        projected["negative_witness_hardgates"] = hardgates_ref
    return projected


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
        "source_issues": list(SOURCE_ISSUES),
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
        "dgt_neural_ablation_pointers": dict(DGT_NEURAL_ABLATION_POINTERS),
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
    head_channel_patch_evidence = _head_channel_patch_evidence(config)
    a4_hardgates = _a4_hardgates(aggregate, residualized_attribution, score_margin_causal_evidence, head_channel_patch_evidence)
    mechanism_case = _mechanism_case(aggregate, hardgates, a4_hardgates, score_margin_causal_evidence)
    columns_by_arm = {
        arm: next(record["feature_columns"] for record in records if record["arm"] == arm)
        for arm in ARM_NAMES
    }
    forbidden_audit = _forbidden_column_audit(columns_by_arm)
    d5_m = _d5_m(hardgates, a4_hardgates)
    d5_readiness = GapHeadOperationalReadinessPolicy().criteria(_gap_head_d5_context())
    d5_o = _d5_o(aggregate, d5_readiness)
    residualized_attribution_claim = _residualized_attribution_claim(
        aggregate,
        residualized_attribution,
        score_margin_causal_evidence,
        a4_hardgates,
    )
    e_hardgates = _e_hardgates(aggregate, residualized_attribution_claim)
    mechanism_evidence = _mechanism_evidence(
        d5_o,
        d5_m,
        mechanism_case,
        a4_hardgates,
        residualized_attribution,
        score_margin_causal_evidence,
        head_channel_patch_evidence,
    )
    source_artifacts = _source_artifacts(config, run_dir)
    capsule: dict[str, Any] = {
        "schema_id": SCHEMA_ID,
        "source_issue": SOURCE_ISSUE,
        "source_issues": list(SOURCE_ISSUES),
        "artifact_id": ARTIFACT_ID,
        "run_id": run_id,
        "generated_at": generated_at,
        "d5_o": d5_o,
        "d5_m": d5_m,
        "mechanism_case": mechanism_case,
        "mechanism_evidence": mechanism_evidence,
        "not_implemented": list(NOT_IMPLEMENTED),
        "ledger_debt": _ledger_debt(mechanism_evidence),
        "hardgates": hardgates,
        "residualized_attribution": residualized_attribution,
        "residualized_attribution_claim": residualized_attribution_claim,
        "e_hardgates": e_hardgates,
        "score_margin_causal_evidence": score_margin_causal_evidence,
        "head_channel_patch_evidence": head_channel_patch_evidence,
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
    lines.extend(["", "## E Hardgates", "", "| gate | status |", "| --- | --- |"])
    for name, gate in payload["e_hardgates"]["gates"].items():
        lines.append(f"| `{name}` | `{gate['status']}` |")
    lines.extend(
        [
            "",
            "## Residualized Attribution Claim",
            "",
            f"- Pointer: `{payload['residualized_attribution_claim']['pointer']}`",
            f"- Non-score mechanism claim allowed: `{payload['residualized_attribution_claim']['non_score_mechanism_claim_allowed']}`",
            f"- E hardgates: `{payload['e_hardgates']['pointer']}`",
        ]
    )
    lines.extend(["", "## Claim Capsule Hardgates", "", "| gate | status |", "| --- | --- |"])
    for name, gate in payload["claim_capsule_hardgates"].items():
        lines.append(f"| `{name}` | `{gate['status']}` |")
    lines.extend(["", "## Scope", ""])
    for item in payload["scope"]["not_claimed"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def _stable_json_payload(payload: Any) -> Any:
    if isinstance(payload, Mapping):
        if tuple(payload.keys()) == A1_NEGATIVE_WITNESS_KEYS:
            return {key: _stable_json_payload(payload[key]) for key in A1_NEGATIVE_WITNESS_KEYS}
        return {key: _stable_json_payload(payload[key]) for key in sorted(payload)}
    if isinstance(payload, list):
        return [_stable_json_payload(item) for item in payload]
    return payload


def _write_json(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(_stable_json_payload(payload), indent=2) + "\n", encoding="utf-8")


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _finalize_claim_state(payload: Mapping[str, Any]) -> dict[str, Any]:
    finalized = dict(payload)
    existing_d5_m = finalized.get("d5_m", {})
    preserve_a1_block = (
        isinstance(existing_d5_m, Mapping)
        and existing_d5_m.get("passed") is False
        and isinstance(existing_d5_m.get("failed_gate"), str)
        and str(existing_d5_m["failed_gate"]).startswith("A1-")
    )
    finalized["head_channel_patch_evidence"] = _finalize_head_channel_patch_evidence(finalized)
    finalized["a4_hardgates"] = _a4_hardgates(
        finalized["aggregate"],
        finalized["residualized_attribution"],
        finalized["score_margin_causal_evidence"],
        finalized["head_channel_patch_evidence"],
    )
    finalized["d5_m"] = dict(existing_d5_m) if preserve_a1_block else _d5_m(finalized["hardgates"], finalized["a4_hardgates"])
    finalized["mechanism_case"] = _mechanism_case(
        finalized["aggregate"],
        finalized["hardgates"],
        finalized["a4_hardgates"],
        finalized["score_margin_causal_evidence"],
    )
    finalized["mechanism_evidence"] = _mechanism_evidence(
        finalized["d5_o"],
        finalized["d5_m"],
        finalized["mechanism_case"],
        finalized["a4_hardgates"],
        finalized["residualized_attribution"],
        finalized["score_margin_causal_evidence"],
        finalized["head_channel_patch_evidence"],
    )
    finalized["ledger_debt"] = _ledger_debt(finalized["mechanism_evidence"])
    finalized["failed_gate"] = finalized["d5_m"]["failed_gate"]
    finalized["what_was_learned"] = finalized["mechanism_case"]["what_was_learned"]
    finalized["revocation_ledger"] = _revocation_ledger(
        finalized["hardgates"],
        str(finalized["generated_at"]),
        finalized["d5_m"],
    )
    finalized["e_hardgates"] = _finalize_e_hardgates(finalized)
    return finalized


def _write_artifacts(payload: Mapping[str, Any], run_dir: Path, *, canonical: bool = True) -> None:
    run_id = str(payload["run_id"])
    payload = _finalize_claim_state(payload)
    claim_capsule = {key: payload[key] for key in (
        "schema_id",
        "source_issue",
        "source_issues",
        "artifact_id",
        "run_id",
        "d5_o",
        "d5_m",
        "mechanism_case",
        "mechanism_evidence",
        "not_implemented",
        "ledger_debt",
        "hardgates",
        "residualized_attribution",
        "residualized_attribution_claim",
        "e_hardgates",
        "score_margin_causal_evidence",
        "head_channel_patch_evidence",
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
    claim_capsule = _attach_run_local_negative_witness(claim_capsule, run_id=run_id)
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
        "source_issues",
        "artifact_id",
        "run_id",
        "generated_at",
        "d5_o",
        "d5_m",
        "mechanism_case",
        "mechanism_evidence",
        "not_implemented",
        "ledger_debt",
        "hardgates",
        "residualized_attribution",
        "residualized_attribution_claim",
        "e_hardgates",
        "score_margin_causal_evidence",
        "head_channel_patch_evidence",
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
    summary = _public_negative_witness_projection(summary, run_id=run_id)
    _write_json(run_dir / "summary.json", summary)
    _write_text(run_dir / "report.md", _render_report(payload))
    if canonical:
        _write_json(ROOT / CANONICAL_JSON_ARTIFACT, summary)
        _write_text(ROOT / CANONICAL_MARKDOWN_ARTIFACT, _render_report(payload))


def _new_run_id() -> str:
    return "a1-canonical"


def _reusable_generated_at(run_id: str) -> str | None:
    summary_path = ROOT / RUNS_DIR / run_id / "summary.json"
    if not summary_path.exists():
        return None
    try:
        payload = json.loads(summary_path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return None
    generated_at = payload.get("generated_at") if isinstance(payload, Mapping) else None
    return generated_at if isinstance(generated_at, str) and generated_at else None


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
    timestamp = generated_at if generated_at is not None else _reusable_generated_at(active_run_id) or datetime.now(timezone.utc).isoformat()
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

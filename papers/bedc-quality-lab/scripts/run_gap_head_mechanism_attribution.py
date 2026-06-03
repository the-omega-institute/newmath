#!/usr/bin/env python3
"""Run fine-grained gap-head mechanism attribution over the learned-h surface."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
import math
from pathlib import Path
import sys
from typing import Any, Sequence

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.experiment_stats import metric_stats
from scripts import run_gap_ledger_head_on_h as producer


JSON_ARTIFACT = "reports/gap_head_mechanism_attribution.json"
REPORT_ARTIFACT = "reports/gap_head_mechanism_attribution.md"
ARTIFACT_ID = "bedc-quality-lab:gap-head-mechanism-attribution"
AUROC_POSITIVE_THRESHOLD = 0.75
AUROC_MARGIN = 0.03
UNLOGGED_REDUCTION_MARGIN = 0.03
ARM_NAMES = (
    "full",
    "h_only",
    "h_direction_only",
    "h_norm_only",
    "h_normalized_no_scale",
    "score_only",
    "margin_only",
    "transition_delta_only",
    "quality_scalars_only",
    "score_plus_margin",
    "h_plus_margin",
    "h_plus_transition",
    "full_without_margin",
    "full_without_transition",
    "full_without_quality_scalars",
    "matched_random",
)
GATING_ARMS = tuple(arm for arm in ARM_NAMES if arm != "h_normalized_no_scale")
SINGLE_CHANNEL_ARMS = (
    "score_only",
    "margin_only",
    "transition_delta_only",
    "quality_scalars_only",
    "h_norm_only",
)
REDUCED_FAMILY_ARMS = (
    "score_plus_margin",
    "h_plus_margin",
    "h_plus_transition",
    "full_without_margin",
    "full_without_transition",
    "full_without_quality_scalars",
)


def _format_float(value: float) -> str:
    if math.isnan(value):
        return "nan"
    return f"{value:.6f}"


def _render_stats(stats: dict[str, Any]) -> str:
    return (
        f"{_format_float(float(stats['mean']))} +/- {_format_float(float(stats['std']))} "
        f"(95% CI +/- {_format_float(float(stats['ci95_half_width']))})"
    )


def _feature_indices(columns: Sequence[str], roots: set[str]) -> list[int]:
    indices = [
        index
        for index, column in enumerate(columns)
        if column.split(":", 1)[0] in roots
    ]
    if not indices:
        raise ValueError(f"feature roots have no columns: {sorted(roots)}")
    return indices


def _row_l2_direction(h: np.ndarray) -> np.ndarray:
    value = producer._require_finite("h", h, ndim=2)
    norms = np.linalg.norm(value, axis=1, keepdims=True)
    return np.divide(value, norms, out=np.zeros_like(value, dtype=np.float64), where=norms > producer.EPS)


def _arm_feature_matrices(surface: dict[str, Any]) -> dict[str, dict[str, Any]]:
    columns = list(surface["feature_columns"])
    producer._assert_inference_columns(columns)
    features = producer._require_finite("features", surface["features"], ndim=2)
    h_indices = _feature_indices(columns, {"h"})
    score_indices = _feature_indices(columns, {"score"})
    margin_indices = _feature_indices(columns, {"margin"})
    transition_indices = _feature_indices(columns, {"transition_delta"})
    quality_indices = _feature_indices(columns, {"quality"})
    h = features[:, h_indices]
    h_direction = _row_l2_direction(h)
    h_direction_columns = [f"h_direction:{index}" for index in range(h_direction.shape[1])]
    h_norm = np.linalg.norm(h, axis=1, keepdims=True).astype(np.float64)
    matrices = {
        "full": {
            "features": features,
            "feature_columns": columns,
            "feature_roots": ["h", "score", "margin", "transition_delta", "quality"],
        },
        "h_only": {
            "features": h,
            "feature_columns": [columns[index] for index in h_indices],
            "feature_roots": ["h"],
        },
        "h_direction_only": {
            "features": h_direction,
            "feature_columns": h_direction_columns,
            "feature_roots": ["h_direction"],
        },
        "h_norm_only": {
            "features": h_norm,
            "feature_columns": ["h_norm:l2"],
            "feature_roots": ["h_norm"],
        },
        "h_normalized_no_scale": {
            "features": h_direction,
            "feature_columns": h_direction_columns,
            "feature_roots": ["h_direction"],
            "alias_of": "h_direction_only",
            "gating_role": "non_gating_alias",
        },
        "score_only": {
            "features": features[:, score_indices],
            "feature_columns": [columns[index] for index in score_indices],
            "feature_roots": ["score"],
        },
        "margin_only": {
            "features": features[:, margin_indices],
            "feature_columns": [columns[index] for index in margin_indices],
            "feature_roots": ["margin"],
        },
        "transition_delta_only": {
            "features": features[:, transition_indices],
            "feature_columns": [columns[index] for index in transition_indices],
            "feature_roots": ["transition_delta"],
        },
        "quality_scalars_only": {
            "features": features[:, quality_indices],
            "feature_columns": [columns[index] for index in quality_indices],
            "feature_roots": ["quality"],
        },
        "score_plus_margin": {
            "features": features[:, score_indices + margin_indices],
            "feature_columns": [columns[index] for index in score_indices + margin_indices],
            "feature_roots": ["score", "margin"],
        },
        "h_plus_margin": {
            "features": features[:, h_indices + margin_indices],
            "feature_columns": [columns[index] for index in h_indices + margin_indices],
            "feature_roots": ["h", "margin"],
        },
        "h_plus_transition": {
            "features": features[:, h_indices + transition_indices],
            "feature_columns": [columns[index] for index in h_indices + transition_indices],
            "feature_roots": ["h", "transition_delta"],
        },
        "full_without_margin": {
            "features": features[:, h_indices + score_indices + transition_indices + quality_indices],
            "feature_columns": [
                columns[index]
                for index in h_indices + score_indices + transition_indices + quality_indices
            ],
            "feature_roots": ["h", "score", "transition_delta", "quality"],
        },
        "full_without_transition": {
            "features": features[:, h_indices + score_indices + margin_indices + quality_indices],
            "feature_columns": [
                columns[index]
                for index in h_indices + score_indices + margin_indices + quality_indices
            ],
            "feature_roots": ["h", "score", "margin", "quality"],
        },
        "full_without_quality_scalars": {
            "features": features[:, h_indices + score_indices + margin_indices + transition_indices],
            "feature_columns": [
                columns[index]
                for index in h_indices + score_indices + margin_indices + transition_indices
            ],
            "feature_roots": ["h", "score", "margin", "transition_delta"],
        },
        "matched_random": {
            "features": features,
            "feature_columns": columns,
            "feature_roots": ["h", "score", "margin", "transition_delta", "quality"],
            "control_role": "full_feature_matched_random_gap_labels",
        },
    }
    for arm in ARM_NAMES:
        arm_columns = list(matrices[arm]["feature_columns"])
        producer._assert_inference_columns(arm_columns)
        if matrices[arm]["features"].shape[1] != len(arm_columns):
            raise ValueError(f"feature column count mismatch for {arm}")
    return matrices


def _forbidden_feature_audit(columns: Sequence[str]) -> dict[str, Any]:
    producer._assert_inference_columns(list(columns))
    forbidden = set(producer.FORBIDDEN_INFERENCE_COLUMNS)
    present = [
        column
        for column in columns
        if column in forbidden or column.split(":", 1)[0] in forbidden
    ]
    return {
        "status": "pass" if not present else "fail",
        "forbidden_inference_columns": list(producer.FORBIDDEN_INFERENCE_COLUMNS),
        "forbidden_present": present,
    }


def _metric_projection(metrics: dict[str, Any]) -> dict[str, Any]:
    return producer._metric_projection(metrics)


def _arm_record(
    *,
    seed: int,
    seed_index: int,
    arm: str,
    arm_matrix: dict[str, Any],
    surface: dict[str, Any],
) -> dict[str, Any]:
    train_idx = surface["train_idx"]
    eval_idx = surface["eval_idx"]
    labels = surface["gap_labels"]
    features = producer._require_finite(f"{arm}_features", arm_matrix["features"], ndim=2)
    randomized_labels = producer._matched_random_gap_labels(labels, seed=seed)
    train_labels = randomized_labels[train_idx] if arm == "matched_random" else labels[train_idx]
    heads = producer._fit_gap_head(features[train_idx], train_labels)
    probabilities = producer._predict_gap_head(heads, features[eval_idx])
    random_heads = producer._fit_gap_head(features[train_idx], randomized_labels[train_idx])
    random_probabilities = producer._predict_gap_head(random_heads, features[eval_idx])
    eval_labels = labels[eval_idx]
    eval_error = surface["prediction_error"][eval_idx]
    vanilla_metrics = producer._metrics_for_arm(
        arm=f"{arm}_vanilla",
        probabilities=np.zeros_like(probabilities, dtype=np.float64),
        labels=eval_labels,
        prediction_error=eval_error,
    )
    learned_metrics = producer._metrics_for_arm(
        arm=f"{arm}_gap_head",
        probabilities=probabilities,
        labels=eval_labels,
        prediction_error=eval_error,
    )
    matched_metrics = producer._metrics_for_arm(
        arm=f"{arm}_matched_random_gap_head",
        probabilities=random_probabilities,
        labels=eval_labels,
        prediction_error=eval_error,
    )
    vanilla_unlogged = float(vanilla_metrics["unlogged_error_rate"])
    learned_unlogged = float(learned_metrics["unlogged_error_rate"])
    matched_unlogged = float(matched_metrics["unlogged_error_rate"])
    return {
        "seed": int(seed),
        "seed_index": int(seed_index),
        "arm": arm,
        "feature_roots": list(arm_matrix["feature_roots"]),
        "feature_columns": list(arm_matrix["feature_columns"]),
        "feature_column_count": int(len(arm_matrix["feature_columns"])),
        "alias_of": arm_matrix.get("alias_of"),
        "gating_role": arm_matrix.get("gating_role", "gating_candidate"),
        "control_role": arm_matrix.get("control_role"),
        "forbidden_feature_audit": _forbidden_feature_audit(arm_matrix["feature_columns"]),
        "arms": {
            "vanilla": _metric_projection(vanilla_metrics),
            "learned": _metric_projection(learned_metrics),
            "matched_random": _metric_projection(matched_metrics),
        },
        "comparison": {
            "unlogged_error_reduction_learned": vanilla_unlogged - learned_unlogged,
            "unlogged_error_reduction_matched_random": vanilla_unlogged - matched_unlogged,
            "failure_detection_auroc_delta_learned_minus_matched_random": float(
                learned_metrics["failure_detection_auroc"]["value"]
                - matched_metrics["failure_detection_auroc"]["value"]
            ),
        },
    }


def _records(config: producer.GapHeadRunConfig) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    for seed_index, seed in enumerate(config.seeds):
        surface = producer._surface_for_seed(seed=int(seed), config=config)
        matrices = _arm_feature_matrices(surface)
        for arm in ARM_NAMES:
            records.append(
                _arm_record(
                    seed=int(seed),
                    seed_index=seed_index,
                    arm=arm,
                    arm_matrix=matrices[arm],
                    surface=surface,
                )
            )
    return records


def _stats_from_records(records: Sequence[dict[str, Any]], getter: Any) -> dict[str, Any]:
    return metric_stats(float(getter(record)) for record in records)


def _arm_aggregate(records: Sequence[dict[str, Any]]) -> dict[str, Any]:
    if not records:
        raise ValueError("arm records must not be empty")
    first = records[0]
    return {
        "record_count": int(len(records)),
        "feature_roots": list(first["feature_roots"]),
        "feature_column_count": int(first["feature_column_count"]),
        "alias_of": first.get("alias_of"),
        "gating_role": first.get("gating_role"),
        "control_role": first.get("control_role"),
        "forbidden_feature_audit": {
            "status": "pass"
            if all(record["forbidden_feature_audit"]["status"] == "pass" for record in records)
            else "fail",
            "forbidden_present": sorted(
                {
                    column
                    for record in records
                    for column in record["forbidden_feature_audit"]["forbidden_present"]
                }
            ),
        },
        "learned": {
            "failure_detection_auroc": _stats_from_records(
                records, lambda record: record["arms"]["learned"]["failure_detection_auroc"]["value"]
            ),
            "unlogged_error_rate": _stats_from_records(
                records, lambda record: record["arms"]["learned"]["unlogged_error_rate"]
            ),
            "unlogged_error_reduction": _stats_from_records(
                records, lambda record: record["comparison"]["unlogged_error_reduction_learned"]
            ),
        },
        "matched_random": {
            "failure_detection_auroc": _stats_from_records(
                records,
                lambda record: record["arms"]["matched_random"]["failure_detection_auroc"]["value"],
            ),
            "unlogged_error_rate": _stats_from_records(
                records, lambda record: record["arms"]["matched_random"]["unlogged_error_rate"]
            ),
            "unlogged_error_reduction": _stats_from_records(
                records,
                lambda record: record["comparison"]["unlogged_error_reduction_matched_random"],
            ),
        },
        "learned_minus_matched_random_auroc": _stats_from_records(
            records,
            lambda record: record["comparison"][
                "failure_detection_auroc_delta_learned_minus_matched_random"
            ],
        ),
    }


def _aggregate(records: Sequence[dict[str, Any]]) -> dict[str, Any]:
    by_arm_records = {arm: [record for record in records if record["arm"] == arm] for arm in ARM_NAMES}
    return {
        "record_count": int(len(records)),
        "seed_order": sorted({int(record["seed"]) for record in records}),
        "arm_order": list(ARM_NAMES),
        "by_arm": {
            arm: _arm_aggregate(by_arm_records[arm])
            for arm in ARM_NAMES
        },
    }


def _mean_metric(aggregate: dict[str, Any], arm: str, metric: str) -> float:
    return float(aggregate["by_arm"][arm]["learned"][metric]["mean"])


def _ci_low(aggregate: dict[str, Any], arm: str, metric: str) -> float:
    return float(aggregate["by_arm"][arm]["learned"][metric]["ci95_low"])


def _ci_high(aggregate: dict[str, Any], arm: str, metric: str) -> float:
    return float(aggregate["by_arm"][arm]["learned"][metric]["ci95_high"])


def _within_full_tolerance(aggregate: dict[str, Any], arm: str) -> bool:
    full_auroc = _mean_metric(aggregate, "full", "failure_detection_auroc")
    arm_auroc = _mean_metric(aggregate, arm, "failure_detection_auroc")
    full_reduction = _mean_metric(aggregate, "full", "unlogged_error_reduction")
    arm_reduction = _mean_metric(aggregate, arm, "unlogged_error_reduction")
    return (
        arm_auroc >= full_auroc - AUROC_MARGIN
        and arm_reduction >= full_reduction - UNLOGGED_REDUCTION_MARGIN
    )


def _full_significantly_exceeds(aggregate: dict[str, Any], arm: str) -> bool:
    full_auroc = _mean_metric(aggregate, "full", "failure_detection_auroc")
    arm_auroc = _mean_metric(aggregate, arm, "failure_detection_auroc")
    full_reduction = _mean_metric(aggregate, "full", "unlogged_error_reduction")
    arm_reduction = _mean_metric(aggregate, arm, "unlogged_error_reduction")
    return (
        full_auroc >= arm_auroc + AUROC_MARGIN
        and full_reduction >= arm_reduction + UNLOGGED_REDUCTION_MARGIN
    )


def _hg_a1_gates(aggregate: dict[str, Any]) -> dict[str, Any]:
    full = aggregate["by_arm"]["full"]["learned"]
    matched = aggregate["by_arm"]["matched_random"]["learned"]
    hg1_pass = (
        float(full["failure_detection_auroc"]["ci95_low"])
        > float(matched["failure_detection_auroc"]["ci95_high"])
        and float(full["unlogged_error_reduction"]["ci95_low"])
        > float(matched["unlogged_error_reduction"]["ci95_high"])
        and float(full["failure_detection_auroc"]["mean"]) >= AUROC_POSITIVE_THRESHOLD
    )
    h_norm_sufficient = _within_full_tolerance(aggregate, "h_norm_only")
    hg2_pass = _full_significantly_exceeds(aggregate, "h_norm_only")
    score_plus_margin_sufficient = _within_full_tolerance(aggregate, "score_plus_margin")
    margin_sufficient = _within_full_tolerance(aggregate, "margin_only")
    hg3_pass = (
        _full_significantly_exceeds(aggregate, "score_plus_margin")
        and _full_significantly_exceeds(aggregate, "margin_only")
    )
    key_ablation_losses = {
        arm: _full_significantly_exceeds(aggregate, arm)
        for arm in (
            "full_without_margin",
            "full_without_transition",
            "full_without_quality_scalars",
        )
    }
    single_channel_sufficiency = {
        arm: _within_full_tolerance(aggregate, arm)
        for arm in SINGLE_CHANNEL_ARMS
    }
    hg4_pass = all(key_ablation_losses.values()) and not any(single_channel_sufficiency.values())
    sufficient_non_alias = [
        arm
        for arm in SINGLE_CHANNEL_ARMS + REDUCED_FAMILY_ARMS
        if arm not in {"h_norm_only", "score_plus_margin"} and _within_full_tolerance(aggregate, arm)
    ]
    if h_norm_sufficient:
        mechanism_status = "scale-dominated-h-norm"
        demotion_channel = "h_norm_only"
    elif score_plus_margin_sufficient:
        mechanism_status = "probe-margin-channel"
        demotion_channel = "score_plus_margin"
    elif sufficient_non_alias:
        mechanism_status = "demote_single_channel_explanation"
        demotion_channel = sufficient_non_alias[0]
    elif hg1_pass and hg2_pass and hg3_pass and hg4_pass:
        mechanism_status = "D5-M_candidate"
        demotion_channel = None
    elif hg1_pass:
        mechanism_status = "D5-O_not_D5-M"
        demotion_channel = None
    else:
        mechanism_status = "not_positive"
        demotion_channel = None
    gates = {
        "HG-A1-1": {
            "status": "pass" if hg1_pass else "fail",
            "criterion": (
                "full AUROC CI low > matched-random AUROC CI high, full UnloggedErrorRate "
                f"reduction CI low > matched-random CI high, and full AUROC mean >= {AUROC_POSITIVE_THRESHOLD}"
            ),
            "full": full,
            "matched_random": matched,
        },
        "HG-A1-2": {
            "status": "pass" if hg2_pass else "fail",
            "criterion": (
                f"full exceeds h_norm_only by AUROC margin {AUROC_MARGIN} and "
                f"UnloggedErrorRate reduction margin {UNLOGGED_REDUCTION_MARGIN}"
            ),
            "h_norm_only_within_full_tolerance": bool(h_norm_sufficient),
            "full": aggregate["by_arm"]["full"]["learned"],
            "h_norm_only": aggregate["by_arm"]["h_norm_only"]["learned"],
        },
        "HG-A1-3": {
            "status": "pass" if hg3_pass else "fail",
            "criterion": "full exceeds score_plus_margin and margin_only by the predeclared margins",
            "score_plus_margin_within_full_tolerance": bool(score_plus_margin_sufficient),
            "margin_only_within_full_tolerance": bool(margin_sufficient),
            "score_plus_margin": aggregate["by_arm"]["score_plus_margin"]["learned"],
            "margin_only": aggregate["by_arm"]["margin_only"]["learned"],
        },
        "HG-A1-4": {
            "status": "pass" if hg4_pass else "fail",
            "criterion": (
                "key full-without ablations lose relative to full and single channels do not "
                "explain full within tolerance"
            ),
            "key_ablation_losses": key_ablation_losses,
            "single_channel_sufficiency": single_channel_sufficiency,
        },
        "HG-A1-5": {
            "status": mechanism_status,
            "mechanism_status": mechanism_status,
            "demotion_channel": demotion_channel,
            "excluded_alias_demotions": ["h_normalized_no_scale"],
            "gating_arms": list(GATING_ARMS),
        },
    }
    return {
        "status": "pass" if mechanism_status == "D5-M_candidate" else "fail",
        "mechanism_status": mechanism_status,
        "demotion_channel": demotion_channel,
        "gates": gates,
    }


def _alias_metadata() -> dict[str, Any]:
    return {
        "h_normalized_no_scale": {
            "alias_of": "h_direction_only",
            "implementation": "row_l2_unit_direction",
            "train_split_centering": False,
            "gating_role": "non_gating_alias",
            "participates_in_HG_A1_2_to_4": False,
            "independent_HG_A1_5_demotion_channel": False,
        }
    }


def _control_protocol(config: producer.GapHeadRunConfig) -> dict[str, Any]:
    return {
        "label_protocol": "seed_deterministic_per_channel_permutation",
        "matched_random_helper": "scripts/run_gap_ledger_head_on_h.py::_matched_random_gap_labels",
        "metric_helper": "scripts/run_gaussian_ou_gap_ledger_head.py::_metrics_for_arm",
        "same_split": True,
        "same_thresholds": True,
        "same_budget": True,
        "sample_count": int(config.sample_count),
        "seed_count": int(len(config.seeds)),
        "gating_aliases_excluded": ["h_normalized_no_scale"],
    }


def _source_artifacts(config: producer.GapHeadRunConfig) -> dict[str, Any]:
    return {
        "artifact_id": ARTIFACT_ID,
        "generation_script": "scripts/run_gap_head_mechanism_attribution.py",
        "source_surface": "scripts/run_gap_ledger_head_on_h.py::_surface_for_seed",
        "source_fit_helper": "scripts/run_gap_ledger_head_on_h.py::_fit_gap_head",
        "source_predict_helper": "scripts/run_gap_ledger_head_on_h.py::_predict_gap_head",
        "source_metric_helper": "scripts/run_gap_ledger_head_on_h.py::_metrics_for_arm",
        "source_matched_random_helper": "scripts/run_gap_ledger_head_on_h.py::_matched_random_gap_labels",
        "source_forbidden_column_audit": "scripts/run_gap_ledger_head_on_h.py::_assert_inference_columns",
        "source_config": "scripts/run_gap_ledger_head_on_h.py::GapHeadRunConfig",
        "json_artifact": config.json_artifact,
        "report_artifact": config.report_artifact,
        "canonical_status": "sidecar_not_canonical",
    }


def _payload(
    records: Sequence[dict[str, Any]],
    config: producer.GapHeadRunConfig,
    *,
    generated_at: str | None = None,
) -> dict[str, Any]:
    aggregate = _aggregate(records)
    gates = _hg_a1_gates(aggregate)
    return {
        "artifact_id": ARTIFACT_ID,
        "json_artifact": config.json_artifact,
        "markdown_artifact": config.report_artifact,
        "generated_at": generated_at if generated_at is not None else datetime.now(timezone.utc).isoformat(),
        "sidecar_role": "pointer_only_non_canonical",
        "mechanism_status": gates["mechanism_status"],
        "demotion_channel": gates["demotion_channel"],
        "D5_target": {
            "input_status": "D5-O_candidate",
            "closed_status": "D5-M_candidate" if gates["mechanism_status"] == "D5-M_candidate" else "blocked",
            "claim": "Gaussian-OU learned-h gap-head mechanism attribution only",
        },
        "config": {
            "sample_count": int(config.sample_count),
            "seed_count": int(len(config.seeds)),
            "seeds": [int(seed) for seed in config.seeds],
            "rho": float(config.rho),
            "use_torch": bool(config.use_torch),
            "run_id_prefix": config.run_id_prefix,
            "arm_count": len(ARM_NAMES),
            "arm_order": list(ARM_NAMES),
            "gating_arm_order": list(GATING_ARMS),
            "auroc_positive_threshold": AUROC_POSITIVE_THRESHOLD,
            "auroc_margin": AUROC_MARGIN,
            "unlogged_error_reduction_margin": UNLOGGED_REDUCTION_MARGIN,
        },
        "source_artifacts": _source_artifacts(config),
        "control_protocol": _control_protocol(config),
        "alias_metadata": _alias_metadata(),
        "forbidden_column_audit": {
            "status": "pass"
            if all(
                row["forbidden_feature_audit"]["status"] == "pass"
                for row in aggregate["by_arm"].values()
            )
            else "fail",
            "forbidden_inference_columns": list(producer.FORBIDDEN_INFERENCE_COLUMNS),
            "assertion_helper": "scripts/run_gap_ledger_head_on_h.py::_assert_inference_columns",
        },
        "HG_A1": gates,
        "aggregate": aggregate,
        "records": list(records),
        "not_claimed": [
            "No global quality claim.",
            "No full LeJEPA claim.",
            "No full Tensor NameCert claim.",
            "No LLM behavior claim.",
            "No canonical discovery-map promotion from this sidecar.",
        ],
    }


def _render_report(payload: dict[str, Any]) -> str:
    lines = [
        "# Gap-Head Mechanism Attribution",
        "",
        f"- Generated at: `{payload['generated_at']}`",
        f"- Artifact: `{payload['artifact_id']}`",
        f"- Sidecar role: `{payload['sidecar_role']}`",
        f"- Mechanism status: `{payload['mechanism_status']}`",
        f"- Demotion channel: `{payload['demotion_channel']}`",
        f"- Arm count: `{payload['config']['arm_count']}`",
        "",
        "## Arms",
        "",
        "| arm | learned AUROC | learned UER reduction | matched-random AUROC | alias | gating role |",
        "| --- | ---: | ---: | ---: | --- | --- |",
    ]
    for arm in payload["config"]["arm_order"]:
        row = payload["aggregate"]["by_arm"][arm]
        lines.append(
            "| "
            f"`{arm}` | "
            f"{_render_stats(row['learned']['failure_detection_auroc'])} | "
            f"{_render_stats(row['learned']['unlogged_error_reduction'])} | "
            f"{_render_stats(row['matched_random']['failure_detection_auroc'])} | "
            f"`{row['alias_of']}` | "
            f"`{row['gating_role']}` |"
        )
    lines.extend(
        [
            "",
            "## HG-A1 Gates",
            "",
            "| gate | status |",
            "| --- | --- |",
        ]
    )
    for gate, row in payload["HG_A1"]["gates"].items():
        lines.append(f"| `{gate}` | `{row['status']}` |")
    lines.extend(
        [
            "",
            "## Alias Metadata",
            "",
            (
                "- `h_normalized_no_scale` is a non-gating alias of "
                "`h_direction_only`; it reuses the row-L2 unit-direction matrix, "
                "does not train-center, and is excluded as an independent demotion channel."
            ),
            "",
            "## Source Pointers",
            "",
        ]
    )
    for key, value in payload["source_artifacts"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## Not Claimed", ""])
    for item in payload["not_claimed"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def _write_payload(payload: dict[str, Any], config: producer.GapHeadRunConfig) -> None:
    json_path = ROOT / config.json_artifact
    report_path = ROOT / config.report_artifact
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    report_path.write_text(_render_report(payload), encoding="utf-8")


def _active_config() -> producer.GapHeadRunConfig:
    default = producer.DEFAULT_CONFIG
    return producer.GapHeadRunConfig(
        sample_count=default.sample_count,
        seeds=default.seeds,
        rho=default.rho,
        use_torch=producer.USE_TORCH,
        json_artifact=JSON_ARTIFACT,
        report_artifact=REPORT_ARTIFACT,
        run_id_prefix="gap-head-mechanism-attribution",
        source_artifact_label="gap-head-mechanism-attribution",
        seed_grid_kind=default.seed_grid_kind,
    )


def build_gap_head_mechanism_attribution(
    *,
    root: Path | str | None = None,
    generated_at: str | None = None,
) -> dict[str, Any]:
    global ROOT
    if root is not None:
        ROOT = Path(root)
        producer.ROOT = ROOT
    config = _active_config()
    return _payload(_records(config), config, generated_at=generated_at)


def write_gap_head_mechanism_attribution(
    *,
    root: Path | str | None = None,
    generated_at: str | None = None,
) -> dict[str, Any]:
    payload = build_gap_head_mechanism_attribution(root=root, generated_at=generated_at)
    config = _active_config()
    _write_payload(payload, config)
    return payload


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", default=str(ROOT), help="Repository root for artifacts.")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> None:
    args = parse_args(argv)
    payload = write_gap_head_mechanism_attribution(root=args.root)
    print(f"wrote {payload['json_artifact']}")
    print(f"wrote {payload['markdown_artifact']}")
    print(f"mechanism_status {payload['mechanism_status']}")


if __name__ == "__main__":
    main()

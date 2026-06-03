#!/usr/bin/env python3
"""Run a dimension-mismatch debt-transfer check over h summaries."""

from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime, timezone
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
from scripts import run_gap_head_observed_debt_transfer as observed_transfer
from scripts import run_gap_ledger_head_on_h as gap_head
from scripts import run_gap_head_robustness_sweep as robustness
from scripts import run_observed_debt_sweep as observed_debt


JSON_ARTIFACT = "reports/canonical/dimension-mismatch-debt-transfer.json"
REPORT_ARTIFACT = "reports/canonical/dimension-mismatch-debt-transfer.md"
ARTIFACT_ID = "bedc-quality-lab:dimension-mismatch-debt-transfer"
TRANSFER_STATUS_POINTER = "$.dimension_mismatch_debt_transfer.status"
DEFAULT_AXIS = "C1"
DEFAULT_AXIS_LABEL = "encoder_output_dim"
DEFAULT_ROW = observed_debt.DIMENSION_ROW
DEFAULT_SCOPE = "encoder_dim grid against producer reference latent dimension"
H_ONLY_REPRESENTATION_SUMMARY_COLUMNS = (
    "h_mean",
    "h_std",
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
FORBIDDEN_FEATURE_COLUMNS = (
    "encoder_dim",
    "reference_latent_dim",
    "abs_encoder_dim_minus_reference_dim",
    "is_reference_encoder_dim",
    "linear_identifiability_r2",
    "quality_debt",
    "debt_delta",
    "ledger_status",
    "ledger_row_status",
    "gap_status",
    "source_metric",
    "envelope_metric",
    "truth_label",
    "label",
    "gap_label",
    "prediction_error",
    "row_index",
    "raw_h",
    "raw_z",
    "h",
    "z",
    "z_pair",
    "representation_payload",
    "envelope_record",
)
NOT_CLAIMED = (
    "no global quality conclusion",
    "no full LeJEPA conclusion",
    "no claim outside the listed encoder_dim-grid debt-transfer surface",
    "no inference-time use of config metadata, quality-debt summary, ledger/gap status, truth labels, prediction error, or raw h/z",
    "fail status blocks any D4/D5 promotion through this boundary ledger",
)


@dataclass(frozen=True)
class DimensionMismatchTransferResult:
    surface_id: str
    status: str
    status_code: str
    reason: str
    discovery_level: str
    learned_auroc: Mapping[str, Any]
    matched_random_auroc: Mapping[str, Any]
    hardgates: Mapping[str, Any]
    result_rows: tuple[Mapping[str, Any], ...]

    def to_record(self) -> dict[str, Any]:
        return {
            "surface_id": self.surface_id,
            "status": self.status,
            "status_code": self.status_code,
            "reason": self.reason,
            "discovery_level": self.discovery_level,
            "learned_auroc": dict(self.learned_auroc),
            "matched_random_auroc": dict(self.matched_random_auroc),
            "hardgates": dict(self.hardgates),
            "result_rows": [dict(row) for row in self.result_rows],
        }


def _format_float(value: float) -> str:
    if math.isnan(value):
        return "nan"
    return f"{value:.6f}"


def _require_h(name: str, value: np.ndarray) -> np.ndarray:
    array = np.asarray(value, dtype=np.float64)
    if array.ndim != 2 or array.shape[0] == 0 or array.shape[1] == 0:
        raise ValueError(f"{name} must be a non-empty matrix")
    if not np.all(np.isfinite(array)):
        raise ValueError(f"{name} contains non-finite values")
    return array


def summarize_h_representation(h: np.ndarray, h_pair: np.ndarray) -> dict[str, float]:
    """Return fixed scalar summaries derived only from h and h_pair."""

    h_value = _require_h("h", h)
    pair_value = _require_h("h_pair", h_pair)
    if h_value.shape != pair_value.shape:
        raise ValueError("h and h_pair must have the same shape")
    row_norms = np.linalg.norm(h_value, axis=1)
    pair_delta_norms = np.linalg.norm(h_value - pair_value, axis=1)
    return {
        "h_mean": float(np.mean(h_value)),
        "h_std": float(np.std(h_value)),
        "h_l2_mean": float(np.mean(row_norms)),
        "h_l2_std": float(np.std(row_norms)),
        "h_abs_mean": float(np.mean(np.abs(h_value))),
        "h_abs_max": float(np.max(np.abs(h_value))),
        "h_abs_q25": float(np.quantile(np.abs(h_value), 0.25)),
        "h_abs_q50": float(np.quantile(np.abs(h_value), 0.50)),
        "h_abs_q75": float(np.quantile(np.abs(h_value), 0.75)),
        "h_pair_delta_l2_mean": float(np.mean(pair_delta_norms)),
        "h_pair_delta_l2_std": float(np.std(pair_delta_norms)),
    }


def _forbidden_feature_hits(columns: Sequence[str]) -> list[str]:
    forbidden = {name.lower() for name in FORBIDDEN_FEATURE_COLUMNS}
    hits = []
    for column in columns:
        lower = str(column).lower()
        root = lower.split(":", 1)[0]
        if lower in forbidden or root in forbidden:
            hits.append(str(column))
    return sorted(set(hits))


def assert_feature_matrix_contract(
    feature_columns: Sequence[str],
    declared_allowlist: Sequence[str] = H_ONLY_REPRESENTATION_SUMMARY_COLUMNS,
) -> None:
    actual = tuple(str(column) for column in feature_columns)
    declared = tuple(str(column) for column in declared_allowlist)
    if actual != declared:
        raise ValueError(
            "feature columns must exactly match declared h-only representation-summary allowlist"
        )
    hits = _forbidden_feature_hits(actual)
    if hits:
        raise ValueError(f"forbidden feature columns present: {', '.join(hits)}")


def _feature_contract_audit(feature_columns: Sequence[str]) -> dict[str, Any]:
    try:
        assert_feature_matrix_contract(feature_columns)
        return {
            "status": "pass",
            "declared_h_only_allowlist": list(H_ONLY_REPRESENTATION_SUMMARY_COLUMNS),
            "actual_model_input_columns": [str(column) for column in feature_columns],
            "forbidden_feature_columns": list(FORBIDDEN_FEATURE_COLUMNS),
            "forbidden_present": [],
            "reason": "actual model input columns exactly match the declared h-only allowlist",
        }
    except ValueError as exc:
        return {
            "status": "fail",
            "declared_h_only_allowlist": list(H_ONLY_REPRESENTATION_SUMMARY_COLUMNS),
            "actual_model_input_columns": [str(column) for column in feature_columns],
            "forbidden_feature_columns": list(FORBIDDEN_FEATURE_COLUMNS),
            "forbidden_present": _forbidden_feature_hits(feature_columns),
            "reason": str(exc),
        }


def _surface_arrays(*, seed: int, seed_index: int, encoder_dim: int) -> dict[str, Any]:
    envelope = observed_debt._observed_envelope(
        axis=DEFAULT_AXIS,
        axis_value=int(encoder_dim),
        seed=int(seed),
        seed_index=int(seed_index),
        encoder_dim=int(encoder_dim),
        training_steps=observed_debt.BASELINE_TRAINING_STEPS,
        sample_count=observed_debt.BASELINE_SAMPLE_COUNT,
        ledger_scope_rows=frozenset({DEFAULT_ROW})
        if int(encoder_dim) != observed_debt.BASELINE_ENCODER_DIM
        else None,
    )
    batch = observed_debt.make_toy_batch(
        observed_debt.BASELINE_SAMPLE_COUNT,
        rho=observed_debt.RHO,
        seed=int(seed),
    )
    train_idx, eval_idx = observed_debt._train_eval_split(batch.z.shape[0], seed=int(seed))
    h, h_pair = observed_debt._standardized_projection(
        train_x=batch.x[train_idx],
        eval_x=batch.x[eval_idx],
        eval_x_pair=batch.x_pair[eval_idx],
        output_dim=int(encoder_dim),
    )
    return {"envelope": envelope, "h": h, "h_pair": h_pair}


def _surface_matrix() -> dict[str, Any]:
    feature_columns = list(H_ONLY_REPRESENTATION_SUMMARY_COLUMNS)
    rows: list[list[float]] = []
    labels: list[list[float]] = []
    evidence_rows: list[dict[str, Any]] = []
    seeds = tuple(int(seed) for seed in observed_debt._seeds(DEFAULT_AXIS, observed_debt.DEFAULT_SEED_COUNT_BY_AXIS[DEFAULT_AXIS]))
    reference_dim: int | None = None
    for seed_index, seed in enumerate(seeds):
        for encoder_dim in observed_debt.C1_ENCODER_DIMS:
            surface = _surface_arrays(seed=seed, seed_index=seed_index, encoder_dim=int(encoder_dim))
            envelope = surface["envelope"]
            if reference_dim is None:
                reference_dim = int(envelope.source_spec["latent_dim"])
            summary = summarize_h_representation(surface["h"], surface["h_pair"])
            rows.append([float(summary[column]) for column in feature_columns])
            is_reference = int(encoder_dim) == int(reference_dim)
            is_under = int(encoder_dim) < int(reference_dim)
            is_over = int(encoder_dim) > int(reference_dim)
            labels.append([
                0.0 if is_reference else 1.0,
                1.0 if is_under else 0.0,
                1.0 if is_over else 0.0,
                1.0 if is_reference else 0.0,
            ])
            evidence_rows.append(
                {
                    "seed": int(seed),
                    "seed_index": int(seed_index),
                    "axis": DEFAULT_AXIS,
                    "axis_label": DEFAULT_AXIS_LABEL,
                    "axis_value": int(encoder_dim),
                    "row": DEFAULT_ROW,
                    "reference_latent_dim": int(reference_dim),
                    "dimension_mismatch_label": bool(not is_reference),
                    "metric": observed_debt.BASELINE_METRIC,
                    "metric_value": float(envelope.metrics[observed_debt.BASELINE_METRIC]),
                    "row_present": observed_debt._row_present(envelope, DEFAULT_ROW),
                    "row_gap": observed_debt._row_gap(envelope, DEFAULT_ROW),
                    "status_code": "reference-dimension"
                    if is_reference
                    else "dimension-mismatch-surface",
                    "reason": "encoder output dimension equals the producer reference latent dimension"
                    if is_reference
                    else "encoder output dimension differs from the producer reference latent dimension",
                    "source_pointer": "scripts/run_observed_debt_sweep.py::_observed_envelope",
                }
            )
    assert_feature_matrix_contract(feature_columns)
    return {
        "features": np.asarray(rows, dtype=np.float64),
        "labels": np.asarray(labels, dtype=np.float64),
        "prediction_error": np.asarray([row[0] for row in labels], dtype=np.float64),
        "feature_columns": feature_columns,
        "evidence_rows": evidence_rows,
        "seeds": seeds,
        "reference_latent_dim": int(reference_dim if reference_dim is not None else observed_debt.BASELINE_ENCODER_DIM),
    }


def _train_eval_split(row_count: int, *, seed: int) -> tuple[np.ndarray, np.ndarray]:
    if row_count < 4:
        raise ValueError("row_count must be at least 4")
    rng = np.random.default_rng(int(seed) ^ 0xD17E5510)
    for _ in range(64):
        indices = rng.permutation(row_count)
        train_count = min(row_count - 1, max(1, round(0.70 * row_count)))
        train_idx = np.sort(indices[:train_count]).astype(np.int64)
        eval_idx = np.sort(indices[train_count:]).astype(np.int64)
        eval_labels = eval_idx
        del eval_labels
        if train_idx.shape[0] > 0 and eval_idx.shape[0] > 0:
            return train_idx, eval_idx
    raise ValueError("could not build train/eval split")


def _metric_projection(metrics: dict[str, Any]) -> dict[str, Any]:
    return gap_head._metric_projection(metrics)


def _fold_record(matrix: Mapping[str, Any], *, fold_seed: int, fold_index: int) -> dict[str, Any]:
    features = np.asarray(matrix["features"], dtype=np.float64)
    labels = np.asarray(matrix["labels"], dtype=np.float64)
    prediction_error = np.asarray(matrix["prediction_error"], dtype=np.float64)
    train_idx, eval_idx = _train_eval_split(features.shape[0], seed=int(fold_seed))
    heads = gap_head._fit_gap_head(features[train_idx], labels[train_idx])
    probabilities = gap_head._predict_gap_head(heads, features[eval_idx])
    randomized_labels = observed_transfer.producer._matched_random_gap_labels(labels, seed=int(fold_seed))
    random_heads = gap_head._fit_gap_head(features[train_idx], randomized_labels[train_idx])
    random_probabilities = gap_head._predict_gap_head(random_heads, features[eval_idx])
    eval_labels = labels[eval_idx]
    eval_error = prediction_error[eval_idx]
    vanilla_probabilities = np.zeros_like(probabilities, dtype=np.float64)
    vanilla = gap_head._metrics_for_arm(
        arm="vanilla",
        probabilities=vanilla_probabilities,
        labels=eval_labels,
        prediction_error=eval_error,
    )
    learned = gap_head._metrics_for_arm(
        arm="learned_h_summary_head",
        probabilities=probabilities,
        labels=eval_labels,
        prediction_error=eval_error,
    )
    matched = gap_head._metrics_for_arm(
        arm=observed_transfer.producer.MATCHED_RANDOM_ARM,
        probabilities=random_probabilities,
        labels=eval_labels,
        prediction_error=eval_error,
    )
    return {
        "fold_index": int(fold_index),
        "fold_seed": int(fold_seed),
        "train_count": int(train_idx.shape[0]),
        "eval_count": int(eval_idx.shape[0]),
        "eval_positive_count": int(np.sum(eval_error > gap_head.PRIMARY_EPSILON)),
        "eval_negative_count": int(eval_error.shape[0] - np.sum(eval_error > gap_head.PRIMARY_EPSILON)),
        "arms": {
            "vanilla": _metric_projection(vanilla),
            "learned_h_summary_head": _metric_projection(learned),
            observed_transfer.producer.MATCHED_RANDOM_ARM: _metric_projection(matched),
        },
        "comparison": {
            "failure_detection_auroc_delta_learned_minus_matched_random": float(
                learned["failure_detection_auroc"]["value"]
                - matched["failure_detection_auroc"]["value"]
            ),
            "failure_detection_auroc_delta_learned_minus_vanilla": float(
                learned["failure_detection_auroc"]["value"]
                - vanilla["failure_detection_auroc"]["value"]
            ),
        },
    }


def _stats_from_records(records: Sequence[Mapping[str, Any]], arm: str, metric: str) -> dict[str, Any]:
    return metric_stats(float(record["arms"][arm][metric]["value"]) for record in records)


def _delta_stats(records: Sequence[Mapping[str, Any]], key: str) -> dict[str, Any]:
    return metric_stats(float(record["comparison"][key]) for record in records)


def _arm_metrics(records: Sequence[Mapping[str, Any]], arm: str) -> dict[str, Any]:
    return {
        "failure_detection_auroc": _stats_from_records(records, arm, "failure_detection_auroc"),
    }


def _hardgates(*, matrix: Mapping[str, Any], records: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    audit = _feature_contract_audit(matrix["feature_columns"])
    learned = _arm_metrics(records, "learned_h_summary_head")["failure_detection_auroc"]
    matched = _arm_metrics(records, observed_transfer.producer.MATCHED_RANDOM_ARM)["failure_detection_auroc"]
    delta = _delta_stats(records, "failure_detection_auroc_delta_learned_minus_matched_random")
    matched_positive = bool(float(matched["mean"]) >= robustness.AUROC_POSITIVE_THRESHOLD)
    comparison_pass = (
        float(learned["ci95_low"]) > float(matched["ci95_high"])
        and float(delta["ci95_low"]) > 0.0
        and not matched_positive
    )
    control_exists = len(records) > 0 and all(observed_transfer.producer.MATCHED_RANDOM_ARM in record["arms"] for record in records)
    claim_audit = _forbidden_claim_term_audit(
        {
            "dimension_mismatch_debt_transfer": {
                "status": "pass" if comparison_pass and audit["status"] == "pass" else "failed",
                "scope": DEFAULT_SCOPE,
            },
            "not_claimed": list(NOT_CLAIMED),
        }
    )
    return {
        "HG-B1": {
            "status": "pass"
            if all(row.get("reason") and row.get("status_code") for row in matrix["evidence_rows"])
            else "fail",
            "criterion": "each result row has a non-empty reason and status code",
            "reason": "all evidence rows carry explicit boundary reasons and status codes",
        },
        "HG-B2": {
            "status": "pass" if control_exists else "fail",
            "criterion": "matched-random control exists and produces per-arm AUROC",
            "matched_random_auroc": matched,
            "reason": "matched-random control arm is present in every fold"
            if control_exists
            else "matched-random control arm is absent",
        },
        "HG-B3": {
            "status": "pass" if comparison_pass else "fail",
            "criterion": (
                "learned AUROC ci95_low > matched-random AUROC ci95_high, delta ci95_low > 0, "
                "and matched-random is not positive"
            ),
            "learned_auroc": learned,
            "matched_random_auroc": matched,
            "learned_minus_matched_random_auroc": delta,
            "matched_random_positive": matched_positive,
            "reason": "learned h-summary head separates the dimension-mismatch label beyond matched-random control"
            if comparison_pass
            else "learned h-summary head does not separate the label beyond matched-random control",
        },
        "HG-B4": {
            "status": audit["status"],
            "criterion": "actual model input columns equal the declared h-only representation-summary allowlist",
            "audit": audit,
            "reason": audit["reason"],
        },
        "HG-B5": {
            "status": claim_audit["status"],
            "criterion": "artifact claim text has no forbidden positive claim terms",
            "audit": claim_audit,
            "reason": claim_audit["reason"],
        },
    }


def _forbidden_claim_term_audit(payload: Mapping[str, Any]) -> dict[str, Any]:
    main_claim_text = json.dumps(
        {
            "dimension_mismatch_debt_transfer": payload.get("dimension_mismatch_debt_transfer"),
        },
        sort_keys=True,
    ).lower()
    hits = [term for term in FORBIDDEN_POSITIVE_CLAIM_TERMS if term.lower() in main_claim_text]
    return {
        "status": "fail" if hits else "pass",
        "forbidden_positive_claim_terms": list(FORBIDDEN_POSITIVE_CLAIM_TERMS),
        "hits": hits,
        "reason": "forbidden positive claim term present" if hits else "no forbidden positive claim terms in main claim text",
    }


def _result(matrix: Mapping[str, Any], records: Sequence[Mapping[str, Any]]) -> DimensionMismatchTransferResult:
    hardgates = _hardgates(matrix=matrix, records=records)
    failed = [name for name, gate in hardgates.items() if gate["status"] != "pass"]
    status = "pass" if not failed else "failed"
    learned = _arm_metrics(records, "learned_h_summary_head")["failure_detection_auroc"]
    matched = _arm_metrics(records, observed_transfer.producer.MATCHED_RANDOM_ARM)["failure_detection_auroc"]
    return DimensionMismatchTransferResult(
        surface_id="observed-debt-c1-encoder-dim-grid",
        status=status,
        status_code="scoped-d4-boundary" if status == "pass" else "failed-boundary",
        reason="all dimension-mismatch transfer hardgates passed"
        if status == "pass"
        else "one or more dimension-mismatch transfer hardgates failed",
        discovery_level="D4" if status == "pass" else "DN",
        learned_auroc=learned,
        matched_random_auroc=matched,
        hardgates=hardgates,
        result_rows=tuple(
            {
                "axis": row["axis"],
                "axis_label": row["axis_label"],
                "axis_value": row["axis_value"],
                "row": row["row"],
                "status_code": row["status_code"],
                "reason": row["reason"],
                "metric": row["metric"],
                "metric_value": row["metric_value"],
                "row_present": row["row_present"],
                "row_gap": row["row_gap"],
                "source_pointer": row["source_pointer"],
            }
            for row in matrix["evidence_rows"]
        ),
    )


def build_payload(*, generated_at: str | None = None) -> dict[str, Any]:
    matrix = _surface_matrix()
    fold_records = [
        _fold_record(matrix, fold_seed=int(seed), fold_index=index)
        for index, seed in enumerate(matrix["seeds"])
    ]
    result = _result(matrix, fold_records)
    status = result.status
    pass_count = 1 if status == "pass" else 0
    return {
        "artifact_id": ARTIFACT_ID,
        "artifact": JSON_ARTIFACT,
        "report": REPORT_ARTIFACT,
        "generated_at": generated_at or datetime.now(timezone.utc).isoformat(),
        "status": "pointer-only",
        "source_artifacts": {
            "generation_script": "scripts/run_dimension_mismatch_debt_transfer.py",
            "observed_debt_surface_owner": "scripts/run_observed_debt_sweep.py",
            "observed_debt_surface": "scripts/run_observed_debt_sweep.py::_observed_envelope",
            "h_projection": "scripts/run_observed_debt_sweep.py::_standardized_projection",
            "toy_world": "bedc_quality_lab.toy_world.make_toy_batch",
            "gap_head_training": "scripts/run_gap_ledger_head_on_h.py::_fit_gap_head",
            "matched_random_control": "scripts/run_gap_ledger_head_on_h.py::_matched_random_gap_labels",
            "metric_helper": "scripts/run_gaussian_ou_gap_ledger_head.py::_metrics_for_arm",
            "claim_terms": "bedc_quality_lab.claim_terms.FORBIDDEN_POSITIVE_CLAIM_TERMS",
        },
        "config": {
            "observed_debt_axis": DEFAULT_AXIS,
            "axis_label": DEFAULT_AXIS_LABEL,
            "encoder_dim_grid": list(observed_debt.C1_ENCODER_DIMS),
            "reference_latent_dim": matrix["reference_latent_dim"],
            "seed_count": len(matrix["seeds"]),
            "seeds": list(matrix["seeds"]),
            "rho": observed_debt.RHO,
            "sample_count": observed_debt.BASELINE_SAMPLE_COUNT,
            "auroc_positive_threshold": robustness.AUROC_POSITIVE_THRESHOLD,
            "transfer_status_pointer": TRANSFER_STATUS_POINTER,
        },
        "representation_boundary": {
            "status": "h-only representation-summary",
            "declared_h_only_allowlist": list(H_ONLY_REPRESENTATION_SUMMARY_COLUMNS),
            "actual_model_input_columns": list(matrix["feature_columns"]),
            "excluded_from_model_input": [
                "config metadata",
                "quality/debt summary",
                "debt delta",
                "ledger row presence/status",
                "gap status",
                "source metrics",
                "envelope aggregate metrics",
                "truth labels",
                "prediction error",
                "row index",
                "raw h",
                "raw z",
                "raw representation payload",
                "envelope record",
            ],
        },
        "control_protocol": {
            "control_arm": observed_transfer.producer.MATCHED_RANDOM_ARM,
            "label_protocol": "seed_deterministic_per_channel_permutation",
            "same_feature_columns_as_treatment": True,
            "same_train_eval_split_as_treatment": True,
            "same_metric_helper_as_treatment": True,
            "same_budget_as_treatment": True,
            "fold_count": len(fold_records),
        },
        "dimension_mismatch_debt_transfer": {
            "status": status,
            "status_code": result.status_code,
            "reason": result.reason,
            "scope": DEFAULT_SCOPE,
            "discovery_level": result.discovery_level,
            "pass_surface_count": pass_count,
            "total_surface_count": 1,
            "discovery_map_pointer": TRANSFER_STATUS_POINTER,
        },
        "metrics": {
            "by_arm": {
                "vanilla": _arm_metrics(fold_records, "vanilla"),
                "learned_h_summary_head": {"failure_detection_auroc": result.learned_auroc},
                observed_transfer.producer.MATCHED_RANDOM_ARM: {"failure_detection_auroc": result.matched_random_auroc},
            },
            "comparison": {
                "failure_detection_auroc_delta_learned_minus_matched_random": _delta_stats(
                    fold_records,
                    "failure_detection_auroc_delta_learned_minus_matched_random",
                ),
                "failure_detection_auroc_delta_learned_minus_vanilla": _delta_stats(
                    fold_records,
                    "failure_detection_auroc_delta_learned_minus_vanilla",
                ),
            },
        },
        "surfaces": [result.to_record()],
        "hardgate_evidence": result.hardgates,
        "boundary_ledger": {
            "status": "recorded",
            "projection": "scoped D4" if status == "pass" else "DN",
            "failed_gates": [
                name for name, gate in result.hardgates.items() if gate["status"] != "pass"
            ],
            "d5_shortcut": False,
            "scope": DEFAULT_SCOPE,
            "reason": "pass is capped at scoped D4; failed status emits no positive D4/D5 fields",
        },
        "not_claimed": list(NOT_CLAIMED),
    }


def render_markdown(payload: Mapping[str, Any]) -> str:
    transfer = payload["dimension_mismatch_debt_transfer"]
    metrics = payload["metrics"]["by_arm"]
    lines = [
        "# Dimension-Mismatch Debt Transfer",
        "",
        f"- JSON artifact pointer: `{payload['artifact']}`",
        f"- Report artifact pointer: `{payload['report']}`",
        f"- Artifact id pointer: `$.artifact_id`",
        f"- Transfer status pointer: `{TRANSFER_STATUS_POINTER}`",
        f"- Boundary ledger pointer: `$.boundary_ledger`",
        f"- H-only allowlist pointer: `$.representation_boundary.declared_h_only_allowlist`",
        f"- Source pointers: `$.source_artifacts`",
        "",
        "## Metric rows",
        "",
        "| metric | arm | mean | ci95 low | ci95 high | source pointer |",
        "| --- | --- | ---: | ---: | ---: | --- |",
    ]
    for arm in ("vanilla", "learned_h_summary_head", observed_transfer.producer.MATCHED_RANDOM_ARM):
        stats = metrics[arm]["failure_detection_auroc"]
        lines.append(
            "| "
            "`failure_detection_auroc` | "
            f"`{arm}` | "
            f"{_format_float(float(stats['mean']))} | "
            f"{_format_float(float(stats['ci95_low']))} | "
            f"{_format_float(float(stats['ci95_high']))} | "
            "`$.metrics.by_arm` |"
        )
    delta = payload["metrics"]["comparison"]["failure_detection_auroc_delta_learned_minus_matched_random"]
    lines.extend(
        [
            "| `failure_detection_auroc_delta` | `learned_minus_matched_random` | "
            f"{_format_float(float(delta['mean']))} | "
            f"{_format_float(float(delta['ci95_low']))} | "
            f"{_format_float(float(delta['ci95_high']))} | "
            "`$.metrics.comparison` |",
            "",
            "## Boundary",
            "",
            "| field | value | pointer |",
            "| --- | --- | --- |",
            f"| status | `{transfer['status']}` | `{TRANSFER_STATUS_POINTER}` |",
            f"| status code | `{transfer['status_code']}` | `$.dimension_mismatch_debt_transfer.status_code` |",
            f"| discovery level | `{transfer['discovery_level']}` | `$.dimension_mismatch_debt_transfer.discovery_level` |",
            f"| scope | `{transfer['scope']}` | `$.dimension_mismatch_debt_transfer.scope` |",
            "",
        ]
    )
    return "\n".join(lines)


def _write_payload(payload: Mapping[str, Any]) -> None:
    json_path = ROOT / JSON_ARTIFACT
    report_path = ROOT / REPORT_ARTIFACT
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")


def main() -> None:
    payload = build_payload()
    _write_payload(payload)
    transfer = payload["dimension_mismatch_debt_transfer"]
    learned = payload["metrics"]["by_arm"]["learned_h_summary_head"]["failure_detection_auroc"]
    matched = payload["metrics"]["by_arm"][observed_transfer.producer.MATCHED_RANDOM_ARM]["failure_detection_auroc"]
    print(f"wrote {JSON_ARTIFACT}")
    print(f"wrote {REPORT_ARTIFACT}")
    print(f"status {transfer['status']}")
    print(f"learned_auroc_mean {_format_float(float(learned['mean']))}")
    print(f"matched_random_auroc_mean {_format_float(float(matched['mean']))}")


if __name__ == "__main__":
    main()

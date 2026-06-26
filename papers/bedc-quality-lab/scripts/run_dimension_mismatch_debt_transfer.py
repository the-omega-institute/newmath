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
from bedc_quality_lab.discovery_compiler.anti_triviality import owner_local_anti_triviality_contract
from bedc_quality_lab.discovery_compiler.pointers import pointer_value, resolve_artifact_pointer
from scripts.experiment_stats import metric_stats
from scripts import run_gap_head_observed_debt_transfer as observed_transfer
from scripts import run_gap_ledger_head_on_h as gap_head
from scripts import run_gap_head_robustness_sweep as robustness
from scripts import run_observed_debt_sweep as observed_debt


JSON_ARTIFACT = "reports/canonical/dimension-mismatch-debt-transfer.json"
REPORT_ARTIFACT = "reports/canonical/dimension-mismatch-debt-transfer.md"
ANTI_TRIVIALITY_ARTIFACT = "reports/dimension_mismatch_anti_triviality.json"
RUN_LOCAL_DIR = "reports/runs/dimension-mismatch-debt-transfer/controlled-geometry"
RUN_LOCAL_CLAIM_CAPSULE_ARTIFACT = f"{RUN_LOCAL_DIR}/claim_capsule.json"
RUN_LOCAL_RAW_METRICS_ARTIFACT = f"{RUN_LOCAL_DIR}/raw_metrics.jsonl"
RUN_LOCAL_SUMMARY_ARTIFACT = f"{RUN_LOCAL_DIR}/summary.json"
RUN_LOCAL_REPORT_ARTIFACT = f"{RUN_LOCAL_DIR}/report.md"
ARTIFACT_ID = "bedc-quality-lab:dimension-mismatch-debt-transfer"
TRANSFER_STATUS_POINTER = "$.dimension_mismatch_debt_transfer.status"
EFFECTIVE_LEVEL_POINTER = "$.dimension_mismatch_debt_transfer.effective_level"
BASE_LEVEL = "D4"
DEFAULT_AXIS = "encoder-dim-grid"
DEFAULT_AXIS_LABEL = "encoder_output_dim"
SOURCE_OBSERVED_DEBT_AXIS = 'C1'
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
    "global dimension theory",
    "representation-geometric debt transfer",
    "D5 promotion",
    "global model quality",
    "full LeJEPA",
    "full TensorNameCert",
    "LLM behavior",
    "mechanism closure unless D5-M",
    "no global quality conclusion",
    "no full LeJEPA conclusion",
    "no claim outside the listed encoder_dim-grid debt-transfer surface",
    "no non-trivial debt-transfer mechanism independent of encoder-dimension information recoverable from h summaries",
    "no inference-time use of config metadata, quality-debt summary, ledger/gap status, truth labels, prediction error, or raw h/z",
    "fail status blocks any D4/D5 promotion through this boundary ledger",
)
NEGATIVE_WITNESS_TEST_POINTER = "$.run_local.test_artifact.regression_tests.scale_leakage_witness"
SCALE_LEAKAGE_WITNESS_POINTER = f"{RUN_LOCAL_CLAIM_CAPSULE_ARTIFACT}:$.run_local.negative_witness[0]"
NEGATIVE_WITNESS_TEST_ARTIFACT = {
    "regression_tests": {
        "scale_leakage_witness": (
            "tests/test_dimension_mismatch_debt_transfer.py::test_scale_leakage_sidecar_maps_to_first_negative_witness"
        )
    }
}
BEDC_GAP_MAPPING_KEYS = (
    "witness_pointer",
    "bedc_gap_field",
    "demotion_rule",
    "regression_test",
)
CONTROL_FAMILY_ORDER = (
    "config_metadata_only",
    "scale_only",
    "h_normalized_no_scale",
    "whitened_h_normalized_no_scale",
    "deterministic_random_projection",
    "rank_proxy_diagnostic",
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


@dataclass(frozen=True)
class NegativeWitnessRow:
    witness_id: str
    source_artifact: str
    source_pointer: str
    bedc_gap_field: str
    demotion_rule: str
    regression_test: str
    evidence_pointer: str
    status: str
    reason: str

    def to_record(self) -> dict[str, Any]:
        return {
            "witness_id": self.witness_id,
            "source_artifact": self.source_artifact,
            "source_pointer": self.source_pointer,
            "bedc_gap_field": self.bedc_gap_field,
            "demotion_rule": self.demotion_rule,
            "regression_test": self.regression_test,
            "evidence_pointer": self.evidence_pointer,
            "status": self.status,
            "reason": self.reason,
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
    features: np.ndarray,
    feature_columns: Sequence[str],
    declared_allowlist: Sequence[str] = H_ONLY_REPRESENTATION_SUMMARY_COLUMNS,
) -> None:
    feature_array = np.asarray(features, dtype=np.float64)
    if feature_array.ndim != 2:
        raise ValueError("features must be a two-dimensional matrix")
    actual = tuple(str(column) for column in feature_columns)
    declared = tuple(str(column) for column in declared_allowlist)
    if feature_array.shape[1] != len(declared):
        raise ValueError(
            "feature matrix width must exactly match declared h-only representation-summary allowlist"
        )
    if feature_array.shape[1] != len(actual):
        raise ValueError("feature matrix width must exactly match actual model input columns")
    if actual != declared:
        raise ValueError(
            "feature columns must exactly match declared h-only representation-summary allowlist"
        )
    hits = _forbidden_feature_hits(actual)
    if hits:
        raise ValueError(f"forbidden feature columns present: {', '.join(hits)}")


def _feature_contract_audit(features: np.ndarray, feature_columns: Sequence[str]) -> dict[str, Any]:
    feature_array = np.asarray(features, dtype=np.float64)
    try:
        assert_feature_matrix_contract(feature_array, feature_columns)
        return {
            "status": "pass",
            "declared_h_only_allowlist": list(H_ONLY_REPRESENTATION_SUMMARY_COLUMNS),
            "actual_model_input_columns": [str(column) for column in feature_columns],
            "actual_model_input_width": int(feature_array.shape[1]),
            "declared_h_only_width": len(H_ONLY_REPRESENTATION_SUMMARY_COLUMNS),
            "forbidden_feature_columns": list(FORBIDDEN_FEATURE_COLUMNS),
            "forbidden_present": [],
            "reason": "actual model input width and columns exactly match the declared h-only allowlist",
        }
    except ValueError as exc:
        return {
            "status": "fail",
            "declared_h_only_allowlist": list(H_ONLY_REPRESENTATION_SUMMARY_COLUMNS),
            "actual_model_input_columns": [str(column) for column in feature_columns],
            "actual_model_input_width": int(feature_array.shape[1]) if feature_array.ndim == 2 else None,
            "declared_h_only_width": len(H_ONLY_REPRESENTATION_SUMMARY_COLUMNS),
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
    seeds = tuple(
        int(seed)
        for seed in observed_debt._seeds(
            SOURCE_OBSERVED_DEBT_AXIS,
            observed_debt.DEFAULT_SEED_COUNT_BY_AXIS[SOURCE_OBSERVED_DEBT_AXIS],
        )
    )
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
    features = np.asarray(rows, dtype=np.float64)
    assert_feature_matrix_contract(features, feature_columns)
    return {
        "features": features,
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
    audit = _feature_contract_audit(matrix["features"], matrix["feature_columns"])
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
            "criterion": "actual model input width and columns equal the declared h-only representation-summary allowlist",
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
        surface_id="observed-debt-encoder-dim-grid",
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


def _sidecar_gate(root: Path, *, required: bool) -> dict[str, Any]:
    path = root / ANTI_TRIVIALITY_ARTIFACT
    if not required:
        return {
            "status": "source_only",
            "sidecar_status": None,
            "recommended_projection": None,
            "effective_level": BASE_LEVEL,
            "terminal_verdict": "source_pass",
            "downgrade_reason": None,
            "failed_gate": None,
            "reason": "anti-triviality sidecar has not been folded into this source snapshot",
        }
    if not path.exists():
        return {
            "status": "defer",
            "sidecar_status": None,
            "recommended_projection": None,
            "effective_level": "defer",
            "terminal_verdict": "incomplete",
            "downgrade_reason": None,
            "failed_gate": "$.dimension_mismatch_debt_transfer.anti_triviality_status",
            "reason": "anti-triviality sidecar is absent",
        }
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return {
            "status": "defer",
            "sidecar_status": None,
            "recommended_projection": None,
            "effective_level": "defer",
            "terminal_verdict": "incomplete",
            "downgrade_reason": None,
            "failed_gate": "$.dimension_mismatch_debt_transfer.anti_triviality_status",
            "reason": "anti-triviality sidecar is malformed",
        }
    if not isinstance(payload, dict):
        return {
            "status": "defer",
            "sidecar_status": None,
            "recommended_projection": None,
            "effective_level": "defer",
            "terminal_verdict": "incomplete",
            "downgrade_reason": None,
            "failed_gate": "$.dimension_mismatch_debt_transfer.anti_triviality_status",
            "reason": "anti-triviality sidecar is not a JSON object",
        }
    sidecar_status = payload.get("status")
    projection = payload.get("recommended_projection")
    controlled_geometry = _sidecar_controlled_geometry(root, payload)
    if sidecar_status in {"scale_leakage_detected", "metadata_leakage_detected"} and projection == "demote_to_DN_or_D1":
        return {
            "status": "pass",
            "sidecar_status": str(sidecar_status),
            "recommended_projection": str(projection),
            "effective_level": "DN",
            "terminal_verdict": "negative_discovery",
            "downgrade_reason": "scale_only_or_metadata_proxy_sufficient"
            if sidecar_status == "scale_leakage_detected"
            else "metadata_proxy_sufficient",
            "failed_gate": "$.dimension_mismatch_debt_transfer.anti_triviality_status",
            "reason": "anti-triviality sidecar recommends DN demotion",
            "controlled_geometry": controlled_geometry,
        }
    if (
        sidecar_status == "anti_triviality_passed"
        and projection == "no_level_change_signal_detected"
        and controlled_geometry["control_family_coverage"]["status"] == "pass"
    ):
        return {
            "status": "pass",
            "sidecar_status": str(sidecar_status),
            "recommended_projection": str(projection),
            "effective_level": BASE_LEVEL,
            "terminal_verdict": "source_pass",
            "downgrade_reason": None,
            "failed_gate": None,
            "reason": "anti-triviality sidecar does not recommend demotion",
            "controlled_geometry": controlled_geometry,
        }
    if sidecar_status == "anti_triviality_passed" and projection == "no_level_change_signal_detected":
        return {
            "status": "defer",
            "sidecar_status": str(sidecar_status),
            "recommended_projection": str(projection),
            "effective_level": "defer",
            "terminal_verdict": "incomplete",
            "downgrade_reason": None,
            "failed_gate": "$.dimension_mismatch_debt_transfer.anti_triviality_status",
            "reason": "anti-triviality pass is missing complete six-family controlled-geometry coverage",
            "controlled_geometry": controlled_geometry,
        }
    return {
        "status": "defer",
        "sidecar_status": sidecar_status if isinstance(sidecar_status, str) else None,
        "recommended_projection": projection if isinstance(projection, str) else None,
        "effective_level": "defer",
        "terminal_verdict": "incomplete",
        "downgrade_reason": None,
        "failed_gate": "$.dimension_mismatch_debt_transfer.anti_triviality_status",
        "reason": "anti-triviality sidecar status and recommended projection are not foldable",
        "controlled_geometry": controlled_geometry,
    }


def _sidecar_control_family_coverage(root: Path, payload: Mapping[str, Any]) -> dict[str, Any]:
    coverage = payload.get("controlled_geometry", {}).get("control_family_coverage") if isinstance(payload.get("controlled_geometry"), Mapping) else None
    if not isinstance(coverage, Mapping):
        return {
            "status": "defer",
            "required_families": list(CONTROL_FAMILY_ORDER),
            "resolved_families": [],
            "missing_families": list(CONTROL_FAMILY_ORDER),
            "malformed_families": [],
            "unknown_families": [],
            "family_pointers": {},
            "reason": "controlled-geometry control_family_coverage is missing or malformed",
        }
    family_pointers = coverage.get("family_pointers")
    required = tuple(str(item) for item in (coverage.get("required_families") or CONTROL_FAMILY_ORDER))
    observed = tuple(str(item) for item in (coverage.get("observed_families") or ()))
    if not isinstance(family_pointers, Mapping):
        family_pointers = {}
    resolved: list[str] = []
    malformed: list[str] = []
    for family in CONTROL_FAMILY_ORDER:
        pointer = family_pointers.get(family)
        value = (
            resolve_artifact_pointer(root, f"{ANTI_TRIVIALITY_ARTIFACT}:{pointer}")
            if isinstance(pointer, str) and pointer.startswith("$.")
            else None
        )
        if not isinstance(pointer, str) or not pointer.startswith("$."):
            malformed.append(family)
        elif isinstance(value, Mapping) and value.get("arm") == family:
            resolved.append(family)
        else:
            malformed.append(family)
    unknown = sorted(set(observed) - set(CONTROL_FAMILY_ORDER))
    missing = [family for family in CONTROL_FAMILY_ORDER if family not in resolved]
    status = (
        "pass"
        if coverage.get("status") == "pass"
        and required == CONTROL_FAMILY_ORDER
        and observed == CONTROL_FAMILY_ORDER
        and not missing
        and not malformed
        and not unknown
        else "defer"
    )
    return {
        "status": status,
        "source_status": coverage.get("status") if isinstance(coverage.get("status"), str) else None,
        "required_families": list(CONTROL_FAMILY_ORDER),
        "observed_families": list(observed),
        "resolved_families": resolved,
        "missing_families": missing,
        "malformed_families": malformed,
        "unknown_families": unknown,
        "family_pointers": {str(key): str(value) for key, value in family_pointers.items() if isinstance(value, str)},
        "reason": "all six control-family pointers resolve"
        if status == "pass"
        else "six-family controlled-geometry coverage is incomplete",
    }


def _sidecar_controlled_geometry(root: Path, payload: Mapping[str, Any]) -> dict[str, Any]:
    evidence_refs = payload.get("controlled_geometry", {}).get("evidence_refs") if isinstance(payload.get("controlled_geometry"), Mapping) else None
    coverage = _sidecar_control_family_coverage(root, payload)
    return {
        "artifact": ANTI_TRIVIALITY_ARTIFACT,
        "controlled_geometry_pointer": "$.controlled_geometry",
        "control_family_coverage_pointer": "$.controlled_geometry.control_family_coverage",
        "hardgates_pointer": "$.controlled_geometry_hardgates",
        "pointer_contract_pointer": "$.controlled_geometry_pointer_contract",
        "evidence_refs": [dict(row) for row in evidence_refs] if isinstance(evidence_refs, list) else [],
        "control_family_coverage": coverage,
    }


def _sidecar_anti_triviality_contract(sidecar: Mapping[str, Any], effective_level: str) -> dict[str, Any]:
    status = "pass" if sidecar.get("sidecar_status") == "anti_triviality_passed" else "fail"
    if sidecar.get("status") == "defer":
        status = "defer"
    failed_gate = sidecar.get("failed_gate")
    if status == "pass":
        failed_gate = None
    return owner_local_anti_triviality_contract(
        recommended_level=effective_level,
        scale_only_pointer="$.dimension_mismatch_debt_transfer.anti_triviality_status",
        metadata_only_pointer="$.dimension_mismatch_debt_transfer.anti_triviality_status",
        matched_random_pointer="$.control_protocol",
        forbidden_column_pointer="$.representation_boundary.actual_model_input_columns",
        status=status,
        failed_gate=failed_gate,
    )


def build_negative_witness_rows(payload: Mapping[str, Any], root: Path) -> tuple[NegativeWitnessRow, ...]:
    transfer = payload.get("dimension_mismatch_debt_transfer")
    if not isinstance(transfer, Mapping):
        return ()
    source_artifact = ANTI_TRIVIALITY_ARTIFACT
    source_pointer = "$.status"
    evidence_pointer = "$.controlled_geometry.feature_partition"
    regression_test = NEGATIVE_WITNESS_TEST_POINTER
    source_value = resolve_artifact_pointer(root, f"{source_artifact}:{source_pointer}")
    evidence_value = resolve_artifact_pointer(root, f"{source_artifact}:{evidence_pointer}")
    status = str(source_value) if isinstance(source_value, str) else None
    projection = transfer.get("anti_triviality_projection")
    active = status == "scale_leakage_detected" and projection == "demote_to_DN_or_D1"
    source_resolved = source_value is not None
    evidence_resolved = evidence_value is not None
    return (
        NegativeWitnessRow(
            witness_id="scale_leakage_witness",
            source_artifact=source_artifact,
            source_pointer=source_pointer,
            bedc_gap_field="representation_scale_leakage",
            demotion_rule="demote_to_DN_or_D1",
            regression_test=regression_test,
            evidence_pointer=f"{source_artifact}:{evidence_pointer}",
            status="valid" if active and source_resolved and evidence_resolved else "blocked",
            reason="scale-only anti-triviality evidence demotes the debt-transfer claim"
            if active and source_resolved and evidence_resolved
            else "scale leakage witness source or evidence pointer is not foldable",
        ),
    )


def negative_witness_hardgates(rows: Sequence[NegativeWitnessRow], root: Path) -> dict[str, Any]:
    row_records = [row.to_record() for row in rows]
    required_fields = (
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
    rows_well_formed = bool(row_records) and all(
        all(record.get(field) not in (None, "") for field in required_fields)
        for record in row_records
    )
    source_resolutions = {
        row.witness_id: resolve_artifact_pointer(root, f"{row.source_artifact}:{row.source_pointer}") is not None
        for row in rows
    }
    regression_source = {"run_local": {"test_artifact": NEGATIVE_WITNESS_TEST_ARTIFACT}}
    regression_resolutions = {
        row.witness_id: (
            pointer_value(regression_source, row.regression_test) is not None
            if row.regression_test.startswith("$.")
            else resolve_artifact_pointer(root, row.regression_test) is not None
        )
        for row in rows
    }
    evidence_resolutions = {
        row.witness_id: resolve_artifact_pointer(root, row.evidence_pointer) is not None
        for row in rows
    }
    valid_coverage_count = sum(
        1
        for row in rows
        if row.status == "valid"
        and bool(source_resolutions.get(row.witness_id))
        and bool(regression_resolutions.get(row.witness_id))
        and bool(evidence_resolutions.get(row.witness_id))
    )
    no_terminal_verdict = "terminal_verdict" not in {
        key
        for record in row_records
        for key in _recursive_keys(record)
    }
    return {
        "NW-HG1": {
            "status": "pass" if rows_well_formed else "fail",
            "criterion": "negative witness rows use the required local projection fields",
            "row_count": len(row_records),
            "required_fields": list(required_fields),
            "reason": "all negative witness rows are well formed"
            if rows_well_formed
            else "negative witness row set is empty or missing required fields",
        },
        "NW-HG2": {
            "status": "pass"
            if row_records
            and all(source_resolutions.values())
            and all(regression_resolutions.values())
            and all(evidence_resolutions.values())
            else "fail",
            "criterion": "source, evidence, and regression-test pointers resolve inside declared artifacts",
            "source_resolves": source_resolutions,
            "regression_test_resolves": regression_resolutions,
            "evidence_resolves": evidence_resolutions,
            "valid_coverage_count": valid_coverage_count,
            "reason": "all negative witness pointers resolve"
            if row_records
            and all(source_resolutions.values())
            and all(regression_resolutions.values())
            and all(evidence_resolutions.values())
            else "one or more negative witness pointers are dangling",
        },
        "NW-HG3": {
            "status": "pass" if no_terminal_verdict else "fail",
            "criterion": "negative witness projection emits evidence fields only",
            "reason": "negative witness rows do not emit terminal verdict fields"
            if no_terminal_verdict
            else "negative witness rows emitted terminal verdict fields",
        },
    }


def scale_leakage_bedc_gap_mapping(root: Path = ROOT) -> dict[str, str]:
    witness = resolve_artifact_pointer(root, SCALE_LEAKAGE_WITNESS_POINTER)
    if not isinstance(witness, Mapping):
        raise ValueError(f"scale leakage witness pointer does not resolve: {SCALE_LEAKAGE_WITNESS_POINTER}")
    cell = {
        "witness_pointer": SCALE_LEAKAGE_WITNESS_POINTER,
        "bedc_gap_field": witness.get("bedc_gap_field"),
        "demotion_rule": witness.get("demotion_rule"),
        "regression_test": witness.get("regression_test"),
    }
    missing = [key for key in BEDC_GAP_MAPPING_KEYS if not isinstance(cell.get(key), str) or not cell[key]]
    if missing:
        raise ValueError(f"scale leakage BEDC gap mapping missing cells: {', '.join(missing)}")
    return {key: str(cell[key]) for key in BEDC_GAP_MAPPING_KEYS}


def _recursive_keys(value: Any):
    if isinstance(value, Mapping):
        for key, item in value.items():
            yield key
            yield from _recursive_keys(item)
    elif isinstance(value, list):
        for item in value:
            yield from _recursive_keys(item)


def build_payload(
    *,
    root: Path = ROOT,
    generated_at: str | None = None,
    require_anti_triviality: bool = True,
) -> dict[str, Any]:
    matrix = _surface_matrix()
    fold_records = [
        _fold_record(matrix, fold_seed=int(seed), fold_index=index)
        for index, seed in enumerate(matrix["seeds"])
    ]
    result = _result(matrix, fold_records)
    status = result.status
    pass_count = 1 if status == "pass" else 0
    source_level = result.discovery_level
    sidecar = _sidecar_gate(root, required=require_anti_triviality) if status == "pass" else {
        "status": "source_failed",
        "sidecar_status": None,
        "recommended_projection": None,
        "effective_level": source_level,
        "terminal_verdict": "source_failed",
        "downgrade_reason": None,
        "failed_gate": TRANSFER_STATUS_POINTER,
        "reason": "source hardgate failure blocks anti-triviality folding",
    }
    effective_level = str(sidecar["effective_level"]) if status == "pass" else source_level
    terminal_verdict = str(sidecar["terminal_verdict"])
    downgrade_reason = sidecar["downgrade_reason"]
    anti_triviality_contract = _sidecar_anti_triviality_contract(sidecar, effective_level)
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
            "base_level": BASE_LEVEL,
            "anti_triviality_status": sidecar["sidecar_status"],
            "anti_triviality_projection": sidecar["recommended_projection"],
            "anti_triviality_fold_status": sidecar["status"],
            "anti_triviality_fold_reason": sidecar["reason"],
            "effective_level": effective_level,
            "downgrade_reason": downgrade_reason,
            "terminal_verdict": terminal_verdict,
            "discovery_level": effective_level,
            "pass_surface_count": pass_count,
            "total_surface_count": 1,
            "discovery_map_pointer": EFFECTIVE_LEVEL_POINTER,
            "hypothesis": "h-summary dimension-mismatch debt transfer remains non-trivial after metadata and scale controls",
            "failed_gate": sidecar["failed_gate"],
            "what_was_learned": sidecar["reason"],
            "not_claimed": [
                "global dimension theory",
                "representation-geometric debt transfer",
                "D5 promotion",
            ],
            "anti_triviality_evidence": {
                "artifact": ANTI_TRIVIALITY_ARTIFACT,
                "status_pointer": "$.status",
                "recommended_projection_pointer": "$.recommended_projection",
                "controlled_geometry_pointer": "$.controlled_geometry",
                "controlled_geometry_hardgates_pointer": "$.controlled_geometry_hardgates",
                "controlled_geometry_pointer_contract_pointer": "$.controlled_geometry_pointer_contract",
                "controlled_geometry": dict(sidecar.get("controlled_geometry", {}))
                if isinstance(sidecar.get("controlled_geometry"), Mapping)
                else {},
            },
            **anti_triviality_contract,
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
            "projection": effective_level,
            "failed_gates": [
                name for name, gate in result.hardgates.items() if gate["status"] != "pass"
            ],
            "d5_shortcut": False,
            "scope": DEFAULT_SCOPE,
            "base_level": BASE_LEVEL,
            "effective_level": effective_level,
            "terminal_verdict": terminal_verdict,
            "downgrade_reason": downgrade_reason,
            "reason": sidecar["reason"],
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
            f"| base level | `{transfer['base_level']}` | `$.dimension_mismatch_debt_transfer.base_level` |",
            f"| anti-triviality status | `{transfer['anti_triviality_status']}` | `$.dimension_mismatch_debt_transfer.anti_triviality_status` |",
            f"| effective level | `{transfer['effective_level']}` | `{EFFECTIVE_LEVEL_POINTER}` |",
            f"| terminal verdict | `{transfer['terminal_verdict']}` | `$.dimension_mismatch_debt_transfer.terminal_verdict` |",
            f"| scope | `{transfer['scope']}` | `$.dimension_mismatch_debt_transfer.scope` |",
            "",
            "## Not claimed",
            "",
        ]
    )
    for item in payload["not_claimed"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def _run_local_artifact_bundle() -> dict[str, str]:
    return {
        "claim_capsule": RUN_LOCAL_CLAIM_CAPSULE_ARTIFACT,
        "raw_metrics": RUN_LOCAL_RAW_METRICS_ARTIFACT,
        "summary": RUN_LOCAL_SUMMARY_ARTIFACT,
        "report": RUN_LOCAL_REPORT_ARTIFACT,
    }


def build_run_local_contract(payload: Mapping[str, Any], root: Path = ROOT) -> dict[str, Any]:
    transfer = payload["dimension_mismatch_debt_transfer"]
    anti = transfer["anti_triviality_evidence"]
    sidecar_refs = anti.get("controlled_geometry", {}).get("evidence_refs")
    negative_witness_rows = build_negative_witness_rows(payload, root)
    evidence_refs = [
        {
            "evidence_id": "canonical-claim",
            "artifact": JSON_ARTIFACT,
            "source_artifact": JSON_ARTIFACT,
            "source_pointer": "$.dimension_mismatch_debt_transfer",
        },
        {
            "evidence_id": "boundary-ledger",
            "artifact": JSON_ARTIFACT,
            "source_artifact": JSON_ARTIFACT,
            "source_pointer": "$.boundary_ledger",
        },
    ]
    if isinstance(sidecar_refs, list):
        evidence_refs.extend(dict(row) for row in sidecar_refs)
    negative_witness = [row.to_record() for row in negative_witness_rows]
    return {
        "projection_kind": "dimension_mismatch_debt_transfer_run_local",
        "source_artifact": JSON_ARTIFACT,
        "source_pointer": "$.dimension_mismatch_debt_transfer",
        "controlled_geometry_artifact": ANTI_TRIVIALITY_ARTIFACT,
        "controlled_geometry_pointer": "$.controlled_geometry",
        "artifact_bundle": _run_local_artifact_bundle(),
        "evidence_refs": evidence_refs,
        "negative_witness": negative_witness,
        "negative_witness_hardgates": negative_witness_hardgates(negative_witness_rows, root),
        "test_artifact": NEGATIVE_WITNESS_TEST_ARTIFACT,
        "owner": "claim:dimension-mismatch-debt-transfer",
    }


def build_run_local_claim_capsule(payload: Mapping[str, Any], root: Path = ROOT) -> dict[str, Any]:
    transfer = payload["dimension_mismatch_debt_transfer"]
    return {
        "schema_id": "bedc.quality.claim_capsule",
        "artifact_id": "bedc-quality-lab:dimension-mismatch-debt-transfer-claim-capsule",
        "json_artifact": RUN_LOCAL_CLAIM_CAPSULE_ARTIFACT,
        "generated_at": payload["generated_at"],
        "producer": "scripts/run_dimension_mismatch_debt_transfer.py",
        "claim_id": "claim:dimension-mismatch-debt-transfer",
        "report": RUN_LOCAL_REPORT_ARTIFACT,
        "source": JSON_ARTIFACT,
        "source_pointer": "$.dimension_mismatch_debt_transfer",
        "status": "complete" if transfer["status"] == "pass" else "incomplete",
        "base_level": transfer["base_level"],
        "anti_triviality_status": transfer["anti_triviality_status"],
        "effective_level": transfer["effective_level"],
        "downgrade_reason": transfer["downgrade_reason"],
        "terminal_verdict": transfer["terminal_verdict"],
        "hypothesis": transfer["hypothesis"],
        "failed_gate": transfer["failed_gate"],
        "what_was_learned": transfer["what_was_learned"],
        "run_local": build_run_local_contract(payload, root),
        "not_claimed": list(payload["not_claimed"]),
    }


def build_run_local_raw_metrics(payload: Mapping[str, Any], root: Path = ROOT) -> tuple[dict[str, Any], ...]:
    contract = build_run_local_contract(payload, root)
    rows = []
    for row in contract["evidence_refs"]:
        rows.append(
            {
                "metric": str(row["evidence_id"]),
                "source_artifact": str(row["source_artifact"]),
                "source_pointer": str(row["source_pointer"]),
            }
        )
    for index, row in enumerate(contract["negative_witness"]):
        rows.append(
            {
                "metric": str(row["witness_id"]),
                "source_artifact": RUN_LOCAL_CLAIM_CAPSULE_ARTIFACT,
                "source_pointer": f"$.run_local.negative_witness[{index}]",
            }
        )
    return tuple(rows)


def build_run_local_summary(payload: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "artifact_id": "bedc-quality-lab:dimension-mismatch-debt-transfer-run-summary",
        "generated_at": payload["generated_at"],
        "producer": "scripts/run_dimension_mismatch_debt_transfer.py",
        "claim_capsule_ref": {
            "artifact": RUN_LOCAL_CLAIM_CAPSULE_ARTIFACT,
            "pointer": "$.run_local",
        },
        "artifact_bundle": _run_local_artifact_bundle(),
        "negative_witness_ref": {
            "artifact": RUN_LOCAL_CLAIM_CAPSULE_ARTIFACT,
            "pointer": "$.run_local.negative_witness",
        },
        "negative_witness_hardgates_ref": {
            "artifact": RUN_LOCAL_CLAIM_CAPSULE_ARTIFACT,
            "pointer": "$.run_local.negative_witness_hardgates",
        },
    }


def render_run_local_markdown(payload: Mapping[str, Any], root: Path = ROOT) -> str:
    transfer = payload["dimension_mismatch_debt_transfer"]
    rows = build_negative_witness_rows(payload, root)
    lines = [
        "# Dimension-Mismatch Debt Transfer Claim Capsule",
        "",
        f"- Source artifact: `{JSON_ARTIFACT}`",
        "- Source pointer: `$.dimension_mismatch_debt_transfer`",
        f"- Controlled geometry artifact: `{ANTI_TRIVIALITY_ARTIFACT}`",
        "- Controlled geometry pointer: `$.controlled_geometry`",
        f"- Claim capsule pointer: `{RUN_LOCAL_CLAIM_CAPSULE_ARTIFACT}:$.run_local`",
        f"- Status: `{transfer['status']}`",
        f"- Effective level: `{transfer['effective_level']}`",
        "",
        "## Negative Witness Pointers",
        "",
        "| witness | owner pointer | source pointer | regression pointer |",
        "| --- | --- | --- | --- |",
    ]
    for index, row in enumerate(rows):
        lines.append(
            f"| `{row.witness_id}` | "
            f"`$.run_local.negative_witness[{index}]` | "
            f"`{row.source_artifact}:{row.source_pointer}` | "
            f"`{row.regression_test}` |"
        )
    lines.append("")
    return "\n".join(
        lines
    )


def _write_json_atomic(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    tmp.replace(path)


def _write_jsonl_atomic(path: Path, rows: Sequence[Mapping[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text("".join(json.dumps(row, sort_keys=True) + "\n" for row in rows), encoding="utf-8")
    tmp.replace(path)


def _write_text_atomic(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(text, encoding="utf-8")
    tmp.replace(path)


def write_dimension_mismatch_debt_transfer(
    *,
    root: Path = ROOT,
    generated_at: str | None = None,
    require_anti_triviality: bool = True,
) -> dict[str, Any]:
    payload = build_payload(root=root, generated_at=generated_at, require_anti_triviality=require_anti_triviality)
    json_path = root / JSON_ARTIFACT
    report_path = root / REPORT_ARTIFACT
    _write_json_atomic(json_path, payload)
    _write_text_atomic(report_path, render_markdown(payload))
    _write_json_atomic(root / RUN_LOCAL_CLAIM_CAPSULE_ARTIFACT, build_run_local_claim_capsule(payload, root))
    _write_jsonl_atomic(root / RUN_LOCAL_RAW_METRICS_ARTIFACT, build_run_local_raw_metrics(payload, root))
    _write_json_atomic(root / RUN_LOCAL_SUMMARY_ARTIFACT, build_run_local_summary(payload))
    _write_text_atomic(root / RUN_LOCAL_REPORT_ARTIFACT, render_run_local_markdown(payload, root))
    return payload


def main() -> None:
    payload = write_dimension_mismatch_debt_transfer()
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

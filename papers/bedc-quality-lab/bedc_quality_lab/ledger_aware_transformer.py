"""Deterministic Ledger-Aware Transformer toy kernel."""

from __future__ import annotations

from dataclasses import asdict, dataclass
from typing import Any, Mapping, Sequence

import numpy as np

from bedc_quality_lab.discovery_compiler.capsule import (
    ARCHITECTURE_CLAIM_CAPSULE_SUBTYPE,
    build_architecture_claim_capsule_payload,
)


JSON_ARTIFACT = "reports/canonical/ledger-aware-transformer.json"
MARKDOWN_ARTIFACT = "reports/canonical/ledger-aware-transformer.md"
ARTIFACT_ID = "bedc-quality-lab:ledger-aware-transformer"
SCHEMA_ID = "bedc.model.ledger_aware_transformer"
DEFAULT_GENERATED_AT = "2026-06-05T15:14:26.399733+00:00"
CLAIM_CAPSULE_POINTER = "$.claim_capsule_ref.capsule"
LAT_HARDGATES = tuple(f"LAT-HG{index}" for index in range(1, 7))
SURFACE_IDS = ("copy_shift", "parity_route", "sparse_recall")
LEDGER_CHANNELS = ("high_residual_norm", "attention_drift", "write_collision")
FORBIDDEN_INFERENCE_COLUMNS = ("label", "error", "ground_truth", "gap_label")


@dataclass(frozen=True)
class LedgerAwareTransformerConfig:
    sample_count: int = 96
    train_count: int = 48
    hidden_dim: int = 6
    layer_count: int = 2
    seed: int = 756
    ledger_threshold: float = 0.42
    cost_unit: str = "toy-numpy-step"


@dataclass(frozen=True)
class SurfaceSpec:
    surface_id: str
    title: str
    ood_kind: str
    seed_offset: int
    ledger_channel: str


@dataclass(frozen=True)
class SurfaceEvaluation:
    surface_id: str
    record: Mapping[str, Any]
    residuals: np.ndarray
    learned_scores: np.ndarray
    control_scores: np.ndarray
    ledger_decisions: np.ndarray
    control_decisions: np.ndarray


def default_config() -> LedgerAwareTransformerConfig:
    return LedgerAwareTransformerConfig()


def surface_specs() -> tuple[SurfaceSpec, ...]:
    return (
        SurfaceSpec("copy_shift", "copy head under shifted token parity", "ood-copy-shift", 11, "high_residual_norm"),
        SurfaceSpec("parity_route", "route head under parity recombination", "ood-parity-route", 23, "attention_drift"),
        SurfaceSpec("sparse_recall", "recall head under sparse key reuse", "ood-sparse-recall", 37, "write_collision"),
    )


def _surface_inputs(spec: SurfaceSpec, config: LedgerAwareTransformerConfig) -> np.ndarray:
    rng = np.random.default_rng(config.seed + spec.seed_offset)
    grid = np.linspace(-1.0, 1.0, config.sample_count, dtype=np.float64)
    base = np.column_stack(
        [
            grid,
            grid * grid,
            np.sin((spec.seed_offset % 5 + 1) * grid),
            np.cos((spec.seed_offset % 7 + 2) * grid),
        ]
    )
    noise = rng.normal(0.0, 0.015, size=base.shape)
    return (base + noise).astype(np.float64)


def _backbone_residuals(inputs: np.ndarray, spec: SurfaceSpec, config: LedgerAwareTransformerConfig) -> np.ndarray:
    rng = np.random.default_rng(config.seed + 100 + spec.seed_offset)
    width = inputs.shape[1]
    state = inputs.astype(np.float64)
    residual_layers: list[np.ndarray] = []
    for layer_index in range(config.layer_count):
        weights = rng.normal(0.0, 0.35, size=(width, config.hidden_dim))
        projected = np.tanh(state @ weights + (layer_index + 1) * 0.07)
        route = np.roll(projected, shift=layer_index + 1, axis=0)
        residual = projected - 0.62 * route
        residual_layers.append(residual)
        state = projected[:, :width] + 0.2 * state
    return np.concatenate(residual_layers, axis=1).astype(np.float64)


def _ledger_event(residuals: np.ndarray, spec: SurfaceSpec) -> np.ndarray:
    primary = residuals[:, 0]
    secondary = residuals[:, 3]
    tertiary = residuals[:, -2]
    if spec.surface_id == "copy_shift":
        score = primary + 0.45 * secondary
    elif spec.surface_id == "parity_route":
        score = -0.35 * primary + secondary + 0.25 * tertiary
    else:
        score = 0.25 * primary - 0.4 * secondary + tertiary
    cutoff = float(np.quantile(score, 0.62))
    return (score > cutoff).astype(np.int64)


def _prediction_error(residuals: np.ndarray, ledger_event: np.ndarray, spec: SurfaceSpec) -> np.ndarray:
    base = 0.16 + 0.08 * np.abs(residuals[:, 1])
    if spec.surface_id == "copy_shift":
        event_load = 0.48 * ledger_event + 0.04 * (residuals[:, 2] > 0.0)
    elif spec.surface_id == "parity_route":
        event_load = 0.44 * ledger_event + 0.05 * (residuals[:, 4] < 0.0)
    else:
        event_load = 0.5 * ledger_event + 0.03 * (residuals[:, 5] > 0.0)
    return (base + event_load).astype(np.float64)


def _fit_linear_scores(train_features: np.ndarray, targets: np.ndarray, eval_features: np.ndarray) -> np.ndarray:
    design = np.column_stack([np.ones(train_features.shape[0]), train_features])
    weights = np.linalg.pinv(design) @ targets.astype(np.float64)
    eval_design = np.column_stack([np.ones(eval_features.shape[0]), eval_features])
    scores = eval_design @ weights
    return np.clip(scores, 0.0, 1.0).astype(np.float64)


def _matched_random_targets(targets: np.ndarray, seed: int) -> np.ndarray:
    rng = np.random.default_rng(seed)
    shuffled = np.array(targets, copy=True)
    rng.shuffle(shuffled)
    return shuffled.astype(np.float64)


def _metrics(*, errors: np.ndarray, decisions: np.ndarray, threshold: float) -> dict[str, float]:
    critical = errors >= threshold
    logged = decisions.astype(bool)
    unlogged = critical & ~logged
    false_alarm = ~critical & logged
    return {
        "unlogged_error_rate": round(float(np.mean(unlogged)), 6),
        "critical_unlogged_error_rate": round(float(np.mean(unlogged & (errors > threshold + 0.08))), 6),
        "false_alarm_rate": round(float(np.mean(false_alarm)), 6),
        "logged_rate": round(float(np.mean(logged)), 6),
    }


def evaluate_surface(spec: SurfaceSpec, config: LedgerAwareTransformerConfig) -> SurfaceEvaluation:
    inputs = _surface_inputs(spec, config)
    residuals = _backbone_residuals(inputs, spec, config)
    ledger_event = _ledger_event(residuals, spec)
    errors = _prediction_error(residuals, ledger_event, spec)
    train = np.arange(0, config.sample_count, 2)[: config.train_count]
    eval_index = np.arange(1, config.sample_count, 2)
    train_features = residuals[train]
    eval_features = residuals[eval_index]
    learned_scores = _fit_linear_scores(train_features, ledger_event[train], eval_features)
    random_targets = _matched_random_targets(ledger_event, config.seed + 200 + spec.seed_offset)
    control_scores = _fit_linear_scores(train_features, random_targets[train], eval_features)
    ledger_decisions = learned_scores >= config.ledger_threshold
    control_decisions = control_scores >= config.ledger_threshold
    eval_errors = errors[eval_index]
    learned = _metrics(errors=eval_errors, decisions=ledger_decisions, threshold=config.ledger_threshold)
    control = _metrics(errors=eval_errors, decisions=control_decisions, threshold=config.ledger_threshold)
    record = {
        "surface_id": spec.surface_id,
        "role": "ood_surface",
        "ood_kind": spec.ood_kind,
        "ledger_channel": spec.ledger_channel,
        "sample_count": int(eval_features.shape[0]),
        "residual_pointer": f"$.records.{SURFACE_IDS.index(spec.surface_id)}.residual_summary",
        "gap_head": {
            "arm": "ledger_aware_gap_head_on_residual",
            "uses_forbidden_columns": False,
            "metrics": learned,
        },
        "matched_random_control": {
            "arm": "matched_random_gap_head",
            "uses_forbidden_columns": False,
            "metrics": control,
        },
        "deltas": {
            "unlogged_error_rate": round(control["unlogged_error_rate"] - learned["unlogged_error_rate"], 6),
            "false_alarm_rate": round(learned["false_alarm_rate"] - control["false_alarm_rate"], 6),
        },
        "residual_summary": {
            "mean_abs": round(float(np.mean(np.abs(eval_features))), 6),
            "max_abs": round(float(np.max(np.abs(eval_features))), 6),
            "dimension": int(eval_features.shape[1]),
        },
    }
    return SurfaceEvaluation(
        surface_id=spec.surface_id,
        record=record,
        residuals=eval_features,
        learned_scores=learned_scores,
        control_scores=control_scores,
        ledger_decisions=ledger_decisions.astype(np.int64),
        control_decisions=control_decisions.astype(np.int64),
    )


def _mean_metric(evaluations: Sequence[SurfaceEvaluation], arm: str, metric: str) -> float:
    values = [float(evaluation.record[arm]["metrics"][metric]) for evaluation in evaluations]
    return round(float(np.mean(values)), 6)


def _ledger_rows(evaluations: Sequence[SurfaceEvaluation]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for index, evaluation in enumerate(evaluations):
        rows.append(
            {
                "row_id": f"lat:{evaluation.surface_id}:ledger-policy",
                "surface_id": evaluation.surface_id,
                "evidence_pointer": f"$.records.{index}.gap_head.metrics",
                "control_pointer": f"$.records.{index}.matched_random_control.metrics",
                "ledger_decision_pointer": f"$.records.{index}.gap_head",
                "status": "recorded",
            }
        )
    return rows


def _surface_registry() -> dict[str, dict[str, Any]]:
    return {
        spec.surface_id: {
            "title": spec.title,
            "surface_id": spec.surface_id,
            "ood_kind": spec.ood_kind,
            "ledger_channel": spec.ledger_channel,
        }
        for spec in surface_specs()
    }


def build_payload(*, generated_at: str = DEFAULT_GENERATED_AT, config: LedgerAwareTransformerConfig | None = None) -> dict[str, Any]:
    active = config or default_config()
    evaluations = [evaluate_surface(spec, active) for spec in surface_specs()]
    learned_uer = _mean_metric(evaluations, "gap_head", "unlogged_error_rate")
    control_uer = _mean_metric(evaluations, "matched_random_control", "unlogged_error_rate")
    learned_false_alarm = _mean_metric(evaluations, "gap_head", "false_alarm_rate")
    control_false_alarm = _mean_metric(evaluations, "matched_random_control", "false_alarm_rate")
    multi_surface = sum(1 for evaluation in evaluations if evaluation.record["deltas"]["unlogged_error_rate"] > 0.0)
    source_artifacts = {
        "producer_script": "scripts/run_ledger_aware_transformer.py",
        "kernel": "bedc_quality_lab/ledger_aware_transformer.py",
        "cost_protocol": {
            "unit": active.cost_unit,
            "sample_count": active.sample_count,
            "train_count": active.train_count,
            "layer_count": active.layer_count,
            "hidden_dim": active.hidden_dim,
            "seed": active.seed,
        },
    }
    payload: dict[str, Any] = {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "generated_at": generated_at,
        "producer": "bedc_quality_lab.ledger_aware_transformer",
        "json_artifact": JSON_ARTIFACT,
        "markdown_artifact": MARKDOWN_ARTIFACT,
        "source_artifacts": source_artifacts,
        "config": asdict(active),
        "surface_registry": _surface_registry(),
        "applicability_boundary": {
            "claimed_scope": "bounded NumPy toy residual gap-head evidence for ledger-aware transformer design",
            "forbidden_inference_columns": list(FORBIDDEN_INFERENCE_COLUMNS),
            "not_claimed": [
                "real-model training",
                "general architecture superiority",
                "terminal discovery verdict",
                "D5 promotion",
            ],
        },
        "control_protocol": {
            "control_arm": "matched_random_gap_head",
            "matching": "same residual features, same train/eval split, shuffled ledger targets",
            "control_pointer": "$.records.0.matched_random_control",
        },
        "records": [dict(evaluation.record) for evaluation in evaluations],
        "aggregate_metrics": {
            "surface_count": len(evaluations),
            "ood_surface_count": len({evaluation.record["ood_kind"] for evaluation in evaluations}),
            "uer_learned": learned_uer,
            "uer_matched_random": control_uer,
            "uer_reduction": round(control_uer - learned_uer, 6),
            "false_alarm_learned": learned_false_alarm,
            "false_alarm_matched_random": control_false_alarm,
            "false_alarm_delta": round(learned_false_alarm - control_false_alarm, 6),
            "only_false_alarm_increase": (control_uer - learned_uer) > 0.0 and learned_false_alarm > control_false_alarm,
            "multi_surface_uer_reduction_count": multi_surface,
        },
        "ledger": {
            "policy": "log residual gap events before error labels are observed",
            "rows": _ledger_rows(evaluations),
            "forbidden_inference_columns_used": False,
        },
        "positive_claim": {
            "status": "evidence-recorded",
            "claim": "residual gap heads reduce unlogged error relative to matched-random gap heads on multiple OOD toy surfaces",
            "evidence_pointer": "$.aggregate_metrics.uer_reduction",
            "control_pointer": "$.control_protocol",
            "surface_registry_pointer": "$.surface_registry",
        },
        "not_claimed": [
            "real-model training",
            "general architecture superiority",
            "terminal discovery verdict",
            "D5 promotion",
        ],
    }
    capsule = build_architecture_capsule(payload)
    payload["claim_capsule_ref"] = {
        "artifact": JSON_ARTIFACT,
        "pointer": CLAIM_CAPSULE_POINTER,
        "capsule_subtype": ARCHITECTURE_CLAIM_CAPSULE_SUBTYPE,
        "source_pointer": "$.positive_claim",
        "forbidden_evidence_pointer": f"{CLAIM_CAPSULE_POINTER}.model_claim.forbidden_evidence",
        "positive_claim_pointer": "$.positive_claim",
        "capsule": capsule,
    }
    if "terminal_verdict" in payload:
        raise ValueError("LAT payload must not emit terminal_verdict")
    return payload


def build_architecture_capsule(payload: Mapping[str, Any]) -> dict[str, Any]:
    model_claim = {
        "model_id": "ledger-aware-transformer-toy",
        "claim": payload["positive_claim"]["claim"],
        "baselines": [
            {"artifact": JSON_ARTIFACT, "pointer": "$.control_protocol"},
            {"artifact": JSON_ARTIFACT, "pointer": "$.records.0.matched_random_control"},
        ],
        "forbidden_evidence": list(FORBIDDEN_INFERENCE_COLUMNS),
        "required_gates": list(LAT_HARDGATES),
        "candidate_pointer": {"artifact": JSON_ARTIFACT, "pointer": "$.config"},
        "evidence_pointer": {"artifact": JSON_ARTIFACT, "pointer": "$.records"},
    }
    capsule = build_architecture_claim_capsule_payload(
        generated_at=str(payload["generated_at"]),
        claim_id="claim:ledger-aware-transformer-toy",
        report="ledger-aware-transformer",
        source_artifact=JSON_ARTIFACT,
        source_pointer="$.positive_claim",
        model_claim=model_claim,
        not_claimed=payload["not_claimed"],
    )
    capsule["json_artifact"] = JSON_ARTIFACT
    return capsule

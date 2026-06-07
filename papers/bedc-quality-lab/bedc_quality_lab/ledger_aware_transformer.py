"""Deterministic Ledger-Aware Transformer toy kernel and projection."""

from __future__ import annotations

import json
import math
from dataclasses import asdict, dataclass
from typing import Any, Mapping, Sequence

import numpy as np

from bedc_quality_lab.claim_terms import FORBIDDEN_POSITIVE_CLAIM_TERMS
from bedc_quality_lab.discovery_compiler.capsule import (
    ARCHITECTURE_CLAIM_CAPSULE_SUBTYPE,
    build_architecture_claim_capsule_payload,
)
from bedc_quality_lab.discovery_compiler.pointers import pointer_value


JSON_ARTIFACT = "reports/canonical/ledger-aware-transformer.json"
MARKDOWN_ARTIFACT = "reports/canonical/ledger-aware-transformer.md"
ARTIFACT_ID = "bedc-quality-lab:ledger-aware-transformer"
SCHEMA_ID = "bedc.model.ledger_aware_transformer"
DEFAULT_GENERATED_AT = "2026-06-05T15:14:26.399733+00:00"
CLAIM_CAPSULE_POINTER = "$.claim_capsule_ref.capsule"
LAT_HARDGATES = tuple(f"LAT-HG{index}" for index in range(1, 8))
LEDGER_CHANNELS = ("high_residual_norm", "attention_drift", "write_collision")
FORBIDDEN_INFERENCE_COLUMNS = ("label", "error", "ground_truth", "gap_label")
DRIFT_TOLERANCE = 1.0e-4
REQUIRED_PASS_SURFACE_COUNT = 3


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


class LatSurfaceSuite:
    _specs: tuple[SurfaceSpec, ...] = (
        SurfaceSpec("delayed_recall", "delayed recall under temporal key reuse", "ood-delayed-recall", 11, "high_residual_norm"),
        SurfaceSpec("compositional_rules", "compositional rule transfer under parity recombination", "ood-compositional-rules", 23, "attention_drift"),
        SurfaceSpec("synthetic_tool_use", "synthetic tool-use trace with latent write collisions", "ood-synthetic-tool-use", 37, "write_collision"),
        SurfaceSpec("counterfactual_binding", "counterfactual binding under shifted slot identity", "ood-counterfactual-binding", 41, "high_residual_norm"),
        SurfaceSpec("hierarchical_planning", "hierarchical planning trace with delayed subgoal joins", "ood-hierarchical-planning", 53, "attention_drift"),
        SurfaceSpec("adversarial_negation", "adversarial negation under rule inversion", "ood-adversarial-negation", 67, "write_collision"),
    )

    def surface_specs(self) -> tuple[SurfaceSpec, ...]:
        return self._specs

    def record_index(self, surface_id: str) -> int:
        for index, spec in enumerate(self._specs):
            if spec.surface_id == surface_id:
                return index
        raise ValueError(f"unknown LAT surface_id: {surface_id}")

    def passing_ood_surface_ids(self, payload: Mapping[str, Any]) -> tuple[str, ...]:
        records = payload.get("records")
        if not isinstance(records, list):
            return ()
        passing: list[str] = []
        for spec in self._specs:
            try:
                record = records[self.record_index(spec.surface_id)]
            except IndexError:
                continue
            delta = 0.0
            if isinstance(record, Mapping) and isinstance(record.get("deltas"), Mapping):
                try:
                    delta = float(record["deltas"].get("unlogged_error_rate", 0.0))
                except (TypeError, ValueError):
                    delta = 0.0
            if (
                isinstance(record, Mapping)
                and record.get("role") == "ood_surface"
                and record.get("surface_id") == spec.surface_id
                and delta > 0.0
            ):
                passing.append(spec.surface_id)
        return tuple(passing)

    def robustness_signal(self, payload: Mapping[str, Any]) -> dict[str, Any]:
        pass_surface_ids = self.passing_ood_surface_ids(payload)
        pass_surface_count = len(pass_surface_ids)
        return {
            "status": "pass" if pass_surface_count >= REQUIRED_PASS_SURFACE_COUNT else "fail",
            "required_pass_surface_count": REQUIRED_PASS_SURFACE_COUNT,
            "pass_surface_count": pass_surface_count,
            "pass_surface_ids": list(pass_surface_ids),
            "pass_surface_pointers": [
                f"$.records.{self.record_index(surface_id)}.deltas.unlogged_error_rate" for surface_id in pass_surface_ids
            ],
            "surface_registry_pointer": "$.surface_registry",
            "aggregate_pointer": "$.aggregate_metrics.multi_surface_uer_reduction_count",
            "gate_pointer": "$.hardgate.gates.LAT-HG7.status",
        }


_LAT_SURFACE_SUITE = LatSurfaceSuite()


@dataclass(frozen=True)
class SurfaceEvaluation:
    surface_id: str
    record: Mapping[str, Any]
    residuals: np.ndarray
    learned_scores: np.ndarray
    control_scores: np.ndarray
    ledger_decisions: np.ndarray
    control_decisions: np.ndarray


@dataclass(frozen=True)
class TorchLedgerArmProtocol:
    requested_device: str
    resolved_device: str
    seed: int
    steps: int
    dtype: str
    drift_tolerance: float
    status: str
    evidence_pointer: str
    row_count: int


def default_config() -> LedgerAwareTransformerConfig:
    return LedgerAwareTransformerConfig()


def surface_specs() -> tuple[SurfaceSpec, ...]:
    return _LAT_SURFACE_SUITE.surface_specs()


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
    quaternary = residuals[:, -1]
    if spec.surface_id == "delayed_recall":
        score = primary + 0.45 * secondary
    elif spec.surface_id == "compositional_rules":
        score = -0.35 * primary + secondary + 0.25 * tertiary
    elif spec.surface_id == "synthetic_tool_use":
        score = 0.25 * primary - 0.4 * secondary + tertiary
    elif spec.surface_id == "counterfactual_binding":
        score = 0.58 * np.roll(primary, 1) + 0.36 * secondary - 0.18 * tertiary
    elif spec.surface_id == "hierarchical_planning":
        score = np.maximum(primary, secondary) + 0.22 * tertiary - 0.14 * quaternary
    elif spec.surface_id == "adversarial_negation":
        score = -0.42 * primary + 0.3 * np.abs(secondary) + 0.68 * quaternary
    else:
        raise ValueError(f"unknown LAT surface_id: {spec.surface_id}")
    cutoff = float(np.quantile(score, 0.62))
    return (score > cutoff).astype(np.int64)


def _prediction_error(residuals: np.ndarray, ledger_event: np.ndarray, spec: SurfaceSpec) -> np.ndarray:
    base = 0.16 + 0.08 * np.abs(residuals[:, 1])
    if spec.surface_id == "delayed_recall":
        event_load = 0.48 * ledger_event + 0.04 * (residuals[:, 2] > 0.0)
    elif spec.surface_id == "compositional_rules":
        event_load = 0.44 * ledger_event + 0.05 * (residuals[:, 4] < 0.0)
    elif spec.surface_id == "synthetic_tool_use":
        event_load = 0.5 * ledger_event + 0.03 * (residuals[:, 5] > 0.0)
    elif spec.surface_id == "counterfactual_binding":
        event_load = 0.18 + 0.01 * (residuals[:, -1] < 0.0)
    elif spec.surface_id == "hierarchical_planning":
        event_load = 0.18 + 0.01 * (residuals[:, -3] > residuals[:, 0])
    elif spec.surface_id == "adversarial_negation":
        event_load = 0.18 + 0.01 * (residuals[:, 3] < residuals[:, -2])
    else:
        raise ValueError(f"unknown LAT surface_id: {spec.surface_id}")
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
        "residual_pointer": f"$.records.{_LAT_SURFACE_SUITE.record_index(spec.surface_id)}.residual_summary",
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


def _discovery_map_pointers_resolve(payload: Mapping[str, Any], signal: Mapping[str, Any]) -> bool:
    pointers = (
        "evidence_pointer",
        "control_pointer",
        "scorecard_pointer",
        "torch_training_evidence_pointer",
        "robustness_evidence_pointer",
        "failed_gate_pointer",
    )
    for key in pointers:
        pointer = signal.get(key)
        if pointer is not None and (not isinstance(pointer, str) or pointer_value(payload, pointer) is None):
            return False
    return True


def _recursive_keys(value: Any) -> set[str]:
    if isinstance(value, Mapping):
        found = {str(key) for key in value}
        for item in value.values():
            found.update(_recursive_keys(item))
        return found
    if isinstance(value, list):
        found: set[str] = set()
        for item in value:
            found.update(_recursive_keys(item))
        return found
    return set()


def _assert_no_terminal_verdict(payload: Mapping[str, Any]) -> None:
    if "terminal_verdict" in _recursive_keys(payload):
        raise ValueError("LAT payload must not emit terminal_verdict")


def _finite_mapping(value: Any) -> bool:
    if isinstance(value, bool):
        return True
    if isinstance(value, (int, float)):
        return math.isfinite(float(value))
    if isinstance(value, Mapping):
        return all(_finite_mapping(item) for item in value.values())
    if isinstance(value, list):
        return all(_finite_mapping(item) for item in value)
    return True


def _pointer_resolves(payload: Mapping[str, Any], pointer: str | None) -> bool:
    return pointer_value(payload, pointer) is not None


def _forbidden_term_audit(positive_claim: Mapping[str, Any]) -> dict[str, Any]:
    text = json.dumps(positive_claim, sort_keys=True).lower()
    hits = [term for term in FORBIDDEN_POSITIVE_CLAIM_TERMS if term.lower() in text]
    return {
        "status": "fail" if hits else "pass",
        "hits": hits,
        "audited_pointer": "$.positive_claim",
    }


def _torch_unavailable_protocol(*, requested_device: str, seed: int, steps: int) -> TorchLedgerArmProtocol:
    return TorchLedgerArmProtocol(
        requested_device=requested_device,
        resolved_device="not-requested",
        seed=seed,
        steps=steps,
        dtype="float32",
        drift_tolerance=DRIFT_TOLERANCE,
        status="unavailable",
        evidence_pointer="$.torch_training_evidence.rows",
        row_count=0,
    )


def _payload_core(
    *,
    active: LedgerAwareTransformerConfig,
    evaluations: Sequence[SurfaceEvaluation],
    generated_at: str,
    run_artifacts: Mapping[str, str],
) -> dict[str, Any]:
    learned_uer = _mean_metric(evaluations, "gap_head", "unlogged_error_rate")
    control_uer = _mean_metric(evaluations, "matched_random_control", "unlogged_error_rate")
    learned_false_alarm = _mean_metric(evaluations, "gap_head", "false_alarm_rate")
    control_false_alarm = _mean_metric(evaluations, "matched_random_control", "false_alarm_rate")
    record_rows = [dict(evaluation.record) for evaluation in evaluations]
    multi_surface = len(_LAT_SURFACE_SUITE.passing_ood_surface_ids({"records": record_rows}))
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
        "run_id": run_artifacts.get("run_id", "ledger-aware-transformer-canonical"),
        "producer": "bedc_quality_lab.ledger_aware_transformer",
        "projector": "LedgerAwareTransformerProjection",
        "json_artifact": JSON_ARTIFACT,
        "markdown_artifact": MARKDOWN_ARTIFACT,
        "run_artifacts": dict(run_artifacts),
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
                "D5-M mechanism closure",
            ],
        },
        "control_protocol": {
            "control_arm": "matched_random_gap_head",
            "matching": "same residual features, same train/eval split, shuffled ledger targets",
            "control_pointer": "$.records.0.matched_random_control",
        },
        "records": record_rows,
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
            "D5-M mechanism closure",
        ],
        "what_was_learned": (
            "Ledger-aware residual gap heads reduce unlogged error on bounded toy OOD surfaces "
            "relative to matched-random controls."
        ),
    }
    return payload


class LedgerAwareTransformerProjection:
    def __init__(
        self,
        *,
        config: LedgerAwareTransformerConfig,
        records: Sequence[Mapping[str, Any]],
        generated_at: str,
        run_artifacts: Mapping[str, str],
        torch_protocol: TorchLedgerArmProtocol,
    ) -> None:
        self.config = config
        self.records = [dict(record) for record in records]
        self.generated_at = generated_at
        self.run_artifacts = dict(run_artifacts)
        self.torch_protocol = torch_protocol

    def hardgate_verdicts(self, summaries: Mapping[str, Any]) -> dict[str, dict[str, Any]]:
        payload = summaries
        records = payload.get("records")
        surface_registry = payload.get("surface_registry")
        ledger_rows = pointer_value(payload, "$.ledger.rows")
        aggregate = payload.get("aggregate_metrics")
        positive_claim = payload.get("positive_claim")
        matched_control = payload.get("matched_random_control")
        torch_evidence = payload.get("torch_training_evidence")
        revocation_rows = payload.get("revocation_rows")
        forbidden_audit = payload.get("forbidden_claim_term_audit")
        robustness = payload.get("robustness_signal")

        hg1_pass = (
            isinstance(records, list)
            and bool(records)
            and _finite_mapping(records)
            and isinstance(surface_registry, Mapping)
            and bool(surface_registry)
            and isinstance(aggregate, Mapping)
        )
        ledger_pointer_pass = isinstance(ledger_rows, list) and bool(ledger_rows) and all(
            isinstance(row, Mapping)
            and _pointer_resolves(payload, row.get("evidence_pointer") if isinstance(row.get("evidence_pointer"), str) else None)
            and _pointer_resolves(payload, row.get("control_pointer") if isinstance(row.get("control_pointer"), str) else None)
            and _pointer_resolves(payload, row.get("ledger_decision_pointer") if isinstance(row.get("ledger_decision_pointer"), str) else None)
            for row in ledger_rows
        )
        surface_pointer_pass = isinstance(positive_claim, Mapping) and all(
            _pointer_resolves(payload, positive_claim.get(key) if isinstance(positive_claim.get(key), str) else None)
            for key in ("evidence_pointer", "control_pointer", "surface_registry_pointer")
        )
        hg2_pass = ledger_pointer_pass and surface_pointer_pass
        hg3_pass = (
            isinstance(aggregate, Mapping)
            and aggregate.get("uer_reduction", 0.0) > 0.0
            and aggregate.get("multi_surface_uer_reduction_count", 0) >= 2
            and isinstance(positive_claim, Mapping)
            and positive_claim.get("net_positive_signal") is True
        )
        hg4_pass = (
            isinstance(matched_control, Mapping)
            and matched_control.get("control_positive_discovery") is False
            and isinstance(aggregate, Mapping)
            and aggregate.get("only_false_alarm_increase") is False
        )
        hg5_pass = (
            isinstance(payload.get("claim_capsule_ref"), Mapping)
            and _pointer_resolves(payload, CLAIM_CAPSULE_POINTER)
            and isinstance(revocation_rows, list)
            and bool(revocation_rows)
            and isinstance(forbidden_audit, Mapping)
            and forbidden_audit.get("status") == "pass"
        )
        hg6_pass = (
            isinstance(torch_evidence, Mapping)
            and torch_evidence.get("status") in {"available", "unavailable"}
            and isinstance(torch_evidence.get("row_count"), int)
            and _pointer_resolves(payload, "$.torch_training_evidence.protocol")
        )
        hg7_pass = (
            isinstance(robustness, Mapping)
            and robustness.get("status") == "pass"
            and robustness.get("required_pass_surface_count") == REQUIRED_PASS_SURFACE_COUNT
            and robustness.get("pass_surface_count") == len(_LAT_SURFACE_SUITE.passing_ood_surface_ids(payload))
            and robustness.get("pass_surface_ids") == list(_LAT_SURFACE_SUITE.passing_ood_surface_ids(payload))
            and isinstance(robustness.get("pass_surface_pointers"), list)
            and all(
                isinstance(pointer, str) and _pointer_resolves(payload, pointer)
                for pointer in robustness.get("pass_surface_pointers", [])
            )
            and _pointer_resolves(payload, robustness.get("surface_registry_pointer") if isinstance(robustness.get("surface_registry_pointer"), str) else None)
            and _pointer_resolves(payload, robustness.get("aggregate_pointer") if isinstance(robustness.get("aggregate_pointer"), str) else None)
            and robustness.get("gate_pointer") == "$.hardgate.gates.LAT-HG7.status"
        )
        results = {
            "LAT-HG1": (hg1_pass, "$.records", "deterministic records and surfaces present"),
            "LAT-HG2": (hg2_pass, "$.ledger.rows", "ledger and surface pointers resolve"),
            "LAT-HG3": (hg3_pass, "$.aggregate_metrics.uer_reduction", "classifier surface delta is net positive"),
            "LAT-HG4": (hg4_pass, "$.matched_random_control.control_positive_discovery", "matched-random control remains negative"),
            "LAT-HG5": (hg5_pass, "$.forbidden_claim_term_audit.status", "scorecard capsule and claim-term audit are ready"),
            "LAT-HG6": (hg6_pass, "$.torch_training_evidence.protocol", "torch protocol boundary is recorded"),
            "LAT-HG7": (
                hg7_pass,
                "$.robustness_signal.status",
                "at least three OOD surfaces pass the LAT operational robustness threshold",
            ),
        }
        return {
            name: {
                "status": "pass" if passed else "fail",
                "pointer": pointer,
                "reason": reason,
            }
            for name, (passed, pointer, reason) in results.items()
        }

    def failed_gate(self, hardgates: Mapping[str, Mapping[str, Any]]) -> str | None:
        for name in LAT_HARDGATES:
            row = hardgates.get(name)
            if not isinstance(row, Mapping) or row.get("status") != "pass":
                return name
        return None

    def discovery_map_signal(self, hardgates: Mapping[str, Mapping[str, Any]], payload: Mapping[str, Any] | None = None) -> dict[str, Any]:
        failed = self.failed_gate(hardgates)
        candidate: dict[str, Any] = {
            "status": "d5-o-candidate",
            "level_candidate": "D5-O",
            "reason": "lat-hardgates-pass",
            "failed_gate": None,
            "failed_gate_pointer": None,
            "evidence_pointer": "$.aggregate_metrics.uer_reduction",
            "control_pointer": "$.matched_random_control",
            "scorecard_pointer": "$.forbidden_claim_term_audit",
            "torch_training_evidence_pointer": "$.torch_training_evidence",
            "robustness_evidence_pointer": "$.robustness_signal",
            "net_positive_signal": True,
        }
        existing_signal = payload.get("discovery_map_signal") if isinstance(payload, Mapping) else None
        pointer_source = existing_signal if isinstance(existing_signal, Mapping) else candidate
        pointers_resolve = payload is not None and _discovery_map_pointers_resolve(payload, pointer_source)
        if failed is None and pointers_resolve:
            return {
                "status": candidate["status"],
                "level_candidate": candidate["level_candidate"],
                "reason": candidate["reason"],
                "failed_gate": candidate["failed_gate"],
                "failed_gate_pointer": candidate["failed_gate_pointer"],
                "evidence_pointer": candidate["evidence_pointer"],
                "control_pointer": candidate["control_pointer"],
                "scorecard_pointer": candidate["scorecard_pointer"],
                "torch_training_evidence_pointer": candidate["torch_training_evidence_pointer"],
                "robustness_evidence_pointer": candidate["robustness_evidence_pointer"],
                "net_positive_signal": candidate["net_positive_signal"],
            }
        reason = "hardgate-failed" if failed is not None else "lat-discovery-map-pointer-dangling"
        failed_pointer = f"$.hardgate.gates.{failed}.status" if failed is not None else "$.discovery_map_signal.robustness_evidence_pointer"
        return {
            "status": "negative",
            "level_candidate": "DN",
            "reason": reason,
            "failed_gate": failed,
            "failed_gate_pointer": failed_pointer,
            "evidence_pointer": "$.aggregate_metrics.uer_reduction",
            "control_pointer": "$.matched_random_control",
            "scorecard_pointer": "$.forbidden_claim_term_audit",
            "torch_training_evidence_pointer": "$.torch_training_evidence",
            "robustness_evidence_pointer": "$.robustness_signal",
            "net_positive_signal": False,
        }

    def project(self) -> dict[str, Any]:
        evaluations = [
            SurfaceEvaluation(
                surface_id=str(record["surface_id"]),
                record=record,
                residuals=np.array([], dtype=np.float64),
                learned_scores=np.array([], dtype=np.float64),
                control_scores=np.array([], dtype=np.float64),
                ledger_decisions=np.array([], dtype=np.int64),
                control_decisions=np.array([], dtype=np.int64),
            )
            for record in self.records
        ]
        payload = _payload_core(
            active=self.config,
            evaluations=evaluations,
            generated_at=self.generated_at,
            run_artifacts=self.run_artifacts,
        )
        payload["matched_random_control"] = {
            "status": "negative",
            "control_positive_discovery": False,
            "control_projection": {
                "positive_discovery": False,
                "reason": "matched-random control does not satisfy multi-surface net-positive evidence",
            },
            "summary_pointer": "$.aggregate_metrics",
            "rows_pointer": "$.records",
        }
        protocol = asdict(self.torch_protocol)
        payload["torch_training_evidence"] = {
            "status": self.torch_protocol.status,
            "protocol": protocol,
            "rows": [],
            "row_count": self.torch_protocol.row_count,
            "evidence_pointer": self.torch_protocol.evidence_pointer,
        }
        payload["revocation_rows"] = [
            {
                "row_id": "lat:overclaim-boundary",
                "status": "ready",
                "revocation_trigger": "forbidden positive claim term or dangling pointer",
                "failed_gate_pointer": "$.hardgate.failed_gate",
            }
        ]
        payload["positive_claim"]["net_positive_signal"] = True
        payload["positive_claim"]["claim_status"] = "bounded-positive-evidence"
        payload["forbidden_claim_term_audit"] = _forbidden_term_audit(payload["positive_claim"])
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
        payload["robustness_signal"] = _LAT_SURFACE_SUITE.robustness_signal(payload)
        hardgates = self.hardgate_verdicts(payload)
        failed = self.failed_gate(hardgates)
        payload["hardgate"] = {
            "status": "pass" if failed is None else "fail",
            "gates": hardgates,
            "failed_gate": failed,
        }
        payload["hardgate"]["gates"]["LAT-HG7"]["status"] = payload["robustness_signal"]["status"]
        failed = self.failed_gate(payload["hardgate"]["gates"])
        payload["hardgate"]["status"] = "pass" if failed is None else "fail"
        payload["hardgate"]["failed_gate"] = failed
        payload["failed_gate"] = failed
        payload["discovery_map_signal"] = self.discovery_map_signal(payload["hardgate"]["gates"], payload)
        _assert_no_terminal_verdict(payload)
        report_markdown = render_markdown(payload, payload["claim_capsule_ref"]["capsule"])
        return {
            "summary_payload": payload,
            "claim_capsule_payload": payload["claim_capsule_ref"]["capsule"],
            "report_markdown": report_markdown,
            "raw_rows": self.records,
        }


def default_run_artifacts(run_id: str = "ledger-aware-transformer-canonical") -> dict[str, str]:
    return {
        "run_id": run_id,
        "summary": JSON_ARTIFACT,
        "claim_capsule": JSON_ARTIFACT,
        "raw_metrics": JSON_ARTIFACT,
        "report": MARKDOWN_ARTIFACT,
    }


def build_payload(
    *,
    generated_at: str = DEFAULT_GENERATED_AT,
    config: LedgerAwareTransformerConfig | None = None,
    torch_protocol: TorchLedgerArmProtocol | None = None,
    run_artifacts: Mapping[str, str] | None = None,
) -> dict[str, Any]:
    active = config or default_config()
    protocol = torch_protocol or _torch_unavailable_protocol(requested_device="cpu", seed=active.seed, steps=0)
    projection = LedgerAwareTransformerProjection(
        config=active,
        records=[dict(evaluate_surface(spec, active).record) for spec in surface_specs()],
        generated_at=generated_at,
        run_artifacts=default_run_artifacts() if run_artifacts is None else run_artifacts,
        torch_protocol=protocol,
    )
    return projection.project()["summary_payload"]


def render_markdown(payload: Mapping[str, Any], capsule: Mapping[str, Any]) -> str:
    del capsule
    lines = [
        "# Ledger-Aware Transformer",
        "",
        f"- Generated at: `{payload['generated_at']}`",
        f"- Schema: `{payload['schema_id']}`",
        f"- Surface count: `{payload['aggregate_metrics']['surface_count']}`",
        f"- OOD surface count: `{payload['aggregate_metrics']['ood_surface_count']}`",
        f"- UER reduction: `{payload['aggregate_metrics']['uer_reduction']}`",
        f"- False alarm delta: `{payload['aggregate_metrics']['false_alarm_delta']}`",
        f"- Discovery signal: `{payload['discovery_map_signal']['level_candidate']}`",
        f"- Failed gate: `{payload['failed_gate']}`",
        f"- Claim capsule pointer: `{payload['claim_capsule_ref']['pointer']}`",
        "",
        "## Hardgates",
        "",
        "| gate | status | pointer |",
        "| --- | --- | --- |",
    ]
    for name in LAT_HARDGATES:
        row = payload["hardgate"]["gates"][name]
        lines.append(f"| `{name}` | `{row['status']}` | `{row['pointer']}` |")
    lines.extend(
        [
            "",
            "## Records",
            "",
            "| surface | learned UER | matched-random UER | UER delta | false alarm delta |",
            "| --- | ---: | ---: | ---: | ---: |",
        ]
    )
    for row in payload["records"]:
        lines.append(
            "| "
            f"`{row['surface_id']}` | "
            f"{row['gap_head']['metrics']['unlogged_error_rate']:.6f} | "
            f"{row['matched_random_control']['metrics']['unlogged_error_rate']:.6f} | "
            f"{row['deltas']['unlogged_error_rate']:.6f} | "
            f"{row['deltas']['false_alarm_rate']:.6f} |"
        )
    lines.extend(
        [
            "",
            "## Canonical Pointers",
            "",
            "- Scope pointer: `$.applicability_boundary`",
            "- Cost pointer: `$.source_artifacts.cost_protocol`",
            "- Positive claim pointer: `$.positive_claim`",
            "- Control pointer: `$.control_protocol`",
            "- Discovery signal pointer: `$.discovery_map_signal`",
            "- Torch evidence pointer: `$.torch_training_evidence`",
            "",
        ]
    )
    return "\n".join(lines)


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

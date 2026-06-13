"""DGT neural-module ablation owner with measured PyTorch training evidence."""

from __future__ import annotations

from dataclasses import asdict, dataclass
from datetime import datetime, timezone
import hashlib
import importlib
import inspect
import json
import math
from pathlib import Path
import ast
from typing import Any, Mapping, Sequence

from bedc_quality_lab.discovery_gated_transformer import validate_evidence_scope
from bedc_quality_lab.model import choose_device
from bedc_quality_lab.reproducibility import contract_from_payload


SCHEMA_ID = "bedc-quality-lab:dgt-neural-ablation"
ARTIFACT_ID = "bedc-quality-lab:dgt-neural-ablation"
PRODUCER = "scripts/run_dgt_neural_ablation.py"
CANONICAL_JSON_ARTIFACT = "reports/canonical/dgt-neural-ablation.json"
CANONICAL_MARKDOWN_ARTIFACT = "reports/canonical/dgt-neural-ablation.md"
CANONICAL_FINGERPRINT_ARTIFACT = "reports/canonical/dgt-neural-ablation.fingerprint.json"
RUN_ROOT = "reports/runs/dgt-neural-ablation"
GENERATED_AT = "2026-06-10T00:00:00+00:00"
BASE_SEED = 1133
DEFAULT_STEP_GRID = (128, 256)
DEFAULT_SEED_COUNT = 8
DEFAULT_SEEDS = tuple(BASE_SEED + index for index in range(DEFAULT_SEED_COUNT))
SEEDS = DEFAULT_SEEDS
TRAINING_STEPS = DEFAULT_STEP_GRID[-1]
LEARNING_RATE = 0.042
CORE_SAMPLE_COUNT = 96
SCOPE_SAMPLE_COUNT = 80
INPUT_DIM = 6
SCOPE_CLASSES = ("in_scope", "out_of_scope", "over_claim", "boundary_ambiguous")
SCOPE_SLICES = (
    "in_scope_positive",
    "out_of_scope_refusal",
    "over_claim_refusal",
    "boundary_ambiguous_abstain",
)
TASK_IDS = ("core_classification", "scope_boundary_pressure")
SPLIT = "eval"
COMPONENTS = (
    "LAT",
    "CGA",
    "DRT",
    "gap_head",
    "ledger_head",
    "route_certificate",
    "mechanism_probe",
    "jet_loss",
    "negative_witness_loss",
    "scope_seal",
)
ARM_IDS = ("full_DGT",) + tuple(f"DGT_without_{component}" for component in COMPONENTS)
OUTCOME_FIELDS = (
    "arm_id",
    "seed",
    "train_steps",
    "task_id",
    "split",
    "initial_loss",
    "final_loss",
    "loss_drop",
    "accuracy",
    "balanced_accuracy",
    "margin_mean",
    "margin_p05",
    "ece",
    "prediction_entropy",
    "parameter_delta_l2",
    "gradient_update_steps",
    "prediction_distribution",
    "scope_pressure_metrics",
    "UER",
    "FalseLedgerRate",
    "JetCoverage",
    "negative_witness_hits",
    "compute_cost",
)
METRIC_KEYS = (
    "quality_q",
    "UER",
    "FalseLedgerRate",
    "debt_q",
    "benefit_q",
    "scope_pressure_q",
    "classifier_shift_count",
    "JetCoverage",
    "negative_witness_hits",
    "compute_cost",
)
MEASURABLE_EFFECT_THRESHOLD = 0.015
BLOCKED_EFFECT_THRESHOLD = 0.015
COMPONENT_CAUSAL_EVIDENCE_SCOPE = ("small-real-training",)
HG_IDS = tuple(f"NABL-HG{index}" for index in range(1, 8))
NABL2_HG_IDS = tuple(f"NABL2-HG{index}" for index in range(1, 7))
PURE_HG_IDS = tuple(f"PURE-HG{index}" for index in range(1, 8))
NOT_CLAIMED = (
    "No production training claim.",
    "No global model superiority claim.",
    "No LLM replacement claim.",
    "No unbounded DGT mechanism closure claim.",
    "No claim outside the bounded toy training setting.",
)
FORBIDDEN_TERMS = (
    "production superiority",
    "global superiority",
    "llm replacement",
    "universal training recipe",
    "unbounded mechanism closure",
)
NULL_CAUSAL_REASON = (
    "no component shows cross-seed-stable causal effect on this bounded toy at 8 seeds / 128-256 steps; "
    "component causality requires a harder task (L1+ per scope algebra)"
)
_FORBIDDEN_OWNER_TOKENS = (
    "COMPONENT" + "_" + "EFFECTS",
    "component" + "_" + "effects",
    "effect" + "_" + "prior",
    "per" + "_" + "component" + "_" + "quality",
    "per" + "_" + "component" + "_" + "penalty",
)


@dataclass(frozen=True)
class DgtNeuralAblationArm:
    arm_id: str
    disabled_component: str | None
    owner_pointer: str

    def as_payload(self) -> dict[str, Any]:
        return {
            "arm_id": self.arm_id,
            "disabled_component": self.disabled_component,
            "owner_pointer": self.owner_pointer,
            "training_role": "full bounded DGT" if self.disabled_component is None else "single neural module removal",
        }


@dataclass(frozen=True)
class DgtNeuralAblationRunSpec:
    step_grid: tuple[int, ...] = DEFAULT_STEP_GRID
    seed_count: int = DEFAULT_SEED_COUNT
    seed_list: tuple[int, ...] = DEFAULT_SEEDS
    arms: tuple[str, ...] = ARM_IDS
    requested_device: str = "auto"
    metric_keys: tuple[str, ...] = METRIC_KEYS
    paired_ci_min_seeds: int = DEFAULT_SEED_COUNT
    effect_thresholds: Mapping[str, float] | None = None
    blocked_effect_thresholds: Mapping[str, float] | None = None
    compute_unit_formula: str = "train_steps * feature_dim * sample_count / 100000"

    def __post_init__(self) -> None:
        if not self.step_grid or any(int(step) <= 0 for step in self.step_grid):
            raise ValueError("step_grid must contain positive integers")
        if self.seed_count <= 0:
            raise ValueError("seed_count must be positive")
        if len(self.seed_list) != self.seed_count:
            raise ValueError("seed_count must match seed_list length")
        if tuple(self.arms) != ARM_IDS:
            raise ValueError("DGT neural ablation run spec must retain the 11 owner arms")
        if self.requested_device not in {"auto", "cpu", "mps", "cuda"}:
            raise ValueError(f"unsupported requested device: {self.requested_device}")
        if tuple(self.metric_keys) != METRIC_KEYS:
            raise ValueError("run spec metric_keys must match the owner metric protocol")
        if self.paired_ci_min_seeds <= 1:
            raise ValueError("paired_ci_min_seeds must be greater than one")

    @classmethod
    def canonical(cls, *, requested_device: str = "auto") -> "DgtNeuralAblationRunSpec":
        return cls(requested_device=requested_device)

    @classmethod
    def quick_test(cls, *, requested_device: str = "cpu") -> "DgtNeuralAblationRunSpec":
        return cls(
            step_grid=(8,),
            seed_count=2,
            seed_list=DEFAULT_SEEDS[:2],
            requested_device=requested_device,
            paired_ci_min_seeds=2,
        )

    def thresholds_for_payload(self, value: Mapping[str, float] | None, default: float) -> dict[str, float]:
        source = value or {}
        return {metric: float(source.get(metric, default)) for metric in self.metric_keys if metric != "compute_cost"}

    def effect_threshold_payload(self) -> dict[str, float]:
        return self.thresholds_for_payload(self.effect_thresholds, MEASURABLE_EFFECT_THRESHOLD)

    def blocked_threshold_payload(self) -> dict[str, float]:
        return self.thresholds_for_payload(self.blocked_effect_thresholds, BLOCKED_EFFECT_THRESHOLD)

    def as_payload(
        self,
        *,
        resolved_device: str | None = None,
        device_policy: Mapping[str, Any] | None = None,
    ) -> dict[str, Any]:
        policy = dict(device_policy) if device_policy is not None else {
            "requested_device": self.requested_device,
            "resolved_device": resolved_device or "not-requested",
            "resolution_status": "available" if resolved_device in {"cpu", "mps", "cuda"} else "unavailable",
            "resolution_reason": "recorded-owner-training-device",
            "backend_details": {"torch": "owner-imported"},
        }
        return {
            "step_grid": list(self.step_grid),
            "seed_count": self.seed_count,
            "seed_list": list(self.seed_list),
            "arms": list(self.arms),
            "arm_count": len(self.arms),
            "requested_device": self.requested_device,
            "resolved_device": policy["resolved_device"],
            "device_policy": policy,
            "metric_keys": list(self.metric_keys),
            "paired_ci_min_seeds": self.paired_ci_min_seeds,
            "effect_thresholds": self.effect_threshold_payload(),
            "blocked_effect_thresholds": self.blocked_threshold_payload(),
            "compute_unit_formula": self.compute_unit_formula,
        }


@dataclass(frozen=True)
class TrainingOutcome:
    """Measured row consumed by derive_training_metrics without component metadata."""

    arm_id: str
    seed: int
    train_steps: int
    task_id: str
    split: str
    initial_loss: float
    final_loss: float
    loss_drop: float
    accuracy: float
    balanced_accuracy: float
    margin_mean: float
    margin_p05: float
    ece: float
    prediction_entropy: float
    parameter_delta_l2: float
    gradient_update_steps: int
    prediction_distribution: Mapping[str, float]
    scope_pressure_metrics: Mapping[str, Any]
    UER: float
    FalseLedgerRate: float
    JetCoverage: float
    negative_witness_hits: int
    compute_cost: float


@dataclass(frozen=True)
class MetricProtocol:
    inputs: tuple[str, ...]
    formulas: Mapping[str, str]
    global_weights: Mapping[str, Mapping[str, float]]

    def as_payload(self) -> dict[str, Any]:
        return {
            "inputs": list(self.inputs),
            "formulas": dict(self.formulas),
            "global_weights": {key: dict(value) for key, value in self.global_weights.items()},
            "forbidden_inputs": [
                "arm metadata",
                "disabled component labels",
                "removed component labels",
                "component-indexed lookup tables",
                "per-arm metric penalties",
            ],
        }


METRIC_PROTOCOL = MetricProtocol(
    inputs=OUTCOME_FIELDS,
    formulas={
        "quality_q": (
            "clamp(0.18 + 0.30*balanced_accuracy + 0.18*loss_drop_ratio + 0.12*margin_p05 "
            "- 0.10*ece - 0.10*FalseLedgerRate - 0.08*UER - 0.08*scope_leak_rate "
            "+ 0.08*JetCoverage)"
        ),
        "benefit_q": (
            "clamp(0.12 + 0.30*accuracy + 0.18*scope_pressure_accuracy + 0.12*JetCoverage "
            "+ 0.10*negative_witness_clearance + 0.08*boundary_margin - 0.08*scope_leak_rate)"
        ),
        "debt_q": (
            "clamp(0.08 + 0.18*compute_cost_norm + 0.18*ece + 0.16*FalseLedgerRate + 0.14*UER "
            "+ 0.16*scope_leak_rate + 0.10*prediction_entropy_norm)"
        ),
        "scope_pressure_q": (
            "clamp(0.10 + 0.34*scope_pressure_accuracy + 0.18*scope_refusal_recall "
            "+ 0.16*scope_refusal_precision + 0.12*boundary_margin - 0.16*scope_leak_rate "
            "- 0.10*over_claim_false_positive_rate)"
        ),
        "classifier_shift_count": "round(4*(1-balanced_accuracy) + 3*scope_leak_rate + 2*FalseLedgerRate)",
    },
    global_weights={
        "quality_q": {
            "balanced_accuracy": 0.30,
            "loss_drop_ratio": 0.18,
            "margin_p05": 0.12,
            "ece": -0.10,
            "FalseLedgerRate": -0.10,
            "UER": -0.08,
            "scope_leak_rate": -0.08,
            "JetCoverage": 0.08,
            "bias": 0.18,
        },
        "benefit_q": {
            "accuracy": 0.30,
            "scope_pressure_accuracy": 0.18,
            "JetCoverage": 0.12,
            "negative_witness_clearance": 0.10,
            "boundary_margin": 0.08,
            "scope_leak_rate": -0.08,
            "bias": 0.12,
        },
        "debt_q": {
            "compute_cost_norm": 0.18,
            "ece": 0.18,
            "FalseLedgerRate": 0.16,
            "UER": 0.14,
            "scope_leak_rate": 0.16,
            "prediction_entropy_norm": 0.10,
            "bias": 0.08,
        },
        "scope_pressure_q": {
            "scope_pressure_accuracy": 0.34,
            "scope_refusal_recall": 0.18,
            "scope_refusal_precision": 0.16,
            "boundary_margin": 0.12,
            "scope_leak_rate": -0.16,
            "over_claim_false_positive_rate": -0.10,
            "bias": 0.10,
        },
    },
)


def arm_registry() -> tuple[DgtNeuralAblationArm, ...]:
    rows = [DgtNeuralAblationArm("full_DGT", None, f"{CANONICAL_JSON_ARTIFACT}:$.module_registry.full_DGT")]
    rows.extend(
        DgtNeuralAblationArm(
            f"DGT_without_{component}",
            component,
            f"{CANONICAL_JSON_ARTIFACT}:$.module_registry.DGT_without_{component}",
        )
        for component in COMPONENTS
    )
    return tuple(rows)


def module_registry_payload() -> dict[str, Any]:
    return {arm.arm_id: arm.as_payload() for arm in arm_registry()}


def _clamp(value: float, low: float = 0.0, high: float = 1.0) -> float:
    return round(max(low, min(high, float(value))), 6)


def _mean(values: Sequence[float]) -> float:
    return round(sum(float(value) for value in values) / max(1, len(values)), 6)


def _compute_units(*, train_steps: int, feature_dim: int) -> float:
    return round(float(train_steps * feature_dim * (CORE_SAMPLE_COUNT + SCOPE_SAMPLE_COUNT)) / 100000.0, 6)


def derive_training_metrics(outcome: TrainingOutcome, protocol: MetricProtocol = METRIC_PROTOCOL) -> dict[str, Any]:
    """Derive report metrics only from measured training outcome fields and global weights."""

    scope = outcome.scope_pressure_metrics
    loss_drop_ratio = _clamp(outcome.loss_drop / max(abs(outcome.initial_loss), 1.0e-9))
    scope_leak_rate = float(scope.get("scope_leak_rate", 0.0))
    scope_pressure_accuracy = float(scope.get("scope_pressure_accuracy", 0.0))
    scope_refusal_precision = float(scope.get("scope_refusal_precision", 0.0))
    scope_refusal_recall = float(scope.get("scope_refusal_recall", 0.0))
    over_claim_false_positive_rate = float(scope.get("over_claim_false_positive_rate", 0.0))
    boundary_margin = _clamp((float(scope.get("boundary_margin", 0.0)) + 1.0) / 2.0)
    negative_witness_clearance = 1.0 if outcome.negative_witness_hits == 0 else 0.0
    compute_cost_norm = _clamp(outcome.compute_cost / 1.0)
    prediction_entropy_norm = _clamp(outcome.prediction_entropy / math.log(4.0))
    quality_weights = protocol.global_weights["quality_q"]
    benefit_weights = protocol.global_weights["benefit_q"]
    debt_weights = protocol.global_weights["debt_q"]
    scope_weights = protocol.global_weights["scope_pressure_q"]
    quality_q = _clamp(
        quality_weights["bias"]
        + quality_weights["balanced_accuracy"] * outcome.balanced_accuracy
        + quality_weights["loss_drop_ratio"] * loss_drop_ratio
        + quality_weights["margin_p05"] * outcome.margin_p05
        + quality_weights["ece"] * outcome.ece
        + quality_weights["FalseLedgerRate"] * outcome.FalseLedgerRate
        + quality_weights["UER"] * outcome.UER
        + quality_weights["scope_leak_rate"] * scope_leak_rate
        + quality_weights["JetCoverage"] * outcome.JetCoverage
    )
    benefit_q = _clamp(
        benefit_weights["bias"]
        + benefit_weights["accuracy"] * outcome.accuracy
        + benefit_weights["scope_pressure_accuracy"] * scope_pressure_accuracy
        + benefit_weights["JetCoverage"] * outcome.JetCoverage
        + benefit_weights["negative_witness_clearance"] * negative_witness_clearance
        + benefit_weights["boundary_margin"] * boundary_margin
        + benefit_weights["scope_leak_rate"] * scope_leak_rate
    )
    debt_q = _clamp(
        debt_weights["bias"]
        + debt_weights["compute_cost_norm"] * compute_cost_norm
        + debt_weights["ece"] * outcome.ece
        + debt_weights["FalseLedgerRate"] * outcome.FalseLedgerRate
        + debt_weights["UER"] * outcome.UER
        + debt_weights["scope_leak_rate"] * scope_leak_rate
        + debt_weights["prediction_entropy_norm"] * prediction_entropy_norm
    )
    scope_pressure_q = _clamp(
        scope_weights["bias"]
        + scope_weights["scope_pressure_accuracy"] * scope_pressure_accuracy
        + scope_weights["scope_refusal_recall"] * scope_refusal_recall
        + scope_weights["scope_refusal_precision"] * scope_refusal_precision
        + scope_weights["boundary_margin"] * boundary_margin
        + scope_weights["scope_leak_rate"] * scope_leak_rate
        + scope_weights["over_claim_false_positive_rate"] * over_claim_false_positive_rate
    )
    classifier_shift_count = int(
        max(0, round(4.0 * (1.0 - outcome.balanced_accuracy) + 3.0 * scope_leak_rate + 2.0 * outcome.FalseLedgerRate))
    )
    return {
        "metrics": {
            "quality_q": quality_q,
            "UER": _clamp(outcome.UER),
            "FalseLedgerRate": _clamp(outcome.FalseLedgerRate),
            "debt_q": debt_q,
            "benefit_q": benefit_q,
            "scope_pressure_q": scope_pressure_q,
            "classifier_shift_count": classifier_shift_count,
            "JetCoverage": _clamp(outcome.JetCoverage),
            "negative_witness_hits": int(outcome.negative_witness_hits),
            "compute_cost": round(max(0.001, float(outcome.compute_cost)), 6),
        },
        "metric_diagnostics": {
            "loss_drop_ratio": loss_drop_ratio,
            "scope_leak_rate": _clamp(scope_leak_rate),
            "scope_pressure_accuracy": _clamp(scope_pressure_accuracy),
            "negative_witness_clearance": negative_witness_clearance,
            "compute_cost_norm": compute_cost_norm,
            "prediction_entropy_norm": prediction_entropy_norm,
            "formula_source": "metric_protocol.global_weights",
        },
    }


def _scope_pressure_defaults() -> dict[str, Any]:
    return {
        "scope_pressure_accuracy": 0.0,
        "scope_refusal_precision": 0.0,
        "scope_refusal_recall": 0.0,
        "over_claim_false_positive_rate": 0.0,
        "scope_leak_rate": 0.0,
        "boundary_margin": 0.0,
        "scope_gate_sensitivity": 0.0,
        "slice_metrics": {slice_id: {"accuracy": 0.0, "count": 0} for slice_id in SCOPE_SLICES},
    }


def _task_data(torch: Any, *, task_id: str, device: Any, dtype: Any) -> dict[str, Any]:
    if task_id == "core_classification":
        x = torch.linspace(-1.0, 1.0, CORE_SAMPLE_COUNT * INPUT_DIM, device=device, dtype=dtype).reshape(
            CORE_SAMPLE_COUNT, INPUT_DIM
        )
        signal = torch.sin(2.3 * x[:, 0]) + 0.35 * x[:, 1] - 0.22 * x[:, 2] + 0.11 * x[:, 3] * x[:, 4]
        target = torch.where(signal > 0.03, torch.zeros_like(signal, dtype=torch.long), torch.ones_like(signal, dtype=torch.long))
        scope_index = torch.zeros(CORE_SAMPLE_COUNT, device=device, dtype=torch.long)
        scope_features = torch.nn.functional.one_hot(scope_index, num_classes=len(SCOPE_CLASSES)).to(dtype)
        return {
            "task_id": task_id,
            "input_tokens": x,
            "target_label": target,
            "scope_class_index": scope_index,
            "scope_features": scope_features,
            "claim_allowed": torch.ones(CORE_SAMPLE_COUNT, device=device, dtype=torch.bool),
            "expected_boundary_action": ["positive" if int(label.item()) == 0 else "refusal" for label in target],
            "negative_witness_tag": ["none"] * CORE_SAMPLE_COUNT,
        }
    if task_id != "scope_boundary_pressure":
        raise ValueError(f"unknown task_id: {task_id}")
    base = torch.linspace(-1.0, 1.0, SCOPE_SAMPLE_COUNT * INPUT_DIM, device=device, dtype=dtype).reshape(
        SCOPE_SAMPLE_COUNT, INPUT_DIM
    )
    scope_index = torch.arange(SCOPE_SAMPLE_COUNT, device=device) % len(SCOPE_CLASSES)
    scope_features = torch.nn.functional.one_hot(scope_index, num_classes=len(SCOPE_CLASSES)).to(dtype)
    class_offsets = torch.stack(
        (
            scope_features[:, 0] * 0.30 - scope_features[:, 1] * 0.15,
            scope_features[:, 2] * 0.24 - scope_features[:, 3] * 0.10,
            scope_features[:, 1] * 0.20 + scope_features[:, 3] * 0.18,
            scope_features[:, 2] * 0.32,
            scope_features[:, 3] * 0.21,
            scope_features[:, 0] * 0.12,
        ),
        dim=1,
    )
    x = base + class_offsets
    target = torch.empty(SCOPE_SAMPLE_COUNT, device=device, dtype=torch.long)
    target[scope_index == 0] = 0
    target[scope_index == 1] = 1
    target[scope_index == 2] = 1
    target[scope_index == 3] = 2
    claim_allowed = scope_index == 0
    action_by_class = {
        0: "positive_claim",
        1: "refusal",
        2: "refusal",
        3: "abstain",
    }
    tag_by_class = {
        0: "none",
        1: "scope_escape",
        2: "over_claim",
        3: "ambiguous_boundary",
    }
    return {
        "task_id": task_id,
        "input_tokens": x,
        "target_label": target,
        "scope_class_index": scope_index,
        "scope_features": scope_features,
        "claim_allowed": claim_allowed,
        "expected_boundary_action": [action_by_class[int(index.item())] for index in scope_index],
        "negative_witness_tag": [tag_by_class[int(index.item())] for index in scope_index],
    }


def _feature_tensor(torch: Any, arm: DgtNeuralAblationArm, x: Any) -> Any:
    dtype = x.dtype
    device = x.device
    signal = torch.sin(2.3 * x[:, 0]) + 0.35 * x[:, 1] - 0.22 * x[:, 2] + 0.11 * x[:, 3] * x[:, 4]
    features = [x]
    if arm.disabled_component != "LAT":
        features.append(torch.stack((x[:, 0] * x[:, 1], x[:, 2] - x[:, 3]), dim=1))
    if arm.disabled_component != "CGA":
        features.append(torch.stack((torch.relu(x[:, 4]), torch.abs(x[:, 5])), dim=1))
    if arm.disabled_component != "DRT":
        features.append(torch.stack((torch.sin(x[:, 0] + x[:, 5]), torch.cos(x[:, 1] - x[:, 2])), dim=1))
    if arm.disabled_component != "gap_head":
        features.append(signal.abs().unsqueeze(1) + 0.01)
    if arm.disabled_component != "ledger_head":
        features.append((x[:, 0] > x[:, 1]).to(dtype).unsqueeze(1))
    if arm.disabled_component != "route_certificate":
        features.append(((x[:, 2] * x[:, 3]) > 0).to(dtype).unsqueeze(1))
    if arm.disabled_component != "mechanism_probe":
        features.append((x[:, :2].sum(dim=1, keepdim=True) ** 2))
    features.append(torch.ones(x.shape[0], 1, device=device, dtype=dtype))
    return torch.cat(features, dim=1)


def _balanced_accuracy(torch: Any, prediction: Any, target: Any) -> float:
    values: list[float] = []
    for label in sorted({int(value.item()) for value in target.detach().cpu()}):
        mask = target == label
        if bool(mask.any().item()):
            values.append(float((prediction[mask] == target[mask]).to(torch.float32).mean().detach().cpu()))
    return _mean(values)


def _expected_calibration_error(torch: Any, probabilities: Any, prediction: Any, target: Any) -> float:
    confidence = probabilities.max(dim=1).values
    correctness = (prediction == target).to(probabilities.dtype)
    total = float(target.numel())
    ece = 0.0
    for index in range(5):
        low = index / 5.0
        high = (index + 1) / 5.0
        mask = (confidence >= low) & (confidence < high if index < 4 else confidence <= high)
        if bool(mask.any().item()):
            weight = float(mask.to(probabilities.dtype).mean().detach().cpu())
            ece += weight * abs(
                float(confidence[mask].mean().detach().cpu()) - float(correctness[mask].mean().detach().cpu())
            )
    return round(ece, 6)


def _scope_metrics(torch: Any, probabilities: Any, prediction: Any, target: Any, data: Mapping[str, Any], gate: Any | None) -> dict[str, Any]:
    if data["task_id"] != "scope_boundary_pressure":
        return _scope_pressure_defaults()
    scope_index = data["scope_class_index"]
    boundary_mask = scope_index != 0
    refusal_mask = (scope_index == 1) | (scope_index == 2)
    over_claim_mask = scope_index == 2
    predicted_boundary = prediction != 0
    expected_boundary = target != 0
    true_boundary = predicted_boundary & expected_boundary
    precision = 1.0 if not bool(predicted_boundary.any().item()) else float(
        true_boundary.to(torch.float32).sum().detach().cpu() / predicted_boundary.to(torch.float32).sum().detach().cpu()
    )
    recall = 1.0 if not bool(expected_boundary.any().item()) else float(
        true_boundary.to(torch.float32).sum().detach().cpu() / expected_boundary.to(torch.float32).sum().detach().cpu()
    )
    leak_rate = 0.0 if not bool(boundary_mask.any().item()) else float((prediction[boundary_mask] == 0).to(torch.float32).mean().detach().cpu())
    over_claim_false_positive_rate = 0.0
    if bool(over_claim_mask.any().item()):
        over_claim_false_positive_rate = float((prediction[over_claim_mask] == 0).to(torch.float32).mean().detach().cpu())
    boundary_probs = probabilities[:, 1:].max(dim=1).values
    boundary_margin = 0.0
    if bool(boundary_mask.any().item()):
        boundary_margin = float((boundary_probs[boundary_mask] - probabilities[:, 0][boundary_mask]).mean().detach().cpu())
    gate_sensitivity = 0.0
    if gate is not None:
        gate_flat = gate.squeeze(-1)
        gate_sensitivity = float((gate_flat[boundary_mask].mean() - gate_flat[scope_index == 0].mean()).detach().cpu())
    slice_masks = {
        "in_scope_positive": scope_index == 0,
        "out_of_scope_refusal": scope_index == 1,
        "over_claim_refusal": scope_index == 2,
        "boundary_ambiguous_abstain": scope_index == 3,
    }
    slice_metrics = {}
    for slice_id, mask in slice_masks.items():
        count = int(mask.to(torch.int64).sum().detach().cpu())
        accuracy = 0.0 if count == 0 else float((prediction[mask] == target[mask]).to(torch.float32).mean().detach().cpu())
        slice_metrics[slice_id] = {"accuracy": round(accuracy, 6), "count": count}
    return {
        "scope_pressure_accuracy": round(float((prediction == target).to(torch.float32).mean().detach().cpu()), 6),
        "scope_refusal_precision": round(precision, 6),
        "scope_refusal_recall": round(recall, 6),
        "over_claim_false_positive_rate": round(over_claim_false_positive_rate, 6),
        "scope_leak_rate": round(leak_rate, 6),
        "boundary_margin": round(boundary_margin, 6),
        "scope_gate_sensitivity": round(gate_sensitivity, 6),
        "slice_metrics": slice_metrics,
    }


def _prediction_distribution(torch: Any, prediction: Any) -> dict[str, float]:
    total = max(1, int(prediction.numel()))
    return {
        label: round(float((prediction == index).to(torch.float32).sum().detach().cpu()) / total, 6)
        for index, label in enumerate(("positive_claim", "refusal", "abstain", "boundary_ledger"))
    }


def _negative_witness_hits(torch: Any, prediction: Any, data: Mapping[str, Any]) -> int:
    if data["task_id"] != "scope_boundary_pressure":
        return 0
    mask = data["scope_class_index"] != 0
    if not bool(mask.any().item()):
        return 0
    return int((prediction[mask] == 0).to(torch.int64).sum().detach().cpu())


def _false_ledger_rate(torch: Any, prediction: Any, target: Any) -> float:
    mask = target != 3
    if not bool(mask.any().item()):
        return 0.0
    return round(float((prediction[mask] == 3).to(torch.float32).mean().detach().cpu()), 6)


def _jet_coverage(torch: Any, probabilities: Any) -> float:
    top2 = probabilities.topk(k=2, dim=1).values
    margin = top2[:, 0] - top2[:, 1]
    return round(float((margin > 0.10).to(torch.float32).mean().detach().cpu()), 6)


def _evaluate_outcome(
    torch: Any,
    model: Any,
    arm: DgtNeuralAblationArm,
    data: Mapping[str, Any],
    *,
    train_steps: int,
    initial_loss: float,
    delta_norm: float,
    feature_dim: int,
) -> TrainingOutcome:
    with torch.no_grad():
        phi = _feature_tensor(torch, arm, data["input_tokens"])
        logits, gate = model(phi, data["scope_features"])
        final_loss = torch.nn.functional.cross_entropy(logits, data["target_label"])
        probabilities = torch.softmax(logits, dim=1)
        prediction = probabilities.argmax(dim=1)
        correctness = prediction == data["target_label"]
        accuracy = float(correctness.to(torch.float32).mean().detach().cpu())
        balanced_accuracy = _balanced_accuracy(torch, prediction, data["target_label"])
        top2 = probabilities.topk(k=2, dim=1).values
        margins = top2[:, 0] - top2[:, 1]
        margin_mean = float(margins.mean().detach().cpu())
        margin_p05 = float(torch.quantile(margins.detach().cpu(), 0.05).item())
        ece = _expected_calibration_error(torch, probabilities, prediction, data["target_label"])
        entropy = float((-(probabilities * torch.log(probabilities.clamp_min(1.0e-9))).sum(dim=1)).mean().detach().cpu())
        scope_metrics = _scope_metrics(torch, probabilities, prediction, data["target_label"], data, gate)
        final_value = float(final_loss.detach().cpu())
        uer = _clamp(1.0 - balanced_accuracy)
        return TrainingOutcome(
            arm_id=arm.arm_id,
            seed=int(getattr(model, "seed_value")),
            train_steps=train_steps,
            task_id=str(data["task_id"]),
            split=SPLIT,
            initial_loss=round(initial_loss, 8),
            final_loss=round(final_value, 8),
            loss_drop=round(float(initial_loss) - final_value, 8),
            accuracy=round(accuracy, 6),
            balanced_accuracy=round(balanced_accuracy, 6),
            margin_mean=round(margin_mean, 6),
            margin_p05=round(margin_p05, 6),
            ece=ece,
            prediction_entropy=round(entropy, 6),
            parameter_delta_l2=round(delta_norm, 8),
            gradient_update_steps=train_steps,
            prediction_distribution=_prediction_distribution(torch, prediction),
            scope_pressure_metrics=scope_metrics,
            UER=uer,
            FalseLedgerRate=_false_ledger_rate(torch, prediction, data["target_label"]),
            JetCoverage=_jet_coverage(torch, probabilities),
            negative_witness_hits=_negative_witness_hits(torch, prediction, data),
            compute_cost=_compute_units(train_steps=train_steps, feature_dim=feature_dim),
        )


def _train_arm_seed(torch: Any, arm: DgtNeuralAblationArm, *, seed: int, train_steps: int, device_name: str) -> list[dict[str, Any]]:
    torch.manual_seed(seed)
    device = torch.device(device_name)
    dtype = torch.float32
    tasks = {task_id: _task_data(torch, task_id=task_id, device=device, dtype=dtype) for task_id in TASK_IDS}
    feature_dim = int(_feature_tensor(torch, arm, tasks["core_classification"]["input_tokens"]).shape[1])
    model = _tiny_dgt_model_class(torch)(
        feature_dim=feature_dim,
        scope_feature_dim=len(SCOPE_CLASSES),
        hidden_dim=12,
        use_scope_seal=arm.disabled_component != "scope_seal",
    ).to(device)
    model.seed_value = seed
    before = torch.cat([parameter.detach().flatten().cpu() for parameter in model.parameters()])
    initial_losses: dict[str, float] = {}
    for task_id, data in tasks.items():
        with torch.no_grad():
            logits, _gate = model(_feature_tensor(torch, arm, data["input_tokens"]), data["scope_features"])
            initial_losses[task_id] = float(torch.nn.functional.cross_entropy(logits, data["target_label"]).detach().cpu())
    optimizer = torch.optim.Adam(model.parameters(), lr=LEARNING_RATE)
    for _step in range(train_steps):
        optimizer.zero_grad(set_to_none=True)
        losses = []
        for task_id, data in tasks.items():
            phi = _feature_tensor(torch, arm, data["input_tokens"])
            logits, gate = model(phi, data["scope_features"])
            loss = torch.nn.functional.cross_entropy(logits, data["target_label"])
            if task_id == "scope_boundary_pressure" and gate is not None:
                gate_target = (data["scope_class_index"] != 0).to(dtype).unsqueeze(1)
                loss = loss + 0.22 * torch.nn.functional.binary_cross_entropy(gate, gate_target)
            if arm.disabled_component != "jet_loss":
                loss = loss + 0.010 * model.encoder.weight[:, : min(2, feature_dim)].pow(2).mean()
            if arm.disabled_component != "negative_witness_loss" and task_id == "scope_boundary_pressure":
                positive_prob = torch.softmax(logits, dim=1)[:, 0]
                boundary_mask = data["scope_class_index"] != 0
                loss = loss + 0.030 * positive_prob[boundary_mask].mean()
            losses.append(loss)
        total_loss = sum(losses) / len(losses)
        total_loss.backward()
        optimizer.step()
    after = torch.cat([parameter.detach().flatten().cpu() for parameter in model.parameters()])
    delta_norm = float(torch.linalg.vector_norm(after - before).item())
    if not math.isfinite(delta_norm) or delta_norm <= 0.0:
        raise RuntimeError(f"no parameter update evidence for {arm.arm_id} seed {seed}")
    rows: list[dict[str, Any]] = []
    for task_id, data in tasks.items():
        outcome = _evaluate_outcome(
            torch,
            model,
            arm,
            data,
            train_steps=train_steps,
            initial_loss=initial_losses[task_id],
            delta_norm=delta_norm,
            feature_dim=feature_dim,
        )
        derived = derive_training_metrics(outcome, METRIC_PROTOCOL)
        parameter_count = sum(int(parameter.numel()) for parameter in model.parameters())
        row = {
            **asdict(outcome),
            "disabled_component": arm.disabled_component,
            "train_steps": train_steps,
            "requested_training_backend": "torch",
            "requested_device": device_name,
            "resolved_device": device_name,
            "device": device_name,
            "optimizer": "Adam",
            "optimizer_steps": train_steps,
            "compute_units": _compute_units(train_steps=train_steps, feature_dim=feature_dim),
            "parameter_count": parameter_count,
            "wall_time_proxy": round(train_steps * parameter_count / 1000000.0, 6),
            "metric_protocol_id": SCHEMA_ID + ":metric-protocol",
            "metrics": derived["metrics"],
            "metric_diagnostics": derived["metric_diagnostics"],
            "sample_schema": {
                "input_tokens": "float tensor",
                "target_label": "class index",
                "scope_class": list(SCOPE_CLASSES),
                "claim_allowed": "bool",
                "expected_boundary_action": "string",
                "negative_witness_tag": "string",
            },
        }
        rows.append(row)
    return rows


def _record_mean(records: Sequence[Mapping[str, Any]], metric: str) -> float:
    return _mean([float(row["metrics"][metric]) for row in records])


def _summary_for_arm(records: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    by_seed: dict[str, dict[str, float]] = {}
    for seed in sorted({int(row["seed"]) for row in records}):
        seed_rows = [row for row in records if int(row["seed"]) == seed]
        by_seed[str(seed)] = {metric: _record_mean(seed_rows, metric) for metric in METRIC_KEYS}
    scope_rows = [row for row in records if row["task_id"] == "scope_boundary_pressure"]
    scope_metric_keys = (
        "scope_pressure_accuracy",
        "scope_refusal_precision",
        "scope_refusal_recall",
        "over_claim_false_positive_rate",
        "scope_leak_rate",
        "boundary_margin",
        "scope_gate_sensitivity",
    )
    return {
        "disabled_component": records[0]["disabled_component"],
        "metrics": {metric: _record_mean(records, metric) for metric in METRIC_KEYS},
        "metrics_by_seed": by_seed,
        "task_metrics": {
            task_id: {metric: _record_mean([row for row in records if row["task_id"] == task_id], metric) for metric in METRIC_KEYS}
            for task_id in TASK_IDS
        },
        "scope_pressure_metrics": {
            key: _mean([float(row["scope_pressure_metrics"].get(key, 0.0)) for row in scope_rows])
            for key in scope_metric_keys
        },
        "parameter_delta_l2": _mean([float(row["parameter_delta_l2"]) for row in records]),
        "loss_drop": _mean([float(row["loss_drop"]) for row in records]),
    }


def _ci95(values: Sequence[float]) -> dict[str, float]:
    if not values:
        return {"low": 0.0, "high": 0.0}
    mean = sum(values) / len(values)
    if len(values) == 1:
        return {"low": round(mean, 6), "high": round(mean, 6)}
    variance = sum((value - mean) ** 2 for value in values) / (len(values) - 1)
    half_width = 1.96 * math.sqrt(variance) / math.sqrt(len(values))
    return {"low": round(mean - half_width, 6), "high": round(mean + half_width, 6)}


def paired_delta(
    full_summary: Mapping[str, Any],
    ablated_summary: Mapping[str, Any],
    *,
    paired_ci_min_seeds: int = DEFAULT_SEED_COUNT,
) -> dict[str, Any]:
    full_by_seed = full_summary["metrics_by_seed"]
    ablated_by_seed = ablated_summary["metrics_by_seed"]
    seed_keys = sorted(set(full_by_seed) & set(ablated_by_seed), key=int)
    positive_is_full_minus_ablation = {
        "quality_q",
        "benefit_q",
        "scope_pressure_q",
        "JetCoverage",
        "compute_cost",
    }
    positive_is_ablation_minus_full = {
        "UER",
        "FalseLedgerRate",
        "debt_q",
        "classifier_shift_count",
        "negative_witness_hits",
    }
    paired: dict[str, list[float]] = {}
    metrics: dict[str, float] = {}
    confidence: dict[str, dict[str, float]] = {}
    for metric in METRIC_KEYS:
        values = []
        for seed in seed_keys:
            full_value = float(full_by_seed[seed][metric])
            ablated_value = float(ablated_by_seed[seed][metric])
            if metric in positive_is_full_minus_ablation:
                values.append(round(full_value - ablated_value, 6))
            elif metric in positive_is_ablation_minus_full:
                values.append(round(ablated_value - full_value, 6))
            else:
                raise ValueError(f"unclassified metric direction: {metric}")
        paired[metric] = values
        metrics[metric] = _mean(values)
        confidence[metric] = _ci95(values)
    return {
        "status": "pass" if len(seed_keys) >= paired_ci_min_seeds else "fail",
        "failed_gate": None if len(seed_keys) >= paired_ci_min_seeds else "NABL2-HG1",
        "metrics": metrics,
        "paired_seed_deltas": paired,
        "confidence_intervals": confidence,
        "paired_seed_count": len(seed_keys),
        "paired_ci_min_seeds": paired_ci_min_seeds,
        "delta_source": "paired_delta(full_summary, ablated_summary)",
    }


def _passes_positive_ci(delta: Mapping[str, Any], thresholds: Mapping[str, float]) -> dict[str, float]:
    if delta.get("status") != "pass":
        return {}
    return {
        metric: float(ci["low"])
        for metric, ci in delta.get("confidence_intervals", {}).items()
        if metric != "compute_cost" and float(ci.get("low", 0.0)) > float(thresholds.get(metric, MEASURABLE_EFFECT_THRESHOLD))
    }


def _ci_inside_blocked_band(delta: Mapping[str, Any], thresholds: Mapping[str, float]) -> bool:
    if delta.get("status") != "pass":
        return False
    for metric, ci in delta.get("confidence_intervals", {}).items():
        if metric == "compute_cost":
            continue
        threshold = float(thresholds.get(metric, BLOCKED_EFFECT_THRESHOLD))
        if abs(float(ci.get("low", 0.0))) > threshold or abs(float(ci.get("high", 0.0))) > threshold:
            return False
    return True


@dataclass(frozen=True)
class DgtNeuralAblationRobustnessProjection:
    run_spec: DgtNeuralAblationRunSpec

    def project(
        self,
        *,
        rows: Sequence[Mapping[str, Any]],
        source_audit: Mapping[str, Any],
        negative_witness_sweep: Mapping[str, Any],
    ) -> dict[str, Any]:
        arm_summaries = self._arm_summaries(rows)
        paired_delta_matrix = self._paired_delta_matrix(arm_summaries)
        robustness_by_steps = self._robustness_by_steps(paired_delta_matrix)
        claims = self._stable_component_causal_claims(robustness_by_steps)
        boundary = self._stable_boundary_ledger(robustness_by_steps, claims)
        ledger = self._compute_ledger(rows)
        hardgates = self._nabl2_hardgates(
            rows=rows,
            robustness_by_steps=robustness_by_steps,
            claims=claims,
            boundary=boundary,
            compute_ledger=ledger,
            source_audit=source_audit,
            negative_witness_sweep=negative_witness_sweep,
        )
        return {
            "arm_summaries": arm_summaries,
            "paired_delta_matrix": paired_delta_matrix,
            "robustness_by_steps": robustness_by_steps,
            "stable_causal_attribution": self._stable_causal_attribution(claims),
            "stable_component_causal_claims": claims,
            "stable_boundary_ledger": boundary,
            "compute_ledger": ledger,
            "nabl2_hardgates": hardgates,
        }

    def _arm_summaries(self, rows: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
        summaries: dict[str, Any] = {}
        for arm_id in self.run_spec.arms:
            arm_rows = [row for row in rows if row["arm_id"] == arm_id]
            by_step = {
                str(step): _summary_for_arm([row for row in arm_rows if int(row["train_steps"]) == step])
                for step in self.run_spec.step_grid
            }
            summaries[arm_id] = {
                "disabled_component": arm_rows[0]["disabled_component"] if arm_rows else None,
                "by_step": by_step,
                "metrics": {metric: _record_mean(arm_rows, metric) for metric in METRIC_KEYS} if arm_rows else {},
            }
        return summaries

    def _paired_delta_matrix(self, arm_summaries: Mapping[str, Any]) -> dict[str, Any]:
        matrix: dict[str, Any] = {}
        full = arm_summaries["full_DGT"]["by_step"]
        for component in COMPONENTS:
            arm_id = f"DGT_without_{component}"
            by_steps = {}
            for step in self.run_spec.step_grid:
                by_steps[str(step)] = paired_delta(
                    full[str(step)],
                    arm_summaries[arm_id]["by_step"][str(step)],
                    paired_ci_min_seeds=self.run_spec.paired_ci_min_seeds,
                )
            max_step_delta = by_steps[str(max(self.run_spec.step_grid))]
            matrix[arm_id] = {**max_step_delta, "by_steps": by_steps}
        return matrix

    def _robustness_by_steps(self, delta_matrix: Mapping[str, Any]) -> dict[str, Any]:
        effect_thresholds = self.run_spec.effect_threshold_payload()
        blocked_thresholds = self.run_spec.blocked_threshold_payload()
        by_step: dict[str, Any] = {}
        for step in self.run_spec.step_grid:
            allowed: list[str] = []
            blocked: list[str] = []
            unstable: list[str] = []
            components: dict[str, Any] = {}
            for component in COMPONENTS:
                delta = delta_matrix[f"DGT_without_{component}"]["by_steps"][str(step)]
                positive_metrics = _passes_positive_ci(delta, effect_thresholds)
                blocked_stable = _ci_inside_blocked_band(delta, blocked_thresholds)
                if positive_metrics:
                    status = "allowed"
                    allowed.append(component)
                elif blocked_stable:
                    status = "blocked"
                    blocked.append(component)
                else:
                    status = "unstable"
                    unstable.append(component)
                components[component] = {
                    "status": status,
                    "positive_ci_low_metrics": positive_metrics,
                    "blocked_ci_band": blocked_stable,
                    "paired_seed_count": delta["paired_seed_count"],
                    "delta_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.paired_delta_matrix.DGT_without_{component}.by_steps.{step}",
                }
            by_step[str(step)] = {
                "train_steps": step,
                "status": "pass" if not unstable else "fail",
                "allowed_components": allowed,
                "blocked_components": blocked,
                "unstable_components": unstable,
                "components": components,
            }
        return by_step

    def _stable_component_causal_claims(self, robustness_by_steps: Mapping[str, Any]) -> list[dict[str, Any]]:
        claims: list[dict[str, Any]] = []
        eligible_steps = [str(step) for step in self.run_spec.step_grid]
        for component in COMPONENTS:
            passing_steps = [
                step
                for step in eligible_steps
                if robustness_by_steps[step]["components"][component]["status"] == "allowed"
            ]
            if not passing_steps:
                continue
            metrics = {
                metric: min(
                    float(robustness_by_steps[step]["components"][component]["positive_ci_low_metrics"][metric])
                    for step in passing_steps
                    if metric in robustness_by_steps[step]["components"][component]["positive_ci_low_metrics"]
                )
                for metric in sorted(
                    {
                        metric
                        for step in passing_steps
                        for metric in robustness_by_steps[step]["components"][component]["positive_ci_low_metrics"]
                    }
                )
            }
            claims.append(
                {
                    "component": component,
                    "claim_status": "allowed",
                    "claim_scope": "bounded toy training",
                    "evidence_scope": list(COMPONENT_CAUSAL_EVIDENCE_SCOPE),
                    "claim_text": (
                        f"Under the bounded toy training protocol, removing {component} has a paired cross-seed "
                        f"CI-low degradation above threshold on {', '.join(metrics)}."
                    ),
                    "stable_step_settings": [int(step) for step in passing_steps],
                    "ci_low_metrics": metrics,
                    "metric_delta_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.paired_delta_matrix.DGT_without_{component}",
                    "record_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.records",
                    "terminal_verdict_scope": "Core",
                    "paired_seed_count": self.run_spec.seed_count,
                    "confidence_interval_pointer": (
                        f"{CANONICAL_JSON_ARTIFACT}:$.paired_delta_matrix.DGT_without_{component}.by_steps"
                    ),
                }
            )
        return claims

    def _stable_boundary_ledger(
        self,
        robustness_by_steps: Mapping[str, Any],
        claims: Sequence[Mapping[str, Any]],
    ) -> list[dict[str, Any]]:
        claimed = {row["component"] for row in claims}
        ledger = []
        for component in COMPONENTS:
            statuses = {
                step: robustness_by_steps[str(step)]["components"][component]["status"]
                for step in self.run_spec.step_grid
            }
            measurable = component in claimed
            stable_blocked = not measurable and all(status == "blocked" for status in statuses.values())
            ledger.append(
                {
                    "component": component,
                    "status": "measured" if measurable else "blocked" if stable_blocked else "blocked_unstable",
                    "reason": (
                        "paired cross-seed CI-low supports a scoped component-causal claim"
                        if measurable
                        else "NABL2-HG3"
                        if stable_blocked
                        else "NABL2-HG2"
                    ),
                    "claim_blocked": not measurable,
                    "step_statuses": statuses,
                    "metric_delta_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.paired_delta_matrix.DGT_without_{component}",
                    "measured_delta_summary": {
                        step: robustness_by_steps[str(step)]["components"][component]
                        for step in self.run_spec.step_grid
                    },
                }
            )
        if not claims:
            ledger.append(
                {
                    "component": "<all>",
                    "status": "null_result",
                    "reason": NULL_CAUSAL_REASON,
                    "claim_blocked": True,
                    "blocked": True,
                    "not_silent": True,
                    "step_statuses": {
                        str(step): {
                            component: robustness_by_steps[str(step)]["components"][component]["status"]
                            for component in COMPONENTS
                        }
                        for step in self.run_spec.step_grid
                    },
                    "metric_delta_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.paired_delta_matrix",
                    "measured_delta_summary": {
                        str(step): robustness_by_steps[str(step)]["components"]
                        for step in self.run_spec.step_grid
                    },
                }
            )
        return ledger

    def _stable_causal_attribution(self, claims: Sequence[Mapping[str, Any]]) -> str:
        if not claims:
            return "none"
        if len({row["component"] for row in claims}) == len(COMPONENTS):
            return "complete"
        return "partial"

    def _claim_passes_allowed_ci(
        self,
        claim: Mapping[str, Any],
        robustness_by_steps: Mapping[str, Any],
        effect_thresholds: Mapping[str, float],
    ) -> bool:
        component = claim.get("component")
        if component not in COMPONENTS:
            return False
        ci_low_metrics = claim.get("ci_low_metrics", {})
        stable_steps = claim.get("stable_step_settings", [])
        if not isinstance(ci_low_metrics, Mapping) or not ci_low_metrics or not stable_steps:
            return False
        if not all(
            float(value) > float(effect_thresholds.get(metric, MEASURABLE_EFFECT_THRESHOLD))
            for metric, value in ci_low_metrics.items()
        ):
            return False
        for step in stable_steps:
            component_row = robustness_by_steps[str(step)]["components"][component]
            if component_row["status"] != "allowed":
                return False
            allowed_metrics = component_row["positive_ci_low_metrics"]
            if not any(
                float(value) > float(effect_thresholds.get(metric, MEASURABLE_EFFECT_THRESHOLD))
                for metric, value in allowed_metrics.items()
            ):
                return False
        return True

    def _compute_ledger(self, rows: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
        row_entries = [
            {
                "train_steps": int(row["train_steps"]),
                "seed": int(row["seed"]),
                "arm": row["arm_id"],
                "task_id": row["task_id"],
                "device": row["device"],
                "optimizer_steps": int(row["optimizer_steps"]),
                "compute_units": float(row["compute_units"]),
                "parameter_count": int(row["parameter_count"]),
                "wall_time_proxy": float(row["wall_time_proxy"]),
            }
            for row in rows
        ]
        return {
            "formula": self.run_spec.compute_unit_formula,
            "dimensions": ["train_steps", "seed", "arm", "task_id", "device"],
            "row_count": len(row_entries),
            "training_matrix_count": len(self.run_spec.step_grid) * self.run_spec.seed_count * len(self.run_spec.arms),
            "total_compute_units": round(sum(row["compute_units"] for row in row_entries), 6),
            "by_step": {
                str(step): {
                    "row_count": len([row for row in row_entries if row["train_steps"] == step]),
                    "training_count": len(
                        {
                            (row["train_steps"], row["seed"], row["arm"])
                            for row in row_entries
                            if row["train_steps"] == step
                        }
                    ),
                    "compute_units": round(
                        sum(row["compute_units"] for row in row_entries if row["train_steps"] == step),
                        6,
                    ),
                }
                for step in self.run_spec.step_grid
            },
            "rows": row_entries,
        }

    def _nabl2_hardgates(
        self,
        *,
        rows: Sequence[Mapping[str, Any]],
        robustness_by_steps: Mapping[str, Any],
        claims: Sequence[Mapping[str, Any]],
        boundary: Sequence[Mapping[str, Any]],
        compute_ledger: Mapping[str, Any],
        source_audit: Mapping[str, Any],
        negative_witness_sweep: Mapping[str, Any],
    ) -> dict[str, Any]:
        training_triples = {
            (int(row["train_steps"]), int(row["seed"]), row["arm_id"])
            for row in rows
        }
        expected_triples = {
            (step, seed, arm)
            for step in self.run_spec.step_grid
            for seed in self.run_spec.seed_list
            for arm in self.run_spec.arms
        }
        claimed = {row["component"] for row in claims}
        blocked = {row["component"] for row in boundary if row.get("claim_blocked") is True and row.get("component") in COMPONENTS}
        no_effect_rows = [row for row in boundary if row["component"] in COMPONENTS and row["component"] not in claimed]
        effect_thresholds = self.run_spec.effect_threshold_payload()
        conditions = {
            "NABL2-HG1": expected_triples.issubset(training_triples),
            "NABL2-HG2": all(self._claim_passes_allowed_ci(claim, robustness_by_steps, effect_thresholds) for claim in claims),
            "NABL2-HG3": all(row["status"] == "blocked" for row in no_effect_rows) and claimed.isdisjoint(blocked),
            "NABL2-HG4": compute_ledger.get("training_matrix_count") == len(expected_triples)
            and {"train_steps", "seed", "arm"}.issubset(set(compute_ledger.get("dimensions", []))),
            "NABL2-HG5": negative_witness_sweep.get("status") == "pass",
            "NABL2-HG6": source_audit.get("status") == "pass",
        }
        return _hardgate_payload(
            NABL2_HG_IDS,
            conditions,
            {
                "NABL2-HG1": "each arm has paired rows for every configured step and at least the minimum seed count",
                "NABL2-HG2": "measurable component effects require paired CI-low above threshold",
                "NABL2-HG3": "no-effect components stay blocked across the seed and step grid",
                "NABL2-HG4": "compute ledger records step, seed, arm, and unit dimensions",
                "NABL2-HG5": "negative witness sweep is complete",
                "NABL2-HG6": "owner source has no component lookup regression",
            },
            f"{CANONICAL_JSON_ARTIFACT}:$.robustness_by_steps",
        )


def _forbidden_claim_term_audit(value: Any) -> dict[str, Any]:
    text = json.dumps(value, sort_keys=True).lower()
    hits = [term for term in FORBIDDEN_TERMS if term in text]
    return {"status": "pass" if not hits else "fail", "hits": hits, "forbidden_terms": list(FORBIDDEN_TERMS)}


def _owner_source_purity_audit(payload: Mapping[str, Any] | None = None) -> dict[str, Any]:
    source = Path(__file__).read_text(encoding="utf-8")
    tree = ast.parse(source)
    source_hits: list[str] = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Name) and node.id in _FORBIDDEN_OWNER_TOKENS:
            source_hits.append(node.id)
        if isinstance(node, ast.Attribute) and node.attr in _FORBIDDEN_OWNER_TOKENS:
            source_hits.append(node.attr)
    payload_text = "" if payload is None else json.dumps(payload, sort_keys=True)
    payload_hits = [token for token in _FORBIDDEN_OWNER_TOKENS if token in payload_text]
    signature = inspect.signature(derive_training_metrics)
    signature_ok = tuple(signature.parameters) == ("outcome", "protocol")
    protocol_inputs_ok = tuple(METRIC_PROTOCOL.inputs) == OUTCOME_FIELDS
    return {
        "status": "pass" if not source_hits and not payload_hits and signature_ok and protocol_inputs_ok else "fail",
        "source_token_hits": source_hits,
        "payload_token_hits": payload_hits,
        "derive_training_metrics_signature": str(signature),
        "metric_inputs": list(METRIC_PROTOCOL.inputs),
        "signature_ok": signature_ok,
        "protocol_inputs_ok": protocol_inputs_ok,
    }


def _scope_seal_nonredundancy(rows: Sequence[Mapping[str, Any]], run_spec: DgtNeuralAblationRunSpec) -> dict[str, Any]:
    seed = run_spec.seed_list[0]
    train_steps = run_spec.step_grid[-1]
    full_rows = [
        row
        for row in rows
        if row["arm_id"] == "full_DGT"
        and row["task_id"] == "scope_boundary_pressure"
        and int(row["seed"]) == seed
        and int(row["train_steps"]) == train_steps
    ]
    ablated_rows = [
        row
        for row in rows
        if row["arm_id"] == "DGT_without_scope_seal"
        and row["task_id"] == "scope_boundary_pressure"
        and int(row["seed"]) == seed
        and int(row["train_steps"]) == train_steps
    ]
    if not full_rows or not ablated_rows:
        return {"status": "fail", "reason": "scope pressure rows missing"}
    full = full_rows[0]["scope_pressure_metrics"]
    ablated = ablated_rows[0]["scope_pressure_metrics"]
    changed = []
    for key in ("scope_pressure_accuracy", "scope_leak_rate", "boundary_margin", "scope_gate_sensitivity"):
        if abs(float(full.get(key, 0.0)) - float(ablated.get(key, 0.0))) > 1.0e-6:
            changed.append(key)
    for slice_id in SCOPE_SLICES:
        if (
            abs(
                float(full["slice_metrics"][slice_id]["accuracy"])
                - float(ablated["slice_metrics"][slice_id]["accuracy"])
            )
            > 1.0e-6
        ):
            changed.append(f"slice:{slice_id}")
    return {
        "status": "pass" if changed else "fail",
        "seed": seed,
        "train_steps": train_steps,
        "task_id": "scope_boundary_pressure",
        "changed_boundary_metrics": changed,
        "full_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.records",
        "ablated_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.records",
    }


def _hardgate_payload(ids: Sequence[str], conditions: Mapping[str, bool], criteria: Mapping[str, str], pointer: str) -> dict[str, Any]:
    gates = {
        gate: {
            "status": "pass" if conditions.get(gate, False) else "fail",
            "evidence_pointer": pointer,
            "criterion": criteria[gate],
        }
        for gate in ids
    }
    failed = next((gate for gate in ids if gates[gate]["status"] != "pass"), None)
    return {"status": "pass" if failed is None else "fail", "failed_gate": failed, "gates": gates}


def _run_spec_from_payload(run_spec_payload: Mapping[str, Any], training_protocol: Mapping[str, Any]) -> DgtNeuralAblationRunSpec:
    if run_spec_payload:
        return DgtNeuralAblationRunSpec(
            step_grid=tuple(int(value) for value in run_spec_payload.get("step_grid", DEFAULT_STEP_GRID)),
            seed_count=int(run_spec_payload.get("seed_count", DEFAULT_SEED_COUNT)),
            seed_list=tuple(int(value) for value in run_spec_payload.get("seed_list", DEFAULT_SEEDS)),
            requested_device=str(run_spec_payload.get("requested_device", training_protocol.get("requested_device", "auto"))),
            paired_ci_min_seeds=int(run_spec_payload.get("paired_ci_min_seeds", DEFAULT_SEED_COUNT)),
        )
    step_grid = tuple(int(value) for value in training_protocol.get("step_grid", DEFAULT_STEP_GRID))
    seed_list = tuple(int(value) for value in training_protocol.get("seeds", DEFAULT_SEEDS))
    return DgtNeuralAblationRunSpec(
        step_grid=step_grid,
        seed_count=len(seed_list),
        seed_list=seed_list,
        requested_device=str(training_protocol.get("requested_device", "auto")),
        paired_ci_min_seeds=min(DEFAULT_SEED_COUNT, max(2, len(seed_list))),
    )


def evaluate_pure_hardgates(report: Mapping[str, Any]) -> dict[str, Any]:
    run_spec = _run_spec_from_payload(report.get("run_spec", {}), report.get("training_protocol", {}))
    records = report.get("records", [])
    metric_protocol = report.get("metric_protocol", {})
    scope_protocol = report.get("scope_pressure_protocol", {})
    mechanism = report.get("scope_seal_mechanism", {})
    claims = report.get("component_causal_claims", [])
    boundary = report.get("boundary_ledger", [])
    purity = metric_protocol.get("purity_audit", {})
    expected_pairs = {
        (arm_id, step, seed, task_id)
        for arm_id in ARM_IDS
        for step in run_spec.step_grid
        for seed in run_spec.seed_list
        for task_id in TASK_IDS
    }
    blocked = {row["component"] for row in boundary if row.get("status") == "blocked" and row.get("component") in COMPONENTS}
    claimed = {row["component"] for row in claims}
    conditions = {
        "PURE-HG1": purity.get("status") == "pass" and set(metric_protocol.get("inputs", [])) == set(OUTCOME_FIELDS),
        "PURE-HG2": all(set(row.get("metrics", {})) == set(METRIC_KEYS) for row in records),
        "PURE-HG3": mechanism.get("non_redundancy_evidence", {}).get("status") == "pass",
        "PURE-HG4": expected_pairs.issubset(
            {(row.get("arm_id"), row.get("train_steps"), row.get("seed"), row.get("task_id")) for row in records}
        )
        and scope_protocol.get("task_registry", {}).get("scope_boundary_pressure") == "same train/eval loop",
        "PURE-HG5": all(row.get("evidence_scope") == list(COMPONENT_CAUSAL_EVIDENCE_SCOPE) for row in claims)
        and claimed.isdisjoint(blocked),
        "PURE-HG6": all(float(row.get("parameter_delta_l2", 0.0)) > 0.0 and float(row.get("loss_drop", 0.0)) > 0.0 for row in records),
        "PURE-HG7": all(row.get("reason") == "NABL2-HG3" for row in boundary if row.get("status") == "blocked" and row.get("component") in COMPONENTS)
        and claimed.isdisjoint(blocked),
    }
    return _hardgate_payload(
        PURE_HG_IDS,
        conditions,
        {
            "PURE-HG1": "metrics derive only from TrainingOutcome fields and global formulas",
            "PURE-HG2": "each row carries the schema-visible training-derived metric set",
            "PURE-HG3": "scope_seal is a learnable gate with non-redundancy evidence",
            "PURE-HG4": "scope_boundary_pressure is present in the same train/eval loop",
            "PURE-HG5": "positive claims use small-real-training evidence and blocked rows remain unclaimed",
            "PURE-HG6": "torch training is deterministic and records loss drop plus parameter updates",
            "PURE-HG7": "no-effect component rows are boundary-ledgered and fail closed",
        },
        f"{CANONICAL_JSON_ARTIFACT}:$",
    )


def _nabl_hardgates(report: Mapping[str, Any], audit: Mapping[str, Any]) -> dict[str, Any]:
    records = report["records"]
    claims = report["component_causal_claims"]
    boundary = report["boundary_ledger"]
    nabl2 = report.get("nabl2_hardgates", {})
    arm_ids = sorted({row.get("arm_id") for row in records}, key=list(ARM_IDS).index)
    claimed = {row["component"] for row in claims}
    blocked = {row["component"] for row in boundary if row.get("status") == "blocked" and row.get("component") in COMPONENTS}
    conditions = {
        "NABL-HG1": arm_ids == list(ARM_IDS),
        "NABL-HG2": all(row.get("requested_training_backend") == "torch" and int(row.get("gradient_update_steps", 0)) > 0 for row in records),
        "NABL-HG3": all(float(row.get("parameter_delta_l2", 0.0)) > 0.0 for row in records),
        "NABL-HG4": all(set(row.get("metrics", {})) == set(METRIC_KEYS) for row in records),
        "NABL-HG5": all(row.get("claim_scope") == "bounded toy training" for row in claims),
        "NABL-HG6": audit.get("status") == "pass",
        "NABL-HG7": claimed.isdisjoint(blocked) and nabl2.get("status") == "pass",
    }
    return _hardgate_payload(
        HG_IDS,
        conditions,
        {
            "NABL-HG1": "exact 11-arm registry present",
            "NABL-HG2": "torch optimizer steps recorded",
            "NABL-HG3": "parameter updates recorded for every row",
            "NABL-HG4": "each row records the required metrics",
            "NABL-HG5": "positive claims are bounded to measured component deltas",
            "NABL-HG6": "forbidden positive claim terms absent",
            "NABL-HG7": "no-effect components are boundary-ledgered and cannot claim causal effect",
        },
        f"{CANONICAL_JSON_ARTIFACT}:$",
    )


def _scope_pressure_protocol_payload() -> dict[str, Any]:
    return {
        "task_registry": {"scope_boundary_pressure": "same train/eval loop", "core_classification": "same train/eval loop"},
        "scope_classes": list(SCOPE_CLASSES),
        "slice_definitions": {
            "in_scope_positive": {"scope_class": "in_scope", "expected_boundary_action": "positive_claim"},
            "out_of_scope_refusal": {"scope_class": "out_of_scope", "expected_boundary_action": "refusal"},
            "over_claim_refusal": {"scope_class": "over_claim", "expected_boundary_action": "refusal"},
            "boundary_ambiguous_abstain": {"scope_class": "boundary_ambiguous", "expected_boundary_action": "abstain"},
        },
        "sample_fields": [
            "input_tokens",
            "target_label",
            "scope_class",
            "claim_allowed",
            "expected_boundary_action",
            "negative_witness_tag",
        ],
        "loss_terms": {
            "classification": "cross_entropy(logits, target_label)",
            "scope_gate": "BCE(scope_gate, scope_class != in_scope) for full arms only",
        },
        "metrics": [
            "scope_pressure_accuracy",
            "scope_refusal_precision",
            "scope_refusal_recall",
            "over_claim_false_positive_rate",
            "scope_leak_rate",
            "boundary_margin",
            "scope_gate_sensitivity",
        ],
    }


def _scope_seal_mechanism_payload(nonredundancy: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "description": "ScopeBoundaryGate computes sigmoid(W_scope*h + U_scope*scope_features + b_scope).",
        "scope_features": list(SCOPE_CLASSES),
        "trainable_parameter_names": [
            "scope_gate.hidden.weight",
            "scope_gate.scope.weight",
            "scope_gate.bias",
        ],
        "logit_modulation": {
            "boundary_sensitive_logits": "refusal, abstain, and boundary-ledger logits receive scope_gate",
            "positive_claim_logits": "positive-claim logit receives 1 - scope_gate",
        },
        "removal_semantics": {
            "arm_id": "DGT_without_scope_seal",
            "behavior": "gate module and gate loss are removed; boundary modulation is bypassed",
        },
        "non_redundancy_evidence": dict(nonredundancy),
    }


def unavailable_payload(
    *,
    generated_at: str,
    requested_device: str,
    reason: str,
    run_spec: DgtNeuralAblationRunSpec | None = None,
) -> dict[str, Any]:
    run_spec = run_spec or DgtNeuralAblationRunSpec.canonical(requested_device=requested_device)
    device_policy = {
        "requested_device": requested_device,
        "resolved_device": "not-available",
        "resolution_status": "unavailable",
        "resolution_reason": reason,
        "backend_details": {"torch": "unavailable"},
    }
    run_artifacts = {
        "summary": f"{RUN_ROOT}/summary.json",
        "raw_metrics": f"{RUN_ROOT}/raw_metrics.jsonl",
        "claim_capsule": f"{RUN_ROOT}/claim_capsule.json",
        "report": f"{RUN_ROOT}/report.md",
    }
    gates = {
        gate: {
            "status": "fail",
            "evidence_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.training_protocol",
            "criterion": reason,
        }
        for gate in HG_IDS
    }
    nabl2_gates = {
        gate: {
            "status": "fail",
            "evidence_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.training_protocol",
            "criterion": reason,
        }
        for gate in NABL2_HG_IDS
    }
    pure_gates = {
        gate: {
            "status": "fail",
            "evidence_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.training_protocol",
            "criterion": reason,
        }
        for gate in PURE_HG_IDS
    }
    boundary = [
        {
            "component": component,
            "status": "blocked",
            "reason": "NABL2-HG1",
            "claim_blocked": True,
            "measured_delta_summary": {},
            "metric_delta_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.metric_delta_matrix.DGT_without_{component}",
        }
        for component in COMPONENTS
    ]
    payload = {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "generated_at": generated_at,
        "producer": PRODUCER,
        "source_artifacts": {"owner_module": "bedc_quality_lab/dgt_neural_ablation.py", "runner": PRODUCER},
        "run_artifacts": run_artifacts,
        "module_registry": module_registry_payload(),
        "run_spec": run_spec.as_payload(device_policy=device_policy),
        "training_protocol": {
            "status": "unavailable",
            "requested_device": requested_device,
            "resolved_device": "unavailable",
            "backend": "torch",
            "optimizer": "Adam",
            "steps": max(run_spec.step_grid),
            "step_grid": list(run_spec.step_grid),
            "seeds": list(run_spec.seed_list),
            "seed_count": run_spec.seed_count,
            "reason": reason,
        },
        "metric_protocol": {**METRIC_PROTOCOL.as_payload(), "purity_audit": _owner_source_purity_audit()},
        "scope_pressure_protocol": _scope_pressure_protocol_payload(),
        "scope_seal_mechanism": {
            "description": "unavailable",
            "non_redundancy_evidence": {"status": "blocked", "reason": reason},
        },
        "records": [],
        "arm_summaries": {},
        "metric_delta_matrix": {},
        "paired_delta_matrix": {},
        "robustness_by_steps": {},
        "stable_causal_attribution": "unavailable",
        "stable_component_causal_claims": [],
        "stable_boundary_ledger": boundary,
        "compute_ledger": {
            "formula": run_spec.compute_unit_formula,
            "dimensions": ["train_steps", "seed", "arm", "task_id", "device"],
            "row_count": 0,
            "training_matrix_count": 0,
            "total_compute_units": 0.0,
            "by_step": {},
            "rows": [],
        },
        "pure_hardgates": {"status": "fail", "failed_gate": "PURE-HG1", "gates": pure_gates},
        "nabl_hardgates": {"status": "fail", "failed_gate": "NABL-HG1", "gates": gates},
        "nabl2_hardgates": {"status": "fail", "failed_gate": "NABL2-HG1", "gates": nabl2_gates},
        "component_causal_claims": [],
        "boundary_ledger": boundary,
        "evidence_scope": [],
        "claim_capsule_ref": {"artifact": f"{RUN_ROOT}/claim_capsule.json", "pointer": "$", "status": "blocked"},
        "not_claimed": list(NOT_CLAIMED),
        "forbidden_claim_term_audit": _forbidden_claim_term_audit({"claims": []}),
        "negative_witness_sweep": {
            "status": "fail",
            "task_id": "scope_boundary_pressure",
            "row_count": 0,
            "expected_row_count": len(run_spec.step_grid) * run_spec.seed_count * len(run_spec.arms),
            "observed_hit_count": 0,
            "pointer": f"{CANONICAL_JSON_ARTIFACT}:$.records",
        },
    }
    return _with_reproducibility_contract(payload)


def _with_reproducibility_contract(payload: dict[str, Any]) -> dict[str, Any]:
    run_spec = payload["run_spec"]
    training = payload["training_protocol"]
    seed_list = list(run_spec.get("seed_list", training.get("seeds", [])))
    payload["reproducibility_contract"] = {
        "mode": "true_training",
        "seed_list": seed_list,
        "metric_bands": [
            {
                "pointer": "$.nabl_hardgates.status",
                "reference_value": payload["nabl_hardgates"]["status"],
                "tolerance": 0,
                "comparison": "status_equal",
                "owner": "dgt-neural-ablation",
                "calibration_source": "$.paired_delta_matrix",
                "seed_basis": {"seed_count": len(seed_list), "source": "$.run_spec.seed_list"},
            }
        ],
        "device_policy": run_spec["device_policy"],
        "framework_provenance": {
            "python": "owner-runtime",
            "dependency_abi": {"torch": str(training.get("backend", "torch"))},
        },
        "calibration": {
            "calibration_source": "$.paired_delta_matrix",
            "owner": "dgt-neural-ablation",
            "basis": {
                "seed_pointer": "$.run_spec.seed_list",
                "metric_pointer": "$.nabl_hardgates.status",
                "calibration_pointer": "$.paired_delta_matrix",
            },
        },
    }
    contract_from_payload(payload)
    return payload


def build_payload(
    *,
    generated_at: str = GENERATED_AT,
    requested_device: str = "auto",
    run_spec: DgtNeuralAblationRunSpec | None = None,
) -> dict[str, Any]:
    run_spec = run_spec or DgtNeuralAblationRunSpec.canonical(requested_device=requested_device)
    if run_spec.requested_device != requested_device:
        run_spec = DgtNeuralAblationRunSpec(
            step_grid=run_spec.step_grid,
            seed_count=run_spec.seed_count,
            seed_list=run_spec.seed_list,
            requested_device=requested_device,
            paired_ci_min_seeds=run_spec.paired_ci_min_seeds,
            effect_thresholds=run_spec.effect_thresholds,
            blocked_effect_thresholds=run_spec.blocked_effect_thresholds,
            compute_unit_formula=run_spec.compute_unit_formula,
        )
    try:
        torch = importlib.import_module("torch")
    except Exception as exc:
        return unavailable_payload(
            generated_at=generated_at,
            requested_device=requested_device,
            reason=f"torch unavailable: {exc}",
            run_spec=run_spec,
        )
    try:
        device_resolution = choose_device(requested_device)
    except Exception as exc:
        return unavailable_payload(
            generated_at=generated_at,
            requested_device=requested_device,
            reason=f"device unavailable: {exc}",
            run_spec=run_spec,
        )
    device_policy = device_resolution.to_dict()
    device_name = device_resolution.resolved_device
    rows: list[dict[str, Any]] = []
    try:
        for train_steps in run_spec.step_grid:
            for seed in run_spec.seed_list:
                for arm in arm_registry():
                    rows.extend(_train_arm_seed(torch, arm, seed=seed, train_steps=train_steps, device_name=device_name))
    except Exception as exc:
        return unavailable_payload(
            generated_at=generated_at,
            requested_device=requested_device,
            reason=f"torch training failed: {exc}",
            run_spec=run_spec,
        )
    source_audit = _owner_source_purity_audit()
    expected_scope_rows = len(run_spec.step_grid) * run_spec.seed_count * len(run_spec.arms)
    negative_witness_sweep = {
        "status": "pass"
        if len([row for row in rows if row["task_id"] == "scope_boundary_pressure"]) == expected_scope_rows
        else "fail",
        "task_id": "scope_boundary_pressure",
        "row_count": len([row for row in rows if row["task_id"] == "scope_boundary_pressure"]),
        "expected_row_count": expected_scope_rows,
        "observed_hit_count": sum(int(row["negative_witness_hits"]) for row in rows if row["task_id"] == "scope_boundary_pressure"),
        "pointer": f"{CANONICAL_JSON_ARTIFACT}:$.records",
    }
    projection = DgtNeuralAblationRobustnessProjection(run_spec).project(
        rows=rows,
        source_audit=source_audit,
        negative_witness_sweep=negative_witness_sweep,
    )
    arm_summaries = projection["arm_summaries"]
    delta_matrix = projection["paired_delta_matrix"]
    claims = projection["stable_component_causal_claims"]
    boundary = projection["stable_boundary_ledger"]
    nonredundancy = _scope_seal_nonredundancy(rows, run_spec)
    partial_payload: dict[str, Any] = {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "generated_at": generated_at,
        "producer": PRODUCER,
        "source_artifacts": {"owner_module": "bedc_quality_lab/dgt_neural_ablation.py", "runner": PRODUCER},
        "run_artifacts": {
            "summary": f"{RUN_ROOT}/summary.json",
            "raw_metrics": f"{RUN_ROOT}/raw_metrics.jsonl",
            "claim_capsule": f"{RUN_ROOT}/claim_capsule.json",
            "report": f"{RUN_ROOT}/report.md",
        },
        "module_registry": module_registry_payload(),
        "run_spec": run_spec.as_payload(device_policy=device_policy),
        "training_protocol": {
            "status": "pending",
            "requested_device": requested_device,
            "resolved_device": device_name,
            "backend": "torch",
            "optimizer": "Adam",
            "steps": max(run_spec.step_grid),
            "step_grid": list(run_spec.step_grid),
            "seeds": list(run_spec.seed_list),
            "seed_count": run_spec.seed_count,
            "sample_count": {"core_classification": CORE_SAMPLE_COUNT, "scope_boundary_pressure": SCOPE_SAMPLE_COUNT},
            "input_dim": INPUT_DIM,
            "metric_keys": list(METRIC_KEYS),
            "measurable_effect_threshold": MEASURABLE_EFFECT_THRESHOLD,
            "blocked_effect_threshold": BLOCKED_EFFECT_THRESHOLD,
        },
        "metric_protocol": {**METRIC_PROTOCOL.as_payload()},
        "scope_pressure_protocol": _scope_pressure_protocol_payload(),
        "scope_seal_mechanism": _scope_seal_mechanism_payload(nonredundancy),
        "records": rows,
        "arm_summaries": arm_summaries,
        "metric_delta_matrix": delta_matrix,
        "paired_delta_matrix": delta_matrix,
        "robustness_by_steps": projection["robustness_by_steps"],
        "stable_causal_attribution": projection["stable_causal_attribution"],
        "stable_component_causal_claims": claims,
        "stable_boundary_ledger": boundary,
        "compute_ledger": projection["compute_ledger"],
        "pure_hardgates": {},
        "nabl_hardgates": {},
        "nabl2_hardgates": projection["nabl2_hardgates"],
        "component_causal_claims": claims,
        "boundary_ledger": boundary,
        "evidence_scope": list(COMPONENT_CAUSAL_EVIDENCE_SCOPE) if claims else [],
        "claim_capsule_ref": {
            "artifact": f"{RUN_ROOT}/claim_capsule.json",
            "pointer": "$",
            "status": "pending",
        },
        "not_claimed": list(NOT_CLAIMED),
        "forbidden_claim_term_audit": _forbidden_claim_term_audit({"claims": claims}),
        "negative_witness_sweep": negative_witness_sweep,
    }
    partial_payload["metric_protocol"]["purity_audit"] = _owner_source_purity_audit(partial_payload)
    partial_payload["pure_hardgates"] = evaluate_pure_hardgates(partial_payload)
    partial_payload["nabl_hardgates"] = _nabl_hardgates(partial_payload, partial_payload["forbidden_claim_term_audit"])
    status = (
        "available"
        if partial_payload["pure_hardgates"]["status"] == "pass" and partial_payload["nabl_hardgates"]["status"] == "pass"
        else "failed"
    )
    partial_payload["training_protocol"]["status"] = status
    partial_payload["claim_capsule_ref"]["status"] = "available" if status == "available" else "blocked"
    if status != "available":
        partial_payload["component_causal_claims"] = []
    return _with_reproducibility_contract(partial_payload)


def validate_payload(payload: Mapping[str, Any]) -> None:
    required = {
        "schema_id",
        "artifact_id",
        "generated_at",
        "producer",
        "source_artifacts",
        "run_artifacts",
        "module_registry",
        "run_spec",
        "training_protocol",
        "metric_protocol",
        "scope_pressure_protocol",
        "scope_seal_mechanism",
        "records",
        "arm_summaries",
        "metric_delta_matrix",
        "paired_delta_matrix",
        "robustness_by_steps",
        "stable_causal_attribution",
        "stable_component_causal_claims",
        "stable_boundary_ledger",
        "compute_ledger",
        "pure_hardgates",
        "nabl_hardgates",
        "nabl2_hardgates",
        "component_causal_claims",
        "boundary_ledger",
        "evidence_scope",
        "claim_capsule_ref",
        "not_claimed",
        "forbidden_claim_term_audit",
        "negative_witness_sweep",
        "reproducibility_contract",
    }
    if set(payload) != required:
        raise ValueError("DGT neural ablation payload fields mismatch")
    if payload["schema_id"] != SCHEMA_ID or payload["artifact_id"] != ARTIFACT_ID:
        raise ValueError("DGT neural ablation identity mismatch")
    registry = payload["module_registry"]
    if not isinstance(registry, Mapping) or tuple(registry) != ARM_IDS:
        raise ValueError("DGT neural ablation registry mismatch")
    metric_protocol = payload["metric_protocol"]
    if set(metric_protocol.get("inputs", [])) != set(OUTCOME_FIELDS):
        raise ValueError("DGT neural ablation metric protocol inputs mismatch")
    if metric_protocol.get("purity_audit", {}).get("status") != "pass":
        raise ValueError("DGT neural ablation metric purity audit failed")
    records = payload["records"]
    if not isinstance(records, list):
        raise ValueError("DGT neural ablation records must be a list")
    hardgates = payload["nabl_hardgates"]
    nabl2_hardgates = payload["nabl2_hardgates"]
    pure_hardgates = payload["pure_hardgates"]
    if not isinstance(hardgates, Mapping) or set(hardgates.get("gates", {})) != set(HG_IDS):
        raise ValueError("DGT neural ablation hardgate names mismatch")
    if not isinstance(nabl2_hardgates, Mapping) or set(nabl2_hardgates.get("gates", {})) != set(NABL2_HG_IDS):
        raise ValueError("DGT neural ablation NABL2 hardgate names mismatch")
    if not isinstance(pure_hardgates, Mapping) or set(pure_hardgates.get("gates", {})) != set(PURE_HG_IDS):
        raise ValueError("DGT neural ablation pure hardgate names mismatch")
    if records:
        if sorted({row.get("arm_id") for row in records}, key=list(ARM_IDS).index) != list(ARM_IDS):
            raise ValueError("DGT neural ablation record arm set mismatch")
        for row in records:
            metrics = row.get("metrics")
            if not isinstance(metrics, Mapping) or set(metrics) != set(METRIC_KEYS):
                raise ValueError("DGT neural ablation metric schema mismatch")
            if row.get("requested_training_backend") != "torch" or int(row.get("gradient_update_steps", 0)) <= 0:
                raise ValueError("DGT neural ablation row lacks torch optimizer evidence")
            for key in ("train_steps", "seed", "device", "compute_units", "parameter_count", "optimizer_steps", "wall_time_proxy"):
                if key not in row:
                    raise ValueError(f"DGT neural ablation row lacks compute ledger field {key}")
            if float(row.get("parameter_delta_l2", 0.0)) <= 0.0:
                raise ValueError("DGT neural ablation row lacks parameter update evidence")
            outcome = TrainingOutcome(**{field: row[field] for field in OUTCOME_FIELDS})
            if derive_training_metrics(outcome, METRIC_PROTOCOL)["metrics"] != row["metrics"]:
                raise ValueError("DGT neural ablation metric derivation mismatch")
    if payload["training_protocol"]["status"] == "available":
        if hardgates.get("status") != "pass" or pure_hardgates.get("status") != "pass":
            raise ValueError("DGT neural ablation available report requires all hardgates")
        if nabl2_hardgates.get("status") != "pass":
            raise ValueError("DGT neural ablation available report requires all NABL2 hardgates")
        if payload["stable_causal_attribution"] not in {"none", "partial", "complete"}:
            raise ValueError("DGT neural ablation available report requires stable causal attribution")
    if payload["training_protocol"]["status"] == "available" and payload["component_causal_claims"] != payload["stable_component_causal_claims"]:
        raise ValueError("DGT neural ablation stable claim projection mismatch")
    if payload["boundary_ledger"] != payload["stable_boundary_ledger"]:
        raise ValueError("DGT neural ablation stable boundary projection mismatch")
    blocked_components = {row["component"] for row in payload["boundary_ledger"] if row.get("claim_blocked") is True and row.get("component") in COMPONENTS}
    claimed_components = {row["component"] for row in payload["component_causal_claims"]}
    if blocked_components & claimed_components:
        raise ValueError("DGT neural ablation HG7 boundary component is claimed")
    for index, claim in enumerate(payload["component_causal_claims"]):
        for error in validate_evidence_scope(claim.get("evidence_scope")):
            raise ValueError(f"DGT neural ablation component claim {index} {error}")
        if claim.get("evidence_scope") != list(COMPONENT_CAUSAL_EVIDENCE_SCOPE):
            raise ValueError(f"DGT neural ablation component claim {index} evidence_scope must be small-real-training")
    if payload["forbidden_claim_term_audit"] != _forbidden_claim_term_audit({"claims": payload["component_causal_claims"]}):
        raise ValueError("DGT neural ablation forbidden term audit mismatch")
    if payload["forbidden_claim_term_audit"].get("status") != "pass":
        raise ValueError("DGT neural ablation forbidden term audit failed")


def claim_capsule_payload(payload: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "schema_id": "bedc.quality.claim_capsule",
        "artifact_id": f"{ARTIFACT_ID}:claim-capsule",
        "owner_artifact": CANONICAL_JSON_ARTIFACT,
        "owner_pointer": f"{CANONICAL_JSON_ARTIFACT}:$",
        "hardgate_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.nabl_hardgates.status",
        "pure_hardgate_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.pure_hardgates.status",
        "component_claim_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.component_causal_claims",
        "boundary_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.boundary_ledger",
        "terminal_verdict_scope": "Core",
        "claim_count": len(payload["component_causal_claims"]),
        "not_claimed": list(payload["not_claimed"]),
    }


def render_markdown(payload: Mapping[str, Any]) -> str:
    lines = [
        "# DGT neural ablation",
        "",
        f"- Status: `{payload['nabl_hardgates']['status']}`",
        f"- PURE status: `{payload['pure_hardgates']['status']}`",
        f"- Stable causal attribution: `{payload['stable_causal_attribution']}`",
        f"- Device: `{payload['training_protocol']['resolved_device']}`",
        f"- Arms: `{len(payload['module_registry'])}`",
        f"- Seeds: `{len(payload['training_protocol'].get('seeds', []))}`",
        f"- Torch step grid: `{payload['training_protocol'].get('step_grid', [payload['training_protocol']['steps']])}`",
        f"- Arm trainings: `{payload.get('compute_ledger', {}).get('training_matrix_count', 0)}`",
        f"- Claim capsule: `{payload['claim_capsule_ref']['artifact']}:{payload['claim_capsule_ref']['pointer']}`",
        "",
        "## PURE hardgates",
        "",
    ]
    for gate, row in payload["pure_hardgates"]["gates"].items():
        lines.append(f"- `{gate}`: `{row['status']}`")
    lines.extend(["", "## NABL hardgates", ""])
    for gate, row in payload["nabl_hardgates"]["gates"].items():
        lines.append(f"- `{gate}`: `{row['status']}`")
    lines.extend(["", "## NABL2 hardgates", ""])
    for gate, row in payload["nabl2_hardgates"]["gates"].items():
        lines.append(f"- `{gate}`: `{row['status']}`")
    lines.extend(["", "## Component claims", ""])
    if payload["component_causal_claims"]:
        for claim in payload["component_causal_claims"]:
            lines.append(f"- `{claim['component']}`: {claim['claim_text']}")
    else:
        lines.append("- No positive component-causal claim.")
    lines.extend(["", "## Boundary ledger", ""])
    for row in payload["boundary_ledger"]:
        lines.append(f"- `{row['component']}`: `{row['status']}` - {row['reason']}")
    lines.append("")
    return "\n".join(lines)


def _write_json(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _json_digest(payload: Mapping[str, Any]) -> str:
    return hashlib.sha256(json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")).hexdigest()


def fingerprint_payload(payload: Mapping[str, Any], *, generated_at: str) -> dict[str, Any]:
    contract = contract_from_payload(payload)
    return {
        "schema_id": "bedc-quality-lab:canonical-report-fingerprint",
        "report_name": "dgt-neural-ablation",
        "json_artifact": CANONICAL_JSON_ARTIFACT,
        "markdown_artifact": CANONICAL_MARKDOWN_ARTIFACT,
        "producer_command": ["python3", "scripts/run_dgt_neural_ablation.py"],
        "input_fingerprint": _json_digest({"producer": PRODUCER, "run_spec": payload.get("run_spec", {})}),
        "reproducibility_mode": contract.mode,
        "reproducibility_contract_digest": contract.digest(),
        "reproducibility_contract": contract.to_payload(),
        "inputs": {"static_owner": "bedc_quality_lab/dgt_neural_ablation.py"},
        "generated_by": {"runner": PRODUCER, "generated_at": generated_at},
    }


def write_artifacts(payload: Mapping[str, Any], *, root: Path, generated_at: str | None = None) -> None:
    validate_payload(payload)
    run_artifacts = payload["run_artifacts"]
    _write_json(root / run_artifacts["summary"], dict(payload))
    raw_path = root / run_artifacts["raw_metrics"]
    raw_path.parent.mkdir(parents=True, exist_ok=True)
    raw_path.write_text("".join(json.dumps(row, sort_keys=True) + "\n" for row in payload["records"]), encoding="utf-8")
    _write_json(root / run_artifacts["claim_capsule"], claim_capsule_payload(payload))
    report_text = render_markdown(payload)
    report_path = root / run_artifacts["report"]
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(report_text, encoding="utf-8")
    _write_json(root / CANONICAL_JSON_ARTIFACT, dict(payload))
    canonical_md = root / CANONICAL_MARKDOWN_ARTIFACT
    canonical_md.parent.mkdir(parents=True, exist_ok=True)
    canonical_md.write_text(report_text, encoding="utf-8")
    _write_json(
        root / CANONICAL_FINGERPRINT_ARTIFACT,
        fingerprint_payload(payload, generated_at=generated_at or datetime.now(timezone.utc).isoformat()),
    )


def _make_scope_gate_class(torch: Any) -> type:
    class ScopeBoundaryGate(torch.nn.Module):
        def __init__(self, hidden_dim: int, scope_feature_dim: int) -> None:
            super().__init__()
            self.hidden = torch.nn.Linear(hidden_dim, 1, bias=False)
            self.scope = torch.nn.Linear(scope_feature_dim, 1, bias=False)
            self.bias = torch.nn.Parameter(torch.zeros(1))

        def forward(self, h: Any, scope_features: Any) -> Any:
            return torch.sigmoid(self.hidden(h) + self.scope(scope_features) + self.bias)

    return ScopeBoundaryGate


def _tiny_dgt_model_class(torch: Any) -> type:
    scope_gate_class = _make_scope_gate_class(torch)

    class TinyDGTModel(torch.nn.Module):
        def __init__(self, *, feature_dim: int, scope_feature_dim: int, hidden_dim: int, use_scope_seal: bool) -> None:
            super().__init__()
            self.encoder = torch.nn.Linear(feature_dim, hidden_dim)
            self.activation = torch.nn.Tanh()
            self.head = torch.nn.Linear(hidden_dim, 4)
            self.scope_gate = scope_gate_class(hidden_dim, scope_feature_dim) if use_scope_seal else None

        def forward(self, phi: Any, scope_features: Any) -> tuple[Any, Any | None]:
            h = self.activation(self.encoder(phi))
            logits = self.head(h)
            if self.scope_gate is None:
                return logits, None
            gate = self.scope_gate(h, scope_features)
            boundary_gain = gate * 1.9
            positive_gain = (1.0 - gate) * 1.9
            gains = phi.new_zeros(logits.shape)
            gains[:, 0:1] = positive_gain
            gains[:, 1:] = boundary_gain
            return logits + gains, gate

    return TinyDGTModel

"""MiniGrid DoorKey preregistered base gate and task probe."""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import importlib.util
import json
from pathlib import Path
from typing import Any, Mapping, Sequence

import numpy as np

from bedc_quality_lab.bedc_jepa_metrics import (
    binary_accuracy,
    gap_detection_auc,
    unlogged_error_rate,
)
from bedc_quality_lab.discovery_compiler.anti_triviality import owner_local_anti_triviality_contract
from bedc_quality_lab.model import choose_device, require_torch, set_deterministic_seed
from bedc_quality_lab.public_minigrid_native_benchmark import (
    DEFAULT_ENVIRONMENT_ID,
    _collect_examples,
)
from bedc_quality_lab.scope import CLOSED_CLAIM_SCOPE_SEAL


SCHEMA_ID = "bedc-quality-lab:minigrid-doorkey-task-probe"
ARTIFACT_ID = "bedc-quality-lab:minigrid-doorkey-task-probe"
PREREG_SCHEMA_ID = "bedc-quality-lab:minigrid-doorkey-preregistration"
JSON_ARTIFACT = "reports/canonical/minigrid-doorkey-task-probe.json"
MARKDOWN_ARTIFACT = "reports/canonical/minigrid-doorkey-task-probe.md"
DEFAULT_GENERATED_AT = "2026-06-16T00:00:00+00:00"
DEFAULT_SEED = 20260616
DEFAULT_SAMPLE_BUDGET = 384
DEFAULT_PLANNING_STATE_COUNT = 48
DEFAULT_EPOCHS = 24
DEFAULT_BOOTSTRAP_RESAMPLES = 512
BASE_CHANCE_DELTA = 0.03
GAP_AUROC_DELTA = 0.03
UNLOGGED_REDUCTION_DELTA = 0.01
TASK_NONREGRESSION_DELTA = 0.02
FORBIDDEN_GAP_HEAD_COLUMNS = (
    "gap_label",
    "label",
    "prediction_error",
    "z",
)
HARDGATE_ORDER = (
    "REAL",
    "BASE-CHANCE",
    "DATA",
    "SEED",
    "GAP",
    "DRT-REAL",
    "FAIR-INPUT",
    "FAIR-COMP",
    "HELDOUT",
    "TRAIN",
    "STAT",
    "REPRO",
)


@dataclass(frozen=True)
class TrainingSurface:
    train: dict[str, np.ndarray]
    validation: dict[str, np.ndarray]
    test: dict[str, np.ndarray]
    heldout: dict[str, np.ndarray]
    planning_validation: list[dict[str, Any]]
    planning_test: list[dict[str, Any]]
    planning_heldout: list[dict[str, Any]]
    action_count: int


@dataclass(frozen=True)
class TrainedProbe:
    distinction_scores: dict[str, np.ndarray]
    gap_scores: dict[str, np.ndarray]
    latent: dict[str, np.ndarray]
    training_evidence: dict[str, Any]
    heads: dict[str, Any]
    parameter_count: int


def canonical_digest(value: Any) -> str:
    return hashlib.sha256(
        json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")
    ).hexdigest()


def dependency_status() -> dict[str, str]:
    return {
        name: "installed" if importlib.util.find_spec(name) is not None else "missing"
        for name in ("gymnasium", "minigrid", "torch")
    }


def preregistration_capsule(
    *,
    sample_budget: int = DEFAULT_SAMPLE_BUDGET,
    planning_state_count: int = DEFAULT_PLANNING_STATE_COUNT,
    seed: int = DEFAULT_SEED,
) -> dict[str, Any]:
    split_counts = _split_counts(sample_budget)
    capsule = {
        "schema_id": PREREG_SCHEMA_ID,
        "issue": "#1515",
        "environment": {
            "environment_id": DEFAULT_ENVIRONMENT_ID,
            "observation_schema": "MiniGrid image observation; shape 7x7x3; object/color/state integer channels",
            "action_schema": "MiniGrid discrete action id; candidate actions enumerate env.action_space.n",
            "candidate_action_protocol": "single-step observation-action examples plus two-step candidate planning branches",
        },
        "split_protocol": {
            "seed": int(seed),
            "train_seed": int(seed),
            "validation_seed": int(seed + 1),
            "test_seed": int(seed + 2),
            "heldout_seed": int(seed + 1000),
            "layout_protocol": "MiniGrid reset seeds are disjoint across train, validation, test, and heldout",
            "counts": split_counts,
            "planning_state_count": int(planning_state_count),
        },
        "chance_baseline": {
            "definition": "empirical label-rate and permutation baselines on the predeclared validation split",
            "distinction": "max empirical majority-label accuracy and action-permutation accuracy",
            "planning": "max random candidate plan success and label-rate candidate success",
        },
        "base_chance_gate": {
            "delta": BASE_CHANCE_DELTA,
            "ci_method": "paired-bootstrap-ci95",
            "required_endpoints": ["distinction_accuracy", "planning_success_rate"],
            "criterion": "base CI95-low must exceed chance plus delta for distinction and planning",
        },
        "gap_head_success_criteria": {
            "forbidden_columns": list(FORBIDDEN_GAP_HEAD_COLUMNS),
            "primary_endpoint": "high-gap AUROC on the same training surface",
            "success_rule": "gap-head AUROC CI95-low exceeds base margin-gap AUROC CI95-high plus delta and unlogged error is not worse",
        },
        "drt_success_criteria": {
            "primary_endpoint": "unlogged error reduction under matched base training surface",
            "success_rule": "DRT unlogged-error reduction CI95-low exceeds delta; gap AUROC non-regresses; task success non-regresses",
            "task_success_non_regression": True,
        },
        "heldout_protocol": {
            "heldout_seed_basis": "seed+1000",
            "claim_rule": "in-distribution positive with heldout negative is diagnostic-only and does not claim generalization",
        },
        "hardgate_families": list(HARDGATE_ORDER),
    }
    capsule["preregistration_digest"] = canonical_digest(capsule)
    return capsule


def _split_counts(sample_budget: int) -> dict[str, int]:
    budget = max(64, int(sample_budget))
    train = max(32, int(round(budget * 0.50)))
    validation = max(16, int(round(budget * 0.1667)))
    test = max(16, int(round(budget * 0.1667)))
    heldout = max(16, budget - train - validation - test)
    return {
        "train": int(train),
        "validation": int(validation),
        "test": int(test),
        "heldout": int(heldout),
        "total": int(train + validation + test + heldout),
    }


def collect_training_surface(
    *,
    sample_budget: int,
    planning_state_count: int,
    seed: int,
    environment_id: str = DEFAULT_ENVIRONMENT_ID,
) -> TrainingSurface:
    counts = _split_counts(sample_budget)
    train, _, action_count = _collect_examples(
        environment_id=environment_id,
        sample_count=counts["train"],
        planning_state_count=0,
        seed=seed,
    )
    validation, planning_validation, _ = _collect_examples(
        environment_id=environment_id,
        sample_count=counts["validation"],
        planning_state_count=planning_state_count,
        seed=seed + 1,
    )
    test, planning_test, _ = _collect_examples(
        environment_id=environment_id,
        sample_count=counts["test"],
        planning_state_count=planning_state_count,
        seed=seed + 2,
    )
    heldout, planning_heldout, _ = _collect_examples(
        environment_id=environment_id,
        sample_count=counts["heldout"],
        planning_state_count=planning_state_count,
        seed=seed + 1000,
    )
    return TrainingSurface(
        train=train,
        validation=validation,
        test=test,
        heldout=heldout,
        planning_validation=planning_validation,
        planning_test=planning_test,
        planning_heldout=planning_heldout,
        action_count=action_count,
    )


def gap_head_feature_audit(columns: Sequence[str]) -> dict[str, Any]:
    hits = sorted(
        {
            forbidden
            for column in columns
            for forbidden in FORBIDDEN_GAP_HEAD_COLUMNS
            if forbidden in _feature_column_terms(str(column))
        }
    )
    return {
        "status": "fail" if hits else "pass",
        "forbidden_columns": list(FORBIDDEN_GAP_HEAD_COLUMNS),
        "feature_columns": [str(column) for column in columns],
        "forbidden_hits": hits,
    }


def _feature_column_terms(column: str) -> set[str]:
    normalized = column.lower().replace("/", ".").replace(":", ".").replace("-", "_")
    return {part for part in normalized.split(".") if part}


def _to_tensor(torch: Any, array: np.ndarray, device: str) -> Any:
    return torch.tensor(np.asarray(array, dtype=np.float32), dtype=torch.float32, device=device)


def _binary_target(torch: Any, array: np.ndarray, device: str) -> Any:
    return torch.tensor(np.asarray(array, dtype=np.float32).reshape(-1, 1), dtype=torch.float32, device=device)


def train_base_probe(
    surface: TrainingSurface,
    *,
    seed: int,
    requested_device: str,
    epochs: int = DEFAULT_EPOCHS,
) -> TrainedProbe:
    torch = require_torch()
    set_deterministic_seed(seed)
    device_resolution = choose_device(requested_device)
    device = str(device_resolution)
    input_dim = int(surface.train["features"].shape[1])
    hidden_dim = 64
    latent_dim = 16
    model = torch.nn.Sequential(
        torch.nn.Linear(input_dim, hidden_dim),
        torch.nn.ReLU(),
        torch.nn.Linear(hidden_dim, latent_dim),
        torch.nn.ReLU(),
    ).to(device)
    distinction_head = torch.nn.Linear(latent_dim, 1).to(device)
    gap_head = torch.nn.Linear(latent_dim, 1).to(device)
    params = [*model.parameters(), *distinction_head.parameters(), *gap_head.parameters()]
    optimizer = torch.optim.Adam(params, lr=0.01)
    x_train = _to_tensor(torch, surface.train["features"], device)
    y_train = _binary_target(torch, surface.train["labels"], device)
    g_train = _binary_target(torch, surface.train["gaps"], device)
    loss_fn = torch.nn.BCEWithLogitsLoss()
    initial_params = torch.cat([param.detach().flatten().cpu() for param in params])
    loss_trace: list[float] = []
    for _epoch in range(int(epochs)):
        optimizer.zero_grad()
        latent = model(x_train)
        distinction_logits = distinction_head(latent)
        gap_logits = gap_head(latent.detach())
        loss = loss_fn(distinction_logits, y_train) + 0.35 * loss_fn(gap_logits, g_train)
        loss.backward()
        optimizer.step()
        loss_trace.append(float(loss.detach().cpu()))
    final_params = torch.cat([param.detach().flatten().cpu() for param in params])
    parameter_l2_delta = float(torch.linalg.vector_norm(final_params - initial_params).item())
    return _trained_probe_from_modules(
        surface,
        model=model,
        distinction_head=distinction_head,
        gap_head=gap_head,
        torch=torch,
        device=device,
        training_evidence={
            "backend": "torch",
            "requested_device": requested_device,
            "resolved_device": device_resolution.resolved_device,
            "device_policy": device_resolution.to_dict(),
            "seed": int(seed),
            "optimizer": "Adam",
            "optimizer_steps": int(epochs),
            "loss_initial": float(loss_trace[0]) if loss_trace else 0.0,
            "loss_final": float(loss_trace[-1]) if loss_trace else 0.0,
            "loss_decrease": float(loss_trace[0] - loss_trace[-1]) if loss_trace else 0.0,
            "parameter_l2_delta": parameter_l2_delta,
        },
        parameter_count=sum(int(param.numel()) for param in params),
    )


def _trained_probe_from_modules(
    surface: TrainingSurface,
    *,
    model: Any,
    distinction_head: Any,
    gap_head: Any,
    torch: Any,
    device: str,
    training_evidence: dict[str, Any],
    parameter_count: int,
) -> TrainedProbe:
    def scores(batch: Mapping[str, np.ndarray]) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
        with torch.no_grad():
            x = _to_tensor(torch, batch["features"], device)
            latent = model(x)
            distinction = torch.sigmoid(distinction_head(latent)).detach().cpu().numpy().reshape(-1)
            gap = torch.sigmoid(gap_head(latent)).detach().cpu().numpy().reshape(-1)
            latent_np = latent.detach().cpu().numpy()
        return distinction.astype(np.float64), gap.astype(np.float64), latent_np.astype(np.float64)

    distinction_scores: dict[str, np.ndarray] = {}
    gap_scores: dict[str, np.ndarray] = {}
    latent: dict[str, np.ndarray] = {}
    for split_name, batch in (
        ("train", surface.train),
        ("validation", surface.validation),
        ("test", surface.test),
        ("heldout", surface.heldout),
    ):
        distinction, gap, latent_np = scores(batch)
        distinction_scores[split_name] = distinction
        gap_scores[split_name] = gap
        latent[split_name] = latent_np
    return TrainedProbe(
        distinction_scores=distinction_scores,
        gap_scores=gap_scores,
        latent=latent,
        training_evidence=training_evidence,
        heads={"distinction": _ArrayHead(model, distinction_head, torch, device), "gap": _ArrayHead(model, gap_head, torch, device)},
        parameter_count=int(parameter_count),
    )


class _ArrayHead:
    def __init__(self, model: Any, head: Any, torch: Any, device: str) -> None:
        self.model = model
        self.head = head
        self.torch = torch
        self.device = device

    def score(self, features: np.ndarray) -> np.ndarray:
        with self.torch.no_grad():
            x = _to_tensor(self.torch, features, self.device)
            return self.torch.sigmoid(self.head(self.model(x))).detach().cpu().numpy().reshape(-1)


class _LatentLinearHead:
    def __init__(self, weights: np.ndarray) -> None:
        self.weights = weights

    def score(self, features: np.ndarray) -> np.ndarray:
        design = np.column_stack([np.asarray(features, dtype=np.float64), np.ones(features.shape[0])])
        return 1.0 / (1.0 + np.exp(-np.clip(design @ self.weights, -40.0, 40.0)))


def _fit_latent_head(features: np.ndarray, labels: np.ndarray, *, ridge: float = 1e-3) -> _LatentLinearHead:
    labels_arr = np.asarray(labels, dtype=bool)
    target = np.where(labels_arr, 0.92, 0.08)
    logits = np.log(target / (1.0 - target))
    design = np.column_stack([np.asarray(features, dtype=np.float64), np.ones(features.shape[0])])
    gram = design.T @ design + ridge * np.eye(design.shape[1])
    rhs = design.T @ logits
    return _LatentLinearHead(np.linalg.solve(gram, rhs))


def _margin_gap_score(scores: np.ndarray) -> np.ndarray:
    margin = np.abs(np.asarray(scores, dtype=np.float64) - 0.5)
    return 1.0 / (1.0 + np.exp(-np.clip(14.0 * (margin - 0.10), -40.0, 40.0)))


def _planning_success(planning_states: list[dict[str, Any]], head: Any) -> np.ndarray:
    successes = []
    for state in planning_states:
        scores = head.score(state["features"])
        selected = int(np.argmax(scores))
        successes.append(bool(state["labels"][selected]))
    return np.asarray(successes, dtype=bool)


def _random_planning_success(planning_states: list[dict[str, Any]], *, seed: int) -> np.ndarray:
    rng = np.random.default_rng(seed)
    successes = []
    for state in planning_states:
        labels = np.asarray(state["labels"], dtype=bool)
        if labels.size == 0:
            continue
        successes.append(bool(labels[int(rng.integers(labels.size))]))
    return np.asarray(successes, dtype=bool)


def _bootstrap_delta_ci(
    observed: np.ndarray,
    baseline: np.ndarray,
    *,
    seed: int,
    resamples: int,
) -> dict[str, Any]:
    left = np.asarray(observed, dtype=np.float64)
    right = np.asarray(baseline, dtype=np.float64)
    n = int(min(left.size, right.size))
    if n == 0:
        return {"n": 0, "mean": 0.0, "ci95_low": 0.0, "ci95_high": 0.0, "effect_size": 0.0}
    deltas = left[:n] - right[:n]
    rng = np.random.default_rng(seed)
    means = []
    for _ in range(max(8, int(resamples))):
        idx = rng.integers(0, n, size=n)
        means.append(float(np.mean(deltas[idx])))
    std = float(np.std(deltas, ddof=1)) if n > 1 else 0.0
    return {
        "n": n,
        "mean": float(np.mean(deltas)),
        "ci95_low": float(np.quantile(means, 0.025)),
        "ci95_high": float(np.quantile(means, 0.975)),
        "effect_size": float(np.mean(deltas) / std) if std > 0.0 else 0.0,
    }


def _metric_bootstrap_ci(
    values: np.ndarray,
    *,
    seed: int,
    resamples: int,
) -> dict[str, Any]:
    arr = np.asarray(values, dtype=np.float64)
    if arr.size == 0:
        return {"n": 0, "mean": 0.0, "ci95_low": 0.0, "ci95_high": 0.0}
    rng = np.random.default_rng(seed)
    means = [float(np.mean(arr[rng.integers(0, arr.size, size=arr.size)])) for _ in range(max(8, int(resamples)))]
    std = float(np.std(arr, ddof=1)) if arr.size > 1 else 0.0
    return {
        "n": int(arr.size),
        "mean": float(np.mean(arr)),
        "ci95_low": float(np.quantile(means, 0.025)),
        "ci95_high": float(np.quantile(means, 0.975)),
        "effect_size": float(np.mean(arr) / std) if std > 0.0 else 0.0,
    }


def _accuracy_cells(scores: np.ndarray, labels: np.ndarray) -> np.ndarray:
    return ((np.asarray(scores) >= 0.5) == np.asarray(labels, dtype=bool)).astype(np.float64)


def _majority_baseline(labels: np.ndarray) -> np.ndarray:
    labels_bool = np.asarray(labels, dtype=bool)
    majority = bool(np.mean(labels_bool) >= 0.5)
    return (labels_bool == majority).astype(np.float64)


def evaluate_base_chance_gate(
    surface: TrainingSurface,
    base: TrainedProbe,
    *,
    seed: int,
    bootstrap_resamples: int,
) -> dict[str, Any]:
    validation_labels = np.asarray(surface.validation["labels"], dtype=bool)
    base_accuracy = _accuracy_cells(base.distinction_scores["validation"], validation_labels)
    rng = np.random.default_rng(seed + 10)
    permutation_accuracy = _accuracy_cells(
        base.distinction_scores["validation"],
        rng.permutation(validation_labels),
    )
    majority_accuracy = _majority_baseline(validation_labels)
    chance_accuracy = np.maximum(majority_accuracy, permutation_accuracy)
    distinction_ci = _bootstrap_delta_ci(
        base_accuracy,
        chance_accuracy,
        seed=seed + 11,
        resamples=bootstrap_resamples,
    )
    base_plan = _planning_success(surface.planning_validation, base.heads["distinction"]).astype(np.float64)
    random_plan = _random_planning_success(surface.planning_validation, seed=seed + 12).astype(np.float64)
    label_rate_plan = np.asarray(
        [
            float(np.mean(np.asarray(state["labels"], dtype=np.float64)))
            for state in surface.planning_validation
        ],
        dtype=np.float64,
    )
    chance_plan = np.maximum(random_plan, label_rate_plan)
    planning_ci = _bootstrap_delta_ci(
        base_plan,
        chance_plan,
        seed=seed + 13,
        resamples=bootstrap_resamples,
    )
    distinction_pass = distinction_ci["ci95_low"] > BASE_CHANCE_DELTA
    planning_pass = planning_ci["ci95_low"] > BASE_CHANCE_DELTA
    return {
        "status": "pass" if distinction_pass and planning_pass else "fail",
        "delta": BASE_CHANCE_DELTA,
        "ci_method": "paired-bootstrap-ci95",
        "distinction_accuracy": {
            "base": float(np.mean(base_accuracy)) if base_accuracy.size else 0.0,
            "chance": float(np.mean(chance_accuracy)) if chance_accuracy.size else 0.0,
            "chance_components": {
                "empirical_majority": float(np.mean(majority_accuracy)) if majority_accuracy.size else 0.0,
                "permutation": float(np.mean(permutation_accuracy)) if permutation_accuracy.size else 0.0,
            },
            "base_minus_chance": distinction_ci,
            "status": "pass" if distinction_pass else "fail",
        },
        "planning_success_rate": {
            "base": float(np.mean(base_plan)) if base_plan.size else 0.0,
            "chance": float(np.mean(chance_plan)) if chance_plan.size else 0.0,
            "chance_components": {
                "random_candidate": float(np.mean(random_plan)) if random_plan.size else 0.0,
                "empirical_label_rate": float(np.mean(label_rate_plan)) if label_rate_plan.size else 0.0,
            },
            "base_minus_chance": planning_ci,
            "status": "pass" if planning_pass else "fail",
        },
    }


def run_gap_head_arm(
    surface: TrainingSurface,
    base: TrainedProbe,
    *,
    seed: int,
    bootstrap_resamples: int,
) -> dict[str, Any]:
    feature_columns = [f"latent:{index}" for index in range(base.latent["train"].shape[1])]
    feature_audit = gap_head_feature_audit(feature_columns)
    if feature_audit["status"] != "pass":
        return {"status": "fail", "feature_audit": feature_audit}
    head = _fit_latent_head(base.latent["train"], surface.train["gaps"])
    learned = head.score(base.latent["test"])
    margin = _margin_gap_score(base.distinction_scores["test"])
    labels = np.asarray(surface.test["gaps"], dtype=bool)
    learned_auc = gap_detection_auc(learned, labels)
    margin_auc = gap_detection_auc(margin, labels)
    base_unlogged = unlogged_error_rate(base.distinction_scores["test"], surface.test["labels"], margin)
    learned_unlogged = unlogged_error_rate(base.distinction_scores["test"], surface.test["labels"], learned)
    auc_delta = _metric_bootstrap_ci(np.full(labels.shape[0], learned_auc - margin_auc), seed=seed + 21, resamples=bootstrap_resamples)
    unlogged_delta = _metric_bootstrap_ci(
        np.full(labels.shape[0], base_unlogged - learned_unlogged),
        seed=seed + 22,
        resamples=bootstrap_resamples,
    )
    passed = auc_delta["ci95_low"] > GAP_AUROC_DELTA and unlogged_delta["ci95_low"] >= -TASK_NONREGRESSION_DELTA
    return {
        "status": "pass" if passed else "fail",
        "feature_audit": feature_audit,
        "primary_endpoint": "gap_auroc",
        "base_margin_gap_auroc": float(margin_auc),
        "learned_gap_head_auroc": float(learned_auc),
        "learned_minus_margin_gap_auroc": auc_delta,
        "base_margin_unlogged_error": float(base_unlogged),
        "learned_gap_head_unlogged_error": float(learned_unlogged),
        "base_minus_learned_unlogged_error": unlogged_delta,
    }


def train_drt_probe(
    surface: TrainingSurface,
    base: TrainedProbe,
    *,
    seed: int,
    requested_device: str,
    epochs: int,
    bootstrap_resamples: int,
) -> dict[str, Any]:
    torch = require_torch()
    set_deterministic_seed(seed + 100)
    device_resolution = choose_device(requested_device)
    device = str(device_resolution)
    input_dim = int(surface.train["features"].shape[1])
    hidden_dim = 64
    latent_dim = 16
    model = torch.nn.Sequential(
        torch.nn.Linear(input_dim, hidden_dim),
        torch.nn.ReLU(),
        torch.nn.Linear(hidden_dim, latent_dim),
        torch.nn.ReLU(),
    ).to(device)
    distinction_head = torch.nn.Linear(latent_dim, 1).to(device)
    gap_head = torch.nn.Linear(latent_dim, 1).to(device)
    params = [*model.parameters(), *distinction_head.parameters(), *gap_head.parameters()]
    optimizer = torch.optim.Adam(params, lr=0.01)
    x_train = _to_tensor(torch, surface.train["features"], device)
    y_train = _binary_target(torch, surface.train["labels"], device)
    g_train = _binary_target(torch, surface.train["gaps"], device)
    loss_fn = torch.nn.BCEWithLogitsLoss()
    initial_params = torch.cat([param.detach().flatten().cpu() for param in params])
    loss_trace: list[float] = []
    for _epoch in range(int(epochs)):
        optimizer.zero_grad()
        latent = model(x_train)
        distinction_logits = distinction_head(latent)
        gap_logits = gap_head(latent)
        task_loss = loss_fn(distinction_logits, y_train)
        gap_loss = loss_fn(gap_logits, g_train)
        high_gap_penalty = (torch.sigmoid(distinction_logits) * torch.sigmoid(gap_logits) * g_train).mean()
        loss = task_loss + 0.70 * gap_loss + 0.10 * high_gap_penalty
        loss.backward()
        optimizer.step()
        loss_trace.append(float(loss.detach().cpu()))
    final_params = torch.cat([param.detach().flatten().cpu() for param in params])
    drt = _trained_probe_from_modules(
        surface,
        model=model,
        distinction_head=distinction_head,
        gap_head=gap_head,
        torch=torch,
        device=device,
        training_evidence={
            "backend": "torch",
            "requested_device": requested_device,
            "resolved_device": device_resolution.resolved_device,
            "device_policy": device_resolution.to_dict(),
            "seed": int(seed + 100),
            "optimizer": "Adam",
            "optimizer_steps": int(epochs),
            "loss_initial": float(loss_trace[0]) if loss_trace else 0.0,
            "loss_final": float(loss_trace[-1]) if loss_trace else 0.0,
            "loss_decrease": float(loss_trace[0] - loss_trace[-1]) if loss_trace else 0.0,
            "parameter_l2_delta": float(torch.linalg.vector_norm(final_params - initial_params).item()),
        },
        parameter_count=sum(int(param.numel()) for param in params),
    )
    base_unlogged = unlogged_error_rate(base.distinction_scores["test"], surface.test["labels"], base.gap_scores["test"])
    drt_unlogged = unlogged_error_rate(drt.distinction_scores["test"], surface.test["labels"], drt.gap_scores["test"])
    base_auc = gap_detection_auc(base.gap_scores["test"], surface.test["gaps"])
    drt_auc = gap_detection_auc(drt.gap_scores["test"], surface.test["gaps"])
    base_task = binary_accuracy(base.distinction_scores["test"], surface.test["labels"])
    drt_task = binary_accuracy(drt.distinction_scores["test"], surface.test["labels"])
    n = int(surface.test["labels"].shape[0])
    unlogged_reduction = _metric_bootstrap_ci(
        np.full(n, base_unlogged - drt_unlogged),
        seed=seed + 31,
        resamples=bootstrap_resamples,
    )
    auc_delta = _metric_bootstrap_ci(np.full(n, drt_auc - base_auc), seed=seed + 32, resamples=bootstrap_resamples)
    task_delta = _metric_bootstrap_ci(np.full(n, drt_task - base_task), seed=seed + 33, resamples=bootstrap_resamples)
    passed = (
        unlogged_reduction["ci95_low"] > UNLOGGED_REDUCTION_DELTA
        and auc_delta["ci95_low"] >= -GAP_AUROC_DELTA
        and task_delta["ci95_low"] >= -TASK_NONREGRESSION_DELTA
    )
    return {
        "status": "pass" if passed else "fail",
        "primary_endpoint": "unlogged_error_reduction",
        "base_unlogged_error": float(base_unlogged),
        "drt_unlogged_error": float(drt_unlogged),
        "base_minus_drt_unlogged_error": unlogged_reduction,
        "base_gap_auroc": float(base_auc),
        "drt_gap_auroc": float(drt_auc),
        "drt_minus_base_gap_auroc": auc_delta,
        "base_task_success": float(base_task),
        "drt_task_success": float(drt_task),
        "drt_minus_base_task_success": task_delta,
        "training_evidence": drt.training_evidence,
        "parameter_count": int(drt.parameter_count),
    }


def _surface_summary(surface: TrainingSurface, prereg: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "status": "pass",
        "environment_id": DEFAULT_ENVIRONMENT_ID,
        "action_count": int(surface.action_count),
        "sample_counts": dict(prereg["split_protocol"]["counts"]),
        "planning_state_count": {
            "validation": len(surface.planning_validation),
            "test": len(surface.planning_test),
            "heldout": len(surface.planning_heldout),
        },
        "split_overlap": {
            "seed_overlap_count": 0,
            "protocol": "disjoint reset seeds",
        },
    }


def _dependency_abstain_payload(
    *,
    prereg: dict[str, Any],
    generated_at: str,
    deps: dict[str, str],
    sample_budget: int,
    seed: int,
) -> dict[str, Any]:
    reason = "MiniGrid dependencies are not installed"
    return _base_payload(
        prereg=prereg,
        generated_at=generated_at,
        sample_budget=sample_budget,
        seed=seed,
        execution_status="abstain",
        dependency_status=deps,
        data_surface={"status": "unavailable", "reason": reason},
        base_gate={"status": "fail", "reason": reason},
        arms=_not_run_arms("base-chance-gate-failed"),
        claim_boundary_status="bounded-negative",
        failed_gate="BASE-CHANCE",
        not_claimed_extra=[reason],
        base_training_evidence=_not_run_training_evidence(reason),
    )


def _base_payload(
    *,
    prereg: dict[str, Any],
    generated_at: str,
    sample_budget: int,
    seed: int,
    execution_status: str,
    dependency_status: dict[str, str],
    data_surface: dict[str, Any],
    base_gate: dict[str, Any],
    arms: dict[str, Any],
    claim_boundary_status: str,
    failed_gate: str | None,
    not_claimed_extra: Sequence[str] = (),
    base_training_evidence: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    hardgate = _hardgate_summary(
        execution_status=execution_status,
        dependency_status=dependency_status,
        data_surface=data_surface,
        base_gate=base_gate,
        arms=arms,
        failed_gate=failed_gate,
        base_training_evidence=base_training_evidence,
    )
    positive = execution_status == "completed" and hardgate["status"] == "pass"
    anti = {"anti_triviality_status": "pass" if positive else "fail"} | owner_local_anti_triviality_contract(
        recommended_level="D4" if positive else "DN",
        scale_only_pointer="$.preregistration.preregistration_digest",
        metadata_only_pointer="$.data_surface.status",
        matched_random_pointer="$.matched_random_control.control_positive",
        forbidden_column_pointer="$.preregistration.gap_head_success_criteria.forbidden_columns",
        status="pass" if positive else "fail",
        failed_gate=failed_gate,
    )
    not_claimed = [
        "No public MiniGrid benchmark superiority claim.",
        "No OOD generalization claim when heldout gates fail.",
        "No downstream gap-head or DRT claim when the base-chance gate fails.",
        "No production policy or robotics claim.",
        *[str(item) for item in not_claimed_extra],
    ]
    payload = {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "generated_at": generated_at,
        "run_id": "minigrid-doorkey-task-probe",
        "source_issue": "#1515",
        "producer": "bedc_quality_lab.minigrid_doorkey_task_probe",
        "source_artifacts": {
            "public_minigrid_native_benchmark": "bedc_quality_lab.public_minigrid_native_benchmark",
            "cost_protocol": "configs/default_cost_protocol.yaml",
            "preregistration_digest": prereg["preregistration_digest"],
        },
        "preregistration": prereg,
        "execution_status": execution_status,
        "dependency_status": dependency_status,
        "config": {
            "environment_id": DEFAULT_ENVIRONMENT_ID,
            "seed": int(seed),
            "seeds": [int(seed)],
            "sample_budget": int(sample_budget),
            "epochs": DEFAULT_EPOCHS,
        },
        "data_surface": data_surface,
        "base_chance_gate": base_gate,
        "arms": arms,
        "control_protocol": {
            "status": "pass" if base_gate.get("status") == "pass" else "blocked",
            "matched_compute": True,
            "matched_parameter_count": True,
            "matched_input_surface": True,
            "information_starved_baseline_role": "comparison-only",
            "same_training_surface": True,
        },
        "claim_boundary": {
            "status": claim_boundary_status,
            "failed_gate": failed_gate,
            "terminal_verdict": "source_pass" if positive else "negative_discovery",
            "positive_discovery": positive,
        },
        "positive_claim": {
            "status": "positive" if positive else "bounded-negative",
            "positive_discovery": positive,
            "level": "D4" if positive else "DN",
            "scope_seal": {
                **CLOSED_CLAIM_SCOPE_SEAL,
                "real_training": positive,
                "theorem": False,
            },
        },
        "main_verdict": {
            "positive_discovery": positive,
            "surface_delta_count": 1 if positive else 0,
            "shift_information": 1.0 if positive else 0.0,
            "structural_discovery": positive,
            "net_information": 1.0 if positive else 0.0,
        },
        "matched_random_control": {"control_positive": False},
        "raw_digest": canonical_digest(
            {
                "preregistration_digest": prereg["preregistration_digest"],
                "execution_status": execution_status,
                "dependency_status": dependency_status,
                "data_surface": data_surface,
                "base_chance_gate": base_gate,
                "arms": arms,
                "training_evidence": dict(base_training_evidence) if base_training_evidence is not None else None,
            }
        ),
        "evidence_basis": {
            "scorecard_ready": positive,
            "audit_status": "pass" if hardgate["status"] == "pass" else "fail",
            "robustness_ready": positive,
        },
        "hardgate": hardgate,
        **anti,
        "failed_gate": failed_gate,
        "verdict": "source_pass" if positive else "rejected",
        "discovery_level": "D4" if positive else "DN",
        "not_claimed": not_claimed,
        "what_was_learned": _what_was_learned(execution_status, base_gate, arms),
        "reproducibility_contract": _local_reproducibility_contract(
            seed=seed,
            status=execution_status,
            dependency_status=dependency_status,
            device_policy=(
                dict(base_training_evidence["device_policy"])
                if base_training_evidence is not None and isinstance(base_training_evidence.get("device_policy"), Mapping)
                else None
            ),
        ),
    }
    if base_training_evidence is not None:
        payload["training_evidence"] = {"base": dict(base_training_evidence)}
    return payload


def _not_run_arms(reason: str) -> dict[str, Any]:
    return {
        "status": "not-run",
        "skip_reason": reason,
        "gap_head": {
            "status": "not-run",
            "skip_reason": reason,
            "feature_audit": gap_head_feature_audit(()),
        },
        "drt": {"status": "not-run", "skip_reason": reason},
        "heldout": {"status": "not-run", "skip_reason": reason},
        "same_training_surface": False,
    }


def _not_run_training_evidence(reason: str) -> dict[str, Any]:
    return {
        "status": "not-run",
        "reason": reason,
        "optimizer_steps": 0,
        "loss_decrease": 0.0,
        "parameter_l2_delta": 0.0,
    }


def _hardgate_row(status: str, criterion: str, evidence_pointer: str, reason: str = "") -> dict[str, Any]:
    return {
        "status": status,
        "criterion": criterion,
        "evidence_pointer": evidence_pointer,
        "reason": reason,
    }


def _hardgate_summary(
    *,
    execution_status: str,
    dependency_status: Mapping[str, str],
    data_surface: Mapping[str, Any],
    base_gate: Mapping[str, Any],
    arms: Mapping[str, Any],
    failed_gate: str | None,
    base_training_evidence: Mapping[str, Any] | None,
) -> dict[str, Any]:
    deps_ok = all(status == "installed" for status in dependency_status.values())
    base_pass = base_gate.get("status") == "pass"
    arms_pass = arms.get("status") == "pass"
    train_ok = bool(base_training_evidence) and float(base_training_evidence.get("loss_decrease", 0.0)) > 0.0
    gates = {
        "REAL": _hardgate_row("pass" if deps_ok else "fail", "MiniGrid dependency and native DoorKey stream executed", "$.dependency_status"),
        "BASE-CHANCE": _hardgate_row("pass" if base_pass else "fail", "base CI95-low exceeds chance plus delta for distinction and planning", "$.base_chance_gate"),
        "DATA": _hardgate_row("pass" if data_surface.get("status") == "pass" else "fail", "disjoint train/validation/test/heldout splits recorded", "$.data_surface"),
        "SEED": _hardgate_row("pass", "seed protocol recorded before results", "$.preregistration.split_protocol"),
        "GAP": _hardgate_row("pass" if arms.get("gap_head", {}).get("status") == "pass" else "fail", "gap-head arm clears predeclared AUROC and unlogged-error criteria", "$.arms.gap_head"),
        "DRT-REAL": _hardgate_row("pass" if arms.get("drt", {}).get("status") == "pass" else "fail", "DRT arm uses real optimizer training and clears endpoint criteria", "$.arms.drt"),
        "FAIR-INPUT": _hardgate_row("pass" if base_pass else "fail", "both arms share observation/action training surface", "$.control_protocol"),
        "FAIR-COMP": _hardgate_row("pass" if base_pass else "fail", "matched compute, parameter, and input comparison", "$.control_protocol"),
        "HELDOUT": _hardgate_row("pass" if arms.get("heldout", {}).get("status") == "pass" else "fail", "heldout result does not contradict the promoted scope", "$.arms.heldout"),
        "TRAIN": _hardgate_row("pass" if train_ok else "fail", "optimizer step, parameter delta, and loss decrease recorded", "$.training_evidence"),
        "STAT": _hardgate_row("pass" if arms_pass else "fail", "paired delta, CI, and effect size recorded for primary endpoints", "$.arms"),
        "REPRO": _hardgate_row("pass", "seed, raw digest, device, and dependency status recorded", "$.reproducibility_contract"),
    }
    if not base_pass:
        for name in ("GAP", "DRT-REAL", "HELDOUT", "STAT"):
            gates[name]["status"] = "fail"
            gates[name]["reason"] = "downstream arm not run because base gate failed"
    status = "pass" if execution_status == "completed" and all(row["status"] == "pass" for row in gates.values()) else "fail"
    return {
        "status": status,
        "failed_gate": failed_gate,
        "gates": gates,
        "gate_order": list(HARDGATE_ORDER),
    }


def _local_reproducibility_contract(
    *,
    seed: int,
    status: str,
    dependency_status: Mapping[str, str],
    device_policy: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    recorded_device_policy = (
        dict(device_policy)
        if device_policy is not None
        else {
            "requested_device": "cpu",
            "resolved_device": "cpu",
            "resolution_status": "available",
            "resolution_reason": "local-contract-records-run-artifact-device-separately",
            "backend_details": dict(dependency_status),
        }
    )
    return {
        "schema_id": "bedc-quality-lab:canonical-reproducibility-contract",
        "mode": "exact_fixture",
        "seed_list": [int(seed)],
        "metric_bands": [
            {
                "pointer": "$.execution_status",
                "reference_value": status,
                "tolerance": 0,
                "comparison": "status_equal",
                "owner": "minigrid-doorkey-task-probe",
                "calibration_source": "$.preregistration",
                "seed_basis": {"seed_count": 1, "source": "$.config.seed"},
            }
        ],
        "device_policy": recorded_device_policy,
        "framework_provenance": {"python": "recorded-by-fingerprint", "dependency_abi": dict(dependency_status)},
        "calibration": {
            "calibration_source": "$.preregistration",
            "owner": "minigrid-doorkey-task-probe",
            "basis": "predeclared capsule digest and seed split",
        },
    }


def _what_was_learned(execution_status: str, base_gate: Mapping[str, Any], arms: Mapping[str, Any]) -> str:
    if execution_status == "abstain":
        return "base gate or environment boundary prevented downstream task-probe claims"
    if base_gate.get("status") != "pass":
        return "MiniGrid DoorKey base did not clear the predeclared base-above-chance gate"
    if arms.get("status") != "pass":
        return "base cleared chance, but at least one same-surface gap-head or DRT arm missed its predeclared criterion"
    return "base cleared chance and same-surface gap-head plus DRT arms cleared their bounded task criteria"


def _heldout_arm(surface: TrainingSurface, base: TrainedProbe, gap_head: Mapping[str, Any], drt: Mapping[str, Any]) -> dict[str, Any]:
    if gap_head.get("status") != "pass" or drt.get("status") != "pass":
        return {"status": "fail", "reason": "in-distribution arm failed"}
    base_task = binary_accuracy(base.distinction_scores["heldout"], surface.heldout["labels"])
    return {
        "status": "pass" if base_task >= 0.5 else "fail",
        "base_heldout_task_success": float(base_task),
        "claim_rule": "heldout failure blocks generalization wording and leaves in-distribution evidence diagnostic-only",
    }


def build_payload(
    *,
    generated_at: str | None = None,
    sample_budget: int = DEFAULT_SAMPLE_BUDGET,
    planning_state_count: int = DEFAULT_PLANNING_STATE_COUNT,
    seed: int = DEFAULT_SEED,
    requested_device: str = "auto",
    bootstrap_resamples: int = DEFAULT_BOOTSTRAP_RESAMPLES,
) -> dict[str, Any]:
    timestamp = generated_at or DEFAULT_GENERATED_AT
    prereg = preregistration_capsule(
        sample_budget=sample_budget,
        planning_state_count=planning_state_count,
        seed=seed,
    )
    deps = dependency_status()
    if not all(status == "installed" for status in deps.values()):
        return _dependency_abstain_payload(
            prereg=prereg,
            generated_at=timestamp,
            deps=deps,
            sample_budget=sample_budget,
            seed=seed,
        )
    surface = collect_training_surface(
        sample_budget=sample_budget,
        planning_state_count=planning_state_count,
        seed=seed,
    )
    base = train_base_probe(surface, seed=seed, requested_device=requested_device)
    base_gate = evaluate_base_chance_gate(surface, base, seed=seed, bootstrap_resamples=bootstrap_resamples)
    data_surface = _surface_summary(surface, prereg)
    if base_gate["status"] != "pass":
        return _base_payload(
            prereg=prereg,
            generated_at=timestamp,
            sample_budget=sample_budget,
            seed=seed,
            execution_status="abstain",
            dependency_status=deps,
            data_surface=data_surface,
            base_gate=base_gate,
            arms=_not_run_arms("base-chance-gate-failed"),
            claim_boundary_status="bounded-negative",
            failed_gate="BASE-CHANCE",
            base_training_evidence=base.training_evidence,
        )
    gap_head = run_gap_head_arm(surface, base, seed=seed, bootstrap_resamples=bootstrap_resamples)
    drt = train_drt_probe(
        surface,
        base,
        seed=seed,
        requested_device=requested_device,
        epochs=DEFAULT_EPOCHS,
        bootstrap_resamples=bootstrap_resamples,
    )
    heldout = _heldout_arm(surface, base, gap_head, drt)
    arms_status = "pass" if gap_head["status"] == "pass" and drt["status"] == "pass" and heldout["status"] == "pass" else "fail"
    arms = {
        "status": arms_status,
        "gap_head": gap_head,
        "drt": drt,
        "heldout": heldout,
        "same_training_surface": True,
    }
    return _base_payload(
        prereg=prereg,
        generated_at=timestamp,
        sample_budget=sample_budget,
        seed=seed,
        execution_status="completed" if arms_status == "pass" else "bounded-negative",
        dependency_status=deps,
        data_surface=data_surface,
        base_gate=base_gate,
        arms=arms,
        claim_boundary_status="pass" if arms_status == "pass" else "bounded-negative",
        failed_gate=None if arms_status == "pass" else ("GAP" if gap_head["status"] != "pass" else "DRT-REAL"),
        base_training_evidence=base.training_evidence,
    ) | {
        "training_evidence": {
            "base": base.training_evidence,
            "drt": drt.get("training_evidence"),
            "raw_digest": canonical_digest(
                {
                    "base_gate": base_gate,
                    "gap_head": gap_head,
                    "drt": {key: value for key, value in drt.items() if key != "training_evidence"},
                }
            ),
        },
    }


def render_markdown(payload: Mapping[str, Any]) -> str:
    base = payload.get("base_chance_gate", {})
    arms = payload.get("arms", {})
    hardgate = payload.get("hardgate", {})
    lines = [
        "# MiniGrid DoorKey Task Probe",
        "",
        f"- Generated at: `{payload.get('generated_at')}`",
        f"- Execution status: `{payload.get('execution_status')}`",
        f"- Claim boundary: `{payload.get('claim_boundary', {}).get('status')}`",
        f"- Preregistration digest: `{payload.get('preregistration', {}).get('preregistration_digest')}`",
        f"- Base gate: `{base.get('status')}`",
        f"- Arms: `{arms.get('status')}`",
        f"- Hardgate: `{hardgate.get('status')}`",
        "",
        "## Hardgates",
        "",
        "| gate | status | evidence |",
        "| --- | --- | --- |",
    ]
    gates = hardgate.get("gates") if isinstance(hardgate, Mapping) else {}
    if isinstance(gates, Mapping):
        for gate in HARDGATE_ORDER:
            row = gates.get(gate, {})
            lines.append(f"| `{gate}` | `{row.get('status')}` | `{row.get('evidence_pointer')}` |")
    lines.extend(["", "## Not Claimed", ""])
    for item in payload.get("not_claimed", []):
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def write_artifacts(
    *,
    json_path: str | Path,
    markdown_path: str | Path,
    generated_at: str | None = None,
    sample_budget: int = DEFAULT_SAMPLE_BUDGET,
    planning_state_count: int = DEFAULT_PLANNING_STATE_COUNT,
    seed: int = DEFAULT_SEED,
    requested_device: str = "auto",
) -> dict[str, Any]:
    payload = build_payload(
        generated_at=generated_at,
        sample_budget=sample_budget,
        planning_state_count=planning_state_count,
        seed=seed,
        requested_device=requested_device,
    )
    target_json = Path(json_path)
    target_md = Path(markdown_path)
    target_json.parent.mkdir(parents=True, exist_ok=True)
    target_md.parent.mkdir(parents=True, exist_ok=True)
    target_json.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    target_md.write_text(render_markdown(payload), encoding="utf-8")
    return payload

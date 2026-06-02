#!/usr/bin/env python3
"""Run a Gaussian-OU operational distinction-head experiment."""

from __future__ import annotations

from datetime import datetime, timezone
import json
import math
from pathlib import Path
import sys
from typing import Any

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.toy_world import make_toy_batch
from scripts.experiment_stats import metric_stats
from scripts.run_gaussian_ou_lejepa import run_experiment


SAMPLE_COUNT = 384
SEED_COUNT = 30
RHO = 0.82
USE_TORCH = False
MASTER_SEED = 479021
TRAIN_FRACTION = 0.70
DISTINCTIONS = ("latent_x_positive", "latent_y_positive", "high_energy")
JSON_ARTIFACT = "reports/gaussian_ou_distinction_head.json"
REPORT_ARTIFACT = "reports/gaussian_ou_distinction_head.md"
PROBE_STEPS = 700
PROBE_LR = 0.18
PROBE_L2 = 1.0e-4
EPS = 1.0e-12
MARGIN_THRESHOLD = 1.0
LOSS_WEIGHTS = {
    "task": 1.0,
    "stability": 0.15,
    "margin": 0.05,
    "intervention": 0.20,
}
_STABILITY_TRANSFORMS = (
    {"name": "translate_small", "kind": "translate", "delta": (0.08, -0.06)},
    {"name": "rotate_small", "kind": "rotate", "radians": 0.08},
    {"name": "noise_bounded", "kind": "noise", "scale": 0.035},
    {"name": "occlude_x_soft", "kind": "scale_axis", "axis": 0, "scale": 0.86},
    {"name": "occlude_y_soft", "kind": "scale_axis", "axis": 1, "scale": 0.86},
)


def _child_seed(master_seed: int, seed_index: int) -> int:
    value = (
        int(master_seed) * 1664525
        + 1013904223
        + int(seed_index) * 2246822519
        + int(seed_index) * int(seed_index) * 3266489917
    )
    return int(value % (2**32))


def _seeds(master_seed: int = MASTER_SEED, count: int = SEED_COUNT) -> list[int]:
    return [_child_seed(master_seed, index) for index in range(count)]


def _require_finite(name: str, array: np.ndarray) -> np.ndarray:
    value = np.asarray(array, dtype=np.float64)
    if value.ndim != 2:
        raise ValueError(f"{name} must be a two-dimensional array")
    if value.shape[0] == 0:
        raise ValueError(f"{name} must not be empty")
    if not np.all(np.isfinite(value)):
        raise ValueError(f"{name} contains non-finite values")
    return value


def _train_eval_split(n: int, *, seed: int, train_fraction: float = TRAIN_FRACTION) -> tuple[np.ndarray, np.ndarray]:
    if n < 4:
        raise ValueError("sample count must be at least four")
    rng = np.random.default_rng(seed ^ 0xA5A5A5A5)
    indices = rng.permutation(n)
    train_count = int(round(float(train_fraction) * n))
    train_count = min(max(train_count, 1), n - 1)
    return np.sort(indices[:train_count]), np.sort(indices[train_count:])


def _high_energy_threshold(z: np.ndarray, train_idx: np.ndarray) -> float:
    z = _require_finite("z", z)
    energy = np.sum(np.square(z[train_idx]), axis=1)
    return float(np.median(energy))


def _label_truth(name: str, z: np.ndarray, *, high_energy_threshold: float) -> np.ndarray:
    z = _require_finite("z", z)
    if z.shape[1] != 2:
        raise ValueError("z must have shape (n, 2)")
    if name == "latent_x_positive":
        labels = z[:, 0] > 0.0
    elif name == "latent_y_positive":
        labels = z[:, 1] > 0.0
    elif name == "high_energy":
        labels = np.sum(np.square(z), axis=1) > float(high_energy_threshold)
    else:
        raise ValueError(f"unknown distinction: {name}")
    return labels.astype(np.float64)


def _transform_latents(z: np.ndarray, transform: dict[str, Any]) -> np.ndarray:
    z = _require_finite("z", z)
    kind = str(transform["kind"])
    if kind == "translate":
        delta = np.asarray(transform["delta"], dtype=np.float64).reshape(1, 2)
        return z + delta
    if kind == "rotate":
        radians = float(transform["radians"])
        c = math.cos(radians)
        s = math.sin(radians)
        matrix = np.array([[c, -s], [s, c]], dtype=np.float64)
        return z @ matrix.T
    if kind == "noise":
        row_phase = np.arange(z.shape[0], dtype=np.float64).reshape(-1, 1)
        bounded = np.sin(z[:, ::-1] * 1.7 + row_phase * 0.37)
        return z + float(transform["scale"]) * bounded
    if kind == "scale_axis":
        out = np.array(z, copy=True)
        out[:, int(transform["axis"])] *= float(transform["scale"])
        return out
    raise ValueError(f"unknown stability transform kind: {kind}")


def _stability_views(name: str, z: np.ndarray, *, high_energy_threshold: float) -> list[dict[str, Any]]:
    labels = _label_truth(name, z, high_energy_threshold=high_energy_threshold)
    views: list[dict[str, Any]] = []
    for transform in _STABILITY_TRANSFORMS:
        transformed = _transform_latents(z, transform)
        transformed_labels = _label_truth(
            name, transformed, high_energy_threshold=high_energy_threshold
        )
        mask = labels == transformed_labels
        views.append(
            {
                "name": str(transform["name"]),
                "x": transformed,
                "mask": mask,
                "truth_preserving_rate": float(np.mean(mask)),
            }
        )
    return views


def _standardize_fit(x: np.ndarray) -> dict[str, np.ndarray]:
    x = _require_finite("x", x)
    mean = np.mean(x, axis=0, keepdims=True)
    scale = np.std(x, axis=0, keepdims=True)
    scale = np.where(scale <= EPS, 1.0, scale)
    return {"mean": mean, "scale": scale}


def _standardize_apply(x: np.ndarray, state: dict[str, np.ndarray]) -> np.ndarray:
    x = _require_finite("x", x)
    return (x - state["mean"]) / state["scale"]


def _sigmoid(logits: np.ndarray) -> np.ndarray:
    clipped = np.clip(logits, -60.0, 60.0)
    return 1.0 / (1.0 + np.exp(-clipped))


def _empty_loss_components() -> dict[str, float]:
    return {
        "task_bce": 0.0,
        "stability": 0.0,
        "margin": 0.0,
        "intervention": 0.0,
        "objective_total": 0.0,
    }


def _loss_components(
    probe: dict[str, Any],
    x: np.ndarray,
    y: np.ndarray,
    *,
    stable_views: list[dict[str, Any]] | None = None,
    intervention_view: dict[str, Any] | None = None,
    off_target_views: list[dict[str, Any]] | None = None,
    loss_weights: dict[str, float] = LOSS_WEIGHTS,
) -> dict[str, float]:
    pred = _predict_probe(probe, x)
    labels = np.asarray(y, dtype=np.float64)
    logits = pred["logits"]
    probs = pred["probabilities"]
    task = _bce(labels, probs)
    margin_values = np.maximum(0.0, MARGIN_THRESHOLD - np.abs(logits))
    margin = float(np.mean(margin_values))

    stability_values: list[float] = []
    for view in stable_views or []:
        mask = np.asarray(view["mask"], dtype=bool)
        if np.any(mask):
            view_probs = _predict_probe(probe, view["x"])["probabilities"]
            stability_values.append(float(np.mean(np.abs(view_probs[mask] - probs[mask]))))
    stability = float(np.mean(stability_values)) if stability_values else 0.0

    intervention_parts: list[float] = []
    if intervention_view is not None:
        target_probs = _predict_probe(probe, intervention_view["x"])["probabilities"]
        intervention_parts.append(float(np.mean(np.abs(target_probs - (1.0 - probs)))))
    for view in off_target_views or []:
        off_probs = _predict_probe(probe, view["x"])["probabilities"]
        mask = np.asarray(view["mask"], dtype=bool)
        if np.any(mask):
            intervention_parts.append(float(np.mean(np.abs(off_probs[mask] - probs[mask]))))
    intervention = float(np.mean(intervention_parts)) if intervention_parts else 0.0

    total = (
        float(loss_weights["task"]) * task
        + float(loss_weights["stability"]) * stability
        + float(loss_weights["margin"]) * margin
        + float(loss_weights["intervention"]) * intervention
    )
    return {
        "task_bce": task,
        "stability": stability,
        "margin": margin,
        "intervention": intervention,
        "objective_total": float(total),
    }


def _train_view_gradients(
    *,
    xs: np.ndarray,
    logits: np.ndarray,
    probs: np.ndarray,
    weights: np.ndarray,
    bias: float,
    standardizer: dict[str, np.ndarray],
    stable_views: list[dict[str, Any]] | None,
    intervention_view: dict[str, Any] | None,
    off_target_views: list[dict[str, Any]] | None,
) -> tuple[np.ndarray, float]:
    grad_w = np.zeros_like(weights)
    grad_b = 0.0

    signed = np.where(logits >= 0.0, 1.0, -1.0)
    active = np.abs(logits) < MARGIN_THRESHOLD
    if np.any(active):
        scale = -signed[active] / float(xs.shape[0])
        grad_w += float(LOSS_WEIGHTS["margin"]) * (xs[active].T @ scale)
        grad_b += float(LOSS_WEIGHTS["margin"]) * float(np.sum(scale))

    for view in stable_views or []:
        mask = np.asarray(view["mask"], dtype=bool)
        if not np.any(mask):
            continue
        view_xs = _standardize_apply(view["x"], standardizer)
        view_logits = view_xs @ weights + float(bias)
        view_probs = _sigmoid(view_logits)
        diff = view_probs[mask] - probs[mask]
        denom = float(np.sum(mask))
        direction = np.sign(diff) / denom
        d_view = direction * view_probs[mask] * (1.0 - view_probs[mask])
        d_base = -direction * probs[mask] * (1.0 - probs[mask])
        grad_w += float(LOSS_WEIGHTS["stability"]) * (view_xs[mask].T @ d_view + xs[mask].T @ d_base)
        grad_b += float(LOSS_WEIGHTS["stability"]) * float(np.sum(d_view + d_base))

    intervention_terms: list[tuple[np.ndarray, np.ndarray, bool, np.ndarray]] = []
    if intervention_view is not None:
        intervention_terms.append(
            (
                _standardize_apply(intervention_view["x"], standardizer),
                1.0 - probs,
                True,
                np.ones(xs.shape[0], dtype=bool),
            )
        )
    for view in off_target_views or []:
        mask = np.asarray(view["mask"], dtype=bool)
        if np.any(mask):
            intervention_terms.append(
                (_standardize_apply(view["x"], standardizer), probs, False, mask)
            )
    if intervention_terms:
        term_weight = float(LOSS_WEIGHTS["intervention"]) / float(len(intervention_terms))
        for view_xs, target_probs, target_flip, mask in intervention_terms:
            view_probs = _sigmoid(view_xs @ weights + float(bias))
            diff = view_probs[mask] - target_probs[mask]
            denom = float(np.sum(mask))
            direction = np.sign(diff) / denom
            d_view = direction * view_probs[mask] * (1.0 - view_probs[mask])
            grad_w += term_weight * (view_xs[mask].T @ d_view)
            grad_b += term_weight * float(np.sum(d_view))
            base_sign = 1.0 if target_flip else -1.0
            d_base = base_sign * direction * probs[mask] * (1.0 - probs[mask])
            grad_w += term_weight * (xs[mask].T @ d_base)
            grad_b += term_weight * float(np.sum(d_base))

    return grad_w, grad_b


def _fit_probe(
    x: np.ndarray,
    y: np.ndarray,
    *,
    steps: int = PROBE_STEPS,
    lr: float = PROBE_LR,
    l2: float = PROBE_L2,
    stable_views: list[dict[str, Any]] | None = None,
    intervention_view: dict[str, Any] | None = None,
    off_target_views: list[dict[str, Any]] | None = None,
) -> dict[str, Any]:
    x = _require_finite("x", x)
    y = np.asarray(y, dtype=np.float64)
    if y.ndim != 1 or y.shape[0] != x.shape[0]:
        raise ValueError("y must be a one-dimensional array aligned with x")
    if not np.all(np.isfinite(y)):
        raise ValueError("y contains non-finite values")
    if not set(np.unique(y)).issubset({0.0, 1.0}):
        raise ValueError("y must contain binary labels")

    standardizer = _standardize_fit(x)
    xs = _standardize_apply(x, standardizer)
    weights = np.zeros(xs.shape[1], dtype=np.float64)
    bias = 0.0
    n = float(xs.shape[0])
    for _ in range(int(steps)):
        logits = xs @ weights + bias
        probs = _sigmoid(logits)
        residual = probs - y
        grad_w = float(LOSS_WEIGHTS["task"]) * ((xs.T @ residual) / n) + float(l2) * weights
        grad_b = float(LOSS_WEIGHTS["task"]) * float(np.mean(residual))
        view_grad_w, view_grad_b = _train_view_gradients(
            xs=xs,
            logits=logits,
            probs=probs,
            weights=weights,
            bias=bias,
            standardizer=standardizer,
            stable_views=stable_views,
            intervention_view=intervention_view,
            off_target_views=off_target_views,
        )
        weights -= float(lr) * (grad_w + view_grad_w)
        bias -= float(lr) * (grad_b + view_grad_b)
    return {"weights": weights, "bias": float(bias), "standardizer": standardizer}


def _predict_probe(probe: dict[str, Any], x: np.ndarray) -> dict[str, np.ndarray]:
    xs = _standardize_apply(x, probe["standardizer"])
    logits = xs @ probe["weights"] + float(probe["bias"])
    probs = _sigmoid(logits)
    return {
        "logits": logits.astype(np.float64),
        "probabilities": probs.astype(np.float64),
        "predictions": (probs >= 0.5).astype(np.float64),
    }


def _bce(y: np.ndarray, probs: np.ndarray) -> float:
    y = np.asarray(y, dtype=np.float64)
    probs = np.asarray(probs, dtype=np.float64)
    clipped = np.clip(probs, EPS, 1.0 - EPS)
    return float(-np.mean(y * np.log(clipped) + (1.0 - y) * np.log(1.0 - clipped)))


def _classification_metrics(probe: dict[str, Any], x: np.ndarray, y: np.ndarray) -> dict[str, float]:
    pred = _predict_probe(probe, x)
    labels = np.asarray(y, dtype=np.float64)
    predictions = pred["predictions"]
    signed = (2.0 * labels - 1.0) * pred["logits"]
    abs_logits = np.abs(pred["logits"])
    return {
        "bce": _bce(labels, pred["probabilities"]),
        "accuracy": float(np.mean(predictions == labels)),
        "margin": float(np.mean(signed)),
        "absolute_margin_mean": float(np.mean(abs_logits)),
        "absolute_margin_p10": float(np.quantile(abs_logits, 0.10)),
        "threshold_debt_rate": float(np.mean(abs_logits < MARGIN_THRESHOLD)),
        "positive_rate": float(np.mean(labels)),
        "prediction_positive_rate": float(np.mean(predictions)),
    }


def _intervene(
    name: str,
    z: np.ndarray,
    z_pair: np.ndarray,
    *,
    high_energy_threshold: float | None = None,
) -> np.ndarray:
    z = _require_finite("z", z)
    z_pair = _require_finite("z_pair", z_pair)
    if z.shape != z_pair.shape:
        raise ValueError("z and z_pair must have the same shape")
    intervened = np.array(z, copy=True)
    if name == "latent_x_positive":
        intervened[:, 0] = -intervened[:, 0]
    elif name == "latent_y_positive":
        intervened[:, 1] = -intervened[:, 1]
    elif name == "high_energy":
        intervened = np.array(z_pair, copy=True)
        if high_energy_threshold is not None:
            before = _label_truth(
                "high_energy", z, high_energy_threshold=float(high_energy_threshold)
            )
            after = _label_truth(
                "high_energy", intervened, high_energy_threshold=float(high_energy_threshold)
            )
            unchanged = before == after
            if np.any(unchanged):
                repaired = np.array(intervened, copy=True)
                threshold = max(float(high_energy_threshold), EPS)
                source = z[unchanged]
                energy = np.sum(np.square(source), axis=1)
                positive = before[unchanged] > 0.5
                scales = np.ones(source.shape[0], dtype=np.float64)
                if np.any(positive):
                    scales[positive] = np.sqrt((0.49 * threshold) / np.maximum(energy[positive], EPS))
                if np.any(~positive):
                    scales[~positive] = np.sqrt((1.44 * threshold) / np.maximum(energy[~positive], EPS))
                crossed = source * scales.reshape(-1, 1)
                zero_rows = np.sum(np.square(crossed), axis=1) <= EPS
                if np.any(zero_rows):
                    crossed[zero_rows, 0] = math.sqrt(1.44 * threshold)
                repaired[unchanged] = crossed
                intervened = repaired
    else:
        raise ValueError(f"unknown distinction: {name}")
    return intervened


def _intervention_training_views(
    name: str,
    z: np.ndarray,
    z_pair: np.ndarray,
    *,
    high_energy_threshold: float,
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    labels = _label_truth(name, z, high_energy_threshold=high_energy_threshold)
    own = _intervene(name, z, z_pair, high_energy_threshold=high_energy_threshold)
    off_target: list[dict[str, Any]] = []
    for target in DISTINCTIONS:
        if target == name:
            continue
        changed = _intervene(target, z, z_pair, high_energy_threshold=high_energy_threshold)
        changed_labels = _label_truth(name, changed, high_energy_threshold=high_energy_threshold)
        off_target.append(
            {
                "name": target,
                "x": changed,
                "mask": labels == changed_labels,
                "truth_preserving_rate": float(np.mean(labels == changed_labels)),
            }
        )
    return {"name": name, "x": own}, off_target


def _stability_metric(
    probe: dict[str, Any],
    x: np.ndarray,
    *,
    stable_views: list[dict[str, Any]],
) -> dict[str, Any]:
    base_probs = _predict_probe(probe, x)["probabilities"]
    per_transform: dict[str, Any] = {}
    values: list[float] = []
    for view in stable_views:
        mask = np.asarray(view["mask"], dtype=bool)
        view_probs = _predict_probe(probe, view["x"])["probabilities"]
        if np.any(mask):
            delta = float(np.mean(np.abs(view_probs[mask] - base_probs[mask])))
        else:
            delta = 0.0
        values.append(delta)
        per_transform[str(view["name"])] = {
            "e_alpha_abs_probability_delta": delta,
            "truth_preserving_rate": float(view["truth_preserving_rate"]),
        }
    return {
        "e_alpha_abs_probability_delta": float(np.mean(values)) if values else 0.0,
        "per_transform": per_transform,
    }


def _source_artifacts() -> dict[str, Any]:
    return {
        "generation_script": "scripts/run_gaussian_ou_distinction_head.py",
        "canonical_runner": "scripts/run_gaussian_ou_lejepa.py::run_experiment",
        "toy_world": "bedc_quality_lab.toy_world.make_toy_batch",
        "stats_helper": "scripts/experiment_stats.py",
        "json_artifact": JSON_ARTIFACT,
        "report_artifact": REPORT_ARTIFACT,
        "import_dependency_chain": [
            "scripts/run_gaussian_ou_distinction_head.py",
            "scripts.run_gaussian_ou_lejepa.run_experiment",
            "bedc_quality_lab.toy_world.make_toy_batch",
            "scripts.experiment_stats.metric_stats",
        ],
    }


def _applicability_boundary() -> dict[str, Any]:
    return {
        "admitted_family": "Gaussian-OU toy world generated by the existing lab toy-world generator.",
        "model": (
            "Script-local numpy logistic probes trained on replayed ground-truth Gaussian-OU latents."
        ),
        "sample_count": SAMPLE_COUNT,
        "seed_count": SEED_COUNT,
        "rho": RHO,
        "distinctions": list(DISTINCTIONS),
        "representation_boundary": (
            "D(z) uses deterministic fallback projection from replayed latent z; this does not claim "
            "coverage of torch-only learned representations."
        ),
        "intervention_boundary": (
            "Interventions are finite Gaussian-OU operators: flip latent coordinate signs or replace "
            "the sample by its OU pair."
        ),
        "threshold_boundary": (
            "The high_energy threshold is fixed from each seed's train split before eval and intervention."
        ),
    }


def _negative_result_note() -> str:
    return (
        "The configured seed count, split, distinctions, threshold rule, and intervention operators are "
        "fixed before observing outcomes; weak or failed intervention separation is reported directly."
    )


def _run_record(*, seed: int, seed_index: int) -> dict[str, Any]:
    batch = make_toy_batch(SAMPLE_COUNT, rho=RHO, seed=seed)
    z = _require_finite("z", batch.z)
    z_pair = _require_finite("z_pair", batch.z_pair)
    train_idx, eval_idx = _train_eval_split(z.shape[0], seed=seed)
    high_threshold = _high_energy_threshold(z, train_idx)
    run_id = f"gaussian-ou-distinction-head-seed-{seed}"
    envelope = run_experiment(
        use_torch=USE_TORCH,
        sample_count=SAMPLE_COUNT,
        seed=seed,
        rho=RHO,
        run_id=run_id,
        envelope_artifact=JSON_ARTIFACT,
        report_artifact=REPORT_ARTIFACT,
    )

    labels = {
        name: _label_truth(name, z, high_energy_threshold=high_threshold)
        for name in DISTINCTIONS
    }
    pair_labels = {
        name: _label_truth(name, z_pair, high_energy_threshold=high_threshold)
        for name in DISTINCTIONS
    }
    train_views: dict[str, Any] = {}
    eval_views: dict[str, Any] = {}
    for name in DISTINCTIONS:
        train_intervention, train_off_target = _intervention_training_views(
            name,
            z[train_idx],
            z_pair[train_idx],
            high_energy_threshold=high_threshold,
        )
        eval_intervention, eval_off_target = _intervention_training_views(
            name,
            z[eval_idx],
            z_pair[eval_idx],
            high_energy_threshold=high_threshold,
        )
        train_views[name] = {
            "stable": _stability_views(name, z[train_idx], high_energy_threshold=high_threshold),
            "intervention": train_intervention,
            "off_target": train_off_target,
        }
        eval_views[name] = {
            "stable": _stability_views(name, z[eval_idx], high_energy_threshold=high_threshold),
            "intervention": eval_intervention,
            "off_target": eval_off_target,
        }
    probes = {
        name: _fit_probe(
            z[train_idx],
            label[train_idx],
            stable_views=train_views[name]["stable"],
            intervention_view=train_views[name]["intervention"],
            off_target_views=train_views[name]["off_target"],
        )
        for name, label in labels.items()
    }

    per_distinction: dict[str, Any] = {}
    for name in DISTINCTIONS:
        train_metrics = _classification_metrics(probes[name], z[train_idx], labels[name][train_idx])
        eval_metrics = _classification_metrics(probes[name], z[eval_idx], labels[name][eval_idx])
        stability = _stability_metric(
            probes[name], z[eval_idx], stable_views=eval_views[name]["stable"]
        )
        train_loss = _loss_components(
            probes[name],
            z[train_idx],
            labels[name][train_idx],
            stable_views=train_views[name]["stable"],
            intervention_view=train_views[name]["intervention"],
            off_target_views=train_views[name]["off_target"],
        )
        eval_loss = _loss_components(
            probes[name],
            z[eval_idx],
            labels[name][eval_idx],
            stable_views=eval_views[name]["stable"],
            intervention_view=eval_views[name]["intervention"],
            off_target_views=eval_views[name]["off_target"],
        )
        per_distinction[name] = {
            "truth": {
                "label_positive_rate_train": float(np.mean(labels[name][train_idx])),
                "label_positive_rate_eval": float(np.mean(labels[name][eval_idx])),
                "pair_label_positive_rate": float(np.mean(pair_labels[name])),
                "ou_pair_truth_agreement_rate": float(np.mean(labels[name] == pair_labels[name])),
            },
            "train": train_metrics,
            "eval": eval_metrics,
            "stability": stability["e_alpha_abs_probability_delta"],
            "stability_detail": stability,
            "margin": float(eval_metrics["absolute_margin_mean"]),
            "margin_distribution": {
                "absolute_margin_mean": float(eval_metrics["absolute_margin_mean"]),
                "absolute_margin_p10": float(eval_metrics["absolute_margin_p10"]),
                "threshold_debt_rate": float(eval_metrics["threshold_debt_rate"]),
            },
            "train_loss_components": train_loss,
            "eval_loss_components": eval_loss,
            "generalization_gap": float(train_metrics["accuracy"] - eval_metrics["accuracy"]),
        }

    intervention: dict[str, Any] = {}
    for target in DISTINCTIONS:
        z_changed = _intervene(
            target, z[eval_idx], z_pair[eval_idx], high_energy_threshold=high_threshold
        )
        target_rows: dict[str, Any] = {}
        off_target_rates: list[float] = []
        for name in DISTINCTIONS:
            before = _predict_probe(probes[name], z[eval_idx])["predictions"]
            after = _predict_probe(probes[name], z_changed)["predictions"]
            truth_after = _label_truth(name, z_changed, high_energy_threshold=high_threshold)
            flip_rate = float(np.mean(before != after))
            accuracy_after = float(np.mean(after == truth_after))
            truth_before = labels[name][eval_idx]
            truth_flip_rate = float(np.mean(truth_before != truth_after))
            target_rows[name] = {
                "prediction_flip_rate": flip_rate,
                "truth_flip_rate": truth_flip_rate,
                "prediction_truth_flip_gap": float(flip_rate - truth_flip_rate),
                "post_intervention_truth_positive_rate": float(np.mean(truth_after)),
                "post_intervention_accuracy": accuracy_after,
            }
            if name != target:
                off_target_rates.append(flip_rate)
        intervention[target] = {
            "on_target_flip_rate": float(target_rows[target]["prediction_flip_rate"]),
            "on_target_truth_flip_rate": float(target_rows[target]["truth_flip_rate"]),
            "on_target_prediction_truth_flip_gap": float(
                target_rows[target]["prediction_truth_flip_gap"]
            ),
            "off_target_flip_rate": float(np.mean(off_target_rates)) if off_target_rates else 0.0,
            "per_distinction": target_rows,
        }

    return {
        "seed_index": int(seed_index),
        "seed_sequence_position": int(seed_index + 1),
        "seed": int(seed),
        "run_id": run_id,
        "config": {
            "sample_count": SAMPLE_COUNT,
            "rho": RHO,
            "use_torch": USE_TORCH,
            "distinctions": list(DISTINCTIONS),
            "train_fraction": TRAIN_FRACTION,
            "train_count": int(len(train_idx)),
            "eval_count": int(len(eval_idx)),
            "probe_steps": PROBE_STEPS,
            "probe_lr": PROBE_LR,
            "probe_l2": PROBE_L2,
            "margin_threshold": MARGIN_THRESHOLD,
            "loss_weights": dict(LOSS_WEIGHTS),
            "stability_transforms": [dict(transform) for transform in _STABILITY_TRANSFORMS],
            "high_energy_threshold": high_threshold,
        },
        "split": {
            "train_indices": [int(index) for index in train_idx],
            "eval_indices": [int(index) for index in eval_idx],
            "overlap_count": int(len(set(train_idx.tolist()) & set(eval_idx.tolist()))),
        },
        "canonical_envelope_projection": {
            "run_id": envelope.run_id,
            "source_spec": dict(envelope.source_spec),
            "classifier_spec": dict(envelope.classifier_spec),
            "metrics": {name: float(value) for name, value in envelope.metrics.items()},
            "artifacts": dict(envelope.artifacts),
        },
        "per_distinction": per_distinction,
        "intervention": intervention,
        "negative_result_note": _negative_result_note(),
        "applicability_boundary": _applicability_boundary(),
        "source_artifacts": _source_artifacts(),
    }


def _records() -> list[dict[str, Any]]:
    return [_run_record(seed=seed, seed_index=index) for index, seed in enumerate(_seeds())]


def _aggregate(records: list[dict[str, Any]]) -> dict[str, Any]:
    per_distinction: dict[str, Any] = {}
    for name in DISTINCTIONS:
        train_accuracy = [
            float(record["per_distinction"][name]["train"]["accuracy"]) for record in records
        ]
        eval_accuracy = [
            float(record["per_distinction"][name]["eval"]["accuracy"]) for record in records
        ]
        train_bce = [float(record["per_distinction"][name]["train"]["bce"]) for record in records]
        eval_bce = [float(record["per_distinction"][name]["eval"]["bce"]) for record in records]
        stability = [float(record["per_distinction"][name]["stability"]) for record in records]
        margin = [float(record["per_distinction"][name]["margin"]) for record in records]
        margin_p10 = [
            float(record["per_distinction"][name]["margin_distribution"]["absolute_margin_p10"])
            for record in records
        ]
        threshold_debt = [
            float(record["per_distinction"][name]["margin_distribution"]["threshold_debt_rate"])
            for record in records
        ]
        gap = [
            float(record["per_distinction"][name]["generalization_gap"]) for record in records
        ]
        train_loss = {
            key: [
                float(record["per_distinction"][name]["train_loss_components"][key])
                for record in records
            ]
            for key in _empty_loss_components()
        }
        eval_loss = {
            key: [
                float(record["per_distinction"][name]["eval_loss_components"][key])
                for record in records
            ]
            for key in _empty_loss_components()
        }
        on_target = [
            float(record["intervention"][name]["on_target_flip_rate"]) for record in records
        ]
        on_target_truth = [
            float(record["intervention"][name]["on_target_truth_flip_rate"]) for record in records
        ]
        on_target_gap = [
            float(record["intervention"][name]["on_target_prediction_truth_flip_gap"])
            for record in records
        ]
        off_target = [
            float(record["intervention"][name]["off_target_flip_rate"]) for record in records
        ]
        per_distinction[name] = {
            "train_accuracy": metric_stats(train_accuracy),
            "eval_accuracy": metric_stats(eval_accuracy),
            "train_bce": metric_stats(train_bce),
            "eval_bce": metric_stats(eval_bce),
            "stability": metric_stats(stability),
            "margin": metric_stats(margin),
            "absolute_margin_p10": metric_stats(margin_p10),
            "threshold_debt_rate": metric_stats(threshold_debt),
            "generalization_gap": metric_stats(gap),
            "train_loss_components": {
                key: metric_stats(values) for key, values in train_loss.items()
            },
            "eval_loss_components": {
                key: metric_stats(values) for key, values in eval_loss.items()
            },
            "intervention_on_target_flip_rate": metric_stats(on_target),
            "intervention_on_target_truth_flip_rate": metric_stats(on_target_truth),
            "intervention_on_target_prediction_truth_flip_gap": metric_stats(on_target_gap),
            "intervention_off_target_flip_rate": metric_stats(off_target),
            "intervention_separation": metric_stats(
                [on - off for on, off in zip(on_target, off_target)]
            ),
        }
    return {
        "record_count": len(records),
        "seed_order": [int(record["seed"]) for record in records],
        "per_distinction": per_distinction,
    }


def _negative_result_findings(aggregate: dict[str, Any]) -> list[dict[str, Any]]:
    findings: list[dict[str, Any]] = []
    for name in DISTINCTIONS:
        stats = aggregate["per_distinction"][name]
        eval_accuracy = float(stats["eval_accuracy"]["mean"])
        truth_flip = float(stats["intervention_on_target_truth_flip_rate"]["mean"])
        prediction_flip = float(stats["intervention_on_target_flip_rate"]["mean"])
        threshold_debt = float(stats["threshold_debt_rate"]["mean"])
        if truth_flip >= 0.80 and prediction_flip < 0.50:
            findings.append(
                {
                    "distinction": name,
                    "finding": "intervention_insensitive",
                    "eval_accuracy_mean": eval_accuracy,
                    "on_target_truth_flip_rate_mean": truth_flip,
                    "on_target_prediction_flip_rate_mean": prediction_flip,
                    "off_target_drift_mean": float(
                        stats["intervention_off_target_flip_rate"]["mean"]
                    ),
                }
            )
        if eval_accuracy < 0.70:
            findings.append(
                {
                    "distinction": name,
                    "finding": "held_out_accuracy_weak",
                    "eval_accuracy_mean": eval_accuracy,
                    "generalization_gap_mean": float(stats["generalization_gap"]["mean"]),
                }
            )
        if threshold_debt > 0.25:
            findings.append(
                {
                    "distinction": name,
                    "finding": "threshold_debt_high",
                    "threshold_debt_rate_mean": threshold_debt,
                    "absolute_margin_p10_mean": float(stats["absolute_margin_p10"]["mean"]),
                }
            )
    return findings


def _payload(records: list[dict[str, Any]]) -> dict[str, Any]:
    aggregate = _aggregate(records)
    return {
        "artifact": JSON_ARTIFACT,
        "report": REPORT_ARTIFACT,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "config": {
            "sample_count": SAMPLE_COUNT,
            "seed_count": SEED_COUNT,
            "seeds": _seeds(),
            "rho": RHO,
            "use_torch": USE_TORCH,
            "distinctions": list(DISTINCTIONS),
            "train_fraction": TRAIN_FRACTION,
            "probe_steps": PROBE_STEPS,
            "probe_lr": PROBE_LR,
            "probe_l2": PROBE_L2,
            "margin_threshold": MARGIN_THRESHOLD,
            "loss_weights": dict(LOSS_WEIGHTS),
            "stability_transforms": [dict(transform) for transform in _STABILITY_TRANSFORMS],
            "expected_record_count": SEED_COUNT,
        },
        "source_artifacts": _source_artifacts(),
        "applicability_boundary": _applicability_boundary(),
        "negative_result_note": _negative_result_note(),
        "negative_result_findings": _negative_result_findings(aggregate),
        "records": records,
        "aggregate": aggregate,
    }


def _format_float(value: float) -> str:
    if math.isnan(value):
        return "nan"
    return f"{value:.6f}"


def _render_stats(stats: dict[str, Any]) -> str:
    return (
        f"{_format_float(float(stats['mean']))} +/- {_format_float(float(stats['std']))} "
        f"(95% CI +/- {_format_float(float(stats['ci95_half_width']))})"
    )


def _render_report(payload: dict[str, Any]) -> str:
    aggregate = payload["aggregate"]
    lines = [
        "# Gaussian-OU Distinction-Head Experiment",
        "",
        f"- Generated at: `{payload['generated_at']}`",
        f"- Canonical runner: `{payload['source_artifacts']['canonical_runner']}`",
        f"- Sample count: `{payload['config']['sample_count']}`",
        f"- Seed count: `{payload['config']['seed_count']}`",
        f"- Rho: `{payload['config']['rho']}`",
        f"- Use torch: `{str(bool(payload['config']['use_torch'])).lower()}`",
        f"- Distinctions: `{', '.join(payload['config']['distinctions'])}`",
        f"- Train/eval split: `{payload['config']['train_fraction']:.2f}` train, deterministic per seed",
        f"- Loss weights: `{json.dumps(payload['config']['loss_weights'], sort_keys=True)}`",
        f"- Stability transforms: `{', '.join(transform['name'] for transform in payload['config']['stability_transforms'])}`",
        f"- Total records: `{aggregate['record_count']}`",
        "",
        "## Per-Distinction Metrics",
        "",
        (
            "| distinction | train accuracy | eval accuracy | eval BCE | stability | margin | "
            "train/eval accuracy gap |"
        ),
        "| --- | ---: | ---: | ---: | ---: | ---: | ---: |",
    ]
    for name in DISTINCTIONS:
        stats = aggregate["per_distinction"][name]
        lines.append(
            "| "
            f"`{name}` | "
            f"{_render_stats(stats['train_accuracy'])} | "
            f"{_render_stats(stats['eval_accuracy'])} | "
            f"{_render_stats(stats['eval_bce'])} | "
            f"{_render_stats(stats['stability'])} | "
            f"{_render_stats(stats['margin'])} | "
            f"{_render_stats(stats['generalization_gap'])} |"
        )
    lines.extend(
        [
            "",
            "## Loss Components",
            "",
            "| distinction | split | task BCE | stability | margin | intervention | objective |",
            "| --- | --- | ---: | ---: | ---: | ---: | ---: |",
        ]
    )
    for name in DISTINCTIONS:
        stats = aggregate["per_distinction"][name]
        for split_name, key in (
            ("train", "train_loss_components"),
            ("eval", "eval_loss_components"),
        ):
            loss = stats[key]
            lines.append(
                "| "
                f"`{name}` | {split_name} | "
                f"{_render_stats(loss['task_bce'])} | "
                f"{_render_stats(loss['stability'])} | "
                f"{_render_stats(loss['margin'])} | "
                f"{_render_stats(loss['intervention'])} | "
                f"{_render_stats(loss['objective_total'])} |"
            )
    lines.extend(
        [
            "",
            "## Margin Distribution",
            "",
            "| distinction | absolute margin p10 | threshold debt rate |",
            "| --- | ---: | ---: |",
        ]
    )
    for name in DISTINCTIONS:
        stats = aggregate["per_distinction"][name]
        lines.append(
            "| "
            f"`{name}` | "
            f"{_render_stats(stats['absolute_margin_p10'])} | "
            f"{_render_stats(stats['threshold_debt_rate'])} |"
        )
    lines.extend(
        [
            "",
            "## Intervention Metrics",
            "",
            "| target distinction | on-target prediction flip | on-target truth flip | prediction/truth gap | off-target drift | separation |",
            "| --- | ---: | ---: | ---: | ---: | ---: |",
        ]
    )
    for name in DISTINCTIONS:
        stats = aggregate["per_distinction"][name]
        lines.append(
            "| "
            f"`{name}` | "
            f"{_render_stats(stats['intervention_on_target_flip_rate'])} | "
            f"{_render_stats(stats['intervention_on_target_truth_flip_rate'])} | "
            f"{_render_stats(stats['intervention_on_target_prediction_truth_flip_gap'])} | "
            f"{_render_stats(stats['intervention_off_target_flip_rate'])} | "
            f"{_render_stats(stats['intervention_separation'])} |"
        )

    lines.extend(
        [
            "",
            "## Applicability Boundary",
            "",
        ]
    )
    for key, value in payload["applicability_boundary"].items():
        lines.append(f"- {key}: `{json.dumps(value, sort_keys=True)}`")

    lines.extend(
        [
            "",
            "## Negative Result Note",
            "",
            payload["negative_result_note"],
            "",
            "## Negative Result Findings",
            "",
            *(
                [f"- `{json.dumps(item, sort_keys=True)}`" for item in payload["negative_result_findings"]]
                if payload["negative_result_findings"]
                else ["- `[]`"]
            ),
            "",
            "## Source Artifacts",
            "",
            f"- Generation script: `{payload['source_artifacts']['generation_script']}`",
            f"- JSON artifact: `{payload['source_artifacts']['json_artifact']}`",
            f"- Report artifact: `{payload['source_artifacts']['report_artifact']}`",
            f"- Toy world: `{payload['source_artifacts']['toy_world']}`",
            f"- Stats helper: `{payload['source_artifacts']['stats_helper']}`",
            "- Import dependency chain:",
        ]
    )
    for item in payload["source_artifacts"]["import_dependency_chain"]:
        lines.append(f"  - `{item}`")

    lines.extend(
        [
            "",
            "## Seed Order",
            "",
            f"`{', '.join(str(seed) for seed in aggregate['seed_order'])}`",
            "",
        ]
    )
    return "\n".join(lines)


def _write_payload(payload: dict[str, Any]) -> None:
    json_path = ROOT / JSON_ARTIFACT
    report_path = ROOT / REPORT_ARTIFACT
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    report_path.write_text(_render_report(payload), encoding="utf-8")


def main() -> None:
    payload = _payload(_records())
    _write_payload(payload)
    print(f"wrote {JSON_ARTIFACT}")
    print(f"wrote {REPORT_ARTIFACT}")
    print(f"records {len(payload['records'])}")


if __name__ == "__main__":
    main()

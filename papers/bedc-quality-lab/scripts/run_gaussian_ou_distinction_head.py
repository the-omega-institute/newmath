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


def _fit_probe(
    x: np.ndarray,
    y: np.ndarray,
    *,
    steps: int = PROBE_STEPS,
    lr: float = PROBE_LR,
    l2: float = PROBE_L2,
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
        probs = _sigmoid(xs @ weights + bias)
        residual = probs - y
        weights -= float(lr) * ((xs.T @ residual) / n + float(l2) * weights)
        bias -= float(lr) * float(np.mean(residual))
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
    return {
        "bce": _bce(labels, pred["probabilities"]),
        "accuracy": float(np.mean(predictions == labels)),
        "margin": float(np.mean(signed)),
        "positive_rate": float(np.mean(labels)),
        "prediction_positive_rate": float(np.mean(predictions)),
    }


def _intervene(name: str, z: np.ndarray, z_pair: np.ndarray) -> np.ndarray:
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
    else:
        raise ValueError(f"unknown distinction: {name}")
    return intervened


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
    probes = {
        name: _fit_probe(z[train_idx], label[train_idx])
        for name, label in labels.items()
    }

    per_distinction: dict[str, Any] = {}
    for name in DISTINCTIONS:
        train_metrics = _classification_metrics(probes[name], z[train_idx], labels[name][train_idx])
        eval_metrics = _classification_metrics(probes[name], z[eval_idx], labels[name][eval_idx])
        stability = float(np.mean(labels[name] == pair_labels[name]))
        per_distinction[name] = {
            "truth": {
                "label_positive_rate_train": float(np.mean(labels[name][train_idx])),
                "label_positive_rate_eval": float(np.mean(labels[name][eval_idx])),
                "pair_label_positive_rate": float(np.mean(pair_labels[name])),
            },
            "train": train_metrics,
            "eval": eval_metrics,
            "stability": stability,
            "margin": float(eval_metrics["margin"]),
            "generalization_gap": float(train_metrics["accuracy"] - eval_metrics["accuracy"]),
        }

    intervention: dict[str, Any] = {}
    for target in DISTINCTIONS:
        z_changed = _intervene(target, z[eval_idx], z_pair[eval_idx])
        target_rows: dict[str, Any] = {}
        off_target_rates: list[float] = []
        for name in DISTINCTIONS:
            before = _predict_probe(probes[name], z[eval_idx])["predictions"]
            after = _predict_probe(probes[name], z_changed)["predictions"]
            truth_after = _label_truth(name, z_changed, high_energy_threshold=high_threshold)
            flip_rate = float(np.mean(before != after))
            accuracy_after = float(np.mean(after == truth_after))
            target_rows[name] = {
                "prediction_flip_rate": flip_rate,
                "post_intervention_truth_positive_rate": float(np.mean(truth_after)),
                "post_intervention_accuracy": accuracy_after,
            }
            if name != target:
                off_target_rates.append(flip_rate)
        intervention[target] = {
            "on_target_flip_rate": float(target_rows[target]["prediction_flip_rate"]),
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
        eval_accuracy = [
            float(record["per_distinction"][name]["eval"]["accuracy"]) for record in records
        ]
        eval_bce = [float(record["per_distinction"][name]["eval"]["bce"]) for record in records]
        stability = [float(record["per_distinction"][name]["stability"]) for record in records]
        margin = [float(record["per_distinction"][name]["margin"]) for record in records]
        gap = [
            float(record["per_distinction"][name]["generalization_gap"]) for record in records
        ]
        on_target = [
            float(record["intervention"][name]["on_target_flip_rate"]) for record in records
        ]
        off_target = [
            float(record["intervention"][name]["off_target_flip_rate"]) for record in records
        ]
        per_distinction[name] = {
            "eval_accuracy": metric_stats(eval_accuracy),
            "eval_bce": metric_stats(eval_bce),
            "stability": metric_stats(stability),
            "margin": metric_stats(margin),
            "generalization_gap": metric_stats(gap),
            "intervention_on_target_flip_rate": metric_stats(on_target),
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


def _payload(records: list[dict[str, Any]]) -> dict[str, Any]:
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
            "expected_record_count": SEED_COUNT,
        },
        "source_artifacts": _source_artifacts(),
        "applicability_boundary": _applicability_boundary(),
        "negative_result_note": _negative_result_note(),
        "records": records,
        "aggregate": _aggregate(records),
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
        f"- Total records: `{aggregate['record_count']}`",
        "",
        "## Per-Distinction Metrics",
        "",
        (
            "| distinction | eval accuracy | eval BCE | stability | margin | "
            "train/eval accuracy gap |"
        ),
        "| --- | ---: | ---: | ---: | ---: | ---: |",
    ]
    for name in DISTINCTIONS:
        stats = aggregate["per_distinction"][name]
        lines.append(
            "| "
            f"`{name}` | "
            f"{_render_stats(stats['eval_accuracy'])} | "
            f"{_render_stats(stats['eval_bce'])} | "
            f"{_render_stats(stats['stability'])} | "
            f"{_render_stats(stats['margin'])} | "
            f"{_render_stats(stats['generalization_gap'])} |"
        )
    lines.extend(
        [
            "",
            "## Intervention Metrics",
            "",
            "| target distinction | on-target flip rate | off-target flip rate | separation |",
            "| --- | ---: | ---: | ---: |",
        ]
    )
    for name in DISTINCTIONS:
        stats = aggregate["per_distinction"][name]
        lines.append(
            "| "
            f"`{name}` | "
            f"{_render_stats(stats['intervention_on_target_flip_rate'])} | "
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

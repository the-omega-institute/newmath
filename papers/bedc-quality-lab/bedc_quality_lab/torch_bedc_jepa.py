"""Gradient-trained BEDC-JEPA heads for the boundary-gated world."""

from __future__ import annotations

from dataclasses import dataclass
from collections.abc import Sequence
from typing import Any

import numpy as np

from bedc_quality_lab.bedc_jepa_metrics import (
    binary_accuracy,
    certified_coverage,
    false_claim_rate,
    gap_detection_auc,
    masked_binary_accuracy,
    unlogged_error_rate,
)
from bedc_quality_lab.bedc_jepa_world import BoundaryGatedBatch, make_boundary_gated_batch
from bedc_quality_lab.metrics import metric_bundle
from bedc_quality_lab.model import choose_device, covariance_loss, mean_loss, require_torch, set_deterministic_seed


@dataclass(frozen=True)
class TorchBedcJepaResult:
    summary: dict[str, object]


def _experiment_debt_score(
    *,
    unlogged_error: float,
    false_claim: float,
    gap_auc: float,
    certified: float,
) -> float:
    raw = 0.55 * unlogged_error + 0.20 * false_claim + 0.20 * (1.0 - gap_auc) + 0.05 * (1.0 - certified)
    return float(max(0.0, min(1.0, raw)))


def _ci95(values: Sequence[float]) -> float:
    if len(values) <= 1:
        return 0.0
    array = np.asarray(values, dtype=np.float64)
    return float(1.96 * np.std(array, ddof=1) / np.sqrt(array.shape[0]))


def _win_rate(values: Sequence[float], *, threshold: float = 0.0) -> float:
    if not values:
        return 0.0
    wins = sum(1 for value in values if float(value) > threshold)
    return float(wins / len(values))


def _make_mlp(torch: Any, in_dim: int, out_dim: int) -> Any:
    return torch.nn.Sequential(
        torch.nn.Linear(in_dim, 96),
        torch.nn.GELU(),
        torch.nn.Linear(96, 96),
        torch.nn.GELU(),
        torch.nn.Linear(96, out_dim),
    )


def _gap_features(torch: Any, z: Any, d_prob: Any) -> Any:
    radius = torch.sum(z * z, dim=1, keepdim=True)
    return torch.cat([z, radius, d_prob], dim=1)


def _distinction_features(torch: Any, z: Any) -> Any:
    radius = torch.sum(z * z, dim=1, keepdim=True)
    return torch.cat([z, radius], dim=1)


def _tensor(torch: Any, array: np.ndarray, *, device: str) -> Any:
    return torch.as_tensor(array, dtype=torch.float32, device=device)


def _train_variant(
    train: BoundaryGatedBatch,
    *,
    seed: int,
    bedc_objective: bool,
    epochs: int = 220,
) -> dict[str, Any]:
    torch = require_torch()
    set_deterministic_seed(seed)
    device = choose_device()
    encoder = _make_mlp(torch, train.x.shape[1], 2).to(device)
    predictor = _make_mlp(torch, 2, 2).to(device)
    distinction_head = _make_mlp(torch, 3, 1).to(device)
    gap_head = _make_mlp(torch, 4, 1).to(device)
    params = list(encoder.parameters()) + list(predictor.parameters())
    params.extend(distinction_head.parameters())
    params.extend(gap_head.parameters())
    optimizer = torch.optim.AdamW(params, lr=2e-3, weight_decay=1e-4)
    x = _tensor(torch, train.x, device=device)
    x_pair = _tensor(torch, train.x_pair, device=device)
    z_target = _tensor(torch, train.z, device=device)
    distinction = _tensor(torch, train.distinction.astype(np.float32)[:, None], device=device)
    gap = _tensor(torch, train.gap.astype(np.float32)[:, None], device=device)
    bce = torch.nn.BCEWithLogitsLoss()
    mse = torch.nn.MSELoss()
    pretrain_epochs = epochs
    bedc_epochs = 320 if bedc_objective else 0
    for _ in range(pretrain_epochs):
        optimizer.zero_grad(set_to_none=True)
        z = encoder(x)
        z_pair = encoder(x_pair).detach()
        pred_pair = predictor(z)
        latent_loss = mse(pred_pair, z_pair) + 0.25 * mse(z, z_target) + 0.15 * covariance_loss(z) + 0.05 * mean_loss(z)
        latent_loss.backward()
        optimizer.step()
    if bedc_objective:
        head_optimizer = torch.optim.AdamW(
            list(distinction_head.parameters()) + list(gap_head.parameters()),
            lr=2e-3,
            weight_decay=1e-4,
        )
        with torch.no_grad():
            z_fixed = encoder(x).detach()
    for _ in range(bedc_epochs):
        head_optimizer.zero_grad(set_to_none=True)
        z = z_fixed
        d_logits = distinction_head(_distinction_features(torch, z))
        d_prob = torch.sigmoid(d_logits)
        g_logits = gap_head(_gap_features(torch, z, d_prob))
        d_loss = bce(d_logits, distinction)
        g_loss = bce(g_logits, gap)
        wrong_soft = torch.abs(d_prob - distinction)
        gap_prob = torch.sigmoid(g_logits)
        unlogged_loss = torch.mean(wrong_soft * (1.0 - gap_prob) ** 2)
        boundary_caution = torch.mean(gap * (1.0 - gap_prob) ** 2)
        loss = 1.2 * d_loss + 1.8 * g_loss + 2.4 * unlogged_loss + 0.8 * boundary_caution
        loss.backward()
        head_optimizer.step()
    if not bedc_objective:
        for _ in range(80):
            optimizer.zero_grad(set_to_none=True)
            with torch.no_grad():
                z = encoder(x)
            d_logits = distinction_head(_distinction_features(torch, z.detach()))
            d_loss = bce(d_logits, distinction)
            d_loss.backward()
            optimizer.step()
    return {
        "encoder": encoder,
        "predictor": predictor,
        "distinction_head": distinction_head,
        "gap_head": gap_head,
        "device": device,
    }


def _scores(model: dict[str, Any], batch: BoundaryGatedBatch) -> dict[str, np.ndarray]:
    torch = require_torch()
    device = model["device"]
    x = _tensor(torch, batch.x, device=device)
    with torch.no_grad():
        z = model["encoder"](x)
        d_logits = model["distinction_head"](_distinction_features(torch, z))
        d_prob = torch.sigmoid(d_logits)
        g_prob = torch.sigmoid(model["gap_head"](_gap_features(torch, z, d_prob)))
    return {
        "latent": z.detach().cpu().numpy(),
        "distinction": d_prob.detach().cpu().numpy().reshape(-1),
        "gap": g_prob.detach().cpu().numpy().reshape(-1),
    }


def _evaluate(
    name: str,
    scores: dict[str, np.ndarray],
    test: BoundaryGatedBatch,
    *,
    gap_override: np.ndarray | None = None,
) -> dict[str, float | str]:
    outside_gap = ~test.gap
    gap_scores = scores["gap"] if gap_override is None else gap_override
    distinction_accuracy = binary_accuracy(scores["distinction"], test.distinction)
    outside_gap_accuracy = masked_binary_accuracy(scores["distinction"], test.distinction, outside_gap)
    false_claim = false_claim_rate(scores["distinction"], test.distinction, test.gap)
    gap_auc = gap_detection_auc(gap_scores, test.gap)
    unlogged_error = unlogged_error_rate(scores["distinction"], test.distinction, gap_scores)
    certified = certified_coverage(gap_scores)
    debt = _experiment_debt_score(
        unlogged_error=unlogged_error,
        false_claim=false_claim,
        gap_auc=gap_auc,
        certified=certified,
    )
    metrics = {
        "system_name": name,
        "distinction_accuracy": distinction_accuracy,
        "distinction_accuracy_outside_gap": outside_gap_accuracy,
        "gap_detection_auc": gap_auc,
        "false_claim_rate_inside_gap": false_claim,
        "unlogged_error_rate": unlogged_error,
        "certified_coverage": certified,
        "bedc_debt_score": debt,
    }
    metrics.update(metric_bundle(scores["latent"], test.z))
    return metrics


def run_torch_bedc_jepa_benchmark(*, seed: int = 4242) -> dict[str, object]:
    train = make_boundary_gated_batch(1536, rho=0.84, radius=1.0, gap_width=0.14, seed=seed)
    test = make_boundary_gated_batch(768, rho=0.84, radius=1.0, gap_width=0.14, seed=seed + 1)
    latent_model = _train_variant(train, seed=seed, bedc_objective=False)
    bedc_model = _train_variant(train, seed=seed, bedc_objective=True)
    latent_scores = _scores(latent_model, test)
    bedc_scores = _scores(bedc_model, test)
    systems = {
        "latent_only": _evaluate(
            "torch-latent-only",
            latent_scores,
            test,
            gap_override=np.zeros(test.gap.shape[0], dtype=np.float64),
        ),
        "bedc_objective": _evaluate("torch-bedc-jepa-objective", bedc_scores, test),
    }
    latent = systems["latent_only"]
    bedc = systems["bedc_objective"]
    return {
        "source": {
            "name": "boundary-gated-ou-world",
            "training": "torch-gradient",
            "seed": float(seed),
            "train_count": float(train.x.shape[0]),
            "test_count": float(test.x.shape[0]),
        },
        "objective_terms": [
            "latent_prediction",
            "distinction_bce",
            "gap_bce",
            "unlogged_error_penalty",
        ],
        "systems": systems,
        "deltas": {
            "gap_auc_gain": float(bedc["gap_detection_auc"]) - float(latent["gap_detection_auc"]),
            "unlogged_error_reduction": float(latent["unlogged_error_rate"]) - float(bedc["unlogged_error_rate"]),
            "debt_reduction": float(latent["bedc_debt_score"]) - float(bedc["bedc_debt_score"]),
            "outside_gap_accuracy_gain": float(bedc["distinction_accuracy_outside_gap"])
            - float(latent["distinction_accuracy_outside_gap"]),
            "latent_r2_delta": float(bedc["linear_identifiability_r2"]) - float(latent["linear_identifiability_r2"]),
        },
    }


def run_torch_bedc_jepa_sweep(*, seeds: Sequence[int] = (4242, 4259, 4276)) -> dict[str, object]:
    runs = [run_torch_bedc_jepa_benchmark(seed=int(seed)) for seed in seeds]
    gap_auc_gains = [float(run["deltas"]["gap_auc_gain"]) for run in runs]
    unlogged_reductions = [float(run["deltas"]["unlogged_error_reduction"]) for run in runs]
    debt_reductions = [float(run["deltas"]["debt_reduction"]) for run in runs]
    outside_gap_gains = [float(run["deltas"]["outside_gap_accuracy_gain"]) for run in runs]
    latent_r2_deltas = [float(run["deltas"]["latent_r2_delta"]) for run in runs]
    compact_runs = [
        {
            "seed": float(run["source"]["seed"]),
            "gap_auc_gain": float(run["deltas"]["gap_auc_gain"]),
            "unlogged_error_reduction": float(run["deltas"]["unlogged_error_reduction"]),
            "debt_reduction": float(run["deltas"]["debt_reduction"]),
            "outside_gap_accuracy_gain": float(run["deltas"]["outside_gap_accuracy_gain"]),
            "latent_r2_delta": float(run["deltas"]["latent_r2_delta"]),
        }
        for run in runs
    ]
    return {
        "seed_count": float(len(seeds)),
        "seeds": [float(seed) for seed in seeds],
        "runs": compact_runs,
        "gap_auc_gain_mean": float(np.mean(gap_auc_gains)),
        "gap_auc_gain_ci95": _ci95(gap_auc_gains),
        "unlogged_error_reduction_mean": float(np.mean(unlogged_reductions)),
        "unlogged_error_reduction_ci95": _ci95(unlogged_reductions),
        "debt_reduction_mean": float(np.mean(debt_reductions)),
        "debt_reduction_ci95": _ci95(debt_reductions),
        "outside_gap_accuracy_gain_mean": float(np.mean(outside_gap_gains)),
        "outside_gap_accuracy_gain_ci95": _ci95(outside_gap_gains),
        "latent_r2_delta_mean": float(np.mean(latent_r2_deltas)),
        "latent_r2_delta_abs_max": float(np.max(np.abs(np.asarray(latent_r2_deltas, dtype=np.float64)))),
        "gap_auc_win_rate": _win_rate(gap_auc_gains),
        "unlogged_error_win_rate": _win_rate(unlogged_reductions, threshold=-1e-12),
        "debt_win_rate": _win_rate(debt_reductions),
    }

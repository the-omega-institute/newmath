"""Gradient-trained BEDC-JEPA heads for the boundary-gated world."""

from __future__ import annotations

from dataclasses import asdict, dataclass
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


@dataclass(frozen=True)
class ActiveGapLedgerConfig:
    seed: int = 4242
    initial_train_count: int = 512
    pool_count: int = 1536
    test_count: int = 512
    active_budget: int = 192
    epochs: int = 80
    rho: float = 0.84
    radius: float = 1.0
    boundary_band_width: float = 0.14
    gap_auc_floor: float = 0.98
    gap_auc_min_delta: float = 0.0
    latent_r2_min_delta: float = 0.0
    unlogged_error_ceiling: float = 0.02
    coverage_min_delta: float = 0.0


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
    return _train_weighted_variant(
        train,
        seed=seed,
        epochs=epochs,
        weights=_variant_weights(bedc_objective=bedc_objective),
    )


def _variant_weights(*, bedc_objective: bool = True, remove: str | None = None) -> dict[str, float]:
    weights = {
        "distinction_bce": 1.2,
        "gap_bce": 1.8,
        "unlogged_error_penalty": 2.4,
        "boundary_caution": 0.8,
        "stability_consistency": 0.6,
        "intervention_bce": 0.9,
    }
    if not bedc_objective:
        return {
            "distinction_bce": 0.0,
            "gap_bce": 0.0,
            "unlogged_error_penalty": 0.0,
            "boundary_caution": 0.0,
        }
    if remove == "gap_bce":
        weights["gap_bce"] = 0.0
        weights["boundary_caution"] = 0.0
    elif remove == "unlogged_error_penalty":
        weights["unlogged_error_penalty"] = 0.0
    elif remove == "stability_consistency":
        weights["stability_consistency"] = 0.0
    elif remove == "intervention_bce":
        weights["intervention_bce"] = 0.0
    return weights


def _train_weighted_variant(
    train: BoundaryGatedBatch,
    *,
    seed: int,
    epochs: int = 220,
    weights: dict[str, float],
) -> dict[str, Any]:
    torch = require_torch()
    set_deterministic_seed(seed)
    device_resolution = choose_device()
    device = device_resolution.resolved_device
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
    distinction_pair = _tensor(torch, train.distinction_pair.astype(np.float32)[:, None], device=device)
    gap = _tensor(torch, train.gap.astype(np.float32)[:, None], device=device)
    gap_pair = _tensor(torch, train.gap_pair.astype(np.float32)[:, None], device=device)
    stability_mask_np = (
        (~train.gap)
        & (~train.gap_pair)
        & (train.distinction == train.distinction_pair)
    ).astype(np.float32)[:, None]
    stability_mask = _tensor(torch, stability_mask_np, device=device)
    bce = torch.nn.BCEWithLogitsLoss()
    mse = torch.nn.MSELoss()
    pretrain_epochs = epochs
    trains_bedc_heads = any(float(value) > 0.0 for value in weights.values())
    bedc_epochs = 320 if trains_bedc_heads else 0
    for _ in range(pretrain_epochs):
        optimizer.zero_grad(set_to_none=True)
        z = encoder(x)
        z_pair = encoder(x_pair).detach()
        pred_pair = predictor(z)
        latent_loss = mse(pred_pair, z_pair) + 0.25 * mse(z, z_target) + 0.15 * covariance_loss(z) + 0.05 * mean_loss(z)
        latent_loss.backward()
        optimizer.step()
    if trains_bedc_heads:
        head_optimizer = torch.optim.AdamW(
            list(distinction_head.parameters()) + list(gap_head.parameters()),
            lr=2e-3,
            weight_decay=1e-4,
        )
        with torch.no_grad():
            z_fixed = encoder(x).detach()
            z_pair_fixed = encoder(x_pair).detach()
            pred_pair_fixed = predictor(z_fixed).detach()
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
        d_pair_logits = distinction_head(_distinction_features(torch, z_pair_fixed))
        d_pair_prob = torch.sigmoid(d_pair_logits)
        d_pred_pair_logits = distinction_head(_distinction_features(torch, pred_pair_fixed))
        stability_numer = torch.sum(stability_mask * (d_prob - d_pair_prob) ** 2)
        stability_denom = torch.clamp(torch.sum(stability_mask), min=1.0)
        stability_loss = stability_numer / stability_denom
        intervention_loss = bce(d_pred_pair_logits, distinction_pair)
        loss = (
            float(weights["distinction_bce"]) * d_loss
            + float(weights["gap_bce"]) * g_loss
            + float(weights["unlogged_error_penalty"]) * unlogged_loss
            + float(weights["boundary_caution"]) * boundary_caution
            + float(weights["stability_consistency"]) * stability_loss
            + float(weights["intervention_bce"]) * intervention_loss
        )
        loss.backward()
        head_optimizer.step()
    if not trains_bedc_heads:
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


def _take_boundary_batch(batch: BoundaryGatedBatch, indices: np.ndarray) -> BoundaryGatedBatch:
    idx = np.asarray(indices, dtype=np.int64)
    return BoundaryGatedBatch(
        z=batch.z[idx],
        z_pair=batch.z_pair[idx],
        x=batch.x[idx],
        x_pair=batch.x_pair[idx],
        distinction=batch.distinction[idx],
        distinction_pair=batch.distinction_pair[idx],
        gap=batch.gap[idx],
        gap_pair=batch.gap_pair[idx],
        radius=batch.radius,
        gap_width=batch.gap_width,
    )


def _concat_boundary_batches(batches: Sequence[BoundaryGatedBatch]) -> BoundaryGatedBatch:
    if not batches:
        raise ValueError("at least one batch is required")
    first = batches[0]
    return BoundaryGatedBatch(
        z=np.concatenate([batch.z for batch in batches], axis=0),
        z_pair=np.concatenate([batch.z_pair for batch in batches], axis=0),
        x=np.concatenate([batch.x for batch in batches], axis=0),
        x_pair=np.concatenate([batch.x_pair for batch in batches], axis=0),
        distinction=np.concatenate([batch.distinction for batch in batches], axis=0),
        distinction_pair=np.concatenate([batch.distinction_pair for batch in batches], axis=0),
        gap=np.concatenate([batch.gap for batch in batches], axis=0),
        gap_pair=np.concatenate([batch.gap_pair for batch in batches], axis=0),
        radius=first.radius,
        gap_width=first.gap_width,
    )


def _metric_deltas(before: dict[str, Any], after: dict[str, Any]) -> dict[str, float]:
    keys = (
        "gap_detection_auc",
        "certified_coverage",
        "bedc_debt_score",
        "unlogged_error_rate",
        "linear_identifiability_r2",
        "distinction_accuracy_outside_gap",
    )
    return {key: float(after[key]) - float(before[key]) for key in keys}


def _choose_ranked_indices(candidates: np.ndarray, *, requested: int, selected: set[int]) -> list[int]:
    chosen: list[int] = []
    if requested <= 0:
        return chosen
    for raw in candidates:
        idx = int(raw)
        if idx in selected:
            continue
        selected.add(idx)
        chosen.append(idx)
        if len(chosen) >= requested:
            break
    return chosen


def _sampling_budgets(active_budget: int) -> dict[str, int]:
    if active_budget < 0:
        raise ValueError("active_budget must be non-negative")
    base = active_budget // 3
    return {
        "high_gap": active_budget - 2 * base,
        "boundary_band": base,
        "unlogged_transition": base,
    }


def _active_gap_ledger_sampling(
    pool: BoundaryGatedBatch,
    scores: dict[str, np.ndarray],
    *,
    active_budget: int,
) -> tuple[np.ndarray, dict[str, Any]]:
    budgets = _sampling_budgets(active_budget)
    gap_scores = np.asarray(scores["gap"], dtype=np.float64)
    distinction_scores = np.asarray(scores["distinction"], dtype=np.float64)
    errors = (distinction_scores >= 0.5) != pool.distinction
    candidates = {
        "high_gap": np.argsort(-gap_scores),
        "boundary_band": np.flatnonzero(pool.gap),
        "unlogged_transition": np.flatnonzero(errors & (gap_scores < 0.5)),
    }
    selected: set[int] = set()
    by_reason: dict[str, list[int]] = {}
    for reason in ("high_gap", "boundary_band", "unlogged_transition"):
        by_reason[reason] = _choose_ranked_indices(
            candidates[reason],
            requested=int(budgets[reason]),
            selected=selected,
        )
    selected_indices = np.asarray(
        [idx for reason in ("high_gap", "boundary_band", "unlogged_transition") for idx in by_reason[reason]],
        dtype=np.int64,
    )
    reason_rows = {
        reason: {
            "requested": int(budgets[reason]),
            "selected": int(len(by_reason[reason])),
            "candidate_count": int(np.asarray(candidates[reason]).shape[0]),
            "indices": [int(idx) for idx in by_reason[reason]],
        }
        for reason in ("high_gap", "boundary_band", "unlogged_transition")
    }
    return selected_indices, {
        "budget": int(active_budget),
        "selected": int(selected_indices.shape[0]),
        "selected_indices": [int(idx) for idx in selected_indices.tolist()],
        "reason_order": ["high_gap", "boundary_band", "unlogged_transition"],
        "reasons": reason_rows,
        "mutually_exclusive": bool(selected_indices.shape[0] == len(set(int(idx) for idx in selected_indices.tolist()))),
        "pool_count": int(pool.z.shape[0]),
    }


def _active_gap_guardrail(
    before: dict[str, Any],
    after: dict[str, Any],
    config: ActiveGapLedgerConfig,
) -> dict[str, Any]:
    deltas = _metric_deltas(before, after)
    checks = {
        "gap_auc_floor": float(after["gap_detection_auc"]) >= float(config.gap_auc_floor),
        "gap_auc_regression": float(deltas["gap_detection_auc"]) >= float(config.gap_auc_min_delta),
        "latent_r2_regression": float(deltas["linear_identifiability_r2"]) >= float(config.latent_r2_min_delta),
        "unlogged_error_ceiling": float(after["unlogged_error_rate"]) <= float(config.unlogged_error_ceiling),
        "coverage_gate": float(deltas["certified_coverage"]) >= float(config.coverage_min_delta),
    }
    failures = [name for name, passed in checks.items() if not passed]
    passed = not failures
    coverage_delta = float(deltas["certified_coverage"])
    coverage_expansion_reported = bool(passed and coverage_delta > 0.0)
    return {
        "passed": bool(passed),
        "checks": checks,
        "failures": failures,
        "coverage_expansion_reported": coverage_expansion_reported,
        "reported_coverage_delta": coverage_delta if coverage_expansion_reported else 0.0,
    }


def _summarize_rows(rows: list[dict[str, Any]]) -> dict[str, float]:
    if not rows:
        return {}
    keys = (
        "distinction_accuracy",
        "distinction_accuracy_outside_gap",
        "gap_detection_auc",
        "unlogged_error_rate",
        "certified_coverage",
        "bedc_debt_score",
        "linear_identifiability_r2",
    )
    return {
        f"{key}_mean": float(np.mean([float(row[key]) for row in rows]))
        for key in keys
    } | {
        f"{key}_ci95": _ci95([float(row[key]) for row in rows])
        for key in keys
    }


def run_torch_retraining_loss_ablation(
    *,
    seeds: Sequence[int] = (4242, 4259, 4276),
    train_count: int = 1536,
    test_count: int = 768,
    epochs: int = 220,
) -> dict[str, Any]:
    torch = require_torch()
    supervision_surface_contract = {
        "stability_consistency": {
            "source_surface": "OU transition pairs whose pre/post states keep the same outside-gap distinction",
            "fields": [
                "stability_source_split",
                "paired_observations_or_augmentations",
                "stability_label_or_invariance_target",
                "same_train_cal_test_split",
            ],
            "implemented_as": "mean squared distinction-probability change over outside-gap OU pairs with unchanged distinction label",
        },
        "intervention_bce": {
            "source_surface": "OU action/transition pair with post-transition operational distinction label",
            "fields": [
                "intervention_source_split",
                "pre_intervention_observation",
                "intervention_or_action",
                "post_intervention_label",
                "same_train_cal_test_split",
            ],
            "implemented_as": "binary cross-entropy on predicted-pair distinction logits against distinction_pair",
        },
    }
    systems = {
        "full_s3": {
            "objective_terms": [
                "latent_prediction",
                "distinction_bce",
                "gap_bce",
                "unlogged_error_penalty",
                "boundary_caution",
                "stability_consistency",
                "intervention_bce",
            ],
            "weights": _variant_weights(),
            "status": "executed",
            "supervision_surface_contract": supervision_surface_contract,
        },
        "minus_l_unlogged": {
            "objective_terms": [
                "latent_prediction",
                "distinction_bce",
                "gap_bce",
                "boundary_caution",
                "stability_consistency",
                "intervention_bce",
            ],
            "weights": _variant_weights(remove="unlogged_error_penalty"),
            "status": "executed",
            "supervision_surface_contract": supervision_surface_contract,
        },
        "minus_l_gap": {
            "objective_terms": [
                "latent_prediction",
                "distinction_bce",
                "unlogged_error_penalty",
                "stability_consistency",
                "intervention_bce",
            ],
            "weights": _variant_weights(remove="gap_bce"),
            "status": "executed",
            "supervision_surface_contract": supervision_surface_contract,
        },
        "minus_l_stab": {
            "objective_terms": [
                "latent_prediction",
                "distinction_bce",
                "gap_bce",
                "unlogged_error_penalty",
                "boundary_caution",
                "intervention_bce",
            ],
            "weights": _variant_weights(remove="stability_consistency"),
            "status": "executed",
            "removed_term": "stability_consistency",
            "supervision_surface_contract": supervision_surface_contract,
        },
        "minus_l_intervention": {
            "objective_terms": [
                "latent_prediction",
                "distinction_bce",
                "gap_bce",
                "unlogged_error_penalty",
                "boundary_caution",
                "stability_consistency",
            ],
            "weights": _variant_weights(remove="intervention_bce"),
            "status": "executed",
            "removed_term": "intervention_bce",
            "supervision_surface_contract": supervision_surface_contract,
        },
    }
    run_rows: list[dict[str, Any]] = []
    by_system: dict[str, list[dict[str, Any]]] = {name: [] for name in systems if systems[name]["status"] == "executed"}
    for seed in seeds:
        train = make_boundary_gated_batch(train_count, rho=0.84, radius=1.0, gap_width=0.14, seed=int(seed))
        test = make_boundary_gated_batch(test_count, rho=0.84, radius=1.0, gap_width=0.14, seed=int(seed) + 1)
        for name, spec in systems.items():
            if spec["status"] != "executed":
                continue
            model = _train_weighted_variant(
                train,
                seed=int(seed),
                epochs=epochs,
                weights=dict(spec["weights"]),
            )
            metrics = _evaluate(name, _scores(model, test), test)
            row = {"seed": float(seed), "system": name, **metrics}
            run_rows.append(row)
            by_system[name].append(row)
    summary = {name: _summarize_rows(rows) for name, rows in by_system.items()}
    full = summary.get("full_s3", {})
    comparisons = {}
    for name in ("minus_l_unlogged", "minus_l_gap", "minus_l_stab", "minus_l_intervention"):
        other = summary.get(name, {})
        if not full or not other:
            continue
        comparisons[f"full_s3_minus_{name}"] = {
            "gap_auc_gain": float(full["gap_detection_auc_mean"]) - float(other["gap_detection_auc_mean"]),
            "unlogged_error_reduction": float(other["unlogged_error_rate_mean"]) - float(full["unlogged_error_rate_mean"]),
            "debt_reduction": float(other["bedc_debt_score_mean"]) - float(full["bedc_debt_score_mean"]),
            "certified_coverage_delta": float(full["certified_coverage_mean"]) - float(other["certified_coverage_mean"]),
            "latent_r2_delta": float(full["linear_identifiability_r2_mean"]) - float(other["linear_identifiability_r2_mean"]),
        }
    return {
        "schema_id": "bedc-jepa-retraining-loss-ablation",
        "status": "executed",
        "source": {
            "name": "boundary-gated-ou-world",
            "training": "torch-gradient-retraining",
            "train_count": float(train_count),
            "test_count": float(test_count),
            "epochs": float(epochs),
        },
        "torch_environment": {
            "torch_version": str(getattr(torch, "__version__", "unknown")),
            "cuda_available": bool(torch.cuda.is_available()),
            "device": choose_device(),
            "cuda_device_name": str(torch.cuda.get_device_name(0)) if torch.cuda.is_available() else "",
        },
        "seeds": [float(seed) for seed in seeds],
        "systems": systems,
        "supervision_surface_contract": supervision_surface_contract,
        "runs": run_rows,
        "summary": summary,
        "comparisons": comparisons,
        "cannot_claim": [
            "public MiniGrid retraining ablation",
            "native V-JEPA2-AC retraining ablation",
            "natural-video stability ablation",
            "robot-control intervention ablation",
        ],
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


def run_active_gap_ledger_curriculum(
    config: ActiveGapLedgerConfig | None = None,
    **overrides: Any,
) -> dict[str, Any]:
    if config is None:
        config = ActiveGapLedgerConfig(**overrides)
    elif overrides:
        raise ValueError("pass either config or keyword overrides, not both")
    if config.initial_train_count <= 0:
        raise ValueError("initial_train_count must be positive")
    if config.pool_count <= 0:
        raise ValueError("pool_count must be positive")
    if config.test_count <= 0:
        raise ValueError("test_count must be positive")
    if config.active_budget <= 0:
        raise ValueError("active_budget must be positive")
    if config.epochs <= 0:
        raise ValueError("epochs must be positive")

    train = make_boundary_gated_batch(
        config.initial_train_count,
        rho=config.rho,
        radius=config.radius,
        gap_width=config.boundary_band_width,
        seed=config.seed,
    )
    pool = make_boundary_gated_batch(
        config.pool_count,
        rho=config.rho,
        radius=config.radius,
        gap_width=config.boundary_band_width,
        seed=config.seed + 100,
    )
    test = make_boundary_gated_batch(
        config.test_count,
        rho=config.rho,
        radius=config.radius,
        gap_width=config.boundary_band_width,
        seed=config.seed + 1,
    )
    initial_model = _train_weighted_variant(
        train,
        seed=config.seed,
        epochs=config.epochs,
        weights=_variant_weights(bedc_objective=True),
    )
    before = _evaluate("torch-active-gap-ledger-before", _scores(initial_model, test), test)
    pool_scores = _scores(initial_model, pool)
    selected_indices, sampling = _active_gap_ledger_sampling(
        pool,
        pool_scores,
        active_budget=config.active_budget,
    )
    selected_train = _take_boundary_batch(pool, selected_indices)
    retrain = _concat_boundary_batches([train, selected_train])
    retrained_model = _train_weighted_variant(
        retrain,
        seed=config.seed + 101,
        epochs=config.epochs,
        weights=_variant_weights(bedc_objective=True),
    )
    after = _evaluate("torch-active-gap-ledger-after", _scores(retrained_model, test), test)
    deltas = _metric_deltas(before, after)
    guardrail = _active_gap_guardrail(before, after, config)
    return {
        "schema_id": "bedc-jepa-active-gap-ledger-curriculum",
        "status": "executed" if guardrail["passed"] else "failed_guardrail",
        "source": {
            "name": "boundary-gated-ou-world",
            "training": "torch-active-gap-ledger-curriculum",
            "train_count_initial": float(config.initial_train_count),
            "train_count_after_active_sampling": float(retrain.z.shape[0]),
            "pool_count": float(config.pool_count),
            "test_count": float(config.test_count),
            "epochs": float(config.epochs),
            "seed": float(config.seed),
            "rho": float(config.rho),
            "radius": float(config.radius),
        },
        "thresholds": asdict(config),
        "sampling": sampling,
        "metrics_before": before,
        "metrics_after": after,
        "deltas": deltas,
        "guardrail": guardrail,
        "minigrid_active_curriculum": {
            "status": "not_executed",
            "cannot_claim": [
                "MiniGrid active retraining improvement",
                "MiniGrid invalid-transition reduction",
                "MiniGrid OOD or planner improvement",
            ],
            "evidence_boundary": "No executed MiniGrid active retraining path is present in this record.",
        },
        "cannot_claim": [
            "public MiniGrid active retraining",
            "native V-JEPA2-AC active retraining",
            "natural-video active curriculum",
            "robot-control active curriculum",
        ],
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

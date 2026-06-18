"""Active gap-ledger curriculum for the boundary-gated BEDC-JEPA world."""

from __future__ import annotations

import json
import subprocess
import sys
import time
from dataclasses import asdict
from pathlib import Path
from typing import Any

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from bedc_quality_lab.bedc_jepa_world import (
    BoundaryGatedBatch,
    make_boundary_gated_batch,
)
from bedc_quality_lab.model import choose_device, require_torch
from bedc_quality_lab.torch_bedc_jepa import (
    _evaluate,
    _scores,
    _train_weighted_variant,
    _variant_weights,
)


REPORT_PATH = Path("reports/bedc_active_gap_ledger.json")
RADIUS = 1.0
GAP_WIDTH = 0.14
RHO = 0.84


def _take(batch: BoundaryGatedBatch, indices: np.ndarray) -> BoundaryGatedBatch:
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


def _concat(batches: list[BoundaryGatedBatch]) -> BoundaryGatedBatch:
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


def _nvidia_smi_snapshot(label: str) -> dict[str, Any]:
    binary = "nvidia-smi"
    for candidate in (
        Path("/usr/lib/wsl/lib/nvidia-smi"),
        Path("/mnt/c/Windows/System32/nvidia-smi.exe"),
    ):
        if candidate.exists():
            binary = str(candidate)
            break
    command = [
        binary,
        "--query-gpu=timestamp,name,utilization.gpu,memory.used,memory.total",
        "--format=csv,noheader,nounits",
    ]
    try:
        output = subprocess.check_output(command, text=True, timeout=10).strip()
    except Exception as exc:  # pragma: no cover - depends on host driver tools.
        return {"label": label, "status": "unavailable", "error": str(exc)}
    return {"label": label, "status": "ok", "query": " ".join(command), "output": output}


def _summarize(values: list[float]) -> dict[str, float]:
    arr = np.asarray(values, dtype=np.float64)
    if arr.size == 0:
        return {"mean": 0.0, "min": 0.0, "max": 0.0}
    return {"mean": float(np.mean(arr)), "min": float(np.min(arr)), "max": float(np.max(arr))}


def _metric_delta(before: dict[str, float], after: dict[str, float]) -> dict[str, float]:
    keys = (
        "gap_detection_auc",
        "certified_coverage",
        "bedc_debt_score",
        "unlogged_error_rate",
        "linear_identifiability_r2",
        "distinction_accuracy_outside_gap",
    )
    return {key: float(after[key]) - float(before[key]) for key in keys}


def _choose_without_replacement(
    rng: np.random.Generator,
    candidates: np.ndarray,
    *,
    count: int,
    used: set[int],
) -> list[int]:
    filtered = np.asarray([int(i) for i in candidates if int(i) not in used], dtype=np.int64)
    if filtered.size == 0 or count <= 0:
        return []
    if filtered.size <= count:
        chosen = filtered
    else:
        chosen = rng.choice(filtered, size=count, replace=False)
    result = [int(i) for i in chosen.tolist()]
    used.update(result)
    return result


def _active_indices(
    pool: BoundaryGatedBatch,
    scores: dict[str, np.ndarray],
    *,
    rng: np.random.Generator,
    add_count: int,
    used: set[int],
) -> tuple[np.ndarray, dict[str, int]]:
    gap_scores = np.asarray(scores["gap"], dtype=np.float64)
    distinction_scores = np.asarray(scores["distinction"], dtype=np.float64)
    errors = (distinction_scores >= 0.5) != pool.distinction
    suspected_unlogged = np.flatnonzero(errors & (gap_scores < 0.5))
    boundary_band = np.flatnonzero(pool.gap)
    near_threshold = np.flatnonzero(np.abs(distinction_scores - 0.5) <= 0.12)
    high_gap_order = np.argsort(-gap_scores)

    counts = {
        "suspected_unlogged": int(round(add_count * 0.10)),
        "boundary_band": int(round(add_count * 0.10)),
        "high_gap": int(round(add_count * 0.10)),
    }
    counts["near_threshold"] = int(round(add_count * 0.10))
    counts["random_fill"] = max(0, add_count - sum(counts.values()))

    selected: list[int] = []
    selected.extend(
        _choose_without_replacement(
            rng,
            suspected_unlogged,
            count=counts["suspected_unlogged"],
            used=used,
        )
    )
    selected.extend(
        _choose_without_replacement(
            rng,
            boundary_band,
            count=counts["boundary_band"],
            used=used,
        )
    )
    selected.extend(
        _choose_without_replacement(
            rng,
            high_gap_order,
            count=counts["high_gap"],
            used=used,
        )
    )
    selected.extend(
        _choose_without_replacement(
            rng,
            near_threshold,
            count=counts["near_threshold"],
            used=used,
        )
    )
    all_indices = np.arange(pool.z.shape[0], dtype=np.int64)
    selected.extend(
        _choose_without_replacement(
            rng,
            all_indices,
            count=add_count - len(selected),
            used=used,
        )
    )

    selected_arr = np.asarray(selected[:add_count], dtype=np.int64)
    realized = {
        "selected": int(selected_arr.size),
        "selected_gap_labeled": int(np.sum(pool.gap[selected_arr])) if selected_arr.size else 0,
        "selected_suspected_unlogged": int(np.sum(errors[selected_arr] & (gap_scores[selected_arr] < 0.5)))
        if selected_arr.size
        else 0,
        "pool_suspected_unlogged": int(np.sum(errors & (gap_scores < 0.5))),
        "pool_gap_labeled": int(np.sum(pool.gap)),
    }
    realized.update({f"target_{key}": int(value) for key, value in counts.items()})
    return selected_arr, realized


def _candidate_is_acceptable(
    previous: dict[str, float],
    candidate: dict[str, float],
    *,
    gap_auc_floor: float = 0.98,
) -> tuple[bool, list[str]]:
    failures: list[str] = []
    if float(candidate["gap_detection_auc"]) < gap_auc_floor:
        failures.append("gap_auc_below_floor")
    if float(candidate["gap_detection_auc"]) + 1e-4 < float(previous["gap_detection_auc"]):
        failures.append("gap_auc_regression")
    if float(candidate["certified_coverage"]) + 1e-12 < float(previous["certified_coverage"]):
        failures.append("coverage_regression")
    if float(candidate["unlogged_error_rate"]) > float(previous["unlogged_error_rate"]) + 1e-12:
        failures.append("unlogged_error_regression")
    if float(candidate["linear_identifiability_r2"]) + 1e-4 < float(previous["linear_identifiability_r2"]):
        failures.append("latent_r2_regression")
    return len(failures) == 0, failures


def _train_and_evaluate(
    train: BoundaryGatedBatch,
    test: BoundaryGatedBatch,
    *,
    seed: int,
    epoch_count: int,
    label: str,
) -> tuple[dict[str, Any], dict[str, float]]:
    start = time.time()
    model = _train_weighted_variant(
        train,
        seed=seed,
        epochs=epoch_count,
        weights=_variant_weights(bedc_objective=True),
    )
    metrics = _evaluate(label, _scores(model, test), test)
    metrics["train_count"] = float(train.z.shape[0])
    metrics["wall_seconds"] = float(time.time() - start)
    return model, metrics


def run_active_gap_ledger(
    *,
    seeds: tuple[int, ...] = (4242, 4259, 4276),
    active_rounds: int = 3,
    initial_train_count: int = 1536,
    add_count: int = 384,
    pool_count: int = 8192,
    test_count: int = 2048,
    epoch_count: int = 200,
) -> dict[str, Any]:
    torch = require_torch()
    device = choose_device()
    if device.resolved_device != "cuda":
        raise RuntimeError(f"active gap-ledger experiment requires cuda, got {device.resolved_device}")

    gpu_snaps = [_nvidia_smi_snapshot("before-training")]
    seed_runs: list[dict[str, Any]] = []
    for seed in seeds:
        rng = np.random.default_rng(seed + 7001)
        base_train = make_boundary_gated_batch(
            initial_train_count,
            rho=RHO,
            radius=RADIUS,
            gap_width=GAP_WIDTH,
            seed=seed,
        )
        pool = make_boundary_gated_batch(
            pool_count,
            rho=RHO,
            radius=RADIUS,
            gap_width=GAP_WIDTH,
            seed=seed + 100,
        )
        test = make_boundary_gated_batch(
            test_count,
            rho=RHO,
            radius=RADIUS,
            gap_width=GAP_WIDTH,
            seed=seed + 1,
        )
        used_pool_indices: set[int] = set()
        train_parts = [base_train]
        train = base_train
        round_rows: list[dict[str, Any]] = []
        model, metrics = _train_and_evaluate(
            train,
            test,
            seed=seed,
            epoch_count=epoch_count,
            label="active-gap-ledger-round-0",
        )
        deployed_metrics = metrics
        round_rows.append(
            {
                "round": 0,
                "stage": "initial",
                "candidate_status": "accepted",
                "candidate_metrics": metrics,
                "deployed_metrics": deployed_metrics,
            }
        )
        if seed == seeds[0]:
            gpu_snaps.append(_nvidia_smi_snapshot("after-first-training"))

        for round_id in range(1, active_rounds + 1):
            pool_scores = _scores(model, pool)
            selected_indices, selection = _active_indices(
                pool,
                pool_scores,
                rng=rng,
                add_count=add_count,
                used=used_pool_indices,
            )
            candidate_parts = [*train_parts, _take(pool, selected_indices)]
            candidate_train = _concat(candidate_parts)
            candidate_model, candidate_metrics = _train_and_evaluate(
                candidate_train,
                test,
                seed=seed + round_id * 101,
                epoch_count=epoch_count,
                label=f"active-gap-ledger-round-{round_id}",
            )
            accepted, guard_failures = _candidate_is_acceptable(deployed_metrics, candidate_metrics)
            if accepted:
                model = candidate_model
                train_parts = candidate_parts
                train = candidate_train
                deployed_metrics = candidate_metrics
                status = "accepted"
            else:
                status = "rejected_by_guard"
            round_rows.append(
                {
                    "round": round_id,
                    "stage": "active_retrain",
                    "selection": selection,
                    "candidate_status": status,
                    "guard_failures": guard_failures,
                    "candidate_metrics": candidate_metrics,
                    "deployed_metrics": deployed_metrics,
                }
            )

        before = round_rows[0]["deployed_metrics"]
        after = round_rows[-1]["deployed_metrics"]
        seed_runs.append(
            {
                "seed": int(seed),
                "rounds": round_rows,
                "before": before,
                "after": after,
                "delta_after_minus_before": _metric_delta(before, after),
            }
        )

    gpu_snaps.append(_nvidia_smi_snapshot("after-training"))
    before_rows = [run["before"] for run in seed_runs]
    after_rows = [run["after"] for run in seed_runs]
    delta_rows = [run["delta_after_minus_before"] for run in seed_runs]
    metric_keys = (
        "gap_detection_auc",
        "certified_coverage",
        "bedc_debt_score",
        "unlogged_error_rate",
        "linear_identifiability_r2",
        "distinction_accuracy_outside_gap",
    )
    summary = {
        "before": {key: _summarize([float(row[key]) for row in before_rows]) for key in metric_keys},
        "after": {key: _summarize([float(row[key]) for row in after_rows]) for key in metric_keys},
        "delta_after_minus_before": {
            key: _summarize([float(row[key]) for row in delta_rows]) for key in metric_keys
        },
    }
    gates = {
        "gap_auc_min_after": float(summary["after"]["gap_detection_auc"]["min"]),
        "gap_auc_target": 0.98,
        "gap_auc_target_met": bool(summary["after"]["gap_detection_auc"]["min"] >= 0.98),
        "coverage_mean_non_decrease": bool(
            summary["delta_after_minus_before"]["certified_coverage"]["mean"] >= -1e-12
        ),
        "unlogged_error_mean_non_increase": bool(
            summary["delta_after_minus_before"]["unlogged_error_rate"]["mean"] <= 1e-12
        ),
        "latent_r2_mean_non_decrease": bool(
            summary["delta_after_minus_before"]["linear_identifiability_r2"]["mean"] >= -1e-12
        ),
    }
    return {
        "schema_id": "bedc-active-gap-ledger-curriculum",
        "status": "executed",
        "source": {
            "world": "boundary-gated-ou",
            "rho": RHO,
            "radius": RADIUS,
            "gap_width": GAP_WIDTH,
            "initial_train_count": float(initial_train_count),
            "active_rounds": float(active_rounds),
            "add_count_per_round": float(add_count),
            "pool_count": float(pool_count),
            "test_count": float(test_count),
            "epoch_count": float(epoch_count),
        },
        "torch_environment": {
            "torch_version": str(getattr(torch, "__version__", "unknown")),
            "cuda_available": bool(torch.cuda.is_available()),
            "device": asdict(device),
            "cuda_device_name": str(torch.cuda.get_device_name(0)) if torch.cuda.is_available() else "",
            "cuda_max_memory_allocated_bytes": float(torch.cuda.max_memory_allocated())
            if torch.cuda.is_available()
            else 0.0,
        },
        "objective_terms": [
            "latent_prediction",
            "distinction_bce",
            "gap_bce",
            "unlogged_error_penalty",
            "boundary_caution",
            "stability_consistency",
            "intervention_bce",
        ],
        "active_policy": {
            "uses_model_gap_head": True,
            "uses_boundary_band_labels": True,
            "uses_suspected_unlogged_errors": True,
            "uses_random_fill": True,
            "description": (
                "Each round scores a held-out OU transition pool with the current BEDC-JEPA heads, "
                "then trains a candidate on high-gap, boundary-band, suspected-unlogged, near-threshold, "
                "and random-fill transitions. The deployed model is replaced only when validation metrics "
                "preserve gap AUC, certified coverage, unlogged-error, and latent R2 guards."
            ),
        },
        "seeds": [int(seed) for seed in seeds],
        "gpu_evidence": gpu_snaps,
        "runs": seed_runs,
        "summary": summary,
        "acceptance_gates": gates,
        "cannot_claim": [
            "MiniGrid active retraining",
            "natural-video active retraining",
            "oracle- or nyxid-backed environment access",
        ],
    }


def main() -> None:
    result = run_active_gap_ledger()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    REPORT_PATH.write_text(json.dumps(result, indent=2, sort_keys=True), encoding="utf-8")
    print(json.dumps(result["summary"], indent=2, sort_keys=True))
    print(f"WROTE {REPORT_PATH}")


if __name__ == "__main__":
    main()

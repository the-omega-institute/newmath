"""Seed-strengthened MiniGrid BEDC-JEPA tournament.

This runner reuses the native MiniGrid training and evaluation code from
``bedc_minigrid_tournament.py`` and adds incremental reporting, seed-level
bootstrap intervals, paired deltas, and a Pareto tradeoff table.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import time
from typing import Any

import numpy as np

import bedc_minigrid_tournament as base


REPORT_PATH = Path("reports/bedc_minigrid_tournament_seeds.json")
DEFAULT_SEEDS = tuple(range(20260618, 20260638))
PRIMARY_ENDPOINTS = ("ood_success", "ood_gap_auc")
SUMMARY_METRICS: tuple[tuple[str, tuple[str, str]], ...] = (
    ("id_success", ("id", "success")),
    ("ood_success", ("ood", "success")),
    ("ood_gap_auc", ("ood", "gap_detection_auc")),
    ("invalid_transition_auc", ("ood", "invalid_transition_auc")),
    ("unlogged_error_rate", ("ood", "unlogged_error_rate")),
    ("certified_coverage", ("ood", "certified_coverage")),
    ("latent_r2", ("ood", "latent_r2")),
)
PARETO_METRICS = (
    "ood_success",
    "ood_gap_auc",
    "invalid_transition_auc",
    "unlogged_error_rate",
    "certified_coverage",
)
PARETO_DIRECTIONS = {
    "ood_success": "higher",
    "ood_gap_auc": "higher",
    "invalid_transition_auc": "higher",
    "unlogged_error_rate": "lower",
    "certified_coverage": "higher",
}


def _bootstrap_ci(values: list[float], *, iterations: int, seed: int) -> dict[str, Any]:
    arr = np.asarray(values, dtype=np.float64)
    if arr.size == 0:
        return {"mean": 0.0, "ci95_low": 0.0, "ci95_high": 0.0, "std": 0.0, "values": []}
    mean = float(np.mean(arr))
    std = float(np.std(arr, ddof=1)) if arr.size > 1 else 0.0
    if arr.size == 1:
        return {"mean": mean, "ci95_low": mean, "ci95_high": mean, "std": std, "values": arr.tolist()}
    rng = np.random.default_rng(seed)
    draws = rng.integers(0, arr.size, size=(int(iterations), arr.size))
    boot_means = np.mean(arr[draws], axis=1)
    return {
        "mean": mean,
        "ci95_low": float(np.percentile(boot_means, 2.5)),
        "ci95_high": float(np.percentile(boot_means, 97.5)),
        "std": std,
        "values": arr.tolist(),
    }


def _extract_values(seed_results: list[dict[str, Any]], arm: str, path: tuple[str, str]) -> list[float]:
    return [float(row["arms"][arm][path[0]][path[1]]) for row in seed_results]


def _summarize(seed_results: list[dict[str, Any]], *, bootstrap_iterations: int) -> dict[str, Any]:
    summary: dict[str, Any] = {}
    for arm_index, arm in enumerate(base.ARM_NAMES):
        arm_summary: dict[str, Any] = {}
        for metric_index, (key, path) in enumerate(SUMMARY_METRICS):
            values = _extract_values(seed_results, arm, path)
            arm_summary[key] = _bootstrap_ci(
                values,
                iterations=bootstrap_iterations,
                seed=91000 + arm_index * 100 + metric_index,
            )
        arm_summary["parameter_count"] = (
            int(seed_results[0]["arms"][arm]["training"]["parameter_count"]) if seed_results else 0
        )
        summary[arm] = arm_summary
    return summary


def _paired_delta(
    seed_results: list[dict[str, Any]],
    *,
    minuend: str,
    subtrahend: str,
    bootstrap_iterations: int,
    seed_offset: int,
) -> dict[str, Any]:
    rows: dict[str, Any] = {}
    for metric_index, (key, path) in enumerate(SUMMARY_METRICS):
        if key not in PRIMARY_ENDPOINTS and key not in {"unlogged_error_rate", "invalid_transition_auc", "certified_coverage"}:
            continue
        values = [
            float(row["arms"][minuend][path[0]][path[1]]) - float(row["arms"][subtrahend][path[0]][path[1]])
            for row in seed_results
        ]
        rows[key] = _bootstrap_ci(
            values,
            iterations=bootstrap_iterations,
            seed=92000 + seed_offset * 100 + metric_index,
        )
        rows[key]["paired_by_seed"] = True
        rows[key]["ci95_low_gt_zero"] = bool(rows[key]["ci95_low"] > 0.0)
    return rows


def _dominates(left: dict[str, float], right: dict[str, float]) -> bool:
    better_or_equal = True
    strictly_better = False
    for metric in PARETO_METRICS:
        direction = PARETO_DIRECTIONS[metric]
        if direction == "higher":
            if left[metric] < right[metric]:
                better_or_equal = False
            if left[metric] > right[metric]:
                strictly_better = True
        else:
            if left[metric] > right[metric]:
                better_or_equal = False
            if left[metric] < right[metric]:
                strictly_better = True
    return bool(better_or_equal and strictly_better)


def _pareto_table(summary: dict[str, Any]) -> dict[str, Any]:
    rows: dict[str, Any] = {}
    means: dict[str, dict[str, float]] = {
        arm: {metric: float(summary[arm][metric]["mean"]) for metric in PARETO_METRICS}
        for arm in base.ARM_NAMES
    }
    for arm in base.ARM_NAMES:
        dominated_by = [other for other in base.ARM_NAMES if other != arm and _dominates(means[other], means[arm])]
        dominates = [other for other in base.ARM_NAMES if other != arm and _dominates(means[arm], means[other])]
        rows[arm] = {
            **means[arm],
            "dominated": bool(dominated_by),
            "dominated_by": dominated_by,
            "dominates": dominates,
        }
    return {"metric_directions": PARETO_DIRECTIONS, "rows": rows}


def _base_payload(
    args: argparse.Namespace,
    *,
    torch: Any,
    device_resolution: Any,
    before: dict[str, Any],
    started_at: float,
    seed_results: list[dict[str, Any]],
    monitor_evidence: dict[str, Any] | None = None,
    after: dict[str, Any] | None = None,
    status: str = "running",
) -> dict[str, Any]:
    summary = _summarize(seed_results, bootstrap_iterations=args.bootstrap_iterations)
    payload = {
        "schema_id": "bedc-quality-lab:bedc-minigrid-tournament-seeds",
        "status": status,
        "primary_endpoints": list(PRIMARY_ENDPOINTS),
        "seed_count": len(seed_results),
        "requested_seed_count": len(args.seed_list),
        "run_contract": {
            "objective": "native MiniGrid external-validity tournament for BEDC-JEPA model ability",
            "train_environment": args.train_env,
            "ood_environment": args.ood_env,
            "heldout_layout_protocol": "train and ID test use disjoint seeds in train_environment; OOD uses ood_environment with disjoint seeds",
            "arms": list(base.ARM_NAMES),
            "planning_rule": "one-step candidate action selection by predicted distinction minus validation-selected lambda times predicted debt",
            "metric_source": "bedc_quality_lab.bedc_jepa_metrics plus MiniGrid native transition labels",
            "paired_delta_protocol": "bedc_jepa deltas are paired by seed against each control arm",
        },
        "config": {
            "seeds": list(args.seed_list),
            "completed_seeds": [int(row["seed"]) for row in seed_results],
            "train_count": int(args.train_count),
            "validation_count": int(args.validation_count),
            "test_count": int(args.test_count),
            "planning_count": int(args.planning_count),
            "epochs": int(args.epochs),
            "head_epochs": int(args.head_epochs),
            "hidden_dim": int(args.hidden_dim),
            "latent_dim": int(args.latent_dim),
            "requested_device": args.device,
            "bootstrap_iterations": int(args.bootstrap_iterations),
        },
        "dependency_status": base._dependency_status(torch),
        "device_resolution": device_resolution.to_dict(),
        "gpu_evidence": {
            "nvidia_smi_before": before,
            "nvidia_smi_monitor": monitor_evidence or {},
            "nvidia_smi_after": after or {},
            "torch_cuda_memory_allocated_max_bytes": int(torch.cuda.max_memory_allocated()) if torch.cuda.is_available() else 0,
        },
        "seed_results": seed_results,
        "summary": summary,
        "paired_deltas": {
            "bedc_jepa_minus_latent_only": _paired_delta(
                seed_results,
                minuend="bedc_jepa",
                subtrahend="latent_only",
                bootstrap_iterations=args.bootstrap_iterations,
                seed_offset=1,
            ),
            "bedc_jepa_minus_supervised_gap": _paired_delta(
                seed_results,
                minuend="bedc_jepa",
                subtrahend="supervised_gap",
                bootstrap_iterations=args.bootstrap_iterations,
                seed_offset=2,
            ),
        },
        "pareto_frontier": _pareto_table(summary),
        "cannot_claim": [
            "full MiniGrid episode solver",
            "MPC or multi-step learned planner",
            "public benchmark superiority",
            "official V-JEPA2-AC reproduction",
            "large-scale visual world-model conclusion",
            "formal neural-network proof",
        ],
        "elapsed_seconds": float(time.time() - started_at),
    }
    return payload


def _write_report(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def build_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser()
    parser.add_argument("--train-env", default=base.DEFAULT_TRAIN_ENV)
    parser.add_argument("--ood-env", default=base.DEFAULT_OOD_ENV)
    parser.add_argument("--seeds", default=",".join(str(seed) for seed in DEFAULT_SEEDS))
    parser.add_argument("--train-count", type=int, default=520)
    parser.add_argument("--validation-count", type=int, default=160)
    parser.add_argument("--test-count", type=int, default=220)
    parser.add_argument("--planning-count", type=int, default=48)
    parser.add_argument("--epochs", type=int, default=45)
    parser.add_argument("--head-epochs", type=int, default=24)
    parser.add_argument("--hidden-dim", type=int, default=80)
    parser.add_argument("--latent-dim", type=int, default=20)
    parser.add_argument("--bootstrap-iterations", type=int, default=6000)
    parser.add_argument("--device", default="cuda")
    parser.add_argument("--report", default=str(REPORT_PATH))
    return parser


def main() -> None:
    args = build_arg_parser().parse_args()
    args.seed_list = tuple(int(item.strip()) for item in str(args.seeds).split(",") if item.strip())
    torch = base.require_torch()
    device_resolution = base.choose_device(args.device)
    device = device_resolution.resolved_device
    report_path = Path(args.report)
    before = base._nvidia_snapshot()
    started_at = time.time()
    seed_results: list[dict[str, Any]] = []
    with base.NvidiaMonitor() as monitor:
        for index, seed in enumerate(args.seed_list, start=1):
            seed_results.append(base.run_seed(args, seed, device))
            if str(device).startswith("cuda"):
                torch.cuda.synchronize()
            partial_payload = _base_payload(
                args,
                torch=torch,
                device_resolution=device_resolution,
                before=before,
                started_at=started_at,
                seed_results=seed_results,
                status="running",
            )
            partial_payload["last_completed_seed_index"] = index
            _write_report(report_path, partial_payload)
            print(json.dumps({"completed_seed": int(seed), "seed_count": len(seed_results)}, sort_keys=True), flush=True)
        if str(device).startswith("cuda"):
            torch.cuda.synchronize()
        monitor_evidence = monitor.collect()
    after = base._nvidia_snapshot()
    payload = _base_payload(
        args,
        torch=torch,
        device_resolution=device_resolution,
        before=before,
        started_at=started_at,
        seed_results=seed_results,
        monitor_evidence=monitor_evidence,
        after=after,
        status="executed",
    )
    _write_report(report_path, payload)
    print(json.dumps({"report": str(report_path), "seed_count": len(seed_results), "device": device}, sort_keys=True))


if __name__ == "__main__":
    main()

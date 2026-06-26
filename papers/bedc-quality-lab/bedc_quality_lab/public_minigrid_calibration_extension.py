"""Seed, horizon-budget, and task-variant extension for public MiniGrid calibration."""

from __future__ import annotations

import json
from pathlib import Path
import traceback
from typing import Any

import numpy as np

from bedc_quality_lab.public_minigrid_debt_closure import build_public_minigrid_debt_closure_analysis
from bedc_quality_lab.public_minigrid_native_benchmark import DEFAULT_ENVIRONMENT_ID


DEFAULT_EXTENSION_SEEDS = (20260602, 20260603, 20260604, 20260605, 20260606)
DEFAULT_TASK_VARIANTS = (
    "MiniGrid-DoorKey-5x5-v0",
    "MiniGrid-DoorKey-6x6-v0",
    DEFAULT_ENVIRONMENT_ID,
    "MiniGrid-Unlock-v0",
    "MiniGrid-KeyCorridorS3R1-v0",
)
DEFAULT_PLANNING_STATE_COUNTS = (8, 16, 32)


def _mean(values: list[float]) -> float:
    return float(np.mean(np.asarray(values, dtype=np.float64))) if values else 0.0


def _win_rate(values: list[float]) -> float:
    arr = np.asarray(values, dtype=np.float64)
    return float(np.mean(arr > 0.0)) if arr.size else 0.0


def _task_family(environment_id: str) -> str:
    name = environment_id
    if name.startswith("MiniGrid-"):
        name = name[len("MiniGrid-") :]
    for separator in ("-", "_"):
        if separator in name:
            return name.split(separator, 1)[0]
    return name


def _extract_row(packet: dict[str, Any], *, seed: int, environment_id: str, planning_state_count: int) -> dict[str, Any]:
    base = {
        "seed": float(seed),
        "environment_id": environment_id,
        "task_family": _task_family(environment_id),
        "planning_state_count_requested": float(planning_state_count),
        "status": packet.get("status"),
    }
    if packet.get("status") != "executed":
        return {
            **base,
            "claim_status": "source_gap",
            "reason": packet.get("message") or packet.get("reason") or "public MiniGrid calibration extension row did not execute",
        }

    debt = packet["debt_decomposition"]
    s0 = debt["S0"]
    s3 = debt["S3"]
    interpretation = packet.get("interpretation", {})
    pareto = packet["risk_success_pareto"]
    best_low_gap = pareto.get("best_low_gap", {})
    baseline = pareto.get("baseline", {})
    silent_delta = float(s0["silent_debt"]) - float(s3["silent_debt"])
    total_debt_delta = float(s0["bedc_debt_score"]) - float(s3["bedc_debt_score"])
    coverage_delta = float(s0["coverage_debt"]) - float(s3["coverage_debt"])
    high_gap_delta = float(baseline.get("high_gap_state_rate", 0.0)) - float(best_low_gap.get("high_gap_state_rate", 0.0))
    success_delta = float(best_low_gap.get("effective_success_rate", 0.0)) - float(
        baseline.get("effective_success_rate", 0.0)
    )
    if silent_delta > 0.0 and high_gap_delta > 0.0:
        claim_status = "silent_debt_and_risk_direction"
    elif silent_delta > 0.0:
        claim_status = "silent_debt_direction"
    elif high_gap_delta > 0.0:
        claim_status = "risk_direction"
    else:
        claim_status = "no_directional_gain"
    return {
        **base,
        "claim_status": claim_status,
        "diagnosis": interpretation.get("diagnosis", ""),
        "silent_debt_delta_s0_minus_s3": silent_delta,
        "total_debt_delta_s0_minus_s3": total_debt_delta,
        "coverage_debt_delta_s0_minus_s3": coverage_delta,
        "best_low_gap_risk_budget": float(best_low_gap.get("risk_budget", 0.0)),
        "baseline_minus_best_low_gap_rate": high_gap_delta,
        "best_low_gap_success_delta_vs_baseline": success_delta,
        "frontier_claim_statuses": sorted(
            {str(row.get("claim_status")) for row in pareto.get("frontier_rows", []) if isinstance(row, dict)}
        ),
    }


def _summarize(rows: list[dict[str, Any]]) -> dict[str, Any]:
    executed = [row for row in rows if row.get("status") == "executed"]
    families = sorted({str(row.get("task_family") or "") for row in rows if row.get("task_family")})
    silent = [float(row["silent_debt_delta_s0_minus_s3"]) for row in executed]
    total = [float(row["total_debt_delta_s0_minus_s3"]) for row in executed]
    coverage = [float(row["coverage_debt_delta_s0_minus_s3"]) for row in executed]
    risk = [float(row["baseline_minus_best_low_gap_rate"]) for row in executed]
    success = [float(row["best_low_gap_success_delta_vs_baseline"]) for row in executed]
    return {
        "row_count": float(len(rows)),
        "executed_row_count": float(len(executed)),
        "source_gap_row_count": float(len(rows) - len(executed)),
        "task_family_count": float(len(families)),
        "task_families": families,
        "silent_debt_delta_mean": _mean(silent),
        "silent_debt_direction_win_rate": _win_rate(silent),
        "total_debt_delta_mean": _mean(total),
        "total_debt_direction_win_rate": _win_rate(total),
        "coverage_debt_delta_mean": _mean(coverage),
        "risk_reduction_mean": _mean(risk),
        "risk_reduction_win_rate": _win_rate(risk),
        "success_delta_at_best_low_gap_mean": _mean(success),
    }


def build_public_minigrid_calibration_extension(
    *,
    seeds: tuple[int, ...] = DEFAULT_EXTENSION_SEEDS,
    task_variants: tuple[str, ...] = DEFAULT_TASK_VARIANTS,
    planning_state_counts: tuple[int, ...] = DEFAULT_PLANNING_STATE_COUNTS,
    train_count: int = 48,
    test_count: int = 48,
) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    for environment_id in task_variants:
        for planning_count in planning_state_counts:
            for seed in seeds:
                try:
                    packet = build_public_minigrid_debt_closure_analysis(
                        environment_id=environment_id,
                        train_count=train_count,
                        test_count=test_count,
                        planning_state_count=planning_count,
                        seed=seed,
                    )
                except Exception as exc:  # pragma: no cover - environment registry dependent
                    packet = {
                        "status": "source_gap",
                        "exception_type": type(exc).__name__,
                        "message": str(exc),
                        "trace_tail": traceback.format_exc().splitlines()[-8:],
                    }
                rows.append(
                    _extract_row(
                        packet,
                        seed=seed,
                        environment_id=environment_id,
                        planning_state_count=planning_count,
                    )
                )
    summary = _summarize(rows)
    return {
        "schema_id": "bedc-jepa-public-minigrid-calibration-extension",
        "status": "executed" if summary["executed_row_count"] > 0.0 else "source_gap",
        "protocol": "public MiniGrid calibration and risk-success extension",
        "task_variants": list(task_variants),
        "seeds": [float(seed) for seed in seeds],
        "planning_state_counts": [float(count) for count in planning_state_counts],
        "train_count": float(train_count),
        "test_count": float(test_count),
        "row_claim_rule": (
            "Each row records directional silent-debt and risk-success evidence, or a source gap if the "
            "public environment cannot be executed under the declared protocol."
        ),
        "summary": summary,
        "rows": rows,
        "cannot_claim": [
            "public benchmark superiority",
            "closed total debt on all public MiniGrid tasks",
            "native V-JEPA2-AC benchmark reproduction",
            "robotics benchmark result",
            "natural-language grounding",
        ],
    }


def write_public_minigrid_calibration_extension(path: str | Path) -> dict[str, Any]:
    packet = build_public_minigrid_calibration_extension()
    target = Path(path)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return packet

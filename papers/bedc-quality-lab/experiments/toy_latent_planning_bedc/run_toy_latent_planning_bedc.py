#!/usr/bin/env python3
"""Run the toy latent planning BEDC owner-local experiment."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Any, Sequence

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.toy_latent_planning_bedc import (  # noqa: E402
    DEFAULT_RUN_ID,
    DEFAULT_SEEDS,
    build_payload,
    write_artifacts,
)
from scripts import run_gaussian_ou_dynamics_planning as planning  # noqa: E402


GENERATED_AT = "run-local:toy_latent_planning_bedc"


def _toy_record(source: dict[str, Any]) -> dict[str, Any]:
    metrics = source["metrics"]
    return {
        "seed": int(source["seed"]),
        "seed_index": int(source["seed_index"]),
        "arm": str(source["arm"]),
        "lambda_gap": float(source["lambda_gap"]),
        "safe_planning_success_rate": float(metrics["safe_planning_success"]),
        "unlogged_error_rate": float(metrics["UnloggedErrorRate"]),
        "collision_rate": float(metrics["collision_rate"]),
        "unsafe_state_rate": float(metrics["unsafe_state_rate"]),
        "mean_planning_regret": float(metrics["planning_regret"]),
        "prediction_error_mean": float(metrics["prediction_error"]),
        "gap_event_rate": float(source["start_state_audit_sample"][0]["gap_score"] >= 0.0),
        "source_projection": {
            "canonical_envelope_run_id": source["canonical_envelope_projection"]["run_id"],
            "train_count": source["config"]["train_count"],
            "eval_count": source["config"]["eval_count"],
            "start_count": source["config"]["eval_start_count"],
        },
    }


def collect_records(*, seeds: Sequence[int]) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    records: list[dict[str, Any]] = []
    for index, seed in enumerate(seeds):
        context = planning._seed_context(int(seed), index)
        models = planning._fit_arm_models(context)
        for row in planning._evaluate_seed(context, models):
            if float(row["lambda_gap"]) == float(planning.PRIMARY_LAMBDA):
                records.append(_toy_record(row))
    return records, {
        "dependency": "scripts/run_gaussian_ou_dynamics_planning.py",
        "primary_lambda": float(planning.PRIMARY_LAMBDA),
        "planner_horizon": int(planning.PLANNER_HORIZON),
        "action_count": len(planning.ACTION_SET),
        "source_seed_count": len(seeds),
    }


def build_projection(
    *,
    root: Path,
    run_id: str = DEFAULT_RUN_ID,
    generated_at: str = GENERATED_AT,
    seeds: Sequence[int] = DEFAULT_SEEDS,
) -> dict[str, Any]:
    records, source_summary = collect_records(seeds=seeds)
    config = {
        "run_id": run_id,
        "generated_at": generated_at,
        "seeds": [int(seed) for seed in seeds],
        "primary_lambda": float(planning.PRIMARY_LAMBDA),
        "lambda_grid": [float(value) for value in planning.LAMBDA_GRID],
        "arms": list(planning.ARM_ORDER),
        "use_torch": bool(planning.USE_TORCH),
        "fixed_seed_policy": "explicit-owner-local-seed-list",
    }
    return build_payload(
        records=records,
        root=root,
        generated_at=generated_at,
        run_id=run_id,
        config=config,
        source_summary=source_summary,
    )


def _parse_int_list(value: str) -> tuple[int, ...]:
    result = tuple(int(item.strip()) for item in value.split(",") if item.strip())
    if not result:
        raise argparse.ArgumentTypeError("at least one integer is required")
    return result


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--run-id", default=DEFAULT_RUN_ID)
    parser.add_argument("--generated-at", default=GENERATED_AT)
    parser.add_argument("--seeds", type=_parse_int_list, default=DEFAULT_SEEDS)
    args = parser.parse_args(argv)
    projection = build_projection(
        root=args.root,
        run_id=args.run_id,
        generated_at=args.generated_at,
        seeds=args.seeds,
    )
    write_artifacts(projection, root=args.root)
    summary = projection["summary_payload"]
    print(
        json.dumps(
            {
                "run_id": summary["run_id"],
                "claim_capsule": summary["run_artifacts"]["claim_capsule"],
                "summary": summary["run_artifacts"]["summary"],
                "result": summary["result"]["status"],
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Run the LeJEPA mini-grid backend evidence producer."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Any, Mapping, Sequence

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.lejepa_mini_grid import (
    DEFAULT_ALIGNMENT_LAMBDAS,
    DEFAULT_MIXINGS,
    DEFAULT_RHOS,
    DEFAULT_SEEDS,
    LeJEPAMiniGridProjection,
    default_grid,
)
from scripts import run_gaussian_ou_lejepa
from scripts.run_sigreg_gaussianity_reproduction import GuardThresholds, SlicedCFGaussianityProbe


DEFAULT_RUN_ID = "lejepa-mini-grid"
DEFAULT_SAMPLE_COUNT = 384
DEFAULT_DIRECTIONS = 16
DEFAULT_FREQUENCIES = (0.5, 1.0, 1.5, 2.0)
MIXING_ALIASES = {
    "spiral": "spiral",
    "parabolic": "parabolic_shear",
    "realnvp": "realnvp_coupling",
}


def _artifact_map(run_id: str) -> dict[str, str]:
    run_dir = f"reports/runs/{run_id}"
    return {
        "summary": f"{run_dir}/summary.json",
        "claim_capsule": f"{run_dir}/claim_capsule.json",
        "raw_metrics": f"{run_dir}/raw_metrics.jsonl",
        "report": f"{run_dir}/report.md",
    }


def _collapse_rate(envelope: Any) -> float:
    cov_trace = float(envelope.metrics.get("covariance_trace", 0.0))
    r2 = float(envelope.metrics.get("linear_identifiability_r2", 0.0))
    return float(max(0.0, min(1.0, (1.0 - min(1.0, max(0.0, r2))) + max(0.0, 0.25 - cov_trace) / 0.25)))


def run_single_arm(
    *,
    alignment_lambda: float,
    rho: float,
    mixing: str,
    seed: int,
    sample_count: int,
    directions: int,
    frequencies: Sequence[float],
    use_torch: bool,
) -> dict[str, Any]:
    source_mixing = MIXING_ALIASES.get(str(mixing), str(mixing))
    envelope = run_gaussian_ou_lejepa.run_experiment(
        use_torch=use_torch,
        sample_count=int(sample_count),
        seed=int(seed),
        rho=float(rho),
        mixing=source_mixing,
        alignment_lambda=float(alignment_lambda),
        run_id=f"lejepa-mini-grid-arm-{seed}",
        envelope_artifact="reports/runs/lejepa-mini-grid/arm-envelope.json",
        report_artifact="reports/runs/lejepa-mini-grid/arm-report.md",
    )
    probe = SlicedCFGaussianityProbe(
        directions=int(directions),
        frequencies=tuple(float(value) for value in frequencies),
        guard_thresholds=GuardThresholds(
            cov_to_identity_max=10.0,
            min_cov_eigenvalue_floor=1.0e-8,
            min_projected_variance_floor=1.0e-8,
        ),
    )
    base = np.asarray(
        [
            [float(envelope.metrics.get("linear_identifiability_r2", 0.0)), float(envelope.metrics.get("quality_q", 0.0))],
            [float(envelope.metrics.get("actual_recovery_mse", 0.0)), float(envelope.metrics.get("theorem3_bound_mse", 0.0))],
            [float(envelope.metrics.get("alignment_loss_mse", 0.0)), float(envelope.metrics.get("covariance_deviation", 0.0))],
        ],
        dtype=np.float64,
    )
    score = probe.score(base, seed=int(seed), directions=min(2, int(directions)), frequencies=tuple(float(value) for value in frequencies))
    return {
        "alignment_lambda": float(alignment_lambda),
        "rho": float(rho),
        "mixing": str(mixing),
        "source_mixing": source_mixing,
        "seed": int(seed),
        "sample_count": int(sample_count),
        "alignment_loss": float(envelope.metrics.get("alignment_loss_mse", 0.0)),
        "sigreg_sliced_cf": float(score["sigreg_penalty"]),
        "covariance_proxy": float(envelope.metrics.get("covariance_deviation", envelope.metrics.get("whitening_deviation_epsilon", 0.0))),
        "linear_identifiability_r2": float(envelope.metrics.get("linear_identifiability_r2", 0.0)),
        "actual_recovery_mse": float(envelope.metrics.get("actual_recovery_mse", 0.0)),
        "theorem3_bound_mse": float(envelope.metrics.get("theorem3_bound_mse", 0.0)),
        "collapse_rate": _collapse_rate(envelope),
        "quality_q": float(envelope.metrics.get("quality_q", 0.0)),
        "source_run_id": str(envelope.run_id),
    }


def collect_records(
    *,
    sample_count: int,
    directions: int,
    frequencies: Sequence[float],
    use_torch: bool,
    alignment_lambdas: Sequence[float] = DEFAULT_ALIGNMENT_LAMBDAS,
    rhos: Sequence[float] = DEFAULT_RHOS,
    mixings: Sequence[str] = DEFAULT_MIXINGS,
    seeds: Sequence[int] = DEFAULT_SEEDS,
) -> list[dict[str, Any]]:
    records = []
    grid = (
        default_grid()
        if tuple(float(value) for value in alignment_lambdas) == DEFAULT_ALIGNMENT_LAMBDAS
        and tuple(float(value) for value in rhos) == DEFAULT_RHOS
        and tuple(str(value) for value in mixings) == DEFAULT_MIXINGS
        and tuple(int(value) for value in seeds) == DEFAULT_SEEDS
        else tuple(
            {
                "alignment_lambda": float(alignment_lambda),
                "rho": float(rho),
                "mixing": str(mixing),
                "seed": int(seed),
            }
            for alignment_lambda in alignment_lambdas
            for rho in rhos
            for mixing in mixings
            for seed in seeds
        )
    )
    for cell in grid:
        records.append(
            run_single_arm(
                alignment_lambda=float(cell["alignment_lambda"]),
                rho=float(cell["rho"]),
                mixing=str(cell["mixing"]),
                seed=int(cell["seed"]),
                sample_count=int(sample_count),
                directions=int(directions),
                frequencies=frequencies,
                use_torch=bool(use_torch),
            )
        )
    return records


def build_projection(
    *,
    run_id: str = DEFAULT_RUN_ID,
    generated_at: str | None = None,
    sample_count: int = DEFAULT_SAMPLE_COUNT,
    directions: int = DEFAULT_DIRECTIONS,
    frequencies: Sequence[float] = DEFAULT_FREQUENCIES,
    use_torch: bool = False,
    alignment_lambdas: Sequence[float] = DEFAULT_ALIGNMENT_LAMBDAS,
    rhos: Sequence[float] = DEFAULT_RHOS,
    mixings: Sequence[str] = DEFAULT_MIXINGS,
    seeds: Sequence[int] = DEFAULT_SEEDS,
    full_lejepa_claim: bool = False,
) -> dict[str, Any]:
    timestamp = generated_at if generated_at is not None else f"run-local:{run_id}"
    records = collect_records(
        sample_count=sample_count,
        directions=directions,
        frequencies=frequencies,
        use_torch=use_torch,
        alignment_lambdas=alignment_lambdas,
        rhos=rhos,
        mixings=mixings,
        seeds=seeds,
    )
    artifacts = _artifact_map(run_id)
    config: Mapping[str, Any] = {
        "run_id": run_id,
        "sample_count": int(sample_count),
        "directions": int(directions),
        "frequencies": [float(value) for value in frequencies],
        "alignment_lambdas": [float(value) for value in alignment_lambdas],
        "rhos": [float(value) for value in rhos],
        "mixings": [str(value) for value in mixings],
        "seeds": [int(value) for value in seeds],
        "use_torch": bool(use_torch),
        "full_lejepa_claim": bool(full_lejepa_claim),
    }
    return LeJEPAMiniGridProjection(
        config=config,
        records=records,
        generated_at=timestamp,
        run_artifacts=artifacts,
    ).project()


def write_artifacts(projection: Mapping[str, Any], *, root: Path) -> None:
    summary = dict(projection["summary_payload"])
    artifacts = summary["run_artifacts"]
    paths = {
        "summary": root / artifacts["summary"],
        "claim_capsule": root / artifacts["claim_capsule"],
        "raw_metrics": root / artifacts["raw_metrics"],
        "report": root / artifacts["report"],
    }
    for path in paths.values():
        path.parent.mkdir(parents=True, exist_ok=True)
    paths["summary"].write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    paths["claim_capsule"].write_text(json.dumps(projection["claim_capsule_payload"], indent=2, sort_keys=True) + "\n", encoding="utf-8")
    paths["raw_metrics"].write_text(
        "".join(json.dumps(record, sort_keys=True) + "\n" for record in projection["raw_rows"]),
        encoding="utf-8",
    )
    paths["report"].write_text(str(projection["report_markdown"]), encoding="utf-8")


def _parse_float_list(value: str) -> tuple[float, ...]:
    result = tuple(float(item.strip()) for item in value.split(",") if item.strip())
    if not result:
        raise argparse.ArgumentTypeError("at least one float is required")
    return result


def _parse_int_list(value: str) -> tuple[int, ...]:
    result = tuple(int(item.strip()) for item in value.split(",") if item.strip())
    if not result:
        raise argparse.ArgumentTypeError("at least one integer is required")
    return result


def _parse_str_list(value: str) -> tuple[str, ...]:
    result = tuple(item.strip() for item in value.split(",") if item.strip())
    if not result:
        raise argparse.ArgumentTypeError("at least one string is required")
    return result


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--run-id", default=DEFAULT_RUN_ID)
    parser.add_argument("--generated-at", default=None)
    parser.add_argument("--sample-count", type=int, default=DEFAULT_SAMPLE_COUNT)
    parser.add_argument("--directions", type=int, default=DEFAULT_DIRECTIONS)
    parser.add_argument("--frequencies", type=_parse_float_list, default=DEFAULT_FREQUENCIES)
    parser.add_argument("--alignment-lambdas", type=_parse_float_list, default=DEFAULT_ALIGNMENT_LAMBDAS)
    parser.add_argument("--rhos", type=_parse_float_list, default=DEFAULT_RHOS)
    parser.add_argument("--mixings", type=_parse_str_list, default=DEFAULT_MIXINGS)
    parser.add_argument("--seeds", type=_parse_int_list, default=DEFAULT_SEEDS)
    parser.add_argument("--use-torch", action="store_true")
    parser.add_argument("--full-lejepa-claim", action="store_true")
    args = parser.parse_args(argv)
    projection = build_projection(
        run_id=args.run_id,
        generated_at=args.generated_at,
        sample_count=args.sample_count,
        directions=args.directions,
        frequencies=args.frequencies,
        use_torch=args.use_torch,
        alignment_lambdas=args.alignment_lambdas,
        rhos=args.rhos,
        mixings=args.mixings,
        seeds=args.seeds,
        full_lejepa_claim=args.full_lejepa_claim,
    )
    write_artifacts(projection, root=args.root)
    summary = projection["summary_payload"]
    print(
        json.dumps(
            {
                "run_id": summary["run_id"],
                "summary": summary["run_artifacts"]["summary"],
                "claim_capsule": summary["run_artifacts"]["claim_capsule"],
                "result": summary["result"]["status"],
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

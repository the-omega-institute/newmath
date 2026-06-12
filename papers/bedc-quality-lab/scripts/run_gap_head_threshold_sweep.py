#!/usr/bin/env python3
"""Run a threshold frontier sweep for the learned-h gap head."""

from __future__ import annotations

import argparse
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
import json
import math
from pathlib import Path
import sys
from typing import Any, Sequence

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.experiment_stats import metric_stats
from scripts import run_gap_ledger_head_on_h as producer


JSON_ARTIFACT = "reports/canonical/gap-head-threshold-frontier.json"
REPORT_ARTIFACT = "reports/canonical/gap-head-threshold-frontier.md"
ARTIFACT_ID = "bedc-quality-lab:gap-head-threshold-frontier"
THRESHOLDS = tuple(round(index / 20.0, 2) for index in range(1, 20))
METRIC_NAMES = (
    "AUROC",
    "UnloggedErrorRate",
    "LoggedFalseAlarmRate",
    "CriticalUnloggedErrorRate",
    "QualityQ",
    "NetInformation",
)
SMOKE_SAMPLE_COUNT = 96
SMOKE_SEED_COUNT = 3


@dataclass(frozen=True)
class ThresholdSweepConfig:
    sample_count: int
    seeds: tuple[int, ...]
    rho: float
    use_torch: bool
    thresholds: tuple[float, ...]
    json_artifact: str
    report_artifact: str
    run_id_prefix: str
    seed_grid_kind: str | None = None


@dataclass(frozen=True)
class ThresholdMetricRow:
    mean: float
    std: float
    n: int
    ci95_low: float
    ci95_high: float


@dataclass(frozen=True)
class ParetoAxisSpec:
    x: str = "AUROC"
    x_direction: str = "maximize"
    y: str = "CriticalLoggedCoverage"
    y_definition: str = "1 - CriticalUnloggedErrorRate"
    y_direction: str = "maximize"


@dataclass(frozen=True)
class HardgateCheck:
    status: str
    criterion: str
    reason: str


@dataclass(frozen=True)
class ThresholdSweepPayload:
    generated_at: str
    config: dict[str, Any]
    source_artifacts: dict[str, Any]
    applicability_boundary: dict[str, Any]
    threshold_curve: list[dict[str, Any]]
    threshold_summary: dict[str, Any]
    pareto_axis_spec: dict[str, Any]
    pareto_frontier: list[dict[str, Any]]
    hardgate: dict[str, Any]
    readiness: dict[str, Any]
    main_claim_status: str
    not_claimed: list[str]


def _active_config(*, smoke: bool = False) -> ThresholdSweepConfig:
    seeds = tuple(int(seed) for seed in producer._seeds())
    if smoke:
        seeds = seeds[:SMOKE_SEED_COUNT]
    return ThresholdSweepConfig(
        sample_count=SMOKE_SAMPLE_COUNT if smoke else producer.DEFAULT_CONFIG.sample_count,
        seeds=seeds,
        rho=producer.DEFAULT_CONFIG.rho,
        use_torch=producer.USE_TORCH,
        thresholds=THRESHOLDS,
        json_artifact=JSON_ARTIFACT,
        report_artifact=REPORT_ARTIFACT,
        run_id_prefix="gap-head-threshold-frontier-smoke" if smoke else "gap-head-threshold-frontier",
        seed_grid_kind="smoke" if smoke else producer.DEFAULT_CONFIG.seed_grid_kind,
    )


def _metric_cell(values: Sequence[float]) -> dict[str, Any]:
    stats = metric_stats(values)
    return asdict(
        ThresholdMetricRow(
            mean=float(stats["mean"]),
            std=float(stats["std"]),
            n=int(stats["n"]),
            ci95_low=float(stats["ci95_low"]),
            ci95_high=float(stats["ci95_high"]),
        )
    )


def _defined_cell(cell: dict[str, Any]) -> bool:
    return all(
        key in cell and isinstance(cell[key], (int, float)) and math.isfinite(float(cell[key]))
        for key in ("mean", "std", "n", "ci95_low", "ci95_high")
    )


def _score_auroc_result(error: np.ndarray, score: np.ndarray) -> dict[str, Any]:
    return producer._metrics_for_arm(
        arm="threshold_frontier_auroc",
        probabilities=np.column_stack([score, score, score, score]),
        labels=np.zeros((score.shape[0], len(producer.GAP_CHANNELS)), dtype=np.float64),
        prediction_error=error,
    )["failure_detection_auroc"]


def _score_auroc(error: np.ndarray, score: np.ndarray) -> float:
    return float(_score_auroc_result(error, score)["value"])


def _quality_q(surface: dict[str, Any]) -> float:
    metrics = surface["canonical_envelope_projection"]["metrics"]
    return float(metrics.get("quality_q", 0.0))


def _threshold_metrics_for_seed(
    *,
    threshold: float,
    probabilities: np.ndarray,
    eval_error: np.ndarray,
    quality_q: float,
) -> dict[str, float]:
    score = probabilities[:, producer.GAP_CHANNELS.index("prediction_error")]
    critical_score = np.max(probabilities, axis=1)
    errors = eval_error > producer.PRIMARY_EPSILON
    non_errors = ~errors
    unlogged = float(np.mean(errors & (score < float(threshold))))
    false_alarm = float(np.mean(non_errors & (score >= float(threshold))))
    critical_unlogged = float(np.mean(errors & (critical_score < float(threshold))))
    auroc = _score_auroc(eval_error, score)
    net_information = float(auroc + (1.0 - critical_unlogged) - false_alarm - unlogged)
    return {
        "AUROC": auroc,
        "UnloggedErrorRate": unlogged,
        "LoggedFalseAlarmRate": false_alarm,
        "CriticalUnloggedErrorRate": critical_unlogged,
        "QualityQ": float(quality_q),
        "NetInformation": net_information,
    }


def _run_record(*, seed: int, seed_index: int, config: ThresholdSweepConfig) -> dict[str, Any]:
    surface_config = producer.GapHeadRunConfig(
        sample_count=config.sample_count,
        seeds=(int(seed),),
        rho=config.rho,
        use_torch=config.use_torch,
        json_artifact=config.json_artifact,
        report_artifact=config.report_artifact,
        run_id_prefix=config.run_id_prefix,
        source_artifact_label="gap-head-threshold-frontier",
        seed_grid_kind=config.seed_grid_kind,
    )
    surface = producer._surface_for_seed(seed=int(seed), config=surface_config)
    train_idx = surface["train_idx"]
    eval_idx = surface["eval_idx"]
    heads = producer._fit_gap_head(surface["features"][train_idx], surface["gap_labels"][train_idx])
    probabilities = producer._predict_gap_head(heads, surface["features"][eval_idx])
    eval_error = surface["prediction_error"][eval_idx]
    score = probabilities[:, producer.GAP_CHANNELS.index("prediction_error")]
    auroc_result = _score_auroc_result(eval_error, score)
    vanilla_probabilities = np.zeros_like(probabilities, dtype=np.float64)
    quality_q = _quality_q(surface)
    by_threshold = {
        f"{threshold:.2f}": _threshold_metrics_for_seed(
            threshold=threshold,
            probabilities=probabilities,
            eval_error=eval_error,
            quality_q=quality_q,
        )
        for threshold in config.thresholds
    }
    vanilla_by_threshold = {
        f"{threshold:.2f}": _threshold_metrics_for_seed(
            threshold=threshold,
            probabilities=vanilla_probabilities,
            eval_error=eval_error,
            quality_q=quality_q,
        )
        for threshold in config.thresholds
    }
    return {
        "seed_index": int(seed_index),
        "seed_sequence_position": int(seed_index + 1),
        "seed": int(seed),
        "run_id": f"{config.run_id_prefix}-seed-{seed}",
        "representation_boundary": producer.REPRESENTATION_BOUNDARY,
        "inference_no_ground_truth_z": producer.INFERENCE_NO_GROUND_TRUTH_Z,
        "sample_count": int(config.sample_count),
        "threshold_metrics": by_threshold,
        "control_baseline_threshold_metrics": vanilla_by_threshold,
        "undefined_metric_reasons": (
            [
                {
                    "metric": "AUROC",
                    "reason": str(auroc_result.get("reason", "degenerate")),
                    "seed": int(seed),
                }
            ]
            if bool(auroc_result.get("degenerate", False))
            else []
        ),
    }


def _records(config: ThresholdSweepConfig) -> list[dict[str, Any]]:
    return [
        _run_record(seed=int(seed), seed_index=index, config=config)
        for index, seed in enumerate(config.seeds)
    ]


def _threshold_curve(records: list[dict[str, Any]], config: ThresholdSweepConfig) -> list[dict[str, Any]]:
    rows = []
    for threshold in config.thresholds:
        key = f"{threshold:.2f}"
        rows.append(
            {
                "threshold": float(threshold),
                "metrics": {
                    metric: _metric_cell(
                        [float(record["threshold_metrics"][key][metric]) for record in records]
                    )
                    for metric in METRIC_NAMES
                },
            }
        )
    return rows


def _control_baseline(records: list[dict[str, Any]], config: ThresholdSweepConfig) -> list[dict[str, Any]]:
    rows = []
    for threshold in config.thresholds:
        key = f"{threshold:.2f}"
        rows.append(
            {
                "threshold": float(threshold),
                "metrics": {
                    "CriticalUnloggedErrorRate": _metric_cell(
                        [
                            float(record["control_baseline_threshold_metrics"][key]["CriticalUnloggedErrorRate"])
                            for record in records
                        ]
                    )
                },
            }
        )
    return rows


def _critical_logged_coverage(row: dict[str, Any]) -> dict[str, Any]:
    critical = row["metrics"]["CriticalUnloggedErrorRate"]
    return {
        "mean": float(1.0 - critical["mean"]),
        "std": float(critical["std"]),
        "n": int(critical["n"]),
        "ci95_low": float(1.0 - critical["ci95_high"]),
        "ci95_high": float(1.0 - critical["ci95_low"]),
    }


def _dominates(a: dict[str, Any], b: dict[str, Any]) -> bool:
    a_x = float(a["metrics"]["AUROC"]["mean"])
    b_x = float(b["metrics"]["AUROC"]["mean"])
    a_y = float(_critical_logged_coverage(a)["mean"])
    b_y = float(_critical_logged_coverage(b)["mean"])
    return a_x >= b_x and a_y >= b_y and (a_x > b_x or a_y > b_y)


def _pareto_frontier(curve: list[dict[str, Any]]) -> list[dict[str, Any]]:
    frontier = []
    for row in curve:
        if not any(_dominates(other, row) for other in curve):
            frontier.append(
                {
                    "threshold": float(row["threshold"]),
                    "metrics": {
                        "AUROC": row["metrics"]["AUROC"],
                        "CriticalLoggedCoverage": _critical_logged_coverage(row),
                    },
                }
            )
    return frontier


def _positive_thresholds(curve: list[dict[str, Any]]) -> list[float]:
    return [
        float(row["threshold"])
        for row in curve
        if _defined_cell(row["metrics"]["AUROC"]) and float(row["metrics"]["AUROC"]["ci95_low"]) > 0.5
    ]


def _controlled_thresholds(
    curve: list[dict[str, Any]],
    control_baseline: list[dict[str, Any]],
) -> list[float]:
    controls = {
        float(row["threshold"]): float(row["metrics"]["CriticalUnloggedErrorRate"]["mean"])
        for row in control_baseline
    }
    thresholds = []
    for row in curve:
        threshold = float(row["threshold"])
        learned = float(row["metrics"]["CriticalUnloggedErrorRate"]["mean"])
        if learned <= controls[threshold]:
            thresholds.append(threshold)
    return thresholds


def _has_adjacent_run(thresholds: Sequence[float], *, length: int = 3) -> bool:
    values = sorted(float(value) for value in thresholds)
    if len(values) < length:
        return False
    run = 1
    for before, after in zip(values, values[1:], strict=False):
        if round(after - before, 2) == 0.05:
            run += 1
            if run >= length:
                return True
        else:
            run = 1
    return False


def _complete_curve(curve: list[dict[str, Any]], config: ThresholdSweepConfig) -> bool:
    expected = [float(threshold) for threshold in config.thresholds]
    actual = [float(row.get("threshold")) for row in curve]
    if actual != expected:
        return False
    for row in curve:
        metrics = row.get("metrics")
        if not isinstance(metrics, dict) or set(metrics) != set(METRIC_NAMES):
            return False
        for cell in metrics.values():
            if not isinstance(cell, dict) or set(cell) != {"mean", "std", "n", "ci95_low", "ci95_high"}:
                return False
            if not _defined_cell(cell):
                return False
    return True


def _hardgate(
    *,
    curve: list[dict[str, Any]],
    frontier: list[dict[str, Any]],
    config: ThresholdSweepConfig,
    positive_thresholds: list[float],
    controlled_thresholds: list[float],
    undefined_metric_reasons: Sequence[dict[str, Any]] = (),
) -> dict[str, Any]:
    invalid_reasons = []
    if len(config.seeds) < 2:
        invalid_reasons.append("at least two seeds are required for seed CI")
    if not _complete_curve(curve, config):
        invalid_reasons.append("threshold curve must contain all metric CI cells")
    for reason in undefined_metric_reasons:
        invalid_reasons.append(f"{reason.get('metric', 'metric')} undefined: {reason.get('reason', 'unknown')}")
    frontier_thresholds = [float(row["threshold"]) for row in frontier]
    frontier_source_rows = [row for row in curve if float(row["threshold"]) in set(frontier_thresholds)]
    t1_pass = bool(frontier) and not any(
        _dominates(a, b)
        for index, a in enumerate(frontier_source_rows)
        for b in frontier_source_rows[index + 1 :]
    ) and not any(
        _dominates(b, a)
        for index, a in enumerate(frontier_source_rows)
        for b in frontier_source_rows[index + 1 :]
    )
    t2_pass = _complete_curve(curve, config)
    single_positive = len(positive_thresholds) == 1
    d5_run_thresholds = sorted(set(positive_thresholds).intersection(controlled_thresholds))
    t4_pass = _has_adjacent_run(d5_run_thresholds, length=3)
    t3_pass = not (single_positive and t4_pass)
    checks = {
        "HG-GH-T1": asdict(
            HardgateCheck(
                status="pass" if t1_pass else "fail",
                criterion="frontier is nonempty and internally non-dominated",
                reason="ok" if t1_pass else "missing or dominated frontier",
            )
        ),
        "HG-GH-T2": asdict(
            HardgateCheck(
                status="pass" if t2_pass else "fail",
                criterion="all 19 thresholds from 0.05 through 0.95 have complete CI cells",
                reason="ok" if t2_pass else "incomplete threshold sensitivity curve",
            )
        ),
        "HG-GH-T3": asdict(
            HardgateCheck(
                status="pass" if t3_pass else "fail",
                criterion="a single positive threshold cannot be marked D5-ready",
                reason="single positive threshold blocks D5" if single_positive else "ok",
            )
        ),
        "HG-GH-T4": asdict(
            HardgateCheck(
                status="pass" if t4_pass else "fail",
                criterion=(
                    "D5-ready requires at least three adjacent thresholds with AUROC ci95_low "
                    "> 0.5 and controlled CriticalUnloggedErrorRate"
                ),
                reason="ok" if t4_pass else "no controlled adjacent positive threshold run",
            )
        ),
    }
    if invalid_reasons:
        status = "invalid"
    elif all(check["status"] == "pass" for check in checks.values()):
        status = "pass"
    else:
        status = "fail"
    return {
        "status": status,
        "reason": "; ".join(invalid_reasons) if invalid_reasons else "mechanical checks evaluated",
        "undefined_metric_reasons": list(undefined_metric_reasons),
        "checks": checks,
        "policy": {
            "positive_auroc_rule": "AUROC.ci95_low > 0.5",
            "critical_unlogged_control": "learned_mean_lte_vanilla_mean_same_threshold_protocol",
            "d5_adjacent_threshold_count": 3,
        },
    }


def _readiness(
    *,
    hardgate: dict[str, Any],
    positive_thresholds: list[float],
    controlled_thresholds: list[float],
) -> dict[str, Any]:
    d5_run = _has_adjacent_run(sorted(set(positive_thresholds).intersection(controlled_thresholds)), length=3)
    if hardgate["status"] == "invalid":
        status = "invalid"
    elif d5_run and hardgate["checks"]["HG-GH-T4"]["status"] == "pass":
        status = "D5-ready"
    elif positive_thresholds:
        status = "D4-at-threshold"
    else:
        status = "not-ready"
    return {
        "status": status,
        "positive_thresholds": [float(value) for value in positive_thresholds],
        "controlled_thresholds": [float(value) for value in controlled_thresholds],
        "basis": {
            "positive_rule": "$.hardgate.policy.positive_auroc_rule",
            "control_rule": "$.hardgate.policy.critical_unlogged_control",
        },
    }


def _source_artifacts(config: ThresholdSweepConfig) -> dict[str, Any]:
    return {
        "artifact_id": ARTIFACT_ID,
        "generation_script": "scripts/run_gap_head_threshold_sweep.py",
        "surface_owner": "scripts/run_gap_ledger_head_on_h.py::_surface_for_seed",
        "gap_head_fit": "scripts/run_gap_ledger_head_on_h.py::_fit_gap_head",
        "gap_head_predict": "scripts/run_gap_ledger_head_on_h.py::_predict_gap_head",
        "stats_helper": "scripts/experiment_stats.py::metric_stats",
        "json_artifact": config.json_artifact,
        "report_artifact": config.report_artifact,
    }


def _applicability_boundary(config: ThresholdSweepConfig) -> dict[str, Any]:
    return {
        "admitted_family": "Gaussian-OU toy world generated by the existing lab toy-world generator.",
        "representation_boundary": producer.REPRESENTATION_BOUNDARY,
        "inference_no_ground_truth_z": producer.INFERENCE_NO_GROUND_TRUTH_Z,
        "sample_count": int(config.sample_count),
        "seed_count": int(len(config.seeds)),
        "rho": float(config.rho),
        "threshold_grid": [float(threshold) for threshold in config.thresholds],
        "not_claimed": [
            "No global quality claim.",
            "No full LeJEPA claim.",
            "No full Tensor NameCert claim.",
            "No LLM behavior claim.",
            "No inference-time use of z, z_pair, gap_label, prediction_error, or eval_gap_labels.",
        ],
    }


def _threshold_summary(
    *,
    curve: list[dict[str, Any]],
    control_baseline: list[dict[str, Any]],
    positive_thresholds: list[float],
    controlled_thresholds: list[float],
) -> dict[str, Any]:
    best_auroc = max(curve, key=lambda row: float(row["metrics"]["AUROC"]["mean"]))
    best_net = max(curve, key=lambda row: float(row["metrics"]["NetInformation"]["mean"]))
    return {
        "best_auroc_threshold": float(best_auroc["threshold"]),
        "best_net_information_threshold": float(best_net["threshold"]),
        "positive_thresholds": [float(value) for value in positive_thresholds],
        "controlled_thresholds": [float(value) for value in controlled_thresholds],
        "control_baseline": control_baseline,
    }


def _payload(
    records: list[dict[str, Any]],
    config: ThresholdSweepConfig,
    *,
    generated_at: str | None = None,
) -> dict[str, Any]:
    curve = _threshold_curve(records, config)
    control_baseline = _control_baseline(records, config)
    frontier = _pareto_frontier(curve)
    positive = _positive_thresholds(curve)
    controlled = _controlled_thresholds(curve, control_baseline)
    undefined_metric_reasons = [
        reason
        for record in records
        for reason in record.get("undefined_metric_reasons", [])
    ]
    hardgate = _hardgate(
        curve=curve,
        frontier=frontier,
        config=config,
        positive_thresholds=positive,
        controlled_thresholds=controlled,
        undefined_metric_reasons=undefined_metric_reasons,
    )
    readiness = _readiness(
        hardgate=hardgate,
        positive_thresholds=positive,
        controlled_thresholds=controlled,
    )
    payload = ThresholdSweepPayload(
        generated_at=generated_at if generated_at is not None else datetime.now(timezone.utc).isoformat(),
        config={
            "sample_count": int(config.sample_count),
            "seed_count": int(len(config.seeds)),
            "seeds": [int(seed) for seed in config.seeds],
            "rho": float(config.rho),
            "use_torch": bool(config.use_torch),
            "thresholds": [float(threshold) for threshold in config.thresholds],
            "threshold_step": 0.05,
            "run_id_prefix": config.run_id_prefix,
            "seed_grid_kind": config.seed_grid_kind,
            "metric_names": list(METRIC_NAMES),
            "quality_q_source": "canonical_envelope_projection.metrics.quality_q",
            "net_information_definition": (
                "AUROC + CriticalLoggedCoverage - LoggedFalseAlarmRate - UnloggedErrorRate; "
                "display only, not a hardgate or Pareto axis"
            ),
        },
        source_artifacts=_source_artifacts(config),
        applicability_boundary=_applicability_boundary(config),
        threshold_curve=curve,
        threshold_summary=_threshold_summary(
            curve=curve,
            control_baseline=control_baseline,
            positive_thresholds=positive,
            controlled_thresholds=controlled,
        ),
        pareto_axis_spec=asdict(ParetoAxisSpec()),
        pareto_frontier=frontier,
        hardgate=hardgate,
        readiness=readiness,
        main_claim_status=readiness["status"],
        not_claimed=_applicability_boundary(config)["not_claimed"],
    )
    return asdict(payload)


def _format_float(value: float) -> str:
    if math.isnan(value):
        return "nan"
    return f"{value:.6f}"


def _render_cell(cell: dict[str, Any]) -> str:
    return (
        f"{_format_float(float(cell['mean']))} +/- {_format_float(float(cell['std']))} "
        f"(95% CI {_format_float(float(cell['ci95_low']))}, {_format_float(float(cell['ci95_high']))})"
    )


def _render_report(payload: dict[str, Any]) -> str:
    lines = [
        "# Gap-Head Threshold Frontier",
        "",
        f"- Generated at: `{payload['generated_at']}`",
        f"- Hardgate status: `{payload['hardgate']['status']}`",
        f"- Readiness: `{payload['readiness']['status']}`",
        f"- Sample count: `{payload['config']['sample_count']}`",
        f"- Seed count: `{payload['config']['seed_count']}`",
        "",
        "## Threshold Curve",
        "",
        (
            "| threshold | AUROC | UnloggedErrorRate | LoggedFalseAlarmRate | "
            "CriticalUnloggedErrorRate | QualityQ | NetInformation |"
        ),
        "| ---: | ---: | ---: | ---: | ---: | ---: | ---: |",
    ]
    for row in payload["threshold_curve"]:
        metrics = row["metrics"]
        lines.append(
            "| "
            f"{float(row['threshold']):.2f} | "
            f"{_render_cell(metrics['AUROC'])} | "
            f"{_render_cell(metrics['UnloggedErrorRate'])} | "
            f"{_render_cell(metrics['LoggedFalseAlarmRate'])} | "
            f"{_render_cell(metrics['CriticalUnloggedErrorRate'])} | "
            f"{_render_cell(metrics['QualityQ'])} | "
            f"{_render_cell(metrics['NetInformation'])} |"
        )
    lines.extend(
        [
            "",
            "## Pareto Frontier",
            "",
            "| threshold | AUROC | CriticalLoggedCoverage |",
            "| ---: | ---: | ---: |",
        ]
    )
    for row in payload["pareto_frontier"]:
        lines.append(
            "| "
            f"{float(row['threshold']):.2f} | "
            f"{_render_cell(row['metrics']['AUROC'])} | "
            f"{_render_cell(row['metrics']['CriticalLoggedCoverage'])} |"
        )
    lines.extend(
        [
            "",
            "## Hardgate",
            "",
            f"- `$.hardgate.status`: `{payload['hardgate']['status']}`",
            f"- Main claim status: `{payload['main_claim_status']}`",
            f"- Positive thresholds: `{', '.join(f'{value:.2f}' for value in payload['readiness']['positive_thresholds'])}`",
            f"- Controlled thresholds: `{', '.join(f'{value:.2f}' for value in payload['readiness']['controlled_thresholds'])}`",
            "",
            "| check | status | criterion | reason |",
            "| --- | --- | --- | --- |",
        ]
    )
    for name, check in payload["hardgate"]["checks"].items():
        lines.append(
            "| "
            f"`{name}` | `{check['status']}` | {check['criterion']} | {check['reason']} |"
        )
    lines.extend(["", "## Boundary", ""])
    for row in payload["not_claimed"]:
        lines.append(f"- {row}")
    lines.append("")
    return "\n".join(lines)


def _write_payload(payload: dict[str, Any], config: ThresholdSweepConfig) -> None:
    json_path = ROOT / config.json_artifact
    report_path = ROOT / config.report_artifact
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    report_path.write_text(_render_report(payload), encoding="utf-8")


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--smoke", action="store_true", help="Run a small seed and sample grid.")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> None:
    args = parse_args(()) if argv is None else parse_args(argv)
    config = _active_config(smoke=bool(args.smoke))
    records = _records(config)
    payload = _payload(records, config)
    _write_payload(payload, config)
    print(f"wrote {config.json_artifact}")
    print(f"wrote {config.report_artifact}")
    print(f"thresholds {len(payload['threshold_curve'])}")
    print(f"hardgate.status {payload['hardgate']['status']}")


if __name__ == "__main__":
    main(sys.argv[1:])

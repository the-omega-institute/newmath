#!/usr/bin/env python3
"""Run a rho identifiability dose-response experiment."""

from __future__ import annotations

from datetime import datetime, timezone
import json
import math
from pathlib import Path
import sys
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.experiment_stats import first_ci_overlap_saturation, fit_linear_slope, metric_stats
from scripts.run_gaussian_ou_lejepa import run_experiment
from scripts.run_sample_size_scaling import _child_seed


MASTER_SEED = 465021
SAMPLE_COUNT = 384
RHO_VALUES = (0.0, 0.25, 0.5, 0.75, 0.9)
SEED_COUNT = 15
USE_TORCH = True
TARGET_METRIC = "linear_identifiability_r2"
JSON_ARTIFACT = "reports/rho_identifiability_dose_response.json"
REPORT_ARTIFACT = "reports/rho_identifiability_dose_response.md"
METRIC_NAMES = (
    "linear_identifiability_r2",
    "approx_identifiability_proxy",
    "orthogonality_error",
    "covariance_deviation",
    "quality_benefit",
    "quality_cost",
    "quality_debt",
    "quality_q",
    "quality_threshold",
    "quality_margin",
)


def _rho_token(rho: float) -> str:
    return str(rho).replace(".", "p").replace("-", "m")


def _seeds(master_seed: int, count: int) -> list[int]:
    return [_child_seed(master_seed, index) for index in range(count)]


def _run_record(*, rho: float, seed: int, seed_index: int) -> dict[str, Any]:
    run_id = f"rho-identifiability-dose-response-rho-{_rho_token(rho)}-seed-{seed}"
    envelope = run_experiment(
        use_torch=USE_TORCH,
        sample_count=SAMPLE_COUNT,
        seed=seed,
        rho=rho,
        run_id=run_id,
        envelope_artifact=JSON_ARTIFACT,
        report_artifact=REPORT_ARTIFACT,
    )
    return {
        "sample_count": int(SAMPLE_COUNT),
        "rho": float(rho),
        "seed_index": int(seed_index),
        "seed": int(seed),
        "run_id": run_id,
        "classifier_name": envelope.classifier_spec.get("name"),
        "classifier_training": envelope.classifier_spec.get("training"),
        "metrics": {name: float(envelope.metrics[name]) for name in METRIC_NAMES},
        "envelope": envelope.to_dict(),
    }


def _records() -> list[dict[str, Any]]:
    seeds = _seeds(MASTER_SEED, SEED_COUNT)
    return [
        _run_record(rho=rho, seed=seed, seed_index=seed_index)
        for rho in RHO_VALUES
        for seed_index, seed in enumerate(seeds)
    ]


def _rho_key(rho: float) -> str:
    return f"rho_{_rho_token(rho)}"


def _aggregate(records: list[dict[str, Any]]) -> dict[str, Any]:
    by_rho: dict[str, Any] = {}
    for rho in RHO_VALUES:
        selected = [record for record in records if float(record["rho"]) == float(rho)]
        by_rho[_rho_key(rho)] = {
            "rho": float(rho),
            "sample_count": int(SAMPLE_COUNT),
            "record_count": len(selected),
            "seeds": [int(record["seed"]) for record in selected],
            "metrics": {
                name: metric_stats([float(record["metrics"][name]) for record in selected])
                for name in METRIC_NAMES
            },
        }
    return {"by_rho": by_rho}


def _target_points(aggregate: dict[str, Any]) -> list[dict[str, float]]:
    points: list[dict[str, float]] = []
    by_rho = aggregate["by_rho"]
    for rho in RHO_VALUES:
        stats = by_rho[_rho_key(rho)]["metrics"][TARGET_METRIC]
        points.append(
            {
                "rho": float(rho),
                "mean": float(stats["mean"]),
                "std": float(stats["std"]),
                "ci95_low": float(stats["ci95_low"]),
                "ci95_high": float(stats["ci95_high"]),
                "ci95_half_width": float(stats["ci95_half_width"]),
                "n": int(stats["n"]),
            }
        )
    return points


def _monotonicity_test(points: list[dict[str, float]]) -> dict[str, Any]:
    means = [float(point["mean"]) for point in points]
    finite = all(math.isfinite(mean) for mean in means)
    deltas = [later - earlier for earlier, later in zip(means, means[1:])]
    nondecreasing = bool(finite and all(delta >= 0.0 for delta in deltas))
    return {
        "hypothesis": "target metric mean is nondecreasing across the configured rho grid",
        "metric": TARGET_METRIC,
        "rho_values": [float(point["rho"]) for point in points],
        "means": means,
        "adjacent_deltas": deltas,
        "nondecreasing": nondecreasing,
        "pass": nondecreasing,
        "negative_result_note": (
            "The configured rho grid and seed count are fixed before observing the outcome."
        ),
    }


def _dose_response_fit(points: list[dict[str, float]]) -> dict[str, Any]:
    return {
        "metric": TARGET_METRIC,
        "fit": fit_linear_slope(points, "rho", "mean"),
    }


def _saturation_estimate(points: list[dict[str, float]]) -> dict[str, Any]:
    estimate = first_ci_overlap_saturation(points, "rho", "mean", "ci95_low", "ci95_high")
    estimate["method"] = "adjacent_ci_overlap_first_rho"
    estimate["metric"] = TARGET_METRIC
    estimate["grid_boundary"] = bool(
        estimate["saturated"] and estimate["saturation_index"] == len(points) - 1
    )
    return estimate


def _post_saturation_slope_ci(saturation_estimate: dict[str, Any]) -> dict[str, Any]:
    fit = saturation_estimate["post_saturation_fit"]
    contains_zero = bool(
        fit.get("status") == "ok"
        and float(fit["slope_ci95_low"]) <= 0.0
        and float(fit["slope_ci95_high"]) >= 0.0
    )
    return {
        "metric": TARGET_METRIC,
        "fit": fit,
        "contains_zero": contains_zero,
        "criterion_pass": contains_zero,
        "criterion": "post-saturation linear slope 95% CI contains zero",
    }


def _applicability_boundary() -> dict[str, Any]:
    return {
        "admitted_family": "Gaussian-OU toy world generated by the canonical runner.",
        "sample_count": SAMPLE_COUNT,
        "rho_values": list(RHO_VALUES),
        "seed_count": SEED_COUNT,
        "model": "Canonical tiny MLP encoder when available, with runner-managed fallback behavior.",
        "metric_behavior_range": (
            "Reported for finite target metric values returned by the canonical quality envelope; "
            "saturation fails closed when adjacent confidence intervals are non-finite or absent."
        ),
        "negative_result_policy": (
            "Non-monotone and unsaturated outcomes are reported directly without changing the rho grid."
        ),
    }


def _source_artifacts() -> dict[str, Any]:
    return {
        "generation_script": "scripts/run_rho_identifiability_dose_response.py",
        "canonical_runner": "scripts/run_gaussian_ou_lejepa.py::run_experiment",
        "shared_stats_helper": "scripts/experiment_stats.py",
        "import_dependency_chain": [
            "scripts/run_rho_identifiability_dose_response.py",
            "scripts.run_gaussian_ou_lejepa.run_experiment",
            "bedc_quality_lab.toy_world.make_toy_batch",
            "bedc_quality_lab.metrics.metric_bundle",
            "bedc_quality_lab.schema.QualityEvidenceEnvelope",
            "scripts.experiment_stats",
        ],
        "json_artifact": JSON_ARTIFACT,
        "report_artifact": REPORT_ARTIFACT,
    }


def _payload(records: list[dict[str, Any]]) -> dict[str, Any]:
    aggregate = _aggregate(records)
    points = _target_points(aggregate)
    saturation = _saturation_estimate(points)
    return {
        "artifact": JSON_ARTIFACT,
        "report": REPORT_ARTIFACT,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "config": {
            "master_seed": MASTER_SEED,
            "seed_count": SEED_COUNT,
            "seeds": _seeds(MASTER_SEED, SEED_COUNT),
            "sample_count": SAMPLE_COUNT,
            "rho_values": list(RHO_VALUES),
            "use_torch": USE_TORCH,
            "target_metric": TARGET_METRIC,
            "metric_names": list(METRIC_NAMES),
            "expected_record_count": len(RHO_VALUES) * SEED_COUNT,
        },
        "source_artifacts": _source_artifacts(),
        "records": records,
        "aggregate": aggregate,
        "target_metric_points": points,
        "monotonicity_test": _monotonicity_test(points),
        "dose_response_fit": _dose_response_fit(points),
        "saturation_estimate": saturation,
        "post_saturation_slope_ci": _post_saturation_slope_ci(saturation),
        "applicability_boundary": _applicability_boundary(),
    }


def _format_float(value: float) -> str:
    if math.isnan(value):
        return "nan"
    return f"{value:.6f}"


def _pass_label(value: bool) -> str:
    return "pass" if value else "fail"


def _render_report(payload: dict[str, Any]) -> str:
    monotonicity = payload["monotonicity_test"]
    dose_fit = payload["dose_response_fit"]["fit"]
    saturation = payload["saturation_estimate"]
    post = payload["post_saturation_slope_ci"]
    post_fit = post["fit"]
    lines = [
        "# Rho Identifiability Dose-Response Experiment",
        "",
        f"- Generated at: `{payload['generated_at']}`",
        f"- Canonical runner: `{payload['source_artifacts']['canonical_runner']}`",
        f"- Shared stats helper: `{payload['source_artifacts']['shared_stats_helper']}`",
        f"- Sample count: `{payload['config']['sample_count']}`",
        f"- Rho values: `{', '.join(str(rho) for rho in payload['config']['rho_values'])}`",
        f"- Seed count per rho: `{payload['config']['seed_count']}`",
        f"- Seeds: `{', '.join(str(seed) for seed in payload['config']['seeds'])}`",
        f"- Target metric: `{payload['config']['target_metric']}`",
        f"- Total records: `{len(payload['records'])}`",
        "",
        "## Per-Rho Confidence Intervals",
        "",
        "| rho | mean +/- std | 95% CI half-width | 95% CI | n |",
        "| ---: | ---: | ---: | ---: | ---: |",
    ]
    for point in payload["target_metric_points"]:
        lines.append(
            "| "
            f"{point['rho']} | "
            f"{_format_float(float(point['mean']))} +/- {_format_float(float(point['std']))} | "
            f"{_format_float(float(point['ci95_half_width']))} | "
            f"[{_format_float(float(point['ci95_low']))}, "
            f"{_format_float(float(point['ci95_high']))}] | {int(point['n'])} |"
        )

    lines.extend(
        [
            "",
            "## Monotonicity",
            "",
            f"- Hypothesis: {monotonicity['hypothesis']}.",
            f"- Result: `{_pass_label(bool(monotonicity['pass']))}`",
            (
                "- Adjacent deltas: "
                f"`{', '.join(_format_float(float(delta)) for delta in monotonicity['adjacent_deltas'])}`"
            ),
            f"- Negative result note: {monotonicity['negative_result_note']}",
            "",
            "## Dose-Response Fit",
            "",
            f"- Slope: `{_format_float(float(dose_fit['slope']))}`",
            (
                f"- Slope 95% CI: `[{_format_float(float(dose_fit['slope_ci95_low']))}, "
                f"{_format_float(float(dose_fit['slope_ci95_high']))}]`"
            ),
            f"- Status: `{dose_fit['status']}`",
            "",
            "## Saturation Estimate",
            "",
            f"- Method: `{saturation['method']}`",
            f"- Saturated: `{str(bool(saturation['saturated'])).lower()}`",
            f"- Saturation rho: `{_format_float(float(saturation['saturation_x']))}`",
            f"- Saturation index: `{saturation['saturation_index']}`",
            f"- Grid boundary: `{str(bool(saturation['grid_boundary'])).lower()}`",
            f"- Status: `{saturation['status']}`",
            "",
            "## Post-Saturation Slope",
            "",
            f"- Criterion: {post['criterion']}.",
            f"- Slope: `{_format_float(float(post_fit['slope']))}`",
            (
                f"- Slope 95% CI: `[{_format_float(float(post_fit['slope_ci95_low']))}, "
                f"{_format_float(float(post_fit['slope_ci95_high']))}]`"
            ),
            f"- Contains zero: `{str(bool(post['contains_zero'])).lower()}`",
            f"- Criterion result: `{_pass_label(bool(post['criterion_pass']))}`",
            f"- Status: `{post_fit['status']}`",
            "",
            "## Applicability Boundary",
            "",
            f"- Admitted family: {payload['applicability_boundary']['admitted_family']}",
            f"- Sample count: `{payload['applicability_boundary']['sample_count']}`",
            (
                "- Rho set: "
                f"`{', '.join(str(rho) for rho in payload['applicability_boundary']['rho_values'])}`."
            ),
            f"- Seed count: `{payload['applicability_boundary']['seed_count']}`",
            f"- Model: {payload['applicability_boundary']['model']}",
            f"- Metric behavior range: {payload['applicability_boundary']['metric_behavior_range']}",
            f"- Negative result policy: {payload['applicability_boundary']['negative_result_policy']}",
            "",
            "## Source Artifacts",
            "",
            f"- Generation script: `{payload['source_artifacts']['generation_script']}`",
            f"- JSON artifact: `{payload['source_artifacts']['json_artifact']}`",
            f"- Report artifact: `{payload['source_artifacts']['report_artifact']}`",
            "- Import dependency chain:",
        ]
    )
    for item in payload["source_artifacts"]["import_dependency_chain"]:
        lines.append(f"  - `{item}`")
    lines.extend(
        [
            "",
            "## Rho Seeds",
            "",
            "| rho | seeds |",
            "| ---: | --- |",
        ]
    )
    by_rho = payload["aggregate"]["by_rho"]
    for rho in payload["config"]["rho_values"]:
        seeds = by_rho[_rho_key(rho)]["seeds"]
        lines.append(f"| {rho} | `{', '.join(str(seed) for seed in seeds)}` |")
    lines.append("")
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

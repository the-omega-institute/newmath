#!/usr/bin/env python3
"""Run a multi-seed sample-count scaling experiment."""

from __future__ import annotations

from datetime import datetime, timezone
import json
import math
from pathlib import Path
import statistics
import sys
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.run_gaussian_ou_lejepa import run_experiment


MASTER_SEED = 445021
SEED_COUNT = 20
SAMPLE_COUNTS = (96, 192, 384, 768, 1536)
RHO = 0.82
USE_TORCH = True
SCALING_METRIC = "linear_identifiability_r2"
SLOPE_ACCEPTANCE_INTERVAL = (-0.8, -0.3)
JSON_ARTIFACT = "reports/sample_size_scaling.json"
REPORT_ARTIFACT = "reports/sample_size_scaling_report.md"
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


def _child_seed(master_seed: int, seed_index: int) -> int:
    value = (
        int(master_seed) * 1664525
        + 1013904223
        + int(seed_index) * 2246822519
        + int(seed_index) * int(seed_index) * 3266489917
    )
    return int(value % (2**32))


def _seeds(master_seed: int, count: int) -> list[int]:
    return [_child_seed(master_seed, index) for index in range(count)]


def _run_record(*, sample_count: int, seed: int, seed_index: int, rho: float) -> dict[str, Any]:
    run_id = f"sample-size-scaling-n{sample_count}-seed-{seed}"
    envelope = run_experiment(
        use_torch=USE_TORCH,
        sample_count=sample_count,
        seed=seed,
        rho=rho,
        run_id=run_id,
        envelope_artifact=JSON_ARTIFACT,
        report_artifact=REPORT_ARTIFACT,
    )
    return {
        "sample_count": int(sample_count),
        "seed_index": int(seed_index),
        "seed": int(seed),
        "rho": float(rho),
        "run_id": run_id,
        "classifier_name": envelope.classifier_spec.get("name"),
        "classifier_training": envelope.classifier_spec.get("training"),
        "metrics": {name: float(envelope.metrics[name]) for name in METRIC_NAMES},
        "envelope": envelope.to_dict(),
    }


def _records() -> list[dict[str, Any]]:
    seeds = _seeds(MASTER_SEED, SEED_COUNT)
    return [
        _run_record(sample_count=sample_count, seed=seed, seed_index=seed_index, rho=RHO)
        for sample_count in SAMPLE_COUNTS
        for seed_index, seed in enumerate(seeds)
    ]


def _sample_std(values: list[float]) -> float:
    if len(values) < 2:
        return 0.0
    return float(statistics.stdev(values))


def _metric_stats(values: list[float]) -> dict[str, float | int]:
    n = len(values)
    if n == 0:
        return {"n": 0, "mean": math.nan, "std": math.nan, "ci95_half_width": math.nan}
    mean = float(statistics.fmean(values))
    std = _sample_std(values)
    ci95 = 0.0 if n < 2 else float(1.96 * std / math.sqrt(n))
    return {"n": n, "mean": mean, "std": std, "ci95_half_width": ci95}


def _fit_log_log_slope(points: list[dict[str, float | int]]) -> dict[str, Any]:
    usable = [
        (math.log(float(point["sample_count"])), math.log(float(point["std"])))
        for point in points
        if float(point["std"]) > 0.0
    ]
    n = len(usable)
    if n < 3:
        return {
            "status": "insufficient_positive_std",
            "n": n,
            "slope": math.nan,
            "intercept": math.nan,
            "slope_ci95_low": math.nan,
            "slope_ci95_high": math.nan,
        }

    xs = [point[0] for point in usable]
    ys = [point[1] for point in usable]
    x_mean = statistics.fmean(xs)
    y_mean = statistics.fmean(ys)
    sxx = sum((x - x_mean) ** 2 for x in xs)
    slope = sum((x - x_mean) * (y - y_mean) for x, y in usable) / sxx
    intercept = y_mean - slope * x_mean
    residual_sse = sum((y - (intercept + slope * x)) ** 2 for x, y in usable)
    df = n - 2
    residual_var = residual_sse / df if df > 0 else 0.0
    slope_se = math.sqrt(residual_var / sxx) if sxx > 0.0 else math.nan
    t95_by_df = {1: 12.706, 2: 4.303, 3: 3.182, 4: 2.776, 5: 2.571}
    t95 = t95_by_df.get(df, 1.96)
    low = slope - t95 * slope_se
    high = slope + t95 * slope_se
    return {
        "status": "ok",
        "n": n,
        "slope": float(slope),
        "intercept": float(intercept),
        "slope_standard_error": float(slope_se),
        "slope_ci95_low": float(low),
        "slope_ci95_high": float(high),
    }


def _aggregate(records: list[dict[str, Any]]) -> dict[str, Any]:
    by_sample_count: dict[str, Any] = {}
    for sample_count in SAMPLE_COUNTS:
        selected = [record for record in records if int(record["sample_count"]) == sample_count]
        by_sample_count[str(sample_count)] = {
            "sample_count": sample_count,
            "record_count": len(selected),
            "seeds": [int(record["seed"]) for record in selected],
            "metrics": {
                name: _metric_stats([float(record["metrics"][name]) for record in selected])
                for name in METRIC_NAMES
            },
        }

    scaling_points = [
        {
            "sample_count": int(sample_count),
            "std": float(by_sample_count[str(sample_count)]["metrics"][SCALING_METRIC]["std"]),
        }
        for sample_count in SAMPLE_COUNTS
    ]
    std_values = [point["std"] for point in scaling_points]
    monotonic_nonincreasing = all(
        later <= earlier for earlier, later in zip(std_values, std_values[1:])
    )
    slope_fit = _fit_log_log_slope(scaling_points)
    slope = float(slope_fit["slope"])
    low, high = SLOPE_ACCEPTANCE_INTERVAL
    slope_in_interval = bool(slope_fit["status"] == "ok" and low <= slope <= high)

    return {
        "sample_counts": by_sample_count,
        "variance_scaling": {
            "metric": SCALING_METRIC,
            "std_by_sample_count": scaling_points,
            "monotonic_nonincreasing": monotonic_nonincreasing,
            "slope_acceptance_interval": list(SLOPE_ACCEPTANCE_INTERVAL),
            "slope_in_acceptance_interval": slope_in_interval,
            "prediction_pass": bool(monotonic_nonincreasing and slope_in_interval),
            "log_log_fit": slope_fit,
        },
    }


def _source_artifacts() -> dict[str, Any]:
    return {
        "generation_script": "scripts/run_sample_size_scaling.py",
        "canonical_runner": "scripts/run_gaussian_ou_lejepa.py::run_experiment",
        "import_dependency_chain": [
            "scripts/run_sample_size_scaling.py",
            "scripts/run_gaussian_ou_lejepa.py::run_experiment",
            "bedc_quality_lab.toy_world.make_toy_batch",
            "bedc_quality_lab.metrics.metric_bundle",
            "bedc_quality_lab.schema.QualityEvidenceEnvelope",
        ],
        "report_artifact": REPORT_ARTIFACT,
        "json_artifact": JSON_ARTIFACT,
    }


def _payload(records: list[dict[str, Any]]) -> dict[str, Any]:
    return {
        "artifact": JSON_ARTIFACT,
        "report": REPORT_ARTIFACT,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "config": {
            "master_seed": MASTER_SEED,
            "seed_count": SEED_COUNT,
            "seeds": _seeds(MASTER_SEED, SEED_COUNT),
            "sample_counts": list(SAMPLE_COUNTS),
            "rho": RHO,
            "use_torch": USE_TORCH,
            "metric_names": list(METRIC_NAMES),
            "scaling_metric": SCALING_METRIC,
            "slope_acceptance_interval": list(SLOPE_ACCEPTANCE_INTERVAL),
        },
        "source_artifacts": _source_artifacts(),
        "records": records,
        "aggregate": _aggregate(records),
    }


def _format_float(value: float) -> str:
    if math.isnan(value):
        return "nan"
    return f"{value:.6f}"


def _format_stat(row: dict[str, float | int]) -> str:
    pm = "\u00b1"
    return (
        f"{_format_float(float(row['mean']))} {pm} {_format_float(float(row['std']))} "
        f"(95% CI {pm} {_format_float(float(row['ci95_half_width']))}; n={int(row['n'])})"
    )


def _pass_label(value: bool) -> str:
    return "pass" if value else "fail"


def _render_report(payload: dict[str, Any]) -> str:
    aggregate = payload["aggregate"]
    scaling = aggregate["variance_scaling"]
    fit = scaling["log_log_fit"]
    lines = [
        "# Sample-Size Scaling Experiment",
        "",
        f"- Generated at: `{payload['generated_at']}`",
        f"- Canonical runner: `{payload['source_artifacts']['canonical_runner']}`",
        f"- Sample counts: `{', '.join(str(n) for n in payload['config']['sample_counts'])}`",
        f"- Seed count per sample count: `{payload['config']['seed_count']}`",
        f"- Seeds: `{', '.join(str(seed) for seed in payload['config']['seeds'])}`",
        f"- Rho: `{payload['config']['rho']}`",
        f"- Scaling metric: `{payload['config']['scaling_metric']}`",
        f"- Total records: `{len(payload['records'])}`",
        "",
        "## Metric Error Bars",
        "",
        "| sample_count | metric | mean \u00b1 std | 95% CI half-width | n |",
        "| ---: | --- | ---: | ---: | ---: |",
    ]
    for sample_count in payload["config"]["sample_counts"]:
        metrics = aggregate["sample_counts"][str(sample_count)]["metrics"]
        for metric_name in payload["config"]["metric_names"]:
            stats = metrics[metric_name]
            lines.append(
                "| "
                f"{sample_count} | `{metric_name}` | "
                f"{_format_float(float(stats['mean']))} \u00b1 {_format_float(float(stats['std']))} | "
                f"{_format_float(float(stats['ci95_half_width']))} | {int(stats['n'])} |"
            )
    lines.extend(
        [
            "",
            "## Identifiability Std By Sample Count",
            "",
            "| sample_count | std |",
            "| ---: | ---: |",
        ]
    )
    for point in scaling["std_by_sample_count"]:
        lines.append(f"| {point['sample_count']} | {_format_float(float(point['std']))} |")

    slope_text = _format_float(float(fit["slope"]))
    low_text = _format_float(float(fit["slope_ci95_low"]))
    high_text = _format_float(float(fit["slope_ci95_high"]))
    interval = scaling["slope_acceptance_interval"]
    lines.extend(
        [
            "",
            "## Variance Scaling Conclusion",
            "",
            (
                f"- Monotonic std result: "
                f"`{_pass_label(bool(scaling['monotonic_nonincreasing']))}`"
            ),
            (
                f"- Log-log slope: `{slope_text}` "
                f"(95% CI `{low_text}` to `{high_text}`)"
            ),
            f"- Accepted slope interval: `[{interval[0]}, {interval[1]}]`",
            (
                f"- Slope interval result: "
                f"`{_pass_label(bool(scaling['slope_in_acceptance_interval']))}`"
            ),
            f"- Prediction result: `{_pass_label(bool(scaling['prediction_pass']))}`",
            "",
            "## Applicability Boundary",
            "",
            "- Admitted family: Gaussian-OU toy world generated by the canonical runner.",
            "- Model: canonical tiny MLP encoder when available, with runner-managed fallback behavior.",
            f"- Sample count range: `{min(SAMPLE_COUNTS)}` to `{max(SAMPLE_COUNTS)}`.",
            f"- Rho: `{RHO}`.",
            (
                "- Metric behavior range: reported only for finite measured values returned by "
                "the canonical quality envelope."
            ),
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
            "## Seed Distribution",
            "",
            "| sample_count | seeds |",
            "| ---: | --- |",
        ]
    )
    for sample_count in payload["config"]["sample_counts"]:
        seeds = aggregate["sample_counts"][str(sample_count)]["seeds"]
        lines.append(f"| {sample_count} | `{', '.join(str(seed) for seed in seeds)}` |")
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


if __name__ == "__main__":
    main()

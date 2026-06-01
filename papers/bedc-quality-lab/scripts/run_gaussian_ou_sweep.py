#!/usr/bin/env python3
"""Run a multi-seed Gaussian-OU quality experiment."""

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


SEED_BASE = 430
SEED_COUNT = 20
RHO_VALUES = (0.3, 0.6, 0.82, 0.95)
ARMS = ("fallback", "torch")
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
REPORT_JSON = ROOT / "reports" / "gaussian_ou_sweep.json"
REPORT_MD = ROOT / "reports" / "gaussian_ou_sweep_report.md"
TORCH_CLASSIFIER = "tiny-mlp-2-128-128-2"


def _derive_seeds(base_seed: int, count: int) -> list[int]:
    return [int(base_seed + 1009 * index + 37 * index * index) for index in range(count)]


def _run_record(*, arm: str, seed: int, rho: float, sample_count: int) -> dict[str, Any]:
    use_torch = arm == "torch"
    run_id = f"gaussian-ou-lejepa-{arm}-seed-{seed}-rho-{str(rho).replace('.', 'p')}"
    envelope = run_experiment(
        use_torch=use_torch,
        sample_count=sample_count,
        seed=seed,
        rho=rho,
        run_id=run_id,
        envelope_artifact="reports/gaussian_ou_sweep.json",
        report_artifact="reports/gaussian_ou_sweep_report.md",
    )
    classifier_name = str(envelope.classifier_spec.get("name", ""))
    if use_torch and classifier_name != TORCH_CLASSIFIER:
        return {
            "arm": arm,
            "rho": rho,
            "seed": seed,
            "sample_count": sample_count,
            "status": "skipped",
            "skip_reason": "torch encoder unavailable; fallback result excluded from torch arm",
            "fallback_classifier_name": classifier_name,
        }
    return {
        "arm": arm,
        "rho": rho,
        "seed": seed,
        "sample_count": sample_count,
        "status": "ok",
        "classifier_name": classifier_name,
        "classifier_training": envelope.classifier_spec.get("training"),
        "metrics": {name: float(envelope.metrics[name]) for name in METRIC_NAMES},
        "envelope": envelope.to_dict(),
    }


def _sample_std(values: list[float]) -> float:
    if len(values) < 2:
        return 0.0
    return float(statistics.stdev(values))


def _metric_stats(values: list[float]) -> dict[str, float | int]:
    n = len(values)
    if n == 0:
        return {"n": 0, "mean": math.nan, "std": math.nan, "ci95": math.nan}
    mean = float(statistics.fmean(values))
    std = _sample_std(values)
    ci95 = 0.0 if n < 2 else float(1.96 * std / math.sqrt(n))
    return {"n": n, "mean": mean, "std": std, "ci95": ci95}


def _aggregate(records: list[dict[str, Any]]) -> dict[str, Any]:
    aggregates: dict[str, Any] = {}
    for rho in RHO_VALUES:
        rho_key = _rho_key(rho)
        aggregates[rho_key] = {}
        for arm in ARMS:
            selected = [
                record
                for record in records
                if record["status"] == "ok" and record["arm"] == arm and record["rho"] == rho
            ]
            skipped = [
                record
                for record in records
                if record["status"] == "skipped" and record["arm"] == arm and record["rho"] == rho
            ]
            metric_rows = {
                name: _metric_stats([float(record["metrics"][name]) for record in selected])
                for name in METRIC_NAMES
            }
            aggregates[rho_key][arm] = {
                "status": "ok" if selected else "skipped",
                "ok_count": len(selected),
                "skipped_count": len(skipped),
                "seeds": [int(record["seed"]) for record in selected],
                "skipped_seeds": [int(record["seed"]) for record in skipped],
                "metrics": metric_rows,
            }
    return aggregates


def _rho_key(rho: float) -> str:
    return f"rho_{str(rho).replace('.', 'p')}"


def _format_float(value: float) -> str:
    if math.isnan(value):
        return "nan"
    return f"{value:.6f}"


def _format_stat(row: dict[str, float | int]) -> str:
    pm = "\u00b1"
    return (
        f"{_format_float(float(row['mean']))} {pm} {_format_float(float(row['std']))} "
        f"(95% CI {pm} {_format_float(float(row['ci95']))}; n={int(row['n'])})"
    )


def _render_markdown(payload: dict[str, Any]) -> str:
    lines = [
        "# Gaussian-OU multi-seed quality experiment",
        "",
        f"- Generated at: `{payload['generated_at']}`",
        f"- Seed base: `{payload['config']['seed_base']}`",
        f"- Seed count: `{payload['config']['seed_count']}`",
        f"- Seeds: `{', '.join(str(seed) for seed in payload['config']['seeds'])}`",
        f"- Rho grid: `{', '.join(str(rho) for rho in payload['config']['rho_values'])}`",
        f"- Sample count: `{payload['config']['sample_count']}`",
        f"- Arms: `{', '.join(payload['config']['arms'])}`",
        "",
        "## Metric error bars",
        "",
    ]
    for rho in RHO_VALUES:
        rho_key = _rho_key(rho)
        lines.extend(
            [
                f"### rho={rho}",
                "",
                "| arm | metric | mean \u00b1 std | 95% CI half-width | n |",
                "| --- | --- | ---: | ---: | ---: |",
            ]
        )
        for arm in ARMS:
            aggregate = payload["aggregates"][rho_key][arm]
            for metric_name in METRIC_NAMES:
                stats = aggregate["metrics"][metric_name]
                lines.append(
                    "| "
                    f"{arm} | `{metric_name}` | "
                    f"{_format_float(float(stats['mean']))} \u00b1 {_format_float(float(stats['std']))} | "
                    f"{_format_float(float(stats['ci95']))} | {int(stats['n'])} |"
                )
        lines.append("")
    lines.extend(["## Encoder contrast", ""])
    lines.append("| rho | metric | fallback mean \u00b1 std | torch mean \u00b1 std | torch status |")
    lines.append("| --- | --- | ---: | ---: | --- |")
    for rho in RHO_VALUES:
        rho_key = _rho_key(rho)
        fallback = payload["aggregates"][rho_key]["fallback"]
        torch = payload["aggregates"][rho_key]["torch"]
        torch_status = "ok" if torch["ok_count"] else "skipped"
        for metric_name in (
            "linear_identifiability_r2",
            "approx_identifiability_proxy",
            "orthogonality_error",
            "covariance_deviation",
            "quality_q",
            "quality_debt",
        ):
            lines.append(
                "| "
                f"{rho} | `{metric_name}` | {_format_stat(fallback['metrics'][metric_name])} | "
                f"{_format_stat(torch['metrics'][metric_name])} | {torch_status} |"
            )
    lines.extend(["", "## Seed distribution", ""])
    lines.append("| rho | arm | status | seeds |")
    lines.append("| --- | --- | --- | --- |")
    for rho in RHO_VALUES:
        rho_key = _rho_key(rho)
        for arm in ARMS:
            aggregate = payload["aggregates"][rho_key][arm]
            seeds = aggregate["seeds"] if aggregate["ok_count"] else aggregate["skipped_seeds"]
            status = "ok" if aggregate["ok_count"] else "skipped"
            lines.append(f"| {rho} | {arm} | {status} | `{', '.join(str(seed) for seed in seeds)}` |")
    skipped = [record for record in payload["records"] if record["status"] == "skipped"]
    if skipped:
        lines.extend(["", "## Skipped records", ""])
        lines.append("| rho | arm | seed | reason |")
        lines.append("| --- | --- | ---: | --- |")
        for record in skipped:
            lines.append(
                f"| {record['rho']} | {record['arm']} | {record['seed']} | {record['skip_reason']} |"
            )
    lines.append("")
    return "\n".join(lines)


def _write_payload(payload: dict[str, Any]) -> None:
    REPORT_JSON.parent.mkdir(parents=True, exist_ok=True)
    REPORT_JSON.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    REPORT_MD.write_text(_render_markdown(payload), encoding="utf-8")


def main() -> None:
    seeds = _derive_seeds(SEED_BASE, SEED_COUNT)
    sample_count = 384
    records = [
        _run_record(arm=arm, seed=seed, rho=rho, sample_count=sample_count)
        for rho in RHO_VALUES
        for seed in seeds
        for arm in ARMS
    ]
    payload = {
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "config": {
            "seed_base": SEED_BASE,
            "seed_count": SEED_COUNT,
            "seeds": seeds,
            "rho_values": list(RHO_VALUES),
            "arms": list(ARMS),
            "sample_count": sample_count,
            "metric_names": list(METRIC_NAMES),
        },
        "records": records,
        "aggregates": _aggregate(records),
    }
    _write_payload(payload)
    print(f"wrote {REPORT_JSON.relative_to(ROOT)}")
    print(f"wrote {REPORT_MD.relative_to(ROOT)}")


if __name__ == "__main__":
    main()

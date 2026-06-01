#!/usr/bin/env python3
"""Run the hidden-debt dose response experiment."""

from __future__ import annotations

from dataclasses import dataclass
import json
import math
from pathlib import Path
import sys
from typing import Any, Iterable

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.debt import assess_debt, format_debt_items
from bedc_quality_lab.ledger import derive_ledger_gaps, format_ledger_gaps
from bedc_quality_lab.metrics import classifier_certificate, metric_bundle, quality_components
from bedc_quality_lab.scope import Scope, scope_rows

MASTER_SEED = 44320260601
SEED_COUNT = 24
DEBT_LEVELS = (0.0, 0.1, 0.2, 0.3, 0.4)
JSON_ARTIFACT = "reports/debt_dose_response.json"
REPORT_ARTIFACT = "reports/debt_dose_response_report.md"
TARGET_RESIDUE = "finite-sample-support"
METRICS = (
    "quality_q",
    "quality_debt",
    "target_score",
    "quality_benefit",
    "quality_cost",
    "linear_identifiability_r2",
    "approx_identifiability_proxy",
)


@dataclass(frozen=True)
class _DoseSurface:
    source_spec: dict[str, Any]
    classifier_spec_base: dict[str, Any]
    stability_spec: dict[str, Any]
    noise_scale: float
    sample_count: int


def _child_seed(master_seed: int, level_index: int, seed_index: int) -> int:
    value = (master_seed + 0x9E3779B9 * (level_index + 1) + 0x85EBCA6B * (seed_index + 1)) & 0xFFFFFFFF
    value ^= value >> 16
    value = (value * 0x7FEB352D) & 0xFFFFFFFF
    value ^= value >> 15
    value = (value * 0x846CA68B) & 0xFFFFFFFF
    value ^= value >> 16
    return int(value)


def _format_number(value: float) -> str:
    return f"{value:.6f}"


def _format_signed(value: float) -> str:
    return f"{value:+.6f}"


def _mean(values: list[float]) -> float:
    return float(sum(values) / len(values))


def _std(values: list[float]) -> float:
    if len(values) < 2:
        return 0.0
    center = _mean(values)
    variance = sum((value - center) ** 2 for value in values) / (len(values) - 1)
    return float(math.sqrt(max(0.0, variance)))


def _summary(values: list[float]) -> dict[str, float]:
    mean = _mean(values)
    std = _std(values)
    half_width = 1.96 * std / math.sqrt(len(values))
    return {
        "n": float(len(values)),
        "mean": mean,
        "std": std,
        "ci95_low": mean - half_width,
        "ci95_high": mean + half_width,
        "ci95_half_width": half_width,
        "min": float(min(values)),
        "max": float(max(values)),
    }


def _linear_regression(xs: list[float], ys: list[float]) -> dict[str, float]:
    if len(xs) != len(ys) or len(xs) < 3:
        raise ValueError("linear regression requires at least three paired observations")
    x_mean = _mean(xs)
    y_mean = _mean(ys)
    sxx = sum((x - x_mean) ** 2 for x in xs)
    if sxx <= 0.0:
        raise ValueError("linear regression requires nonconstant x values")
    slope = sum((x - x_mean) * (y - y_mean) for x, y in zip(xs, ys)) / sxx
    intercept = y_mean - slope * x_mean
    residuals = [y - (intercept + slope * x) for x, y in zip(xs, ys)]
    degrees = len(xs) - 2
    residual_std = math.sqrt(max(0.0, sum(residual * residual for residual in residuals) / degrees))
    slope_se = residual_std / math.sqrt(sxx)
    half_width = 1.96 * slope_se
    return {
        "intercept": float(intercept),
        "slope": float(slope),
        "slope_se": float(slope_se),
        "slope_ci95_low": float(slope - half_width),
        "slope_ci95_high": float(slope + half_width),
        "residual_std": float(residual_std),
    }


def _dose_surface(debt_level: float) -> _DoseSurface:
    source_spec = {
        "name": "gaussian-ou-hidden-debt-dose",
        "latent_dim": 2,
        "source_count": 3,
        "sample_count": 2048,
        "rho": 0.82,
        "mixing": ("sinusoidal", "parabolic", "shear"),
        "global_claim": True,
    }
    classifier_spec_base = {
        "name": "certified-standardized-linear-reader",
        "output_dim": 2,
        "training": "certified deterministic standardization",
    }
    stability_spec = {
        "name": "multi-seed-stability",
        "pair_process": "ornstein-uhlenbeck",
        "multi_seed": True,
    }

    if debt_level in (0.1, 0.3, 0.4):
        classifier_spec_base["name"] = "deterministic-standardized-linear-reader"
        classifier_spec_base["training"] = "deterministic standardization"
    if debt_level >= 0.2:
        source_spec["sample_count"] = 384
    if debt_level >= 0.4:
        stability_spec["name"] = "single-seed-stability"
        stability_spec["multi_seed"] = False

    return _DoseSurface(
        source_spec=source_spec,
        classifier_spec_base=classifier_spec_base,
        stability_spec=stability_spec,
        noise_scale=0.035 + 0.03 * debt_level,
        sample_count=int(source_spec["sample_count"]),
    )


def _synthetic_metrics(seed: int, surface: _DoseSurface) -> dict[str, float]:
    rng = np.random.default_rng(seed)
    z = rng.normal(loc=0.0, scale=1.0, size=(surface.sample_count, 2))
    mixer = np.array([[1.0, 0.16], [-0.10, 0.94]], dtype=np.float64)
    h = z @ mixer + rng.normal(loc=0.0, scale=surface.noise_scale, size=z.shape)
    return metric_bundle(h, z)


def _target_score(debt_items: Any) -> float:
    matches = [item.score for item in debt_items if item.residue == TARGET_RESIDUE]
    if len(matches) != 1:
        raise ValueError(f"expected one target residue {TARGET_RESIDUE!r}, found {len(matches)}")
    return float(matches[0])


def _record(debt_level: float, level_index: int, seed_index: int) -> dict[str, Any]:
    seed = _child_seed(MASTER_SEED, level_index, seed_index)
    surface = _dose_surface(debt_level)
    base_metrics = _synthetic_metrics(seed, surface)
    certificate = classifier_certificate(base_metrics, min_r2=0.80, min_proxy=0.68)
    classifier_spec = {**surface.classifier_spec_base, **certificate}
    stability_spec = {**surface.stability_spec, "seed": seed}
    debt_assessment = assess_debt(base_metrics, surface.source_spec, classifier_spec, stability_spec)
    ledger_gaps = derive_ledger_gaps(
        base_metrics,
        surface.source_spec,
        classifier_spec,
        stability_spec,
        debt_assessment,
    )
    quality = quality_components(base_metrics, debt_assessment.debt_total, classifier_spec)
    metrics = {
        **base_metrics,
        **quality,
        "target_score": _target_score(debt_assessment.items),
    }
    scope = Scope(
        domain_ids=frozenset({"gaussian-ou", f"seed-{seed_index:02d}"}),
        model_id="hidden-debt-dose-surface",
        admitted_family_id="ornstein-uhlenbeck",
        behavior_id="linear-identifiability",
    )
    return {
        "debt_level": float(debt_level),
        "level_index": level_index,
        "seed_index": seed_index,
        "master_seed": MASTER_SEED,
        "seed": seed,
        "generation": {
            "noise_scale": surface.noise_scale,
            "sample_count": surface.sample_count,
        },
        "scope": {
            "model_id": scope.model_id,
            "admitted_family_id": scope.admitted_family_id,
            "behavior_id": scope.behavior_id,
            "domain_ids": sorted(scope.domain_ids),
            "row_count": len(scope_rows(scope)),
        },
        "source_spec": surface.source_spec,
        "classifier_spec": classifier_spec,
        "stability_spec": stability_spec,
        "metrics": metrics,
        "debt_items": format_debt_items(debt_assessment),
        "ledger_gaps": format_ledger_gaps(ledger_gaps),
    }


def _records() -> list[dict[str, Any]]:
    return [
        _record(debt_level, level_index, seed_index)
        for level_index, debt_level in enumerate(DEBT_LEVELS)
        for seed_index in range(SEED_COUNT)
    ]


def _aggregate(records: Iterable[dict[str, Any]]) -> dict[str, Any]:
    grouped: dict[float, list[dict[str, Any]]] = {float(level): [] for level in DEBT_LEVELS}
    for record in records:
        grouped[float(record["debt_level"])].append(record)

    by_level: dict[str, dict[str, Any]] = {}
    for level in DEBT_LEVELS:
        level_records = grouped[float(level)]
        if len(level_records) != SEED_COUNT:
            raise ValueError(f"expected {SEED_COUNT} records for debt level {level}, found {len(level_records)}")
        metric_summary = {
            metric: _summary([float(record["metrics"][metric]) for record in level_records])
            for metric in METRICS
        }
        seeds = [int(record["seed"]) for record in level_records]
        measured_debts = sorted({float(record["metrics"]["quality_debt"]) for record in level_records})
        by_level[f"{level:.1f}"] = {
            "debt_level": float(level),
            "seed_count": len(level_records),
            "seeds": seeds,
            "measured_quality_debt_values": measured_debts,
            "metrics": metric_summary,
        }

    levels = [float(level) for level in DEBT_LEVELS]
    quality_means = [by_level[f"{level:.1f}"]["metrics"]["quality_q"]["mean"] for level in DEBT_LEVELS]
    strictly_decreasing = all(left > right for left, right in zip(quality_means, quality_means[1:]))
    regression = _linear_regression(levels, quality_means)
    slope_ci_below_zero = regression["slope_ci95_high"] < 0.0
    return {
        "master_seed": MASTER_SEED,
        "debt_levels": list(DEBT_LEVELS),
        "seed_count_per_level": SEED_COUNT,
        "record_count": sum(len(group) for group in grouped.values()),
        "metrics": list(METRICS),
        "by_level": by_level,
        "monotonicity": {
            "quality_q_means": quality_means,
            "strictly_decreasing": strictly_decreasing,
            "slope_ci_below_zero": slope_ci_below_zero,
            "pass": bool(strictly_decreasing and slope_ci_below_zero),
            "criterion": "pass iff quality_q level means are strictly decreasing and the fitted slope 95% CI is below zero",
        },
        "regression": regression,
    }


def _render_level_table(aggregate: dict[str, Any]) -> list[str]:
    lines = [
        "| debt level | measured debt | seeds | quality_q mean | std | 95% CI | target_score mean | quality_debt mean |",
        "| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |",
    ]
    for level in DEBT_LEVELS:
        summary = aggregate["by_level"][f"{level:.1f}"]
        q = summary["metrics"]["quality_q"]
        target = summary["metrics"]["target_score"]
        debt = summary["metrics"]["quality_debt"]
        measured = ", ".join(_format_number(value) for value in summary["measured_quality_debt_values"])
        lines.append(
            "| "
            f"{level:.1f} | {measured} | {int(summary['seed_count'])} | "
            f"{_format_signed(q['mean'])} | {_format_number(q['std'])} | "
            f"[{_format_signed(q['ci95_low'])}, {_format_signed(q['ci95_high'])}] | "
            f"{_format_number(target['mean'])} | {_format_number(debt['mean'])} |"
        )
    return lines


def _render_metric_table(aggregate: dict[str, Any]) -> list[str]:
    lines = [
        "| debt level | metric | mean | std | 95% CI | min | max |",
        "| ---: | --- | ---: | ---: | ---: | ---: | ---: |",
    ]
    for level in DEBT_LEVELS:
        summary = aggregate["by_level"][f"{level:.1f}"]
        for metric in METRICS:
            item = summary["metrics"][metric]
            lines.append(
                "| "
                f"{level:.1f} | `{metric}` | {_format_signed(item['mean'])} | "
                f"{_format_number(item['std'])} | "
                f"[{_format_signed(item['ci95_low'])}, {_format_signed(item['ci95_high'])}] | "
                f"{_format_signed(item['min'])} | {_format_signed(item['max'])} |"
            )
    return lines


def _render_seed_table(records: list[dict[str, Any]]) -> list[str]:
    lines = [
        "| debt level | seed index | seed | quality_q | quality_debt | target_score | r2 | proxy |",
        "| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |",
    ]
    for record in records:
        metrics = record["metrics"]
        lines.append(
            "| "
            f"{record['debt_level']:.1f} | {record['seed_index']} | {record['seed']} | "
            f"{_format_signed(metrics['quality_q'])} | {_format_number(metrics['quality_debt'])} | "
            f"{_format_number(metrics['target_score'])} | "
            f"{_format_number(metrics['linear_identifiability_r2'])} | "
            f"{_format_number(metrics['approx_identifiability_proxy'])} |"
        )
    return lines


def _render_report(records: list[dict[str, Any]], aggregate: dict[str, Any]) -> str:
    monotonic = aggregate["monotonicity"]
    regression = aggregate["regression"]
    result = "pass" if monotonic["pass"] else "fail"
    lines = [
        "# BEDC Quality Lab Debt Dose Response",
        "",
        "## Experimental Design",
        "",
        f"- Master seed: `{aggregate['master_seed']}`",
        f"- Debt levels: `{', '.join(f'{level:.1f}' for level in DEBT_LEVELS)}`",
        f"- Seeds per level: `{aggregate['seed_count_per_level']}`",
        f"- Record count: `{aggregate['record_count']}`",
        f"- Metrics: {', '.join(f'`{metric}`' for metric in METRICS)}.",
        f"- Monotonicity criterion: {monotonic['criterion']}.",
        "",
        "## Dose Summary",
        "",
        *_render_level_table(aggregate),
        "",
        "## Monotonicity Check",
        "",
        f"- Result: `{result}`",
        f"- Strictly decreasing level means: `{str(monotonic['strictly_decreasing']).lower()}`",
        f"- Slope 95% CI below zero: `{str(monotonic['slope_ci_below_zero']).lower()}`",
        f"- Degradation slope: `{_format_signed(regression['slope'])}` quality_q per debt-level unit",
        f"- Slope 95% CI: `[{_format_signed(regression['slope_ci95_low'])}, {_format_signed(regression['slope_ci95_high'])}]`",
        f"- Intercept: `{_format_signed(regression['intercept'])}`",
        "",
        "## Metric Summary",
        "",
        *_render_metric_table(aggregate),
        "",
        "## Seed Records",
        "",
        *_render_seed_table(records),
    ]
    return "\n".join(lines) + "\n"


def main() -> None:
    records = _records()
    aggregate = _aggregate(records)
    payload = {
        "artifact": JSON_ARTIFACT,
        "report": REPORT_ARTIFACT,
        "records": records,
        "aggregate": aggregate,
    }

    json_path = ROOT / JSON_ARTIFACT
    report_path = ROOT / REPORT_ARTIFACT
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    report_path.write_text(_render_report(records, aggregate), encoding="utf-8")
    print(f"wrote {json_path.relative_to(ROOT)}")
    print(f"wrote {report_path.relative_to(ROOT)}")
    print(f"records={aggregate['record_count']}")
    print(f"monotonicity={aggregate['monotonicity']['pass']}")


if __name__ == "__main__":
    main()

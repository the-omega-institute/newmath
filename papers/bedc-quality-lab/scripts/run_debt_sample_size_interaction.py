#!/usr/bin/env python3
"""Run the hidden-debt by sample-count interaction experiment."""

from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime, timezone
import json
import math
from pathlib import Path
import sys
from typing import Any, Iterable

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.debt import assess_debt, format_debt_items
from bedc_quality_lab.ledger import derive_ledger_gaps, format_ledger_gaps
from bedc_quality_lab.metrics import classifier_certificate, quality_components
from bedc_quality_lab.scope import Scope, scope_rows
from scripts.experiment_stats import fit_linear_slope, metric_stats, slope_ci_common_overlap
from scripts.run_debt_dose_response import TARGET_RESIDUE, _synthetic_metrics, _target_score


MASTER_SEED = 45620260601
SAMPLE_COUNTS = (96, 192, 384, 768)
DEBT_LEVELS = (0.0, 0.1, 0.2, 0.3, 0.4)
SEED_COUNT = 15
INTERACTION_METRIC = "quality_q"
JSON_ARTIFACT = "reports/debt_sample_size_interaction.json"
REPORT_ARTIFACT = "reports/debt_sample_size_interaction.md"
METRIC_NAMES = (
    "quality_q",
    "quality_debt",
    "target_score",
    "quality_benefit",
    "quality_cost",
    "quality_threshold",
    "quality_margin",
    "linear_identifiability_r2",
    "approx_identifiability_proxy",
    "orthogonality_error",
    "covariance_deviation",
)


@dataclass(frozen=True)
class _InteractionSurface:
    source_spec: dict[str, Any]
    classifier_spec_base: dict[str, Any]
    stability_spec: dict[str, Any]
    noise_scale: float
    sample_count: int


def _validate_config(
    *,
    sample_counts: Iterable[int] = SAMPLE_COUNTS,
    debt_levels: Iterable[float] = DEBT_LEVELS,
    seed_count: int = SEED_COUNT,
) -> None:
    sample_values = [int(value) for value in sample_counts]
    debt_values = [float(value) for value in debt_levels]
    if len(sample_values) < 4:
        raise ValueError("expected at least four sample_count values")
    if len(debt_values) < 5:
        raise ValueError("expected at least five debt_level values")
    if int(seed_count) < 15:
        raise ValueError("expected seed_count >= 15")
    if any(value <= 0 for value in sample_values):
        raise ValueError("sample_count values must be positive")
    if any(left >= right for left, right in zip(sample_values, sample_values[1:])):
        raise ValueError("sample_count grid must be strictly increasing")
    if any(left >= right for left, right in zip(debt_values, debt_values[1:])):
        raise ValueError("debt_level grid must be strictly increasing")
    if any(not math.isfinite(value) for value in debt_values):
        raise ValueError("debt_level values must be finite")


def _child_seed(master_seed: int, sample_index: int, level_index: int, seed_index: int) -> int:
    value = (
        int(master_seed)
        + 0x9E3779B9 * (sample_index + 1)
        + 0x85EBCA6B * (level_index + 1)
        + 0xC2B2AE35 * (seed_index + 1)
    ) & 0xFFFFFFFF
    value ^= value >> 16
    value = (value * 0x7FEB352D) & 0xFFFFFFFF
    value ^= value >> 15
    value = (value * 0x846CA68B) & 0xFFFFFFFF
    value ^= value >> 16
    return int(value)


def _level_token(debt_level: float) -> str:
    return f"{debt_level:.1f}".replace(".", "p").replace("-", "m")


def _cell_key(sample_count: int, debt_level: float) -> str:
    return f"n_{int(sample_count)}__debt_{_level_token(float(debt_level))}"


def _format_float(value: float) -> str:
    if math.isnan(value):
        return "nan"
    return f"{value:.6f}"


def _format_signed(value: float) -> str:
    if math.isnan(value):
        return "nan"
    return f"{value:+.6f}"


def _classifier_base(debt_level: float) -> dict[str, Any]:
    spec = {
        "name": "certified-standardized-linear-reader",
        "output_dim": 2,
        "training": "certified deterministic standardization",
    }
    if debt_level in (0.1, 0.3, 0.4):
        spec["name"] = "deterministic-standardized-linear-reader"
        spec["training"] = "deterministic standardization"
    return spec


def _source_spec(sample_count: int, debt_level: float) -> dict[str, Any]:
    spec: dict[str, Any] = {
        "name": "gaussian-ou-hidden-debt-sample-size-surface",
        "latent_dim": 2,
        "source_count": 3,
        "sample_count": int(sample_count),
        "rho": 0.82,
        "mixing": ("sinusoidal", "parabolic", "shear"),
        "global_claim": True,
        "debt_level": float(debt_level),
    }
    if debt_level >= 0.2:
        spec["mixing"] = ("sinusoidal", "shear")
    if debt_level >= 0.4:
        spec["source_count"] = 2
    return spec


def _stability_spec(debt_level: float, seed: int) -> dict[str, Any]:
    spec = {
        "name": "multi-seed-stability",
        "pair_process": "ornstein-uhlenbeck",
        "multi_seed": True,
        "seed": int(seed),
    }
    if debt_level >= 0.3:
        spec["name"] = "single-seed-stability"
        spec["multi_seed"] = False
    return spec


def _surface(sample_count: int, debt_level: float, seed: int) -> _InteractionSurface:
    sample_factor = math.sqrt(96.0 / float(sample_count))
    return _InteractionSurface(
        source_spec=_source_spec(sample_count, debt_level),
        classifier_spec_base=_classifier_base(debt_level),
        stability_spec=_stability_spec(debt_level, seed),
        noise_scale=0.032 + 0.055 * debt_level + 0.030 * debt_level * sample_factor,
        sample_count=int(sample_count),
    )


def _record_source_artifacts() -> dict[str, Any]:
    return {
        "script": "scripts/run_debt_sample_size_interaction.py",
        "debt_dose_adapter": "scripts/run_debt_dose_response.py::_synthetic_metrics",
        "target_score_adapter": "scripts/run_debt_dose_response.py::_target_score",
    }


def _source_artifacts() -> dict[str, Any]:
    return {
        "generation_script": "scripts/run_debt_sample_size_interaction.py",
        "shared_stats_helper": "scripts/experiment_stats.py",
        "debt_dose_helper": "scripts/run_debt_dose_response.py",
        "import_dependency_chain": [
            "scripts/run_debt_sample_size_interaction.py",
            "scripts.run_debt_dose_response._synthetic_metrics",
            "bedc_quality_lab.metrics.metric_bundle",
            "bedc_quality_lab.metrics.classifier_certificate",
            "bedc_quality_lab.metrics.quality_components",
            "bedc_quality_lab.debt.assess_debt",
            "bedc_quality_lab.ledger.derive_ledger_gaps",
            "bedc_quality_lab.scope.Scope",
            "scripts.experiment_stats",
        ],
        "json_artifact": JSON_ARTIFACT,
        "report_artifact": REPORT_ARTIFACT,
    }


def _run_record(
    *,
    sample_count: int,
    sample_index: int,
    debt_level: float,
    level_index: int,
    seed_index: int,
    seed: int,
) -> dict[str, Any]:
    run_id = (
        f"debt-sample-size-n{sample_count}-debt-{_level_token(debt_level)}-seed-{seed}"
    )
    surface = _surface(sample_count, debt_level, seed)
    base_metrics = _synthetic_metrics(seed, surface)
    certificate = classifier_certificate(base_metrics, min_r2=0.80, min_proxy=0.68)
    classifier_spec = {**surface.classifier_spec_base, **certificate}
    debt_assessment = assess_debt(
        base_metrics,
        surface.source_spec,
        classifier_spec,
        surface.stability_spec,
    )
    ledger_gaps = derive_ledger_gaps(
        base_metrics,
        surface.source_spec,
        classifier_spec,
        surface.stability_spec,
        debt_assessment,
    )
    quality = quality_components(base_metrics, debt_assessment.debt_total, classifier_spec)
    metrics = {
        **base_metrics,
        **quality,
        "target_score": _target_score(debt_assessment.items),
    }
    scope = Scope(
        domain_ids=frozenset(
            {
                "gaussian-ou",
                f"sample-count-{int(sample_count)}",
                f"seed-{int(seed_index):02d}",
            }
        ),
        model_id="hidden-debt-sample-size-surface",
        admitted_family_id="ornstein-uhlenbeck",
        behavior_id="linear-identifiability",
    )
    return {
        "sample_count": int(sample_count),
        "sample_index": int(sample_index),
        "debt_level": float(debt_level),
        "level_index": int(level_index),
        "seed_index": int(seed_index),
        "master_seed": int(MASTER_SEED),
        "seed": int(seed),
        "run_id": run_id,
        "classifier_name": classifier_spec.get("name"),
        "classifier_training": classifier_spec.get("training"),
        "generation": {
            "noise_scale": float(surface.noise_scale),
            "sample_count": int(surface.sample_count),
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
        "stability_spec": surface.stability_spec,
        "metrics": {name: float(metrics[name]) for name in METRIC_NAMES},
        "debt_items": format_debt_items(debt_assessment),
        "ledger_gaps": format_ledger_gaps(ledger_gaps),
        "source_artifacts": _record_source_artifacts(),
    }


def _records() -> list[dict[str, Any]]:
    _validate_config()
    return [
        _run_record(
            sample_count=sample_count,
            sample_index=sample_index,
            debt_level=debt_level,
            level_index=level_index,
            seed_index=seed_index,
            seed=_child_seed(MASTER_SEED, sample_index, level_index, seed_index),
        )
        for sample_index, sample_count in enumerate(SAMPLE_COUNTS)
        for level_index, debt_level in enumerate(DEBT_LEVELS)
        for seed_index in range(SEED_COUNT)
    ]


def _aggregate(records: list[dict[str, Any]]) -> dict[str, Any]:
    by_cell: dict[str, Any] = {}
    for sample_count in SAMPLE_COUNTS:
        for debt_level in DEBT_LEVELS:
            selected = [
                record
                for record in records
                if int(record["sample_count"]) == int(sample_count)
                and float(record["debt_level"]) == float(debt_level)
            ]
            by_cell[_cell_key(sample_count, debt_level)] = {
                "sample_count": int(sample_count),
                "debt_level": float(debt_level),
                "record_count": len(selected),
                "seeds": [int(record["seed"]) for record in selected],
                "metrics": {
                    name: metric_stats([float(record["metrics"][name]) for record in selected])
                    for name in METRIC_NAMES
                },
            }

    return {
        "by_sample_count_debt_level": by_cell,
        "record_count": len(records),
        "cell_count": len(SAMPLE_COUNTS) * len(DEBT_LEVELS),
    }


def _per_sample_count_slopes(aggregate: dict[str, Any]) -> dict[str, Any]:
    by_cell = aggregate["by_sample_count_debt_level"]
    slopes: dict[str, Any] = {}
    for sample_count in SAMPLE_COUNTS:
        points = [
            {
                "sample_count": int(sample_count),
                "debt_level": float(debt_level),
                INTERACTION_METRIC: float(
                    by_cell[_cell_key(sample_count, debt_level)]["metrics"][
                        INTERACTION_METRIC
                    ]["mean"]
                ),
            }
            for debt_level in DEBT_LEVELS
        ]
        fit = fit_linear_slope(points, "debt_level", INTERACTION_METRIC)
        slopes[f"n_{sample_count}"] = {
            "sample_count": int(sample_count),
            "metric": INTERACTION_METRIC,
            "points": points,
            "linear_fit": fit,
        }
    return slopes


def _interaction_test(per_sample_count_slopes: dict[str, Any]) -> dict[str, Any]:
    fits = [entry["linear_fit"] for entry in per_sample_count_slopes.values()]
    overlap = slope_ci_common_overlap(fits)
    return {
        "hypothesis": (
            "per-sample_count degradation slope 95% confidence intervals share a common overlap"
        ),
        "metric": INTERACTION_METRIC,
        "slope_ci_common_overlap": overlap,
        "h0_not_rejected": bool(overlap["all_overlap"]),
        "h0_rejected": not bool(overlap["all_overlap"]),
        "negative_result_note": (
            "The experiment reports the measured CI-overlap outcome directly; "
            "no debt-level, sample-count, or seed setting is tuned after observing the result."
        ),
    }


def _applicability_boundary() -> dict[str, Any]:
    return {
        "admitted_family": "Gaussian-OU toy world with lab-local hidden-debt assessment.",
        "model": "Deterministic standardized linear reader over synthetic Gaussian-OU samples.",
        "sample_count_range": [min(SAMPLE_COUNTS), max(SAMPLE_COUNTS)],
        "sample_counts": list(SAMPLE_COUNTS),
        "debt_levels": list(DEBT_LEVELS),
        "seed_count_per_cell": SEED_COUNT,
        "metric_behavior_range": (
            "Reported only for finite measured quality_q values produced by the debt, metric, "
            "and ledger path; slope fitting fails closed for non-finite values, constant grids, "
            "or insufficient points."
        ),
        "claim_scope": (
            "The interaction result applies only to the listed Gaussian-OU family, model, "
            "sample-count grid, debt grid, seed schedule, and quality_q construction."
        ),
    }


def _payload(records: list[dict[str, Any]]) -> dict[str, Any]:
    _validate_config()
    aggregate = _aggregate(records)
    slopes = _per_sample_count_slopes(aggregate)
    return {
        "artifact": JSON_ARTIFACT,
        "report": REPORT_ARTIFACT,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "config": {
            "master_seed": MASTER_SEED,
            "sample_counts": list(SAMPLE_COUNTS),
            "debt_levels": list(DEBT_LEVELS),
            "seed_count": SEED_COUNT,
            "expected_record_count": len(SAMPLE_COUNTS) * len(DEBT_LEVELS) * SEED_COUNT,
            "interaction_metric": INTERACTION_METRIC,
            "metric_names": list(METRIC_NAMES),
        },
        "records": records,
        "aggregate": aggregate,
        "per_sample_count_slopes": slopes,
        "interaction_test": _interaction_test(slopes),
        "applicability_boundary": _applicability_boundary(),
        "source_artifacts": _source_artifacts(),
    }


def _render_cell_table(payload: dict[str, Any]) -> list[str]:
    aggregate = payload["aggregate"]
    lines = [
        "| sample_count | debt_level | mean +/- std | 95% CI half-width | 95% CI | n |",
        "| ---: | ---: | ---: | ---: | ---: | ---: |",
    ]
    for sample_count in payload["config"]["sample_counts"]:
        for debt_level in payload["config"]["debt_levels"]:
            stats = aggregate["by_sample_count_debt_level"][
                _cell_key(sample_count, debt_level)
            ]["metrics"][INTERACTION_METRIC]
            lines.append(
                "| "
                f"{sample_count} | {debt_level:.1f} | "
                f"{_format_signed(float(stats['mean']))} +/- {_format_float(float(stats['std']))} | "
                f"{_format_float(float(stats['ci95_half_width']))} | "
                f"[{_format_signed(float(stats['ci95_low']))}, "
                f"{_format_signed(float(stats['ci95_high']))}] | {int(stats['n'])} |"
            )
    return lines


def _render_slope_table(payload: dict[str, Any]) -> list[str]:
    lines = [
        "| sample_count | degradation slope | 95% CI | standard error | points | status |",
        "| ---: | ---: | ---: | ---: | ---: | --- |",
    ]
    for entry in payload["per_sample_count_slopes"].values():
        fit = entry["linear_fit"]
        lines.append(
            "| "
            f"{entry['sample_count']} | {_format_signed(float(fit['slope']))} | "
            f"[{_format_signed(float(fit['slope_ci95_low']))}, "
            f"{_format_signed(float(fit['slope_ci95_high']))}] | "
            f"{_format_float(float(fit['slope_standard_error']))} | "
            f"{int(fit['n'])} | `{fit['status']}` |"
        )
    return lines


def _render_source_artifacts(source_artifacts: dict[str, Any]) -> list[str]:
    lines = [
        f"- Generation script: `{source_artifacts['generation_script']}`",
        f"- Shared stats helper: `{source_artifacts['shared_stats_helper']}`",
        f"- Debt-dose helper: `{source_artifacts['debt_dose_helper']}`",
        f"- JSON artifact: `{source_artifacts['json_artifact']}`",
        f"- Report artifact: `{source_artifacts['report_artifact']}`",
        "- Import dependency chain:",
    ]
    for item in source_artifacts["import_dependency_chain"]:
        lines.append(f"  - `{item}`")
    return lines


def _render_report(payload: dict[str, Any]) -> str:
    interaction = payload["interaction_test"]
    overlap = interaction["slope_ci_common_overlap"]
    boundary = payload["applicability_boundary"]
    lines = [
        "# Hidden-Debt Sample-Size Interaction Experiment",
        "",
        f"- Generated at: `{payload['generated_at']}`",
        f"- Sample counts: `{', '.join(str(value) for value in payload['config']['sample_counts'])}`",
        f"- Debt levels: `{', '.join(f'{value:.1f}' for value in payload['config']['debt_levels'])}`",
        f"- Seed count per cell: `{payload['config']['seed_count']}`",
        f"- Total records: `{len(payload['records'])}`",
        f"- Interaction metric: `{payload['config']['interaction_metric']}`",
        "",
        "## Cell Error Bars",
        "",
        *_render_cell_table(payload),
        "",
        "## Per-Sample Count Degradation Slopes",
        "",
        *_render_slope_table(payload),
        "",
        "## Interaction Test",
        "",
        f"- H0: {interaction['hypothesis']}.",
        (
            f"- Common CI overlap: `{str(bool(overlap['all_overlap'])).lower()}` "
            f"with interval `[{_format_signed(float(overlap['overlap_low']))}, "
            f"{_format_signed(float(overlap['overlap_high']))}]`"
        ),
        f"- H0 not rejected: `{str(bool(interaction['h0_not_rejected'])).lower()}`",
        f"- H0 rejected: `{str(bool(interaction['h0_rejected'])).lower()}`",
        f"- Negative result note: {interaction['negative_result_note']}",
        "",
        "## Applicability Boundary",
        "",
        f"- Admitted family: {boundary['admitted_family']}",
        f"- Model: {boundary['model']}",
        (
            "- Sample count range: "
            f"`{boundary['sample_count_range'][0]}` to `{boundary['sample_count_range'][1]}`."
        ),
        f"- Sample counts: `{', '.join(str(value) for value in boundary['sample_counts'])}`.",
        f"- Debt set: `{', '.join(f'{value:.1f}' for value in boundary['debt_levels'])}`.",
        f"- Seed count per cell: `{boundary['seed_count_per_cell']}`.",
        f"- Metric behavior range: {boundary['metric_behavior_range']}",
        f"- Claim scope: {boundary['claim_scope']}",
        "",
        "## Source Artifacts",
        "",
        *_render_source_artifacts(payload["source_artifacts"]),
        "",
        "## Raw Record Index",
        "",
        "| sample_count | debt_level | seed_index | seed | run_id | quality_q | source_artifacts |",
        "| ---: | ---: | ---: | ---: | --- | ---: | --- |",
    ]
    for record in payload["records"]:
        lines.append(
            "| "
            f"{record['sample_count']} | {record['debt_level']:.1f} | "
            f"{record['seed_index']} | {record['seed']} | `{record['run_id']}` | "
            f"{_format_signed(float(record['metrics'][INTERACTION_METRIC]))} | "
            f"`{record['source_artifacts']['script']}` |"
        )
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
    print(f"h0_not_rejected {payload['interaction_test']['h0_not_rejected']}")


if __name__ == "__main__":
    main()

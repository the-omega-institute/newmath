#!/usr/bin/env python3

from __future__ import annotations

import json
import math
from pathlib import Path
import sys
from typing import Any, Iterable

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import run_quality_improvement as improvement
from scripts.run_gaussian_ou_lejepa import run_experiment

MASTER_SEED = 43820260601
SEED_COUNT = 24
BEFORE_SAMPLE_COUNT = 384
AFTER_SAMPLE_COUNT = 2048
CONTROL_SAMPLE_COUNT = 384
JSON_ARTIFACT = "reports/quality_improvement_sweep.json"
REPORT_ARTIFACT = "reports/quality_improvement_sweep_report.md"
METRICS = (
    "delta_q",
    "delta_debt",
    "delta_target_score",
    "debt_reduction",
    "target_score_reduction",
)


def _child_seed(master_seed: int, index: int, stream: int) -> int:
    value = (master_seed + 0x9E3779B9 * (index + 1) + 0x85EBCA6B * (stream + 1)) & 0xFFFFFFFF
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


def _delta_record(
    *,
    arm: str,
    index: int,
    master_seed: int,
    before_seed: int,
    after_seed: int,
    before_sample_count: int,
    after_sample_count: int,
) -> dict[str, Any]:
    before = run_experiment(
        use_torch=False,
        sample_count=before_sample_count,
        seed=before_seed,
        run_id=f"quality-improvement-{arm}-seed-{index:02d}-before",
        envelope_artifact=f"reports/{arm}_seed_{index:02d}_before_envelope.json",
        report_artifact=REPORT_ARTIFACT,
    )
    after = run_experiment(
        use_torch=False,
        sample_count=after_sample_count,
        seed=after_seed,
        run_id=f"quality-improvement-{arm}-seed-{index:02d}-after",
        envelope_artifact=f"reports/{arm}_seed_{index:02d}_after_envelope.json",
        report_artifact=REPORT_ARTIFACT,
    )
    delta = improvement.quality_delta(before, after)
    delta_q = float(delta["delta_q"])
    delta_debt = float(delta["delta_debt"])
    delta_target_score = float(delta["delta_target_score"])
    metrics = {
        "delta_q": delta_q,
        "delta_debt": delta_debt,
        "delta_target_score": delta_target_score,
        "debt_reduction": -delta_debt,
        "target_score_reduction": -delta_target_score,
    }
    return {
        "arm": arm,
        "seed_index": index,
        "master_seed": master_seed,
        "before_seed": before_seed,
        "after_seed": after_seed,
        "before_sample_count": before_sample_count,
        "after_sample_count": after_sample_count,
        "before_run_id": before.run_id,
        "after_run_id": after.run_id,
        "before_status": str(delta["before_status"]),
        "after_status": str(delta["after_status"]),
        "before_score": float(delta["before_score"]),
        "after_score": float(delta["after_score"]),
        "before_quality_q": float(before.metrics["quality_q"]),
        "after_quality_q": float(after.metrics["quality_q"]),
        "before_quality_debt": float(before.metrics["quality_debt"]),
        "after_quality_debt": float(after.metrics["quality_debt"]),
        "before_linear_identifiability_r2": float(before.metrics["linear_identifiability_r2"]),
        "after_linear_identifiability_r2": float(after.metrics["linear_identifiability_r2"]),
        "before_approx_identifiability_proxy": float(before.metrics["approx_identifiability_proxy"]),
        "after_approx_identifiability_proxy": float(after.metrics["approx_identifiability_proxy"]),
        "metrics": metrics,
    }


def _records() -> list[dict[str, Any]]:
    records = []
    for index in range(SEED_COUNT):
        before_seed = _child_seed(MASTER_SEED, index, 0)
        improvement_seed = before_seed
        control_seed = before_seed
        records.append(
            _delta_record(
                arm="improvement",
                index=index,
                master_seed=MASTER_SEED,
                before_seed=before_seed,
                after_seed=improvement_seed,
                before_sample_count=BEFORE_SAMPLE_COUNT,
                after_sample_count=AFTER_SAMPLE_COUNT,
            )
        )
        records.append(
            _delta_record(
                arm="control",
                index=index,
                master_seed=MASTER_SEED,
                before_seed=before_seed,
                after_seed=control_seed,
                before_sample_count=BEFORE_SAMPLE_COUNT,
                after_sample_count=CONTROL_SAMPLE_COUNT,
            )
        )
    return records


def _aggregate(records: Iterable[dict[str, Any]]) -> dict[str, Any]:
    by_arm: dict[str, list[dict[str, Any]]] = {"improvement": [], "control": []}
    for record in records:
        by_arm[str(record["arm"])].append(record)

    summaries: dict[str, dict[str, dict[str, float]]] = {}
    for arm, arm_records in by_arm.items():
        summaries[arm] = {}
        for metric in METRICS:
            summaries[arm][metric] = _summary([float(record["metrics"][metric]) for record in arm_records])

    comparisons = {}
    for metric in METRICS:
        improvement_summary = summaries["improvement"][metric]
        control_summary = summaries["control"][metric]
        comparisons[metric] = {
            "mean_difference": improvement_summary["mean"] - control_summary["mean"],
            "separated_ci95": improvement_summary["ci95_low"] > control_summary["ci95_high"],
        }

    passes = (
        summaries["improvement"]["delta_q"]["ci95_low"] > 0.0
        and summaries["improvement"]["debt_reduction"]["ci95_low"] > 0.0
        and summaries["improvement"]["target_score_reduction"]["ci95_low"] > 0.0
        and comparisons["delta_q"]["separated_ci95"]
        and comparisons["debt_reduction"]["separated_ci95"]
        and comparisons["target_score_reduction"]["separated_ci95"]
    )
    return {
        "master_seed": MASTER_SEED,
        "seed_count": SEED_COUNT,
        "before_sample_count": BEFORE_SAMPLE_COUNT,
        "after_sample_count": AFTER_SAMPLE_COUNT,
        "control_sample_count": CONTROL_SAMPLE_COUNT,
        "metrics": list(METRICS),
        "summaries": summaries,
        "comparisons": comparisons,
        "significance_rule": (
            "pass iff improvement delta_q, debt_reduction, and target_score_reduction "
            "all have 95% CI lower bounds above 0 and their 95% CIs are separated from control"
        ),
        "significance_pass": passes,
    }


def _render_metric_table(aggregate: dict[str, Any]) -> list[str]:
    lines = [
        "| arm | metric | mean | std | 95% CI | min | max |",
        "| --- | --- | ---: | ---: | ---: | ---: | ---: |",
    ]
    for arm in ("improvement", "control"):
        for metric in METRICS:
            summary = aggregate["summaries"][arm][metric]
            lines.append(
                "| "
                f"{arm} | `{metric}` | {_format_signed(summary['mean'])} | {_format_number(summary['std'])} | "
                f"[{_format_signed(summary['ci95_low'])}, {_format_signed(summary['ci95_high'])}] | "
                f"{_format_signed(summary['min'])} | {_format_signed(summary['max'])} |"
            )
    return lines


def _render_comparison_table(aggregate: dict[str, Any]) -> list[str]:
    lines = [
        "| metric | improvement mean | control mean | mean difference | separated 95% CI |",
        "| --- | ---: | ---: | ---: | --- |",
    ]
    for metric in METRICS:
        improvement_summary = aggregate["summaries"]["improvement"][metric]
        control_summary = aggregate["summaries"]["control"][metric]
        comparison = aggregate["comparisons"][metric]
        lines.append(
            "| "
            f"`{metric}` | {_format_signed(improvement_summary['mean'])} | "
            f"{_format_signed(control_summary['mean'])} | {_format_signed(comparison['mean_difference'])} | "
            f"{'yes' if comparison['separated_ci95'] else 'no'} |"
        )
    return lines


def _render_seed_table(records: list[dict[str, Any]]) -> list[str]:
    lines = [
        "| seed index | before seed | improvement after seed | control after seed | improvement delta_q | control delta_q | improvement debt reduction | control debt reduction |",
        "| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |",
    ]
    by_index: dict[int, dict[str, dict[str, Any]]] = {}
    for record in records:
        by_index.setdefault(int(record["seed_index"]), {})[str(record["arm"])] = record
    for index in sorted(by_index):
        improvement_record = by_index[index]["improvement"]
        control_record = by_index[index]["control"]
        lines.append(
            "| "
            f"{index} | {improvement_record['before_seed']} | {improvement_record['after_seed']} | "
            f"{control_record['after_seed']} | {_format_signed(improvement_record['metrics']['delta_q'])} | "
            f"{_format_signed(control_record['metrics']['delta_q'])} | "
            f"{_format_signed(improvement_record['metrics']['debt_reduction'])} | "
            f"{_format_signed(control_record['metrics']['debt_reduction'])} |"
        )
    return lines


def _render_report(records: list[dict[str, Any]], aggregate: dict[str, Any]) -> str:
    pass_label = "pass" if aggregate["significance_pass"] else "fail"
    lines = [
        "# BEDC Quality Lab Quality Improvement Sweep",
        "",
        "## Experimental Design",
        "",
        f"- Master seed: `{aggregate['master_seed']}`",
        f"- Seed count: `{aggregate['seed_count']}`",
        f"- Before sample count: `{aggregate['before_sample_count']}`",
        f"- Improvement arm after sample count: `{aggregate['after_sample_count']}`",
        f"- Control arm after sample count: `{aggregate['control_sample_count']}`",
        "- Improvement arm: finite-sample hardening by increasing support from 384 to 2048 observations.",
        "- Control arm: no-op operator with the same seed and sample count as the before surface.",
        f"- Significance rule: {aggregate['significance_rule']}.",
        f"- Significance result: `{pass_label}`.",
        "",
        "## Metric Summary",
        "",
        *_render_metric_table(aggregate),
        "",
        "## Arm Comparison",
        "",
        *_render_comparison_table(aggregate),
        "",
        "## Seed Distribution",
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
    print(f"significance={aggregate['significance_pass']}")


if __name__ == "__main__":
    main()

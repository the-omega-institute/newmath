#!/usr/bin/env python3
"""Run a sample-count by rho interaction experiment."""

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

from scripts.experiment_stats import fit_log_log_slope, metric_stats, slope_ci_common_overlap
from scripts.run_gaussian_ou_lejepa import run_experiment
from scripts.run_sample_size_scaling import _child_seed


MASTER_SEED = 453021
SEED_COUNT = 15
SAMPLE_COUNTS = (96, 192, 384, 768)
RHO_VALUES = (0.3, 0.6, 0.9)
USE_TORCH = True
INTERACTION_METRIC = "linear_identifiability_r2"
JSON_ARTIFACT = "reports/sample_size_rho_interaction.json"
REPORT_ARTIFACT = "reports/sample_size_rho_interaction.md"
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


def _run_record(*, sample_count: int, rho: float, seed: int, seed_index: int) -> dict[str, Any]:
    run_id = f"sample-size-rho-n{sample_count}-rho-{_rho_token(rho)}-seed-{seed}"
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
        _run_record(sample_count=sample_count, rho=rho, seed=seed, seed_index=seed_index)
        for rho in RHO_VALUES
        for sample_count in SAMPLE_COUNTS
        for seed_index, seed in enumerate(seeds)
    ]


def _cell_key(rho: float, sample_count: int) -> str:
    return f"rho_{_rho_token(rho)}__n_{sample_count}"


def _aggregate(records: list[dict[str, Any]]) -> dict[str, Any]:
    by_cell: dict[str, Any] = {}
    for rho in RHO_VALUES:
        for sample_count in SAMPLE_COUNTS:
            selected = [
                record
                for record in records
                if float(record["rho"]) == float(rho)
                and int(record["sample_count"]) == int(sample_count)
            ]
            by_cell[_cell_key(rho, sample_count)] = {
                "rho": float(rho),
                "sample_count": int(sample_count),
                "record_count": len(selected),
                "seeds": [int(record["seed"]) for record in selected],
                "metrics": {
                    name: metric_stats([float(record["metrics"][name]) for record in selected])
                    for name in METRIC_NAMES
                },
            }

    return {"by_rho_sample_count": by_cell}


def _per_rho_slopes(aggregate: dict[str, Any]) -> dict[str, Any]:
    slopes: dict[str, Any] = {}
    by_cell = aggregate["by_rho_sample_count"]
    for rho in RHO_VALUES:
        points = [
            {
                "rho": float(rho),
                "sample_count": int(sample_count),
                "std": float(
                    by_cell[_cell_key(rho, sample_count)]["metrics"][INTERACTION_METRIC]["std"]
                ),
            }
            for sample_count in SAMPLE_COUNTS
        ]
        fit = fit_log_log_slope(points)
        slopes[f"rho_{_rho_token(rho)}"] = {
            "rho": float(rho),
            "metric": INTERACTION_METRIC,
            "std_by_sample_count": points,
            "log_log_fit": fit,
        }
    return slopes


def _interaction_test(per_rho_slopes: dict[str, Any]) -> dict[str, Any]:
    fits = [entry["log_log_fit"] for entry in per_rho_slopes.values()]
    overlap = slope_ci_common_overlap(fits)
    return {
        "hypothesis": "per-rho log-log slope 95% confidence intervals share a common overlap",
        "metric": INTERACTION_METRIC,
        "slope_ci_common_overlap": overlap,
        "h0_not_rejected": bool(overlap["all_overlap"]),
        "h0_rejected": not bool(overlap["all_overlap"]),
        "negative_result_note": (
            "The experiment reports the measured CI-overlap outcome directly; "
            "no rho or sample-count setting is tuned after observing the result."
        ),
    }


def _applicability_boundary() -> dict[str, Any]:
    return {
        "admitted_family": "Gaussian-OU toy world generated by the canonical runner.",
        "model": "Canonical tiny MLP encoder when available, with runner-managed fallback behavior.",
        "sample_count_range": [min(SAMPLE_COUNTS), max(SAMPLE_COUNTS)],
        "sample_counts": list(SAMPLE_COUNTS),
        "rho_values": list(RHO_VALUES),
        "metric_behavior_range": (
            "Reported only for finite measured values returned by the canonical quality envelope; "
            "slope fitting ignores non-positive cell standard deviations and fails closed with "
            "insufficient positive points."
        ),
    }


def _source_artifacts() -> dict[str, Any]:
    return {
        "generation_script": "scripts/run_sample_size_rho_interaction.py",
        "canonical_runner": "scripts/run_gaussian_ou_lejepa.py::run_experiment",
        "shared_stats_helper": "scripts/experiment_stats.py",
        "import_dependency_chain": [
            "scripts/run_sample_size_rho_interaction.py",
            "scripts.run_gaussian_ou_lejepa.run_experiment",
            "bedc_quality_lab.toy_world.make_toy_batch",
            "bedc_quality_lab.metrics.metric_bundle",
            "bedc_quality_lab.schema.QualityEvidenceEnvelope",
            "scripts.experiment_stats",
        ],
        "report_artifact": REPORT_ARTIFACT,
        "json_artifact": JSON_ARTIFACT,
    }


def _payload(records: list[dict[str, Any]]) -> dict[str, Any]:
    aggregate = _aggregate(records)
    per_rho_slopes = _per_rho_slopes(aggregate)
    return {
        "artifact": JSON_ARTIFACT,
        "report": REPORT_ARTIFACT,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "config": {
            "master_seed": MASTER_SEED,
            "seed_count": SEED_COUNT,
            "seeds": _seeds(MASTER_SEED, SEED_COUNT),
            "sample_counts": list(SAMPLE_COUNTS),
            "rho_values": list(RHO_VALUES),
            "use_torch": USE_TORCH,
            "metric_names": list(METRIC_NAMES),
            "interaction_metric": INTERACTION_METRIC,
            "expected_record_count": len(SAMPLE_COUNTS) * len(RHO_VALUES) * SEED_COUNT,
        },
        "source_artifacts": _source_artifacts(),
        "records": records,
        "aggregate": aggregate,
        "per_rho_slopes": per_rho_slopes,
        "interaction_test": _interaction_test(per_rho_slopes),
        "applicability_boundary": _applicability_boundary(),
    }


def _format_float(value: float) -> str:
    if math.isnan(value):
        return "nan"
    return f"{value:.6f}"


def _pass_label(value: bool) -> str:
    return "pass" if value else "fail"


def _render_report(payload: dict[str, Any]) -> str:
    aggregate = payload["aggregate"]
    interaction = payload["interaction_test"]
    overlap = interaction["slope_ci_common_overlap"]
    lines = [
        "# Sample-Size Rho Interaction Experiment",
        "",
        f"- Generated at: `{payload['generated_at']}`",
        f"- Canonical runner: `{payload['source_artifacts']['canonical_runner']}`",
        f"- Shared stats helper: `{payload['source_artifacts']['shared_stats_helper']}`",
        f"- Sample counts: `{', '.join(str(n) for n in payload['config']['sample_counts'])}`",
        f"- Rho values: `{', '.join(str(rho) for rho in payload['config']['rho_values'])}`",
        f"- Seed count per cell: `{payload['config']['seed_count']}`",
        f"- Seeds: `{', '.join(str(seed) for seed in payload['config']['seeds'])}`",
        f"- Interaction metric: `{payload['config']['interaction_metric']}`",
        f"- Total records: `{len(payload['records'])}`",
        "",
        "## Cell Error Bars",
        "",
        "| rho | sample_count | mean +/- std | 95% CI half-width | 95% CI | n |",
        "| ---: | ---: | ---: | ---: | ---: | ---: |",
    ]
    for rho in payload["config"]["rho_values"]:
        for sample_count in payload["config"]["sample_counts"]:
            stats = aggregate["by_rho_sample_count"][_cell_key(rho, sample_count)]["metrics"][
                payload["config"]["interaction_metric"]
            ]
            lines.append(
                "| "
                f"{rho} | {sample_count} | "
                f"{_format_float(float(stats['mean']))} +/- {_format_float(float(stats['std']))} | "
                f"{_format_float(float(stats['ci95_half_width']))} | "
                f"[{_format_float(float(stats['ci95_low']))}, "
                f"{_format_float(float(stats['ci95_high']))}] | {int(stats['n'])} |"
            )

    lines.extend(
        [
            "",
            "## Per-Rho Std Slopes",
            "",
            "| rho | slope | 95% CI | positive points | status |",
            "| ---: | ---: | ---: | ---: | --- |",
        ]
    )
    for entry in payload["per_rho_slopes"].values():
        fit = entry["log_log_fit"]
        lines.append(
            "| "
            f"{entry['rho']} | {_format_float(float(fit['slope']))} | "
            f"[{_format_float(float(fit['slope_ci95_low']))}, "
            f"{_format_float(float(fit['slope_ci95_high']))}] | "
            f"{int(fit['n'])} | `{fit['status']}` |"
        )

    lines.extend(
        [
            "",
            "## Interaction Test",
            "",
            f"- H0: {interaction['hypothesis']}.",
            (
                f"- Common CI overlap: `{_pass_label(bool(overlap['all_overlap']))}` "
                f"with interval `[{_format_float(float(overlap['overlap_low']))}, "
                f"{_format_float(float(overlap['overlap_high']))}]`"
            ),
            f"- H0 not rejected: `{_pass_label(bool(interaction['h0_not_rejected']))}`",
            f"- H0 rejected: `{_pass_label(bool(interaction['h0_rejected']))}`",
            f"- Negative result note: {interaction['negative_result_note']}",
            "",
            "## Applicability Boundary",
            "",
            f"- Admitted family: {payload['applicability_boundary']['admitted_family']}",
            f"- Model: {payload['applicability_boundary']['model']}",
            (
                "- Sample count range: "
                f"`{payload['applicability_boundary']['sample_count_range'][0]}` to "
                f"`{payload['applicability_boundary']['sample_count_range'][1]}`."
            ),
            (
                "- Rho set: "
                f"`{', '.join(str(rho) for rho in payload['applicability_boundary']['rho_values'])}`."
            ),
            f"- Metric behavior range: {payload['applicability_boundary']['metric_behavior_range']}",
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
            "## Cell Seeds",
            "",
            "| rho | sample_count | seeds |",
            "| ---: | ---: | --- |",
        ]
    )
    for rho in payload["config"]["rho_values"]:
        for sample_count in payload["config"]["sample_counts"]:
            seeds = aggregate["by_rho_sample_count"][_cell_key(rho, sample_count)]["seeds"]
            lines.append(f"| {rho} | {sample_count} | `{', '.join(str(seed) for seed in seeds)}` |")
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

#!/usr/bin/env python3
"""Run the anisotropic Gaussian-OU transition-isotropy sweep."""

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

from bedc_quality_lab.transition import TransitionKernelSpec
from scripts.run_gaussian_ou_lejepa import run_experiment


SEED_BASE = 497
SEED_COUNT = 20
RHO_BY_AXIS_GRID = (
    (0.9, 0.9),
    (0.9, 0.6),
    (0.95, 0.3),
    (0.99, 0.5),
)
SAMPLE_COUNT = 384
METRIC_NAMES = (
    "linear_identifiability_r2",
    "approx_identifiability_proxy",
    "alignment_loss",
    "quality_benefit",
    "quality_cost",
    "quality_debt",
    "quality_q",
    "quality_margin",
)
REPORT_JSON = ROOT / "reports" / "anisotropic_ou_sweep.json"
REPORT_MD = ROOT / "reports" / "anisotropic_ou_sweep.md"


def _derive_seeds(base_seed: int, count: int) -> list[int]:
    return [int(base_seed + 997 * index + 29 * index * index) for index in range(count)]


def _rho_key(rho_by_axis: tuple[float, ...]) -> str:
    return "rho_axes_" + "_".join(str(value).replace(".", "p") for value in rho_by_axis)


def _format_float(value: float) -> str:
    if math.isnan(value):
        return "nan"
    return f"{value:.6f}"


def _parse_debt_item(row: str) -> dict[str, str]:
    parts = {}
    for chunk in row.split("; "):
        key, sep, value = chunk.partition("=")
        if sep:
            parts[key] = value
    return parts


def _transition_debt_item(debt_items: list[str]) -> dict[str, str]:
    matches = [
        _parse_debt_item(item)
        for item in debt_items
        if "kind=source;" in item and "residue=transition-isotropy;" in item
    ]
    if len(matches) != 1:
        raise ValueError("expected exactly one transition-isotropy debt item")
    return matches[0]


def _run_record(*, rho_by_axis: tuple[float, ...], seed: int, sample_count: int) -> dict[str, Any]:
    spec = TransitionKernelSpec(rho_by_axis=rho_by_axis)
    scalar_rho = float(statistics.fmean(rho_by_axis))
    run_id = f"anisotropic-ou-baseline-seed-{seed}-{_rho_key(rho_by_axis)}"
    envelope = run_experiment(
        use_torch=False,
        sample_count=sample_count,
        seed=seed,
        rho=scalar_rho,
        transition_kernel=spec,
        run_id=run_id,
        envelope_artifact="reports/anisotropic_ou_sweep.json",
        report_artifact="reports/anisotropic_ou_sweep.md",
    )
    transition_debt = _transition_debt_item(envelope.debt_items)
    return {
        "rho_by_axis": list(rho_by_axis),
        "rho_key": _rho_key(rho_by_axis),
        "scalar_formula_rho": scalar_rho,
        "seed": seed,
        "sample_count": sample_count,
        "status": "ok",
        "latent_distribution": "gaussian",
        "classifier_name": envelope.classifier_spec.get("name"),
        "transition_source_spec": envelope.source_spec["transition_kernel"],
        "transition_debt_item": transition_debt,
        "transition_ledger_gaps": [
            gap for gap in envelope.ledger_gaps if "residue=transition-isotropy;" in gap
        ],
        "metrics": {name: float(envelope.metrics[name]) for name in METRIC_NAMES},
        "envelope": envelope.to_dict(),
    }


def _sample_std(values: list[float]) -> float:
    if len(values) < 2:
        return 0.0
    return float(statistics.stdev(values))


def _metric_stats(values: list[float]) -> dict[str, float | int]:
    count = len(values)
    if count == 0:
        return {"n": 0, "mean": math.nan, "std": math.nan, "ci95": math.nan}
    mean = float(statistics.fmean(values))
    std = _sample_std(values)
    ci95 = 0.0 if count < 2 else float(1.96 * std / math.sqrt(count))
    return {"n": count, "mean": mean, "std": std, "ci95": ci95}


def _aggregate(records: list[dict[str, Any]]) -> dict[str, Any]:
    aggregates: dict[str, Any] = {}
    for rho_by_axis in RHO_BY_AXIS_GRID:
        key = _rho_key(rho_by_axis)
        selected = [record for record in records if record["status"] == "ok" and record["rho_key"] == key]
        aggregates[key] = {
            "rho_by_axis": list(rho_by_axis),
            "ok_count": len(selected),
            "seeds": [int(record["seed"]) for record in selected],
            "transition_isotropic": bool(selected[0]["transition_source_spec"]["isotropic"]) if selected else False,
            "transition_anisotropy_gap": (
                float(selected[0]["transition_source_spec"]["anisotropy_gap"]) if selected else math.nan
            ),
            "transition_debt": _metric_stats(
                [float(record["transition_debt_item"]["score"]) for record in selected]
            ),
            "metrics": {
                name: _metric_stats([float(record["metrics"][name]) for record in selected])
                for name in METRIC_NAMES
            },
        }
    return aggregates


def _transition_debt_by_grid(aggregates: dict[str, Any]) -> dict[str, Any]:
    return {
        key: {
            "rho_by_axis": value["rho_by_axis"],
            "transition_isotropic": value["transition_isotropic"],
            "transition_anisotropy_gap": value["transition_anisotropy_gap"],
            "debt_score_mean": value["transition_debt"]["mean"],
            "status": "closed" if float(value["transition_debt"]["mean"]) <= 0.0 else "open-or-partial",
        }
        for key, value in aggregates.items()
    }


def _negative_result_summary(aggregates: dict[str, Any]) -> dict[str, Any]:
    baseline = aggregates[_rho_key(RHO_BY_AXIS_GRID[0])]["metrics"]["quality_q"]["mean"]
    cells = {}
    any_negative = False
    for rho_by_axis in RHO_BY_AXIS_GRID:
        key = _rho_key(rho_by_axis)
        mean_q = aggregates[key]["metrics"]["quality_q"]["mean"]
        delta = float(mean_q) - float(baseline)
        negative = delta < 0.0
        any_negative = any_negative or negative
        cells[key] = {
            "rho_by_axis": list(rho_by_axis),
            "quality_q_delta_vs_isotropic": delta,
            "negative_result": negative,
        }
    return {
        "baseline_rho_by_axis": list(RHO_BY_AXIS_GRID[0]),
        "comparison_metric": "quality_q_delta_vs_isotropic",
        "any_negative_result": any_negative,
        "cells": cells,
    }


def _applicability_boundary() -> dict[str, Any]:
    return {
        "latent_family": "gaussian",
        "transition_family": "ornstein-uhlenbeck",
        "transition_noise_family": "gaussian",
        "claimed_scope": "Gaussian latent + anisotropic transition",
        "not_claimed": "This sweep does not claim non-Gaussian transition noise or non-Gaussian latent coverage.",
        "eigenvalue_interleaving": [
            TransitionKernelSpec(rho_by_axis=rho_by_axis).eigenvalue_interleaving_summary()
            for rho_by_axis in RHO_BY_AXIS_GRID
        ],
    }


def _payload(records: list[dict[str, Any]], seeds: list[int]) -> dict[str, Any]:
    aggregates = _aggregate(records)
    return {
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "config": {
            "seed_base": SEED_BASE,
            "seed_count": SEED_COUNT,
            "seeds": seeds,
            "rho_by_axis_grid": [list(values) for values in RHO_BY_AXIS_GRID],
            "sample_count": SAMPLE_COUNT,
            "arm": "baseline-only",
            "metric_names": list(METRIC_NAMES),
        },
        "source_artifacts": {
            "transition_surface": "bedc_quality_lab/transition.py",
            "canonical_runner": "scripts/run_gaussian_ou_lejepa.py",
            "cost_protocol": "configs/default_cost_protocol.yaml",
        },
        "applicability_boundary": _applicability_boundary(),
        "records": records,
        "aggregates": aggregates,
        "transition_debt_by_grid": _transition_debt_by_grid(aggregates),
        "negative_result_summary": _negative_result_summary(aggregates),
    }


def _render_markdown(payload: dict[str, Any]) -> str:
    lines = [
        "# Anisotropic Gaussian-OU transition-isotropy sweep",
        "",
        f"- Generated at: `{payload['generated_at']}`",
        f"- Seed count: `{payload['config']['seed_count']}`",
        f"- Sample count: `{payload['config']['sample_count']}`",
        "- Applicability boundary: `Gaussian latent + anisotropic transition`",
        "- Transition noise family: `gaussian`",
        "- Non-Gaussian transition noise: not claimed",
        "",
        "## Transition debt by grid",
        "",
        "| rho_by_axis | isotropic | anisotropy gap | transition debt mean | status | quality_q mean |",
        "| --- | --- | ---: | ---: | --- | ---: |",
    ]
    for key in payload["aggregates"]:
        row = payload["aggregates"][key]
        debt = payload["transition_debt_by_grid"][key]
        quality_q = row["metrics"]["quality_q"]["mean"]
        rho_text = ", ".join(str(value) for value in row["rho_by_axis"])
        lines.append(
            "| "
            f"`({rho_text})` | `{row['transition_isotropic']}` | "
            f"{_format_float(float(row['transition_anisotropy_gap']))} | "
            f"{_format_float(float(debt['debt_score_mean']))} | {debt['status']} | "
            f"{_format_float(float(quality_q))} |"
        )

    lines.extend(
        [
            "",
            "## Negative-result audit",
            "",
            "| rho_by_axis | quality_q delta vs isotropic | negative result |",
            "| --- | ---: | --- |",
        ]
    )
    for cell in payload["negative_result_summary"]["cells"].values():
        rho_text = ", ".join(str(value) for value in cell["rho_by_axis"])
        lines.append(
            "| "
            f"`({rho_text})` | {_format_float(float(cell['quality_q_delta_vs_isotropic']))} | "
            f"`{cell['negative_result']}` |"
        )

    lines.extend(
        [
            "",
            "## Applicability boundary",
            "",
            f"- Claimed scope: `{payload['applicability_boundary']['claimed_scope']}`",
            f"- Not claimed: {payload['applicability_boundary']['not_claimed']}",
            "- Eigenvalue interleaving summaries are copied from the JSON evidence payload.",
            "",
            "| eigenvalues | anisotropy gap | min adjacent gap |",
            "| --- | ---: | ---: |",
        ]
    )
    for summary in payload["applicability_boundary"]["eigenvalue_interleaving"]:
        eigenvalues = ", ".join(str(value) for value in summary["eigenvalues"])
        lines.append(
            "| "
            f"`({eigenvalues})` | {_format_float(float(summary['anisotropy_gap']))} | "
            f"{_format_float(float(summary['min_adjacent_gap']))} |"
        )
    lines.append("")
    return "\n".join(lines)


def _write_payload(payload: dict[str, Any]) -> None:
    REPORT_JSON.parent.mkdir(parents=True, exist_ok=True)
    REPORT_JSON.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    REPORT_MD.write_text(_render_markdown(payload), encoding="utf-8")


def main() -> None:
    seeds = _derive_seeds(SEED_BASE, SEED_COUNT)
    records = [
        _run_record(rho_by_axis=rho_by_axis, seed=seed, sample_count=SAMPLE_COUNT)
        for rho_by_axis in RHO_BY_AXIS_GRID
        for seed in seeds
    ]
    _write_payload(_payload(records, seeds))
    print(f"wrote {REPORT_JSON.relative_to(ROOT)}")
    print(f"wrote {REPORT_MD.relative_to(ROOT)}")


if __name__ == "__main__":
    main()

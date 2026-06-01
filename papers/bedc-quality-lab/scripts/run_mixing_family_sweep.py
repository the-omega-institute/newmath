#!/usr/bin/env python3
"""Run the canonical nonlinear mixing-family coverage sweep."""

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

from bedc_quality_lab.debt import assess_debt, format_debt_items
from bedc_quality_lab.mixing import canonical_mixing_families, covered_canonical_mixing_families
from scripts.run_gaussian_ou_lejepa import run_experiment


SEED_BASE = 498
SEED_COUNT = 6
SAMPLE_COUNT = 384
RHO = 0.82
METRIC_NAMES = (
    "linear_identifiability_r2",
    "approx_identifiability_proxy",
    "alignment_loss",
    "quality_benefit",
    "quality_cost",
    "quality_debt",
    "quality_q",
    "quality_margin",
    "theorem3_bound",
    "actual_recovery_error",
    "bound_margin",
)
REPORT_JSON = ROOT / "reports" / "mixing_family_sweep.json"
REPORT_MD = ROOT / "reports" / "mixing_family_sweep.md"


def _derive_seeds(base_seed: int, count: int) -> list[int]:
    return [int(base_seed + 991 * index + 41 * index * index) for index in range(count)]


def _format_float(value: float) -> str:
    if math.isnan(value):
        return "nan"
    return f"{value:.6f}"


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


def _parse_debt_item(row: str) -> dict[str, str]:
    parts = {}
    for chunk in row.split("; "):
        key, sep, value = chunk.partition("=")
        if sep:
            parts[key] = value
    return parts


def _mixing_debt_item(debt_items: list[str]) -> dict[str, str]:
    matches = [
        _parse_debt_item(item)
        for item in debt_items
        if "kind=source;" in item and "residue=mixing-family-coverage;" in item
    ]
    if len(matches) != 1:
        raise ValueError("expected exactly one mixing-family-coverage debt item")
    return matches[0]


def _coverage_item(observed: list[str]) -> dict[str, Any]:
    canonical = list(canonical_mixing_families())
    covered = list(covered_canonical_mixing_families(observed))
    missing = [name for name in canonical if name not in covered]
    source_spec = {
        "source_count": 3,
        "sample_count": 2048,
        "mixing": observed,
    }
    classifier_spec = {"name": "certified-search", "training": "certified"}
    stability_spec = {"multi_seed": True}
    metrics = {
        "theorem3_bound": 1.0,
        "actual_recovery_error": 0.0,
        "bound_margin": 1.0,
    }
    assessment = assess_debt(metrics, source_spec, classifier_spec, stability_spec)
    return {
        "kind": "source",
        "residue": "mixing-family-coverage",
        "canonical_families": canonical,
        "covered_families": covered,
        "missing_families": missing,
        "observed_values": observed,
        "debt_item": _mixing_debt_item(format_debt_items(assessment)),
    }


def _run_record(*, mixing: str, seed: int, sample_count: int) -> dict[str, Any]:
    run_id = f"mixing-family-{mixing}-seed-{seed}"
    envelope = run_experiment(
        use_torch=False,
        sample_count=sample_count,
        seed=seed,
        rho=RHO,
        mixing=mixing,
        run_id=run_id,
        envelope_artifact="reports/mixing_family_sweep.json",
        report_artifact="reports/mixing_family_sweep.md",
    )
    return {
        "mixing": mixing,
        "seed": seed,
        "sample_count": sample_count,
        "status": "ok",
        "classifier_name": envelope.classifier_spec.get("name"),
        "classifier_training": envelope.classifier_spec.get("training"),
        "source_mixing": envelope.source_spec.get("mixing"),
        "mixing_debt_item": _mixing_debt_item(envelope.debt_items),
        "metrics": {name: float(envelope.metrics[name]) for name in METRIC_NAMES},
        "envelope_projection": {
            "schema_id": envelope.schema_id,
            "run_id": envelope.run_id,
            "source_spec": envelope.source_spec,
            "classifier_spec": envelope.classifier_spec,
            "stability_spec": envelope.stability_spec,
            "metrics": {name: float(envelope.metrics[name]) for name in METRIC_NAMES},
            "debt_items": envelope.debt_items,
            "ledger_gaps": envelope.ledger_gaps,
        },
    }


def _aggregate(records: list[dict[str, Any]]) -> dict[str, Any]:
    aggregates: dict[str, Any] = {}
    for family in canonical_mixing_families():
        selected = [
            record
            for record in records
            if record["status"] == "ok" and record["mixing"] == family
        ]
        aggregates[family] = {
            "ok_count": len(selected),
            "seeds": [int(record["seed"]) for record in selected],
            "source_mixing_values": [str(record["source_mixing"]) for record in selected],
            "metrics": {
                name: _metric_stats([float(record["metrics"][name]) for record in selected])
                for name in METRIC_NAMES
            },
            "canonical_runner_mixing_debt": [
                record["mixing_debt_item"]
                for record in selected
            ],
        }
    return aggregates


def _negative_result_summary(aggregates: dict[str, Any]) -> dict[str, Any]:
    baseline = float(aggregates[canonical_mixing_families()[0]]["metrics"]["quality_q"]["mean"])
    cells = {}
    any_negative = False
    for family in canonical_mixing_families():
        quality_q = float(aggregates[family]["metrics"]["quality_q"]["mean"])
        delta = quality_q - baseline
        negative = delta < 0.0
        any_negative = any_negative or negative
        cells[family] = {
            "quality_q_delta_vs_spiral": delta,
            "negative_result": negative,
        }
    return {
        "baseline_family": canonical_mixing_families()[0],
        "comparison_metric": "quality_q_delta_vs_spiral",
        "any_negative_result": any_negative,
        "cells": cells,
    }


def _applicability_boundary() -> dict[str, Any]:
    return {
        "latent_family": "gaussian",
        "latent_dim": 2,
        "transition_family": "ornstein-uhlenbeck",
        "transition_noise_family": "gaussian",
        "mixing_families": list(canonical_mixing_families()),
        "claimed_scope": "Gaussian 2D latent + Gaussian OU transition + canonical nonlinear observation mixing families.",
        "not_claimed": "This sweep does not claim non-Gaussian latent coverage, non-Gaussian transition noise, or non-canonical mixing closure.",
    }


def _payload(records: list[dict[str, Any]], seeds: list[int]) -> dict[str, Any]:
    aggregates = _aggregate(records)
    observed = [
        str(record["source_mixing"])
        for record in records
        if record["status"] == "ok"
    ]
    return {
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "config": {
            "seed_base": SEED_BASE,
            "seed_count": SEED_COUNT,
            "seed_floor": SEED_COUNT,
            "seeds": seeds,
            "sample_count": SAMPLE_COUNT,
            "rho": RHO,
            "families": list(canonical_mixing_families()),
            "metric_names": list(METRIC_NAMES),
            "use_torch": False,
        },
        "source_artifacts": {
            "mixing_surface": "bedc_quality_lab/mixing.py",
            "toy_world_surface": "bedc_quality_lab/toy_world.py",
            "canonical_runner": "scripts/run_gaussian_ou_lejepa.py",
            "debt_scorer": "bedc_quality_lab/debt.py",
            "cost_protocol": "configs/default_cost_protocol.yaml",
        },
        "applicability_boundary": _applicability_boundary(),
        "records": records,
        "family_aggregates": aggregates,
        "coverage_item": _coverage_item(observed),
        "negative_result_summary": _negative_result_summary(aggregates),
    }


def _render_markdown(payload: dict[str, Any]) -> str:
    lines = [
        "# Canonical nonlinear mixing-family sweep",
        "",
        f"- Generated at: `{payload['generated_at']}`",
        f"- Seed count: `{payload['config']['seed_count']}`",
        f"- Seed floor: `{payload['config']['seed_floor']}`",
        f"- Sample count: `{payload['config']['sample_count']}`",
        f"- Rho: `{payload['config']['rho']}`",
        f"- Families: `{', '.join(payload['config']['families'])}`",
        "- Runner mode: `use_torch=False`",
        "",
        "## Coverage item",
        "",
        f"- Row: `{payload['coverage_item']['kind']}/{payload['coverage_item']['residue']}`",
        f"- Covered: `{', '.join(payload['coverage_item']['covered_families'])}`",
        f"- Missing: `{', '.join(payload['coverage_item']['missing_families'])}`",
        f"- Status: `{payload['coverage_item']['debt_item']['status']}`",
        f"- Score: `{payload['coverage_item']['debt_item']['score']}`",
        "",
        "## Family aggregates",
        "",
        "| family | ok count | seeds | linear R2 mean | proxy mean | quality_q mean | debt mean | bound margin mean |",
        "| --- | ---: | --- | ---: | ---: | ---: | ---: | ---: |",
    ]
    for family in payload["config"]["families"]:
        aggregate = payload["family_aggregates"][family]
        metrics = aggregate["metrics"]
        lines.append(
            "| "
            f"`{family}` | {aggregate['ok_count']} | "
            f"`{', '.join(str(seed) for seed in aggregate['seeds'])}` | "
            f"{_format_float(float(metrics['linear_identifiability_r2']['mean']))} | "
            f"{_format_float(float(metrics['approx_identifiability_proxy']['mean']))} | "
            f"{_format_float(float(metrics['quality_q']['mean']))} | "
            f"{_format_float(float(metrics['quality_debt']['mean']))} | "
            f"{_format_float(float(metrics['bound_margin']['mean']))} |"
        )
    lines.extend(
        [
            "",
            "## Negative-result audit",
            "",
            "| family | quality_q delta vs spiral | negative result |",
            "| --- | ---: | --- |",
        ]
    )
    for family, cell in payload["negative_result_summary"]["cells"].items():
        lines.append(
            "| "
            f"`{family}` | {_format_float(float(cell['quality_q_delta_vs_spiral']))} | "
            f"`{cell['negative_result']}` |"
        )
    lines.extend(
        [
            "",
            "## Applicability boundary",
            "",
            f"- Claimed scope: `{payload['applicability_boundary']['claimed_scope']}`",
            f"- Not claimed: {payload['applicability_boundary']['not_claimed']}",
            "",
        ]
    )
    return "\n".join(lines)


def _write_payload(payload: dict[str, Any]) -> None:
    REPORT_JSON.parent.mkdir(parents=True, exist_ok=True)
    REPORT_JSON.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    REPORT_MD.write_text(_render_markdown(payload), encoding="utf-8")


def main() -> None:
    seeds = _derive_seeds(SEED_BASE, SEED_COUNT)
    records = [
        _run_record(mixing=family, seed=seed, sample_count=SAMPLE_COUNT)
        for family in canonical_mixing_families()
        for seed in seeds
    ]
    _write_payload(_payload(records, seeds))
    print(f"wrote {REPORT_JSON.relative_to(ROOT)}")
    print(f"wrote {REPORT_MD.relative_to(ROOT)}")


if __name__ == "__main__":
    main()

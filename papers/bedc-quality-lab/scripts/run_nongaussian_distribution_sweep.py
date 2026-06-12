#!/usr/bin/env python3
"""Run the canonical latent distribution observed-debt sweep."""

from __future__ import annotations

from datetime import datetime, timezone
import json
import math
from pathlib import Path
import statistics
import sys
from typing import Any

import numpy as np


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.debt import assess_debt, format_debt_items
from bedc_quality_lab.identifiability_bound import identifiability_bound_metrics
from bedc_quality_lab.latent_distribution import (
    CANONICAL_LATENT_DISTRIBUTION_ARMS,
    CANONICAL_LATENT_DISTRIBUTION_KEYS,
    LatentDistributionSpec,
    covered_distribution_family_keys,
)
from bedc_quality_lab.ledger import derive_ledger_gaps, format_ledger_gaps
from bedc_quality_lab.metrics import metric_bundle, quality_components_from_bound
from bedc_quality_lab.mixing import DEFAULT_MIXING
from bedc_quality_lab.schema import SCHEMA_ID, QualityEvidenceEnvelope
from bedc_quality_lab.theorem_bound_quality import theorem_bound_certificate
from bedc_quality_lab.toy_world import make_toy_batch
from bedc_quality_lab.transition import TransitionKernelSpec
from scripts.run_gaussian_ou_lejepa import _fallback_encoder, _index_checksum, _train_eval_split


SEED_BASE = 544
SEED_COUNT = 6
SAMPLE_COUNT = 384
RHO = 0.82
BOOTSTRAP_COUNT = 199
MIN_R2_DROP = 0.01
JSON_ARTIFACT = "reports/canonical/nongaussian-distribution-sweep.json"
REPORT_ARTIFACT = "reports/canonical/nongaussian-distribution-sweep.md"
REPORT_JSON = ROOT / JSON_ARTIFACT
REPORT_MD = ROOT / REPORT_ARTIFACT
METRIC_NAMES = (
    "linear_identifiability_r2",
    "actual_recovery_mse",
    "theorem3_bound_mse",
    "quality_q",
    "quality_debt",
    "bound_margin_mse",
)


def derive_seeds(base_seed: int = SEED_BASE, count: int = SEED_COUNT) -> list[int]:
    return [int(base_seed + 977 * index + 37 * index * index) for index in range(count)]


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


def _debt_item(debt_items: list[str], residue: str) -> dict[str, str]:
    matches = [
        _parse_debt_item(item)
        for item in debt_items
        if "kind=source;" in item and f"residue={residue};" in item
    ]
    if len(matches) != 1:
        raise ValueError(f"expected exactly one {residue} debt item")
    return matches[0]


def _source_projection(
    spec: LatentDistributionSpec,
    batch_size: int,
    transition_source: dict[str, object],
) -> dict[str, object]:
    latent_projection = spec.to_source_spec()
    return {
        "name": "latent-distribution-toy-world",
        "latent_dim": spec.latent_dim,
        "sample_count": int(batch_size),
        "source_count": len(CANONICAL_LATENT_DISTRIBUTION_KEYS),
        "rho": RHO,
        "rho_by_axis": list(transition_source["rho_by_axis"]),
        "latent_distribution": latent_projection,
        "latent_distribution_family": latent_projection["family"],
        "latent_distribution_shape_parameter": latent_projection["shape_parameter"],
        "latent_distribution_coverage_keys": list(CANONICAL_LATENT_DISTRIBUTION_KEYS),
        "mixing": DEFAULT_MIXING,
        "transition_kernel": transition_source,
        "transition_isotropic": transition_source["isotropic"],
        "transition_anisotropy_gap": transition_source["anisotropy_gap"],
        "global_claim": False,
    }


def run_arm_record(
    spec: LatentDistributionSpec,
    *,
    seed: int,
    sample_count: int = SAMPLE_COUNT,
) -> dict[str, Any]:
    transition = TransitionKernelSpec.isotropic(RHO, latent_dim=spec.latent_dim)
    batch = make_toy_batch(
        sample_count,
        rho=RHO,
        seed=seed,
        transition_kernel=transition,
        mixing=DEFAULT_MIXING,
        latent_distribution=spec,
    )
    train_idx, eval_idx = _train_eval_split(batch.z.shape[0], seed=seed)
    train_x = batch.x[train_idx]
    eval_x = batch.x[eval_idx]
    eval_x_pair = batch.x_pair[eval_idx]
    eval_z = batch.z[eval_idx]
    h, h_pair = _fallback_encoder(train_x, eval_x, eval_x_pair)
    metrics = {
        **metric_bundle(h, eval_z),
        **identifiability_bound_metrics(h, h_pair, eval_z, RHO),
    }
    certificate = theorem_bound_certificate(metrics)
    transition_source = transition.to_source_spec()
    source_spec = _source_projection(spec, batch.z.shape[0], transition_source)
    classifier_spec = {
        "name": "standardized-nonlinear-observation",
        "output_dim": 2,
        "training": "deterministic-standardization",
        "split_policy": "train-eval-disjoint",
        "train_fraction": 0.70,
        "train_count": int(train_idx.shape[0]),
        "eval_count": int(eval_idx.shape[0]),
        "train_index_checksum": _index_checksum(train_idx),
        "eval_index_checksum": _index_checksum(eval_idx),
        "overlap_count": int(np.intersect1d(train_idx, eval_idx).shape[0]),
        **certificate,
    }
    stability_spec = {
        "name": "paired-seed-latent-distribution-sweep",
        "seed": seed,
        "pair_process": "ornstein-uhlenbeck",
        "paired_seed_id": seed,
        "transition_noise_family": transition.noise_family,
        "transition_eigenvalue_interleaving": transition_source["eigenvalue_interleaving"],
        "multi_seed": True,
    }
    debt_assessment = assess_debt(metrics, source_spec, classifier_spec, stability_spec)
    metrics = {
        **metrics,
        **quality_components_from_bound(metrics, debt_assessment.debt_total, classifier_spec),
    }
    ledger_gaps = derive_ledger_gaps(
        metrics,
        source_spec,
        classifier_spec,
        stability_spec,
        debt_assessment,
    )
    envelope = QualityEvidenceEnvelope(
        schema_id=SCHEMA_ID,
        run_id=f"latent-distribution-{spec.distribution_family_key()}-seed-{seed}",
        source_spec=source_spec,
        pattern_spec={
            "name": "latent-linear-recovery",
            "target": "recover z from representation h by linear least squares",
        },
        classifier_spec=classifier_spec,
        stability_spec=stability_spec,
        metrics=metrics,
        ledger_gaps=format_ledger_gaps(ledger_gaps),
        debt_items=format_debt_items(debt_assessment),
        artifacts={
            "envelope": JSON_ARTIFACT,
            "report": REPORT_ARTIFACT,
        },
        bedc_refs=[
            "LeJEPA Theorem 2 latent non-Gaussian identifiability caveat",
            "papers/bedc/parts/project_governance/theory_amendment_policy.tex",
        ],
    )
    latent_debt = _debt_item(envelope.debt_items, "latent-distribution-gaussianity")
    coverage_debt = _debt_item(envelope.debt_items, "distribution-family-coverage")
    return {
        "distribution": spec.family,
        "shape_parameter": spec.shape_parameter,
        "distribution_key": spec.distribution_family_key(),
        "report_label": spec.report_label(),
        "seed": seed,
        "paired_seed_id": seed,
        "sample_count": sample_count,
        "linear_identifiability_r2": float(metrics["linear_identifiability_r2"]),
        "actual_recovery_mse": float(metrics["actual_recovery_mse"]),
        "theorem3_bound_mse": float(metrics["theorem3_bound_mse"]),
        "latent_distribution_debt": float(latent_debt["score"]),
        "quality_q": float(metrics["quality_q"]),
        "not_claimed": "No universal non-Gaussian failure claim; this cell is an observed finite-sample debt record.",
        "debt_items": envelope.debt_items,
        "ledger_gaps": envelope.ledger_gaps,
        "source_spec": envelope.source_spec,
        "classifier_spec": envelope.classifier_spec,
        "stability_spec": envelope.stability_spec,
        "metrics": {name: float(metrics[name]) for name in METRIC_NAMES},
        "latent_distribution_debt_item": latent_debt,
        "distribution_family_coverage_debt_item": coverage_debt,
    }


def _aggregate(records: list[dict[str, Any]]) -> dict[str, Any]:
    aggregates: dict[str, Any] = {}
    for spec in CANONICAL_LATENT_DISTRIBUTION_ARMS:
        key = spec.distribution_family_key()
        selected = [record for record in records if record["distribution_key"] == key]
        aggregates[key] = {
            "distribution": spec.family,
            "shape_parameter": spec.shape_parameter,
            "report_label": spec.report_label(),
            "ok_count": len(selected),
            "seeds": [int(record["seed"]) for record in selected],
            "metrics": {
                name: _metric_stats([float(record[name]) for record in selected])
                for name in (
                    "linear_identifiability_r2",
                    "actual_recovery_mse",
                    "theorem3_bound_mse",
                    "latent_distribution_debt",
                    "quality_q",
                )
            },
        }
    return aggregates


def _bootstrap_ci(values: list[float], *, seed: int = 90544) -> dict[str, Any]:
    if len(values) < 2:
        return {"supported": False, "reason": "paired bootstrap requires at least two paired seeds"}
    rng = np.random.default_rng(seed)
    arr = np.asarray(values, dtype=np.float64)
    means = []
    for _ in range(BOOTSTRAP_COUNT):
        indices = rng.integers(0, arr.shape[0], size=arr.shape[0])
        means.append(float(np.mean(arr[indices])))
    low, high = np.percentile(np.asarray(means), [2.5, 97.5])
    return {
        "supported": True,
        "method": "paired-bootstrap-mean-delta",
        "bootstrap_count": BOOTSTRAP_COUNT,
        "mean_delta": float(np.mean(arr)),
        "ci95": [float(low), float(high)],
        "supports_gaussian_optimality": bool(high < (-MIN_R2_DROP - 1.0e-12)),
    }


def _claim_gate(records: list[dict[str, Any]]) -> dict[str, Any]:
    gaussian = {
        int(record["paired_seed_id"]): float(record["linear_identifiability_r2"])
        for record in records
        if record["distribution_key"] == "gaussian"
    }
    cells: dict[str, Any] = {}
    supported_cells = []
    for spec in CANONICAL_LATENT_DISTRIBUTION_ARMS:
        key = spec.distribution_family_key()
        if key == "gaussian":
            continue
        selected = {
            int(record["paired_seed_id"]): float(record["linear_identifiability_r2"])
            for record in records
            if record["distribution_key"] == key
        }
        paired = sorted(set(gaussian) & set(selected))
        deltas = [selected[seed] - gaussian[seed] for seed in paired]
        ci = _bootstrap_ci(deltas)
        supports = bool(ci.get("supported") is True and ci.get("supports_gaussian_optimality") is True)
        if supports:
            supported_cells.append(key)
        cells[key] = {
            "paired_seed_ids": paired,
            "comparison": "non_gaussian_minus_gaussian_linear_identifiability_r2",
            "deltas": deltas,
            "ci": ci,
            "supports_gaussian_optimality": supports,
        }
    all_supported = len(supported_cells) == len(CANONICAL_LATENT_DISTRIBUTION_ARMS) - 1
    return {
        "status": "gaussian-optimality-supported" if all_supported else "observed-debt-pipeline-only",
        "supporting_cells": supported_cells,
        "minimum_r2_drop": MIN_R2_DROP,
        "cells": cells,
        "not_claimed": (
            "Gaussian optimality is not asserted unless every non-Gaussian arm has a supported paired-bootstrap R2 drop."
        ),
    }


def _negative_result_ledger(records: list[dict[str, Any]]) -> list[dict[str, Any]]:
    gaussian = {
        int(record["paired_seed_id"]): float(record["linear_identifiability_r2"])
        for record in records
        if record["distribution_key"] == "gaussian"
    }
    entries = []
    for spec in CANONICAL_LATENT_DISTRIBUTION_ARMS:
        key = spec.distribution_family_key()
        if key == "gaussian":
            continue
        selected = {
            int(record["paired_seed_id"]): float(record["linear_identifiability_r2"])
            for record in records
            if record["distribution_key"] == key
        }
        paired = sorted(set(gaussian) & set(selected))
        no_drop = [
            seed
            for seed in paired
            if selected[seed] >= gaussian[seed] - MIN_R2_DROP
        ]
        if no_drop:
            entries.append(
                {
                    "distribution_key": key,
                    "report_label": spec.report_label(),
                    "criterion": "non_gaussian_r2 >= gaussian_r2 - minimum_r2_drop",
                    "minimum_r2_drop": MIN_R2_DROP,
                    "paired_seed_ids": no_drop,
                    "not_claimed": "This cell is not evidence for a Gaussian optimality claim.",
                }
            )
    return entries


def _coverage_item(records: list[dict[str, Any]]) -> dict[str, Any]:
    observed = [
        record["source_spec"]["latent_distribution"]
        for record in records
    ]
    covered = list(covered_distribution_family_keys({"latent_distribution": observed}))
    missing = [key for key in CANONICAL_LATENT_DISTRIBUTION_KEYS if key not in covered]
    source_spec = dict(records[0]["source_spec"])
    source_spec["latent_distribution"] = observed
    source_spec["source_count"] = len(CANONICAL_LATENT_DISTRIBUTION_KEYS)
    source_spec["sample_count"] = 2048
    metrics = {
        "theorem3_bound_mse": 1.0,
        "actual_recovery_mse": 0.0,
        "bound_margin_mse": 1.0,
        "normalized_gap_d_mse": 0.0,
        "whitening_deviation_epsilon": 0.0,
    }
    classifier_spec = {"name": "certified-search", "training": "certified"}
    stability_spec = {"multi_seed": True}
    assessment = assess_debt(metrics, source_spec, classifier_spec, stability_spec)
    item = _debt_item(format_debt_items(assessment), "distribution-family-coverage")
    return {
        "kind": "source",
        "residue": "distribution-family-coverage",
        "canonical_distribution_keys": list(CANONICAL_LATENT_DISTRIBUTION_KEYS),
        "covered_distribution_keys": covered,
        "missing_distribution_keys": missing,
        "debt_item": item,
    }


def _payload(records: list[dict[str, Any]], seeds: list[int]) -> dict[str, Any]:
    claim_gate = _claim_gate(records)
    return {
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "config": {
            "seed_base": SEED_BASE,
            "seed_count": SEED_COUNT,
            "seeds": seeds,
            "sample_count": SAMPLE_COUNT,
            "rho": RHO,
            "arms": [spec.to_source_spec() for spec in CANONICAL_LATENT_DISTRIBUTION_ARMS],
            "metric_names": list(METRIC_NAMES),
            "use_torch": False,
        },
        "source_artifacts": {
            "latent_distribution_surface": "bedc_quality_lab/latent_distribution.py",
            "toy_world_surface": "bedc_quality_lab/toy_world.py",
            "encoder_split_surface": "scripts/run_gaussian_ou_lejepa.py",
            "debt_scorer": "bedc_quality_lab/debt.py",
            "cost_protocol": "configs/default_cost_protocol.yaml",
        },
        "records": records,
        "family_aggregates": _aggregate(records),
        "coverage_item": _coverage_item(records),
        "claim_gate": claim_gate,
        "main_claim_status": claim_gate["status"],
        "negative_result_ledger": _negative_result_ledger(records),
        "not_claimed": (
            "The report records observed latent-distribution debt for a finite toy setting and does not claim broad non-Gaussian failure."
        ),
    }


def _render_markdown(payload: dict[str, Any]) -> str:
    lines = [
        "# Canonical latent distribution observed-debt sweep",
        "",
        f"- Generated at: `{payload['generated_at']}`",
        f"- Seed count: `{payload['config']['seed_count']}`",
        f"- Sample count: `{payload['config']['sample_count']}`",
        f"- Rho: `{payload['config']['rho']}`",
        f"- Main claim status: `{payload['main_claim_status']}`",
        f"- Not claimed: {payload['not_claimed']}",
        "",
        "## Coverage item",
        "",
        f"- Row: `{payload['coverage_item']['kind']}/{payload['coverage_item']['residue']}`",
        f"- Covered: `{', '.join(payload['coverage_item']['covered_distribution_keys'])}`",
        f"- Missing: `{', '.join(payload['coverage_item']['missing_distribution_keys'])}`",
        f"- Status: `{payload['coverage_item']['debt_item']['status']}`",
        f"- Score: `{payload['coverage_item']['debt_item']['score']}`",
        "",
        "## Distribution aggregates",
        "",
        "| distribution | shape_parameter | linear_identifiability_r2 | actual_recovery_mse | theorem3_bound_mse | latent_distribution_debt | quality_q |",
        "| --- | ---: | ---: | ---: | ---: | ---: | ---: |",
    ]
    for arm in payload["config"]["arms"]:
        key = arm["coverage_key"]
        aggregate = payload["family_aggregates"][key]
        metrics = aggregate["metrics"]
        lines.append(
            "| "
            f"`{aggregate['distribution']}` | "
            f"`{aggregate['shape_parameter']}` | "
            f"{_format_float(float(metrics['linear_identifiability_r2']['mean']))} | "
            f"{_format_float(float(metrics['actual_recovery_mse']['mean']))} | "
            f"{_format_float(float(metrics['theorem3_bound_mse']['mean']))} | "
            f"{_format_float(float(metrics['latent_distribution_debt']['mean']))} | "
            f"{_format_float(float(metrics['quality_q']['mean']))} |"
        )
    lines.extend(
        [
            "",
            "## Claim gate",
            "",
            f"- Status: `{payload['claim_gate']['status']}`",
            f"- Minimum R2 drop: `{payload['claim_gate']['minimum_r2_drop']}`",
            f"- Not claimed: {payload['claim_gate']['not_claimed']}",
            "",
            "| distribution_key | mean delta | ci95 | supports Gaussian optimality |",
            "| --- | ---: | --- | --- |",
        ]
    )
    for key, cell in payload["claim_gate"]["cells"].items():
        ci = cell["ci"]
        if ci.get("supported") is True:
            ci_text = f"{_format_float(float(ci['ci95'][0]))}, {_format_float(float(ci['ci95'][1]))}"
            mean_delta = _format_float(float(ci["mean_delta"]))
        else:
            ci_text = str(ci.get("reason", "unsupported"))
            mean_delta = "nan"
        lines.append(
            "| "
            f"`{key}` | {mean_delta} | `{ci_text}` | "
            f"`{cell['supports_gaussian_optimality']}` |"
        )
    lines.extend(
        [
            "",
            "## Negative-result ledger",
            "",
            "| distribution_key | paired seeds | not claimed |",
            "| --- | --- | --- |",
        ]
    )
    for entry in payload["negative_result_ledger"]:
        lines.append(
            "| "
            f"`{entry['distribution_key']}` | "
            f"`{', '.join(str(seed) for seed in entry['paired_seed_ids'])}` | "
            f"{entry['not_claimed']} |"
        )
    if not payload["negative_result_ledger"]:
        lines.append("| `none` | `` | `all non-Gaussian arms decreased beyond the ledger threshold` |")
    lines.append("")
    return "\n".join(lines)


def _write_payload(payload: dict[str, Any]) -> None:
    REPORT_JSON.parent.mkdir(parents=True, exist_ok=True)
    REPORT_JSON.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    REPORT_MD.write_text(_render_markdown(payload), encoding="utf-8")


def main() -> None:
    seeds = derive_seeds()
    records = [
        run_arm_record(spec, seed=seed, sample_count=SAMPLE_COUNT)
        for seed in seeds
        for spec in CANONICAL_LATENT_DISTRIBUTION_ARMS
    ]
    _write_payload(_payload(records, seeds))
    print(f"wrote {REPORT_JSON.relative_to(ROOT)}")
    print(f"wrote {REPORT_MD.relative_to(ROOT)}")


if __name__ == "__main__":
    main()

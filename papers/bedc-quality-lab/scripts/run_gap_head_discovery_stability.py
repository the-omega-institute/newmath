#!/usr/bin/env python3
"""Measure gap-head discovery verdict stability over an independent seed grid."""

from collections import Counter
from datetime import datetime, timezone
import hashlib, json, math, sys, time
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.experiment_stats import metric_stats
from scripts import run_gap_head_discovery as discovery
from scripts import run_gap_ledger_head_on_h as producer

JSON_ARTIFACT, REPORT_ARTIFACT = "reports/gap_head_discovery_stability.json", "reports/gap_head_discovery_stability.md"
ARTIFACT_LABEL = "bedc-quality-lab:gap-head-discovery-stability"
SAMPLE_COUNTS, SEEDS_PER_SAMPLE_COUNT = (96, 192, 384, 768), 10
GRID_KIND, MASTER_SEED = "independent_seed_grid", 5270521
PREDICATE_BOUNDARY = {"projection_helper": "scripts/run_gap_head_discovery.py::_build_gap_head_projection", "verdict_helper": "scripts/run_gap_head_discovery.py::_verdict_payload", "direct_formula_reimplementation": False}
VERDICT_FIELDS = ("surface_delta_count", "shift_information", "net_information", "structural_discovery", "positive_discovery", "net_positive_signal", "non_discovery_reason")

def _child_seed(sample_count_index: int, seed_index: int) -> int:
    raw = f"{MASTER_SEED}:{GRID_KIND}:{sample_count_index}:{seed_index}".encode()
    return int.from_bytes(hashlib.sha256(raw).digest()[:8], "big") % (2**31 - 1)

def _cell_configs() -> list[tuple[int, int, producer.GapHeadRunConfig]]:
    rows = []
    for sample_i, sample_count in enumerate(SAMPLE_COUNTS):
        for seed_i in range(SEEDS_PER_SAMPLE_COUNT):
            seed = _child_seed(sample_i, seed_i)
            source = f"reports/gap_head_discovery_stability/source_payloads/sample-{sample_count}-seed-{seed}"
            rows.append((sample_i, seed_i, producer.GapHeadRunConfig(
                sample_count, (seed,), producer.DEFAULT_CONFIG.rho, producer.DEFAULT_CONFIG.use_torch,
                f"{source}.json", f"{source}.md", f"gap-head-discovery-stability-sample-{sample_count}",
                "gap-head-discovery-stability-cell", GRID_KIND,
            )))
    return rows

def _config_payload(config: producer.GapHeadRunConfig) -> dict[str, Any]:
    fields = ("sample_count", "rho", "use_torch", "json_artifact", "report_artifact", "run_id_prefix", "source_artifact_label", "seed_grid_kind")
    return {field: getattr(config, field) for field in fields} | {"seeds": list(config.seeds)}

def _run_cell(sample_i: int, seed_i: int, config: producer.GapHeadRunConfig) -> dict[str, Any]:
    base = {"sample_count": config.sample_count, "sample_count_index": sample_i, "seed_index": seed_i, "seed": int(config.seeds[0])}
    try:
        source_payload = producer._payload(producer._records(config), config)
        verdict = discovery._verdict_payload(discovery._build_gap_head_projection(source_payload))
        return base | {"source_payload_config": dict(source_payload["config"]), "source_artifacts": dict(verdict["source_artifacts"]), "boundary_checks": dict(verdict["boundary_checks"]), "valid_cell": True} | {key: verdict[key] for key in VERDICT_FIELDS}
    except Exception as error:
        return base | {
            "source_payload_config": _config_payload(config),
            "source_artifacts": {},
            "boundary_checks": {},
            "surface_delta_count": 0, "shift_information": 0.0, "net_information": 0.0,
            "structural_discovery": False, "positive_discovery": False, "net_positive_signal": False,
            "non_discovery_reason": f"invalid_cell:{type(error).__name__}",
            "valid_cell": False,
            "validation_error": str(error),
        }

def _stats(values: list[float]) -> dict[str, Any]:
    stats = metric_stats(values)
    return stats | {"variance": float(stats["std"]) ** 2}

def _sample_count_summary(sample_count: int, cells: list[dict[str, Any]]) -> dict[str, Any]:
    valid = [cell for cell in cells if cell["valid_cell"]]
    positive = [cell for cell in valid if cell["positive_discovery"]]
    reasons = Counter(
        str(cell["non_discovery_reason"])
        for cell in cells
        if not cell["positive_discovery"] and cell["non_discovery_reason"] is not None
    )
    return {
        "sample_count": sample_count,
        "cell_count": len(cells),
        "valid_cell_count": len(valid),
        "invalid_cell_count": len(cells) - len(valid),
        "positive_seed_count": len(positive),
        "positive_rate": 0.0 if not valid else len(positive) / len(valid),
        "seed_order": [int(cell["seed"]) for cell in cells],
        "non_discovery_reason_counts": dict(sorted(reasons.items())),
    } | {
        key: _stats([float(cell[key]) for cell in valid])
        for key in ("surface_delta_count", "shift_information", "net_information")
    }

def _aggregate(cells: list[dict[str, Any]]) -> dict[str, Any]:
    groups = [
        _sample_count_summary(sample_count, [cell for cell in cells if cell["sample_count"] == sample_count])
        for sample_count in SAMPLE_COUNTS
    ]
    valid = [cell for cell in cells if cell["valid_cell"]]
    return {
        "cell_count": len(cells),
        "valid_cell_count": len(valid),
        "invalid_cell_count": len(cells) - len(valid),
        "positive_cell_count": sum(1 for cell in valid if cell["positive_discovery"]),
        "sample_count_groups": groups,
        "positive_rate_by_sample_count": {str(group["sample_count"]): float(group["positive_rate"]) for group in groups},
        "positive_rate_variance_across_sample_counts": _stats([float(group["positive_rate"]) for group in groups])["variance"],
    }

def _final_verdict(aggregate: dict[str, Any]) -> str:
    groups = aggregate["sample_count_groups"]
    if aggregate["invalid_cell_count"] > 0:
        return "invalid_grid"
    if aggregate["positive_cell_count"] in (0, aggregate["cell_count"]):
        return "not_positive" if aggregate["positive_cell_count"] == 0 else "robust_positive"
    largest = groups[-1]
    if any(group["positive_seed_count"] > 0 for group in groups[:-1]) and (
        largest["positive_seed_count"] == 0 or float(largest["net_information"]["mean"]) <= 0.0
    ):
        return "finite_sample_artifact"
    if any(0 < group["positive_seed_count"] < group["valid_cell_count"] for group in groups):
        return "seed_dependent_or_noisy"
    return "not_positive"

def _payload(cells: list[dict[str, Any]], *, elapsed_seconds: float) -> dict[str, Any]:
    aggregate = _aggregate(cells)
    return {
        "artifact": ARTIFACT_LABEL,
        "json_artifact": JSON_ARTIFACT,
        "report": REPORT_ARTIFACT,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "elapsed_seconds": float(elapsed_seconds),
        "final_verdict": _final_verdict(aggregate),
        "grid": {"kind": GRID_KIND, "master_seed": MASTER_SEED, "sample_counts": list(SAMPLE_COUNTS), "seeds_per_sample_count": SEEDS_PER_SAMPLE_COUNT, "cell_shape": "one source payload per sample_count and child seed"},
        "producer_defaults": {"rho": producer.DEFAULT_CONFIG.rho, "use_torch": producer.DEFAULT_CONFIG.use_torch, "representation_boundary": producer.REPRESENTATION_BOUNDARY, "inference_no_ground_truth_z": producer.INFERENCE_NO_GROUND_TRUTH_Z},
        "predicate_boundary": PREDICATE_BOUNDARY,
        "aggregate": aggregate,
        "cells": cells,
    }

def _format_float(value: float) -> str:
    return "nan" if math.isnan(value) else f"{value:.6f}"

def _render_stats(stats: dict[str, Any]) -> str:
    return f"{_format_float(float(stats['mean']))} +/- {_format_float(float(stats['std']))} (95% CI +/- {_format_float(float(stats['ci95_half_width']))})"

def _render_report(payload: dict[str, Any]) -> str:
    lines = ["# Gap-Head Discovery Stability", ""]
    for label, value in [
        ("Artifact", payload["artifact"]),
        ("Generated at", payload["generated_at"]),
        ("Final verdict", payload["final_verdict"]),
        ("Backend use_torch", str(bool(payload["producer_defaults"]["use_torch"])).lower()),
        ("Elapsed seconds", _format_float(float(payload["elapsed_seconds"]))),
        ("Grid", payload["grid"]["kind"]),
        ("Cell shape", payload["grid"]["cell_shape"]),
        ("Sample counts", ", ".join(str(value) for value in payload["grid"]["sample_counts"])),
        ("Cells per sample count", payload["grid"]["seeds_per_sample_count"]),
        ("Total cells", payload["aggregate"]["cell_count"]),
        ("Invalid cells", payload["aggregate"]["invalid_cell_count"]),
    ]:
        lines.append(f"- {label}: `{value}`")
    lines += [
        "",
        "## Sample Counts",
        "",
        "| sample count | positive seeds | positive rate | mean net information | mean surface delta | mean shift information | invalid cells |",
        "| ---: | ---: | ---: | ---: | ---: | ---: | ---: |",
    ]
    for group in payload["aggregate"]["sample_count_groups"]:
        lines.append(
            f"| {group['sample_count']} | {group['positive_seed_count']}/{group['valid_cell_count']} | "
            f"{_format_float(float(group['positive_rate']))} | {_render_stats(group['net_information'])} | "
            f"{_render_stats(group['surface_delta_count'])} | {_render_stats(group['shift_information'])} | {group['invalid_cell_count']} |"
        )
    lines += [
        "",
        "## Boundary",
        "",
        f"- Representation boundary: `{payload['producer_defaults']['representation_boundary']}`",
        f"- Inference no ground-truth z: `{str(bool(payload['producer_defaults']['inference_no_ground_truth_z'])).lower()}`",
        f"- Projection helper: `{payload['predicate_boundary']['projection_helper']}`",
        f"- Verdict helper: `{payload['predicate_boundary']['verdict_helper']}`",
        "",
        "## Notes",
        "",
        "Each cell contains exactly one source seed, so `surface_delta_count` is expected to be smaller than the #521 30-record aggregate.",
        "Markdown values render from the JSON payload.",
        "",
    ]
    return "\n".join(lines)

def _write_payload(payload: dict[str, Any]) -> None:
    (ROOT / JSON_ARTIFACT).parent.mkdir(parents=True, exist_ok=True)
    (ROOT / JSON_ARTIFACT).write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    (ROOT / REPORT_ARTIFACT).write_text(_render_report(payload), encoding="utf-8")

def main() -> None:
    started = time.perf_counter()
    payload = _payload(
        [_run_cell(sample_i, seed_i, config) for sample_i, seed_i, config in _cell_configs()],
        elapsed_seconds=time.perf_counter() - started,
    )
    _write_payload(payload)
    print(f"wrote {JSON_ARTIFACT}")
    print(f"wrote {REPORT_ARTIFACT}")
    print(f"cells {len(payload['cells'])}")
    print(f"final_verdict {payload['final_verdict']}")

if __name__ == "__main__":
    main()

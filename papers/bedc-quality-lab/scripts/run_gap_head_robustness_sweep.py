#!/usr/bin/env python3
"""Run the gap-head-on-h robustness sweep as a thin owner orchestrator."""

from __future__ import annotations

from datetime import datetime, timezone
import json
import math
from pathlib import Path
import sys
import time
from typing import Any

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.experiment_stats import metric_stats
from scripts import run_anisotropic_ou_sweep as anisotropic_transfer
from scripts import run_gap_head_discovery_stability as stability
from scripts import run_gap_ledger_head_on_h as producer
from scripts import run_mixing_family_sweep as mixing_transfer
from scripts import run_nongaussian_distribution_sweep as nongaussian_transfer


JSON_ARTIFACT = "reports/canonical/gap-head-robustness-sweep.json"
REPORT_ARTIFACT = "reports/canonical/gap-head-robustness-sweep.md"
ARTIFACT_ID = "bedc-quality-lab:gap-head-robustness-sweep"
CLAIM_TEXT = "Gap classifiers can be learned on representations to reduce unlogged model errors."
TRANSFER_POINTERS = (
    {
        "name": "nongaussian-distribution-sweep",
        "script": "scripts/run_nongaussian_distribution_sweep.py",
        "json_artifact": nongaussian_transfer.JSON_ARTIFACT,
        "markdown_artifact": nongaussian_transfer.REPORT_ARTIFACT,
        "pointer": "$.main_claim_status",
    },
    {
        "name": "anisotropic-ou-sweep",
        "script": "scripts/run_anisotropic_ou_sweep.py",
        "json_artifact": "reports/canonical/anisotropic-ou-sweep.json",
        "markdown_artifact": "reports/canonical/anisotropic-ou-sweep.md",
        "pointer": "$.negative_result_summary",
    },
    {
        "name": "mixing-family-sweep",
        "script": "scripts/run_mixing_family_sweep.py",
        "json_artifact": "reports/canonical/mixing-family-sweep.json",
        "markdown_artifact": "reports/canonical/mixing-family-sweep.md",
        "pointer": "$.negative_result_summary",
    },
    {
        "name": "gaussian-ou-gap-ledger-shift-robustness",
        "script": "scripts/run_gaussian_ou_gap_ledger_shift_robustness.py",
        "json_artifact": "reports/gaussian_ou_gap_ledger_shift_robustness.json",
        "markdown_artifact": "reports/gaussian_ou_gap_ledger_shift_robustness.md",
        "pointer": "$.aggregate.advantage_degradation_slope",
    },
)
FEATURE_FAMILIES = {
    "full": ("h", "score", "margin", "transition_delta", "quality"),
    "h_only": ("h",),
    "probe_only": ("score", "margin", "transition_delta"),
    "no_quality": ("h", "score", "margin", "transition_delta"),
    "quality_only": ("quality",),
}
AUROC_POSITIVE_THRESHOLD = 0.75
MATCHED_RANDOM_AUROC_CEILING = 0.60
H_ONLY_AUROC_TOLERANCE = 0.03
H_ONLY_REDUCTION_TOLERANCE = 0.03


def _format_float(value: float) -> str:
    if math.isnan(value):
        return "nan"
    return f"{value:.6f}"


def _render_stats(stats: dict[str, Any]) -> str:
    return (
        f"{_format_float(float(stats['mean']))} +/- {_format_float(float(stats['std']))} "
        f"(95% CI +/- {_format_float(float(stats['ci95_half_width']))})"
    )


def _owner_pointers() -> dict[str, Any]:
    return {
        "a1_threshold_sweep": {
            "owner": "scripts/run_gap_ledger_head_on_h.py",
            "config": "scripts/run_gap_ledger_head_on_h.py::GapHeadRunConfig",
            "tau_grid": "scripts/run_gap_ledger_head_on_h.py::TAU_GRID",
            "epsilon_grid": "scripts/run_gap_ledger_head_on_h.py::EPSILON_GRID",
            "primary_tau": "scripts/run_gap_ledger_head_on_h.py::PRIMARY_TAU",
            "primary_epsilon": "scripts/run_gap_ledger_head_on_h.py::PRIMARY_EPSILON",
        },
        "a2_feature_ablation": {
            "surface": "scripts/run_gap_ledger_head_on_h.py::_surface_for_seed",
            "split": "scripts/run_gap_ledger_head_on_h.py::_run_record",
            "matched_random": "scripts/run_gap_ledger_head_on_h.py::_matched_random_gap_labels",
            "metric_helper": "scripts/run_gaussian_ou_gap_ledger_head.py::_metrics_for_arm",
            "forbidden_audit": "scripts/run_gap_ledger_head_on_h.py::_assert_inference_columns",
        },
        "a3_seed_expansion": {
            "owner": "scripts/run_gap_head_discovery_stability.py",
            "cell_grid": "scripts/run_gap_head_discovery_stability.py::_cell_configs",
            "verdict": "scripts/run_gap_head_discovery.py::_verdict_payload",
        },
        "a4_distribution_transfer": [
            {
                "name": pointer["name"],
                "script": pointer["script"],
                "json_artifact": pointer["json_artifact"],
                "pointer": pointer["pointer"],
            }
            for pointer in TRANSFER_POINTERS
        ],
        "a5_no_leak_audit": {
            "forbidden_inference_columns": "scripts/run_gap_ledger_head_on_h.py::FORBIDDEN_INFERENCE_COLUMNS",
            "producer_audit": "scripts/run_gap_ledger_head_on_h.py::_forbidden_column_audit",
        },
    }


def _claim_boundary() -> dict[str, Any]:
    return {
        "claim": CLAIM_TEXT,
        "positive_scope": (
            "The claim is limited to the learned-h Gaussian-OU source surface and the "
            "explicit transfer pointers reported here."
        ),
        "not_claimed": [
            "No global quality claim.",
            "No claim over transfer surfaces without a listed pointer.",
            "No large-model extrapolation.",
            "No inference-time use of z, z_pair, gap_label, prediction_error, or eval_gap_labels.",
        ],
    }


def _stats_from_records(records: list[dict[str, Any]], getter: Any) -> dict[str, Any]:
    return metric_stats(float(getter(record)) for record in records)


def _reduction_stats(records: list[dict[str, Any]], arm: str) -> dict[str, Any]:
    return _stats_from_records(
        records,
        lambda record: float(record["arms"]["vanilla"]["unlogged_error_rate"])
        - float(record["arms"][arm]["unlogged_error_rate"]),
    )


def _a1_threshold_summary(source_payload: dict[str, Any]) -> dict[str, Any]:
    aggregate = source_payload["aggregate"]
    records = source_payload["records"]
    learned = "learned_gap_head_on_h"
    matched = producer.MATCHED_RANDOM_ARM
    return {
        "status": "complete",
        "owner": "scripts/run_gap_ledger_head_on_h.py",
        "json_artifact": "reports/canonical/gap-head-on-h.json",
        "report_artifact": "reports/canonical/gap-head-on-h.md",
        "sample_count": int(source_payload["config"]["sample_count"]),
        "seed_count": int(source_payload["config"]["seed_count"]),
        "record_count": int(aggregate["record_count"]),
        "tau_grid": list(source_payload["config"]["tau_grid"]),
        "epsilon_grid": list(source_payload["config"]["epsilon_grid"]),
        "primary_tau": float(source_payload["config"]["primary_tau"]),
        "primary_epsilon": float(source_payload["config"]["primary_epsilon"]),
        "threshold_scan_metadata": {
            "tau_grid": "$.config.tau_grid",
            "epsilon_grid": "$.config.epsilon_grid",
            "primary_gap_sound": "$.aggregate.by_arm.*.gap_sound_*",
        },
        "learned_gap_head_on_h": {
            "failure_detection_auroc": aggregate["by_arm"][learned]["failure_detection_auroc"],
            "unlogged_error_rate": aggregate["by_arm"][learned]["unlogged_error_rate"],
            "critical_unlogged_error_rate": aggregate["by_arm"][learned][
                "critical_unlogged_error_rate"
            ],
            "unlogged_error_reduction": _reduction_stats(records, learned),
        },
        "matched_random_gap_head": {
            "failure_detection_auroc": aggregate["by_arm"][matched]["failure_detection_auroc"],
            "unlogged_error_rate": aggregate["by_arm"][matched]["unlogged_error_rate"],
            "critical_unlogged_error_rate": aggregate["by_arm"][matched][
                "critical_unlogged_error_rate"
            ],
            "unlogged_error_reduction": _reduction_stats(records, matched),
        },
        "vanilla": {
            "failure_detection_auroc": aggregate["by_arm"]["vanilla"]["failure_detection_auroc"],
            "unlogged_error_rate": aggregate["by_arm"]["vanilla"]["unlogged_error_rate"],
            "critical_unlogged_error_rate": aggregate["by_arm"]["vanilla"][
                "critical_unlogged_error_rate"
            ],
        },
        "treatment_verdict": source_payload["treatment_verdict"],
        "control_verdict": source_payload["control_verdict"],
    }


def _family_roots(name: str) -> tuple[str, ...]:
    if name not in FEATURE_FAMILIES:
        raise ValueError(f"unknown feature family: {name}")
    return FEATURE_FAMILIES[name]


def _family_indices(columns: list[str], family: str) -> list[int]:
    roots = set(_family_roots(family))
    indices = [
        index
        for index, column in enumerate(columns)
        if column.split(":", 1)[0] in roots
    ]
    if not indices:
        raise ValueError(f"feature family has no columns: {family}")
    return indices


def _assert_no_forbidden_features(columns: list[str]) -> None:
    producer._assert_inference_columns(columns)
    forbidden = set(producer.FORBIDDEN_INFERENCE_COLUMNS)
    present = [
        column
        for column in columns
        if column in forbidden or column.split(":", 1)[0] in forbidden
    ]
    if present:
        raise ValueError(f"forbidden feature columns: {present}")


def _ablation_record(
    *,
    seed: int,
    seed_index: int,
    surface: dict[str, Any],
    family: str,
) -> dict[str, Any]:
    indices = _family_indices(list(surface["feature_columns"]), family)
    selected_columns = [surface["feature_columns"][index] for index in indices]
    _assert_no_forbidden_features(selected_columns)
    train_idx = surface["train_idx"]
    eval_idx = surface["eval_idx"]
    features = surface["features"][:, indices]
    labels = surface["gap_labels"]
    heads = producer._fit_gap_head(features[train_idx], labels[train_idx])
    probabilities = producer._predict_gap_head(heads, features[eval_idx])
    randomized_labels = producer._matched_random_gap_labels(labels, seed=seed)
    random_heads = producer._fit_gap_head(features[train_idx], randomized_labels[train_idx])
    random_probabilities = producer._predict_gap_head(random_heads, features[eval_idx])
    eval_labels = labels[eval_idx]
    eval_error = surface["prediction_error"][eval_idx]
    vanilla = producer._metrics_for_arm(
        arm="vanilla",
        probabilities=np.zeros_like(probabilities, dtype=np.float64),
        labels=eval_labels,
        prediction_error=eval_error,
    )
    learned = producer._metrics_for_arm(
        arm=f"{family}_gap_head",
        probabilities=probabilities,
        labels=eval_labels,
        prediction_error=eval_error,
    )
    matched = producer._metrics_for_arm(
        arm=f"{family}_matched_random_gap_head",
        probabilities=random_probabilities,
        labels=eval_labels,
        prediction_error=eval_error,
    )
    return {
        "seed": int(seed),
        "seed_index": int(seed_index),
        "feature_family": family,
        "feature_roots": list(_family_roots(family)),
        "feature_column_count": int(len(selected_columns)),
        "forbidden_feature_audit": {
            "status": "pass",
            "forbidden_inference_columns": list(producer.FORBIDDEN_INFERENCE_COLUMNS),
            "forbidden_present": [],
        },
        "arms": {
            "vanilla": producer._metric_projection(vanilla),
            "learned": producer._metric_projection(learned),
            "matched_random": producer._metric_projection(matched),
        },
        "comparison": {
            "unlogged_error_reduction_learned": float(
                vanilla["unlogged_error_rate"] - learned["unlogged_error_rate"]
            ),
            "unlogged_error_reduction_matched_random": float(
                vanilla["unlogged_error_rate"] - matched["unlogged_error_rate"]
            ),
            "failure_detection_auroc_delta_learned_minus_matched_random": float(
                learned["failure_detection_auroc"]["value"]
                - matched["failure_detection_auroc"]["value"]
            ),
        },
    }


def _family_aggregate(records: list[dict[str, Any]]) -> dict[str, Any]:
    if not records:
        raise ValueError("feature family records must not be empty")
    return {
        "record_count": int(len(records)),
        "feature_roots": list(records[0]["feature_roots"]),
        "feature_column_count": int(records[0]["feature_column_count"]),
        "forbidden_feature_audit": {
            "status": "pass"
            if all(record["forbidden_feature_audit"]["status"] == "pass" for record in records)
            else "fail",
            "forbidden_present": sorted(
                {
                    column
                    for record in records
                    for column in record["forbidden_feature_audit"]["forbidden_present"]
                }
            ),
        },
        "learned": {
            "failure_detection_auroc": _stats_from_records(
                records, lambda record: record["arms"]["learned"]["failure_detection_auroc"]["value"]
            ),
            "unlogged_error_rate": _stats_from_records(
                records, lambda record: record["arms"]["learned"]["unlogged_error_rate"]
            ),
            "unlogged_error_reduction": _stats_from_records(
                records, lambda record: record["comparison"]["unlogged_error_reduction_learned"]
            ),
        },
        "matched_random": {
            "failure_detection_auroc": _stats_from_records(
                records,
                lambda record: record["arms"]["matched_random"]["failure_detection_auroc"]["value"],
            ),
            "unlogged_error_rate": _stats_from_records(
                records, lambda record: record["arms"]["matched_random"]["unlogged_error_rate"]
            ),
            "unlogged_error_reduction": _stats_from_records(
                records,
                lambda record: record["comparison"]["unlogged_error_reduction_matched_random"],
            ),
        },
        "learned_minus_matched_random_auroc": _stats_from_records(
            records,
            lambda record: record["comparison"][
                "failure_detection_auroc_delta_learned_minus_matched_random"
            ],
        ),
    }


def _run_ablation_sweep(config: producer.GapHeadRunConfig) -> dict[str, Any]:
    by_family_records: dict[str, list[dict[str, Any]]] = {
        family: [] for family in FEATURE_FAMILIES
    }
    for seed_index, seed in enumerate(config.seeds):
        surface = producer._surface_for_seed(seed=int(seed), config=config)
        for family in FEATURE_FAMILIES:
            by_family_records[family].append(
                _ablation_record(
                    seed=int(seed),
                    seed_index=seed_index,
                    surface=surface,
                    family=family,
                )
            )
    by_family = {
        family: _family_aggregate(records)
        for family, records in by_family_records.items()
    }
    return {
        "status": "complete",
        "owner": "scripts/run_gap_ledger_head_on_h.py",
        "surface_owner": "scripts/run_gap_ledger_head_on_h.py::_surface_for_seed",
        "metric_helper": "scripts/run_gaussian_ou_gap_ledger_head.py::_metrics_for_arm",
        "sample_count": int(config.sample_count),
        "seed_count": int(len(config.seeds)),
        "feature_families": {
            family: list(roots) for family, roots in FEATURE_FAMILIES.items()
        },
        "by_family": by_family,
    }


def _run_stability_sweep() -> dict[str, Any]:
    started = time.perf_counter()
    cells = [
        stability._run_cell(sample_i, seed_i, config)
        for sample_i, seed_i, config in stability._cell_configs()
    ]
    payload = stability._payload(cells, elapsed_seconds=time.perf_counter() - started)
    return {
        "status": "complete",
        "owner": "scripts/run_gap_head_discovery_stability.py",
        "json_artifact": stability.JSON_ARTIFACT,
        "report_artifact": stability.REPORT_ARTIFACT,
        "final_verdict": payload["final_verdict"],
        "grid": payload["grid"],
        "aggregate": payload["aggregate"],
        "predicate_boundary": payload["predicate_boundary"],
    }


def _load_json_artifact(relative_path: str) -> dict[str, Any] | None:
    path = ROOT / relative_path
    if not path.exists():
        return None
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return None
    return value if isinstance(value, dict) else None


def _pointer_value(payload: dict[str, Any], pointer: str) -> Any:
    if not pointer.startswith("$."):
        return None
    cursor: Any = payload
    for part in pointer[2:].split("."):
        if isinstance(cursor, dict) and part in cursor:
            cursor = cursor[part]
        else:
            return None
    return cursor


def _compact_pointer_value(value: Any) -> Any:
    if isinstance(value, (str, int, float, bool)) or value is None:
        return value
    if isinstance(value, list):
        return {
            "kind": "list",
            "count": len(value),
        }
    if isinstance(value, dict):
        compact: dict[str, Any] = {"kind": "dict", "keys": sorted(value.keys())}
        for key in (
            "status",
            "main_claim_status",
            "any_negative_result",
            "slope",
            "slope_ci95_low",
            "slope_ci95_high",
        ):
            if key in value and isinstance(value[key], (str, int, float, bool)):
                compact[key] = value[key]
        if "cells" in value and isinstance(value["cells"], dict):
            compact["cell_count"] = len(value["cells"])
            compact["negative_cell_count"] = sum(
                1
                for cell in value["cells"].values()
                if isinstance(cell, dict) and cell.get("negative_result") is True
            )
        return compact
    return str(type(value).__name__)


def _transfer_pointer_summary() -> dict[str, Any]:
    surfaces = []
    for pointer in TRANSFER_POINTERS:
        payload = _load_json_artifact(str(pointer["json_artifact"]))
        value = None if payload is None else _pointer_value(payload, str(pointer["pointer"]))
        surfaces.append(
            {
                "name": pointer["name"],
                "status": "available" if payload is not None else "missing",
                "script": pointer["script"],
                "json_artifact": pointer["json_artifact"],
                "markdown_artifact": pointer["markdown_artifact"],
                "pointer": pointer["pointer"],
                "pointer_value_summary": _compact_pointer_value(value),
            }
        )
    return {
        "status": "complete",
        "policy": "pointer_only_existing_transfer_surfaces_no_retraining",
        "surfaces": surfaces,
    }


def _a5_no_leak_audit(source_payload: dict[str, Any], ablation: dict[str, Any]) -> dict[str, Any]:
    producer_audit = source_payload["forbidden_column_audit"]
    ablation_failures = [
        family
        for family, row in ablation["by_family"].items()
        if row["forbidden_feature_audit"]["status"] != "pass"
    ]
    return {
        "status": "pass"
        if producer_audit["status"] == "pass" and not ablation_failures
        else "fail",
        "producer_forbidden_column_audit": producer_audit,
        "forbidden_inference_columns": list(producer.FORBIDDEN_INFERENCE_COLUMNS),
        "ablation_failed_families": ablation_failures,
        "assertion_helpers": [
            "scripts/run_gap_ledger_head_on_h.py::_assert_inference_columns",
            "scripts/run_gap_head_robustness_sweep.py::_assert_no_forbidden_features",
        ],
    }


def _mechanism_label(ablation: dict[str, Any]) -> dict[str, Any]:
    full = ablation["by_family"]["full"]["learned"]
    h_only = ablation["by_family"]["h_only"]["learned"]
    full_auroc = float(full["failure_detection_auroc"]["mean"])
    h_auroc = float(h_only["failure_detection_auroc"]["mean"])
    full_reduction = float(full["unlogged_error_reduction"]["mean"])
    h_reduction = float(h_only["unlogged_error_reduction"]["mean"])
    h_only_sufficient = (
        h_auroc >= full_auroc - H_ONLY_AUROC_TOLERANCE
        and h_reduction >= full_reduction - H_ONLY_REDUCTION_TOLERANCE
    )
    return {
        "status": "pass",
        "h_only_sufficient": bool(h_only_sufficient),
        "mechanical_label": (
            "h_boundary_gap_classifier"
            if h_only_sufficient
            else "full_feature_family_gap_classifier"
        ),
        "criterion": {
            "auroc_tolerance": H_ONLY_AUROC_TOLERANCE,
            "unlogged_error_reduction_tolerance": H_ONLY_REDUCTION_TOLERANCE,
            "full_auroc_mean": full_auroc,
            "h_only_auroc_mean": h_auroc,
            "full_unlogged_error_reduction_mean": full_reduction,
            "h_only_unlogged_error_reduction_mean": h_reduction,
        },
    }


def _evaluate_acceptance_gates(
    *,
    a1: dict[str, Any],
    ablation: dict[str, Any],
    leak_audit: dict[str, Any],
) -> dict[str, Any]:
    learned_auroc = a1["learned_gap_head_on_h"]["failure_detection_auroc"]
    matched_auroc = a1["matched_random_gap_head"]["failure_detection_auroc"]
    learned_reduction = a1["learned_gap_head_on_h"]["unlogged_error_reduction"]
    matched_reduction = a1["matched_random_gap_head"]["unlogged_error_reduction"]
    hg1 = {
        "status": "pass"
        if (
            float(learned_auroc["ci95_low"]) > float(matched_auroc["ci95_high"])
            and float(learned_auroc["mean"]) >= AUROC_POSITIVE_THRESHOLD
        )
        else "fail",
        "criterion": (
            "learned AUROC ci95_low > matched-random AUROC ci95_high and learned "
            f"AUROC mean >= {AUROC_POSITIVE_THRESHOLD}"
        ),
        "learned_auroc": learned_auroc,
        "matched_random_auroc": matched_auroc,
    }
    hg2 = {
        "status": "pass"
        if (
            float(learned_reduction["ci95_low"]) > float(matched_reduction["ci95_high"])
            and float(learned_reduction["mean"]) > 0.0
        )
        else "fail",
        "criterion": (
            "learned UnloggedErrorRate reduction ci95_low > matched-random reduction "
            "ci95_high and learned mean reduction > 0"
        ),
        "learned_unlogged_error_reduction": learned_reduction,
        "matched_random_unlogged_error_reduction": matched_reduction,
    }
    control_positive = bool(a1["control_verdict"]["positive"])
    hg3 = {
        "status": "pass"
        if (
            not control_positive
            and float(matched_auroc["ci95_high"]) <= MATCHED_RANDOM_AUROC_CEILING
        )
        else "fail",
        "criterion": (
            "producer control_verdict.positive is false and matched-random AUROC "
            f"ci95_high <= {MATCHED_RANDOM_AUROC_CEILING}"
        ),
        "control_verdict": a1["control_verdict"],
        "matched_random_auroc": matched_auroc,
    }
    hg4 = {
        "status": leak_audit["status"],
        "criterion": "producer and ablation forbidden-column audits pass",
        "audit": leak_audit,
    }
    hg5 = _mechanism_label(ablation)
    gates = {
        "A-HG1": hg1,
        "A-HG2": hg2,
        "A-HG3": hg3,
        "A-HG4": hg4,
        "A-HG5": hg5,
    }
    pass_all = all(row["status"] == "pass" for row in gates.values())
    return {
        "status": "pass" if pass_all else "fail",
        "gates": gates,
        "claim_scope_label": hg5["mechanical_label"] if pass_all else "not_positive",
    }


def _payload(
    *,
    source_payload: dict[str, Any],
    ablation: dict[str, Any],
    stability_summary: dict[str, Any],
    transfer_summary: dict[str, Any],
    elapsed_seconds: float,
) -> dict[str, Any]:
    a1 = _a1_threshold_summary(source_payload)
    leak_audit = _a5_no_leak_audit(source_payload, ablation)
    acceptance = _evaluate_acceptance_gates(
        a1=a1,
        ablation=ablation,
        leak_audit=leak_audit,
    )
    return {
        "artifact": ARTIFACT_ID,
        "json_artifact": JSON_ARTIFACT,
        "markdown_artifact": REPORT_ARTIFACT,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "elapsed_seconds": float(elapsed_seconds),
        "claim_boundary": _claim_boundary(),
        "owner_pointers": _owner_pointers(),
        "A1_threshold_sweep": a1,
        "A2_feature_ablation": ablation,
        "A3_seed_expansion": stability_summary,
        "A4_distribution_transfer": transfer_summary,
        "A5_no_leak_audit": leak_audit,
        "acceptance_gates": acceptance,
        "final_status": acceptance["status"],
        "final_claim_scope": acceptance["claim_scope_label"],
    }


def _render_report(payload: dict[str, Any]) -> str:
    a1 = payload["A1_threshold_sweep"]
    gates = payload["acceptance_gates"]["gates"]
    lines = [
        "# Gap-Head Robustness Sweep",
        "",
        f"- Generated at: `{payload['generated_at']}`",
        f"- Artifact: `{payload['artifact']}`",
        f"- Final status: `{payload['final_status']}`",
        f"- Final claim scope: `{payload['final_claim_scope']}`",
        f"- Claim: {payload['claim_boundary']['claim']}",
        f"- Elapsed seconds: `{_format_float(float(payload['elapsed_seconds']))}`",
        "",
        "## A-HG Gates",
        "",
        "| gate | status | criterion |",
        "| --- | --- | --- |",
    ]
    for gate_name, gate in gates.items():
        lines.append(f"| `{gate_name}` | `{gate['status']}` | {gate['criterion']} |")
    lines.extend(
        [
            "",
            "## A1 Threshold Sweep",
            "",
            f"- Owner: `{a1['owner']}`",
            f"- Records: `{a1['record_count']}`",
            f"- Tau grid: `{a1['tau_grid']}`",
            f"- Epsilon grid: `{a1['epsilon_grid']}`",
            (
                "- Learned AUROC: "
                f"{_render_stats(a1['learned_gap_head_on_h']['failure_detection_auroc'])}"
            ),
            (
                "- Learned UnloggedErrorRate: "
                f"{_render_stats(a1['learned_gap_head_on_h']['unlogged_error_rate'])}"
            ),
            (
                "- Learned UnloggedErrorRate reduction: "
                f"{_render_stats(a1['learned_gap_head_on_h']['unlogged_error_reduction'])}"
            ),
            (
                "- Matched-random AUROC: "
                f"{_render_stats(a1['matched_random_gap_head']['failure_detection_auroc'])}"
            ),
            (
                "- Matched-random UnloggedErrorRate reduction: "
                f"{_render_stats(a1['matched_random_gap_head']['unlogged_error_reduction'])}"
            ),
            "",
            "## A2 Feature Ablation",
            "",
            "| family | columns | learned AUROC | learned UER reduction | matched-random AUROC |",
            "| --- | ---: | ---: | ---: | ---: |",
        ]
    )
    for family, row in payload["A2_feature_ablation"]["by_family"].items():
        lines.append(
            "| "
            f"`{family}` | "
            f"{row['feature_column_count']} | "
            f"{_render_stats(row['learned']['failure_detection_auroc'])} | "
            f"{_render_stats(row['learned']['unlogged_error_reduction'])} | "
            f"{_render_stats(row['matched_random']['failure_detection_auroc'])} |"
        )
    a3 = payload["A3_seed_expansion"]
    lines.extend(
        [
            "",
            "## A3 Seed Expansion",
            "",
            f"- Owner: `{a3['owner']}`",
            f"- Final verdict: `{a3['final_verdict']}`",
            f"- Cell count: `{a3['aggregate']['cell_count']}`",
            f"- Positive cells: `{a3['aggregate']['positive_cell_count']}`",
            f"- Invalid cells: `{a3['aggregate']['invalid_cell_count']}`",
            "",
            "## A4 Distribution Transfer",
            "",
            "| surface | status | artifact | pointer | pointer summary |",
            "| --- | --- | --- | --- | --- |",
        ]
    )
    for surface in payload["A4_distribution_transfer"]["surfaces"]:
        lines.append(
            "| "
            f"`{surface['name']}` | "
            f"`{surface['status']}` | "
            f"`{surface['json_artifact']}` | "
            f"`{surface['pointer']}` | "
            f"`{json.dumps(surface['pointer_value_summary'], sort_keys=True)}` |"
        )
    lines.extend(
        [
            "",
            "## A5 No-Leak Audit",
            "",
            f"- Status: `{payload['A5_no_leak_audit']['status']}`",
            (
                "- Forbidden inference columns: "
                f"`{', '.join(payload['A5_no_leak_audit']['forbidden_inference_columns'])}`"
            ),
            "",
            "## Source Pointers",
            "",
        ]
    )
    for name, pointer in payload["owner_pointers"].items():
        lines.append(f"- `{name}`: `{json.dumps(pointer, sort_keys=True)}`")
    lines.extend(["", "## Boundary", ""])
    for item in payload["claim_boundary"]["not_claimed"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def _write_payload(payload: dict[str, Any]) -> None:
    json_path = ROOT / JSON_ARTIFACT
    report_path = ROOT / REPORT_ARTIFACT
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    report_path.write_text(_render_report(payload), encoding="utf-8")


def _active_config() -> producer.GapHeadRunConfig:
    return producer.GapHeadRunConfig(
        sample_count=producer.DEFAULT_CONFIG.sample_count,
        seeds=producer.DEFAULT_CONFIG.seeds,
        rho=producer.DEFAULT_CONFIG.rho,
        use_torch=producer.USE_TORCH,
        json_artifact="reports/canonical/gap-head-on-h.json",
        report_artifact="reports/canonical/gap-head-on-h.md",
        run_id_prefix=producer.DEFAULT_CONFIG.run_id_prefix,
        source_artifact_label=producer.DEFAULT_CONFIG.source_artifact_label,
        seed_grid_kind=producer.DEFAULT_CONFIG.seed_grid_kind,
    )


def main() -> None:
    started = time.perf_counter()
    config = _active_config()
    source_payload = producer._payload(producer._records(config), config)
    ablation = _run_ablation_sweep(config)
    stability_summary = _run_stability_sweep()
    transfer_summary = _transfer_pointer_summary()
    payload = _payload(
        source_payload=source_payload,
        ablation=ablation,
        stability_summary=stability_summary,
        transfer_summary=transfer_summary,
        elapsed_seconds=time.perf_counter() - started,
    )
    _write_payload(payload)
    print(f"wrote {JSON_ARTIFACT}")
    print(f"wrote {REPORT_ARTIFACT}")
    print(f"final_status {payload['final_status']}")
    print(f"final_claim_scope {payload['final_claim_scope']}")


if __name__ == "__main__":
    main()

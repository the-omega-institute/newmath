"""Read-only null decomposition for the DGT neural ablation report."""

from __future__ import annotations

from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
from typing import Any, Mapping, Sequence


SCHEMA_ID = "bedc-quality-lab:dgt-ablation-null-decomposition"
ARTIFACT_ID = "dgt-ablation-null-decomposition"
PRODUCER = "scripts/run_dgt_ablation_null_decomposition.py"
SOURCE_ARTIFACT = "reports/canonical/dgt-neural-ablation.json"
SOURCE_POINTER = "$"
CANONICAL_JSON_ARTIFACT = "reports/canonical/dgt-ablation-null-decomposition.json"
CANONICAL_MARKDOWN_ARTIFACT = "reports/canonical/dgt-ablation-null-decomposition.md"
CANONICAL_FINGERPRINT_ARTIFACT = "reports/canonical/dgt-ablation-null-decomposition.fingerprint.json"
GENERATED_AT = "2026-06-10T00:00:00+00:00"
COMPONENT_COUNT = 10
DIAGNOSTIC_METRIC = "quality_q"
CLASSIFICATIONS = ("saturation", "redundancy", "underpowered", "mixed", "unresolved")
ROUTE_BY_SIGNAL = {
    "saturation": "climb-ladder",
    "redundancy": "redesign-decomposition",
    "underpowered": "add-seeds",
}
ROUTE_TIE_ORDER = {
    "add-seeds": 0,
    "redesign-decomposition": 1,
    "climb-ladder": 2,
}
NOT_CLAIMED = (
    "No production training claim.",
    "No global model superiority claim.",
    "No LLM replacement claim.",
    "No final empirical verdict on DGT is claimed.",
    "This report only diagnoses bounded-toy null causes from the existing neural ablation artifact.",
)


def threshold_schema() -> dict[str, dict[str, Any]]:
    return {
        "ceiling_metric_min": {
            "value": 0.80,
            "description": "Minimum bounded quality metric for both full and leave-one-out arms.",
        },
        "ceiling_distance_max": {
            "value": 0.20,
            "description": "Maximum distance from the metric ceiling for the weaker arm.",
        },
        "inter_arm_spread_max": {
            "value": 0.003,
            "description": "Maximum absolute metric spread between full and leave-one-out arms.",
        },
        "effect_tol": {
            "value": 0.0005,
            "description": "Minimum absolute paired effect before CI width can indicate low power.",
        },
        "ci_width_over_effect_min": {
            "value": 2.0,
            "description": "Minimum CI width divided by absolute effect for an underpowered signal.",
        },
        "redundancy_abs_delta_max": {
            "value": 0.0005,
            "description": "Maximum absolute leave-one-out delta for a redundancy signal.",
        },
        "global_dominance_min": {
            "value": 0.70,
            "description": "Minimum share required for a single empirical global verdict.",
        },
    }


def decision_table() -> dict[str, list[dict[str, Any]]]:
    return {
        "component_classification": [
            {
                "condition": "required source pointers absent, nonnumeric, or schema-invalid",
                "evidence_status": "missing_or_invalid",
                "classification": "unresolved",
            },
            {
                "condition": "exactly one signal active",
                "evidence_status": "complete",
                "classification": "the active signal",
            },
            {
                "condition": "more than one signal active",
                "evidence_status": "complete",
                "classification": "mixed",
            },
            {
                "condition": "no signal active",
                "evidence_status": "complete",
                "classification": "mixed",
            },
        ],
        "global_verdict": [
            {
                "condition": "any ND-HG1..ND-HG6 status is fail",
                "analysis_status": "fail",
                "verdict": "unresolved",
                "roadmap_recommendation": "repair-evidence",
            },
            {
                "condition": "unique empirical top category reaches global_dominance_min",
                "analysis_status": "pass",
                "verdict": "top category",
                "roadmap_recommendation": "mapped route",
            },
            {
                "condition": "top category is mixed, tied, or below global_dominance_min",
                "analysis_status": "pass",
                "verdict": "mixed",
                "roadmap_recommendation": "mixed",
            },
        ],
        "roadmap_mapping": [
            {"classification": "saturation", "roadmap_recommendation": "climb-ladder"},
            {"classification": "redundancy", "roadmap_recommendation": "redesign-decomposition"},
            {"classification": "underpowered", "roadmap_recommendation": "add-seeds"},
            {"classification": "mixed", "roadmap_recommendation": "mixed"},
            {"classification": "unresolved", "roadmap_recommendation": "repair-evidence"},
        ],
    }


def _write_json(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _json_digest(payload: Mapping[str, Any]) -> str:
    return hashlib.sha256(json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")).hexdigest()


def _file_digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _pointer_value(payload: Any, pointer: str) -> Any:
    if pointer == "$":
        return payload
    if not pointer.startswith("$."):
        raise KeyError(pointer)
    cursor = payload
    for part in pointer[2:].split("."):
        if isinstance(cursor, Mapping) and part in cursor:
            cursor = cursor[part]
        else:
            raise KeyError(pointer)
    return cursor


def _is_number(value: Any) -> bool:
    return isinstance(value, (int, float)) and not isinstance(value, bool)


def _number(payload: Mapping[str, Any], pointer: str) -> float:
    value = _pointer_value(payload, pointer)
    if not _is_number(value):
        raise TypeError(pointer)
    return float(value)


def _component_ids(source: Mapping[str, Any]) -> tuple[str, ...]:
    arms = source.get("run_spec", {}).get("arms")
    if isinstance(arms, Sequence) and not isinstance(arms, (str, bytes)):
        components = []
        for arm in arms:
            if isinstance(arm, str) and arm.startswith("DGT_without_"):
                components.append(arm.removeprefix("DGT_without_"))
        if components:
            return tuple(components)
    registry = source.get("module_registry")
    if isinstance(registry, Mapping):
        components = []
        for row in registry.values():
            if isinstance(row, Mapping) and isinstance(row.get("disabled_component"), str):
                components.append(row["disabled_component"])
        return tuple(components)
    return ()


def _signal(active: bool, score: float, reason_codes: Sequence[str]) -> dict[str, Any]:
    return {
        "active": bool(active),
        "score": round(float(score), 6),
        "reason_codes": list(reason_codes),
    }


def _component_row(source: Mapping[str, Any], component: str, thresholds: Mapping[str, Mapping[str, Any]]) -> dict[str, Any]:
    arm = f"DGT_without_{component}"
    metric_inputs = [
        f"{SOURCE_ARTIFACT}:$.arm_summaries.full_DGT.metrics.{DIAGNOSTIC_METRIC}",
        f"{SOURCE_ARTIFACT}:$.arm_summaries.{arm}.metrics.{DIAGNOSTIC_METRIC}",
    ]
    leave_one_out_inputs = [
        f"{SOURCE_ARTIFACT}:$.paired_delta_matrix.{arm}.metrics.{DIAGNOSTIC_METRIC}",
    ]
    paired_ci_inputs = [
        f"{SOURCE_ARTIFACT}:$.paired_delta_matrix.{arm}.metrics.{DIAGNOSTIC_METRIC}",
        f"{SOURCE_ARTIFACT}:$.paired_delta_matrix.{arm}.confidence_intervals.{DIAGNOSTIC_METRIC}.low",
        f"{SOURCE_ARTIFACT}:$.paired_delta_matrix.{arm}.confidence_intervals.{DIAGNOSTIC_METRIC}.high",
        f"{SOURCE_ARTIFACT}:$.paired_delta_matrix.{arm}.paired_seed_count",
        f"{SOURCE_ARTIFACT}:$.paired_delta_matrix.{arm}.paired_ci_min_seeds",
    ]
    source_pointers = {
        "metric_inputs": metric_inputs,
        "leave_one_out_inputs": leave_one_out_inputs,
        "paired_ci_inputs": paired_ci_inputs,
    }
    missing: list[str] = []

    def numeric(local_pointer: str) -> float | None:
        try:
            return _number(source, local_pointer)
        except (KeyError, TypeError, ValueError):
            missing.append(f"{SOURCE_ARTIFACT}:{local_pointer}")
            return None

    full_metric = numeric(f"$.arm_summaries.full_DGT.metrics.{DIAGNOSTIC_METRIC}")
    ablated_metric = numeric(f"$.arm_summaries.{arm}.metrics.{DIAGNOSTIC_METRIC}")
    effect = numeric(f"$.paired_delta_matrix.{arm}.metrics.{DIAGNOSTIC_METRIC}")
    ci_low = numeric(f"$.paired_delta_matrix.{arm}.confidence_intervals.{DIAGNOSTIC_METRIC}.low")
    ci_high = numeric(f"$.paired_delta_matrix.{arm}.confidence_intervals.{DIAGNOSTIC_METRIC}.high")
    paired_seed_count = numeric(f"$.paired_delta_matrix.{arm}.paired_seed_count")
    paired_ci_min_seeds = numeric(f"$.paired_delta_matrix.{arm}.paired_ci_min_seeds")

    if missing:
        return {
            "component_id": component,
            "source_pointers": source_pointers,
            "evidence_status": "missing",
            "missing_evidence": sorted(set(missing)),
            "signals": {
                "saturation": _signal(False, 0.0, ["missing-metric-inputs"]),
                "redundancy": _signal(False, 0.0, ["missing-leave-one-out-inputs"]),
                "underpowered": _signal(False, 0.0, ["missing-paired-ci-inputs"]),
            },
            "active_signals": [],
            "classification": "unresolved",
            "classification_reason_codes": ["required-evidence-missing"],
        }

    assert full_metric is not None
    assert ablated_metric is not None
    assert effect is not None
    assert ci_low is not None
    assert ci_high is not None
    assert paired_seed_count is not None
    assert paired_ci_min_seeds is not None

    ceiling_metric = min(full_metric, ablated_metric)
    ceiling_distance = 1.0 - ceiling_metric
    inter_arm_spread = abs(full_metric - ablated_metric)
    saturation_active = (
        ceiling_metric >= float(thresholds["ceiling_metric_min"]["value"])
        and ceiling_distance <= float(thresholds["ceiling_distance_max"]["value"])
        and inter_arm_spread <= float(thresholds["inter_arm_spread_max"]["value"])
    )
    redundancy_delta = abs(effect)
    redundancy_active = redundancy_delta <= float(thresholds["redundancy_abs_delta_max"]["value"])
    ci_width = ci_high - ci_low
    ci_crosses_zero = ci_low <= 0.0 <= ci_high
    abs_effect = abs(effect)
    width_ratio = ci_width / abs_effect if abs_effect > 0.0 else 0.0
    underpowered_active = (
        abs_effect > float(thresholds["effect_tol"]["value"])
        and ci_crosses_zero
        and width_ratio >= float(thresholds["ci_width_over_effect_min"]["value"])
        and paired_seed_count >= paired_ci_min_seeds
    )

    signals = {
        "saturation": _signal(
            saturation_active,
            max(0.0, min(ceiling_metric, 1.0) - inter_arm_spread),
            ["near-ceiling-low-spread"] if saturation_active else ["ceiling-or-spread-threshold-not-met"],
        ),
        "redundancy": _signal(
            redundancy_active,
            redundancy_delta,
            ["leave-one-out-delta-below-threshold"] if redundancy_active else ["leave-one-out-delta-above-threshold"],
        ),
        "underpowered": _signal(
            underpowered_active,
            width_ratio,
            ["ci-crosses-zero-wide-relative-to-effect"] if underpowered_active else ["ci-width-predicate-not-met"],
        ),
    }
    active_signals = [name for name, row in signals.items() if row["active"]]
    if len(active_signals) == 1:
        classification = active_signals[0]
        classification_reason_codes = [f"single-{classification}-signal"]
    elif len(active_signals) > 1:
        classification = "mixed"
        classification_reason_codes = ["multiple-active-signals"]
    else:
        classification = "mixed"
        classification_reason_codes = ["no-active-signal"]
    return {
        "component_id": component,
        "source_pointers": source_pointers,
        "evidence_status": "complete",
        "missing_evidence": [],
        "signals": signals,
        "active_signals": active_signals,
        "classification": classification,
        "classification_reason_codes": classification_reason_codes,
    }


def _global_counts(components: Sequence[Mapping[str, Any]]) -> dict[str, int]:
    counts = {key: 0 for key in CLASSIFICATIONS}
    for row in components:
        classification = row.get("classification")
        if classification in counts:
            counts[str(classification)] += 1
    return counts


def _dominance(counts: Mapping[str, int], total: int) -> dict[str, Any]:
    if total <= 0:
        return {"category": "unresolved", "count": 0, "share": 0.0, "is_unique": False}
    top_count = max(counts.values())
    top_categories = [key for key, value in counts.items() if value == top_count]
    category = top_categories[0] if len(top_categories) == 1 else "mixed"
    return {
        "category": category,
        "count": top_count,
        "share": round(top_count / total, 6),
        "is_unique": len(top_categories) == 1,
    }


def _roadmap_priority(components: Sequence[Mapping[str, Any]], preferred: str | None = None) -> list[str]:
    route_counts = {route: 0 for route in ROUTE_TIE_ORDER}
    for row in components:
        classification = row.get("classification")
        if classification in ROUTE_BY_SIGNAL:
            route_counts[ROUTE_BY_SIGNAL[str(classification)]] += 1
        elif classification == "mixed":
            for signal in row.get("active_signals", []):
                route = ROUTE_BY_SIGNAL.get(str(signal))
                if route is not None:
                    route_counts[route] += 1
    ranked = [
        route
        for route, count in sorted(route_counts.items(), key=lambda item: (-item[1], ROUTE_TIE_ORDER[item[0]]))
        if count > 0
    ]
    if preferred is not None and preferred in ranked:
        return [preferred] + [route for route in ranked if route != preferred]
    return ranked


def _hardgates(
    *,
    source_status: str,
    component_ids: Sequence[str],
    components: Sequence[Mapping[str, Any]],
) -> dict[str, dict[str, Any]]:
    metric_complete = bool(components) and all(row.get("evidence_status") == "complete" for row in components)
    leave_complete = metric_complete
    ci_complete = metric_complete
    hg6_complete = source_status == "resolved" and len(component_ids) == COMPONENT_COUNT and metric_complete
    return {
        "ND-HG1": {
            "status": "pass" if source_status == "resolved" else "fail",
            "criterion": "source artifact and root pointer resolve",
            "input_pointers": [f"{SOURCE_ARTIFACT}:{SOURCE_POINTER}"],
            "mutation_test": "remove or corrupt the source artifact",
        },
        "ND-HG2": {
            "status": "pass" if len(component_ids) == COMPONENT_COUNT else "fail",
            "criterion": "exactly ten source component ids are represented",
            "input_pointers": [f"{SOURCE_ARTIFACT}:$.run_spec.arms", f"{SOURCE_ARTIFACT}:$.module_registry"],
            "mutation_test": "drop or duplicate a DGT_without component arm",
        },
        "ND-HG3": {
            "status": "pass" if metric_complete else "fail",
            "criterion": "saturation fields derive from numeric arm metrics",
            "input_pointers": [f"{SOURCE_ARTIFACT}:$.arm_summaries"],
            "mutation_test": "delete or denormalize a quality metric",
        },
        "ND-HG4": {
            "status": "pass" if leave_complete else "fail",
            "criterion": "redundancy fields derive from numeric leave-one-out deltas",
            "input_pointers": [f"{SOURCE_ARTIFACT}:$.paired_delta_matrix"],
            "mutation_test": "change or delete a leave-one-out delta",
        },
        "ND-HG5": {
            "status": "pass" if ci_complete else "fail",
            "criterion": "underpowered fields derive from numeric paired-CI bands and seed pairing metadata",
            "input_pointers": [f"{SOURCE_ARTIFACT}:$.paired_delta_matrix"],
            "mutation_test": "change CI crossing, width, effect, or paired seed metadata",
        },
        "ND-HG6": {
            "status": "pass" if hg6_complete else "fail",
            "criterion": "global verdict, route, priority, and counts are recomputed from component rows",
            "input_pointers": [f"{CANONICAL_JSON_ARTIFACT}:$.null_decomposition.components"],
            "mutation_test": "mutate a component classification and recompute global fields",
        },
    }


def _null_decomposition(components: Sequence[Mapping[str, Any]], hardgates: Mapping[str, Mapping[str, Any]], thresholds: Mapping[str, Mapping[str, Any]]) -> dict[str, Any]:
    counts = _global_counts(components)
    dominance = _dominance(counts, len(components))
    if any(row.get("status") == "fail" for row in hardgates.values()):
        return {
            "analysis_status": "fail",
            "components": list(components),
            "global_counts": counts,
            "dominance": dominance,
            "verdict": "unresolved",
            "roadmap_recommendation": "repair-evidence",
            "roadmap_priority": ["repair-evidence"],
        }
    global_dominance_min = float(thresholds["global_dominance_min"]["value"])
    category = dominance["category"]
    if category in ROUTE_BY_SIGNAL and dominance["is_unique"] and dominance["share"] >= global_dominance_min:
        route = ROUTE_BY_SIGNAL[category]
        verdict = category
        recommendation = route
        priority = _roadmap_priority(components, preferred=route)
    else:
        verdict = "mixed"
        recommendation = "mixed"
        priority = _roadmap_priority(components)
    return {
        "analysis_status": "pass",
        "components": list(components),
        "global_counts": counts,
        "dominance": dominance,
        "verdict": verdict,
        "roadmap_recommendation": recommendation,
        "roadmap_priority": priority,
    }


def _source_record(*, root: Path, status: str, sha256: str | None, required_pointers: Sequence[str]) -> dict[str, Any]:
    return {
        "path": SOURCE_ARTIFACT,
        "json_pointer": SOURCE_POINTER,
        "sha256": sha256,
        "status": status,
        "required_pointers": list(required_pointers),
    }


def _load_source(root: Path) -> tuple[str, dict[str, Any] | None, str | None]:
    path = root / SOURCE_ARTIFACT
    if not path.exists():
        return "missing", None, None
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return "invalid", None, None
    if not isinstance(payload, dict):
        return "invalid", None, _file_digest(path)
    return "resolved", payload, _file_digest(path)


def build_payload(
    *,
    root: Path,
    generated_at: str = GENERATED_AT,
    source_payload: Mapping[str, Any] | None = None,
    source_status: str | None = None,
    source_sha256: str | None = None,
) -> dict[str, Any]:
    if source_payload is None:
        resolved_status, loaded_source, resolved_sha = _load_source(root)
        source_status = source_status or resolved_status
        source_payload = loaded_source
        source_sha256 = source_sha256 if source_sha256 is not None else resolved_sha
    else:
        source_status = source_status or "resolved"
        source_sha256 = source_sha256 if source_sha256 is not None else _json_digest(dict(source_payload))

    thresholds = threshold_schema()
    components: list[dict[str, Any]] = []
    component_ids: tuple[str, ...] = ()
    required_pointers = [f"{SOURCE_ARTIFACT}:{SOURCE_POINTER}"]
    if source_status == "resolved" and isinstance(source_payload, Mapping):
        component_ids = _component_ids(source_payload)
        for component in component_ids[:COMPONENT_COUNT]:
            row = _component_row(source_payload, component, thresholds)
            components.append(row)
            for group in row["source_pointers"].values():
                required_pointers.extend(group)
    hardgates = _hardgates(source_status=source_status or "invalid", component_ids=component_ids, components=components)
    payload = {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "generated_at": generated_at,
        "producer": PRODUCER,
        "source_artifact": _source_record(
            root=root,
            status=source_status or "invalid",
            sha256=source_sha256,
            required_pointers=sorted(set(required_pointers)),
        ),
        "threshold_schema": thresholds,
        "decision_table": decision_table(),
        "null_decomposition": _null_decomposition(components, hardgates, thresholds),
        "hardgates": hardgates,
        "not_claimed": list(NOT_CLAIMED),
    }
    validate_payload(payload)
    return payload


def validate_payload(payload: Mapping[str, Any]) -> None:
    required = {
        "schema_id",
        "artifact_id",
        "generated_at",
        "producer",
        "source_artifact",
        "threshold_schema",
        "decision_table",
        "null_decomposition",
        "hardgates",
        "not_claimed",
    }
    if set(payload) != required:
        raise ValueError("DGT ablation null decomposition payload fields mismatch")
    if payload["schema_id"] != SCHEMA_ID or payload["artifact_id"] != ARTIFACT_ID:
        raise ValueError("DGT ablation null decomposition identity mismatch")
    hardgates = payload["hardgates"]
    if not isinstance(hardgates, Mapping) or set(hardgates) != {f"ND-HG{index}" for index in range(1, 7)}:
        raise ValueError("DGT ablation null decomposition hardgate names mismatch")
    null = payload["null_decomposition"]
    if null["analysis_status"] == "fail":
        if null["verdict"] != "unresolved" or null["roadmap_recommendation"] != "repair-evidence":
            raise ValueError("failed null decomposition must repair evidence")
    if null["analysis_status"] == "pass":
        if any(row.get("status") == "fail" for row in hardgates.values()):
            raise ValueError("passing null decomposition cannot have failed hardgates")
        if null["verdict"] == "unresolved" or null["roadmap_recommendation"] == "repair-evidence":
            raise ValueError("unresolved route is only legal for failed analysis")
    components = null["components"]
    if null["analysis_status"] == "pass" and len(components) != COMPONENT_COUNT:
        raise ValueError("passing null decomposition must represent ten components")
    if null["global_counts"] != _global_counts(components):
        raise ValueError("global counts drift from component rows")
    for row in components:
        classification = row.get("classification")
        if classification not in CLASSIFICATIONS:
            raise ValueError(f"invalid null classification: {classification}")
        signals = row.get("signals")
        if set(signals or {}) != {"saturation", "redundancy", "underpowered"}:
            raise ValueError("component signal keys mismatch")
        active = [name for name, signal in signals.items() if signal.get("active") is True]
        if row.get("active_signals") != active:
            raise ValueError("component active_signals drift from signals")


def render_markdown(payload: Mapping[str, Any]) -> str:
    null = payload["null_decomposition"]
    lines = [
        "# DGT ablation null decomposition",
        "",
        f"- Source: `{payload['source_artifact']['path']}:{payload['source_artifact']['json_pointer']}`",
        f"- Analysis status: `{null['analysis_status']}`",
        f"- Verdict: `{null['verdict']}`",
        f"- Roadmap recommendation: `{null['roadmap_recommendation']}`",
        f"- Roadmap priority: `{', '.join(null['roadmap_priority'])}`",
        "",
        "## Component rows",
        "",
    ]
    for row in null["components"]:
        signals = ",".join(row["active_signals"]) if row["active_signals"] else "none"
        lines.append(f"- `{row['component_id']}`: `{row['classification']}` ({signals})")
    lines.extend(["", "## Hardgates", ""])
    for gate_id, row in payload["hardgates"].items():
        lines.append(f"- `{gate_id}`: `{row['status']}`")
    lines.append("")
    return "\n".join(lines)


def fingerprint_payload(payload: Mapping[str, Any], *, generated_at: str) -> dict[str, Any]:
    return {
        "schema_id": "bedc-quality-lab:canonical-report-fingerprint",
        "report_name": "dgt-ablation-null-decomposition",
        "json_artifact": CANONICAL_JSON_ARTIFACT,
        "markdown_artifact": CANONICAL_MARKDOWN_ARTIFACT,
        "producer_command": ["python3", PRODUCER],
        "input_fingerprint": payload["source_artifact"]["sha256"],
        "output_digest": _json_digest(dict(payload)),
        "inputs": {"source_artifact": SOURCE_ARTIFACT, "json_pointer": SOURCE_POINTER},
        "generated_by": {"runner": PRODUCER, "generated_at": generated_at},
    }


def write_artifacts(payload: Mapping[str, Any], *, root: Path, generated_at: str | None = None) -> None:
    validate_payload(payload)
    _write_json(root / CANONICAL_JSON_ARTIFACT, dict(payload))
    markdown_path = root / CANONICAL_MARKDOWN_ARTIFACT
    markdown_path.parent.mkdir(parents=True, exist_ok=True)
    markdown_path.write_text(render_markdown(payload), encoding="utf-8")
    _write_json(
        root / CANONICAL_FINGERPRINT_ARTIFACT,
        fingerprint_payload(payload, generated_at=generated_at or datetime.now(timezone.utc).isoformat()),
    )

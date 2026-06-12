"""Read-only component redundancy audit for DGT ablation artifacts."""

from __future__ import annotations

from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
from typing import Any, Mapping, Sequence


SCHEMA_ID = "bedc-quality-lab:dgt-component-redundancy-audit"
ARTIFACT_ID = "bedc-quality-lab:dgt-component-redundancy-audit"
PRODUCER = "scripts/run_dgt_component_redundancy_audit.py"
NEURAL_SOURCE_ARTIFACT = "reports/canonical/dgt-neural-ablation.json"
NULL_SOURCE_ARTIFACT = "reports/canonical/dgt-ablation-null-decomposition.json"
CANONICAL_JSON_ARTIFACT = "reports/canonical/dgt-component-redundancy-audit.json"
CANONICAL_MARKDOWN_ARTIFACT = "reports/canonical/dgt-component-redundancy-audit.md"
CANONICAL_FINGERPRINT_ARTIFACT = "reports/canonical/dgt-component-redundancy-audit.fingerprint.json"
GENERATED_AT = "2026-06-10T00:00:00+00:00"
COMPONENT_COUNT = 10
DIAGNOSTIC_METRIC = "quality_q"
VERDICTS = ("confirmed-redundant", "independent", "inconclusive")
SUSPECT_COMPONENTS = ("route_certificate", "mechanism_probe", "negative_witness_loss")
NOT_CLAIMED = (
    "Bounded toy component redundancy audit only.",
    "No production or global DGT component necessity verdict is claimed.",
    "No architecture redesign is performed by this report.",
    "No claim outside the existing canonical leave-one-out artifacts is made.",
)


def threshold_schema() -> dict[str, dict[str, Any]]:
    return {
        "redundancy_abs_delta_max": {
            "value": 0.0005,
            "description": "Maximum absolute leave-one-out quality delta for a near-zero independent contribution.",
        },
        "independent_abs_delta_min": {
            "value": 0.0005,
            "description": "Minimum absolute leave-one-out quality delta before a non-crossing CI can support independence.",
        },
    }


def decision_table() -> list[dict[str, str]]:
    return [
        {
            "condition": "required neural or null-decomposition pointers are missing or nonnumeric",
            "verdict": "inconclusive",
            "reason_code": "required-evidence-missing",
        },
        {
            "condition": "absolute leave-one-out quality delta is at most redundancy_abs_delta_max and null report exposes an active redundancy signal",
            "verdict": "confirmed-redundant",
            "reason_code": "near-zero-delta-with-null-redundancy-signal",
        },
        {
            "condition": "absolute leave-one-out quality delta is at least independent_abs_delta_min and the quality CI does not cross zero",
            "verdict": "independent",
            "reason_code": "nonzero-delta-with-noncrossing-ci",
        },
        {
            "condition": "available evidence does not identify either near-zero redundancy or a stable independent contribution",
            "verdict": "inconclusive",
            "reason_code": "evidence-band-does-not-separate",
        },
    ]


def _write_json(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _json_digest(payload: Any) -> str:
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


def _load_json_artifact(root: Path, artifact: str) -> tuple[str, dict[str, Any] | None, str | None]:
    path = root / artifact
    if not path.exists():
        return "missing", None, None
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return "invalid", None, None
    if not isinstance(payload, dict):
        return "invalid", None, _file_digest(path)
    return "resolved", payload, _file_digest(path)


def _component_ids(neural: Mapping[str, Any]) -> tuple[str, ...]:
    arms = neural.get("run_spec", {}).get("arms")
    if not isinstance(arms, Sequence) or isinstance(arms, (str, bytes)):
        return ()
    components = [
        arm.removeprefix("DGT_without_")
        for arm in arms
        if isinstance(arm, str) and arm.startswith("DGT_without_")
    ]
    return tuple(components)


def _null_rows(null_payload: Mapping[str, Any]) -> dict[str, tuple[int, Mapping[str, Any]]]:
    rows = null_payload.get("null_decomposition", {}).get("components")
    if not isinstance(rows, list):
        return {}
    indexed: dict[str, tuple[int, Mapping[str, Any]]] = {}
    for index, row in enumerate(rows):
        if isinstance(row, Mapping) and isinstance(row.get("component_id"), str):
            indexed[str(row["component_id"])] = (index, row)
    return indexed


def _component_row(
    *,
    neural: Mapping[str, Any],
    null_rows: Mapping[str, tuple[int, Mapping[str, Any]]],
    component: str,
    thresholds: Mapping[str, Mapping[str, Any]],
) -> dict[str, Any]:
    arm = f"DGT_without_{component}"
    source_pointers = {
        "quality_delta": f"{NEURAL_SOURCE_ARTIFACT}:$.paired_delta_matrix.{arm}.metrics.{DIAGNOSTIC_METRIC}",
        "quality_ci_low": f"{NEURAL_SOURCE_ARTIFACT}:$.paired_delta_matrix.{arm}.confidence_intervals.{DIAGNOSTIC_METRIC}.low",
        "quality_ci_high": f"{NEURAL_SOURCE_ARTIFACT}:$.paired_delta_matrix.{arm}.confidence_intervals.{DIAGNOSTIC_METRIC}.high",
        "null_components": f"{NULL_SOURCE_ARTIFACT}:$.null_decomposition.components",
    }
    missing: list[str] = []

    def numeric(local_pointer: str, public_pointer: str) -> float | None:
        try:
            return _number(neural, local_pointer)
        except (KeyError, TypeError, ValueError):
            missing.append(public_pointer)
            return None

    delta = numeric(
        f"$.paired_delta_matrix.{arm}.metrics.{DIAGNOSTIC_METRIC}",
        source_pointers["quality_delta"],
    )
    ci_low = numeric(
        f"$.paired_delta_matrix.{arm}.confidence_intervals.{DIAGNOSTIC_METRIC}.low",
        source_pointers["quality_ci_low"],
    )
    ci_high = numeric(
        f"$.paired_delta_matrix.{arm}.confidence_intervals.{DIAGNOSTIC_METRIC}.high",
        source_pointers["quality_ci_high"],
    )
    null_index_row = null_rows.get(component)
    if null_index_row is None:
        missing.append(source_pointers["null_components"])
        null_index = None
        null_row: Mapping[str, Any] = {}
    else:
        null_index, null_row = null_index_row
        source_pointers["null_component_row"] = f"{NULL_SOURCE_ARTIFACT}:$.null_decomposition.components[{null_index}]"

    null_active_signals = [
        str(signal)
        for signal in null_row.get("active_signals", [])
        if isinstance(signal, str)
    ]
    null_classification = null_row.get("classification") if isinstance(null_row.get("classification"), str) else None
    null_redundancy_signal = "redundancy" in null_active_signals or null_classification == "redundancy"

    if missing or delta is None or ci_low is None or ci_high is None:
        verdict = "inconclusive"
        reason_codes = ["required-evidence-missing"]
        evidence_status = "missing"
        abs_delta = None
        ci_crosses_zero = None
    else:
        evidence_status = "complete"
        abs_delta = abs(delta)
        ci_crosses_zero = ci_low <= 0.0 <= ci_high
        redundancy_max = float(thresholds["redundancy_abs_delta_max"]["value"])
        independent_min = float(thresholds["independent_abs_delta_min"]["value"])
        if abs_delta <= redundancy_max and null_redundancy_signal:
            verdict = "confirmed-redundant"
            reason_codes = ["near-zero-delta-with-null-redundancy-signal"]
        elif abs_delta >= independent_min and not ci_crosses_zero:
            verdict = "independent"
            reason_codes = ["nonzero-delta-with-noncrossing-ci"]
        else:
            verdict = "inconclusive"
            reason_codes = ["evidence-band-does-not-separate"]

    return {
        "component_id": component,
        "arm_id": arm,
        "suspect_component": component in SUSPECT_COMPONENTS,
        "evidence_status": evidence_status,
        "missing_evidence": sorted(set(missing)),
        "source_pointers": source_pointers,
        "quality_delta": None if delta is None else round(delta, 6),
        "quality_delta_abs": None if abs_delta is None else round(abs_delta, 6),
        "quality_ci": {
            "low": None if ci_low is None else round(ci_low, 6),
            "high": None if ci_high is None else round(ci_high, 6),
            "crosses_zero": ci_crosses_zero,
        },
        "null_decomposition": {
            "component_index": null_index,
            "classification": null_classification,
            "active_signals": null_active_signals,
            "redundancy_signal": null_redundancy_signal,
        },
        "verdict": verdict,
        "verdict_reason_codes": reason_codes,
    }


def _counts(components: Sequence[Mapping[str, Any]]) -> dict[str, int]:
    counts = {key: 0 for key in VERDICTS}
    for row in components:
        verdict = row.get("verdict")
        if verdict in counts:
            counts[str(verdict)] += 1
    return counts


def _global_recommendation(components: Sequence[Mapping[str, Any]], counts: Mapping[str, int]) -> dict[str, Any]:
    confirmed = [str(row["component_id"]) for row in components if row.get("verdict") == "confirmed-redundant"]
    suspect_confirmed = [component for component in SUSPECT_COMPONENTS if component in confirmed]
    inconclusive = [str(row["component_id"]) for row in components if row.get("verdict") == "inconclusive"]
    if suspect_confirmed:
        recommendation = "redesign-confirmed-redundant-components"
        reason = "suspect-components-confirmed-redundant-in-bounded-toy-audit"
    elif counts.get("confirmed-redundant", 0) > 0:
        recommendation = "review-confirmed-redundant-components"
        reason = "non-suspect-components-confirmed-redundant-in-bounded-toy-audit"
    elif inconclusive:
        recommendation = "collect-more-evidence-before-redesign"
        reason = "some-component-verdicts-remain-inconclusive"
    else:
        recommendation = "retain-current-decomposition"
        reason = "no-confirmed-redundant-component-detected"
    return {
        "recommendation": recommendation,
        "reason_code": reason,
        "confirmed_redundant_components": confirmed,
        "suspect_confirmed_redundant_components": suspect_confirmed,
        "inconclusive_components": inconclusive,
        "redesign_action": "advisory-only",
    }


def _source_record(status: str, artifact: str, sha256: str | None, required_pointers: Sequence[str]) -> dict[str, Any]:
    return {
        "path": artifact,
        "json_pointer": "$",
        "sha256": sha256,
        "status": status,
        "required_pointers": sorted(set(required_pointers)),
    }


def build_payload(
    *,
    root: Path,
    generated_at: str = GENERATED_AT,
    neural_payload: Mapping[str, Any] | None = None,
    null_payload: Mapping[str, Any] | None = None,
    neural_status: str | None = None,
    null_status: str | None = None,
    neural_sha256: str | None = None,
    null_sha256: str | None = None,
) -> dict[str, Any]:
    if neural_payload is None:
        resolved_status, loaded_payload, resolved_sha = _load_json_artifact(root, NEURAL_SOURCE_ARTIFACT)
        neural_status = neural_status or resolved_status
        neural_payload = loaded_payload
        neural_sha256 = neural_sha256 if neural_sha256 is not None else resolved_sha
    else:
        neural_status = neural_status or "resolved"
        neural_sha256 = neural_sha256 if neural_sha256 is not None else _json_digest(neural_payload)

    if null_payload is None:
        resolved_status, loaded_payload, resolved_sha = _load_json_artifact(root, NULL_SOURCE_ARTIFACT)
        null_status = null_status or resolved_status
        null_payload = loaded_payload
        null_sha256 = null_sha256 if null_sha256 is not None else resolved_sha
    else:
        null_status = null_status or "resolved"
        null_sha256 = null_sha256 if null_sha256 is not None else _json_digest(null_payload)

    thresholds = threshold_schema()
    components: list[dict[str, Any]] = []
    neural_required = [f"{NEURAL_SOURCE_ARTIFACT}:$"]
    null_required = [f"{NULL_SOURCE_ARTIFACT}:$"]
    if neural_status == "resolved" and null_status == "resolved" and isinstance(neural_payload, Mapping) and isinstance(null_payload, Mapping):
        null_by_component = _null_rows(null_payload)
        for component in _component_ids(neural_payload)[:COMPONENT_COUNT]:
            row = _component_row(
                neural=neural_payload,
                null_rows=null_by_component,
                component=component,
                thresholds=thresholds,
            )
            components.append(row)
            for pointer in row["source_pointers"].values():
                if pointer.startswith(NEURAL_SOURCE_ARTIFACT):
                    neural_required.append(pointer)
                elif pointer.startswith(NULL_SOURCE_ARTIFACT):
                    null_required.append(pointer)

    source_ok = neural_status == "resolved" and null_status == "resolved"
    component_count_ok = len(components) == COMPONENT_COUNT
    complete_ok = component_count_ok and all(row["evidence_status"] == "complete" for row in components)
    counts = _counts(components)
    audit_status = "pass" if source_ok and complete_ok else "inconclusive"
    audit = {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "generated_at": generated_at,
        "producer": PRODUCER,
        "scope": {
            "claim": "bounded toy read-only audit of DGT leave-one-out component redundancy",
            "diagnostic_metric": DIAGNOSTIC_METRIC,
            "component_count": COMPONENT_COUNT,
        },
        "source_artifacts": {
            "dgt_neural_ablation": _source_record(neural_status or "invalid", NEURAL_SOURCE_ARTIFACT, neural_sha256, neural_required),
            "dgt_ablation_null_decomposition": _source_record(null_status or "invalid", NULL_SOURCE_ARTIFACT, null_sha256, null_required),
        },
        "threshold_schema": thresholds,
        "decision_table": decision_table(),
        "audit_status": audit_status,
        "components": components,
        "verdict_counts": counts,
        "suspect_components": list(SUSPECT_COMPONENTS),
        "global_recommendation": _global_recommendation(components, counts),
        "not_claimed": list(NOT_CLAIMED),
    }
    payload = {"component_redundancy_audit": audit}
    validate_payload(payload)
    return payload


def validate_payload(payload: Mapping[str, Any]) -> None:
    if set(payload) != {"component_redundancy_audit"}:
        raise ValueError("component redundancy audit payload must expose only component_redundancy_audit")
    audit = payload["component_redundancy_audit"]
    required = {
        "schema_id",
        "artifact_id",
        "generated_at",
        "producer",
        "scope",
        "source_artifacts",
        "threshold_schema",
        "decision_table",
        "audit_status",
        "components",
        "verdict_counts",
        "suspect_components",
        "global_recommendation",
        "not_claimed",
    }
    if not isinstance(audit, Mapping) or set(audit) != required:
        raise ValueError("component redundancy audit fields mismatch")
    if audit["schema_id"] != SCHEMA_ID or audit["artifact_id"] != ARTIFACT_ID:
        raise ValueError("component redundancy audit identity mismatch")
    components = audit["components"]
    if not isinstance(components, list):
        raise ValueError("component redundancy audit components must be a list")
    if audit["audit_status"] == "pass" and len(components) != COMPONENT_COUNT:
        raise ValueError("passing component redundancy audit must represent ten components")
    if audit["verdict_counts"] != _counts(components):
        raise ValueError("component redundancy audit counts drift from component rows")
    for row in components:
        if row.get("verdict") not in VERDICTS:
            raise ValueError(f"invalid component redundancy verdict: {row.get('verdict')}")
        if row.get("verdict") == "confirmed-redundant" and row.get("null_decomposition", {}).get("redundancy_signal") is not True:
            raise ValueError("confirmed redundant verdict requires null redundancy signal")
        pointers = row.get("source_pointers")
        if not isinstance(pointers, Mapping) or not all(isinstance(value, str) for value in pointers.values()):
            raise ValueError("component redundancy row pointers must be string-valued")


def render_markdown(payload: Mapping[str, Any]) -> str:
    audit = payload["component_redundancy_audit"]
    recommendation = audit["global_recommendation"]
    lines = [
        "# DGT component redundancy audit",
        "",
        f"- Audit status: `{audit['audit_status']}`",
        f"- Global recommendation: `{recommendation['recommendation']}`",
        f"- Confirmed redundant: `{', '.join(recommendation['confirmed_redundant_components']) or 'none'}`",
        f"- Inconclusive: `{', '.join(recommendation['inconclusive_components']) or 'none'}`",
        "",
        "## Component verdicts",
        "",
    ]
    for row in audit["components"]:
        lines.append(
            f"- `{row['component_id']}`: `{row['verdict']}` "
            f"(delta `{row['quality_delta']}`, null `{row['null_decomposition']['classification']}`)"
        )
    lines.extend(["", "## Not claimed", ""])
    for item in audit["not_claimed"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def fingerprint_payload(payload: Mapping[str, Any], *, generated_at: str) -> dict[str, Any]:
    audit = payload["component_redundancy_audit"]
    source_artifacts = audit["source_artifacts"]
    return {
        "schema_id": "bedc-quality-lab:canonical-report-fingerprint",
        "report_name": "dgt-component-redundancy-audit",
        "json_artifact": CANONICAL_JSON_ARTIFACT,
        "markdown_artifact": CANONICAL_MARKDOWN_ARTIFACT,
        "producer_command": ["python3", PRODUCER],
        "input_fingerprint": _json_digest(source_artifacts),
        "output_digest": _json_digest(payload),
        "inputs": {"source_artifacts": source_artifacts},
        "generated_by": {"runner": PRODUCER, "generated_at": generated_at},
    }


def write_artifacts(payload: Mapping[str, Any], *, root: Path, generated_at: str | None = None) -> None:
    validate_payload(payload)
    _write_json(root / CANONICAL_JSON_ARTIFACT, payload)
    markdown_path = root / CANONICAL_MARKDOWN_ARTIFACT
    markdown_path.parent.mkdir(parents=True, exist_ok=True)
    markdown_path.write_text(render_markdown(payload), encoding="utf-8")
    _write_json(
        root / CANONICAL_FINGERPRINT_ARTIFACT,
        fingerprint_payload(payload, generated_at=generated_at or datetime.now(timezone.utc).isoformat()),
    )

"""Shared L1 admissibility protocol over owner-produced metric packets."""

from __future__ import annotations

from datetime import datetime, timezone
import json
from pathlib import Path
from typing import Any, Mapping, Sequence


SCHEMA_ID = "bedc-quality-lab:l1-admissibility-audit"
ARTIFACT_ID = "bedc-quality-lab:l1-admissibility-audit"
PRODUCER = "bedc_quality_lab.l1_admissibility_audit"
CANONICAL_JSON_ARTIFACT = "reports/canonical/l1-admissibility-audit.json"
CANONICAL_MARKDOWN_ARTIFACT = "reports/canonical/l1-admissibility-audit.md"
FINGERPRINT_ARTIFACT = "reports/canonical/l1-admissibility-audit.fingerprint.json"
DEFAULT_GENERATED_AT = "2026-06-18T00:00:00+00:00"

GATE_CARD_STATUSES = ("not_ready", "pass", "kill", "abstain", "block")
REQUIRED_DEPENDENCIES = (
    {
        "dependency_id": "canonical-sha",
        "source_issue": 1556,
        "evidence_ref": "github:issue:1556",
        "description": "canonical metrics producer SHA is recorded by the owner surface",
    },
    {
        "dependency_id": "claim-artifact-consistency",
        "source_issue": 1547,
        "evidence_ref": "github:issue:1547",
        "description": "claim-artifact consistency gate has resolved for the source metrics",
    },
    {
        "dependency_id": "run-interface-freeze",
        "source_issue": 1553,
        "evidence_ref": "github:issue:1553",
        "description": "run-interface contract is stable before L1 admission is adjudicated",
    },
)
PROTOCOL_THRESHOLDS = {
    "base_margin_min": 0.05,
    "negative_control_max": 0.02,
    "leakage_score_max": 0.0,
    "memorization_score_max": 0.0,
    "order_sentinel_min": 0.0,
}
GATE_IDS = (
    "L1A-HG1-READINESS",
    "L1A-HG2-SCHEMA",
    "L1A-HG3-BASE",
    "L1A-HG4-NEGATIVE-CONTROL",
    "L1A-HG5-LEAKAGE",
    "L1A-HG6-MEMORIZATION",
    "L1A-HG7-ORDER",
)
NOT_CLAIMED = (
    "The audit does not generate task data, train models, select splits, calibrate evaluators, or define per-surface semantics.",
    "The audit does not tune thresholds from observed artifacts.",
    "A not_ready gate card is an execution state, not a positive or negative L1 audit result.",
)


def _now(generated_at: str | None) -> str:
    return generated_at or datetime.now(timezone.utc).isoformat()


def _json_digest(payload: Any) -> str:
    normalized = json.dumps(payload, sort_keys=True, separators=(",", ":"), default=str)
    import hashlib

    return hashlib.sha256(normalized.encode("utf-8")).hexdigest()


def _pointer_value(payload: Mapping[str, Any], pointer: str) -> Any:
    if pointer == "$":
        return payload
    if not pointer.startswith("$."):
        return None
    cursor: Any = payload
    for part in pointer[2:].split("."):
        if isinstance(cursor, Mapping) and part in cursor:
            cursor = cursor[part]
        else:
            return None
    return cursor


def _resolve_artifact_pointer(root: Path, artifact_pointer: str) -> Any:
    if ":" not in artifact_pointer:
        return None
    artifact, pointer = artifact_pointer.split(":", 1)
    artifact_path = Path(artifact)
    if artifact_path.is_absolute() or ".." in artifact_path.parts:
        return None
    path = root / artifact_path
    if not path.exists():
        return None
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return None
    return _pointer_value(payload, pointer)


def default_metrics_payload() -> dict[str, Any]:
    return {
        "schema_id": "bedc-quality-lab:l1-owner-metrics-packet",
        "owner_surface": "unresolved",
        "canonical_sha": None,
        "run_interface_frozen": False,
        "claim_artifact_consistency_status": "missing",
        "base_accuracy_l95": None,
        "chance_accuracy_u95": None,
        "negative_control_delta": None,
        "leakage_score": None,
        "memorization_score": None,
        "order_sentinel_margin": None,
        "owner_metrics_ref": "not-ready:missing-owner-local-canonical-metrics",
    }


def load_metrics_payload(root: Path, metrics_pointer: str | None = None) -> dict[str, Any]:
    if metrics_pointer is None:
        return default_metrics_payload()
    resolved = _resolve_artifact_pointer(root, metrics_pointer)
    if not isinstance(resolved, Mapping):
        payload = default_metrics_payload()
        payload["owner_metrics_ref"] = metrics_pointer
        return payload
    return dict(resolved)


def _dependency_statuses(metrics: Mapping[str, Any]) -> list[dict[str, Any]]:
    checks = {
        "canonical-sha": bool(metrics.get("canonical_sha")),
        "claim-artifact-consistency": metrics.get("claim_artifact_consistency_status") == "pass",
        "run-interface-freeze": metrics.get("run_interface_frozen") is True,
    }
    rows: list[dict[str, Any]] = []
    for dependency in REQUIRED_DEPENDENCIES:
        dependency_id = dependency["dependency_id"]
        ready = checks[dependency_id]
        rows.append(
            {
                **dependency,
                "status": "ready" if ready else "missing",
                "ready": ready,
            }
        )
    return rows


def _metric_number(metrics: Mapping[str, Any], key: str) -> float | None:
    value = metrics.get(key)
    if value is None:
        return None
    try:
        return float(value)
    except (TypeError, ValueError):
        return None


def _gate(gate_id: str, status: str, reason: str, evidence_pointer: str, *, actual: Any = None, threshold: Any = None) -> dict[str, Any]:
    return {
        "gate_id": gate_id,
        "status": status,
        "reason": reason,
        "evidence_pointer": evidence_pointer,
        "actual": actual,
        "threshold": threshold,
    }


def evaluate_owner_metrics(metrics: Mapping[str, Any]) -> dict[str, Any]:
    dependencies = _dependency_statuses(metrics)
    missing_dependencies = [row["dependency_id"] for row in dependencies if not row["ready"]]
    if missing_dependencies:
        return {
            "status": "not_ready",
            "reason": "required upstream readiness dependency is missing",
            "failed_gate": "L1A-HG1-READINESS",
            "dependency_statuses": dependencies,
            "hardgates": {
                "L1A-HG1-READINESS": _gate(
                    "L1A-HG1-READINESS",
                    "fail",
                    "upstream dependency missing",
                    "$.dependency_statuses",
                    actual=missing_dependencies,
                    threshold="all dependencies ready",
                )
            },
        }

    required_metrics = (
        "base_accuracy_l95",
        "chance_accuracy_u95",
        "negative_control_delta",
        "leakage_score",
        "memorization_score",
        "order_sentinel_margin",
    )
    missing_metrics = [key for key in required_metrics if _metric_number(metrics, key) is None]
    if missing_metrics:
        return {
            "status": "block",
            "reason": "owner metrics packet is incomplete",
            "failed_gate": "L1A-HG2-SCHEMA",
            "dependency_statuses": dependencies,
            "hardgates": {
                "L1A-HG1-READINESS": _gate("L1A-HG1-READINESS", "pass", "dependencies ready", "$.dependency_statuses"),
                "L1A-HG2-SCHEMA": _gate(
                    "L1A-HG2-SCHEMA",
                    "fail",
                    "required owner metric missing",
                    "$.owner_metrics",
                    actual=missing_metrics,
                    threshold="complete fixed metrics schema",
                ),
            },
        }

    base_margin = _metric_number(metrics, "base_accuracy_l95") - _metric_number(metrics, "chance_accuracy_u95")  # type: ignore[operator]
    negative_delta = _metric_number(metrics, "negative_control_delta")
    leakage = _metric_number(metrics, "leakage_score")
    memorization = _metric_number(metrics, "memorization_score")
    order_margin = _metric_number(metrics, "order_sentinel_margin")
    gates = {
        "L1A-HG1-READINESS": _gate("L1A-HG1-READINESS", "pass", "dependencies ready", "$.dependency_statuses"),
        "L1A-HG2-SCHEMA": _gate("L1A-HG2-SCHEMA", "pass", "owner metrics schema complete", "$.owner_metrics"),
        "L1A-HG3-BASE": _gate(
            "L1A-HG3-BASE",
            "pass" if base_margin >= PROTOCOL_THRESHOLDS["base_margin_min"] else "fail",
            "base lower confidence bound clears chance upper confidence bound by the fixed margin",
            "$.owner_metrics",
            actual=base_margin,
            threshold=PROTOCOL_THRESHOLDS["base_margin_min"],
        ),
        "L1A-HG4-NEGATIVE-CONTROL": _gate(
            "L1A-HG4-NEGATIVE-CONTROL",
            "pass" if negative_delta <= PROTOCOL_THRESHOLDS["negative_control_max"] else "fail",  # type: ignore[operator]
            "negative control remains below the fixed maximum delta",
            "$.owner_metrics.negative_control_delta",
            actual=negative_delta,
            threshold=PROTOCOL_THRESHOLDS["negative_control_max"],
        ),
        "L1A-HG5-LEAKAGE": _gate(
            "L1A-HG5-LEAKAGE",
            "pass" if leakage <= PROTOCOL_THRESHOLDS["leakage_score_max"] else "fail",  # type: ignore[operator]
            "leakage sentinel must be zero",
            "$.owner_metrics.leakage_score",
            actual=leakage,
            threshold=PROTOCOL_THRESHOLDS["leakage_score_max"],
        ),
        "L1A-HG6-MEMORIZATION": _gate(
            "L1A-HG6-MEMORIZATION",
            "pass" if memorization <= PROTOCOL_THRESHOLDS["memorization_score_max"] else "fail",  # type: ignore[operator]
            "memorization sentinel must be zero",
            "$.owner_metrics.memorization_score",
            actual=memorization,
            threshold=PROTOCOL_THRESHOLDS["memorization_score_max"],
        ),
        "L1A-HG7-ORDER": _gate(
            "L1A-HG7-ORDER",
            "pass" if order_margin >= PROTOCOL_THRESHOLDS["order_sentinel_min"] else "fail",  # type: ignore[operator]
            "order sentinel margin must not be negative",
            "$.owner_metrics.order_sentinel_margin",
            actual=order_margin,
            threshold=PROTOCOL_THRESHOLDS["order_sentinel_min"],
        ),
    }
    failed = [gate_id for gate_id, row in gates.items() if row["status"] != "pass"]
    if not failed:
        status = "pass"
        reason = "all fixed L1 admissibility gates passed"
    elif any(gate_id in failed for gate_id in ("L1A-HG5-LEAKAGE", "L1A-HG6-MEMORIZATION")):
        status = "kill"
        reason = "leakage or memorization sentinel failed"
    elif failed == ["L1A-HG3-BASE"]:
        status = "abstain"
        reason = "base evidence does not clear chance by the fixed margin"
    else:
        status = "block"
        reason = "one or more non-leakage L1 admissibility gates failed"
    return {
        "status": status,
        "reason": reason,
        "failed_gate": failed[0] if failed else None,
        "dependency_statuses": dependencies,
        "hardgates": gates,
        "computed_metrics": {
            "base_margin": base_margin,
            "negative_control_delta": negative_delta,
            "leakage_score": leakage,
            "memorization_score": memorization,
            "order_sentinel_margin": order_margin,
        },
    }


def _axis_projection(status: str) -> dict[str, str]:
    if status == "pass":
        return {
            "scientific_claim_status": "pass",
            "hardgate_status": "pass",
            "decision_status": "pass",
            "ladder_state": "ready",
        }
    if status == "abstain":
        return {
            "scientific_claim_status": "scoped-boundary",
            "hardgate_status": "fail",
            "decision_status": "scoped-boundary",
            "ladder_state": "boundary",
        }
    if status == "kill":
        return {
            "scientific_claim_status": "bounded-negative",
            "hardgate_status": "fail",
            "decision_status": "bounded-negative",
            "ladder_state": "l1-bounded-negative",
        }
    return {
        "scientific_claim_status": "blocked",
        "hardgate_status": "fail",
        "decision_status": "blocked",
        "ladder_state": "blocked",
    }


def build_payload(
    *,
    root: Path | None = None,
    owner_metrics: Mapping[str, Any] | None = None,
    metrics_pointer: str | None = None,
    generated_at: str | None = DEFAULT_GENERATED_AT,
) -> dict[str, Any]:
    active_root = root or Path(".")
    metrics = dict(owner_metrics) if owner_metrics is not None else load_metrics_payload(active_root, metrics_pointer)
    gate_card = evaluate_owner_metrics(metrics)
    status = gate_card["status"]
    axes = _axis_projection(status)
    payload = {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "generated_at": _now(generated_at),
        "producer": PRODUCER,
        "source_artifacts": {
            "owner_metrics": metrics.get("owner_metrics_ref", metrics_pointer or "not-ready:missing-owner-local-canonical-metrics"),
            "canonical_sha_dependency": "github:issue:1556",
            "claim_artifact_consistency_dependency": "github:issue:1547",
            "run_interface_freeze_dependency": "github:issue:1553",
        },
        "protocol": {
            "schema_id": SCHEMA_ID,
            "allowed_statuses": list(GATE_CARD_STATUSES),
            "thresholds": dict(PROTOCOL_THRESHOLDS),
            "gate_ids": list(GATE_IDS),
            "negative_controls": ["negative_control_delta"],
            "sentinels": ["leakage_score", "memorization_score", "order_sentinel_margin"],
        },
        "owner_metrics": metrics,
        "dependency_statuses": gate_card["dependency_statuses"],
        "hardgates": gate_card["hardgates"],
        "gate_card": {
            "status": status,
            "allowed_statuses": list(GATE_CARD_STATUSES),
            "reason": gate_card["reason"],
            "failed_gate": gate_card["failed_gate"],
            "canonical_auxiliary_report": {
                "artifact": CANONICAL_JSON_ARTIFACT,
                "pointer": "$.gate_card",
                "projection_role": "shared-l1-admissibility-gate-card",
            },
        },
        "claim_boundary": {
            "status": axes["scientific_claim_status"],
            "source_status": status,
            "scope": "shared L1 admissibility audit over owner-local canonical metrics only",
        },
        "status_axes": axes,
        "not_claimed": list(NOT_CLAIMED),
    }
    if "computed_metrics" in gate_card:
        payload["computed_metrics"] = gate_card["computed_metrics"]
    validate_payload(payload)
    return payload


def validate_payload(payload: Mapping[str, Any]) -> None:
    required = {
        "schema_id",
        "artifact_id",
        "generated_at",
        "producer",
        "source_artifacts",
        "protocol",
        "owner_metrics",
        "dependency_statuses",
        "hardgates",
        "gate_card",
        "claim_boundary",
        "status_axes",
        "not_claimed",
    }
    if not required.issubset(payload):
        missing = sorted(required - set(payload))
        raise ValueError(f"L1 admissibility payload missing required keys: {', '.join(missing)}")
    if payload["schema_id"] != SCHEMA_ID or payload["artifact_id"] != ARTIFACT_ID:
        raise ValueError("L1 admissibility identity mismatch")
    protocol = payload["protocol"]
    if not isinstance(protocol, Mapping) or protocol.get("thresholds") != PROTOCOL_THRESHOLDS:
        raise ValueError("L1 admissibility thresholds must match the fixed protocol")
    if protocol.get("gate_ids") != list(GATE_IDS):
        raise ValueError("L1 admissibility gate ids mismatch")
    gate_card = payload["gate_card"]
    if not isinstance(gate_card, Mapping) or gate_card.get("status") not in GATE_CARD_STATUSES:
        raise ValueError("L1 admissibility gate-card status domain mismatch")
    hardgates = payload["hardgates"]
    if not isinstance(hardgates, Mapping) or not set(hardgates).issubset(set(GATE_IDS)):
        raise ValueError("L1 admissibility hardgate ids are outside the fixed protocol")
    for gate_id, row in hardgates.items():
        if not isinstance(row, Mapping) or row.get("gate_id") != gate_id or row.get("status") not in {"pass", "fail"}:
            raise ValueError(f"L1 admissibility hardgate row invalid: {gate_id}")
    expected = evaluate_owner_metrics(payload["owner_metrics"])
    expected_status = expected["status"]
    if gate_card.get("status") != expected_status or gate_card.get("failed_gate") != expected["failed_gate"]:
        raise ValueError("L1 admissibility gate-card does not match owner metrics")
    axes = payload["status_axes"]
    if axes != _axis_projection(expected_status):
        raise ValueError("L1 admissibility status-axis projection mismatch")


def render_markdown(payload: Mapping[str, Any]) -> str:
    validate_payload(payload)
    lines = [
        "# L1 Admissibility Audit",
        "",
        f"- Status: `{payload['gate_card']['status']}`",
        f"- Reason: {payload['gate_card']['reason']}",
        f"- Failed gate: `{payload['gate_card']['failed_gate']}`",
        "",
        "## Hardgates",
        "",
        "| gate | status | reason |",
        "| --- | --- | --- |",
    ]
    for gate_id in GATE_IDS:
        row = payload["hardgates"].get(gate_id)
        if isinstance(row, Mapping):
            lines.append(f"| `{gate_id}` | `{row['status']}` | {row['reason']} |")
    lines.extend(["", "## Dependencies", "", "| dependency | status | source |", "| --- | --- | --- |"])
    for row in payload["dependency_statuses"]:
        lines.append(f"| `{row['dependency_id']}` | `{row['status']}` | `{row['evidence_ref']}` |")
    lines.extend(["", "## Not Claimed", ""])
    for item in payload["not_claimed"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def write_artifacts(
    *,
    root: str | Path = ".",
    owner_metrics: Mapping[str, Any] | None = None,
    metrics_pointer: str | None = None,
    generated_at: str | None = DEFAULT_GENERATED_AT,
) -> dict[str, Any]:
    root_path = Path(root)
    payload = build_payload(
        root=root_path,
        owner_metrics=owner_metrics,
        metrics_pointer=metrics_pointer,
        generated_at=generated_at,
    )
    json_path = root_path / CANONICAL_JSON_ARTIFACT
    markdown_path = root_path / CANONICAL_MARKDOWN_ARTIFACT
    json_path.parent.mkdir(parents=True, exist_ok=True)
    markdown_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    markdown_path.write_text(render_markdown(payload), encoding="utf-8")
    return payload


__all__ = [
    "ARTIFACT_ID",
    "CANONICAL_JSON_ARTIFACT",
    "CANONICAL_MARKDOWN_ARTIFACT",
    "DEFAULT_GENERATED_AT",
    "FINGERPRINT_ARTIFACT",
    "GATE_CARD_STATUSES",
    "GATE_IDS",
    "PRODUCER",
    "PROTOCOL_THRESHOLDS",
    "SCHEMA_ID",
    "build_payload",
    "default_metrics_payload",
    "evaluate_owner_metrics",
    "load_metrics_payload",
    "render_markdown",
    "validate_payload",
    "write_artifacts",
]

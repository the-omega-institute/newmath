"""Fail-closed certified claim entry gate."""

from __future__ import annotations

import json
from typing import Any, Mapping

from bedc_quality_lab.audit import _REQUIRED_PROJECTION_FIELDS
from bedc_quality_lab.claim_projection import (
    project_certificate_guided_claim,
    require_certificate_guided_projection_source,
)
from bedc_quality_lab.claim_terms import FORBIDDEN_POSITIVE_CLAIM_TERMS
from bedc_quality_lab.schema import SCHEMA_ID


MALFORMED_EVIDENCE = "malformed-evidence"
NO_CLASSIFIER_SHIFT = "no-classifier-shift"
CONTROL_UNRESOLVED = "control-unresolved"
OVERCLAIM = "overclaim"
NOT_REJECTED = "not-rejected"


def _decision(
    *,
    rejected: bool,
    reason: str,
    evidence_basis: Mapping[str, Any],
    timestamp_iso: str,
) -> dict[str, Any]:
    return {
        "rejected": bool(rejected),
        "reason": reason,
        "evidence_basis": dict(evidence_basis),
        "decided_at": timestamp_iso,
    }


def _malformed(*, detail: str, timestamp_iso: str, evidence_basis: Mapping[str, Any] | None = None) -> dict[str, Any]:
    basis = dict(evidence_basis or {})
    basis["malformed_detail"] = detail
    return _decision(
        rejected=True,
        reason=MALFORMED_EVIDENCE,
        evidence_basis=basis,
        timestamp_iso=timestamp_iso,
    )


def _schema_detail(evidence_payload: Mapping[str, Any]) -> str | None:
    schema_id = evidence_payload.get("schema_id")
    if schema_id is None:
        return "missing-schema-id"
    if schema_id != SCHEMA_ID:
        return "schema-id-mismatch"
    return None


def _text_for_term_scan(value: Any) -> str:
    if isinstance(value, (dict, list, tuple)):
        return json.dumps(value, sort_keys=True).lower()
    return str(value).lower()


def _forbidden_claim_term_hits(certificate_payload: Mapping[str, Any] | None) -> list[str]:
    if certificate_payload is None:
        return []
    text = _text_for_term_scan(certificate_payload)
    return [term for term in FORBIDDEN_POSITIVE_CLAIM_TERMS if term.lower() in text]


def _classifier_shift_basis(projection_payload: Mapping[str, Any]) -> dict[str, Any]:
    main = projection_payload["main_verdict"]
    return {
        "main_surface_delta_count": main.get("surface_delta_count"),
        "main_shift_information": main.get("shift_information"),
        "main_structural_discovery": main.get("structural_discovery"),
        "main_verdict": main.get("verdict"),
    }


def _has_classifier_shift(projection_payload: Mapping[str, Any]) -> bool:
    main = projection_payload["main_verdict"]
    return bool(main.get("surface_delta_count")) and bool(main.get("shift_information"))


def _control_basis(projection_payload: Mapping[str, Any]) -> dict[str, Any]:
    baseline = projection_payload["matched_random_baseline"]
    return {
        "control_surface_delta_count": baseline.get("surface_delta_count"),
        "control_shift_information": baseline.get("shift_information"),
        "control_structural_discovery": baseline.get("structural_discovery"),
        "control_positive_discovery": baseline.get("positive_discovery"),
        "control_verdict": baseline.get("verdict"),
    }


def _control_unresolved_or_positive(projection_payload: Mapping[str, Any]) -> bool:
    baseline = projection_payload["matched_random_baseline"]
    if baseline.get("positive_discovery") is True or baseline.get("verdict") == "positive":
        return True
    return not (
        bool(baseline.get("surface_delta_count"))
        and bool(baseline.get("shift_information"))
        and baseline.get("structural_discovery") is True
    )


def reject_certified_claim(
    certificate_payload: Mapping[str, Any] | None,
    evidence_payload: Mapping[str, Any],
    *,
    timestamp_iso: str,
) -> dict[str, Any]:
    schema_detail = _schema_detail(evidence_payload)
    if schema_detail is not None:
        return _malformed(
            detail=schema_detail,
            timestamp_iso=timestamp_iso,
            evidence_basis={"source_schema_id": evidence_payload.get("schema_id")},
        )

    try:
        require_certificate_guided_projection_source(evidence_payload)
        projection = project_certificate_guided_claim(evidence_payload)
    except (KeyError, TypeError, ValueError) as exc:
        return _malformed(detail=f"projection-unavailable:{exc}", timestamp_iso=timestamp_iso)

    projection_payload = projection.to_dict()
    missing = [field for field in _REQUIRED_PROJECTION_FIELDS if field not in projection_payload]
    if missing:
        return _malformed(
            detail=f"projection-fields-missing:{','.join(missing)}",
            timestamp_iso=timestamp_iso,
            evidence_basis=projection_payload.get("evidence_basis", {}),
        )

    evidence_basis = {
        **projection.evidence_basis,
        "main_claim_status": projection.main_claim_status,
        "claim_gate": projection.claim_gate,
        **_classifier_shift_basis(projection_payload),
        **_control_basis(projection_payload),
    }

    if not _has_classifier_shift(projection_payload):
        return _decision(
            rejected=True,
            reason=NO_CLASSIFIER_SHIFT,
            evidence_basis=evidence_basis,
            timestamp_iso=timestamp_iso,
        )

    if _control_unresolved_or_positive(projection_payload):
        return _decision(
            rejected=True,
            reason=CONTROL_UNRESOLVED,
            evidence_basis=evidence_basis,
            timestamp_iso=timestamp_iso,
        )

    hits = _forbidden_claim_term_hits(certificate_payload)
    if hits:
        return _decision(
            rejected=True,
            reason=OVERCLAIM,
            evidence_basis={**evidence_basis, "forbidden_claim_term_hits": hits},
            timestamp_iso=timestamp_iso,
        )

    return _decision(
        rejected=False,
        reason=NOT_REJECTED,
        evidence_basis={**evidence_basis, "forbidden_claim_term_hits": []},
        timestamp_iso=timestamp_iso,
    )

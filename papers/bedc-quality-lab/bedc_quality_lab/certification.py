"""Certificate record issuance for terminal quality verdicts."""

from __future__ import annotations

import hashlib
import json
from typing import Any, Mapping


CERTIFICATION_RECORD_KIND = "certification-record"
_VALID_VERDICTS = {
    "accepted",
    "rejected",
    "demoted",
    "ledger-only",
    "positive-discovery",
}


def _canonical_json_digest(payload: Mapping[str, Any]) -> str:
    canonical = json.dumps(
        payload,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
    )
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def _required_string(mapping: Mapping[str, Any], key: str) -> str:
    value = mapping[key]
    if not isinstance(value, str) or not value:
        raise ValueError(f"{key} must be a non-empty string")
    return value


def _optional_string(mapping: Mapping[str, Any], key: str) -> str | None:
    value = mapping.get(key)
    if value is None:
        return None
    if not isinstance(value, str) or not value:
        raise ValueError(f"{key} must be a non-empty string or None")
    return value


def issue_certification_record(
    model_identity: Mapping[str, Any],
    verdict_decision: Mapping[str, Any],
    *,
    timestamp_iso: str,
    source_ref: str,
    previous_certificate_id: str | None = None,
) -> dict[str, Any]:
    if not isinstance(timestamp_iso, str) or not timestamp_iso:
        raise ValueError("timestamp_iso must be a non-empty string")
    if not isinstance(source_ref, str) or not source_ref:
        raise ValueError("source_ref must be a non-empty string")
    if previous_certificate_id is not None and (
        not isinstance(previous_certificate_id, str) or not previous_certificate_id
    ):
        raise ValueError("previous_certificate_id must be a non-empty string or None")

    verdict = _required_string(verdict_decision, "verdict")
    if verdict not in _VALID_VERDICTS:
        raise ValueError(f"verdict must be one of {sorted(_VALID_VERDICTS)!r}")
    evidence_basis = verdict_decision["evidence_basis"]
    if not isinstance(evidence_basis, Mapping):
        raise TypeError("evidence_basis must be a mapping")

    record = {
        "record_kind": CERTIFICATION_RECORD_KIND,
        "source_ref": source_ref,
        "model_id": _required_string(model_identity, "model_id"),
        "model_version": _optional_string(model_identity, "model_version"),
        "classifier_id": _optional_string(model_identity, "classifier_id"),
        "scope_id": _optional_string(model_identity, "scope_id"),
        "verdict": verdict,
        "reason": _required_string(verdict_decision, "reason"),
        "decided_at": _required_string(verdict_decision, "decided_at"),
        "issued_at": timestamp_iso,
        "evidence_basis_digest": _canonical_json_digest(evidence_basis),
        "previous_certificate_id": previous_certificate_id,
    }
    return {
        "certificate_id": _canonical_json_digest(record),
        **record,
    }

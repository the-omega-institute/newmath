"""Append-only certification ledger publication and audit."""

from __future__ import annotations

from datetime import datetime
from typing import Any, Mapping

from .canonical_digest import canonical_json_digest
from .certification import CERTIFICATION_RECORD_KIND


CERTIFICATION_LEDGER_KIND = "certification-ledger"
CERTIFICATION_LEDGER_ENTRY_KIND = "certification-ledger-entry"

_LEDGER_KEYS = {
    "ledger_kind",
    "source_ref",
    "entries",
    "head_certificate_id",
    "head_entry_digest",
    "entry_count",
}
_ENTRY_KEYS = {
    "entry_kind",
    "certificate_id",
    "previous_certificate_id",
    "published_at",
    "source_ref",
    "certificate_source_ref",
    "previous_entry_digest",
    "entry_digest",
}


def empty_certification_ledger(*, source_ref: str | None = None) -> dict[str, Any]:
    if source_ref is not None and (
        not isinstance(source_ref, str) or not source_ref
    ):
        raise ValueError("source_ref must be a non-empty string or None")
    return {
        "ledger_kind": CERTIFICATION_LEDGER_KIND,
        "source_ref": source_ref,
        "entries": [],
        "head_certificate_id": None,
        "head_entry_digest": None,
        "entry_count": 0,
    }


def publish_certification_record(
    ledger_state: Mapping[str, Any],
    certificate_record: Mapping[str, Any],
    *,
    timestamp_iso: str,
    source_ref: str,
) -> dict[str, Any]:
    ledger_errors = audit_certification_ledger(ledger_state)
    if ledger_errors:
        raise ValueError(f"ledger audit failed: {ledger_errors!r}")
    _require_timestamp(timestamp_iso)
    _require_non_empty_string(source_ref, "source_ref")

    if certificate_record.get("record_kind") != CERTIFICATION_RECORD_KIND:
        raise ValueError("certificate_record must be a certification record")
    certificate_id = _require_non_empty_string(
        certificate_record.get("certificate_id"),
        "certificate_id",
    )
    record_basis = dict(certificate_record)
    record_basis.pop("certificate_id", None)
    if canonical_json_digest(record_basis) != certificate_id:
        raise ValueError("certificate_id mismatch")

    previous_certificate_id = certificate_record.get("previous_certificate_id")
    if previous_certificate_id is not None and (
        not isinstance(previous_certificate_id, str) or not previous_certificate_id
    ):
        raise ValueError("previous_certificate_id must be a non-empty string or None")
    certificate_source_ref = _require_non_empty_string(
        certificate_record.get("source_ref"),
        "certificate_source_ref",
    )

    entries = _entry_copies(ledger_state["entries"])
    head_certificate_id = ledger_state["head_certificate_id"]
    if certificate_id == head_certificate_id:
        return _ledger_copy(ledger_state)
    if any(entry["certificate_id"] == certificate_id for entry in entries):
        raise ValueError("certificate_id already appears before ledger head")
    if not entries:
        if previous_certificate_id is not None:
            raise ValueError("genesis certificate must not have a previous id")
    elif previous_certificate_id != head_certificate_id:
        raise ValueError("certificate chain discontinuity")

    entry_basis = {
        "entry_kind": CERTIFICATION_LEDGER_ENTRY_KIND,
        "certificate_id": certificate_id,
        "previous_certificate_id": previous_certificate_id,
        "published_at": timestamp_iso,
        "source_ref": source_ref,
        "certificate_source_ref": certificate_source_ref,
        "previous_entry_digest": ledger_state["head_entry_digest"],
    }
    entry = {
        **entry_basis,
        "entry_digest": canonical_json_digest(entry_basis),
    }
    next_entries = [*entries, entry]
    return {
        "ledger_kind": CERTIFICATION_LEDGER_KIND,
        "source_ref": ledger_state["source_ref"],
        "entries": next_entries,
        "head_certificate_id": certificate_id,
        "head_entry_digest": entry["entry_digest"],
        "entry_count": len(next_entries),
    }


def audit_certification_ledger(ledger_state: Mapping[str, Any]) -> list[str]:
    errors: list[str] = []
    if not isinstance(ledger_state, Mapping):
        return ["ledger state must be a mapping"]
    if set(ledger_state.keys()) != _LEDGER_KEYS:
        errors.append("ledger field set mismatch")
    if ledger_state.get("ledger_kind") != CERTIFICATION_LEDGER_KIND:
        errors.append("ledger kind mismatch")
    source_ref = ledger_state.get("source_ref")
    if source_ref is not None and (not isinstance(source_ref, str) or not source_ref):
        errors.append("ledger source_ref must be a non-empty string or None")

    entries_value = ledger_state.get("entries")
    if not isinstance(entries_value, list):
        errors.append("entries must be a list")
        entries: list[Any] = []
    else:
        entries = entries_value

    seen: set[str] = set()
    previous_certificate_id: str | None = None
    previous_entry_digest: str | None = None
    head_certificate_id: str | None = None
    head_entry_digest: str | None = None

    for index, entry in enumerate(entries):
        if not isinstance(entry, Mapping):
            errors.append(f"entry {index} must be a mapping")
            previous_certificate_id = None
            previous_entry_digest = None
            continue
        if set(entry.keys()) != _ENTRY_KEYS:
            errors.append(f"entry {index} field set mismatch")
        if entry.get("entry_kind") != CERTIFICATION_LEDGER_ENTRY_KIND:
            errors.append(f"entry {index} kind mismatch")

        certificate_id = entry.get("certificate_id")
        if not isinstance(certificate_id, str) or not certificate_id:
            errors.append(f"entry {index} certificate_id must be a non-empty string")
            certificate_id = None
        elif certificate_id in seen:
            errors.append(f"duplicate certificate id: {certificate_id}")
        else:
            seen.add(certificate_id)

        entry_previous_certificate_id = entry.get("previous_certificate_id")
        if entry_previous_certificate_id is not None and (
            not isinstance(entry_previous_certificate_id, str)
            or not entry_previous_certificate_id
        ):
            errors.append(
                f"entry {index} previous_certificate_id must be a non-empty string or None"
            )
        elif entry_previous_certificate_id != previous_certificate_id:
            errors.append(f"entry {index} certificate-chain discontinuity")

        entry_previous_digest = entry.get("previous_entry_digest")
        if entry_previous_digest is not None and (
            not isinstance(entry_previous_digest, str) or not entry_previous_digest
        ):
            errors.append(
                f"entry {index} previous_entry_digest must be a non-empty string or None"
            )
        elif entry_previous_digest != previous_entry_digest:
            errors.append(f"entry {index} previous_entry_digest mismatch")

        for key in ("published_at", "source_ref", "certificate_source_ref"):
            value = entry.get(key)
            if not isinstance(value, str) or not value:
                errors.append(f"entry {index} {key} must be a non-empty string")
        if isinstance(entry.get("published_at"), str) and entry.get("published_at"):
            try:
                _require_timestamp(entry["published_at"])
            except ValueError:
                errors.append(f"entry {index} published_at must be an ISO timestamp")

        entry_digest = entry.get("entry_digest")
        if not isinstance(entry_digest, str) or not entry_digest:
            errors.append(f"entry {index} entry_digest must be a non-empty string")
        else:
            digest_basis = dict(entry)
            digest_basis.pop("entry_digest", None)
            if canonical_json_digest(digest_basis) != entry_digest:
                errors.append(f"entry {index} entry digest mismatch")

        if isinstance(certificate_id, str):
            head_certificate_id = certificate_id
            previous_certificate_id = certificate_id
        else:
            previous_certificate_id = None
        if isinstance(entry_digest, str):
            head_entry_digest = entry_digest
            previous_entry_digest = entry_digest
        else:
            previous_entry_digest = None

    if ledger_state.get("entry_count") != len(entries):
        errors.append("entry_count mismatch")
    if ledger_state.get("head_certificate_id") != head_certificate_id:
        errors.append("head_certificate_id mismatch")
    if ledger_state.get("head_entry_digest") != head_entry_digest:
        errors.append("head_entry_digest mismatch")
    return errors


def _require_non_empty_string(value: Any, key: str) -> str:
    if not isinstance(value, str) or not value:
        raise ValueError(f"{key} must be a non-empty string")
    return value


def _require_timestamp(value: Any) -> str:
    timestamp = _require_non_empty_string(value, "timestamp_iso")
    parse_value = timestamp[:-1] + "+00:00" if timestamp.endswith("Z") else timestamp
    try:
        datetime.fromisoformat(parse_value)
    except ValueError as exc:
        raise ValueError("timestamp_iso must be an ISO timestamp") from exc
    return timestamp


def _entry_copies(entries: Any) -> list[dict[str, Any]]:
    return [dict(entry) for entry in entries]


def _ledger_copy(ledger_state: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "ledger_kind": ledger_state["ledger_kind"],
        "source_ref": ledger_state["source_ref"],
        "entries": _entry_copies(ledger_state["entries"]),
        "head_certificate_id": ledger_state["head_certificate_id"],
        "head_entry_digest": ledger_state["head_entry_digest"],
        "entry_count": ledger_state["entry_count"],
    }

"""Append-only certification revocation ledger publication and audit."""

from __future__ import annotations

from datetime import datetime
from typing import Any, Mapping

from .canonical_digest import canonical_json_digest


CERTIFICATION_REVOCATION_LEDGER_KIND = "certification-revocation-ledger"
CERTIFICATION_REVOCATION_LEDGER_ENTRY_KIND = "certification-revocation-ledger-entry"

_LEDGER_KEYS = {
    "ledger_kind",
    "source_ref",
    "entries",
    "head_revocation_id",
    "head_entry_digest",
    "entry_count",
}
_ENTRY_KEYS = {
    "entry_kind",
    "revocation_id",
    "revoked_certificate_id",
    "previous_revocation_id",
    "reason",
    "published_at",
    "source_ref",
    "certificate_source_ref",
    "previous_entry_digest",
    "entry_digest",
}


def issue_certification_revocation_record(
    *,
    revoked_certificate_id: str,
    previous_revocation_id: str | None = None,
    reason: str,
    source_ref: str,
    certificate_source_ref: str,
) -> dict[str, Any]:
    record = {
        "revoked_certificate_id": _require_non_empty_string(
            revoked_certificate_id,
            "revoked_certificate_id",
        ),
        "previous_revocation_id": _require_optional_string(
            previous_revocation_id,
            "previous_revocation_id",
        ),
        "reason": _require_non_empty_string(reason, "reason"),
        "source_ref": _require_non_empty_string(source_ref, "source_ref"),
        "certificate_source_ref": _require_non_empty_string(
            certificate_source_ref,
            "certificate_source_ref",
        ),
    }
    return {
        "revocation_id": canonical_json_digest(record),
        **record,
    }


def empty_certification_revocation_ledger(
    *,
    source_ref: str | None = None,
) -> dict[str, Any]:
    if source_ref is not None and not _is_non_empty_string(source_ref):
        raise ValueError("source_ref must be a non-empty string or None")
    return {
        "ledger_kind": CERTIFICATION_REVOCATION_LEDGER_KIND,
        "source_ref": source_ref,
        "entries": [],
        "head_revocation_id": None,
        "head_entry_digest": None,
        "entry_count": 0,
    }


def publish_certification_revocation(
    ledger_state: Mapping[str, Any],
    revocation_record: Mapping[str, Any],
    *,
    timestamp_iso: str,
    source_ref: str,
) -> dict[str, Any]:
    ledger_errors = audit_certification_revocation_ledger(ledger_state)
    if ledger_errors:
        raise ValueError(f"ledger audit failed: {ledger_errors!r}")
    _require_timestamp(timestamp_iso)
    _require_non_empty_string(source_ref, "source_ref")

    revocation_id = _require_non_empty_string(
        revocation_record.get("revocation_id"),
        "revocation_id",
    )
    record_basis = dict(revocation_record)
    record_basis.pop("revocation_id", None)
    if canonical_json_digest(record_basis) != revocation_id:
        raise ValueError("revocation_id mismatch")

    revoked_certificate_id = _require_non_empty_string(
        revocation_record.get("revoked_certificate_id"),
        "revoked_certificate_id",
    )
    previous_revocation_id = _require_optional_string(
        revocation_record.get("previous_revocation_id"),
        "previous_revocation_id",
    )
    reason = _require_non_empty_string(revocation_record.get("reason"), "reason")
    _require_non_empty_string(revocation_record.get("source_ref"), "record source_ref")
    certificate_source_ref = _require_non_empty_string(
        revocation_record.get("certificate_source_ref"),
        "certificate_source_ref",
    )

    entries = _entry_copies(ledger_state["entries"])
    head_revocation_id = ledger_state["head_revocation_id"]
    if revocation_id == head_revocation_id:
        return _ledger_copy(ledger_state)
    if not entries:
        raise ValueError("empty revocation ledger has no head")
    if any(entry["revocation_id"] == revocation_id for entry in entries):
        raise ValueError("revocation_id already appears before ledger head")
    if previous_revocation_id != head_revocation_id:
        raise ValueError("revocation chain discontinuity")

    entry_basis = {
        "entry_kind": CERTIFICATION_REVOCATION_LEDGER_ENTRY_KIND,
        "revocation_id": revocation_id,
        "revoked_certificate_id": revoked_certificate_id,
        "previous_revocation_id": previous_revocation_id,
        "reason": reason,
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
        "ledger_kind": CERTIFICATION_REVOCATION_LEDGER_KIND,
        "source_ref": ledger_state["source_ref"],
        "entries": next_entries,
        "head_revocation_id": revocation_id,
        "head_entry_digest": entry["entry_digest"],
        "entry_count": len(next_entries),
    }


def audit_certification_revocation_ledger(ledger_state: Mapping[str, Any]) -> list[str]:
    errors: list[str] = []
    if not isinstance(ledger_state, Mapping):
        return ["ledger state must be a mapping"]
    if set(ledger_state.keys()) != _LEDGER_KEYS:
        errors.append("ledger field set mismatch")
    if ledger_state.get("ledger_kind") != CERTIFICATION_REVOCATION_LEDGER_KIND:
        errors.append("ledger kind mismatch")
    source_ref = ledger_state.get("source_ref")
    if source_ref is not None and not _is_non_empty_string(source_ref):
        errors.append("ledger source_ref must be a non-empty string or None")

    entries_value = ledger_state.get("entries")
    if not isinstance(entries_value, list):
        errors.append("entries must be a list")
        entries: list[Any] = []
    else:
        entries = entries_value

    seen: set[str] = set()
    previous_revocation_id: str | None = None
    previous_entry_digest: str | None = None
    head_revocation_id: str | None = None
    head_entry_digest: str | None = None

    for index, entry in enumerate(entries):
        if not isinstance(entry, Mapping):
            errors.append(f"entry {index} must be a mapping")
            previous_revocation_id = None
            previous_entry_digest = None
            continue
        if set(entry.keys()) != _ENTRY_KEYS:
            errors.append(f"entry {index} field set mismatch")
        if entry.get("entry_kind") != CERTIFICATION_REVOCATION_LEDGER_ENTRY_KIND:
            errors.append(f"entry {index} kind mismatch")

        revocation_id = entry.get("revocation_id")
        if not _is_non_empty_string(revocation_id):
            errors.append(f"entry {index} revocation_id must be a non-empty string")
            revocation_id = None
        elif revocation_id in seen:
            errors.append(f"duplicate revocation id: {revocation_id}")
        else:
            seen.add(revocation_id)

        entry_previous_revocation_id = entry.get("previous_revocation_id")
        if entry_previous_revocation_id is not None and (
            not _is_non_empty_string(entry_previous_revocation_id)
        ):
            errors.append(
                f"entry {index} previous_revocation_id must be a non-empty string or None"
            )
        elif entry_previous_revocation_id != previous_revocation_id:
            errors.append(f"entry {index} revocation-chain discontinuity")

        entry_previous_digest = entry.get("previous_entry_digest")
        if entry_previous_digest is not None and (
            not _is_non_empty_string(entry_previous_digest)
        ):
            errors.append(
                f"entry {index} previous_entry_digest must be a non-empty string or None"
            )
        elif entry_previous_digest != previous_entry_digest:
            errors.append(f"entry {index} previous_entry_digest mismatch")

        for key in (
            "revoked_certificate_id",
            "reason",
            "published_at",
            "source_ref",
            "certificate_source_ref",
        ):
            value = entry.get(key)
            if not _is_non_empty_string(value):
                errors.append(f"entry {index} {key} must be a non-empty string")
        if _is_non_empty_string(entry.get("published_at")):
            try:
                _require_timestamp(entry["published_at"])
            except ValueError:
                errors.append(f"entry {index} published_at must be an ISO timestamp")

        entry_digest = entry.get("entry_digest")
        if not _is_non_empty_string(entry_digest):
            errors.append(f"entry {index} entry_digest must be a non-empty string")
        else:
            digest_basis = dict(entry)
            digest_basis.pop("entry_digest", None)
            if canonical_json_digest(digest_basis) != entry_digest:
                errors.append(f"entry {index} entry digest mismatch")

        if _is_non_empty_string(revocation_id):
            head_revocation_id = revocation_id
            previous_revocation_id = revocation_id
        else:
            previous_revocation_id = None
        if _is_non_empty_string(entry_digest):
            head_entry_digest = entry_digest
            previous_entry_digest = entry_digest
        else:
            previous_entry_digest = None

    entry_count = ledger_state.get("entry_count")
    if type(entry_count) is not int:
        errors.append("entry_count must be an integer")
    elif entry_count != len(entries):
        errors.append("entry_count mismatch")
    if ledger_state.get("head_revocation_id") != head_revocation_id:
        errors.append("head_revocation_id mismatch")
    if ledger_state.get("head_entry_digest") != head_entry_digest:
        errors.append("head_entry_digest mismatch")
    return errors


def _require_non_empty_string(value: Any, key: str) -> str:
    if not _is_non_empty_string(value):
        raise ValueError(f"{key} must be a non-empty string")
    return value


def _require_optional_string(value: Any, key: str) -> str | None:
    if value is None:
        return None
    if not _is_non_empty_string(value):
        raise ValueError(f"{key} must be a non-empty string or None")
    return value


def _is_non_empty_string(value: Any) -> bool:
    return type(value) is str and bool(value)


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
        "head_revocation_id": ledger_state["head_revocation_id"],
        "head_entry_digest": ledger_state["head_entry_digest"],
        "entry_count": ledger_state["entry_count"],
    }

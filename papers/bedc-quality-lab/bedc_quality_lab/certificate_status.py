"""Certificate standing resolution across certification and revocation ledgers."""

from __future__ import annotations

from typing import Any, Mapping

from .certification_ledger import audit_certification_ledger
from .certification_revocation import audit_certification_revocation_ledger


def resolve_certificate_status(
    cert_ledger_state: Mapping[str, Any],
    revocation_ledger_state: Mapping[str, Any],
    certificate_id: str,
) -> dict[str, Any]:
    if type(certificate_id) is not str or not certificate_id:
        raise ValueError("certificate_id must be a non-empty string")

    cert_errors = audit_certification_ledger(cert_ledger_state)
    if cert_errors:
        raise ValueError(f"certification ledger audit failed: {cert_errors!r}")

    revocation_errors = audit_certification_revocation_ledger(revocation_ledger_state)
    if revocation_errors:
        raise ValueError(f"revocation ledger audit failed: {revocation_errors!r}")

    certified_ids = {entry["certificate_id"] for entry in cert_ledger_state["entries"]}
    matching_revocations = [
        entry
        for entry in revocation_ledger_state["entries"]
        if entry["revoked_certificate_id"] == certificate_id
    ]

    if len(matching_revocations) > 1:
        raise ValueError("duplicate revocation for certificate_id")

    if matching_revocations:
        if certificate_id not in certified_ids:
            raise ValueError("revocation references unknown certificate_id")
        revocation_entry = matching_revocations[0]
        return {
            "status": "revoked",
            "certificate_id": certificate_id,
            "revocation_id": revocation_entry["revocation_id"],
            "reason": revocation_entry["reason"],
            "published_at": revocation_entry["published_at"],
            "revocation_source_ref": revocation_entry["source_ref"],
            "certificate_source_ref": revocation_entry["certificate_source_ref"],
        }

    if certificate_id in certified_ids:
        return {"status": "active", "certificate_id": certificate_id}
    return {"status": "unknown", "certificate_id": certificate_id}

"""Fleet standing projection across certification and revocation ledgers."""

from __future__ import annotations

from typing import Any, Mapping

from .certification_ledger import audit_certification_ledger
from .certification_revocation import audit_certification_revocation_ledger
from .certificate_status import resolve_certificate_status


def project_certificate_standings(
    cert_ledger_state: Mapping[str, Any],
    revocation_ledger_state: Mapping[str, Any],
) -> dict[str, Any]:
    cert_errors = audit_certification_ledger(cert_ledger_state)
    if cert_errors:
        raise ValueError(f"certification ledger audit failed: {cert_errors!r}")

    revocation_errors = audit_certification_revocation_ledger(revocation_ledger_state)
    if revocation_errors:
        raise ValueError(f"revocation ledger audit failed: {revocation_errors!r}")

    certified_ids = [entry["certificate_id"] for entry in cert_ledger_state["entries"]]
    certified_id_set = set(certified_ids)

    revocations_by_certificate_id: dict[str, list[Mapping[str, Any]]] = {}
    for entry in revocation_ledger_state["entries"]:
        revoked_certificate_id = entry["revoked_certificate_id"]
        revocations_by_certificate_id.setdefault(revoked_certificate_id, []).append(
            entry
        )

    for entries in revocations_by_certificate_id.values():
        if len(entries) > 1:
            raise ValueError("duplicate revocation for certificate_id")

    standings: dict[str, dict[str, Any]] = {}
    for certificate_id in certified_ids:
        standings[certificate_id] = resolve_certificate_status(
            cert_ledger_state,
            revocation_ledger_state,
            certificate_id,
        )

    integrity_faults = []
    for entry in revocation_ledger_state["entries"]:
        revoked_certificate_id = entry["revoked_certificate_id"]
        if revoked_certificate_id not in certified_id_set:
            integrity_faults.append(
                {
                    "fault": "revocation references unknown certificate_id",
                    "certificate_id": revoked_certificate_id,
                    "revocation_id": entry["revocation_id"],
                    "revocation_source_ref": entry["source_ref"],
                    "certificate_source_ref": entry["certificate_source_ref"],
                }
            )

    return {"standings": standings, "integrity_faults": integrity_faults}

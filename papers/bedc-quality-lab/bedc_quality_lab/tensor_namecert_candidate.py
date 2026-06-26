"""Lab-local Tensor NameCert candidate projection."""

from __future__ import annotations

from copy import deepcopy
from dataclasses import asdict, dataclass
from typing import Any, Mapping

from .schema import QualityEvidenceEnvelope

_STATUS_KEYS = (
    "status",
    "cert_status",
    "certificate_status",
    "verification_status",
)

_CLOSED_STATUS = {
    "closed",
    "sufficient",
}


@dataclass(frozen=True)
class TensorNameCertCandidate:
    name: str
    source_spec: dict[str, Any]
    pattern_spec: dict[str, Any]
    classifier_spec: dict[str, Any]
    stab_cert: dict[str, Any]
    ledger_policy: dict[str, Any]
    scope_seal: dict[str, Any]
    closure_status: dict[str, str]
    evidence_envelope_ref: dict[str, str]

    @classmethod
    def from_quality_evidence_envelope(
        cls,
        envelope: QualityEvidenceEnvelope,
    ) -> "TensorNameCertCandidate":
        return from_quality_evidence_envelope(envelope)

    @classmethod
    def from_envelope(cls, envelope: QualityEvidenceEnvelope) -> "TensorNameCertCandidate":
        return cls.from_quality_evidence_envelope(envelope)

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


def from_quality_evidence_envelope(envelope: QualityEvidenceEnvelope) -> TensorNameCertCandidate:
    source_spec = deepcopy(envelope.source_spec)
    pattern_spec = deepcopy(envelope.pattern_spec)
    classifier_spec = deepcopy(envelope.classifier_spec)
    stab_cert = deepcopy(envelope.stability_spec)
    ledger_policy = _ledger_policy_from_envelope(envelope)
    scope_seal = _scope_seal_from_envelope(envelope)
    evidence_envelope_ref = {
        "schema_id": envelope.schema_id,
        "run_id": envelope.run_id,
    }

    closure_rows = _candidate_closure_rows(
        source_spec,
        pattern_spec,
        classifier_spec,
        stab_cert,
        ledger_policy,
        scope_seal,
    )
    closure_status = {field: level for field, level, _provenance in closure_rows}

    return TensorNameCertCandidate(
        name=f"TensorNameCertCandidate:{envelope.run_id}",
        source_spec=source_spec,
        pattern_spec=pattern_spec,
        classifier_spec=classifier_spec,
        stab_cert=stab_cert,
        ledger_policy=ledger_policy,
        scope_seal=scope_seal,
        closure_status=closure_status,
        evidence_envelope_ref=evidence_envelope_ref,
    )


from_envelope = from_quality_evidence_envelope


def _ledger_policy_from_envelope(envelope: QualityEvidenceEnvelope) -> dict[str, Any]:
    return {
        "ledger_gaps": list(envelope.ledger_gaps),
        "debt_items": list(envelope.debt_items),
        "artifacts": dict(envelope.artifacts),
        "bedc_refs": list(envelope.bedc_refs),
        "active_gap_count": len(envelope.ledger_gaps),
        "debt_item_count": len(envelope.debt_items),
    }


def _scope_seal_from_envelope(envelope: QualityEvidenceEnvelope) -> dict[str, Any]:
    return {
        "boundary": "lab-local candidate projection",
        "source": envelope.schema_id,
        "formal_bedc_certificate": False,
        "candidate_json_artifact": False,
        "bedc_closurestatus": False,
        "evidence_envelope_schema_extension": False,
        "not_claimed": [
            "not a formal BEDC NameCert",
            "not a BEDC closurestatus",
            "not an evidence-envelope schema extension",
        ],
    }


def closure_status_rows(candidate: TensorNameCertCandidate) -> list[tuple[str, str, str]]:
    return _candidate_closure_rows(
        candidate.source_spec,
        candidate.pattern_spec,
        candidate.classifier_spec,
        candidate.stab_cert,
        candidate.ledger_policy,
        candidate.scope_seal,
    )


def _candidate_closure_rows(
    source_spec: Mapping[str, Any],
    pattern_spec: Mapping[str, Any],
    classifier_spec: Mapping[str, Any],
    stab_cert: Mapping[str, Any],
    ledger_policy: Mapping[str, Any],
    scope_seal: Mapping[str, Any],
) -> list[tuple[str, str, str]]:
    return [
        _spec_closure_row("source_spec", source_spec),
        _spec_closure_row("pattern_spec", pattern_spec),
        _spec_closure_row("classifier_spec", classifier_spec),
        _spec_closure_row("stab_cert", stab_cert),
        _ledger_closure_row(ledger_policy),
        _scope_seal_closure_row(scope_seal),
    ]


def _spec_closure_row(field: str, spec: Mapping[str, Any]) -> tuple[str, str, str]:
    if not _has_required_name(spec):
        return (field, "missing", "missing_name")

    if _has_critical_gaps(spec):
        return (field, "partial", "critical_gaps")

    status = _explicit_status(spec)
    if status is None:
        return (field, "present", "name_only")
    if status in _CLOSED_STATUS:
        return (field, "closed", "explicit_status")
    return (field, "partial", "explicit_status")


def _ledger_closure_row(ledger_policy: Mapping[str, Any]) -> tuple[str, str, str]:
    if "ledger_gaps" not in ledger_policy or "debt_items" not in ledger_policy:
        return ("ledger_policy", "missing", "missing_ledger_policy")

    if _has_critical_gaps(ledger_policy):
        return ("ledger_policy", "partial", "critical_gaps")

    rows = [
        *ledger_policy.get("ledger_gaps", []),
        *ledger_policy.get("debt_items", []),
    ]
    if not rows:
        return ("ledger_policy", "present", "explicit_empty_ledger_policy")

    row_statuses = [_status_from_ledger_row(row) for row in rows]
    if row_statuses and all(status in _CLOSED_STATUS for status in row_statuses):
        return ("ledger_policy", "closed", "explicit_closed_ledger_rows")
    return ("ledger_policy", "partial", "open_ledger_rows")


def _scope_seal_closure_row(scope_seal: Mapping[str, Any]) -> tuple[str, str, str]:
    level = _scope_seal_closure(scope_seal)
    if level == "partial" and not _has_scope_boundary(scope_seal):
        return ("scope_seal", "partial", "missing_scope_boundary")
    if level == "partial":
        return ("scope_seal", "partial", "missing_not_claimed")
    return ("scope_seal", "closed", "explicit_scope_seal")


def _scope_seal_closure(scope_seal: Mapping[str, Any]) -> str:
    if not _has_scope_boundary(scope_seal):
        return "partial"
    if not _has_nonempty_value(scope_seal.get("not_claimed")):
        return "partial"
    return "closed"


def _has_required_name(spec: Mapping[str, Any]) -> bool:
    name = spec.get("name")
    return isinstance(name, str) and bool(name.strip())


def _has_critical_gaps(mapping: Mapping[str, Any]) -> bool:
    return _has_nonempty_value(mapping.get("critical_gaps"))


def _has_nonempty_value(value: Any) -> bool:
    if isinstance(value, str):
        return bool(value.strip())
    if isinstance(value, (list, tuple, set, dict)):
        return bool(value)
    return value is not None and bool(value)


def _has_scope_boundary(scope_seal: Mapping[str, Any]) -> bool:
    return (
        scope_seal.get("boundary") == "lab-local candidate projection"
        and isinstance(scope_seal.get("source"), str)
        and bool(scope_seal.get("source", "").strip())
        and scope_seal.get("formal_bedc_certificate") is False
        and scope_seal.get("candidate_json_artifact") is False
        and scope_seal.get("bedc_closurestatus") is False
        and scope_seal.get("evidence_envelope_schema_extension") is False
    )


def _explicit_status(spec: Mapping[str, Any]) -> str | None:
    for key in _STATUS_KEYS:
        value = spec.get(key)
        if isinstance(value, str) and value.strip():
            return value.strip().lower()
    return None


def _status_from_ledger_row(row: Any) -> str:
    if not isinstance(row, str):
        return "weak"
    parts = [part.strip() for part in row.split(";")]
    for part in parts:
        if part.startswith("status="):
            value = part.removeprefix("status=").strip().lower()
            return value if value else "weak"
    return "weak"

"""Lab-local Tensor NameCert candidate projection."""

from __future__ import annotations

from copy import deepcopy
from dataclasses import asdict, dataclass
from typing import Any, Mapping

from .schema import QualityEvidenceEnvelope


_RAW_TO_CLOSURE = {
    "missing": "warning",
    "weak": "partial",
    "sufficient": "closed",
    "unused": "none",
}

_STATUS_KEYS = (
    "status",
    "cert_status",
    "certificate_status",
    "verification_status",
)

_SUFFICIENT_STATUS = {
    "certified",
    "closed",
    "complete",
    "kernel-checked",
    "ok",
    "passed",
    "sufficient",
    "verified",
}

_UNUSED_STATUS = {
    "absent",
    "n/a",
    "none",
    "not-applicable",
    "unused",
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

    closure_status = {
        "source_spec": _spec_closure(source_spec),
        "pattern_spec": _spec_closure(pattern_spec),
        "classifier_spec": _spec_closure(classifier_spec),
        "stab_cert": _spec_closure(stab_cert),
        "ledger_policy": _ledger_closure(ledger_policy),
        "scope_seal": _closure_label("sufficient"),
    }

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
    }


def _spec_closure(spec: Mapping[str, Any]) -> str:
    if not _has_required_name(spec):
        return _closure_label("missing")

    status = _explicit_status(spec)
    if status is None:
        return _closure_label("sufficient")
    if status in _UNUSED_STATUS:
        return _closure_label("unused")
    if status in _SUFFICIENT_STATUS:
        return _closure_label("sufficient")
    return _closure_label("weak")


def _ledger_closure(ledger_policy: Mapping[str, Any]) -> str:
    rows = [
        *ledger_policy.get("ledger_gaps", []),
        *ledger_policy.get("debt_items", []),
    ]
    if not rows:
        return _closure_label("unused")

    row_statuses = [_status_from_ledger_row(row) for row in rows]
    if row_statuses and all(status in _SUFFICIENT_STATUS for status in row_statuses):
        return _closure_label("sufficient")
    return _closure_label("weak")


def _has_required_name(spec: Mapping[str, Any]) -> bool:
    name = spec.get("name")
    return isinstance(name, str) and bool(name.strip())


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


def _closure_label(raw_status: str) -> str:
    return _RAW_TO_CLOSURE[raw_status]

"""Finite scoped-certification projection for the BEDC quality lab."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Callable, Literal, Mapping, Optional, Sequence

from .ledger import LedgerRowKey, ledger_complete


CLAIM_SCOPE_SEAL_KEYS = frozenset(
    {"toy", "bounded", "theorem", "real_training", "production_forbidden"}
)
CLAIM_SCOPE_POSITIVE_KEYS = frozenset({"toy", "bounded", "theorem", "real_training"})
CLOSED_CLAIM_SCOPE_SEAL = {
    "status": "closed",
    "toy": True,
    "bounded": True,
    "theorem": False,
    "real_training": False,
    "production_forbidden": True,
}
ORDERED_SCOPE_LEVELS = (
    "toy",
    "bounded-design",
    "backend-evidence",
    "theorem-backed",
    "real-training",
    "production-forbidden",
)
SCOPE_LEVEL_RANK = {scope: index for index, scope in enumerate(ORDERED_SCOPE_LEVELS)}
ScopeGateStatus = Literal["pass", "fail"]
PointerLookup = Callable[[Mapping[str, Any], Optional[str]], Any]
DEFAULT_SCOPE_CLAIM_POINTER = "$.scope_claim"
DEFAULT_SCOPE_EVIDENCE_POINTER = "$.scope_evidence"


@dataclass(frozen=True)
class Scope:
    domain_ids: frozenset[str]
    model_id: str
    admitted_family_id: str
    behavior_id: str


@dataclass(frozen=True)
class ScopeExpansionEvidence:
    edge: str
    pointer: str
    status: str = "resolved"


@dataclass(frozen=True)
class ScopeExpansionClaim:
    source_scope: str
    target_scope: str
    evidence: Mapping[str, ScopeExpansionEvidence]


@dataclass(frozen=True)
class ScopeExpansionGate:
    status: ScopeGateStatus
    reason: str
    failed_edge: str | None
    failed_pointer: str | None
    required_edges: tuple[str, ...]

    def as_dict(self) -> dict[str, object]:
        return {
            "status": self.status,
            "reason": self.reason,
            "failed_edge": self.failed_edge,
            "failed_pointer": self.failed_pointer,
            "required_edges": list(self.required_edges),
        }


@dataclass(frozen=True)
class ScopedCertificate:
    scope: Scope
    classifier_id: str
    namecert_id: str
    required_rows: frozenset[LedgerRowKey]
    recorded_rows: frozenset[LedgerRowKey]
    certificate: Mapping[str, object]
    not_claimed_boundary: frozenset[str]


@dataclass(frozen=True)
class GlobalResolutionClaim:
    model_id: str
    behavior_family: frozenset[str]
    certificates: Sequence[ScopedCertificate]
    global_recorded_rows: frozenset[LedgerRowKey]


def scope_level_rank(scope: str) -> int | None:
    return SCOPE_LEVEL_RANK.get(scope)


def scope_expansion_edges(source_scope: str, target_scope: str) -> tuple[str, ...]:
    source_rank = scope_level_rank(source_scope)
    target_rank = scope_level_rank(target_scope)
    if source_rank is None or target_rank is None or target_rank <= source_rank:
        return ()
    return tuple(
        f"{ORDERED_SCOPE_LEVELS[index]}->{ORDERED_SCOPE_LEVELS[index + 1]}"
        for index in range(source_rank, target_rank)
    )


def scope_expansion_gate(claim: ScopeExpansionClaim) -> ScopeExpansionGate:
    if scope_level_rank(claim.source_scope) is None:
        return ScopeExpansionGate(
            status="fail",
            reason="unknown-source-scope",
            failed_edge=None,
            failed_pointer="$.scope_claim.source_scope",
            required_edges=(),
        )
    if scope_level_rank(claim.target_scope) is None:
        return ScopeExpansionGate(
            status="fail",
            reason="unknown-target-scope",
            failed_edge=None,
            failed_pointer="$.scope_claim.target_scope",
            required_edges=(),
        )
    required_edges = scope_expansion_edges(claim.source_scope, claim.target_scope)
    for edge in required_edges:
        evidence = claim.evidence.get(edge)
        if evidence is None:
            return ScopeExpansionGate(
                status="fail",
                reason="scope-expansion-evidence-missing",
                failed_edge=edge,
                failed_pointer=f"$.scope_evidence.{edge}",
                required_edges=required_edges,
            )
        if evidence.status != "resolved":
            return ScopeExpansionGate(
                status="fail",
                reason="scope-expansion-evidence-missing",
                failed_edge=edge,
                failed_pointer=evidence.pointer,
                required_edges=required_edges,
            )
        if not evidence.pointer:
            return ScopeExpansionGate(
                status="fail",
                reason="scope-expansion-evidence-missing",
                failed_edge=edge,
                failed_pointer=f"$.scope_evidence.{edge}.pointer",
                required_edges=required_edges,
            )
    return ScopeExpansionGate(
        status="pass",
        reason="scope-expansion-evidence-resolved",
        failed_edge=None,
        failed_pointer=None,
        required_edges=required_edges,
    )


def scope_payload_pointer(pointer: str | None, default: str) -> str:
    return pointer if isinstance(pointer, str) else default


def scope_claim_payload(
    payload: Mapping[str, Any],
    pointer_lookup: PointerLookup,
    *,
    scope_claim_pointer: str | None = None,
) -> Mapping[str, Any] | None:
    pointer = scope_payload_pointer(scope_claim_pointer, DEFAULT_SCOPE_CLAIM_POINTER)
    value = pointer_lookup(payload, pointer)
    return value if isinstance(value, Mapping) else None


def scope_evidence_payload(
    payload: Mapping[str, Any],
    pointer_lookup: PointerLookup,
    *,
    scope_evidence_pointer: str | None = None,
) -> Mapping[str, Any]:
    pointer = scope_payload_pointer(scope_evidence_pointer, DEFAULT_SCOPE_EVIDENCE_POINTER)
    value = pointer_lookup(payload, pointer)
    return value if isinstance(value, Mapping) else {}


def scope_expansion_evidence_from_payload(
    edge: str,
    cell: Any,
    payload: Mapping[str, Any],
    pointer_lookup: PointerLookup,
) -> ScopeExpansionEvidence:
    if isinstance(cell, Mapping):
        pointer = cell.get("pointer")
        status = str(cell.get("status", "resolved"))
        if isinstance(pointer, str) and pointer.startswith("$.") and pointer_lookup(payload, pointer) is None:
            status = "unresolved"
        return ScopeExpansionEvidence(edge=edge, pointer=pointer if isinstance(pointer, str) else "", status=status)
    return ScopeExpansionEvidence(edge=edge, pointer="", status="missing")


def scope_expansion_claim_from_payload(
    payload: Mapping[str, Any],
    pointer_lookup: PointerLookup,
    *,
    scope_claim_pointer: str | None = None,
    scope_evidence_pointer: str | None = None,
) -> ScopeExpansionClaim | None:
    claim = scope_claim_payload(
        payload,
        pointer_lookup,
        scope_claim_pointer=scope_claim_pointer,
    )
    if claim is None:
        return None
    source_scope = claim.get("source_scope")
    target_scope = claim.get("target_scope")
    if not isinstance(source_scope, str) or not isinstance(target_scope, str):
        return ScopeExpansionClaim(source_scope=str(source_scope), target_scope=str(target_scope), evidence={})
    evidence_payload = scope_evidence_payload(
        payload,
        pointer_lookup,
        scope_evidence_pointer=scope_evidence_pointer,
    )
    evidence = {
        edge: scope_expansion_evidence_from_payload(edge, cell, payload, pointer_lookup)
        for edge, cell in evidence_payload.items()
        if isinstance(edge, str)
    }
    return ScopeExpansionClaim(source_scope=source_scope, target_scope=target_scope, evidence=evidence)


def scope_expansion_gate_for_payload(
    payload: Mapping[str, Any],
    pointer_lookup: PointerLookup,
    *,
    scope_claim_pointer: str | None = None,
    scope_evidence_pointer: str | None = None,
) -> ScopeExpansionGate | None:
    claim = scope_expansion_claim_from_payload(
        payload,
        pointer_lookup,
        scope_claim_pointer=scope_claim_pointer,
        scope_evidence_pointer=scope_evidence_pointer,
    )
    return None if claim is None else scope_expansion_gate(claim)


def scope_rows(scope: Scope) -> frozenset[LedgerRowKey]:
    return frozenset(
        {LedgerRowKey("model", scope.model_id)}
        | {LedgerRowKey("source", f"{scope.model_id}:{domain_id}") for domain_id in scope.domain_ids}
        | {LedgerRowKey("perturbation", f"{scope.model_id}:{scope.admitted_family_id}")}
        | {LedgerRowKey("behavior", f"{scope.model_id}:{scope.behavior_id}")}
    )


def scoped_resolved(cert: ScopedCertificate) -> bool:
    return (
        cert.certificate.get("cert_status") == "certified"
        and ledger_complete(cert.required_rows, cert.recorded_rows)
        and bool(cert.not_claimed_boundary)
    )


def closed_claim_scope_seal(value: object) -> bool:
    if not isinstance(value, Mapping):
        return False
    if value.get("status") != "closed":
        return False
    for key in CLAIM_SCOPE_SEAL_KEYS:
        if not isinstance(value.get(key), bool):
            return False
    return value["production_forbidden"] is True and any(
        value[key] is True for key in CLAIM_SCOPE_POSITIVE_KEYS
    )


def behavior_family_rows(claim: GlobalResolutionClaim) -> frozenset[LedgerRowKey]:
    return frozenset(
        LedgerRowKey("behavior-family", f"{claim.model_id}:{behavior_id}")
        for behavior_id in claim.behavior_family
    )


def classifier_family_rows(claim: GlobalResolutionClaim) -> frozenset[LedgerRowKey]:
    return frozenset(
        LedgerRowKey(
            "classifier-family",
            f"{claim.model_id}:{cert.scope.behavior_id}:{cert.classifier_id}",
        )
        for cert in claim.certificates
    )


def namecert_family_rows(claim: GlobalResolutionClaim) -> frozenset[LedgerRowKey]:
    return frozenset(
        LedgerRowKey(
            "namecert-family",
            f"{claim.model_id}:{cert.scope.behavior_id}:{cert.namecert_id}",
        )
        for cert in claim.certificates
    )


def verification_rows(cert: ScopedCertificate) -> frozenset[LedgerRowKey]:
    if cert.certificate.get("verification_status") != "kernel-checked":
        return frozenset()
    prefix = f"{cert.scope.model_id}:{cert.scope.behavior_id}"
    return frozenset(
        LedgerRowKey("verification", f"{prefix}:{residue}")
        for residue in (
            "checked-statement",
            "statement-scope",
            "backend",
            "trust-boundary",
            "proof-dependencies",
            "translation-assumptions",
            "portability-boundary",
            "not-covered-behaviors",
        )
    )


def semantic_rows(cert: ScopedCertificate) -> frozenset[LedgerRowKey]:
    if not cert.certificate.get("semantic_globalizer"):
        return frozenset()
    prefix = f"{cert.scope.model_id}:{cert.scope.behavior_id}"
    return frozenset(
        LedgerRowKey("semantic", f"{prefix}:{residue}")
        for residue in (
            "positive",
            "negative",
            "ambiguous",
            "polysemy",
            "domain",
            "context",
            "drift",
            "unsupported-connotation",
            "not-claimed-semantics",
        )
    )


def bridge_rows(cert: ScopedCertificate) -> frozenset[LedgerRowKey]:
    if not cert.certificate.get("product_classifier"):
        return frozenset()
    prefix = f"{cert.scope.model_id}:{cert.scope.behavior_id}:{cert.classifier_id}"
    return frozenset(
        LedgerRowKey("bridge", f"{prefix}:{residue}")
        for residue in (
            "source-scopes",
            "classifier-boundary",
            "product-distinctions",
            "unified-separated-behaviors",
            "not-claimed-boundary",
        )
    )


def not_claimed_rows(cert: ScopedCertificate) -> frozenset[LedgerRowKey]:
    prefix = f"{cert.scope.model_id}:{cert.scope.behavior_id}"
    return frozenset(
        LedgerRowKey("not-claimed", f"{prefix}:{boundary}")
        for boundary in cert.not_claimed_boundary
    )


def global_ledger_row(claim: GlobalResolutionClaim) -> LedgerRowKey:
    return LedgerRowKey("global-ledger", claim.model_id)


def global_required_rows(claim: GlobalResolutionClaim) -> frozenset[LedgerRowKey]:
    rows: set[LedgerRowKey] = {global_ledger_row(claim)}
    rows.update(behavior_family_rows(claim))
    rows.update(classifier_family_rows(claim))
    rows.update(namecert_family_rows(claim))
    for cert in claim.certificates:
        rows.update(cert.required_rows)
        rows.update(verification_rows(cert))
        rows.update(semantic_rows(cert))
        rows.update(bridge_rows(cert))
        rows.update(not_claimed_rows(cert))
    return frozenset(rows)


def global_ledger_complete(claim: GlobalResolutionClaim) -> bool:
    return ledger_complete(global_required_rows(claim), claim.global_recorded_rows)


def globally_resolved(claim: GlobalResolutionClaim) -> bool:
    if any(cert.scope.model_id != claim.model_id for cert in claim.certificates):
        return False
    resolved_behaviors = frozenset(
        cert.scope.behavior_id for cert in claim.certificates if scoped_resolved(cert)
    )
    return claim.behavior_family.issubset(resolved_behaviors) and global_ledger_complete(claim)

"""Finite scoped-certification projection for the BEDC quality lab."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Mapping, Sequence

from .ledger import LedgerRowKey, ledger_complete


@dataclass(frozen=True)
class Scope:
    domain_ids: frozenset[str]
    model_id: str
    admitted_family_id: str
    behavior_id: str


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
    resolved_behaviors = frozenset(
        cert.scope.behavior_id for cert in claim.certificates if scoped_resolved(cert)
    )
    return claim.behavior_family.issubset(resolved_behaviors) and global_ledger_complete(claim)

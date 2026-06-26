"""Finite positive-discovery projection for the BEDC quality lab."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Mapping

from .classifier_shift import (
    ClassifierPassage,
    classifier_shift,
    shift_information,
    structural_discovery,
)
from .hardening import HardeningBackend, HardeningProfile, critical_hardening_gap
from .ledger import LedgerRowKey, ledger_complete
from .scope import GlobalResolutionClaim, ScopedCertificate, globally_resolved, scoped_resolved


NumberMap = Mapping[str, float]


@dataclass(frozen=True)
class DiscoveryClaim:
    passage: ClassifierPassage
    benefit_terms: NumberMap
    score_terms: NumberMap
    debt_terms: NumberMap
    ledger_required_rows: frozenset[LedgerRowKey]
    ledger_recorded_rows: frozenset[LedgerRowKey]
    public_cost_protocol: bool
    scope_sealed: bool
    not_claimed_boundary: frozenset[str]
    local_or_formal_witness: bool = True
    weight_profile_public: bool = True
    source_scope_public: bool = True
    target_scope_public: bool = True
    benefit_modes: frozenset[str] = field(default_factory=frozenset)
    omitted_debt_terms: NumberMap = field(default_factory=dict)
    scoped_certificate: ScopedCertificate | None = None
    global_claim: GlobalResolutionClaim | None = None
    hardening_profile: HardeningProfile | None = None
    hardening_backend: HardeningBackend | None = None
    critical_debt_rows: frozenset[LedgerRowKey] = field(default_factory=frozenset)
    reproducible_evidence: bool = False
    ndna_complete: bool = False
    ndna_anchored: bool = False
    ndna_namecert_compatible: bool = False
    ndna_ledger_complete: bool = False
    ndna_net_information: float = 0.0
    black_box_debt_reduction: float = 0.0
    black_box_score_cost: float = 0.0
    verification_assisted: bool = False
    verification_benefit: float = 0.0
    verification_required_rows: frozenset[LedgerRowKey] = field(default_factory=frozenset)
    verification_recorded_rows: frozenset[LedgerRowKey] = field(default_factory=frozenset)
    laundering_modes: frozenset[str] = field(default_factory=frozenset)


def _total(values: NumberMap) -> float:
    return float(sum(float(value) for value in values.values()))


def apparent_net_information(claim: DiscoveryClaim) -> float:
    return _total(claim.benefit_terms) - _total(claim.score_terms) - _total(claim.debt_terms)


def net_information(claim: DiscoveryClaim) -> float:
    return apparent_net_information(claim) - _total(claim.omitted_debt_terms)


def positive_information(claim: DiscoveryClaim) -> bool:
    return net_information(claim) > 0.0


def ledger_completion(claim: DiscoveryClaim) -> bool:
    return ledger_complete(claim.ledger_required_rows, claim.ledger_recorded_rows)


def protocol_complete(claim: DiscoveryClaim) -> bool:
    return (
        claim.public_cost_protocol
        and bool(claim.benefit_terms)
        and bool(claim.score_terms)
        and bool(claim.debt_terms)
        and claim.weight_profile_public
        and claim.source_scope_public
        and claim.target_scope_public
        and bool(claim.not_claimed_boundary)
    )


def protocol_scope_complete(claim: DiscoveryClaim) -> bool:
    if not claim.scope_sealed:
        return False
    if claim.global_claim is not None:
        return globally_resolved(claim.global_claim)
    if claim.scoped_certificate is not None:
        return scoped_resolved(claim.scoped_certificate)
    return True


def debt_complete(claim: DiscoveryClaim) -> bool:
    return not claim.omitted_debt_terms and ledger_completion(claim)


def critical_debt_free(claim: DiscoveryClaim) -> bool:
    if claim.critical_debt_rows:
        return False
    if claim.hardening_profile is not None and claim.hardening_backend is not None:
        return not critical_hardening_gap(claim.hardening_profile, claim.hardening_backend)
    return True


def certified_discovery(claim: DiscoveryClaim) -> bool:
    return (
        structural_discovery(claim.passage)
        and shift_information(claim.passage) > 0
        and claim.local_or_formal_witness
        and ledger_completion(claim)
        and bool(claim.not_claimed_boundary)
    )


def positive_discovery(claim: DiscoveryClaim) -> bool:
    return (
        certified_discovery(claim)
        and positive_information(claim)
        and protocol_complete(claim)
        and protocol_scope_complete(claim)
        and debt_complete(claim)
        and not claim.laundering_modes
    )


def benefit_modes(claim: DiscoveryClaim) -> frozenset[str]:
    explicit = frozenset(mode for mode in claim.benefit_modes if float(claim.benefit_terms.get(mode, 0.0)) > 0.0)
    inferred = frozenset(mode for mode, value in claim.benefit_terms.items() if float(value) > 0.0)
    return explicit | inferred


def benefit_modes_overlap(claim: DiscoveryClaim) -> bool:
    return positive_discovery(claim) and len(benefit_modes(claim)) > 1


def ndna_positive_criterion(claim: DiscoveryClaim) -> bool:
    return (
        certified_discovery(claim)
        and positive_information(claim)
        and protocol_complete(claim)
        and protocol_scope_complete(claim)
        and debt_complete(claim)
        and classifier_shift(claim.passage)
        and claim.ndna_complete
        and claim.ndna_anchored
        and claim.ndna_namecert_compatible
        and claim.ndna_ledger_complete
        and claim.ndna_net_information > 0.0
        and not claim.laundering_modes
    )


def strong_positive_discovery(claim: DiscoveryClaim) -> bool:
    return (
        positive_discovery(claim)
        and critical_debt_free(claim)
        and claim.reproducible_evidence
        and claim.public_cost_protocol
        and claim.ndna_complete
        and claim.ndna_anchored
        and claim.ndna_namecert_compatible
        and claim.ndna_ledger_complete
    )


def positive_black_box_resolution(claim: DiscoveryClaim) -> bool:
    return (
        protocol_scope_complete(claim)
        and claim.black_box_debt_reduction - claim.black_box_score_cost > 0.0
    )


def positive_discovery_resolution(claim: DiscoveryClaim) -> bool:
    return positive_discovery(claim) and positive_black_box_resolution(claim)


def verification_assisted_positive_discovery(claim: DiscoveryClaim) -> bool:
    return positive_discovery(claim) and claim.verification_assisted and claim.verification_benefit > 0.0


def verification_dependent(claim: DiscoveryClaim) -> bool:
    return verification_assisted_positive_discovery(claim) and net_information(claim) - claim.verification_benefit <= 0.0


def verification_cost_counted(claim: DiscoveryClaim) -> bool:
    if not claim.verification_assisted:
        return True
    return (
        _total({key: value for key, value in claim.score_terms.items() if "verification" in key}) > 0.0
        and ledger_complete(claim.verification_required_rows, claim.verification_recorded_rows)
    )


def discovery_becomes_positive_later(initial: DiscoveryClaim, later: DiscoveryClaim) -> bool:
    return certified_discovery(initial) and net_information(initial) <= 0.0 and positive_discovery(later)


def positive_status_decays(before: DiscoveryClaim, after: DiscoveryClaim) -> bool:
    return positive_discovery(before) and certified_discovery(after) and net_information(after) <= 0.0


def laundering_invalidates(claim: DiscoveryClaim) -> bool:
    return bool(claim.laundering_modes) and not positive_discovery(claim)


def capstone_positive_interpretability_discovery(claim: DiscoveryClaim) -> bool:
    return (
        positive_discovery(claim)
        and certified_discovery(claim)
        and classifier_shift(claim.passage)
        and ledger_completion(claim)
        and protocol_complete(claim)
        and protocol_scope_complete(claim)
        and debt_complete(claim)
        and net_information(claim) > 0.0
    )

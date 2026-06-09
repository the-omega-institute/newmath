"""Finite hardening taxonomy for ledger-only classifiers."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Mapping

from .ledger import LedgerEntry, LedgerRowKey, critical_gap, ledger_complete, ledger_gap


@dataclass(frozen=True)
class HardeningBackend:
    backend_id: str
    hardenable_rows: frozenset[LedgerRowKey]


@dataclass(frozen=True)
class HardeningProfile:
    certificate: Mapping[str, object]
    mode_rows: frozenset[LedgerRowKey]
    declared_mode_rows: frozenset[LedgerRowKey]
    open_mode_rows: frozenset[LedgerRowKey]
    ledger_required_rows: frozenset[LedgerRowKey]
    ledger_recorded_rows: frozenset[LedgerRowKey]
    critical_rows: frozenset[LedgerRowKey]
    hardened_rows: frozenset[LedgerRowKey]
    frontier_rows: frozenset[LedgerRowKey]
    non_hardenable_residue: frozenset[LedgerRowKey]
    empirical_stability: bool = False


def _certified(profile: HardeningProfile) -> bool:
    return profile.certificate.get("cert_status") == "certified"


def _residue_ledgered(profile: HardeningProfile) -> bool:
    return ledger_complete(profile.non_hardenable_residue, profile.ledger_recorded_rows)


def mode_gap(profile: HardeningProfile) -> frozenset[LedgerRowKey]:
    declared_closed = profile.declared_mode_rows - profile.open_mode_rows
    return ledger_gap(profile.mode_rows, declared_closed) | profile.open_mode_rows


def mode_complete(profile: HardeningProfile) -> bool:
    return not mode_gap(profile)


def backend_relative_hardenable(backend: HardeningBackend, row: LedgerRowKey) -> bool:
    return row in backend.hardenable_rows


def hardened(profile: HardeningProfile, row: LedgerRowKey) -> bool:
    return row in profile.hardened_rows


def hardened_implies_hardenable(
    profile: HardeningProfile,
    backend: HardeningBackend,
) -> bool:
    return profile.hardened_rows.issubset(backend.hardenable_rows)


def hardening_frontier(
    profile: HardeningProfile,
    backend: HardeningBackend,
) -> frozenset[LedgerRowKey]:
    return profile.frontier_rows & ledger_gap(backend.hardenable_rows, profile.hardened_rows)


def critical_hardening_gap(
    profile: HardeningProfile,
    backend: HardeningBackend,
) -> frozenset[LedgerRowKey]:
    required = profile.critical_rows & backend.hardenable_rows
    recorded = profile.hardened_rows | profile.frontier_rows | profile.ledger_recorded_rows
    missing = ledger_gap(required, recorded)
    adapters = tuple(
        LedgerEntry(row=row, source_ref=f"{backend.backend_id}:critical-hardening", critical=True)
        for row in missing
    )
    return critical_gap(adapters)


def ledger_only_classifier(profile: HardeningProfile) -> bool:
    return (
        _certified(profile)
        and mode_complete(profile)
        and ledger_complete(profile.ledger_required_rows, profile.ledger_recorded_rows)
        and _residue_ledgered(profile)
        and not profile.hardened_rows
    )


def partially_hardened_classifier(profile: HardeningProfile) -> bool:
    return (
        _certified(profile)
        and bool(profile.hardened_rows)
        and bool(profile.critical_rows - profile.hardened_rows)
    )


def fully_hardened_classifier(
    profile: HardeningProfile,
    backend: HardeningBackend,
) -> bool:
    return (
        _certified(profile)
        and mode_complete(profile)
        and ledger_complete(profile.ledger_required_rows, profile.ledger_recorded_rows)
        and _residue_ledgered(profile)
        and not critical_hardening_gap(profile, backend)
    )


def local_hardening_delta(
    before: HardeningProfile,
    after: HardeningProfile,
) -> frozenset[LedgerRowKey]:
    return ledger_gap(after.hardened_rows, before.hardened_rows)


def should_harden_immediately(
    backend: HardeningBackend,
    row: LedgerRowKey,
    net_gain_by_row: Mapping[LedgerRowKey, float],
) -> bool:
    return backend_relative_hardenable(backend, row) and float(net_gain_by_row.get(row, 0.0)) > 0.0

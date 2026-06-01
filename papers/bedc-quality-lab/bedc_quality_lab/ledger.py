"""Finite ledger row kernel and envelope adapters."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING, Any, Iterable, Mapping

if TYPE_CHECKING:
    from .debt import DebtAssessment


@dataclass(frozen=True, order=True)
class LedgerRowKey:
    kind: str
    residue: str


@dataclass(frozen=True)
class LedgerEntry:
    row: LedgerRowKey
    source_ref: str
    weight: float = 0.0
    critical: bool = False


@dataclass(frozen=True)
class LedgerGap:
    kind: str
    residue: str
    severity: str
    status: str


LedgerRowLike = LedgerEntry | LedgerRowKey


def _row_key(row: LedgerRowLike) -> LedgerRowKey:
    return row.row if isinstance(row, LedgerEntry) else row


def required_rows(target: Iterable[LedgerRowLike]) -> frozenset[LedgerRowKey]:
    return frozenset(_row_key(row) for row in target)


def recorded_rows(entries: Iterable[LedgerRowLike]) -> frozenset[LedgerRowKey]:
    return frozenset(_row_key(entry) for entry in entries)


def ledger_gap(
    required: Iterable[LedgerRowLike],
    recorded: Iterable[LedgerRowLike],
) -> frozenset[LedgerRowKey]:
    return required_rows(required) - recorded_rows(recorded)


def ledger_complete(
    required: Iterable[LedgerRowLike],
    recorded: Iterable[LedgerRowLike],
) -> bool:
    return not ledger_gap(required, recorded)


def ledger_debt(
    gap: Iterable[LedgerRowKey],
    cost_map: Mapping[LedgerRowKey, float],
) -> float:
    return float(sum(float(cost_map.get(row, 0.0)) for row in gap))


def critical_gap(gap: Iterable[LedgerEntry]) -> frozenset[LedgerRowKey]:
    return frozenset(entry.row for entry in gap if entry.critical)


def _metric_gap(metrics: Mapping[str, float]) -> LedgerGap | None:
    from .theorem_bound_quality import theorem_bound_ledger_gap

    if not any(
        key in metrics
        for key in (
            "theorem3_bound",
            "actual_recovery_error",
            "bound_margin",
            "normalized_gap_d",
            "whitening_deviation_epsilon",
        )
    ):
        return None
    return theorem_bound_ledger_gap(metrics)


def derive_ledger_gaps(
    metrics: Mapping[str, float],
    source_spec: Mapping[str, Any],
    classifier_spec: Mapping[str, Any],
    stability_spec: Mapping[str, Any],
    debt_assessment: DebtAssessment,
) -> list[LedgerGap]:
    """Derive canonical ledger gaps from the consensus producer surface."""
    del source_spec, classifier_spec, stability_spec
    required = [
        LedgerRowKey(item.kind, item.residue)
        for item in debt_assessment.items
    ]
    recorded = [
        LedgerRowKey(item.kind, item.residue)
        for item in debt_assessment.items
        if item.status == "closed"
    ]
    gap_rows = ledger_gap(required, recorded)
    item_by_row = {
        LedgerRowKey(item.kind, item.residue): item
        for item in debt_assessment.items
    }
    gaps = []
    for row in sorted(gap_rows):
        item = item_by_row[row]
        gaps.append(
            LedgerGap(
                kind=item.kind,
                residue=item.residue,
                severity=item.severity,
                status=item.status,
            )
        )
    metric_gap = _metric_gap(metrics)
    if metric_gap is not None:
        gaps.append(metric_gap)
    return gaps


def format_ledger_gaps(gaps: list[LedgerGap]) -> list[str]:
    return [
        (
            f"kind={gap.kind}; residue={gap.residue}; severity={gap.severity}; "
            f"status={gap.status}"
        )
        for gap in gaps
    ]

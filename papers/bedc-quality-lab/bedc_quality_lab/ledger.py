"""Ledger gap derivation for quality evidence envelopes."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping

from .debt import DebtAssessment


@dataclass(frozen=True)
class LedgerGap:
    residue: str
    severity: str
    status: str


def _metric_gap(metrics: Mapping[str, float]) -> LedgerGap | None:
    value = float(metrics.get("approx_identifiability_proxy", 0.0))
    if value >= 0.75:
        return None
    severity = "medium" if value >= 0.5 else "high"
    status = "partial" if value >= 0.5 else "open"
    return LedgerGap(
        residue="identifiability-proxy-margin",
        severity=severity,
        status=status,
    )


def derive_ledger_gaps(
    metrics: Mapping[str, float],
    source_spec: Mapping[str, Any],
    classifier_spec: Mapping[str, Any],
    stability_spec: Mapping[str, Any],
    debt_assessment: DebtAssessment,
) -> list[LedgerGap]:
    del source_spec, classifier_spec, stability_spec
    gaps = [
        LedgerGap(residue=item.residue, severity=item.severity, status=item.status)
        for item in debt_assessment.items
        if item.status != "closed"
    ]
    metric_gap = _metric_gap(metrics)
    if metric_gap is not None:
        gaps.append(metric_gap)
    return gaps


def format_ledger_gaps(gaps: list[LedgerGap]) -> list[str]:
    return [
        f"residue={gap.residue}; severity={gap.severity}; status={gap.status}"
        for gap in gaps
    ]

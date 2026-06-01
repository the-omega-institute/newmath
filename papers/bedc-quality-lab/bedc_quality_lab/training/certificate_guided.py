"""Certificate-guided objective helpers for lab-local training runners."""

from __future__ import annotations

from dataclasses import dataclass
import math
from typing import Any, Iterable, Mapping

from bedc_quality_lab.cost_protocol import REQUIRED_DEBT_ROWS
from bedc_quality_lab.ledger import LedgerRowKey


@dataclass(frozen=True)
class CertificateGuidedWeights:
    lambda_s: float = 0.25
    lambda_m: float = 0.50
    lambda_l: float = 0.75
    lambda_c: float = 1.00


@dataclass(frozen=True)
class CertificateGuidedLossBreakdown:
    margin: float
    stability: float
    ledger: float
    coverage: float
    deterministic_fallback: bool
    torch_arm: bool


def _finite_nonnegative(name: str, value: float) -> float:
    scalar = float(value)
    if not math.isfinite(scalar):
        raise ValueError(f"{name} must be finite")
    return max(0.0, scalar)


def _finite(name: str, value: float) -> float:
    scalar = float(value)
    if not math.isfinite(scalar):
        raise ValueError(f"{name} must be finite")
    return scalar


def _row_key(row: Any) -> LedgerRowKey:
    if isinstance(row, LedgerRowKey):
        return row
    if isinstance(row, Mapping):
        return LedgerRowKey(str(row["kind"]), str(row["residue"]))
    return LedgerRowKey(str(getattr(row, "kind")), str(getattr(row, "residue")))


def _row_status(row: Any) -> str:
    if isinstance(row, LedgerRowKey):
        return "open"
    if isinstance(row, Mapping):
        return str(row.get("status", "open"))
    return str(getattr(row, "status", "open"))


def _row_score(row: Any) -> float | None:
    if isinstance(row, LedgerRowKey):
        return None
    value = row.get("score") if isinstance(row, Mapping) else getattr(row, "score", None)
    if value is None:
        return None
    return _finite_nonnegative("ledger row score", float(value))


def margin_loss(quality_margin: float) -> float:
    return max(0.0, -_finite("quality_margin", quality_margin))


def stability_loss(stability_gap: float) -> float:
    return _finite_nonnegative("stability_gap", stability_gap)


def ledger_loss(ledger_rows: Iterable[Any], cost_protocol: Any) -> float:
    rows = tuple(ledger_rows)
    cost_protocol.validate_required_rows(REQUIRED_DEBT_ROWS)
    row_keys = frozenset(_row_key(row) for row in rows)
    missing = REQUIRED_DEBT_ROWS - row_keys
    if missing:
        labels = ", ".join(f"{row.kind}/{row.residue}" for row in sorted(missing))
        raise ValueError(f"ledger rows missing required debt rows: {labels}")

    total = 0.0
    for row in rows:
        key = _row_key(row)
        upper = _finite_nonnegative("cost protocol weight", cost_protocol.weight(key))
        if _row_status(row) == "closed":
            continue
        score = _row_score(row)
        total += upper if score is None else min(score, upper)
    return float(total)


def coverage_loss(
    unlogged_error_rate: float,
    critical_unlogged_error_rate: float,
) -> float:
    return _finite_nonnegative("unlogged_error_rate", unlogged_error_rate) + _finite_nonnegative(
        "critical_unlogged_error_rate",
        critical_unlogged_error_rate,
    )


def total_loss(
    task_loss: float,
    breakdown: CertificateGuidedLossBreakdown,
    weights: CertificateGuidedWeights,
) -> float:
    task = _finite_nonnegative("task_loss", task_loss)
    return float(
        task
        + float(weights.lambda_s) * breakdown.stability
        + float(weights.lambda_m) * breakdown.margin
        + float(weights.lambda_l) * breakdown.ledger
        + float(weights.lambda_c) * breakdown.coverage
    )

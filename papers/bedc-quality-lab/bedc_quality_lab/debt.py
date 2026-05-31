"""Lab-local debt assessment for quality evidence envelopes."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Mapping, Any


_CATEGORY_WEIGHTS = {
    "source": 0.18,
    "distribution": 0.22,
    "finite-sample": 0.20,
    "optimization": 0.20,
    "global-claim": 0.20,
}


@dataclass(frozen=True)
class DebtItem:
    kind: str
    residue: str
    severity: str
    status: str
    score: float


@dataclass(frozen=True)
class DebtAssessment:
    items: tuple[DebtItem, ...]
    debt_total: float


def _bounded(value: float, upper: float) -> float:
    return max(0.0, min(upper, float(value)))


def _severity(score: float, upper: float) -> str:
    if score <= 0.0:
        return "none"
    if score < 0.5 * upper:
        return "low"
    if score < upper:
        return "medium"
    return "high"


def _status(score: float, upper: float) -> str:
    if score <= 0.0:
        return "closed"
    if score < upper:
        return "partial"
    return "open"


def _positive_int(spec: Mapping[str, Any], key: str, default: int) -> int:
    value = spec.get(key, default)
    return value if isinstance(value, int) and value > 0 else default


def _source_score(source_spec: Mapping[str, Any]) -> float:
    upper = _CATEGORY_WEIGHTS["source"]
    count = _positive_int(source_spec, "source_count", 1)
    if count <= 1:
        return upper
    if count < 3:
        return 0.5 * upper
    return 0.0


def _distribution_score(source_spec: Mapping[str, Any]) -> float:
    upper = _CATEGORY_WEIGHTS["distribution"]
    mixing = source_spec.get("mixing")
    if isinstance(mixing, (list, tuple, set)):
        count = len(mixing)
    else:
        count = 1 if mixing else 0
    if count <= 1:
        return upper
    if count < 3:
        return 0.5 * upper
    return 0.0


def _finite_sample_score(source_spec: Mapping[str, Any]) -> float:
    upper = _CATEGORY_WEIGHTS["finite-sample"]
    sample_count = _positive_int(source_spec, "sample_count", 0)
    if sample_count >= 2048:
        return 0.0
    if sample_count >= 1024:
        return 0.25 * upper
    if sample_count >= 512:
        return 0.5 * upper
    return upper


def _optimization_score(classifier_spec: Mapping[str, Any]) -> float:
    upper = _CATEGORY_WEIGHTS["optimization"]
    training = str(classifier_spec.get("training", ""))
    name = str(classifier_spec.get("name", ""))
    text = f"{name} {training}".lower()
    if "certified" in text or "exhaustive" in text:
        return 0.0
    if "deterministic" in text:
        return 0.5 * upper
    return upper


def _global_claim_score(source_spec: Mapping[str, Any], stability_spec: Mapping[str, Any]) -> float:
    upper = _CATEGORY_WEIGHTS["global-claim"]
    if source_spec.get("global_claim") is True and stability_spec.get("multi_seed") is True:
        return 0.0
    if source_spec.get("global_claim") is True:
        return 0.5 * upper
    return upper


def _item(kind: str, residue: str, score: float) -> DebtItem:
    upper = _CATEGORY_WEIGHTS[kind]
    bounded = _bounded(score, upper)
    return DebtItem(
        kind=kind,
        residue=residue,
        severity=_severity(bounded, upper),
        status=_status(bounded, upper),
        score=bounded,
    )


def assess_debt(
    metrics: Mapping[str, float],
    source_spec: Mapping[str, Any],
    classifier_spec: Mapping[str, Any],
    stability_spec: Mapping[str, Any],
) -> DebtAssessment:
    """Assess canonical producer debt from the consensus producer surface.

    The full signature is forward-compatible with derivations that consume more
    envelope fields; the present scoring consumes the current debt subset.
    """
    del metrics
    items = (
        _item("source", "source-coverage", _source_score(source_spec)),
        _item("distribution", "mixing-family-coverage", _distribution_score(source_spec)),
        _item("finite-sample", "finite-sample-support", _finite_sample_score(source_spec)),
        _item("optimization", "optimizer-certificate", _optimization_score(classifier_spec)),
        _item("global-claim", "global-claim-boundary", _global_claim_score(source_spec, stability_spec)),
    )
    total = sum(item.score for item in items)
    return DebtAssessment(items=items, debt_total=float(total))


def format_debt_items(assessment: DebtAssessment) -> list[str]:
    return [
        (
            f"kind={item.kind}; residue={item.residue}; severity={item.severity}; "
            f"status={item.status}; score={item.score:.6f}"
        )
        for item in assessment.items
    ]

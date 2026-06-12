"""Finite classifier-shift projection for the BEDC quality lab."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Mapping

from .ledger import LedgerRowKey, ledger_complete


RelationRow = tuple[str, str, str]
SurfacePair = tuple[str, str]


@dataclass(frozen=True)
class ClassifierState:
    source_ids: frozenset[str]
    pattern_id: str
    ledger_policy: frozenset[LedgerRowKey]
    relation: frozenset[RelationRow]
    certificate: Mapping[str, object]
    surface_used: frozenset[SurfacePair]
    verification_status: str = "unverified"
    record_count: int = 0
    feature_count: int = 0
    notation: str = "default"


@dataclass(frozen=True)
class ClassifierPassage:
    source: ClassifierState
    target: ClassifierState
    recorded_rows: frozenset[LedgerRowKey] = field(default_factory=frozenset)


def common_source(passage: ClassifierPassage) -> frozenset[str]:
    return passage.source.source_ids & passage.target.source_ids


def _relation_on_common(
    state: ClassifierState,
    source_ids: frozenset[str],
) -> frozenset[RelationRow]:
    return frozenset(
        (left, right, judgment)
        for left, right, judgment in state.relation
        if left in source_ids and right in source_ids
    )


def classifier_equivalent(passage: ClassifierPassage) -> bool:
    source_ids = common_source(passage)
    return _relation_on_common(passage.source, source_ids) == _relation_on_common(
        passage.target,
        source_ids,
    )


def classifier_shift(passage: ClassifierPassage) -> bool:
    return not classifier_equivalent(passage)


def has_certificate(state: ClassifierState) -> bool:
    return state.certificate.get("cert_status") == "certified"


def has_ledger_witness(passage: ClassifierPassage) -> bool:
    return ledger_complete(passage.target.ledger_policy, passage.recorded_rows)


def _judgments_by_pair(
    state: ClassifierState,
    source_ids: frozenset[str],
) -> dict[SurfacePair, frozenset[str]]:
    judgments: dict[SurfacePair, set[str]] = {}
    for left, right, judgment in state.relation:
        if left in source_ids and right in source_ids:
            judgments.setdefault((left, right), set()).add(judgment)
    return {pair: frozenset(values) for pair, values in judgments.items()}


def classifier_surface_delta(passage: ClassifierPassage) -> frozenset[SurfacePair]:
    source_ids = common_source(passage)
    source_relation = _judgments_by_pair(passage.source, source_ids)
    target_relation = _judgments_by_pair(passage.target, source_ids)
    pairs = frozenset(source_relation) | frozenset(target_relation)
    return frozenset(
        pair
        for pair in pairs
        if source_relation.get(pair, frozenset()) != target_relation.get(pair, frozenset())
        and pair in passage.target.surface_used
    )


def _row_for_pair(pair: SurfacePair) -> LedgerRowKey:
    left, right = pair
    return LedgerRowKey("classifier", f"{left}->{right}")


def recorded_residue(passage: ClassifierPassage) -> frozenset[LedgerRowKey]:
    return frozenset(
        row for row in (_row_for_pair(pair) for pair in classifier_surface_delta(passage))
        if row in passage.recorded_rows
    )


def structural_discovery(passage: ClassifierPassage) -> bool:
    return (
        classifier_shift(passage)
        and has_certificate(passage.target)
        and has_ledger_witness(passage)
        and bool(classifier_surface_delta(passage))
    )


def shift_information(passage: ClassifierPassage) -> int:
    if not has_certificate(passage.target) or not has_ledger_witness(passage):
        return 0
    delta_rows = frozenset(_row_for_pair(pair) for pair in classifier_surface_delta(passage))
    if not delta_rows.issubset(passage.recorded_rows):
        return 0
    return len(delta_rows)

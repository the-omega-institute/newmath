"""Lab-local debt assessment for quality evidence envelopes."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable, Mapping, Any, Sequence

from .cost_protocol import CostProtocol, REQUIRED_DEBT_ROWS, SCOPED_DEBT_ROWS, load_cost_protocol
from .latent_distribution import CANONICAL_LATENT_DISTRIBUTION_KEYS, covered_distribution_family_keys
from .ledger import LedgerEntry, LedgerRowKey, ledger_debt, ledger_gap, recorded_rows, required_rows
from .mixing import covered_canonical_mixing_families
from .theorem_bound_quality import THEOREM_BOUND_ROW, _bound_values

ACTION_TRANSITION_ROW = LedgerRowKey("source", "action-transition-identification")
DIMENSION_MATCH_ROW = LedgerRowKey("source", "dimension-match")
DERIVATIVE_ROW_COVERAGE_ROW = LedgerRowKey("derivative", "row-coverage")
DERIVATIVE_HIGH_ORDER_INSTABILITY_ROW = LedgerRowKey("derivative", "high-order-instability")
DERIVATIVE_SHORTCUT_ATTRIBUTION_ROW = LedgerRowKey("derivative", "shortcut-attribution")
DERIVATIVE_COST_BENEFIT_NEGATIVE_ROW = LedgerRowKey("derivative", "cost-benefit-negative")
DERIVATIVE_UNPATCHABLE_HIGH_ORDER_CLAIM_ROW = LedgerRowKey("derivative", "unpatchable-high-order-claim")
JET_ORDER_COVERAGE_ROW = LedgerRowKey("jet", "order-coverage")
JET_MATCHED_RANDOM_CONTROL_ROW = LedgerRowKey("jet", "matched-random-control")
DERIVATIVE_SCOPED_ROWS = frozenset(
    {
        DERIVATIVE_ROW_COVERAGE_ROW,
        DERIVATIVE_HIGH_ORDER_INSTABILITY_ROW,
        DERIVATIVE_SHORTCUT_ATTRIBUTION_ROW,
        DERIVATIVE_COST_BENEFIT_NEGATIVE_ROW,
        DERIVATIVE_UNPATCHABLE_HIGH_ORDER_CLAIM_ROW,
        JET_ORDER_COVERAGE_ROW,
        JET_MATCHED_RANDOM_CONTROL_ROW,
    }
)
_EPS = 1.0e-12


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


def _number(value: Any) -> float | None:
    if isinstance(value, bool):
        return None
    if isinstance(value, (int, float)):
        return float(value)
    return None


def _mapping_value(spec: Mapping[str, Any], path: tuple[str, ...]) -> Any:
    value: Any = spec
    for key in path:
        if not isinstance(value, Mapping):
            return None
        value = value.get(key)
    return value


def _first_value(*sources: Mapping[str, Any], keys: tuple[str, ...]) -> Any:
    for key in keys:
        path = tuple(part for part in key.split(".") if part)
        for source in sources:
            value = _mapping_value(source, path)
            if value is not None:
                return value
    return None


def _row_sequence(value: Any) -> Sequence[Any]:
    if isinstance(value, Sequence) and not isinstance(value, (str, bytes, bytearray)):
        return value
    return ()


def _source_score(source_spec: Mapping[str, Any], protocol: CostProtocol) -> float:
    upper = protocol.weight(LedgerRowKey("source", "source-coverage"))
    count = _positive_int(source_spec, "source_count", 1)
    if count <= 1:
        return upper
    if count < 3:
        return 0.5 * upper
    return 0.0


def _distribution_score(source_spec: Mapping[str, Any], protocol: CostProtocol) -> float:
    upper = protocol.weight(LedgerRowKey("source", "mixing-family-coverage"))
    count = len(covered_canonical_mixing_families(source_spec.get("mixing")))
    if count <= 1:
        return upper
    if count < 4:
        return 0.5 * upper
    return 0.0


def _latent_gaussianity_score(source_spec: Mapping[str, Any], protocol: CostProtocol) -> float:
    upper = protocol.weight(LedgerRowKey("source", "latent-distribution-gaussianity"))
    distribution = source_spec.get("latent_distribution")
    family = distribution.get("family") if isinstance(distribution, Mapping) else distribution
    return 0.0 if family == "gaussian" else upper


def _latent_distribution_family_score(source_spec: Mapping[str, Any], protocol: CostProtocol) -> float:
    upper = protocol.weight(LedgerRowKey("source", "distribution-family-coverage"))
    count = len(covered_distribution_family_keys(source_spec))
    target = len(CANONICAL_LATENT_DISTRIBUTION_KEYS)
    if count <= 1:
        return upper
    if count < target:
        return 0.5 * upper
    return 0.0


def _finite_sample_score(source_spec: Mapping[str, Any], protocol: CostProtocol) -> float:
    upper = protocol.weight(LedgerRowKey("source", "finite-sample-support"))
    sample_count = _positive_int(source_spec, "sample_count", 0)
    if sample_count >= 2048:
        return 0.0
    if sample_count >= 1024:
        return 0.25 * upper
    if sample_count >= 512:
        return 0.5 * upper
    return upper


def _dimension_match_score(
    source_spec: Mapping[str, Any],
    classifier_spec: Mapping[str, Any],
    protocol: CostProtocol,
) -> float:
    upper = protocol.weight(DIMENSION_MATCH_ROW)
    latent_dim = source_spec.get("latent_dim")
    output_dim = classifier_spec.get("output_dim")
    if not isinstance(latent_dim, int) or not isinstance(output_dim, int):
        return upper
    if latent_dim <= 0 or output_dim <= 0:
        return upper
    gap = abs(latent_dim - output_dim)
    if gap == 0:
        return 0.0
    if gap == 1:
        return 0.5 * upper
    return upper


def _transition_isotropy_score(source_spec: Mapping[str, Any], protocol: CostProtocol) -> float:
    upper = protocol.weight(LedgerRowKey("source", "transition-isotropy"))
    transition = source_spec.get("transition_kernel")
    if not isinstance(transition, Mapping):
        return 0.0
    if transition.get("isotropic") is True:
        return 0.0
    gap = transition.get("anisotropy_gap", source_spec.get("transition_anisotropy_gap", 0.0))
    if not isinstance(gap, (int, float)):
        return upper
    if gap <= 0.0:
        return 0.0
    return _bounded((float(gap) / 0.5) * upper, upper)


def _action_transition_score(source_spec: Mapping[str, Any], protocol: CostProtocol) -> float:
    upper = protocol.weight(ACTION_TRANSITION_ROW)
    return 0.0 if source_spec.get("action_transition_identified") is True else upper


def _optimization_score(classifier_spec: Mapping[str, Any], protocol: CostProtocol) -> float:
    upper = protocol.weight(LedgerRowKey("classifier", "optimizer-certificate"))
    steps = classifier_spec.get("optimizer_certificate_steps")
    if isinstance(steps, int) and steps > 0:
        if steps >= 2000:
            return 0.0
        if steps >= 500:
            return 0.25 * upper
        if steps >= 100:
            return 0.5 * upper
        return upper
    training = str(classifier_spec.get("training", ""))
    name = str(classifier_spec.get("name", ""))
    text = f"{name} {training}".lower()
    if "certified" in text or "exhaustive" in text:
        return 0.0
    if "deterministic" in text:
        return 0.5 * upper
    return upper


def _global_claim_score(
    source_spec: Mapping[str, Any],
    stability_spec: Mapping[str, Any],
    protocol: CostProtocol,
) -> float:
    upper = protocol.weight(LedgerRowKey("generalization", "global-claim-boundary"))
    if source_spec.get("global_claim") is True and stability_spec.get("multi_seed") is True:
        return 0.0
    if source_spec.get("global_claim") is True:
        return 0.5 * upper
    return 0.0


def _theorem_bound_score(metrics: Mapping[str, float], protocol: CostProtocol) -> float:
    upper = protocol.weight(THEOREM_BOUND_ROW)
    values = _bound_values(metrics)
    if values is None:
        return upper
    margin = values["bound_margin_mse"]
    if margin >= 0.0:
        return 0.0
    scale = max(_EPS, 1.0, abs(values["theorem3_bound_mse"]))
    return _bounded((-margin / scale) * upper, upper)


def _derivative_row_coverage_score(
    metrics: Mapping[str, Any],
    source_spec: Mapping[str, Any],
    classifier_spec: Mapping[str, Any],
    stability_spec: Mapping[str, Any],
    protocol: CostProtocol,
) -> float:
    upper = protocol.weight(DERIVATIVE_ROW_COVERAGE_ROW)
    observed = _number(
        _first_value(
            metrics,
            source_spec,
            classifier_spec,
            stability_spec,
            keys=("derivative_row_count", "layerwise_derivative_rows.row_count", "jet.row_count"),
        )
    )
    required = _number(
        _first_value(
            metrics,
            source_spec,
            classifier_spec,
            stability_spec,
            keys=("required_derivative_row_count", "derivative_required_row_count", "jet.required_row_count"),
        )
    )
    if required is None:
        required = 1.0
    if observed is None:
        rows = _row_sequence(
            _first_value(
                source_spec,
                classifier_spec,
                stability_spec,
                keys=("raw_intervention_rows", "derivative_rows", "jet.rows"),
            )
        )
        observed = float(len(rows)) if rows else 0.0
    if required <= 0.0:
        return 0.0
    if observed >= required:
        return 0.0
    if observed > 0.0:
        return 0.5 * upper
    return upper


def _derivative_high_order_instability_score(
    metrics: Mapping[str, Any],
    source_spec: Mapping[str, Any],
    classifier_spec: Mapping[str, Any],
    stability_spec: Mapping[str, Any],
    protocol: CostProtocol,
) -> float:
    upper = protocol.weight(DERIVATIVE_HIGH_ORDER_INSTABILITY_ROW)
    status = _first_value(
        metrics,
        source_spec,
        classifier_spec,
        stability_spec,
        keys=("high_order_instability_status", "derivative.high_order_instability_status", "jet.high_order_instability_status"),
    )
    if status in {"closed", "stable", "pass", "none"}:
        return 0.0
    if status in {"partial", "unstable", "fail", "open"}:
        return 0.5 * upper if status == "partial" else upper
    value = _number(
        _first_value(
            metrics,
            source_spec,
            classifier_spec,
            stability_spec,
            keys=("high_order_instability", "derivative_instability", "jet.instability", "derivative.instability"),
        )
    )
    if value is None:
        return upper
    if value <= 0.0:
        return 0.0
    return _bounded((value / 0.20) * upper, upper)


def _derivative_shortcut_score(
    metrics: Mapping[str, Any],
    source_spec: Mapping[str, Any],
    classifier_spec: Mapping[str, Any],
    stability_spec: Mapping[str, Any],
    protocol: CostProtocol,
) -> float:
    upper = protocol.weight(DERIVATIVE_SHORTCUT_ATTRIBUTION_ROW)
    shortcut = _first_value(
        metrics,
        source_spec,
        classifier_spec,
        stability_spec,
        keys=("shortcut_derivative", "shortcut_derivative_detected", "derivative.shortcut_detected", "jet.shortcut_detected"),
    )
    if shortcut is True:
        return upper
    if shortcut is False:
        return 0.0
    value = _number(
        _first_value(
            metrics,
            source_spec,
            classifier_spec,
            stability_spec,
            keys=("shortcut_derivative_score", "shortcut_attribution_score", "derivative.shortcut_score", "jet.shortcut_score"),
        )
    )
    if value is None:
        return upper
    if value <= 0.0:
        return 0.0
    if value < 0.5:
        return 0.5 * upper
    return upper


def _derivative_cost_benefit_score(
    metrics: Mapping[str, Any],
    source_spec: Mapping[str, Any],
    classifier_spec: Mapping[str, Any],
    stability_spec: Mapping[str, Any],
    protocol: CostProtocol,
) -> float:
    upper = protocol.weight(DERIVATIVE_COST_BENEFIT_NEGATIVE_ROW)
    signal = _number(
        _first_value(
            metrics,
            source_spec,
            classifier_spec,
            stability_spec,
            keys=("derivative_net_benefit", "jet_net_benefit", "discovery_map_signal.net_positive_signal"),
        )
    )
    if signal is None:
        positive = _first_value(
            metrics,
            source_spec,
            classifier_spec,
            stability_spec,
            keys=("net_positive_signal", "discovery_map_signal.net_positive_signal"),
        )
        if positive is True:
            return 0.0
        if positive is False:
            return upper
        return upper
    if signal > 0.0:
        return 0.0
    if signal == 0.0:
        return 0.5 * upper
    return upper


def _derivative_unpatchable_claim_score(
    metrics: Mapping[str, Any],
    source_spec: Mapping[str, Any],
    classifier_spec: Mapping[str, Any],
    stability_spec: Mapping[str, Any],
    protocol: CostProtocol,
) -> float:
    upper = protocol.weight(DERIVATIVE_UNPATCHABLE_HIGH_ORDER_CLAIM_ROW)
    value = _first_value(
        metrics,
        source_spec,
        classifier_spec,
        stability_spec,
        keys=(
            "unpatchable_high_order_claim",
            "derivative.unpatchable_high_order_claim",
            "jet.unpatchable_high_order_claim",
        ),
    )
    if value is True:
        return upper
    if value is False:
        return 0.0
    effective_level = _first_value(
        metrics,
        source_spec,
        classifier_spec,
        stability_spec,
        keys=("effective_level", "discovery_map_signal.level_candidate", "d5_m.status"),
    )
    failed_gate = _first_value(
        metrics,
        source_spec,
        classifier_spec,
        stability_spec,
        keys=("failed_gate", "discovery_map_signal.failed_gate", "d5_m.failed_gate"),
    )
    if effective_level == "D5-M" and failed_gate:
        return upper
    if effective_level == "D5-M":
        return 0.5 * upper
    return 0.0


def _jet_order_coverage_score(
    metrics: Mapping[str, Any],
    source_spec: Mapping[str, Any],
    classifier_spec: Mapping[str, Any],
    stability_spec: Mapping[str, Any],
    protocol: CostProtocol,
) -> float:
    upper = protocol.weight(JET_ORDER_COVERAGE_ROW)
    observed = _number(
        _first_value(
            metrics,
            source_spec,
            classifier_spec,
            stability_spec,
            keys=("jet_order_count", "covered_jet_order_count", "jet.order_count"),
        )
    )
    required = _number(
        _first_value(
            metrics,
            source_spec,
            classifier_spec,
            stability_spec,
            keys=("required_jet_order_count", "jet.required_order_count", "required_order"),
        )
    )
    if required is None:
        required = 1.0
    if observed is None:
        orders = _row_sequence(
            _first_value(
                source_spec,
                classifier_spec,
                stability_spec,
                keys=("jet.orders", "jet_orders", "derivative_orders"),
            )
        )
        observed = float(len(frozenset(orders))) if orders else 0.0
    if required <= 0.0 or observed >= required:
        return 0.0
    if observed > 0.0:
        return 0.5 * upper
    return upper


def _jet_matched_random_control_score(
    metrics: Mapping[str, Any],
    source_spec: Mapping[str, Any],
    classifier_spec: Mapping[str, Any],
    stability_spec: Mapping[str, Any],
    protocol: CostProtocol,
) -> float:
    upper = protocol.weight(JET_MATCHED_RANDOM_CONTROL_ROW)
    status = _first_value(
        metrics,
        source_spec,
        classifier_spec,
        stability_spec,
        keys=("matched_random_jet_control_status", "jet.matched_random_control_status"),
    )
    if status in {"pass", "negative", "closed"}:
        return 0.0
    if status in {"partial", "mixed"}:
        return 0.5 * upper
    if status in {"fail", "positive", "open"}:
        return upper
    value = _number(
        _first_value(
            metrics,
            source_spec,
            classifier_spec,
            stability_spec,
            keys=("matched_random_jet_gain", "matched_random_high_order_gain", "jet.matched_random_gain"),
        )
    )
    if value is None:
        return upper
    if value <= 0.0:
        return 0.0
    if value < 0.02:
        return 0.5 * upper
    return upper


def _derivative_scoped_score(
    row: LedgerRowKey,
    metrics: Mapping[str, Any],
    source_spec: Mapping[str, Any],
    classifier_spec: Mapping[str, Any],
    stability_spec: Mapping[str, Any],
    protocol: CostProtocol,
) -> float:
    helpers = {
        DERIVATIVE_ROW_COVERAGE_ROW: _derivative_row_coverage_score,
        DERIVATIVE_HIGH_ORDER_INSTABILITY_ROW: _derivative_high_order_instability_score,
        DERIVATIVE_SHORTCUT_ATTRIBUTION_ROW: _derivative_shortcut_score,
        DERIVATIVE_COST_BENEFIT_NEGATIVE_ROW: _derivative_cost_benefit_score,
        DERIVATIVE_UNPATCHABLE_HIGH_ORDER_CLAIM_ROW: _derivative_unpatchable_claim_score,
        JET_ORDER_COVERAGE_ROW: _jet_order_coverage_score,
        JET_MATCHED_RANDOM_CONTROL_ROW: _jet_matched_random_control_score,
    }
    return helpers[row](metrics, source_spec, classifier_spec, stability_spec, protocol)


def _item(row: LedgerRowKey, score: float, protocol: CostProtocol) -> DebtItem:
    upper = protocol.weight(row)
    bounded = _bounded(score, upper)
    return DebtItem(
        kind=row.kind,
        residue=row.residue,
        severity=_severity(bounded, upper),
        status=_status(bounded, upper),
        score=bounded,
    )


def _required_entries(protocol: CostProtocol) -> tuple[LedgerEntry, ...]:
    return tuple(
        LedgerEntry(row=row, source_ref="quality-lab-cost-policy", weight=weight, critical=True)
        for row, weight in protocol.row_weights.items()
    )


def _required_entries_for_rows(rows: Iterable[LedgerRowKey], protocol: CostProtocol) -> tuple[LedgerEntry, ...]:
    return tuple(
        LedgerEntry(row=row, source_ref="quality-lab-cost-policy", weight=protocol.weight(row), critical=True)
        for row in rows
    )


def _recorded_entries(items: tuple[DebtItem, ...]) -> tuple[LedgerEntry, ...]:
    entries = []
    for item in items:
        if item.status == "closed":
            entries.append(
                LedgerEntry(
                    row=LedgerRowKey(item.kind, item.residue),
                    source_ref="quality-lab-observed-closure",
                    weight=0.0,
                    critical=True,
                )
            )
    return tuple(entries)


def assess_debt(
    metrics: Mapping[str, float],
    source_spec: Mapping[str, Any],
    classifier_spec: Mapping[str, Any],
    stability_spec: Mapping[str, Any],
    protocol: CostProtocol | None = None,
    extra_rows: Iterable[LedgerRowKey] = (),
) -> DebtAssessment:
    """Assess canonical producer debt from the consensus producer surface.

    The full signature is forward-compatible with derivations that consume more
    envelope fields; the present scoring consumes the current debt subset.
    """
    cost_protocol = load_cost_protocol() if protocol is None else protocol
    requested_extra_rows = frozenset(extra_rows)
    unknown_extra_rows = requested_extra_rows - SCOPED_DEBT_ROWS
    if unknown_extra_rows:
        rows = ", ".join(f"{row.kind}/{row.residue}" for row in sorted(unknown_extra_rows))
        raise ValueError(f"unknown scoped debt rows: {rows}")
    cost_protocol.validate_required_rows(REQUIRED_DEBT_ROWS | requested_extra_rows)
    items = [
        _item(LedgerRowKey("source", "source-coverage"), _source_score(source_spec, cost_protocol), cost_protocol),
        _item(
            LedgerRowKey("source", "mixing-family-coverage"),
            _distribution_score(source_spec, cost_protocol),
            cost_protocol,
        ),
        _item(
            LedgerRowKey("source", "latent-distribution-gaussianity"),
            _latent_gaussianity_score(source_spec, cost_protocol),
            cost_protocol,
        ),
        _item(
            LedgerRowKey("source", "distribution-family-coverage"),
            _latent_distribution_family_score(source_spec, cost_protocol),
            cost_protocol,
        ),
        _item(
            LedgerRowKey("source", "finite-sample-support"),
            _finite_sample_score(source_spec, cost_protocol),
            cost_protocol,
        ),
        _item(
            LedgerRowKey("source", "transition-isotropy"),
            _transition_isotropy_score(source_spec, cost_protocol),
            cost_protocol,
        ),
        _item(
            LedgerRowKey("classifier", "optimizer-certificate"),
            _optimization_score(classifier_spec, cost_protocol),
            cost_protocol,
        ),
        _item(
            THEOREM_BOUND_ROW,
            _theorem_bound_score(metrics, cost_protocol),
            cost_protocol,
        ),
        _item(
            LedgerRowKey("generalization", "global-claim-boundary"),
            _global_claim_score(source_spec, stability_spec, cost_protocol),
            cost_protocol,
        ),
    ]
    if DIMENSION_MATCH_ROW in requested_extra_rows:
        items.insert(
            5,
            _item(
                DIMENSION_MATCH_ROW,
                _dimension_match_score(source_spec, classifier_spec, cost_protocol),
                cost_protocol,
            ),
        )
    if ACTION_TRANSITION_ROW in requested_extra_rows:
        insert_at = 7 if DIMENSION_MATCH_ROW in requested_extra_rows else 6
        items.insert(
            insert_at,
            _item(ACTION_TRANSITION_ROW, _action_transition_score(source_spec, cost_protocol), cost_protocol),
        )
    for row in sorted(requested_extra_rows & DERIVATIVE_SCOPED_ROWS):
        items.append(
            _item(
                row,
                _derivative_scoped_score(
                    row,
                    metrics,
                    source_spec,
                    classifier_spec,
                    stability_spec,
                    cost_protocol,
                ),
                cost_protocol,
            )
        )
    item_tuple = tuple(items)
    required = required_rows(_required_entries_for_rows(REQUIRED_DEBT_ROWS | requested_extra_rows, cost_protocol))
    recorded = recorded_rows(_recorded_entries(item_tuple))
    gap = ledger_gap(required, recorded)
    cost_map = {
        LedgerRowKey(item.kind, item.residue): item.score
        for item in item_tuple
    }
    total = ledger_debt(gap, cost_map)
    return DebtAssessment(items=item_tuple, debt_total=float(total))


def format_debt_items(assessment: DebtAssessment) -> list[str]:
    return [
        (
            f"kind={item.kind}; residue={item.residue}; severity={item.severity}; "
            f"status={item.status}; score={item.score:.6f}"
        )
        for item in assessment.items
    ]

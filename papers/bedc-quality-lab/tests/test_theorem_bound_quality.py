import math

import pytest

from bedc_quality_lab.ledger import LedgerRowKey
from bedc_quality_lab.theorem_bound_quality import (
    theorem_bound_certificate,
    theorem_bound_ledger_gap,
    theorem_bound_quality_components,
)


def metrics(**patch):
    base = {
        "theorem3_bound": 1.0,
        "actual_recovery_error": 0.25,
        "bound_margin": 0.75,
        "normalized_gap_d": 0.10,
        "whitening_deviation_epsilon": 0.20,
    }
    return base | patch


def classifier(**patch):
    return {"output_dim": 2, "training": "align-cov-mean", "cert_status": "certified"} | patch


def test_positive_margin_certifies_and_negative_margin_is_not_clipped():
    certified = theorem_bound_certificate(metrics(bound_margin=0.10))
    not_certified = theorem_bound_certificate(
        metrics(theorem3_bound=0.40, actual_recovery_error=0.70, bound_margin=-0.30)
    )

    assert certified["cert_status"] == "certified"
    assert not_certified["cert_status"] == "not-certified"
    assert not_certified["cert_bound_margin"] == pytest.approx(-0.30)


def test_missing_bound_keys_fail_closed():
    certificate = theorem_bound_certificate({"theorem3_bound": 1.0})
    values = theorem_bound_quality_components({"theorem3_bound": 1.0}, 0.0, classifier())
    gap = theorem_bound_ledger_gap({"theorem3_bound": 1.0})

    assert certificate["cert_status"] == "not-certified"
    assert values["theorem_bound_benefit"] == 0.0
    assert gap is not None
    assert gap.residue == "theorem3-bound-margin"
    assert gap.status == "open"


def test_quality_q_identity_uses_theorem_bound_benefit():
    values = theorem_bound_quality_components(metrics(), 0.30, classifier())

    assert values["quality_benefit"] == values["theorem_bound_benefit"]
    assert values["quality_q"] == pytest.approx(
        values["theorem_bound_benefit"] - values["quality_cost"] - values["quality_debt"]
    )


def test_benefit_drops_as_actual_error_reaches_and_exceeds_bound():
    low_error = theorem_bound_quality_components(
        metrics(theorem3_bound=1.0, actual_recovery_error=0.20, bound_margin=0.80),
        0.0,
        classifier(),
    )
    near_bound = theorem_bound_quality_components(
        metrics(theorem3_bound=1.0, actual_recovery_error=0.90, bound_margin=0.10),
        0.0,
        classifier(),
    )
    over_bound = theorem_bound_quality_components(
        metrics(theorem3_bound=1.0, actual_recovery_error=1.10, bound_margin=-0.10),
        0.0,
        classifier(),
    )

    assert low_error["theorem_bound_benefit"] > near_bound["theorem_bound_benefit"]
    assert near_bound["theorem_bound_benefit"] >= over_bound["theorem_bound_benefit"]
    assert over_bound["theorem_bound_benefit"] == 0.0


def test_gap_and_whitening_penalties_are_monotone_inside_clamp():
    low_penalty = theorem_bound_quality_components(
        metrics(normalized_gap_d=0.10, whitening_deviation_epsilon=0.10),
        0.0,
        classifier(),
    )
    high_gap = theorem_bound_quality_components(
        metrics(normalized_gap_d=0.50, whitening_deviation_epsilon=0.10),
        0.0,
        classifier(),
    )
    high_whitening = theorem_bound_quality_components(
        metrics(normalized_gap_d=0.10, whitening_deviation_epsilon=0.50),
        0.0,
        classifier(),
    )

    assert high_gap["theorem_bound_benefit"] < low_penalty["theorem_bound_benefit"]
    assert high_whitening["theorem_bound_benefit"] < low_penalty["theorem_bound_benefit"]


def test_ledger_emits_theorem_bound_margin_not_proxy_row():
    gap = theorem_bound_ledger_gap(
        metrics(theorem3_bound=0.40, actual_recovery_error=0.70, bound_margin=-0.30)
    )

    assert gap is not None
    assert (gap.kind, gap.residue) == ("verification", "theorem3-bound-margin")
    assert LedgerRowKey(gap.kind, gap.residue) == LedgerRowKey("verification", "theorem3-bound-margin")


def test_positive_bound_margin_closes_ledger_gap():
    assert theorem_bound_ledger_gap(metrics(bound_margin=0.01)) is None


def test_non_finite_bound_values_fail_closed():
    bad = metrics(theorem3_bound=math.inf)

    assert theorem_bound_certificate(bad)["cert_status"] == "not-certified"
    assert theorem_bound_quality_components(bad, 0.0, classifier())["theorem_bound_benefit"] == 0.0
    assert theorem_bound_ledger_gap(bad).status == "open"

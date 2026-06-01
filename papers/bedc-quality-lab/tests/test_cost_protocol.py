from pathlib import Path

import pytest

from bedc_quality_lab.cost_protocol import (
    CostProtocol,
    NotClaimedPolicy,
    QualityFormula,
    REQUIRED_DEBT_ROWS,
    load_cost_protocol,
)
from bedc_quality_lab.debt import assess_debt
from bedc_quality_lab.ledger import LedgerRowKey
from bedc_quality_lab.metrics import QUALITY_Q_FORMULA_ID, quality_components, quality_formula_description


SENTINEL_WEIGHTS = {
    LedgerRowKey("source", "source-coverage"): 0.31,
    LedgerRowKey("source", "mixing-family-coverage"): 0.37,
    LedgerRowKey("source", "finite-sample-support"): 0.41,
    LedgerRowKey("source", "transition-isotropy"): 0.43,
    LedgerRowKey("classifier", "optimizer-certificate"): 0.47,
    LedgerRowKey("verification", "theorem3-bound-margin"): 0.49,
    LedgerRowKey("generalization", "global-claim-boundary"): 0.53,
}


def write_protocol(tmp_path: Path, body: str) -> Path:
    path = tmp_path / "cost_protocol.yaml"
    path.write_text(body, encoding="utf-8")
    return path


def protocol_body(*, omit: str | None = None, extra: str = "", formula_id: str = "quality_q") -> str:
    rows = {
        "source/source-coverage": "0.18",
        "source/mixing-family-coverage": "0.22",
        "source/finite-sample-support": "0.20",
        "source/transition-isotropy": "0.12",
        "classifier/optimizer-certificate": "0.20",
        "verification/theorem3-bound-margin": "0.20",
        "generalization/global-claim-boundary": "0.20",
    }
    row_lines = "\n".join(f"  {key}: {value}" for key, value in rows.items() if key != omit)
    return f"""name: test-cost-protocol
quality_formula:
  id: {formula_id}
  text: quality_benefit - quality_cost - quality_debt
row_weights:
{row_lines}
{extra}not_claimed:
  global_boundary: [outside-declared-scope, untested-source-families]
  treatment: Claims outside these boundary tokens are not included in quality_q closure credit.
"""


def cost_protocol(row_weights: dict[LedgerRowKey, float] | None = None) -> CostProtocol:
    return CostProtocol(
        name="custom-cost-protocol",
        row_weights=dict(SENTINEL_WEIGHTS if row_weights is None else row_weights),
        quality_formula=QualityFormula(id=QUALITY_Q_FORMULA_ID, text=quality_formula_description()),
        not_claimed=NotClaimedPolicy(
            global_boundary=("outside-declared-scope",),
            treatment="Claims outside this boundary token are not included in quality_q closure credit.",
        ),
    )


def closed_specs():
    return (
        {"source_count": 3, "mixing": ["a", "b", "c"], "sample_count": 2048, "global_claim": False},
        {"name": "certified-search", "training": "certified"},
        {"multi_seed": True},
    )


def closed_metrics(**patch):
    return {
        "theorem3_bound": 1.0,
        "actual_recovery_error": 0.25,
        "bound_margin": 0.75,
        "normalized_gap_d": 0.10,
        "whitening_deviation_epsilon": 0.20,
    } | patch


def item_scores(assessment):
    return {
        LedgerRowKey(item.kind, item.residue): item.score
        for item in assessment.items
    }


def test_default_protocol_covers_all_debt_rows():
    protocol = load_cost_protocol()

    assert frozenset(protocol.row_weights) == REQUIRED_DEBT_ROWS
    assert protocol.quality_formula.id == QUALITY_Q_FORMULA_ID
    assert protocol.formula_description() == quality_formula_description()


def test_missing_required_weight_fails_closed(tmp_path):
    path = write_protocol(tmp_path, protocol_body(omit="generalization/global-claim-boundary"))

    with pytest.raises(ValueError, match="missing required row weights"):
        load_cost_protocol(path)


def test_unknown_or_duplicate_row_fails_closed(tmp_path):
    unknown_path = write_protocol(
        tmp_path,
        protocol_body(extra="  source/unregistered-row: 0.01\n"),
    )
    with pytest.raises(ValueError, match="unknown cost protocol row"):
        load_cost_protocol(unknown_path)

    duplicate_path = write_protocol(
        tmp_path,
        protocol_body(extra="  source/source-coverage: 0.19\n"),
    )
    with pytest.raises(ValueError, match="duplicate cost protocol key"):
        load_cost_protocol(duplicate_path)


def test_bad_weight_and_formula_fail_closed(tmp_path):
    bad_weight_path = write_protocol(
        tmp_path,
        protocol_body().replace("  source/source-coverage: 0.18", "  source/source-coverage: -0.18"),
    )
    with pytest.raises(ValueError, match="out of bounds"):
        load_cost_protocol(bad_weight_path)

    bad_formula_path = write_protocol(tmp_path, protocol_body(formula_id="quality_q_alt"))
    with pytest.raises(ValueError, match="unknown quality formula id"):
        load_cost_protocol(bad_formula_path)


def test_debt_uses_injected_protocol_weights():
    default = load_cost_protocol()
    custom_weights = dict(default.row_weights)
    custom_weights[LedgerRowKey("source", "source-coverage")] = 0.50
    protocol = cost_protocol(custom_weights)

    assessment = assess_debt(
        closed_metrics(),
        {"source_count": 1, "mixing": ["a", "b", "c"], "sample_count": 2048},
        {"name": "certified-search", "training": "certified"},
        {"multi_seed": True},
        protocol=protocol,
    )

    source_item = next(item for item in assessment.items if item.residue == "source-coverage")
    assert source_item.score == pytest.approx(0.50)
    assert assessment.debt_total == pytest.approx(0.50)


@pytest.mark.parametrize(
    ("row", "metrics_patch", "source_patch", "classifier_patch", "stability_patch", "expected_factor"),
    [
        (
            LedgerRowKey("source", "source-coverage"),
            {},
            {"source_count": 1},
            {},
            {},
            1.0,
        ),
        (
            LedgerRowKey("source", "mixing-family-coverage"),
            {},
            {"mixing": ["a", "b"]},
            {},
            {},
            0.5,
        ),
        (
            LedgerRowKey("source", "finite-sample-support"),
            {},
            {"sample_count": 512},
            {},
            {},
            0.5,
        ),
        (
            LedgerRowKey("source", "transition-isotropy"),
            {},
            {"transition_kernel": {"isotropic": False, "anisotropy_gap": 0.25}},
            {},
            {},
            0.5,
        ),
        (
            LedgerRowKey("classifier", "optimizer-certificate"),
            {},
            {},
            {"name": "standardized-observation", "training": "deterministic-standardization"},
            {},
            0.5,
        ),
        (
            LedgerRowKey("verification", "theorem3-bound-margin"),
            {"theorem3_bound": 1.0, "actual_recovery_error": 2.0, "bound_margin": -1.0},
            {},
            {},
            {},
            1.0,
        ),
        (
            LedgerRowKey("generalization", "global-claim-boundary"),
            {},
            {"global_claim": True},
            {},
            {"multi_seed": False},
            0.5,
        ),
    ],
)
def test_assess_debt_derives_every_row_from_protocol_weight(
    row,
    metrics_patch,
    source_patch,
    classifier_patch,
    stability_patch,
    expected_factor,
):
    source_spec, classifier_spec, stability_spec = closed_specs()
    assessment = assess_debt(
        closed_metrics(**metrics_patch),
        source_spec | source_patch,
        classifier_spec | classifier_patch,
        stability_spec | stability_patch,
        protocol=cost_protocol(),
    )

    scores = item_scores(assessment)
    assert frozenset(scores) == REQUIRED_DEBT_ROWS
    expected_score = SENTINEL_WEIGHTS[row] * expected_factor
    assert scores[row] == pytest.approx(expected_score)
    assert assessment.debt_total == pytest.approx(expected_score)
    for other_row in REQUIRED_DEBT_ROWS - {row}:
        assert scores[other_row] == pytest.approx(0.0)


def test_theorem_bound_margin_debt_item_tracks_negative_zero_positive_and_missing_metrics():
    source_spec, classifier_spec, stability_spec = closed_specs()

    positive = assess_debt(closed_metrics(bound_margin=0.25), source_spec, classifier_spec, stability_spec)
    zero = assess_debt(
        closed_metrics(theorem3_bound=1.0, actual_recovery_error=1.0, bound_margin=0.0),
        source_spec,
        classifier_spec,
        stability_spec,
    )
    negative = assess_debt(
        closed_metrics(theorem3_bound=1.0, actual_recovery_error=2.0, bound_margin=-1.0),
        source_spec,
        classifier_spec,
        stability_spec,
        protocol=cost_protocol(),
    )
    missing = assess_debt({}, source_spec, classifier_spec, stability_spec, protocol=cost_protocol())

    positive_item = next(item for item in positive.items if item.residue == "theorem3-bound-margin")
    zero_item = next(item for item in zero.items if item.residue == "theorem3-bound-margin")
    negative_item = next(item for item in negative.items if item.residue == "theorem3-bound-margin")
    missing_item = next(item for item in missing.items if item.residue == "theorem3-bound-margin")

    assert positive_item.status == "closed"
    assert positive_item.score == pytest.approx(0.0)
    assert zero_item.status == "closed"
    assert zero_item.score == pytest.approx(0.0)
    assert negative_item.status == "open"
    assert negative_item.score == pytest.approx(SENTINEL_WEIGHTS[LedgerRowKey("verification", "theorem3-bound-margin")])
    assert negative.debt_total == pytest.approx(negative_item.score)
    assert missing_item.status == "open"
    assert missing_item.score == pytest.approx(SENTINEL_WEIGHTS[LedgerRowKey("verification", "theorem3-bound-margin")])
    assert missing.debt_total == pytest.approx(missing_item.score)


def test_single_row_protocol_weight_change_changes_that_row_score():
    row = LedgerRowKey("generalization", "global-claim-boundary")
    source_spec, classifier_spec, stability_spec = closed_specs()
    source_spec = source_spec | {"global_claim": True}
    stability_spec = stability_spec | {"multi_seed": False}
    changed_weights = dict(SENTINEL_WEIGHTS)
    changed_weights[row] = 0.79

    baseline = assess_debt(closed_metrics(), source_spec, classifier_spec, stability_spec, protocol=cost_protocol())
    changed = assess_debt(closed_metrics(), source_spec, classifier_spec, stability_spec, protocol=cost_protocol(changed_weights))

    assert item_scores(baseline)[row] == pytest.approx(0.5 * SENTINEL_WEIGHTS[row])
    assert item_scores(changed)[row] == pytest.approx(0.5 * changed_weights[row])
    assert changed.debt_total != pytest.approx(baseline.debt_total)
    assert changed.debt_total == pytest.approx(0.5 * changed_weights[row])


def test_quality_q_public_recomputation_uses_protocol_formula():
    protocol = load_cost_protocol()
    assessment = assess_debt(
        closed_metrics(),
        {"source_count": 1, "mixing": "single-family", "sample_count": 384, "global_claim": True},
        {"name": "tiny-mlp", "training": "align-cov-mean", "cert_status": "certified", "output_dim": 2},
        {"multi_seed": False},
        protocol=protocol,
    )
    values = quality_components(
        {"linear_identifiability_r2": 0.90, "approx_identifiability_proxy": 0.80},
        assessment.debt_total,
        {"name": "tiny-mlp", "training": "align-cov-mean", "cert_status": "certified", "output_dim": 2},
    )

    assert protocol.formula_description() == "quality_benefit - quality_cost - quality_debt"
    assert values["quality_q"] == pytest.approx(
        values["quality_benefit"] - values["quality_cost"] - values["quality_debt"]
    )

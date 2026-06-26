import numpy as np

from bedc_quality_lab.bedc_jepa_metrics import (
    bedc_debt_score,
    certified_coverage,
    false_claim_rate,
    gap_detection_auc,
    masked_binary_accuracy,
    unlogged_error_rate,
)
from bedc_quality_lab.bedc_jepa_world import (
    boundary_distinction,
    boundary_gap,
    make_boundary_gated_batch,
    radial_distinction_score,
    radial_gap_score,
    standardize_observation,
)


def test_boundary_gated_world_has_distinction_and_gap_labels():
    batch = make_boundary_gated_batch(1200, rho=0.81, radius=1.0, gap_width=0.15, seed=5)
    assert batch.z.shape == (1200, 2)
    assert batch.x.shape == (1200, 2)
    assert batch.distinction.shape == (1200,)
    assert batch.gap.shape == (1200,)
    assert 0.10 < float(np.mean(batch.distinction)) < 0.65
    assert 0.02 < float(np.mean(batch.gap)) < 0.25
    assert np.array_equal(batch.distinction, boundary_distinction(batch.z, radius=batch.radius))
    assert np.array_equal(batch.gap, boundary_gap(batch.z, radius=batch.radius, gap_width=batch.gap_width))


def test_radial_scores_support_low_gap_classifier_claims():
    batch = make_boundary_gated_batch(768, rho=0.84, radius=1.0, gap_width=0.14, seed=41)
    h = standardize_observation(batch.x)
    distinction_scores = radial_distinction_score(h, radius=batch.radius)
    gap_scores = radial_gap_score(h, radius=batch.radius, gap_width=batch.gap_width)
    outside_gap = ~batch.gap

    assert masked_binary_accuracy(distinction_scores, batch.distinction, outside_gap) > 0.75
    assert gap_detection_auc(gap_scores, batch.gap) > 0.55
    assert 0.0 <= false_claim_rate(distinction_scores, batch.distinction, batch.gap) <= 1.0
    assert 0.0 <= unlogged_error_rate(distinction_scores, batch.distinction, gap_scores) <= 1.0
    assert 0.0 <= certified_coverage(gap_scores) <= 1.0


def test_bedc_debt_score_penalizes_unlogged_errors_and_bad_gap_auc():
    good = bedc_debt_score(unlogged_error=0.02, false_claim=0.04, gap_auc=0.90, certified=0.80)
    bad = bedc_debt_score(unlogged_error=0.20, false_claim=0.25, gap_auc=0.55, certified=0.50)
    assert good < bad
    assert 0.0 <= good <= 1.0
    assert 0.0 <= bad <= 1.0

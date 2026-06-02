import copy

import pytest

from bedc_quality_lab.classifier_shift import classifier_surface_delta, shift_information, structural_discovery
from bedc_quality_lab.discovery import net_information, positive_discovery
from scripts import run_spectral_ablation_discovery as runner


def _payload():
    return runner._load_payload()


def _verdicts(payload=None):
    return runner._verdict_payload(_payload() if payload is None else payload)["verdicts"]


def _row(name, payload=None):
    return next(row for row in _verdicts(payload) if row["arm"] == name)


def test_projection_reuses_existing_predicates():
    payload = _payload()
    projection = runner._project_arm(payload, "hinge-ranked-treatment")
    passage = projection["passage"]
    claim = projection["claim"]
    row = _row("hinge-ranked-treatment", payload)

    assert row["surface_delta_count"] == len(classifier_surface_delta(passage))
    assert row["shift_information"] == shift_information(passage)
    assert row["structural_discovery"] == structural_discovery(passage)
    assert row["net_information"] == pytest.approx(net_information(claim))
    assert row["positive_discovery"] == positive_discovery(claim)


def test_common_vanilla_source_and_surface_delta_rows():
    projection = runner._project_arm(_payload(), "matched-random-single-axis")
    passage = projection["passage"]
    delta = classifier_surface_delta(passage)

    assert passage.source.pattern_id.endswith("vanilla")
    assert passage.source.source_ids == passage.target.source_ids
    assert delta
    assert delta.issubset(passage.target.surface_used)
    assert shift_information(passage) == len(delta)


def test_negative_verdict_is_runner_local_net_negative_case():
    payload = _payload()
    row = _row("hinge-ranked-treatment", payload)
    projection = runner._project_arm(payload, "hinge-ranked-treatment")

    assert structural_discovery(projection["passage"]) is True
    assert classifier_surface_delta(projection["passage"])
    assert net_information(projection["claim"]) < 0.0
    assert positive_discovery(projection["claim"]) is False
    assert row["verdict"] == "negative"


def test_compression_boundary_does_not_emit_positive_claim():
    payload = copy.deepcopy(_payload())
    vanilla_metrics = next(arm for arm in payload["arms"] if arm["name"] == runner.BEFORE_ARM)["envelope_projection"]["metrics"]
    arm = next(arm for arm in payload["arms"] if arm["name"] == "hinge-ranked-treatment")
    arm["envelope_projection"]["metrics"] = dict(vanilla_metrics)
    arm["observed_degradation_score"] = 0.0
    row = _row("hinge-ranked-treatment", payload)

    assert row["surface_delta_count"] == 0
    assert row["net_information"] == pytest.approx(0.0)
    assert row["positive_discovery"] is False
    assert row["verdict"] == "compression"


def test_rank_correlation_uses_hinge_degradation_scores():
    payload = _payload()
    report = runner._verdict_payload(payload)
    source_pairs = payload["rank_correlation"]["pairs"]
    pairs = report["rank_correlation"]["pairs"]

    assert [row["arm"] for row in pairs] == [row["arm"] for row in source_pairs]
    assert [row["observed_degradation_score"] for row in pairs] == [
        row["observed_degradation_score"] for row in source_pairs
    ]
    assert report["rank_correlation"]["source_hinge"] == payload["rank_correlation"]


def test_matched_random_baseline_is_reported_as_control():
    payload = _payload()
    report = runner._verdict_payload(payload)
    controls = report["matched_random_baseline"]["verdicts"]

    assert report["matched_random_baseline"]["source"] == payload["negative_control_summary"]
    assert controls
    assert {row["family"] for row in controls} == {"matched-random-control"}

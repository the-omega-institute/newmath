import copy
import json

import pytest

from bedc_quality_lab.classifier_shift import classifier_surface_delta, shift_information, structural_discovery
from bedc_quality_lab.discovery import net_information, positive_discovery
from scripts import run_spectral_ablation_discovery as runner


def _payload():
    return runner._load_payload()


def _write_payload(tmp_path, payload):
    path = tmp_path / "payload.json"
    path.write_text(json.dumps(payload), encoding="utf-8")
    return path


def _verdicts(payload=None):
    return runner._verdict_payload(_payload() if payload is None else payload)["verdicts"]


def _row(name, payload=None):
    return next(row for row in _verdicts(payload) if row["arm"] == name)


def test_payload_requires_vanilla_arm(tmp_path):
    path = _write_payload(
        tmp_path,
        {
            "config": {"metric_names": ["accuracy"]},
            "arms": [{"name": "treatment", "envelope_projection": {"metrics": {"accuracy": 0.8}}}],
        },
    )

    with pytest.raises(ValueError, match="^spectral-ablation payload must contain vanilla arm$"):
        runner._load_payload(path)


@pytest.mark.parametrize("config", [{}, {"metric_names": []}])
def test_payload_requires_metric_names(tmp_path, config):
    path = _write_payload(
        tmp_path,
        {
            "config": config,
            "arms": [{"name": runner.BEFORE_ARM, "envelope_projection": {"metrics": {"accuracy": 1.0}}}],
        },
    )

    with pytest.raises(ValueError, match="^spectral-ablation payload must contain metric_names$"):
        runner._load_payload(path)


def test_payload_requires_projected_metrics_for_each_arm(tmp_path):
    path = _write_payload(
        tmp_path,
        {
            "config": {"metric_names": ["accuracy", "coverage"]},
            "arms": [
                {
                    "name": runner.BEFORE_ARM,
                    "envelope_projection": {"metrics": {"accuracy": 1.0, "coverage": 1.0}},
                },
                {"name": "treatment", "envelope_projection": {"metrics": {"accuracy": 0.8}}},
            ],
        },
    )

    with pytest.raises(ValueError, match="^arm lacks projected metrics: treatment$"):
        runner._load_payload(path)


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


def test_positive_verdict_is_runner_local_positive_claim():
    payload = _payload()
    row = _row("tail-mixing-perturbation", payload)
    projection = runner._project_arm(payload, "tail-mixing-perturbation")
    delta = classifier_surface_delta(projection["passage"])

    assert structural_discovery(projection["passage"]) is True
    assert delta
    assert row["surface_delta_count"] == len(delta)
    assert row["surface_delta"]
    assert net_information(projection["claim"]) > 0.0
    assert row["net_information"] == pytest.approx(net_information(projection["claim"]))
    assert positive_discovery(projection["claim"]) is True
    assert row["positive_discovery"] is True
    assert row["verdict"] == "positive"


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

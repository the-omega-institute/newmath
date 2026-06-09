import copy
import json
import math

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


def _assert_row_matches_predicates(payload, arm_name):
    row = _row(arm_name, payload)
    projection = runner._project_arm(payload, arm_name)
    passage = projection["passage"]
    claim = projection["claim"]
    delta = classifier_surface_delta(passage)
    net = net_information(claim)

    assert row["surface_delta_count"] == len(delta)
    assert row["surface_delta"] == [list(pair) for pair in sorted(delta)]
    assert row["shift_information"] == shift_information(passage)
    assert row["structural_discovery"] == structural_discovery(passage)
    if math.isnan(net):
        assert math.isnan(row["net_information"])
    else:
        assert row["net_information"] == pytest.approx(net)
    assert row["positive_discovery"] == positive_discovery(claim)
    return row, projection, delta


def _minimal_source_payload():
    return {
        "applicability_boundary": {
            "claimed_scope": "tmp-path Gaussian spectral source.",
            "not_claimed": "No biological killed-walk coverage is claimed.",
        },
        "arms": [
            {
                "deletion_axes": [],
                "envelope_projection": {"metrics": {"accuracy": 1.0, "coverage": 1.0}},
                "family": "baseline",
                "name": runner.BEFORE_ARM,
                "observed_degradation_score": 0.0,
            },
            {
                "deletion_axes": ["tail"],
                "envelope_projection": {"metrics": {"accuracy": 0.8, "coverage": 0.9}},
                "family": "hinge-treatment",
                "name": "hinge-ranked-treatment",
                "observed_degradation_score": 0.25,
            },
            {
                "deletion_axes": ["random"],
                "envelope_projection": {"metrics": {"accuracy": 0.95, "coverage": 0.92}},
                "family": "matched-random-control",
                "name": "matched-random-single-axis",
                "observed_degradation_score": 0.05,
            },
        ],
        "config": {"metric_names": ["accuracy", "coverage"]},
        "generated_at": "2026-06-02T00:00:00+00:00",
        "negative_control_summary": {
            "max_control_score": 0.05,
            "treatment_better_than_all_controls": True,
            "treatment_score": 0.25,
        },
        "rank_correlation": {
            "method": "source-hinge-order",
            "pairs": [
                {"arm": "hinge-ranked-treatment", "observed_degradation_score": 0.25},
                {"arm": "matched-random-single-axis", "observed_degradation_score": 0.05},
            ],
            "spearman": 1.0,
        },
    }


@pytest.mark.parametrize(
    "arms",
    [
        [],
        [{"name": "treatment", "envelope_projection": {"metrics": {"accuracy": 0.8}}}],
    ],
)
def test_payload_requires_vanilla_arm(tmp_path, arms):
    path = _write_payload(
        tmp_path,
        {
            "config": {"metric_names": ["accuracy"]},
            "arms": arms,
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


@pytest.mark.parametrize("missing_arm_name", [runner.BEFORE_ARM, "treatment"])
def test_payload_requires_projected_metrics_for_each_arm(tmp_path, missing_arm_name):
    complete_metrics = {"accuracy": 1.0, "coverage": 1.0}
    missing_metrics = {"accuracy": 0.8}
    path = _write_payload(
        tmp_path,
        {
            "config": {"metric_names": ["accuracy", "coverage"]},
            "arms": [
                {
                    "name": runner.BEFORE_ARM,
                    "envelope_projection": {"metrics": missing_metrics if missing_arm_name == runner.BEFORE_ARM else complete_metrics},
                },
                {
                    "name": "treatment",
                    "envelope_projection": {"metrics": missing_metrics if missing_arm_name == "treatment" else complete_metrics},
                },
            ],
        },
    )

    with pytest.raises(ValueError, match=f"^arm lacks projected metrics: {missing_arm_name}$"):
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
    row, projection, delta = _assert_row_matches_predicates(payload, "hinge-ranked-treatment")

    assert structural_discovery(projection["passage"]) is True
    assert delta
    assert net_information(projection["claim"]) < 0.0
    assert positive_discovery(projection["claim"]) is False
    assert row["structural_discovery"] is True
    assert row["positive_discovery"] is False
    assert row["verdict"] == "negative"


def test_positive_verdict_is_runner_local_positive_claim():
    payload = _payload()
    row, projection, delta = _assert_row_matches_predicates(payload, "tail-mixing-perturbation")

    assert structural_discovery(projection["passage"]) is True
    assert delta
    assert net_information(projection["claim"]) > 0.0
    assert positive_discovery(projection["claim"]) is True
    assert row["structural_discovery"] is True
    assert row["positive_discovery"] is True
    assert row["verdict"] == "positive"


def test_compression_verdict_is_runner_local_zero_net_case():
    payload = copy.deepcopy(_payload())
    arm = next(arm for arm in payload["arms"] if arm["name"] == "hinge-ranked-treatment")
    arm["observed_degradation_score"] = -0.04
    row, projection, delta = _assert_row_matches_predicates(payload, "hinge-ranked-treatment")

    assert structural_discovery(projection["passage"]) is True
    assert delta
    assert net_information(projection["claim"]) == pytest.approx(0.0)
    assert positive_discovery(projection["claim"]) is False
    assert row["structural_discovery"] is True
    assert row["positive_discovery"] is False
    assert row["verdict"] == "compression"


def test_compression_verdict_covers_no_surface_delta_case():
    payload = copy.deepcopy(_payload())
    vanilla_metrics = next(arm for arm in payload["arms"] if arm["name"] == runner.BEFORE_ARM)["envelope_projection"]["metrics"]
    arm = next(arm for arm in payload["arms"] if arm["name"] == "hinge-ranked-treatment")
    arm["envelope_projection"]["metrics"] = dict(vanilla_metrics)
    arm["observed_degradation_score"] = 0.0
    row, projection, delta = _assert_row_matches_predicates(payload, "hinge-ranked-treatment")

    assert structural_discovery(projection["passage"]) is False
    assert not delta
    assert row["surface_delta_count"] == 0
    assert row["net_information"] == pytest.approx(0.0)
    assert row["positive_discovery"] is False
    assert row["verdict"] == "compression"


def test_project_arm_accepts_observed_score_override():
    projection = runner._project_arm(_payload(), "hinge-ranked-treatment", observed_degradation_score=-0.04)

    assert projection["score"] == pytest.approx(-0.04)
    assert net_information(projection["claim"]) == pytest.approx(0.0)


def test_runner_verdict_vocabulary_is_reachable_outcomes_only():
    payload = _payload()
    verdicts = runner._verdict_payload(payload)["verdicts"]

    assert {row["verdict"] for row in verdicts}.issubset({"positive", "negative", "compression"})
    for row in verdicts:
        _assert_row_matches_predicates(payload, row["arm"])


def test_verdict_payload_skips_vanilla_arm():
    report = runner._verdict_payload(_payload())

    assert report["scope_seal"] == runner.SCOPE_SEAL
    assert runner.BEFORE_ARM in report["arms"]
    assert runner.BEFORE_ARM not in {row["arm"] for row in report["verdicts"]}


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


def test_rank_correlation_filters_pairs_without_verdict_rows():
    payload = copy.deepcopy(_payload())
    payload["rank_correlation"]["pairs"].append(
        {
            "arm": runner.BEFORE_ARM,
            "observed_degradation_score": 0.0,
            "expected": "source-only",
        }
    )
    payload["rank_correlation"]["pairs"].append(
        {
            "arm": "outside-runner",
            "observed_degradation_score": 1.0,
            "expected": "absent",
        }
    )
    report = runner._verdict_payload(payload)

    pair_arms = {row["arm"] for row in report["rank_correlation"]["pairs"]}
    assert runner.BEFORE_ARM not in pair_arms
    assert "outside-runner" not in pair_arms


def test_rank_correlation_reports_nan_for_single_after_arm():
    payload = copy.deepcopy(_payload())
    payload["arms"] = [
        next(arm for arm in payload["arms"] if arm["name"] == runner.BEFORE_ARM),
        next(arm for arm in payload["arms"] if arm["name"] == "hinge-ranked-treatment"),
    ]
    payload["rank_correlation"]["pairs"] = [
        next(pair for pair in payload["rank_correlation"]["pairs"] if pair["arm"] == "hinge-ranked-treatment")
    ]
    report = runner._verdict_payload(payload)

    assert len(report["rank_correlation"]["pairs"]) == 1
    assert math.isnan(report["rank_correlation"]["spearman"])


def test_matched_random_baseline_is_reported_as_control():
    payload = _payload()
    report = runner._verdict_payload(payload)
    controls = report["matched_random_baseline"]["verdicts"]

    assert report["matched_random_baseline"]["source"] == payload["negative_control_summary"]
    assert controls
    assert {row["family"] for row in controls} == {"matched-random-control"}


def test_write_payload_writes_json_and_markdown_from_same_payload(monkeypatch, tmp_path):
    monkeypatch.setattr(runner, "ROOT", tmp_path)
    (tmp_path / "reports").mkdir()
    payload = runner._verdict_payload(_minimal_source_payload())

    runner._write_payload(payload)

    json_path = tmp_path / runner.JSON_ARTIFACT
    md_path = tmp_path / runner.REPORT_ARTIFACT
    assert json_path.exists()
    assert md_path.exists()
    written = json.loads(json_path.read_text(encoding="utf-8"))
    report = md_path.read_text(encoding="utf-8")
    treatment = next(row for row in written["verdicts"] if row["arm"] == "hinge-ranked-treatment")
    control = next(row for row in written["verdicts"] if row["arm"] == "matched-random-single-axis")

    assert written == payload
    assert written["artifact"] == runner.JSON_ARTIFACT
    assert written["report"] == runner.REPORT_ARTIFACT
    assert written["rank_correlation"]["method"] == "hinge-observed-degradation-vs-discovery-net-information"
    assert written["matched_random_baseline"]["source"]["treatment_score"] == pytest.approx(0.25)
    assert written["applicability_boundary"]["claimed_scope"] == "tmp-path Gaussian spectral source."
    assert f"| `{treatment['arm']}` | `{treatment['family']}` | {treatment['observed_degradation_score']:.6f} |" in report
    assert f"{treatment['surface_delta_count']} | {treatment['shift_information']} | {treatment['net_information']:.6f}" in report
    assert f"| `{control['arm']}` | `{control['family']}` | {control['observed_degradation_score']:.6f} |" in report
    assert f"- Method: `{written['rank_correlation']['method']}`" in report
    assert f"- Spearman: `{written['rank_correlation']['spearman']:.6f}`" in report
    assert "- Treatment score: `0.250000`" in report
    assert "- Max control score: `0.050000`" in report
    assert "- Claimed scope: `tmp-path Gaussian spectral source.`" in report
    assert "- Not claimed: No biological killed-walk coverage is claimed." in report


def test_main_writes_json_and_markdown_discovery_projection(monkeypatch, tmp_path):
    monkeypatch.setattr(runner, "ROOT", tmp_path)
    source_path = tmp_path / runner.SOURCE_JSON_ARTIFACT
    source_path.parent.mkdir(parents=True)
    source_path.write_text(json.dumps(_minimal_source_payload()), encoding="utf-8")

    runner.main()

    json_path = tmp_path / runner.JSON_ARTIFACT
    md_path = tmp_path / runner.REPORT_ARTIFACT
    assert json_path.exists()
    assert md_path.exists()
    payload = json.loads(json_path.read_text(encoding="utf-8"))
    report = md_path.read_text(encoding="utf-8")

    assert payload["artifact"] == runner.JSON_ARTIFACT
    assert payload["report"] == runner.REPORT_ARTIFACT
    assert payload["source_artifacts"]["source_json_artifact"] == runner.SOURCE_JSON_ARTIFACT
    assert payload["source_artifacts"]["source_report_artifact"] == runner.SOURCE_REPORT_ARTIFACT
    assert payload["arms"] == [runner.BEFORE_ARM, "hinge-ranked-treatment", "matched-random-single-axis"]
    assert {row["arm"] for row in payload["verdicts"]} == {"hinge-ranked-treatment", "matched-random-single-axis"}
    assert {row["verdict"] for row in payload["verdicts"]}.issubset({"positive", "negative", "compression"})
    assert payload["rank_correlation"]["method"] == "hinge-observed-degradation-vs-discovery-net-information"
    assert payload["matched_random_baseline"]["source"]["treatment_better_than_all_controls"] is True
    assert [row["arm"] for row in payload["matched_random_baseline"]["verdicts"]] == ["matched-random-single-axis"]
    assert payload["applicability_boundary"]["claimed_scope"] == "tmp-path Gaussian spectral source."
    assert payload["applicability_boundary"]["not_claimed"] == "No biological killed-walk coverage is claimed."

    for row in payload["verdicts"]:
        assert (
            f"| `{row['arm']}` | `{row['family']}` | {row['observed_degradation_score']:.6f} | "
            f"{row['surface_delta_count']} | {row['shift_information']} | {row['net_information']:.6f} | "
            f"`{str(row['structural_discovery']).lower()}` | `{str(row['positive_discovery']).lower()}` | `{row['verdict']}` |"
        ) in report
    assert f"- Method: `{payload['rank_correlation']['method']}`" in report
    assert f"- Spearman: `{payload['rank_correlation']['spearman']:.6f}`" in report
    assert f"- Source hinge Spearman: `{payload['rank_correlation']['source_hinge']['spearman']:.6f}`" in report
    assert f"- Treatment score: `{payload['matched_random_baseline']['source']['treatment_score']:.6f}`" in report
    assert f"- Max control score: `{payload['matched_random_baseline']['source']['max_control_score']:.6f}`" in report
    assert f"- Claimed scope: `{payload['applicability_boundary']['claimed_scope']}`" in report
    assert f"- Not claimed: {payload['applicability_boundary']['not_claimed']}" in report

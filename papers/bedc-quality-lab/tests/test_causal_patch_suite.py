import json
from copy import deepcopy

from scripts import run_causal_patch_suite as runner


def test_patch_registry_covers_nine_channels_once():
    channels = [spec.channel for spec in runner.PATCH_REGISTRY]

    assert tuple(channels) == runner.PATCH_CHANNELS
    assert len(channels) == 9
    assert len(set(channels)) == 9
    assert all(spec.eval_only for spec in runner.PATCH_REGISTRY)


def test_patch_hardgates_pass_for_local_eval_only_suite():
    payload = runner.build_payload(generated_at="fixture")
    gates = payload["hardgates"]["gates"]

    assert payload["hardgates"]["status"] == "pass"
    assert gates["PATCH-HG1"]["status"] == "pass"
    assert gates["PATCH-HG2"]["status"] == "pass"
    assert gates["PATCH-HG3"]["status"] == "pass"
    assert gates["PATCH-HG4"]["status"] == "pass"
    assert gates["PATCH-HG5"]["status"] == "pass"
    for record in payload["records"]:
        if record["role"] == "after":
            assert set(record["touched_channels"]) <= set(record["allowed_touched_channels"])
        assert record["eval_only"] is True


def _hardgates_for(payload):
    return runner._hardgates(
        records=payload["records"],
        effect_summary=payload["effect_summary"],
        matched_control_summary=payload["matched_control_summary"],
        side_effect_ledger=payload["side_effect_ledger"],
    )


def _first_patch_summary(payload):
    return next(iter(payload["effect_summary"]["by_patch"].values()))


def test_patch_hg1_fails_closed_when_treatment_touches_non_target_channel():
    payload = runner.build_payload(generated_at="fixture")
    mutated = deepcopy(payload)
    treatment = next(record for record in mutated["records"] if record["role"] == "after")
    treatment["touched_channels"] = [*treatment["allowed_touched_channels"], "off-target-channel"]

    hardgates = _hardgates_for(mutated)

    assert hardgates["gates"]["PATCH-HG1"]["status"] == "fail"
    assert hardgates["status"] == "fail"


def test_patch_hg2_fails_closed_when_any_record_is_not_eval_only():
    payload = runner.build_payload(generated_at="fixture")
    mutated = deepcopy(payload)
    mutated["records"][0]["eval_only"] = False

    hardgates = _hardgates_for(mutated)

    assert hardgates["gates"]["PATCH-HG2"]["status"] == "fail"
    assert hardgates["status"] == "fail"


def test_patch_hg3_fails_closed_when_treatment_ci_is_not_positive():
    payload = runner.build_payload(generated_at="fixture")
    mutated = deepcopy(payload)
    treatment = _first_patch_summary(mutated)["treatment"][runner.PATCH_EFFECT_METRIC]
    treatment["ci95_low"] = 0.0

    hardgates = _hardgates_for(mutated)

    assert hardgates["gates"]["PATCH-HG3"]["status"] == "fail"
    assert hardgates["status"] == "fail"


def test_patch_hg4_fails_closed_when_matched_control_ci_excludes_zero():
    payload = runner.build_payload(generated_at="fixture")
    mutated = deepcopy(payload)
    control = _first_patch_summary(mutated)["matched_control"][runner.PATCH_EFFECT_METRIC]
    control["ci95_low"] = 0.01
    control["ci95_high"] = 0.02
    mutated["matched_control_summary"] = runner._matched_control_summary(mutated["effect_summary"])

    hardgates = _hardgates_for(mutated)

    assert mutated["matched_control_summary"]["rows"][0]["ci_includes_zero"] is False
    assert hardgates["gates"]["PATCH-HG4"]["status"] == "fail"
    assert hardgates["status"] == "fail"


def test_patch_hg5_fails_closed_when_side_effect_ledger_row_is_missing():
    payload = runner.build_payload(generated_at="fixture")
    mutated = deepcopy(payload)
    mutated["side_effect_ledger"] = mutated["side_effect_ledger"][1:]

    hardgates = _hardgates_for(mutated)

    assert hardgates["gates"]["PATCH-HG5"]["status"] == "fail"
    assert hardgates["status"] == "fail"


def test_patch_hg5_fails_closed_when_side_effect_ledger_row_is_false():
    payload = runner.build_payload(generated_at="fixture")
    mutated = deepcopy(payload)
    mutated["side_effect_ledger"][0]["ledger_row_present"] = False

    hardgates = _hardgates_for(mutated)

    assert hardgates["gates"]["PATCH-HG5"]["status"] == "fail"
    assert hardgates["status"] == "fail"


def test_treatment_quality_ci_is_positive_and_control_ci_includes_zero():
    payload = runner.build_payload(generated_at="fixture")

    for summary in payload["effect_summary"]["by_patch"].values():
        treatment = summary["treatment"][runner.PATCH_EFFECT_METRIC]
        control = summary["matched_control"][runner.PATCH_EFFECT_METRIC]
        assert treatment["status"] == "ok"
        assert treatment["n"] == runner.PATCH_MIN_PAIRED_SEEDS
        assert treatment["ci95_low"] > 0.0
        assert control["status"] == "ok"
        assert control["ci95_low"] <= 0.0 <= control["ci95_high"]


def test_side_effect_ledger_has_one_row_per_non_target_control_touch():
    payload = runner.build_payload(generated_at="fixture")
    expected = [
        (record["patch_id"], record["seed"], channel)
        for record in payload["records"]
        if record["role"] == "matched_control"
        for channel in record["touched_channels"]
    ]
    observed = [
        (row["patch_id"], row["seed"], row["touched_channel"])
        for row in payload["side_effect_ledger"]
    ]

    assert observed == expected
    assert all(row["target_local"] is False for row in payload["side_effect_ledger"])
    assert all(row["ledger_row_present"] is True for row in payload["side_effect_ledger"])


def test_schema_constants_are_emitted_verbatim():
    payload = runner.build_payload(generated_at="fixture")
    constants = payload["schema_constants"]

    assert constants["CAUSAL_PATCH_SCHEMA_ID"] == "bedc-quality-lab:causal-patch-suite"
    assert tuple(constants["PATCH_CHANNELS"]) == runner.PATCH_CHANNELS
    assert tuple(constants["PATCH_HARDGATES"]) == runner.PATCH_HARDGATES
    assert constants["PATCH_MIN_PAIRED_SEEDS"] == 3
    assert constants["PATCH_CI_ALPHA"] == 0.05
    assert constants["PATCH_EFFECT_METRIC"] == "quality_q"
    assert tuple(constants["PATCH_METRICS"]) == runner.PATCH_METRICS
    assert constants["PATCH_MATCHED_CONTROL"] == runner.PATCH_MATCHED_CONTROL
    assert constants["PATCH_SIDE_EFFECT_COMPLETENESS"] == runner.PATCH_SIDE_EFFECT_COMPLETENESS


def test_write_artifacts_creates_json_ledger_and_markdown(tmp_path):
    paths = runner.write_artifacts(root=tmp_path, generated_at="fixture")

    assert set(paths) == {"json", "ledger", "markdown"}
    assert paths["json"].relative_to(tmp_path).as_posix() == runner.JSON_ARTIFACT
    assert paths["ledger"].relative_to(tmp_path).as_posix() == runner.LEDGER_ARTIFACT
    assert paths["markdown"].relative_to(tmp_path).as_posix() == runner.REPORT_ARTIFACT
    payload = json.loads(paths["json"].read_text(encoding="utf-8"))
    ledger = json.loads(paths["ledger"].read_text(encoding="utf-8"))
    report = paths["markdown"].read_text(encoding="utf-8")
    assert payload["schema_id"] == runner.CAUSAL_PATCH_SCHEMA_ID
    assert ledger["source_artifact"] == runner.JSON_ARTIFACT
    assert "# Causal Patch Suite" in report


def test_not_claimed_denies_real_transformer_token_attention_closure():
    payload = runner.build_payload(generated_at="fixture")
    text = " ".join(payload["not_claimed"]).lower()

    assert "no real transformer token or attention closure is claimed" in text
    assert payload["discovery_projection"]["discovery_level_effect"] == "none"
    assert payload["discovery_projection"]["not_a_terminal_verdict"] is True

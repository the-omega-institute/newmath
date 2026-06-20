import json

import pytest

from bedc_quality_lab import namecert_closure_routing as ncr
from scripts import (
    run_namecert_audit,
    run_namecert_authswap,
    run_namecert_closure_routing,
    run_namecert_closure_verify,
)


def _assert_smoke_contract(payload):
    assert payload["schema_id"] == ncr.SCHEMA_ID
    assert payload["admission"]["admission_gate"] is False
    assert {row["status"] for row in payload["hardgates"].values()} == {"pass"}

    metrics = payload["metrics"]
    assert metrics["learned"]["accuracy"] > 0.5
    assert metrics["heldout_depth"]["depth"] > metrics["heldout_depth"]["train_max_depth"]
    assert metrics["heldout_depth"]["accuracy"] > 0.5
    assert metrics["learned"]["accuracy"] <= payload["analytic_ceiling"]["analytic_bayes"] + payload["analytic_ceiling"]["tolerance"]

    for key in (
        "matched_twin_closure_blind",
        "serialization_only_adversary",
        "bounded_pattern_control",
    ):
        low, high = metrics[key]["ci"]
        assert low <= 0.5 <= high
        assert metrics[key]["accuracy"] == 0.5


def test_smoke_authswap_real_torch_contract():
    payload = ncr.build_record("smoke_authswap", device="cpu", generated_at="fixture-time").to_dict()

    _assert_smoke_contract(payload)
    assert payload["profile"]["profile_id"] == "smoke_authswap"
    assert payload["json_artifact"] == "reports/namecert_authswap.json"


def test_smoke_audit_real_torch_contract():
    payload = ncr.build_record("smoke_audit", device="cpu", generated_at="fixture-time").to_dict()

    _assert_smoke_contract(payload)
    assert payload["profile"]["profile_id"] == "smoke_audit"
    assert payload["json_artifact"] == "reports/namecert_audit.json"


def test_runner_writes_authswap_and_audit_reports(tmp_path):
    authswap = ncr.run_and_write("smoke_authswap", root=tmp_path, device="cpu", generated_at="fixture-time")
    audit = ncr.run_and_write("smoke_audit", root=tmp_path, device="cpu", generated_at="fixture-time")

    for payload in (authswap, audit):
        _assert_smoke_contract(payload)
        json_path = tmp_path / payload["json_artifact"]
        markdown_path = tmp_path / payload["markdown_artifact"]
        assert json_path.exists()
        assert markdown_path.exists()
        assert json.loads(json_path.read_text(encoding="utf-8")) == payload
        assert payload["profile"]["profile_id"] in markdown_path.read_text(encoding="utf-8")


def test_profile_scripts_are_thin_entrypoints(tmp_path, capsys):
    assert run_namecert_closure_routing.main(["--root", str(tmp_path), "--device", "cpu", "--generated-at", "fixture-time"]) == 0
    assert run_namecert_closure_verify.main(["--root", str(tmp_path), "--device", "cpu", "--generated-at", "fixture-time"]) == 0
    assert run_namecert_authswap.main(["--root", str(tmp_path), "--device", "cpu", "--generated-at", "fixture-time"]) == 0
    assert run_namecert_audit.main(["--root", str(tmp_path), "--device", "cpu", "--generated-at", "fixture-time"]) == 0

    lines = capsys.readouterr().out.strip().splitlines()
    summaries = [json.loads(line) for line in lines]
    expected = [
        ("smoke_closure_routing", "reports/namecert_closure_routing.json"),
        ("smoke_closure_verify", "reports/namecert_closure_verify.json"),
        ("smoke_authswap", "reports/namecert_authswap.json"),
        ("smoke_audit", "reports/namecert_audit.json"),
    ]
    assert [(summary["profile_id"], summary["json_artifact"]) for summary in summaries] == expected
    for profile_id, json_artifact in expected:
        json_path = tmp_path / json_artifact
        markdown_path = json_path.with_suffix(".md")
        assert json_path.exists()
        assert markdown_path.exists()
        payload = json.loads(json_path.read_text(encoding="utf-8"))
        _assert_smoke_contract(payload)
        assert payload["profile"]["profile_id"] == profile_id
        assert profile_id in markdown_path.read_text(encoding="utf-8")


def test_profile_validation_rejects_unknown_and_invalid_overrides():
    with pytest.raises(ValueError, match="unknown NameCert closure-routing profile"):
        ncr.resolve_profile("missing-profile")
    with pytest.raises(ValueError, match="train_max_depth must be positive"):
        ncr.resolve_profile("smoke_authswap", train_max_depth=0)
    with pytest.raises(ValueError, match="epochs must be positive"):
        ncr.resolve_profile("smoke_authswap", epochs=0)


def test_profile_overrides_are_reflected_in_payload():
    payload = ncr.build_record(
        "smoke_closure_verify",
        device="cpu",
        generated_at="fixture-time",
        train_max_depth=2,
        epochs=8,
    ).to_dict()

    _assert_smoke_contract(payload)
    assert payload["profile"]["train_max_depth"] == 2
    assert payload["profile"]["heldout_depth"] == 3
    assert payload["profile"]["epochs"] == 8
    assert payload["metrics"]["heldout_depth"]["train_max_depth"] == 2
    assert payload["metrics"]["heldout_depth"]["depth"] == 3


def test_device_policy_validation_and_cuda_availability(monkeypatch):
    with pytest.raises(ValueError, match="device must be one of"):
        ncr.resolve_device_policy("bad-device")

    monkeypatch.setattr(ncr.torch.cuda, "is_available", lambda: False)
    assert ncr.resolve_device_policy("auto")["selected"] == "cpu"
    assert ncr.resolve_device_policy("cpu")["selected"] == "cpu"
    with pytest.raises(RuntimeError, match="requested cuda device is not available"):
        ncr.resolve_device_policy("cuda")

    monkeypatch.setattr(ncr.torch.cuda, "is_available", lambda: True)
    assert ncr.resolve_device_policy("auto")["selected"] == "cuda"
    assert ncr.resolve_device_policy("cuda")["selected"] == "cuda"


def test_evaluate_hardgates_fails_closed_for_malformed_and_below_threshold_metrics():
    profile = ncr.resolve_profile("smoke_authswap")
    malformed = ncr.evaluate_hardgates(
        {
            "learned": [],
            "matched_twin_closure_blind": {"ci": ["not", "numeric"]},
            "serialization_only_adversary": {"ci": [0.7, 0.8]},
            "heldout_depth": {"depth": profile.train_max_depth, "accuracy": 0.5},
            "bounded_pattern_control": {"ci": []},
        },
        profile,
    )

    assert {row["status"] for row in malformed.values()} == {"fail"}

    below_threshold = ncr.evaluate_hardgates(
        {
            "learned": {"accuracy": 0.5},
            "matched_twin_closure_blind": {"ci": [0.6, 0.8]},
            "serialization_only_adversary": {"ci": [0.0, 0.4]},
            "heldout_depth": {"depth": profile.train_max_depth, "accuracy": 1.0},
            "bounded_pattern_control": {"ci": [0.51, 0.9]},
        },
        profile,
    )

    assert below_threshold["learned_above_chance"]["status"] == "fail"
    assert below_threshold["matched_twin_closure_blind_chance"]["status"] == "fail"
    assert below_threshold["serialization_only_adversary_chance"]["status"] == "fail"
    assert below_threshold["heldout_depth_above_chance"]["status"] == "fail"
    assert below_threshold["bounded_pattern_chance"]["status"] == "fail"


def test_cli_no_markdown_and_overrides_affect_outputs(tmp_path, capsys):
    assert (
        run_namecert_closure_verify.main(
            [
                "--root",
                str(tmp_path),
                "--device",
                "cpu",
                "--generated-at",
                "fixture-time",
                "--train-max-depth",
                "2",
                "--epochs",
                "8",
                "--no-markdown",
            ]
        )
        == 0
    )

    summary = json.loads(capsys.readouterr().out.strip())
    json_path = tmp_path / summary["json_artifact"]
    markdown_path = json_path.with_suffix(".md")
    payload = json.loads(json_path.read_text(encoding="utf-8"))

    assert summary["profile_id"] == "smoke_closure_verify"
    assert json_path.exists()
    assert not markdown_path.exists()
    assert payload["profile"]["train_max_depth"] == 2
    assert payload["profile"]["heldout_depth"] == 3
    assert payload["profile"]["epochs"] == 8
    assert payload["metrics"]["heldout_depth"]["depth"] == 3
